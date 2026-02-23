# 011: Type Resolution

## Status: Brainstorming

## Depends on: none

## Blocks: 010 (Query System), 012 (Sort-Defined Syntax Sugar)

## Motivation

Several design questions converge on the need for a type resolution mechanism:

1. **Query desugaring** (010) needs to know which sort an expression belongs to in order to desugar comprehension syntax into the correct `flatMap`/`guard`/`pure` calls.
2. **Sort-defined syntax sugar** (012) activates based on sort — the desugarer needs type information to know which sugar applies.
3. **Logical variables in type position** (`?T`) need resolution to determine what sort a variable ranges over.
4. **Operation dispatch** — when multiple sorts define an operation with the same name, the caller's argument types determine which one applies.
5. **Subsort polymorphism** — querying by sort `S` should match subsorts; this requires knowing the sort lattice at resolution time.

Currently, Anthill's pipeline is: parse (tree-sitter CST) → convert (parse IR) → scan definitions → load (KB). Type information is only fully available after loading. But desugaring and some resolution decisions need type info earlier.

## Key Fact: Type Variables ARE Logic Variables

In the current implementation, type variables (`?T` in sort definitions and operation signatures) and logic variables (`?x` in rule bodies) use the **same representation**: `Term::Var(VarId)`.

| Source | KB representation |
|--------|-------------------|
| `sort T = ?` in sort body | `SortInfo(T, Abstract)` fact; `?` not stored as a separate term |
| `?T` in operation param type | `Var(VarId)` directly in the operation's `Fn` named_args |
| `?x` in rule body | `Var(VarId)` — structurally identical |
| `Stream{T = Int}` (instantiation) | `Fn("Stream", T: Ref("Int"))` — **not** unification, just structured data |

This means: type parameters and logic variables are **unified at the KB level**. The distinction is a user-level/parse-time concept only.

### Implication: Two paths for type instantiation

**Path A: Instantiation = unification.** Since `?T` is `Var(VarId)`, binding `Stream{T = Int}` could be literal unification of `?T` with `Int`. Type resolution IS query resolution. Most "types-are-terms" approach.

**Path B: Instantiation stays syntactic.** `Stream{T = Int}` remains `Fn("Stream", T: Ref("Int"))` — a concrete term. The KB never unifies type vars during instantiation. Simpler, current behavior.

## The Problem

The kernel language spec says "types are terms" — sort identifiers are just terms. This is powerful but means there's no separate "type system" in the traditional sense. Instead, sort relationships are facts in the KB:

```
-- These are KB facts, not a separate type lattice:
fact red <: Color
fact green <: Color
fact blue <: Color
fact Eq{T = Int}     -- Int satisfies Eq
```

This raises the question: when and how does the system resolve types?

### What is the typing lattice?

The current type structure in Anthill, from concrete to abstract:

```
Literals (Int, Float, String, Bool)     — ground types, always known
    ↑
Entities (account, cons, nil, ...)      — constructors, typed by enclosing sort
    ↑
Sorts with constructors (Account, List) — sum types (closed: exactly these constructors)
    ↑
Abstract sorts (sort T = ?)             — type parameters, unbound until instantiated
    ↑
Spec sorts (Eq, Ordered, Numeric)       — interfaces, satisfied via fact assertions
    ↑
Logical variables (?x in rules)         — fully unbound, typed only by unification context
```

Key questions about this lattice:

**Are there untyped terms?** Currently yes — several cases:
- `Term::Fn("foo", [...])` where `foo` is not a declared constructor — it's a valid term but has no declared sort. Is it untyped? Or implicitly typed as "Fact" (the universal sort)?
- `Term::Var(v)` before unification — no type constraint. Ranges over everything.
- `Term::Ref(sym)` — a reference to a name. The referenced name has a sort, but the ref term itself?
- Rule heads: `rule length(nil) = 0` — what sort is the rule fact itself? Currently stored with sort `Rule`.

**Is everything in the KB typed?** Facts have an explicit `fe_sort` field (the sort under which the fact was asserted). But terms within facts may contain untyped subterms (variables, nested Fn terms). Should every subterm have a known sort?

**Where do types come from?**
- Entity declarations: `entity account(id: Int, owner: String, balance: Int)` — types from signature
- Operation declarations: types from parameter/return annotations
- Rule bodies: types inferred from unification context
- Standalone facts: types from the `fact` assertion's sort parameter
- Instantiation: types from binding `{T = Int}`

## Open Questions

### OQ1. When does type resolution happen?

**OQ1.1.** Current pipeline stages where type info is needed:

| Stage | What's known | What's needed |
|-------|-------------|---------------|
| Parse (tree-sitter) | Syntax only | Nothing — purely structural |
| Convert (parse IR) | Names, structure | Nothing yet |
| Scan definitions | Sort names, scope parents | Scope resolution (already done) |
| Load (KB) | Full sort lattice, all facts | Everything |
| Post-load | Complete KB | Query resolution, sugar desugaring |

Where should type resolution fit? Options:
  - (a) **During loading**: as facts are loaded, resolve types incrementally. Pro: single pass. Con: order-dependent.
  - (b) **Post-load pass**: load everything, then resolve types. Pro: order-independent. Con: extra pass.
  - (c) **Lazy/on-demand**: resolve types when needed (e.g., when a query is executed or sugar is desugared). Pro: minimal work. Con: late errors.

**OQ1.2.** Is type resolution a one-time thing, or ongoing? If agents can assert new sort relationships (`fact MyType <: SomeSpec`) at runtime, the type lattice changes dynamically. Does resolution need to be incremental?

### OQ2. What does type resolution produce?

**OQ2.1.** For a term `account(?id, ?owner, ?bal)`:
  - What sort is this term? → `Account` (by functor `account` matching a constructor)
  - What sorts are the arguments? → `?id: Int`, `?owner: String`, `?bal: Int` (from entity declaration)
  - Is this a complete/partial application? → complete (all 3 args provided)

**OQ2.2.** For a variable `?x`:
  - What sort does `?x` range over? → unknown until unified
  - Can we constrain it? `?x : Int` → `?x` ranges over `Int`
  - Does the constraint come from the declaration site or use site?

**OQ2.3.** For a sort expression `Stream{T = Account}`:
  - Is this a valid instantiation? → need to check `T` is a sort parameter of `Stream`
  - What operations are available? → need to know `Stream`'s operations
  - Does it satisfy any spec sorts? → need to check `fact SomeSpec{T = Stream}`

### OQ3. Type inference vs type checking

**OQ3.1.** Does Anthill have **type inference** (deduce types from usage) or only **type checking** (verify explicit annotations)?

In logic programming, unification IS a form of type inference — variables get bound to terms of specific sorts through unification. Is this sufficient, or do we need a separate inference pass?

**OQ3.2.** How much inference is needed for sort-defined syntax sugar? If `[?x | ?x <- expr]` needs to know that `expr` is a `Stream` to desugar, then at minimum we need to infer the sort of `expr`. Options:
  - Require explicit annotation: `[?x | ?x <- (expr : Stream{T = Int})]` — no inference needed
  - Infer from context: if `expr` is a call to an operation returning `Stream{T = Int}`, propagate that
  - Infer from operations: if `expr` supports `flatMap`/`guard`/`pure`, it's comprehension-compatible (structural typing)

**OQ3.3.** Bidirectional type checking? Some systems propagate type info both top-down (expected type) and bottom-up (inferred type). E.g., `let s : Stream{T = Int} = query account(?, ?, ?bal)` — the expected type `Stream{T = Int}` constrains how `query` is desugared. Is bidirectional checking worth the complexity?

### OQ4. Sort resolution for operations

**OQ4.1.** When an operation name appears in a term, which sort's operation is it? E.g., both `List` and `Stream` might have a `map` operation. Resolution options:
  - **Qualified names**: `Stream.map(s, f)` — explicit, no ambiguity
  - **Receiver-based**: `map(s, f)` where the sort of `s` determines which `map`
  - **Import-based**: the current scope's imports determine which `map` is visible

**OQ4.2.** Can operations be **overloaded** across sorts? If `add` exists on both `Int` and `Float`, is `add(1, 2)` resolved by argument types?

**OQ4.3.** How does this interact with spec sorts? If `Numeric` declares `add`, and both `Int` and `Float` satisfy `Numeric`, then `add` is polymorphic. Resolution needs to know the concrete sort to dispatch.

### OQ5. Types-are-terms implications

**OQ5.1.** Since sorts are terms, sort resolution IS term resolution in the KB. Checking "is `X` of sort `S`?" is equivalent to querying `fact X : S` (or the equivalent subsort chain). Should type resolution literally be a KB query?

**OQ5.2.** If type resolution is a KB query, then it requires the KB to be loaded. This creates a chicken-and-egg problem for sugar desugaring — you need type info to desugar, but desugaring happens before (or during) KB loading.

**OQ5.3.** Possible resolution: a **two-phase load**:
  1. First pass: load sort declarations, entity constructors, operation signatures (the "type skeleton")
  2. Desugar + resolve types using the skeleton
  3. Second pass: load rules, facts, constraints (the "logic content")

This separates "what sorts exist and what operations they have" from "what facts hold about them."

### OQ5b. The Typing Lattice — What Categories of Types Exist?

The Anthill type universe, from most concrete to most abstract:

```
                    ┌─────────────────────────────────┐
                    │  Logical variables (?x in rules) │  — fully unbound
                    └──────────────┬──────────────────┘
                                   │
                    ┌──────────────┴──────────────────┐
                    │  Abstract sorts (sort T = ?)     │  — type parameters, bound by instantiation
                    └──────────────┬──────────────────┘
                                   │
                    ┌──────────────┴──────────────────┐
                    │  Spec sorts (Eq, Ordered, ...)   │  — interfaces, satisfied via facts
                    └──────────────┬──────────────────┘
                                   │
               ┌───────────────────┼───────────────────┐
               │                   │                   │
    ┌──────────┴─────────┐  ┌─────┴──────┐  ┌────────┴────────┐
    │ Sorts with entities │  │ Namespaces │  │ Parametric sorts │
    │ (sum types: Color,  │  │ (grouping) │  │ (List{T=?},     │
    │  Account, List)     │  │            │  │  Stream{T=?})   │
    └──────────┬─────────┘  └────────────┘  └────────┬────────┘
               │                                      │
    ┌──────────┴─────────┐              ┌─────────────┴────────┐
    │ Entities/ctors      │              │ Instantiated sorts   │
    │ (red, account,      │              │ (List{T=Int},        │
    │  cons, nil)         │              │  Stream{T=Account})  │
    └──────────┬─────────┘              └──────────────────────┘
               │
    ┌──────────┴─────────┐
    │ Literals            │
    │ (Int, Float,        │
    │  String, Bool)      │
    └────────────────────┘
```

**OQ5b.1. Are there untyped terms?** Several cases where terms lack a known sort:

| Term | Typed? | Issue |
|------|--------|-------|
| `Fn("foo", [...])` where `foo` not declared | No sort | Is this a soft error? Or is it valid as a "raw fact"? |
| `Var(v)` before unification | No constraint | Ranges over all sorts until bound |
| `Ref(sym)` to a sort name | Sort of the sort? | `Color` is a sort — but what is the sort of `Color` itself? `Sort`? |
| Rule head `length(nil) = 0` | Stored as sort `Rule` | But what sort is the head term `length(nil)`? |
| `Quoted("rust", "fn main() {}")` | No sort | Foreign code — opaque to the sort system |
| `Bottom` | No sort | The contradiction/denial marker |

**OQ5b.2. Should every KB term have a known sort?** Options:
  - (a) **Yes — fully typed.** Every term's sort is determined at load time. Untyped terms are errors. This enables static checking but may be too restrictive for incremental/agent-driven KB construction.
  - (b) **Partially typed.** Declared entities and operations are typed. Variables and raw `Fn` terms are untyped until unified/resolved. The KB is a mix of typed and untyped regions.
  - (c) **Everything is "Fact" by default.** Untyped terms have an implicit universal sort `Fact` or `Term`. Sorts provide refinement but aren't required.

**OQ5b.3. How do sorts relate to each other?** The current relationships:
  - **Subsort** (`<:`): `red <: Color` — constructors are subsorts of their enclosing sort
  - **Spec satisfaction**: `fact Eq{T = Int}` — Int satisfies the Eq spec
  - **Type parameter binding**: `List{T = Int}` — T is bound to Int
  - **Type alias**: `sort Money = Int` — Money is another name for Int

Are these all the same relation (subtyping)? Or distinct relations with different semantics?

**OQ5b.4. Sort of sorts.** What is the sort of `Int`? Options:
  - `Int : Sort` — all sort names have sort `Sort`
  - `Int : Type` — with `Type` as a universe (á la Haskell's `Type` kind)
  - No meta-sort — sort names are just terms, not typed themselves
  - Currently: sort declarations create `SortInfo(name, kind)` facts with sort `Sort` and domain = scope

**OQ5b.5. Spec sorts and the lattice.** Spec sorts (Eq, Ordered, Numeric) are at a different level — they classify sorts, not terms. `Eq{T = Int}` says "Int as a sort satisfies Eq." This is a **sort-level predicate**, not a term-level type. Should the lattice distinguish:
  - Term-level types: `42 : Int`, `red : Color`
  - Sort-level predicates: `Int satisfies Eq`, `Account satisfies Persistent`

Or are these unified in the types-are-terms framework?

### OQ6. Fact-Set Matching (not term unification)

Type resolution in Anthill should be **fact-set matching**: unifying a set of fact patterns (from a sort definition) against the actual facts in the KB, with consistent variable binding across the set.

#### Why not term unification?

A sort is not a single term — it's a **template for a set of facts**. When you define:

```
sort Eq {
  sort T = ?
  operation eq(a: T, b: T) -> Bool
}
```

This generates a fact template (a set of patterns with shared variable `T`):

```
Template(Eq, T):
  { SortInfo(T, ...),
    Operation(eq, a: T, b: T, _returns: Bool) }
```

Asserting `fact Eq{T = Int}` means: apply substitution `{T → Int}` and check the KB:

```
Check against KB:
  SortInfo(Int, ...) ?                → ✓ Int is a declared sort
  Operation(eq, a: Int, b: Int, _returns: Bool) ?  → ✓ or ✗ (obligation if missing)
```

This is fundamentally different from term unification:

| | Term unification | Fact-set matching |
|--|-----------------|-------------------|
| Input | two terms | set of fact patterns + KB |
| Matches | one term against one term | multiple patterns against KB contents |
| Variables | bind within one equation | bind **consistently across** multiple facts |
| Result | single substitution | substitution + per-fact status (found / missing / partial) |
| Partial match | failure | meaningful — missing facts = **obligations** |

#### The key operations

**Instantiation checking.** Given `Eq{T = Int}`:
1. Look up the fact template for `Eq`
2. Apply substitution `{T → Int}` to all patterns in the template
3. Query the KB for each instantiated pattern
4. Report: which facts exist, which are missing (= obligations)

**Spec satisfaction.** `fact Eq{T = Int}` asserts that Int satisfies Eq. The system:
1. Performs instantiation checking (above)
2. Missing facts become **open obligations** — pheromone signals for agents to fulfill
3. Full match = satisfaction verified

**Subsort-aware matching.** When checking if `Operation(eq, a: Int, b: Int, _returns: Bool)` exists, allow subsort matches: if `Nat <: Int`, an operation `eq(a: Nat, b: Nat) -> Bool` could partially match (with subsort coercion).

#### Analogies in other systems

| System | Mechanism | Anthill equivalent |
|--------|-----------|-------------------|
| ML module signatures | Signature matching: does module M provide types/values declared in sig S? | Fact-set matching: does KB provide facts declared in sort S? |
| Rust trait impl | Does `impl Eq for Int` provide all required methods? | Does `fact Eq{T = Int}` + KB have all required operation facts? |
| TypeScript structural typing | Does this object have the right shape? | Does this KB region have the right fact shape? |
| Algebraic specification (Maude) | Theory morphism: map spec axioms to implementation | Fact-set substitution: map sort template to KB facts |

#### Open questions

**OQ6.1.** Is fact-set matching a kernel primitive, or derived from single-fact queries? It could be implemented as: for each pattern in the template, run `query(kb, pattern)`. But the **consistency** requirement (same `?T` binding across all queries) makes it more than just independent queries.

**OQ6.2.** How does fact-set matching relate to the query system (010)? A fact-set match is essentially a **conjunctive query** with shared variables: "find substitution σ such that all patterns in the template match KB facts under σ." This is exactly what rule bodies do.

**OQ6.3.** What happens on partial match? Options:
  - (a) **Obligation generation**: missing facts become work items / pheromone signals. This is the Anthill way — the colony discovers what's needed.
  - (b) **Error**: partial match = type error. Strict, catches problems early.
  - (c) **Conditional**: the sort is "partially satisfied" — some operations available, others not yet.

**OQ6.4.** Can fact-set matching be **incremental**? If new facts are asserted, does a previously partial match become complete? E.g., an agent implements `eq` for `Int` after `fact Eq{T = Int}` was asserted — the obligation is now fulfilled.

**OQ6.5.** Does fact-set matching subsume term unification for type instantiation? I.e., is `Stream{T = Int}` also fact-set matching (check that Stream's template with `T = Int` has consistent facts)? Or is instantiation simpler (just syntactic substitution)?

#### Sort definitions as fact templates with variables (not Abstract marker)

Currently, `sort T = ?` in a sort body creates `SortInfo(T, Abstract)` — using a special enum variant. Instead, store `SortInfo(T, ?)` where `?` is a logical variable:

```
-- Current (special Abstract kind):
sort Eq { sort T = ? }   →   SortInfo(Eq.T, Abstract)

-- Proposed (logical variable):
sort Eq { sort T = ? }   →   SortInfo(Eq.T, ?kind)
```

Then the sort definition IS its fact template — a set of facts with logical variables:

```
Template for Eq:
  SortInfo(Eq.T, ?kind)                                  -- T's kind is unbound
  Operation(eq, a: Eq.T, b: Eq.T, _returns: Bool)        -- eq takes two T's

Template for List:
  SortInfo(List.T, ?kind)                                 -- T's kind is unbound
  Entity(nil)                                             -- nil constructor
  Entity(cons, head: List.T, tail: List)                  -- cons constructor
  Operation(length, l: List, _returns: Int)               -- length operation
```

Instantiation `Eq{T = Int}` applies `{Eq.T → Int}` and does fact-set matching:

```
After substitution:
  SortInfo(Int, ?kind)         → matches SortInfo(Int, Defined) ✓, binds ?kind = Defined
  Operation(eq, a: Int, ...)   → check KB ✓ or generate obligation
```

Benefits:
- **No special `Abstract`/`Defined`/`Constructor` enum** — sort kind is discovered by matching, not declared
- **Uniform**: sort definitions, instantiations, and queries all use the same representation (facts with variables)
- **The `?` in `sort T = ?` literally means what it says** — "T's definition is an unbound variable"
- Sort kind (Abstract, Defined, Constructor) becomes a **derived property** from matching, not a stored tag

**OQ6.6.** Should we adopt this representation? Trade-offs:
  - Pro: maximally uniform, "types are terms" taken to its conclusion
  - Pro: sort templates become queryable (you can ask "what does Eq require?")
  - Con: more complex loading (need to track which facts are template facts vs concrete facts)
  - Con: the `?` in template facts must not be confused with `?` in queries/rules
  - Con: need to distinguish "this fact is part of a sort's template" from "this fact is asserted in the KB"

**OQ6.7.** How to distinguish template facts from concrete facts? Options:
  - (a) Template facts have a special domain (e.g., domain = the sort term itself)
  - (b) Template facts have a special sort (e.g., sort = `Template`)
  - (c) Template facts contain unbound variables — that's what makes them templates
  - (d) Separate storage: templates in one index, concrete facts in another

### OQ7. Parametric sorts and instantiation

**OQ7.1.** `Stream{T = Account}` is a sort instantiation — `T` is bound to `Account`. How does the type resolver handle:
  - Checking that `T` is a valid parameter of `Stream`?
  - Propagating the binding into operations? (`map` on `Stream{T = Account}` expects `Account -> ?B`)
  - Nested instantiation? `Stream{T = List{T = Int}}`

**OQ6.2.** How do type variables (`?T`) interact with parametric sorts? In `operation identity(x: ?T) -> ?T`, `?T` is a universally quantified type variable. Resolution at call sites binds `?T` to a concrete sort.

**OQ6.3.** Constraints on type variables? `operation sort_list(l: List{T = ?T}) -> List{T = ?T} requires Ordered{T = ?T}` — the `requires` constrains `?T` to sorts satisfying `Ordered`. How is this checked?

### OQ8. Error reporting

**OQ7.1.** When type resolution fails, what errors are produced?
  - "Unknown sort `Foo`" — name not found
  - "Sort mismatch: expected `Int`, got `String`" — argument type error
  - "Operation `map` is ambiguous: found in `List` and `Stream`" — overload resolution failure
  - "Sort `MyType` does not satisfy `Ordered`" — spec sort not satisfied

**OQ7.2.** Where are errors reported? At the term level (pointing to the specific argument)? At the declaration level (pointing to the operation signature)?

**OQ7.3.** Can errors be deferred? In a logic programming system, some type mismatches might be detected only at query time (when unification fails). Is it acceptable to have "runtime type errors" from unification failure, or should everything be caught statically?

## Relationship to Other Proposals

- **010 (Query System)**: Queries need type resolution for sort-query (`? : Color`), for comprehension syntax desugaring, and for checking that query patterns match fact sorts.
- **012 (Sort-Defined Syntax Sugar)**: Sugar activation depends on type resolution — "does this sort support comprehension syntax?" requires knowing the sort and its operations.
- **002 (Arrow Sorts)**: Arrow sorts (`A -> B`) introduce function types that need resolution in operation signatures and higher-order operations.

## References

- Current symbol resolution: `rustland/anthill-core/src/intern.rs` (`SymbolTable`, `resolve_in_scope`)
- Current scan-then-load pipeline: `rustland/anthill-core/src/parse/scan.rs`, `rustland/anthill-core/src/kb/load.rs`
- Sort lattice: subsort facts in KB, `is_subtype` in `Anthill_Kernel.thy`
- Spec sort satisfaction: `fact Eq{T = Int}` pattern in stdlib
- kernel-language.md §3 (sorts), §5 (operations), §8 (semantics)
