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

### OQ6. Parametric sorts and instantiation

**OQ6.1.** `Stream{T = Account}` is a sort instantiation — `T` is bound to `Account`. How does the type resolver handle:
  - Checking that `T` is a valid parameter of `Stream`?
  - Propagating the binding into operations? (`map` on `Stream{T = Account}` expects `Account -> ?B`)
  - Nested instantiation? `Stream{T = List{T = Int}}`

**OQ6.2.** How do type variables (`?T`) interact with parametric sorts? In `operation identity(x: ?T) -> ?T`, `?T` is a universally quantified type variable. Resolution at call sites binds `?T` to a concrete sort.

**OQ6.3.** Constraints on type variables? `operation sort_list(l: List{T = ?T}) -> List{T = ?T} requires Ordered{T = ?T}` — the `requires` constrains `?T` to sorts satisfying `Ordered`. How is this checked?

### OQ7. Error reporting

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
