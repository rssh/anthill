# 011: Type Resolution

## Status: Brainstorming

## Depends on: none (013 dependency resolved — abstract effect parameters implemented)

## Blocks: 010 (Query System — syntax sugar only, core layers 0-1 unblocked), 012 (Sort-Defined Syntax Sugar)

## Motivation

Several design questions converge on the need for a type resolution mechanism:

1. **Query desugaring** (010) needs to know which sort an expression belongs to in order to desugar comprehension syntax into the correct `flatMap`/`guard`/`pure` calls.
2. **Sort-defined syntax sugar** (012) activates based on sort — the desugarer needs type information to know which sugar applies.
3. **Logical variables in type position** (`?T`) need resolution to determine what sort a variable ranges over.
4. **Operation dispatch** — when multiple sorts define an operation with the same name, the caller's argument types determine which one applies.
5. **Entity subtyping** — querying by sort `S` should match its entities; this requires knowing EntityOf relationships at resolution time.

Currently, Anthill's pipeline is: parse (tree-sitter CST) → convert (parse IR) → scan definitions → load (KB). Type information is only fully available after loading. But desugaring and some resolution decisions need type info earlier.

## Key Fact: Type Variables ARE Logic Variables

In the current implementation, type variables (`?T` in sort definitions and operation signatures) and logic variables (`?x` in rule bodies) use the **same representation**: `Term::Var(VarId)`.

| Source | KB representation |
|--------|-------------------|
| `sort T = ?` in sort body | `SortAlias(T, Var(?))` fact; the `?` IS stored as a Var term |
| `?T` in operation param type | `Var(VarId)` directly in the operation's `Fn` named_args |
| `?x` in rule body | `Var(VarId)` — structurally identical |
| `Stream[T = Int]` (instantiation) | `Fn("Stream", T: Ref("Int"))` — **not** unification, just structured data |

This means: type parameters and logic variables are **unified at the KB level**. The distinction is a user-level/parse-time concept only.

### Implication: Two paths for type instantiation

**Path A: Instantiation = unification.** Since `?T` is `Var(VarId)`, binding `Stream[T = Int]` could be literal unification of `?T` with `Int`. Type resolution IS query resolution. Most "types-are-terms" approach.

**Path B: Instantiation stays syntactic.** `Stream[T = Int]` remains `Fn("Stream", T: Ref("Int"))` — a concrete term. The KB never unifies type vars during instantiation. Simpler, current behavior.

### Key Insight: Type Checking = Logic Procedures Against the KB

Since types are terms and sort relationships are facts, **type checking is just querying the KB**. There is no separate type checker — the reasoning engine IS the type checker.

Concretely, all type-level operations reduce to KB queries/rules:

```
-- Entity-of: 1-level constructor → parent sort (non-transitive).
-- EntityOf(entity, parent) facts are emitted by the loader.
rule is_entity_of(?A, ?B) :- EntityOf(?A, ?B)

-- Spec refinement: transitive closure of Requires chain.
-- Requires(sort_ref, base_sort, spec_inst) facts are emitted by the loader.
rule refines(?A, ?B_inst) :- Requires(?A, ?, ?B_inst)
rule refines(?A, ?C_inst) :- Requires(?A, ?B, ?), refines(?B, ?C_inst)

-- Type compatibility: can type A be used where type B is expected?
rule type_compatible(?A, ?A)                          -- same type (unification)
rule type_compatible(?A, ?B) :- is_entity_of(?A, ?B)  -- entity subtyping
rule type_compatible(?A, ?B) :- refines(?A, ?B)       -- spec refinement

-- Spec satisfaction: does Int satisfy Eq?
-- = conjunctive query: apply {T → Int} to Eq's fact template, check all match
rule satisfies(?Sort, ?Spec) :-
    template_of(?Spec, ?Facts),
    all_facts_present(?Facts, {?Spec.T -> ?Sort})

-- Operation dispatch: which sort's `map` applies?
-- = query for Operation(map, ...) facts, filter by argument sort
rule resolves_to(?op_name, ?args, ?sort) :-
    Operation(?op_name, ?params) in ?sort,
    args_match(?args, ?params)
```

This means:
- **No separate type checker** — reuse the query/rule engine
- **Typing rules are KB facts** — extensible (agents can add new subtyping rules)
- **Type errors are query failures** — "no substitution σ satisfies the fact-set template"
- **The typing lattice is emergent** from KB facts, not a separate data structure
- **Incremental**: as agents assert new facts (implementations, sort relations), the typing landscape evolves dynamically

The Isabelle formalization already works this way: `is_subtype` is defined as the reflexive-transitive closure of entity-of relationships (which is just `set (kb_entity_of kb)` — facts). Extending this to spec satisfaction and operation dispatch is natural.

This resolves the "when does type resolution happen?" question (OQ1): **whenever you query**. Type resolution is not a pipeline stage — it's a query against the current KB state. Early checks use the available facts; later checks use more facts. Missing facts = obligations, not errors.

### Implementation Status: The Engine Already Exists

The Rust implementation already has the core machinery for this approach:

| Component | Status | Location |
|-----------|--------|----------|
| SLD resolution (backward chaining) | **Done** | `kb/resolve.rs` — conjunctive goals, shared vars |
| Pattern matching with variables | **Done** | `kb/mod.rs` — `query(pattern)` |
| Discrimination tree index | **Done** | `kb/discrim.rs` — structural matching |
| Equational rewriting | **Done** | `kb/resolve.rs` — `simplify()` |
| Indexes (by_sort, by_functor, by_domain) | **Done** | `kb/mod.rs` |
| Entity subtyping (EntityOf facts + in-memory indexes) | **Done** | `kb/mod.rs`, `kb/load.rs` |
| Forward chaining | Missing | Automatic fact derivation |
| Constraint/denial checking | Missing | Integrity enforcement |
| Negation-as-failure | Missing | `not(pattern)` in queries |
| Tabling/memoization | Missing | Cached recursive solutions |

The SLD resolver (`resolve(goals, config) -> Vec<Solution>`) already supports conjunctive goals with shared variables — which is exactly what fact-set matching needs. **Type checking as logic procedures can be built on top of `resolve()` today.**

### Type Application: Resolve On Demand, Don't Materialize

When you write `List[T = Int]`, the question is whether to **materialize** concrete facts for the instantiation or **resolve on demand**.

**Materialize** = generate concrete facts:
```
-- From template Operation(length, l: List, _returns: Int) with List.T = ?
-- Generate: Operation(length, l: List[T=Int], _returns: Int)
```
Pro: fast lookup. Con: combinatorial explosion (N instantiations × M operations).

**Resolve on demand** = keep templates with variables, use SLD resolution with substitution:
```
-- Query: "what operations does List[T=Int] have?"
-- = resolve([Operation(?name, ?params) in List], {T → Int})
-- SLD resolver applies substitution, returns matching operations
```
Pro: no explosion, lazy, naturally incremental. Con: every type query is a resolution step.

Since SLD resolution already exists and handles exactly this (conjunctive goals with substitution), **on-demand resolution is the right default**. Tabling (caching resolved results) can be added later if performance requires it.

This means type application `List[T = Int]` is NOT a separate mechanism — it's a parameterized query. No new code needed for type instantiation; just express it as goals for the resolver.

## What Is Typing?

In Anthill, sorts are terms. A logical variable `?x` is a term, and it is also a valid sort (`sort T = ?`). This means every term always has a sort — the sort just might be `?` (fully unspecified).

### Typing is a constraint expression

The **typing of a term** is not a judgment ("typed or untyped") — it is a **constraint expression** over the term, composed from facts and rules in the KB.

For example, the typing of `foo(?x)` with `requires gt(?x, 0)` is the constraint:

```
∃S: HasSort(?x, S), HasOperation(gt, S, Int, Bool), ...
```

This expression IS the typing. The question is not "is this typed?" but "what are the constraints?"

### Three levels of typedness

Since typing formulas may contain **free logical variables** (which is fundamental — `?` is central to Anthill), the typing status of a term falls into three categories:

| Level | Condition | Meaning |
|-------|-----------|---------|
| **Ill-typed** | `¬∃ binding: constraints hold` | Contradiction found — no binding can satisfy the constraints |
| **Well-typed** | `∃ binding: constraints hold` | Some binding satisfies constraints — the term is OK |
| **Universally typed** | `∀ bindings: constraints hold` | All bindings satisfy constraints — fully resolved |

Note: the middle state is **not** `¬¬typed(x)` (which under CWA collapses to `typed(x)`). It is genuinely the state where constraints have free variables and are satisfiable for some but not all bindings:

```
operation foo(x: ?T) -> ?T
  requires gt(x, 0)
```

- `?T = Int` → well-typed (gt on Int exists)
- `?T = String` → ill-typed (gt on String may not exist)
- The formula has free variable `?T`, so typing is **indeterminate** until `?T` is bound

### Typing and the development lifecycle

This three-level classification maps directly to the specification workflow:

- **During specification**: most terms are well-typed — constraints exist but free variables remain. The developer is still refining.
- **Complete spec**: all constraints are internally consistent. This does NOT mean "no `?` remain" — abstract sort definitions like `sort Eq { sort T = ? }` are complete specs with intentional free variables. The `?` is a declared parameter, not an unfilled hole. A spec is complete when its constraints are satisfiable for all valid bindings of its declared parameters.
- **Ill-typed at any stage**: contradiction detected — report error immediately.

The distinction: a **well-typed** term has some bindings that work. A **complete spec** has constraints that work for all valid bindings of its declared parameters — the free variables are intentional (parameters), not accidental (holes).

Conversational specification (see `docs/usage-scenarios/conversational-specification.md`) is the process of moving from accidental `?` (holes the developer hasn't thought about yet) to either concrete types or intentional `?` (declared parameters).

### No separate type checker

Since typing is a constraint expression over KB facts, **there is no separate type checker**. The KB query/resolution engine IS the type checker:

- **Type inference** = constraint solving: find bindings for free sort variables that satisfy all constraints
- **Type checking** = constraint verification: given concrete bindings, check that all constraints hold
- **Type error** = unsatisfiable constraints: no binding exists

The query engine already supports all three operations via SLD resolution with unification.

### For each KB snapshot, typing is decidable

For any concrete KB state (a finite set of facts and rules), `typed(t) ∨ ¬typed(t)` holds for each term — LEM applies because the KB is finite and the constraint language is decidable. The "indeterminate" state exists not because of logical incompleteness, but because the **formula itself has free variables**. At each snapshot, for each specific binding of free variables, the answer is definite.

## The Problem

The kernel language spec says "types are terms" — sort identifiers are just terms. This is powerful but means there's no separate "type system" in the traditional sense. Instead, sort relationships are facts in the KB:

```
-- These are KB facts, not a separate type lattice:
fact red <: Color
fact green <: Color
fact blue <: Color
fact Eq[T = Int]     -- Int satisfies Eq
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

### OQ1. When does type resolution happen? (partially resolved)

Since typing is constraint solving via KB queries, type resolution happens **whenever you query** — it is not a pipeline stage. See "Key Insight: Type Checking = Logic Procedures Against the KB" above.

The remaining question is about **sugar desugaring** (OQ5.2/OQ5.3) which needs type info before full KB loading.

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

**OQ2.3.** For a sort expression `Stream[T = Account]`:
  - Is this a valid instantiation? → need to check `T` is a sort parameter of `Stream`
  - What operations are available? → need to know `Stream`'s operations
  - Does it satisfy any spec sorts? → need to check `fact SomeSpec[T = Stream]`

### OQ3. Type inference vs type checking (partially resolved)

The "What Is Typing?" section above resolves the fundamental question: type inference and type checking are **the same operation** — constraint solving over sort variables via KB queries.

- **Type inference** = find bindings for free sort variables that satisfy all constraints (open-ended constraint solving)
- **Type checking** = given specific bindings, verify all constraints hold (ground constraint checking)

Both reduce to SLD resolution against the KB. There is no separate inference pass — unification during query resolution IS type inference.

**OQ3.2.** (Remaining) How much inference is needed for sort-defined syntax sugar? If `[?x | ?x <- expr]` needs to know that `expr` is a `Stream` to desugar, then at minimum we need to infer the sort of `expr`. Options:
  - Require explicit annotation: `[?x | ?x <- (expr : Stream[T = Int])]` — no inference needed
  - Infer from context: if `expr` is a call to an operation returning `Stream[T = Int]`, propagate that
  - Infer from operations: if `expr` supports `flatMap`/`guard`/`pure`, it's comprehension-compatible (structural typing)

**OQ3.3.** Bidirectional type checking? Some systems propagate type info both top-down (expected type) and bottom-up (inferred type). E.g., `let s : Stream[T = Int] = query account(?, ?, ?bal)` — the expected type `Stream[T = Int]` constrains how `query` is desugared. Is bidirectional checking worth the complexity?

**OQ3.4.** Literal desugaring. The untyped term language includes `SetLiteral`, `TupleLiteral`, and `ListLiteral` (Proposal 019) — syntactic forms that the typing process must rewrite into concrete operations. `[a, b, c]` desugars via `Collection.add`/`empty`, `[?h | ?t]` desugars via `Iteration.split`. Both algebras are parameterized by an effect set `Effect` (since effectful types like `Stream` also need literal support). The typing process must define:
  - How expected types propagate to literal positions (field types, parameter types, return types)
  - What happens when no expected type is available (default to `List`? error?)
  - How effects propagate through literal desugaring (the `Effect` parameter of Collection/Iteration)

### OQ4. Sort resolution for operations (partially resolved)

Operation dispatch is a primary driver for typing. When an unresolved name `map(x, f)` appears, the system generates a constraint query:

```
:- HasSort(x, ?S), HasOperation(?S, map, arity=2, ...)
```

Then runs it against the KB:
- **One answer** → resolved, rewrite `map` to the qualified form (e.g., `List.map`)
- **Many answers** → ambiguity error (but see specificity below)
- **Zero answers** → unknown operation error

**Specificity ordering.** If both `List.map` and `Monad.map` match (because `fact Monad[F = List]`), prefer the more specific sort — the one that refines the other. Since `List` satisfies `Monad` via spec refinement, `List.map` wins.

**Why this matters now.** Currently anthill has no unresolved operation calls — rules/facts use functors (just symbols), and declared operations resolve by scope/import. But operation dispatch becomes necessary in two cases:

1. **Expressions** — once anthill has expressions (`let x = map(myList, f)`), ambiguous operation names require constraint solving to dispatch.
2. **Host language realization** — generating interfaces for host languages (Rust, Java, etc.) requires concrete types. Even without expressions in anthill:

```
-- anthill:
sort Eq {
  sort T = ?
  operation eq(a: T, b: T) -> Bool
}
```
```rust
// generated Rust — ? maps to generic parameter, OK:
trait Eq { type T; fn eq(a: &Self::T, b: &Self::T) -> bool; }
```

But an accidental `?` (not a declared parameter):
```
operation process(x: ?V) -> ?V    -- ?V is not declared anywhere
```
cannot generate a host language signature — the host language needs an answer.

**Two drivers for typing, two levels of resolution:**

| Driver | When | Resolution needed |
|---|---|---|
| **Operation dispatch** | Expressions with ambiguous names | Well-typed — enough to pick one answer |
| **Realization** | Generating host language interfaces | All accidental `?` eliminated — intentional parameters become host generics, everything else concrete |

The realization boundary is where accidental `?` must be zero. Intentional `?` (declared sort parameters) map to host language generics/type parameters.

**OQ4.1.** (Remaining) Fallback when constraint solving doesn't disambiguate. Options:
  - **Qualified names**: `Stream.map(s, f)` — explicit, always available as escape hatch
  - **Import-based priority**: the current scope's imports determine preference
  - **Error**: require the user to disambiguate

**OQ4.2.** Can operations be **overloaded** across sorts? If `add` exists on both `Int` and `Float`, is `add(1, 2)` resolved by argument types? (Yes — this is exactly the constraint query mechanism above.)

**OQ4.3.** How does this interact with spec sorts? If `Numeric` declares `add`, and both `Int` and `Float` satisfy `Numeric`, then `add` is polymorphic. The specificity ordering handles this: if the argument is known to be `Int`, prefer `Int.add` over `Numeric.add`.

### OQ5. Types-are-terms implications

**OQ5.1.** Since sorts are terms, sort resolution IS term resolution in the KB. Checking "is `X` of sort `S`?" is equivalent to querying `fact X : S` (or checking the entity-of relationship). Should type resolution literally be a KB query?

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
    │ (sum types: Color,  │  │ (grouping) │  │ (List[T=?],     │
    │  Account, List)     │  │            │  │  Stream[T=?])   │
    └──────────┬─────────┘  └────────────┘  └────────┬────────┘
               │                                      │
    ┌──────────┴─────────┐              ┌─────────────┴────────┐
    │ Entities/ctors      │              │ Instantiated sorts   │
    │ (red, account,      │              │ (List[T=Int],        │
    │  cons, nil)         │              │  Stream[T=Account])  │
    └──────────┬─────────┘              └──────────────────────┘
               │
    ┌──────────┴─────────┐
    │ Singleton sorts     │  — entity instances AS sorts: Draft, kb, nil
    │ (each instance is   │    (derived by rule, not asserted individually)
    │  its own type)      │
    └──────────┬─────────┘
               │
    ┌──────────┴─────────┐
    │ Literals            │
    │ (Int, Float,        │
    │  String, Bool)      │
    └────────────────────┘
```

### Entity Instances as Sorts (Singleton Types)

A key design decision: **every entity instance is also a sort** — a singleton type containing exactly itself. This is not a special mechanism but a natural consequence of "types are terms": if `SortId = TermId`, then any term can appear where a sort is expected.

**The rule, not the fact.** This property is expressed as a general law in the KB, not as per-entity fact assertions:

The loader already emits `EntityOf(entity, parent)` for every entity in a sort body. This single fact is sufficient — an entity is a valid sort if and only if an `EntityOf` fact exists for it. No new predicate is needed.

The `is_entity_of` rule (implemented in `typing.anthill`) handles this:

```
-- 1-level entity → parent sort (non-transitive)
rule is_entity_of(?A, ?B) :- EntityOf(?A, ?B)
```

When type resolution checks whether `kb` is a valid sort (e.g., in `Modifies[kb]`), it queries `EntityOf(kb, ?)`. If found, `kb` is an entity of some sort. No additional `is_sort` predicate or `Sort(kb, Singleton)` facts are needed.

The critical point: this is **derived knowledge, not asserted facts**. The loader emits `EntityOf(Draft, WorkStatus)` because `entity Draft` appears inside `sort WorkStatus`. If the entity declaration is retracted, the `EntityOf` fact disappears, and `Draft` ceases to be a valid entity. Compare:

| Approach | Per-entity `Sort(Draft, Singleton)` facts | `EntityOf(Draft, WorkStatus)` (existing) |
|----------|-------------------------------------------|----------------------------------------|
| Mechanism | Loader emits N extra facts | Already emitted — no new facts |
| Sort validity | Separate predicate to check | Query EntityOf (existing) |
| Retraction | Must track and retract separately | Automatic with entity retraction |
| New entities | Must remember to emit | Already part of entity loading |

**Spectrum of singleton types.** Different entity forms give different strength of singleton:

| Entity form | As sort | Inhabitants | Example |
|---|---|---|---|
| Nullary (`entity Draft`) | Singleton — exactly one value | `Draft` | `Draft <: WorkStatus` |
| With fields (`entity Account(id, bal)`) | Refinement family — each application is a sort | `Account(42, 100)` | `Account(42, 100) <: Account` |
| Parameterized (`entity Pair(fst: ?A, snd: ?B)`) | Dependent family — sort varies with params | `Pair(Int, String)` | `Pair(Int, String) <: Pair` |

For the effect system, the **nullary case** is the primary need (resource identifiers like `kb`, `store`). The refinement and dependent cases are powerful but can be deferred.

**Connection to effects.** With entity-instances-as-sorts, effect targets become regular sort parameters:

```
sort KB { entity kb }

-- kb is both a value of sort KB AND a singleton sort
-- Therefore Modifies[kb] is a regular sort instantiation:
operation mutate(kb: KB) -> KB
  effects (Modifies[kb])           -- kb is a sort parameter, not a special name

-- Abstract effects work uniformly:
sort Stream {
  sort E = ?                       -- abstract effect parameter
  operation next(s: Stream) -> Option[T = ?Elem]
    effects (E)                    -- E could be Reads{kb}, Modifies{store}, etc.
}
```

No special effect-target resolution needed — effect parameters are sort parameters, entity instances are sorts, and the existing sort instantiation / subtyping machinery handles everything:

- `Modifies[kb]` is valid because `EntityOf(kb, KB)` exists
- `effects (E)` where `E = Modifies[kb]` works by substitution
- Whether `Modifies[kb] <: Modifies[KB]` holds depends on variance — see OQ5c below

**Why this is not full dependent types.** This looks like dependent types, but the complexity is bounded:

1. **No Pi/Sigma types** — no function types that depend on values (that's proposal 002's territory)
2. **No type-level computation** — singleton sorts are just facts, not computed types
3. **Decidability preserved** — checking `kb <: KB` is a KB query (fact lookup), not a reduction
4. **No universe hierarchy** — `Sort` is the only meta-level, no `Sort : Sort : Sort ...`

The key insight: in a system where "type checking = KB querying" and "types are terms", singleton types are free — they're just the observation that entity terms can appear in sort positions, and the KB's existing unification handles it.

### OQ5c. Variance of Parameterized Sorts

Anthill currently has no notion of variance. Given `EntityOf(kb, KB)`, does `Modifies[kb] <: Modifies[KB]` hold? This depends on whether the sort parameter of `Modifies` is covariant.

Rather than introducing variance annotations (like Scala's `+T`/`-T`), variance can be expressed as **subtyping rules** — consistent with "type checking = KB querying":

```
-- Modifies is covariant: if A <: B then Modifies[A] <: Modifies[B]
rule is_subtype(Modifies[?A], Modifies[?B]) :- is_subtype(?A, ?B)

-- Reads is covariant
rule is_subtype(Reads[?A], Reads[?B]) :- is_subtype(?A, ?B)

-- Fn is contravariant in input, covariant in output
rule is_subtype(Fn[A = ?A2, R = ?R1], Fn[A = ?A1, R = ?R2])
  :- is_subtype(?A1, ?A2), is_subtype(?R1, ?R2)
```

Each parameterized sort explicitly declares how subtyping propagates through its parameters. No special annotation mechanism, no compiler inference — just rules in the KB.

**Trade-offs:**

- **Pro**: no new language feature — pure rules, extensible by agents
- **Pro**: each sort controls its own variance (some parameters covariant, others not)
- **Pro**: non-standard variance patterns are expressible (e.g., invariant for mutable containers, phantom parameters)
- **Con**: requires writing explicit subtyping rules for each parameterized sort
- **Con**: no static check that the declared variance is sound (a covariant rule on a mutable container would be unsound)

**OQ5c.1.** Should there be a convenience mechanism to derive variance rules from parameter usage patterns? E.g., if a parameter only appears in return types of operations, automatically generate a covariant rule. This would be sugar over the explicit rules, not a separate mechanism.

**OQ5c.2.** How to ensure soundness? In traditional type systems, the compiler checks that declared variance is consistent with usage (covariant parameters can't appear in input positions). With rules-as-variance, unsound rules are expressible. Options: (a) trust the author, (b) add a checking rule/constraint that validates variance declarations against operation signatures, (c) defer — soundness checking is a concern for a later iteration.

**OQ5c.3.** Default variance: should parameterized sorts without explicit subtyping rules be **invariant** by default? This is the safe choice — `List[Int]` and `List[Nat]` are unrelated unless a rule says otherwise.

### OQ5d. Execution Model: Primitives, Procedural Chunks, and Residuals

#### Primitive classification

Typing operations divide into **truly primitive** (require procedural/oracle access) and **derivable** (expressible as rules over KB facts):

**Meta-level primitives** (procedural — inspect variable binding state):

| Primitive | Meaning | Use case |
|---|---|---|
| `nonvar(?x)` | Top-level is not a variable — functor visible | `entity_of` needs to see the constructor |
| `ground(?x)` | Fully concrete, no variables anywhere | `gt` needs actual values to compare |

These cannot be expressed as KB queries because they inspect the **current state of resolution**, not KB content.

**Oracle primitives** (access KB internals, defined in `anthill.reflect`):

| Primitive | Meaning |
|---|---|
| `reify` / `reflect` | Term structure decomposition/construction |
| `execute` | Run a query against the KB |
| `sort_template` / `instantiation_query` | Extract/instantiate sort fact templates |
| `sorts` / `operations` / `constructors` / `fields` / `rules` / `descriptions` | KB index access |
| `apply_subst` / `compose` | Substitution operations |

**Derivable as rules** (everything else):

```
-- Entity-of: 1-level entity → parent sort (non-transitive).
-- EntityOf(entity, parent) facts are emitted by the loader.
rule is_entity_of(?A, ?B) :- EntityOf(?A, ?B)

-- Spec refinement: transitive closure of Requires chain.
rule refines(?A, ?B_inst) :- Requires(?A, ?, ?B_inst)
rule refines(?A, ?C_inst) :- Requires(?A, ?B, ?), refines(?B, ?C_inst)

-- Type compatibility: can type A be used where type B is expected?
rule type_compatible(?A, ?A)                          -- same type (unification)
rule type_compatible(?A, ?B) :- is_entity_of(?A, ?B)  -- entity subtyping
rule type_compatible(?A, ?B) :- refines(?A, ?B)       -- spec refinement

-- Entity-of with nonvar guard (inspect functor first)
rule entity_of(?x, ?sort) :- nonvar(?x), EntityOf(?x, ?sort)

-- Operation dispatch: constraint query (uses is_entity_of directly)
-- OperationInfo facts have named args: name (Symbol), sort_context, params, return_type, effects
rule resolve_operation(?name, ?x, ?info)
  :- is_entity_of(?x, ?S), OperationInfo(name: ?name, sort_context: some(value: ?S), params: ?_, return_type: ?_, effects: ?_)
```

#### Operation Auto-Binding

Operations in parametric sorts are implicitly parameterized — like type parameters (`sort T = ?`), they are logical variables bound at instantiation. When a sort declares `fact S[T]` (spec satisfaction), operations with matching names and compatible signatures are **automatically unified**. No explicit binding is required.

The `resolve_operation` rules extend to handle inherited operations:

```
-- Direct: operation declared on entity's own sort
rule resolve_operation(?name, ?x, ?info)
  :- is_entity_of(?x, ?S),
     OperationInfo(name: ?name, sort_context: some(value: ?S),
                   params: ?_, return_type: ?_, effects: ?_)

-- Inherited: from spec via refines chain, not overridden locally
rule resolve_operation(?name, ?x, ?info)
  :- is_entity_of(?x, ?S),
     refines(?S, ?Spec_inst),
     spec_sort(?Spec_inst, ?Spec),
     OperationInfo(name: ?name, sort_context: some(value: ?Spec),
                   params: ?p, return_type: ?r, effects: ?e),
     not(overrides(?S, ?name))

-- overrides: sort S has its own version of operation ?name
rule overrides(?S, ?name)
  :- OperationInfo(name: ?name, sort_context: some(value: ?S),
                   params: ?_, return_type: ?_, effects: ?_)
```

The `not(overrides(?S, ?name))` clause uses negation-as-failure (NAF): an operation is inherited only if the sort does not define its own version.

**Trace: `resolve_operation(head, ls_entity, ?info)` through LogicalStream → Stream.**

1. `is_entity_of(ls_entity, LogicalStream)` — succeeds (entity fact).
2. Try direct rule: `OperationInfo(name: head, sort_context: some(value: LogicalStream), ...)` — **fails** (LogicalStream does not declare `head`).
3. Try inherited rule:
   - `refines(LogicalStream, Stream[T])` — succeeds (LogicalStream has `fact Stream[T]`).
   - `spec_sort(Stream[T], Stream)` — extracts base sort.
   - `OperationInfo(name: head, sort_context: some(value: Stream), ...)` — **succeeds** (Stream declares `head`).
   - `not(overrides(LogicalStream, head))` — succeeds (LogicalStream has no `head`).
4. Result: `?info` binds to Stream's `head` operation info.

Contrast with `splitFirst`: LogicalStream declares its own `splitFirst`, so `overrides(LogicalStream, splitFirst)` succeeds, and the inherited rule is blocked — the direct rule fires instead, returning LogicalStream's version.

#### Procedural chunks in Term

The meta-level primitives (`nonvar`, `ground`) and oracle operations need a way to execute procedurally during SLD resolution. This requires a new `Term` variant — a **procedural chunk**: a term that, when encountered as a goal, calls a handler with the current resolution context.

```
-- Conceptually, a Term can be:
--   Fn, Var, Ref, Literal, Quoted, Bottom   (existing)
--   Procedure(handler, args)                 (new)
```

When SLD resolution encounters a `Procedure` goal, it invokes the handler with:
- The current substitution (variable bindings)
- The arguments

The handler returns one of:
- **Success** with substitution updates
- **Failure** (goal cannot be satisfied)
- **Delay** (goal cannot be evaluated yet — insufficient bindings)

#### Delay handling in SLD resolution

When a procedural chunk (or a `nonvar`/`ground` guard) returns DELAY, the SLD resolver has strategies:

1. **Reorder**: put the delayed goal at the end of the goal list, try other goals first. If other goals bind the needed variables, retry succeeds.
2. **Attach to variables**: associate the delayed goal with its unbound variables. When a variable gets bound (through unification elsewhere), wake up the delayed goal and re-evaluate.
3. **Residualize**: if resolution completes with goals still delayed, return them as **residuals** — unresolved constraints.

The `resolved(?x)` guard primitive provides a clean separation:

```
-- entity_of requires nonvar to inspect the functor:
rule entity_of(?x, ?sort) :- nonvar(?x), EntityOf(?x, ?sort)

-- gt requires ground values to compare:
rule can_compare(?x, ?y, ?result) :- ground(?x), ground(?y), gt(?x, ?y)
```

If `nonvar(?x)` encounters an unbound `?x`, it returns DELAY. The resolver reorders or attaches to `?x`. When `?x` gets bound through another goal, `nonvar(?x)` succeeds, and `entity_of` proceeds.

#### Query execution

A query returns a stream of fully-resolved substitutions. Unresolvable goals (delayed constraints on unbound variables) are reported via the `Error` effect — they are not silently mixed into the result stream.

```
operation execute(query: LogicalQuery)
  -> Stream[T = Substitution, E = Read[kb]]
  effects (Read{kb}, Error)
```

- **Stream yields only fully-resolved substitutions** — each element is a complete answer.
- **Unresolvable goals → Error** — if a goal cannot be resolved (e.g., `nonvar(?X)` where `?X` remains unbound after exhausting all rules), execution raises an error rather than returning a conditional answer the caller must inspect.

| Stream | Error | Typing status |
|---|---|---|
| Non-empty | No | Fully typed — solutions exist |
| Empty | No | Ill-typed — no solutions |
| Any | Yes | Partially resolved — unresolvable constraints reported |

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
  - **EntityOf** (`<:`): `red <: Color` — constructors are entities of their enclosing sort (1-level, non-transitive)
  - **Spec satisfaction**: `fact Eq[T = Int]` — Int satisfies the Eq spec
  - **Type parameter binding**: `List[T = Int]` — T is bound to Int
  - **Type alias**: `sort Money = Int` — Money is another name for Int

Are these all the same relation (subtyping)? Or distinct relations with different semantics?

**OQ5b.4. Sort of sorts.** What is the sort of `Int`? Options:
  - `Int : Sort` — all sort names have sort `Sort`
  - `Int : Type` — with `Type` as a universe (á la Haskell's `Type` kind)
  - No meta-sort — sort names are just terms, not typed themselves
  - Currently: sort declarations create `SortInfo(name: Symbol, definition: Term, constructors: [...], operations: [...], parameters: [...], requires: [...])` facts with sort `Sort` and domain = enclosing scope

**OQ5b.5. Spec sorts and the lattice.** Spec sorts (Eq, Ordered, Numeric) are at a different level — they classify sorts, not terms. `Eq[T = Int]` says "Int as a sort satisfies Eq." This is a **sort-level predicate**, not a term-level type. Should the lattice distinguish:
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
  { SortInfo(name: T, ...),
    OperationInfo(name: eq, sort_context: some(value: Eq), params: [FieldInfo(name: "a", type_name: T), FieldInfo(name: "b", type_name: T)], return_type: Bool, ...) }
```

Asserting `fact Eq[T = Int]` means: apply substitution `{T → Int}` and check the KB:

```
Check against KB:
  SortInfo(name: Int, ...) ?          → ✓ Int is a declared sort
  OperationInfo(name: eq, sort_context: some(value: Eq), params: [FieldInfo(name: "a", type_name: Int), ...], return_type: Bool, ...) ?  → ✓ or ✗
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

**Instantiation checking.** Given `Eq[T = Int]`:
1. Look up the fact template for `Eq`
2. Apply substitution `{T → Int}` to all patterns in the template
3. Query the KB for each instantiated pattern
4. Report: which facts exist, which are missing (= obligations)

**Spec satisfaction.** `fact Eq[T = Int]` asserts that Int satisfies Eq. The system:
1. Performs instantiation checking (above)
2. Missing facts become **open obligations** — pheromone signals for agents to fulfill
3. Full match = satisfaction verified

**Type-compatible matching.** When checking if `Operation(eq, a: Int, b: Int, _returns: Bool)` exists, allow compatible matches: if `red` is an entity of `Color`, an operation `eq(a: Color, b: Color) -> Bool` could match with `red` as argument (via `type_compatible`).

#### Analogies in other systems

| System | Mechanism | Anthill equivalent |
|--------|-----------|-------------------|
| ML module signatures | Signature matching: does module M provide types/values declared in sig S? | Fact-set matching: does KB provide facts declared in sort S? |
| Rust trait impl | Does `impl Eq for Int` provide all required methods? | Does `fact Eq[T = Int]` + KB have all required operation facts? |
| TypeScript structural typing | Does this object have the right shape? | Does this KB region have the right fact shape? |
| Algebraic specification (Maude) | Theory morphism: map spec axioms to implementation | Fact-set substitution: map sort template to KB facts |

#### Open questions

**OQ6.1.** Is fact-set matching a kernel primitive, or derived from single-fact queries? It could be implemented as: for each pattern in the template, run `query(kb, pattern)`. But the **consistency** requirement (same `?T` binding across all queries) makes it more than just independent queries.

**OQ6.2.** How does fact-set matching relate to the query system (010)? A fact-set match is essentially a **conjunctive query** with shared variables: "find substitution σ such that all patterns in the template match KB facts under σ." This is exactly what rule bodies do.

**OQ6.3.** What happens on partial match? Options:
  - (a) **Obligation generation**: missing facts become work items / pheromone signals. This is the Anthill way — the colony discovers what's needed.
  - (b) **Error**: partial match = type error. Strict, catches problems early.
  - (c) **Conditional**: the sort is "partially satisfied" — some operations available, others not yet.

**OQ6.4.** Can fact-set matching be **incremental**? If new facts are asserted, does a previously partial match become complete? E.g., an agent implements `eq` for `Int` after `fact Eq[T = Int]` was asserted — the obligation is now fulfilled.

**OQ6.5.** Does fact-set matching subsume term unification for type instantiation? I.e., is `Stream[T = Int]` also fact-set matching (check that Stream's template with `T = Int` has consistent facts)? Or is instantiation simpler (just syntactic substitution)?

#### Sort definitions as fact templates with variables (not Abstract marker)

**Update (implemented):** `sort T = ?` now emits `SortAlias(T, Var(?))` — the logical variable is stored directly as a `Term::Var`. Both variable (`sort T = ?Element`) and alias (`sort T = Int`) forms use `SortAlias`. The old `SortInfo(T, Abstract)` path has been removed.

The proposed extension: store sort templates with logical variables throughout:

```
-- Implemented: SortAlias with Var
sort Eq { sort T = ? }   →   SortAlias(Eq.T, Var(?))

-- Template extension: all facts use variables
sort Eq { sort T = ? }   →   SortAlias(Eq.T, ?kind)
```

Then the sort definition IS its fact template — a set of facts with logical variables:

```
Template for Eq:
  SortInfo(name: Eq.T, definition: ?def, ...)             -- T's definition is unbound
  OperationInfo(name: eq, sort_context: some(value: Eq),
    params: [FieldInfo(name: "a", type_name: Eq.T), FieldInfo(name: "b", type_name: Eq.T)],
    return_type: Bool, effects: [])

Template for List:
  SortInfo(name: List.T, definition: ?def, ...)           -- T's definition is unbound
  Entity(nil)                                             -- nil constructor
  Entity(cons, head: List.T, tail: List)                  -- cons constructor
  OperationInfo(name: length, ..., return_type: Int, ...) -- length operation
```

Instantiation `Eq[T = Int]` applies `{Eq.T → Int}` and does fact-set matching:

```
After substitution:
  SortInfo(name: Int, ...) ?   → matches SortInfo for Int ✓
  OperationInfo(name: eq, ..., params: [FieldInfo(name: "a", type_name: Int), ...]) ?  → check KB ✓ or generate obligation
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

**OQ7.1.** `Stream[T = Account]` is a sort instantiation — `T` is bound to `Account`. How does the type resolver handle:
  - Checking that `T` is a valid parameter of `Stream`?
  - Propagating the binding into operations? (`map` on `Stream[T = Account]` expects `Account -> ?B`)
  - Nested instantiation? `Stream[T = List[T = Int]]`

**OQ6.2.** How do type variables (`?T`) interact with parametric sorts? In `operation identity(x: ?T) -> ?T`, `?T` is a universally quantified type variable. Resolution at call sites binds `?T` to a concrete sort.

**OQ6.3.** Constraints on type variables? `operation sort_list(l: List[T = ?T]) -> List[T = ?T] requires Ordered[T = ?T]` — the `requires` constrains `?T` to sorts satisfying `Ordered`. How is this checked?

### OQ8. Error reporting

**OQ7.1.** When type resolution fails, what errors are produced?
  - "Unknown sort `Foo`" — name not found
  - "Sort mismatch: expected `Int`, got `String`" — argument type error
  - "Operation `map` is ambiguous: found in `List` and `Stream`" — overload resolution failure
  - "Sort `MyType` does not satisfy `Ordered`" — spec sort not satisfied

**OQ7.2.** Where are errors reported? At the term level (pointing to the specific argument)? At the declaration level (pointing to the operation signature)?

**OQ7.3.** Can errors be deferred? In a logic programming system, some type mismatches might be detected only at query time (when unification fails). Is it acceptable to have "runtime type errors" from unification failure, or should everything be caught statically?

## Required Stdlib Sorts

The type resolution and query system require several new sorts. These form a dependency chain from primitives up to first-class queries.

### Unit (literal, not entity)

`unit` should be a **built-in literal constant** (like `true`, `false`, `42`, `"hello"`), not an entity in a sort. This requires:

- **Grammar**: `unit` as a reserved keyword alongside `true`/`false`
- **Rust**: `Literal::Unit` variant in `enum Literal`
- **Stdlib**: `sort Unit = ?` (abstract/built-in, like `sort Int = ?`)

`unit` is the return type of effectful operations with no meaningful result, and the element type of `guard(cond: Bool) -> LogicalStream[T = Unit]`.

### Pair (prelude)

Product type. Needed for `msplit` result and Substitution bindings.

```
sort anthill.prelude.Pair
  export Pair, pair, fst, snd

  sort A = ?
  sort B = ?
  entity pair(fst: A, snd: B)

  operation fst(p: Pair) -> A
  operation snd(p: Pair) -> B
  rule fst(pair(?a, ?b)) = ?a
  rule snd(pair(?a, ?b)) = ?b
end
```

### Stream (prelude, spec sort) — read-only lazy sequence

A **spec sort** (interface) for read-only lazy sequences. Declares the observation protocol — any sort that supports `msplit` and observation operations can satisfy `Stream`.

```
sort anthill.prelude.Stream
  import anthill.prelude.{Option, Pair, List, Int}
  export Stream, msplit, once, observeOne, observeN, collect

  sort T = ?                -- the implementing sort

  -- Decompose into first element + rest. THE fundamental primitive.
  operation msplit(s: T) -> Option[T = Pair[A = ?Elem, B = T]]

  -- First result only
  operation once(s: T) -> T

  -- Observation: crossing from lazy-land to concrete values
  operation observeOne(s: T) -> Option[T = ?Elem]
  operation observeN(s: T, n: Int) -> List[T = ?Elem]
  operation collect(s: T) -> List[T = ?Elem]
end
```

Database cursors, file readers, and other sequential sources satisfy `Stream`. Note: the element type `?Elem` is determined by the implementing sort's structure (e.g., `LogicalStream[T = Account]` has `?Elem = Account`). This is a higher-kinded relationship — see OQ9.5.

### LogicalStream (prelude, concrete sort) — logic monad

The **logic monad**: a concrete sort for multi-valued computation with backtracking. This is what queries produce.

LogicalStream declares `fact Stream[T]` inside its body — "I provide Stream for any element type T." Stream operations (`head`, `tail`, `splitFirst`, `takeN`, `collect`, `isEmpty`) are inherited, not redeclared. LogicalStream only provides `splitFirst` (Stream's primitive); the rest derive from Stream's rules.

```
sort anthill.prelude.LogicalStream
  import anthill.prelude.{Stream, Option, Pair, Unit, Bool, Int}
  export LogicalStream, empty, pure, mplus, guard, interleave

  sort T = ?

  -- LogicalStream provides Stream for any T.
  -- Stream operations inherited — not redeclared here.
  -- Only splitFirst (Stream's primitive) is provided.
  fact Stream[T]

  -- Stream primitive (required by fact Stream[T])
  operation splitFirst(s: LogicalStream[T = ?A])
    -> Option[T = Pair[A = ?A, B = LogicalStream[T = ?A]]]

  -- Logic-specific construction
  entity empty                                             -- zero results (failure)
  operation pure(x: T) -> LogicalStream                    -- single result
  operation mplus(a: LogicalStream[T = ?A], b: LogicalStream[T = ?A])
    -> LogicalStream[T = ?A]                               -- disjunction
  operation guard(cond: Bool) -> LogicalStream[T = Unit]   -- filter
  operation interleave(a: LogicalStream[T = ?A], b: LogicalStream[T = ?A])
    -> LogicalStream[T = ?A]                               -- fair disjunction

  -- Derived
  rule interleave(?a, ?b) = mplus(pure(?first), interleave(?b, ?rest))
    :- splitFirst(?a) = some(pair(?first, ?rest))
  rule interleave(?a, ?b) = ?b
    :- splitFirst(?a) = none

  -- Monadic operations pending arrow sorts (proposal 002):
  -- flatMap, map, filter, fairFlatMap, ifte
end
```

**Key distinction**: `Stream` declares observation operations with derived rules. `LogicalStream` satisfies Stream (provides `splitFirst`) and adds **construction** (`mplus`, `pure`, `empty`) and **branching** (`guard`). No operation duplication — Stream's `head`/`tail`/`takeN`/`collect`/`isEmpty` are inherited via `fact Stream[T]`.

### Substitution (reflect)

Variable bindings from query/unification results. The output of `execute(query)` is `LogicalStream[T = Substitution]`.

```
-- Added to stdlib/anthill/reflect/reflect.anthill alongside Term/TermRepr:

-- A substitution maps variable names to terms: {?x → t1, ?y → t2, ...}
-- Uses Map from prelude — get, put, keys, values, contains all available.
sort Substitution = Map[K = String, V = Term]

-- Apply a substitution to a term (replace all bound variables)
operation apply_subst(s: Substitution, t: Term) -> Term
  effects (Reads(kb))

-- Compose two substitutions: apply s1 then s2
operation compose(s1: Substitution, s2: Substitution) -> Substitution
```

Substitution is a type alias for `Map[K = String, V = Term]`. All Map operations (`get`, `put`, `keys`, `contains`, etc.) work directly on substitutions. `execute(query)` returns `LogicalStream[T = Substitution]`: each element is a complete set of bindings for one solution.

Lives in `reflect` alongside `Term` and `TermRepr` — it's part of the KB introspection/manipulation API.

### Map (prelude)

General-purpose key-value association. Required by Substitution, useful broadly.

```
sort anthill.prelude.Map
  sort K = ?
  sort V = ?
  requires Eq[T = K]

  entity empty_map
  entity entry(key: K, value: V, rest: Map)

  operation get(m: Map, key: K) -> Option[T = V]
  operation put(m: Map, key: K, value: V) -> Map
  operation contains(m: Map, key: K) -> Bool
  operation remove(m: Map, key: K) -> Map
  operation keys(m: Map) -> List[T = K]
  operation values(m: Map) -> List[T = V]
  operation entries(m: Map) -> List[T = Pair[A = K, B = V]]
  operation size(m: Map) -> Int
end
```

Representation is an association list (`entry(k, v, rest)`) — transparent, pattern-matchable, works with existing rewrite rules. Implementations can optimize to hash maps or trees via realization.

### LogicalQuery (reflect)

First-class query representation. Queries as composable, storable, inspectable KB values.

```
-- Added to stdlib/anthill/reflect/reflect.anthill:

sort LogicalQuery {
  entity pattern_query(term: Term)                        -- single pattern match
  entity sort_query(sort_name: String)                    -- all facts of a sort
  entity conjunction(left: LogicalQuery, right: LogicalQuery)   -- AND (shared vars = join)
  entity disjunction(left: LogicalQuery, right: LogicalQuery)   -- OR
  entity negation(query: LogicalQuery)                    -- NOT (negation-as-failure)
  entity guarded(query: LogicalQuery, condition: Term)    -- filter
  entity projected(query: LogicalQuery, vars: List[T = String]) -- projection
  entity limited(query: LogicalQuery, count: Int)         -- cardinality limit
}

-- Execute a query against the KB
operation execute(query: LogicalQuery) -> LogicalStream[T = Substitution]
  effects (Reads(kb))

-- The type-to-query mapping:
-- Extract a sort's fact template as a LogicalQuery
operation sort_template(sort_name: String) -> LogicalQuery
  effects (Reads(kb))

-- Apply a substitution to a sort template → concrete conjunctive query
-- Eq[T=Int] → instantiation_query("Eq", bind("T", reflect("Int"), empty_subst))
operation instantiation_query(sort_name: String, bindings: Substitution)
  -> LogicalQuery
  effects (Reads(kb))
```

The **type-to-query mapping**: `sort_template` extracts a sort's fact template. `instantiation_query` applies a substitution to produce a concrete conjunctive query. This is how type checking becomes querying:

```
-- "Does Int satisfy Eq?" becomes:
execute(instantiation_query("Eq", bind("T", reflect("Int"), empty_subst)))
-- → checks KB for: SortInfo(name: Int, ...), OperationInfo(name: eq, sort_context: some(value: Eq), ...)
-- → LogicalStream of substitutions (non-empty = satisfied, empty = obligations)
```

### Monad hierarchy (spec sorts, pending proposal 002)

With arrow sorts, the spec sort hierarchy for monadic abstractions:

```
-- Functor: map over a parameterized sort
sort anthill.prelude.Functor
  sort F { sort T = ? }
  sort A = ?
  sort B = ?
  operation map(fa: F[T = A], f: (A) => B) -> F[T = B]
  rule identity: map(?fa, ?x => ?x) = ?fa
end

-- Monad: sequencing with context
sort anthill.prelude.Monad
  requires Functor[F]
  sort A = ?
  sort B = ?
  operation pure(a: A) -> F[T = A]
  operation flatMap(fa: F[T = A], f: (A) => F[T = B]) -> F[T = B]
  rule left_id:  flatMap(pure(?x), ?f) = ?f(?x)
  rule right_id: flatMap(?m, pure) = ?m
end

-- LogicMonad: Monad + backtracking
sort anthill.prelude.LogicMonad
  requires Monad[F]
  sort A = ?
  operation empty() -> F[T = A]
  operation mplus(a: F[T = A], b: F[T = A]) -> F[T = A]
  operation msplit(s: F[T = A]) -> Option[T = Pair[A = A, B = F[T = A]]]
  operation guard(cond: Bool) -> F[T = Unit]
end

-- LogicalStream satisfies all three:
fact Functor[F = LogicalStream]
fact Monad[F = LogicalStream]
fact LogicMonad[F = LogicalStream]
-- Auto-binding: LogicalStream.guard auto-binds to LogicMonad.guard
-- because both have compatible signature (cond: Bool) -> F[T = Unit].
-- LogicalStream.flatMap auto-binds to Monad.flatMap, etc.
-- No explicit operation mapping needed — names match, signatures unify.
```

These spec sorts enable sort-defined syntax sugar (proposal 012): any sort satisfying `Monad` gets comprehension syntax; any sort satisfying `LogicMonad` gets backtracking/choose syntax.

### Sort dependency chain

```
Unit (literal)        ←── guard returns LogicalStream[T = Unit]
    ↑
Pair                  ←── msplit returns Option[T = Pair[...]], Map entries
    ↑
Map                   ←── key-value association (requires Eq on keys)
    ↑
Stream (spec sort)    ←── read-only observation interface
    ↑
LogicalStream         ←── concrete sort, fact Stream[T] (inherits Stream ops)
    ↑
Substitution          ←── Map[K = String, V = Term] (type alias, in reflect)
    ↑
LogicalQuery          ←── first-class queries (depends on Term, LogicalStream, Substitution)
    ↑
Functor/Monad/        ←── spec sorts (depend on arrow sorts / proposal 002)
  LogicMonad
```

### Open questions (new sorts)

**OQ9.1.** Resolved: Stream is a sort with operations and derived rules. Concrete sorts satisfy it by declaring `fact Stream[T]` inside their body and providing the primitive operation (`splitFirst`). Derived operations (`head`, `tail`, `isEmpty`, etc.) are inherited — not redeclared. LogicalStream is one such sort; database cursors, file readers, etc. would be others.

**OQ9.2.** Should observation operations (`observeOne`, `observeN`, `collect`) have `effects (Reads(kb))`? They're consuming lazy values, which might trigger KB reads. Or should effects be on the *stream construction* side only?

**OQ9.3.** Resolved: LogicalStream declares `fact Stream[T]` inside its body — "I provide Stream for any element type T." Note: `fact Stream[T = LogicalStream]` would mean "Stream of LogicalStreams" (wrong). The fact goes inside the sort body, where `T` refers to the sort's own type parameter.

**OQ9.3b.** Resolved: **Operation inheritance via fact (auto-binding).** When a sort declares `fact Stream[T]`, it does NOT redeclare Stream's operations. Operations with matching names are automatically unified via the auto-binding mechanism (see "Operation Auto-Binding" section above). Stream's operations (`head`, `tail`, `splitFirst`, `takeN`, `collect`, `isEmpty`) are automatically available on the satisfying sort. Stream's derived rules (e.g., `head` from `splitFirst`) carry over via the `inherited_operation` path in `resolve_operation`. The satisfying sort only provides the **primitive** operations (e.g., `splitFirst`); derived operations inherit via the refines chain.

This is the **minimal complete definition** pattern. Stream declares which operations are primitive vs derived. LogicalStream implements `splitFirst` (which `overrides` Stream's declaration); `head`, `tail`, `isEmpty` derive from Stream's rules and are inherited (no local override). This avoids duplication and keeps satisfying sorts focused on what's unique to them.

**OQ9.4.** Should `Substitution` be generic over the value type? `Substitution[V = Term]` vs `Substitution[V = TermRepr]` vs always `Term`. Currently pinned to `Term` since that's what the KB stores.

**OQ9.5.** The Monad spec sort hierarchy uses higher-kinded type parameter `F { sort T = ? }`. This requires the type resolution system to handle higher-kinded matching — checking that `LogicalStream` (which has `sort T = ?`) matches the shape expected by `Monad[F]`. How complex is this? The Stream spec sort has the same issue: `sort T = ?` in Stream means "the implementing sort", but the implementing sort itself has an element type parameter. Matching `Stream[T = LogicalStream]` needs to understand that LogicalStream's operations produce results parameterized by LogicalStream's own `T`.

**OQ9.6.** Element type in the Stream spec sort. The Stream spec declares `msplit(s: T) -> Option[T = Pair[A = ?Elem, B = T]]` where `?Elem` is the element type. But `?Elem` is not a declared parameter of Stream — it's implicitly determined by the implementing sort's structure. Should `?Elem` be an explicit parameter? E.g., `sort Stream { sort T = ?; sort Elem = ? }` with `fact Stream[T = LogicalStream, Elem = Account]`? Or is `?Elem` resolved by unification when checking that the implementing sort's `msplit` matches the spec's signature?

**OQ10. NAF vs priority for override semantics.** *Resolved:* NAF implemented via `BuiltinTag::Not` in the SLD resolver. `not(overrides(?S, ?name))` now works directly. Delays on non-ground inner goals (floundering prevention). Sub-resolution uses `max_solutions: 1` for efficiency.

**OQ11. Signature compatibility for auto-binding.** After applying the type substitution from `fact S[T]`, must the satisfying sort's operation signature *unify* with the spec's operation signature, or be *structurally identical*? Unification is more flexible (allows additional parameters or default values) but harder to check. Structural identity is simpler but more restrictive. A middle ground: signatures must be compatible modulo the substitution — same name, same arity, parameter types unify under the substitution.

## Implementation Notes for Auto-Binding

This section documents what code changes are needed to implement operation auto-binding.

### 1. Loader: `fact S[T]` → Requires entity

`load_fact()` in `kb/load.rs` needs to detect `fact S[T]` inside a sort body and also emit a `Requires(sort_ref: domain, base_sort: S, spec_inst: S[T])` fact, reusing the existing Requires entity. Currently `fact` only stores a generic Fact term, invisible to the `refines` chain. The loader must distinguish:

- `fact S[T]` **inside a sort body** → emit both the Fact and a Requires, enabling the refines chain and operation inheritance.
- `fact S[T = Int]` **at namespace level** → emit only the Fact (standalone spec satisfaction, no operation inheritance).

### 2. Resolver: NAF support

`not(overrides(?S, ?name))` requires negation-as-failure in the SLD resolver (`resolve.rs`). This is non-trivial: NAF requires that all variables in the negated goal be bound at the time of evaluation (ground check). Alternative: expose `direct_operation` and `inherited_operation` as separate queries, with the consumer preferring direct over inherited. This avoids NAF entirely at the cost of pushing the override logic to the query consumer.

### 3. Grammar: operation bindings in fact

`fact S[T, combine = add]` needs operation bindings distinguished from type parameter bindings in instantiation syntax. Currently `Name[named_args]` in the grammar only supports sort bindings. Options:

- Reuse the same `named_arg` syntax — the loader distinguishes type vs operation bindings by looking up whether the name refers to a sub-sort or an operation in the spec.
- Add explicit syntax, e.g., `fact S[T, op combine = add]` — more verbose but unambiguous at parse time.

The first option (reuse existing syntax, disambiguate in the loader) is preferred to avoid grammar changes.

### 4. Tests needed

- `resolve_operation` through refines chain (inherited operation resolves correctly).
- Auto-binding: same-named operation on satisfying sort overrides spec operation.
- Explicit rename: `fact S[T, combine = add]` maps `combine` to local `add`.
- Diamond inheritance: sort satisfies two specs that both define `op` — should produce an ambiguity error.

## Relationship to Other Proposals

- **010 (Query System)**: Core query semantics (layers 0-1: pattern matching, conjunctive queries, unification) do **not** need type resolution — they work via unification and rule resolution against the KB directly. Sort annotations like `?x: Account` are user-provided labels that map to `by_sort` lookups, not type inference. The dependency on 011 is only through **syntax sugar** (comprehension desugaring in layer 2+, which is really 012's concern).
- **012 (Sort-Defined Syntax Sugar)**: Sugar activation depends on type resolution — "does this sort support comprehension syntax?" requires knowing the sort and its operations. This is the primary consumer of type resolution.
- **002 (Arrow Sorts)**: Arrow sorts (`A -> B`) introduce function types that need resolution in operation signatures and higher-order operations.

## References

- Current symbol resolution: `rustland/anthill-core/src/intern.rs` (`SymbolTable`, `resolve_in_scope`)
- Current scan-then-load pipeline: `rustland/anthill-core/src/parse/scan.rs`, `rustland/anthill-core/src/kb/load.rs`
- Sort lattice: entity-of facts in KB, `is_subtype` in `Anthill_Kernel.thy`
- Spec sort satisfaction: `fact Eq[T = Int]` pattern in stdlib
- kernel-language.md §3 (sorts), §5 (operations), §8 (semantics)
