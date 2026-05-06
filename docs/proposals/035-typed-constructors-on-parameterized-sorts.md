# 035: Typed Constructors on Parameterized Sorts (Map et al.)

## Status: Accepted

## Depends on: 011 (type resolution), 026 (expression evaluator)

## Relates to: WI-183 (bundle perf — needs a runnable Map builtin), `stdlib/anthill/prelude/map.anthill`, follow-up WI for variance inference algorithm

## Motivation

`stdlib/anthill/prelude/map.anthill` declares `sort Map` with two abstract type parameters (`K`, `V`) and operations `empty`, `put`, `get`, ... Today only the *rules* are present — no Rust-side runtime, and no syntactic way to call `empty()` and pin its type. Anthill is missing the analog of Scala's

```scala
val m: Map[String, Int] = Map.empty[String, Int]
```

— a constructor on a parameterized sort that carries explicit type arguments. The same gap will hit `Set`, `Queue`, any user-defined parametric container.

`Map` deliberately is **not** an `enum`: it has no canonical constructors at the value level (entries vary at runtime). So the entity-constructor sugar `some(value: T) / none()` doesn't apply. We need a different shape.

## What the surface should look like

Three valid forms, in priority order of ergonomics:

```anthill
-- (1) Inferred from expected type
let m: Map[K = String, V = Int] = Map.empty()

-- (2) Inferred from immediate use (the put fixes K, V)
let m = put(Map.empty(), "wi", 1)

-- (3) Explicit type arguments at the call site (the "companion" form)
let m = Map[K = String, V = Int].empty()
```

Form (3) is the Scala-companion analog: `Map[K = String, V = Int]` is an instantiation term that names the sort *with* type bindings, and method dispatch on it produces values typed at those bindings.

## Mechanics

### Runtime: type erasure

Anthill values are tagged at runtime by their concrete shape (`Value::Int`, `Value::Str`, `Value::Entity { functor, .. }`, etc.). A `Map`'s K and V do not need to be observable at runtime — heterogeneity only matters to the type checker. So the runtime representation of `Map[K, V]` is one shape, e.g. `Value::Map(MapHandle)` wrapping a `HashMap<MapKey, Value>` regardless of K and V. `empty()` produces the same value at runtime no matter the type bindings.

### Type checker: three-way resolution

When the type checker sees `Map.empty()` it must produce a `Map[K = ?, V = ?]` and unify the two free `?`s against context. The cases:

1. **Expected-type context exists** (assignment LHS, function return, named arg position) — unify the free vars against the expected type.
2. **No expected type, but enclosing expression constrains** — `put(Map.empty(), "x", 1)` infers `K = String, V = Int` from `put`'s parameter types. Standard HM.
3. **No constraint at all** — the call is ambiguous; the typer requires explicit form (3) or an annotation.

This is no different in spirit from how `[]` (the empty-list literal) is typed today.

### Surface form (3): instantiation-term as receiver

`Map[K = String, V = Int]` is already a valid instantiation term in the grammar — it appears in `requires` clauses and parameter types. The proposal is to allow the same term as a **dot-call receiver**: `Map[K = String, V = Int].empty()` desugars to `empty()` resolved within the scope of `Map`, with K and V bound at the call. The dispatch already exists (sort scope chains), the only work is letting an instantiation term sit on the LHS of a method call.

Concretely the parser change is small: `dot_call : term '.' identifier '(' args ')'` already accepts complex left-sides. We need to confirm the existing grammar treats `Map[K = String, V = Int]` as valid in that left-side position.

### Effect on stdlib `map.anthill`

No change to operation signatures. The existing rules (`get(empty, ?) = none`, etc.) keep working — they're polymorphic in K, V and the typer instantiates them per call site. What lands alongside this proposal is the **Rust builtin set** for `empty / put / get / contains / remove / keys / values / entries / size`, backed by an arena-refcounted `Value::Map(MapHandle)`. That work is the WI-183 implementation; this proposal is the language-level shape that makes it usable from anthill code.

## Non-goals

- **No `companion` keyword.** Scala's companion objects exist because Scala distinguishes types from values rigidly. Anthill sorts already double as namespace-y dispatch points, so we re-use that machinery.
- **No type-parameter erasure check at runtime.** If user code somehow obtains a `Map[String, Int]` and passes it where `Map[Int, String]` is expected, that is a type-checker bug; runtime won't double-check.
- **No reflection over a Map's K/V at runtime.** Adding `Map.key_type(m) -> Type` is a separate ask; the proposal doesn't preclude it.

## Variance, logically

Type parameters in anthill *are* logical variables. That gives co- and contra-variance a clean propositional reading: variance is **a fact about how `type_compatible` is allowed to descend through a parameterized constructor**, expressed as SLD rules — not a syntactic annotation on the declaration.

The existing rules in `typing.anthill`:

```anthill
rule type_compatible(?A, ?A)                     -- reflexive
rule type_compatible(?A, ?B) :- is_entity_of(?A, ?B)
rule type_compatible(?A, ?B) :- refines(?A, ?B_inst), type_compatible(?B_inst, ?B)
```

…say nothing about parameterized constructors yet. `type_compatible(List[T = Cat], List[T = Animal])` succeeds today only by reflexivity (fails) or `is_entity_of` (no). So List is **invariant by default** — the safe choice.

Variance enters as additional rules dispatching on per-(sort, param) facts. Two consequences worth calling out up front:

1. **No variance keyword needed.** Variance is a fact like any other — declared in the same place the sort is, queried by the resolver. Adding new variance kinds (use-site variance, F-bounded, …) is an extra rule, not a grammar change.

2. **Default is invariant.** A user-defined `sort Box { sort T = ? }` with no `Covariant` / `Contravariant` fact is invariant in `T`. Same as Scala default; matches the safe-by-default principle. (Current code is covariant-by-default — see "Risk: existing tests" for migration.)

For `Map[K, V]` specifically: `K` should be invariant (used in both negative and positive position — `put(m, k, _)` is negative, `get(m, k) -> Option[V]` returns nothing parameterized by K), and `V` is naturally covariant for read-only Maps but invariant once `put` is in the picture. Standard answer; no new machinery needed.

### Sketch: `stdlib/anthill/reflect/typing.anthill` patch

Replace the existing parameterized-types compatibility rule (lines 119–132) and add the variance plumbing:

```anthill
-- ────────────────────────────────────────────────────────────────
-- Variance facts (proposal 035)
-- ────────────────────────────────────────────────────────────────
-- Per-sort, per-parameter variance is metadata, not behavior — so it
-- lives in entity facts, not operations. A user (or the prelude)
-- asserts `Covariant(sort, param)` or `Contravariant(sort, param)`
-- to opt the parameter out of the safe default.
--
-- Default (no fact for the pair):           invariant
-- Only Covariant asserted:                  covariant
-- Only Contravariant asserted:              contravariant
-- Both Covariant AND Contravariant asserted: bivariant
--
-- Bivariance is the right answer for parameters that don't appear in
-- input or output positions of any operation on the sort — phantom-
-- type tags, capability carriers, compile-time-only restrictions on
-- T (e.g. `Tagged[Validated, V]`). With both facts present, the two
-- variance arms below both fire and the resolver accepts subtype
-- relations in either direction. This is intentional, not a coherence
-- bug — explicitly co+contra means "T's position is structural;
-- vary it freely along the subtype lattice."

entity Covariant(sort: Symbol, param: Symbol)
entity Contravariant(sort: Symbol, param: Symbol)

-- Example assertions:
fact Covariant(List, T)
fact Contravariant(Function, A)
fact Covariant(Function, B)
-- Phantom carrier: both → bivariant.
fact Covariant(Tagged, T)
fact Contravariant(Tagged, T)
-- Map (mutating container): no facts → K and V invariant.

-- ────────────────────────────────────────────────────────────────
-- Variance-aware parameterized type compatibility
-- ────────────────────────────────────────────────────────────────
-- Replaces the prior covariant-by-default rule. Same base sort on
-- both sides; per-parameter check dispatches on declared variance.

rule type_compatible(
  parameterized(base: sort_ref(name: ?S), bindings: ?Binds1),
  parameterized(base: sort_ref(name: ?S), bindings: ?Binds2))
  :- bindings_variance_compatible(?S, ?Binds1, ?Binds2)

rule bindings_variance_compatible(?, ?, nil)

rule bindings_variance_compatible(?S, ?Actual,
  cons(head: TypeBinding(param: ?P, value: ?V2), tail: ?rest))
  :- list_contains(TypeBinding(param: ?P, value: ?V1), ?Actual),
     check_variance(?S, ?P, ?V1, ?V2),
     bindings_variance_compatible(?S, ?Actual, ?rest)

-- The variance arms consult `effective_*` rather than the entities
-- directly, so an inference layer can plug in later without touching
-- consumers. For the first landing, `effective_*` is just a pass-
-- through over the declared entity.

rule effective_covariant(?S, ?P) :- Covariant(sort: ?S, param: ?P)
rule effective_contravariant(?S, ?P) :- Contravariant(sort: ?S, param: ?P)

-- Covariant arm: actual <: expected.
rule check_variance(?S, ?P, ?V1, ?V2)
  :- effective_covariant(?S, ?P), type_compatible(?V1, ?V2)

-- Contravariant arm: expected <: actual (flipped).
rule check_variance(?S, ?P, ?V1, ?V2)
  :- effective_contravariant(?S, ?P), type_compatible(?V2, ?V1)

-- Default invariant: both directions, only when no variance is in effect.
rule check_variance(?S, ?P, ?V1, ?V2)
  :- not(effective_covariant(?S, ?P)),
     not(effective_contravariant(?S, ?P)),
     type_compatible(?V1, ?V2),
     type_compatible(?V2, ?V1)
```

The three arms are mutually exclusive at the *fact-presence* level: if any variance fact is asserted, the default-invariant arm's negation guards block it. When both Covariant and Contravariant are asserted, both variance arms can fire — the resolver succeeds via either, giving bivariance for free.

**Removed from the existing file:** the covariant-by-default `bindings_compatible` rules (lines 127–132 of typing.anthill). They're subsumed by the new path.

**Cleanup:** the hand-rolled arrow rule (lines 134–140) can stay as a special case (its variance is structural, not per-parameter — `param` and `result` aren't named parameters of a sort), or be rewritten in terms of `Function[A, B]` with `covariant(Function, B)` / `contravariant(Function, A)` facts. Suggest the latter for uniformity in a follow-up patch; not required for the first landing.

### Variance through `requires`

A sort's variance interacts with its `requires` clauses. Concretely:

```anthill
sort Map
  sort K = ?
  fact Covariant(Map, K)        -- (hypothetical)
  requires Eq[T = K]
end
```

If we want `Map[K = Cat] <: Map[K = Animal]`, the substitution must be sound everywhere a `Map[Animal]` was used — including the contexts that consumed its `Eq[Animal]` requirement. The `Map[Cat]` instance only carries `Eq[Cat]`, so soundness depends on `Eq[Cat]` being usable as `Eq[Animal]` — i.e., on **Eq's own variance in T**.

This is just variance composition: `outer-position × inner-position = effective`. Map's covariance in K is sound iff K's effective variance, after composing with its position inside each requires clause, dominates the declared outer variance.

**The proposal handles this lazily.** No load-time check; the existing `refines` chain plus variance-aware `type_compatible` already gets us most of the way. The single rule that closes the loop:

```anthill
-- A is compatible with C if A refines some intermediate B_inst, and
-- B_inst itself is compatible with C under B_inst's own sort's variance.
-- This composes refines (subtype-via-spec) with type_compatible
-- (subtype-via-variance) so widening propagates through requires.
rule type_compatible(?A, ?C)
  :- refines(?A, ?B_inst),
     type_compatible(?B_inst, ?C)
```

Worked example. Suppose `fact Covariant(Eq, T)` (hypothetically — Eq with only the comparison-result-side exposed), `fact Covariant(Map, K)`, and `is_entity_of(Cat, Animal)`:

```
type_compatible(Map[K=Cat], Eq[T=Animal])
  :- refines(Map[K=Cat], Eq[T=Cat])             -- Map's requires, K bound
     type_compatible(Eq[T=Cat], Eq[T=Animal])    -- Eq's variance arm
       :- check_variance(Eq, T, Cat, Animal)
          :- Covariant(Eq, T), type_compatible(Cat, Animal)   -- entity sub
```

If instead Eq were invariant in T (no Covariant fact), the inner `check_variance` falls into the default-invariant arm, which requires `Cat <: Animal AND Animal <: Cat` — fails on Cat/Animal not being equal. So `Map[Cat] <: Map[Animal]` is rejected — *exactly because Eq is invariant in T*. The variance gate is correctly applied at the requires layer.

**Why lazy beats eager here.**

- The eager check has to compute variance for every K-mention inside arbitrarily nested spec instantiations at load time. Doable, but it duplicates the logic the resolver already performs.
- The lazy chain reuses the resolver. A rejected substitution at a use-site already produces an error in the same diagnostic channel as other type-compatibility failures.
- An eager check could give a more directed error message ("Map declared covariant in K but K appears in invariant position of Eq[T = K]"); that's a tooling improvement, additive to the lazy semantics.

**Termination.** The composing rule has the form `type_compatible(?A, ?C) :- refines(?A, ?B), type_compatible(?B, ?C)`. The refines chain is acyclic by construction (the `requires` relation is a DAG — a sort can't require itself). The recursive `type_compatible` call descends to a structurally smaller term inside one variance arm. So SLD terminates.

### Inference: declared vs derived, layering

Once we have a name for variance, inference is just another way to populate it. Anthill's facts-and-rules model gives two natural places to plug inference in:

**(A) Single predicate, mixed sources.** `Covariant(?S, ?P)` is a predicate. A `fact Covariant(Map, K)` and a `rule Covariant(?S, ?P) :- ...` are both ways to satisfy a query — the resolver doesn't care which fired. This is the maximally Prolog-idiomatic choice: variance is a *claim*, and any path that derives the claim is as good as any other.

```anthill
-- (A) — single predicate, both facts and rules contribute
operation Covariant(s: Symbol, param: Symbol) -> Bool
operation Contravariant(s: Symbol, param: Symbol) -> Bool

-- Direct: user assertion.
fact Covariant(List, T)

-- Inferred: rule walks operation signatures and emits Covariant.
rule Covariant(?S, ?P)
  :- ... operation signature analysis ...
```

Pros: simplest. Cons: no way to distinguish declared from inferred at query-time, so diagnostics like "Map is invariant in K because we couldn't infer it and you didn't declare it" can't tell the user *which*.

**(B) Layered: declared as entity, inferred as rule.** Keep `Covariant` as the explicit-declaration entity, add an `inferred_covariant` rule, and have a single check predicate `effective_covariant` consult both. The variance arm in `check_variance` consults `effective_*` rather than `Covariant` directly.

```anthill
-- (B) — layered, declared entity + inferred rule
entity Covariant(sort: Symbol, param: Symbol)        -- declared
entity Contravariant(sort: Symbol, param: Symbol)    -- declared

-- Inference rules — derived from operation signatures, requires-spec
-- positions, and so on. Body deferred to a follow-up; for now the
-- inference layer is empty.
rule inferred_covariant(?S, ?P) :- ... -- TBD ...
rule inferred_contravariant(?S, ?P) :- ... -- TBD ...

-- Effective predicate: union of declared + inferred. The variance
-- arm in `check_variance` queries these instead of the entity directly.
rule effective_covariant(?S, ?P) :- Covariant(sort: ?S, param: ?P)
rule effective_covariant(?S, ?P) :- inferred_covariant(?S, ?P)
rule effective_contravariant(?S, ?P) :- Contravariant(sort: ?S, param: ?P)
rule effective_contravariant(?S, ?P) :- inferred_contravariant(?S, ?P)
```

Then `check_variance` consults the effective layer:

```anthill
rule check_variance(?S, ?P, ?V1, ?V2)
  :- effective_covariant(?S, ?P), type_compatible(?V1, ?V2)

rule check_variance(?S, ?P, ?V1, ?V2)
  :- effective_contravariant(?S, ?P), type_compatible(?V2, ?V1)

rule check_variance(?S, ?P, ?V1, ?V2)
  :- not(effective_covariant(?S, ?P)),
     not(effective_contravariant(?S, ?P)),
     type_compatible(?V1, ?V2),
     type_compatible(?V2, ?V1)
```

Pros: tooling can introspect (`Covariant` vs `inferred_covariant`); declared facts always win because they're consulted on the same predicate path; the inference layer can be added later without touching the consumer side.

Cons: two-tier; one extra predicate hop on every variance check. Not a perf concern at compile time but it's more moving parts.

**Conflict semantics under (B).** If user declares `Covariant(F, T)` *and* inference produces `inferred_contravariant(F, T)`, the effective query yields *both* `effective_covariant(F, T)` and `effective_contravariant(F, T)`. By the bivariance reading already adopted, that's interpreted as "T's variance is unconstrained along the subtype lattice" — useful when the user's declaration is stronger than what the system can derive (the user vouches for safety in positions inference can't see). If that's not the intended behavior, a separate "consistency rule" can fire a load-time warning when declared and inferred disagree — diagnostic, not soundness.

**Recommendation: design (B), with the inference rules left empty for now.** The `effective_*` indirection is cheap, and adding inference later doesn't require touching variance consumers.

### Risk: existing tests

The change from default-covariant to default-invariant *could* break tests that exercise `List[Cat]` vs `List[Animal]` compatibility. Mitigation: declare `fact Covariant(List, T)` (and `Option`, `Stream`, both `Pair` positions) in the relevant prelude namespaces so the public-facing behavior of the prelude container types is preserved. Containers with mutating ops (`Map`, `Set`, `Cell`) stay invariant — the previously-allowed unsound coercion gets correctly rejected.

The full variance story (use-site / wildcard variance, F-bounded polymorphism, nested-position checks) is out of scope here. The proposal lands the logical scaffolding so those can land as additional rules without further grammar work.

## Free-standing parametric operations

Free-standing operations already exist (`extract_sort_ref` at namespace level in `typing.anthill`), so the only question is whether they can carry type parameters. Symmetry says yes: if `operation foo[A, B](...) -> ...` is valid inside a sort body, it must be valid at namespace level too — same lexical scope rules, same dispatch. Concretely:

```anthill
namespace anthill.prelude.Pair
  operation pair[A, B](a: A, b: B) -> Pair[A = A, B = B]
  -- No enclosing sort. Type params A, B introduced by the operation
  -- declaration; their scope is the signature + body.
end
```

This is the same desugaring as a sort-nested operation, just without an enclosing scope contributing additional `sort K = ?` parameters. The resolver already handles operation type-param lookup through the symbol table — extending it to namespace-direct operations is a scope-table tweak.

## What this proposal commits to

1. **Surface form (3) — instantiation-term as method receiver.** `Map[K = String, V = Int].empty()` parses; the dispatch resolves `empty` in the scope of `Map` with K and V bound at the call.
2. **HM-style inference for forms (1) and (2).** Expected-type context and immediate-use context fill in the type parameters; bare `Map.empty()` with no constraint is a type error.
3. **`Value::Map(MapHandle)` runtime.** Arena-refcounted, like `Substitution` / `Stream`. `MapKey` covers Int / Bool / Str / Term; non-scalar keys deferred.
4. **Free-standing parametric operations** are valid (symmetry with sort-nested form).
5. **Variance via `entity Covariant` / `entity Contravariant`** — declared per (sort, param). Default invariant.
6. **`effective_covariant` / `effective_contravariant` as the consumer-side predicate** (design B, layered). Inference rules slot into this predicate later without touching `check_variance`.
7. **`type_compatible` composition rule** propagates widening through `refines`, so variance is correctly applied to requires-spec parameters.
8. **Migration:** the prelude declares `Covariant` for `List` / `Option` / `Stream` / `Pair.A` / `Pair.B`. `Map` / `Set` / `Cell` stay invariant — the previously-allowed unsound widening is correctly rejected.
9. **Variance inference algorithm itself** — out of scope; tracked as a follow-up WI.

## Out of scope (open follow-ups)

- **Variance inference body.** Standard recipe (Pierce ATAPL ch. 14): walk `OperationInfo` for each sort, classify each parameter by its position usage, emit `inferred_covariant` / `inferred_contravariant`. Filed as separate WI.
- **Use-site variance.** Java-style `List<? extends Animal>` widening at call sites — not handled; declaration-site only.
- **Higher-rank polymorphism.** `operation map_with_anything[F](f: F[A] -> F[B], xs: F[A]) -> F[B]` — F is a type-constructor variable. HM stays rank-1.
- **Inference quality / diagnostics.** Once mutual recursion + delayed substitution enter the picture, ambiguity reports may need polish. Typing-pass work, not blocking.
- **Eager variance-through-requires check.** Current proposal handles this lazily via the resolver. An eager load-time pass would yield more directed errors ("Map declared covariant in K but K appears in invariant position of Eq[T = K]"). Tooling improvement; additive to the lazy semantics.
- **Arrow rule rewrite.** The hand-rolled arrow rule (lines 134–140 of typing.anthill) can be re-expressed as a `Function[A, B]` sort with `Contravariant(Function, A)` / `Covariant(Function, B)` facts. Cleanup, not a semantic change.

## Acceptance

- `Map.empty()` works in all three surface forms above; the type checker rejects form (1)/(2) with no constraint and a clear "ambiguous type parameter" error.
- `cargo test` covers a fixture that does `Map[K = String, V = Int].empty() |> put(_, "a", 1) |> get(_, "a") = some(1)`.
- WI-183 can replace its `List[Pair[String, X]]` lookups with `Map[String, X]` and report measured speedup.
