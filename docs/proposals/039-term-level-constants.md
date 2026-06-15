# 039 — Term-Level Named Constants

## Status

Draft — **2026-06-15 redesign** (this revision is authoritative). `const` is reframed as a **nullary, carrier-independent reflect-function value**: a `SymbolKind::Const` carrying a declared type, whose value is produced by a reflect function (default = fold the body lazily and cache; host-supplied = a provided reflect builtin). The earlier mechanisms — the desugar-to-0-arg-operation, the `Constant` reflection relation/fact, a persistence-backend (proposal 007) route, the Tarjan cycle pre-pass, and the abstract algebraic-identity case — are all **dropped**. See *Revised design* below; it supersedes the matching legacy sections. All earlier Open Questions A–D are resolved or dissolved.

Driver is WI-084: webots binding sentinels and safety-proof magic numbers need a named, typed, single-point-of-definition shape that is unifiable as the underlying primitive type at every use site. Today's workarounds — `entity NAME` + a side fact, or unit-sort-with-coercion — fail that requirement.

## Revised design (2026-06-15) — const as a nullary reflect-function value

A `const` is **a symbol of kind `Const`, carrying a declared type, whose value is produced by a reflect function and memoized in a per-symbol cache.** Nothing more. There is no relation, no asserted fact, no desugared operation, no persistence backend, and no abstract case. The model has three pieces:

### 1. `SymbolKind::Const`

`const NAME: T [= EXPR]` defines a symbol of kind `Const` carrying the declared type `T`. No desugar to an operation; no name mangling (`NAME` stays `NAME`). The symbol is **value-denoting in term position** — it joins the existing bare-name candidate set the resolver already arbitrates (locals, ADT variants via *variant exposure*; kernel-language §6), and §6's ambiguity rule applies unchanged: scope-nearest wins, a same-step tie of ≥2 candidates is an ambiguous error you fix by qualifying. `intern::SymbolKind::is_value_place()` is the predicate that marks a `Const` value-denoting where an `Operation` is not (until first-class operations land — deferred, see [`future/first-class-operations.md`](future/first-class-operations.md)).

The type annotation is **always required**, even with a body — a constant is a named, typed value; the type is part of the name's contract, not an inference target.

### 2. A reflect-function value source

A const's value comes from a function `fn() -> Value` keyed on the const symbol, reusing the reflect / builtin layer (`register_builtin`-style). It is **not** a relation query, **not** a persisted fact, and **not** a proposal-007 route — 007 is relational, cross-session persistence machinery, and a const has no relation, no goal, and nothing to persist.

- **Anthill-bodied** (`const D_MIN: Float = 1.0`) — the function folds the stored body. The body is stored at load (like an operation body); folding runs the real evaluator (WI-179's iterative evaluator) under the `step_cap` runaway guard. Lazy: folded on first value-demand, then cached.
- **Host-supplied** (`const X: T`, value from the host, e.g. `webots::Emitter::CHANNEL_BROADCAST`) — you *provide* a reflect builtin that returns the host value. No anthill body to fold.

The signature `fn() -> Value` — **zero arguments, no carrier** — is the dividing line of the whole proposal:

> **`const` = nullary AND carrier-independent. Anything carrier-dependent is an operation.**

The moment a value depends on a carrier the function must be `fn(carrier) -> Value`, which is an operation, not a const (see *Not a const: abstract identities*).

### 3. A per-symbol value cache (memo + forcing sentinel)

The cache *is* the memoization: a const's value is folded/fetched **at most once** and shared by every reference (referentially transparent — the value source is pure, see §Foldability). This holds across all value sources; the host case is constant by construction, so caching the first fetch is trivially safe.

A "being-forced" sentinel in the cache detects dependency cycles **dynamically**: forcing a const whose entry is already in the *forcing* state is a load/eval error naming the cycle (`const A = B + 1; const B = A + 1`). This replaces the static Tarjan SCC pre-pass over a const-dependency graph — forcing a referenced const happens naturally on demand, and dependencies need no pre-computed topological order.

### Value carrier, not Term

A folded value is a `Value`; it is cached and matched **as a `Value`** via the `TermView` abstraction (`kb::term_view`). No `Value→Term` reifier, no hash-cons projection: the system is carrier-agnostic by design — `views_structurally_equal` compares "constants by value" regardless of carrier, and the discrimination tree keys on structural `DiscrimKey`s, so a `Value::Int(-1)` matches a `Term::Const(Int(-1))` cross-carrier ("discrim-query-is-the-unifier: a cross-carrier miss is a wrong answer", WI-425). Hash-consing is a storage optimization for heavily-shared persistent structure (per CLAUDE.md's representation note) and buys nothing for a one-off const value.

### Stay symbolic in bodies; expand at the use boundary

Operation / rule / constraint bodies retain `Ref(const_sym)` — they are **not** rewritten to the folded value at load. Two reasons:

- **Provenance.** A safety constraint stays `lt(?d, D_MIN)`, keeping `D_MIN` a named premise the proof can reference, rather than collapsing to a magic `1.0`. anthill is a reasoning system, not only a program; the named assumption is load-bearing for proofs.
- **Canonical identity.** A `Ref(const_sym)` is a hash-consed `TermId`, so stored bodies stay entirely in `TermId`-land; the `Value` materializes only at the use boundary, where the carrier-agnostic match handles it.

The value materializes only where demanded:

- **eval** — the common driver case. `set_channel(em, BROADCAST_CHANNEL)` / `lt(?d, D_MIN)` have the const in *argument* position, which is evaluated; the eval hook reads the cache (forcing the value source on first demand).
- **resolver** — only at a fact-head query boundary (`fact DistanceBounds(d_min: D_MIN)` queried back as `DistanceBounds(d_min: ?x)`); resolving `Ref(const_sym)` to its value, again via the value source.

Neither path requires value-level expansion-during-unification. That mechanism — the value-level generalization of WI-374's type-level "elimination at the unify boundary" — is explicitly **not** a v1 dependency. (A future hybrid could expand eagerly in data / fact-head positions while staying symbolic in guards; the eval-side cache read covers all current drivers without it.)

### Typing is fold-free

The load-bearing driver — `set_channel(em, BROADCAST_CHANNEL)` checking against `channel: Int64` — needs only the **declared type** `T`, read directly off the `Const` symbol. No evaluation occurs during type-checking; folding is triggered solely by an actual value demand at eval / codegen. So a const type-checks even when its value source is unavailable (the host-supplied, spec-only case).

### Uniqueness

"One definition per const symbol," already guaranteed by `scan_definitions` + `SymbolKind::Const`. No fact dedup, no uniqueness constraint — the question (raised against multi-Implementation `Constant` facts) evaporates with the relation.

### Not a const: abstract algebraic identities

`Ring.zero`, `Group.identity`, `Ring.one` are **not** constants, and the `const` keyword does not mint them. There is no carrier-independent value to bind:

- `Ring.zero` is a *function of the carrier* — `Int64 ↦ 0`, `Float ↦ 0.0`. A global value has nothing to store.
- `Ring{ zero = 1 }` binds `zero` *instance-locally* in a witness; different instantiations bind it differently. No global truth exists.

Both fail the `fn() -> Value` test. They are **nullary carrier-dispatched operations** — `operation zero() -> R`, resolved by return-type / witness dispatch and provided per carrier (the typeclass-member shape; satisfaction is an operation with a body, not a const). They live in the operation + witness-dispatch machinery, **not** in 039. The return-type-dispatch surface (`zero[R = Int64]()`) is where proposal 042 matters — as an *operation* feature. This removes the proposal's former Phase 4b entirely; 039 no longer depends on 042.

## Depends on

- [018-expressions-and-operation-implementation](018-expressions-and-operation-implementation.md) — a const body reuses the operation expression grammar.
- [026-expression-evaluator](026-expression-evaluator.md) / WI-179 — the lazy fold runs the real iterative evaluator under `step_cap`.
- [027.1-alloc-effect-and-allocator-revision](027.1-alloc-effect-and-allocator-revision.md) — fresh allocators carry `effects Modify[result]`; this is what excludes `Cell.new`, `Map.empty`, etc. from const-foldability (the purity gate) without a special case.
- [045-effect-sets-and-expressions](045-effect-sets-and-expressions.md) — effect-row language; the purity gate is phrased over the declared effect row.

## Relates to (not dependencies)

- [007-persistence-layer](007-persistence-layer.md) — *considered and rejected as the wrong layer.* Its route/oracle machinery answers relation goals from a durable store; a const is a function value, not a relation, so it reuses the reflect/builtin layer instead.
- [042-explicit-type-parameters-on-operations](042-explicit-type-parameters-on-operations.md) — relevant only to the abstract algebraic identities (now out of scope as operations), not to `const`.
- WI-084 (driver), WI-083 (Bytes — adjacent magic-number territory), WI-156 (scaland resync).

## Affects

- Kernel-language spec §5/§6: one sentence making `const`-declared names value-denoting in term position (no new precedence text — they join §6's existing bare-name candidate set).
- Grammar (`grammar.js`): one new construct `Const`, with-body and bodyless. Slots into both `_body_namespace` and `_body_sort` (the same positions as `operation_declaration`). No `effects` clause admitted.
- Resolver / typer: a bare `const` reference is value-denoting and types as the declared `T`; an eval/resolver hook reads its memoized value.
- Stdlib + examples: opportunistic adoption (webots sentinels first; `safety_common`'s `D_MIN`/`D_MAX` second).

## Motivation

Anthill currently has primitive literals (`-1`, `1.0`, `"hello"`) and named entities. There is no shape that lets a name `BROADCAST_CHANNEL` *be* the integer `-1` at every term-position use. The webots binding documents this gap explicitly:

```
-- examples/webots-modelling/lf1/webots/emitter.anthill:22-24
-- Sentinel for broadcast (mirrors webots::Emitter::CHANNEL_BROADCAST = -1).
-- TODO: model as a constant once anthill has term-level constants.
-- For now, callers pass -1 directly to set_channel.
entity BROADCAST_CHANNEL
```

The `entity BROADCAST_CHANNEL` workaround declares a name but binds it to an entity term, not to the `Int64` `-1`. The call-site `set_channel(em, BROADCAST_CHANNEL)` fails to type-check against `set_channel(em: Emitter, channel: Int64)`. Callers fall back to the literal `-1`, losing the name. The same shape recurs:

- Webots motor velocity-mode sentinel (`+infinity` for `setPosition`).
- Safety-proof application parameters (`d_min: 1.0`, `d_max: 20.0`, `leader_speed_max: 8.0` in `safety_common.anthill`).

### When constants are actually needed

| Driver | Strength |
|---|---|
| Host-binding sentinels (broadcast channel, infinity for velocity-mode) | **Strong** — no other natural fit; values come from the host API and callers must pass the primitive type. |
| Application-specific proof parameters | **Soft** — the current "fact with named fields, rules unify on it" pattern works when values are read through queries; clunky when you want the number directly in an expression. |
| Enum-like Int64 values | **Neutral** — entity-side identity usually also wanted. |

The host-binding case is the load-bearing driver. (Algebraic identity elements, a former driver, are *not* constants — see *Not a const: abstract identities*.)

## Surface form

```
Const ::= DescriptionBlock*
            [Visibility] 'const' Name ':' Type ['=' ConstExpr]
            ['meta' ':' Meta]
```

Two shapes:

```anthill
const BROADCAST_CHANNEL: Int64 = -1        -- concrete, anthill-bodied
const CHANNEL_BROADCAST: Int64             -- host-supplied (value from a provided reflect fn)
```

**Visibility.** Constants accept the inline `Visibility` prefix (`internal`/`export`/`public`), matching operations and the standing convention for sorts/entities. Per-declaration form is encouraged — the reader sees `export const D_MIN: Float = 1.0` at the declaration site. The namespace-level `export` clause also lists const names.

```anthill
namespace anthill.examples.lf1.webots.Emitter
  export const BROADCAST_CHANNEL: Int64 = -1
  ...
end
```

Description blocks are admitted, identically to operations.

## Foldability — pure + bounded, lazy

A const's anthill body is foldable iff it **evaluates to a value, purely, within the fold budget**. There is no closed-grammar subset: the body may be any expression the real evaluator accepts — `let`, `match`, recursion, calls to other pure operations, entity construction, references to other consts — provided:

- **Purity** — an empty declared effect row (the `const` grammar position admits no `effects` clause). This recursively excludes allocators (`Cell.new`, `Map.empty`, `Substitution.empty`), which carry `Modify[result]` per 027.1, and any call into an effectful operation. Purity is what makes a const referentially transparent and therefore safe to memoize. A body that does not reduce to a value (free logical variables, an unresolved name) simply fails to fold.
- **Termination within budget** — folding runs the evaluator under the `step_cap` runaway guard (WI-179). A body that does not reduce within the cap is a load-time error ("const X exceeded the fold budget"), naming the const.

Folding is **lazy**: triggered on the first value-demand at eval / codegen (not at load), then cached. Cycles are caught by the cache's forcing sentinel, not a pre-pass (see *Revised design §3*). The only static gate is purity; termination and cyclicity are dynamic, on-demand checks. This reuses WI-179's evaluator rather than maintaining a second fold-only evaluator.

The same purity gate applies to **every anthill-side value source**. Host-supplied (Rust/Scala/C++) reflect functions waive the fold check — the kernel cannot inspect their body; they are trusted to return a value of the declared type.

## Interaction with proposals 027.1 and 037 (allocators)

Per 027.1, fresh-allocator operations carry `effects Modify[result]`:

```anthill
-- stdlib/anthill/prelude/cell.anthill:20-21
operation new(v: V) -> Cell
  effects Modify[result]
```

Their declared effect row is non-empty, so the purity gate rejects them as const bodies. `const COUNTER: Cell[Int64] = Cell.new(0)` is a load-time error: "body calls operation `Cell.new` with non-empty effect row `{Modify[result]}` — not foldable." This is intended: a const denotes value-level referential transparency, which an allocator violates. If a load-time singleton is genuinely wanted, declare the operation explicitly:

```anthill
operation counter() -> Cell[Int64]
  effects Modify[result]
  = Cell.new(0)
```

…and call it at use sites; the explicit signature makes the effect visible.

## Equational reasoning

The proposal pivots on referential transparency: a nullary, carrier-independent value source with a pure body denotes the same value at every occurrence, and the per-symbol cache realizes that as a single evaluation shared across references. The generativity question (`Cell.new() ≠ Cell.new()`, `rand()`) is handled outside this proposal — 027.1's `Modify[result]` marks any operation whose call sites can't be collapsed, and the purity gate excludes those. The classical framing is Plotkin & Power's *Algebraic Operations and Generic Effects* (2003), `new : 1 → Loc` as the canonical "no input, still not pure" example.

## Examples

### Concrete primitive constant — webots broadcast channel

```anthill
sort anthill.examples.lf1.webots.Emitter
  import anthill.prelude.{Int64, Float, Unit, String, Bool, Modify}
  export Emitter, BROADCAST_CHANNEL
  export set_channel, get_channel, send

  -- Sentinel for broadcast (mirrors webots::Emitter::CHANNEL_BROADCAST = -1).
  const BROADCAST_CHANNEL: Int64 = -1

  operation set_channel(self: Emitter, channel: Int64) -> Unit
    effects Modify[self]
end
```

Call site (bare-identifier resolution + the eval hook; no call-site grammar change):

```anthill
set_channel(my_emitter, BROADCAST_CHANNEL)   -- types as Int64; eval reads the cached -1
```

### Concrete float constants — safety-proof envelope

```anthill
namespace anthill.examples.lf1.safety
  const D_MIN: Float = 1.0
  const D_MAX: Float = 20.0

  -- bodies stay symbolic: D_MIN remains a named premise
  constraint within_envelope: ⊥ :- pose_distance(?d), lt(?d, D_MIN)
end
```

### Const-expression composition

A const body may reference other consts; the lazy forcing resolves dependencies on demand:

```anthill
const PI:      Float = 3.14159265358979
const TWO_PI:  Float = 2.0 * PI
const HALF_PI: Float = PI / 2.0
```

Cycles (`const A = B + 1; const B = A + 1`) are caught by the forcing sentinel — forcing `A` forces `B` forces `A`, whose entry is already *forcing* → a load/eval error with the cycle path.

### NOT a const — algebraic identity (for contrast)

```anthill
sort Ring
  sort R = ?
  operation zero() -> R          -- nullary carrier-dispatched operation, NOT a const
  operation one()  -> R
  operation add(a: R, b: R) -> R
end

fact Implementation[Ring[R = Int64]]
  operation zero() -> Int64 = 0
  operation one()  -> Int64 = 1
  ...
end
```

`zero`/`one` are operations because their value depends on the carrier `R` (`fn(carrier) -> Value`). See *Not a const: abstract identities*.

## Out of scope

- **Parametric constants** (`const empty[T]: List[T] = nil`). Use the operation-with-body form (`operation empty[T] -> List[T] = nil`); the `const` keyword is intentionally monomorphic. The escape hatch is gated on proposal 042.
- **Carrier-dependent "constants"** (`Ring.zero`, `Ring{zero=1}`). Operations + witness dispatch, not 039 (*Not a const: abstract identities*).
- **Multi-clause "constants".** Use the long form (`operation` + `rule`/`match` body). `const` is "this name has one foldable value."
- **Cross-KB override semantics.** Whether a downstream namespace can redefine an imported constant. Default: no. Separate proposal.
- **Eager constant propagation into bodies.** Bodies stay symbolic (*Revised design § Stay symbolic*); a future hybrid may expand in data/fact-head positions.

## Resolved / dissolved questions

The earlier draft's Open Questions A–D are all closed:

- **A (foldable-subset boundary)** — RESOLVED: there is no subset. Foldability is "pure + evaluates within `step_cap`," run by the real evaluator; `let`/`match`/recursion are native (§Foldability).
- **B (bare-name precedence vs ADT-variant resolution)** — RESOLVED: ambiguity-is-an-error, no precedence ladder. A `const` joins §6's existing bare-name candidate set; a same-step tie is an ambiguous error fixed by qualifying (*Revised design §1*).
- **C (Implementation-supplied / host bodies)** — DISSOLVED: there is no `Constant` fact and no `TrustedConstant`. A host const is a *provided reflect function*; whether it is registered is the spec-only-vs-codegen axis (unregistered → typed but value-unavailable; registered → value known).
- **D (profile-keyed `Constant` reflection)** — DISSOLVED: no relation to key. Per-profile differences are just which reflect function a build registers; no ambient profile is added to the resolver/typer.

## Migration / phasing

Four phases, each landing independently with its own tests. **No prerequisite WI** — the substrate (`SymbolKind::Const`, a per-symbol value cache, an eval/resolver hook, reuse of the reflect/builtin registry) is contained in 039.

**Phase 1 — grammar + loader.** Add `const` to `grammar.js`, the parser/converter, and the loader. Bodyless and body forms. Define a `SymbolKind::Const` symbol carrying the declared type; store the anthill body where operation bodies are stored. No value source yet — just the symbol + type. Slots into `_body_namespace` and `_body_sort`. Independent of any other in-flight proposal.

**Phase 2 — resolution + typing.** A bare `const` reference resolves (value-denoting, joins the candidate set, §6 ambiguity rule) and types as the declared `T`. Tests: `set_channel(em, BROADCAST_CHANNEL)` type-checks against `Int64`; an ambiguous same-name tie is a load error. Fully de-entangled from first-class-operations (no `Value::OpRef` needed for `const`).

**Phase 3 — value source + cache + hook.** Land the per-symbol value cache (memo + forcing sentinel), the default fold value source (lazy fold via the real evaluator + `step_cap`, purity gate, cyclicity via the sentinel), the reflect-builtin registration path for host consts, and the eval/resolver hook that reads a `Const` symbol's value. Tests: bare `BROADCAST_CHANNEL` evaluates to `-1`; `TWO_PI` folds via `PI`; a cyclic pair errors; an over-budget body errors; a host const with a registered builtin returns the host value, and without one type-checks but reports value-unavailable on demand.

**Phase 4 — adoption.** Convert lf1 webots sentinels (`BROADCAST_CHANNEL`, motor velocity-mode infinity), then `safety_common`'s `D_MIN`/`D_MAX`. Needs only Phases 1–3; no upstream-proposal dependency.
