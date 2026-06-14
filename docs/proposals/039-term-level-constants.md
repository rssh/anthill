# 039 — Term-Level Named Constants

## Status

Draft — cleanup pass 2026-05-28: dropped stale Cell.new "effect-pure" threads (superseded by 027.1), pinned the foldable subset and cycle-detection stage, resolved the original Open Questions, surfaced four new ones (A–D) that gate Phase 3+4. **2026-06-15 revision** (see *Design revision* below): `const` reframed as a memoized value binding, the foldable subset replaced by "pure + `step_cap`", operations-as-first-class deferred to `future/first-class-operations.md`, and Open Questions A–D all resolved.

Driver is WI-084: webots binding sentinels and safety-proof magic numbers need a named, typed, single-point-of-definition shape that is unifiable as the underlying primitive type at every use site. Today's workarounds — `entity NAME` + a side fact, or unit-sort-with-coercion — fail that requirement.

## Design revision (2026-06-15) — `()` is application; operations are first-class; `const` is a memoized value binding

This supersedes the original "`const` is sugar for a 0-arg operation + bare-call sugar" framing throughout the body below. Three decisions:

1. **DEFERRED → [`future/first-class-operations.md`](future/first-class-operations.md).** The enabling idea that motivated this revision — a bare operation name as a first-class function value (`Value::OpRef`) with `()` as uniform application — is a language-wide change, and **039 does not depend on it.** 039 ships decisions 2–3 (`const` as a memoized value binding) standalone; until first-class operations land, operations keep today's `g()` invocation and a `const` is the way to expose a bare value. When it lands it composes with 039 (both `const`s and bare op references are value-denoting, and Open Question B's ambiguity rule already covers both).

2. **`const` is a value binding, not an operation.** `const NAME: T [= body]` binds a name to a value; a bare `NAME` *is* that value, with no accessor to invoke. See §Call-site semantics for the full statement (function-valued consts, thunks, ambiguity).

3. **A `const` is memoized: its body is evaluated at most once and the value is shared across all references.** Sound because a const body is pure / referentially transparent (the §Validator purity gate). For the foldable consts this proposal targets, the single evaluation is **eager, at load time** (the §Validator fold; the emitted `Constant` fact *is* the memo). The guarantee is "≤ 1 evaluation," independent of whether a future relaxation evaluates lazily on first use. Memoization covers the const's **value**: a function-valued const builds its closure once; *applying* it (`g()`) still runs each time — memoizing applications would be a separate "lazy val" feature. Operations are **not** memoized (each `f()` runs the body) — which is exactly the value-vs-computation line between `const` and `operation`.

Consequence: the old "parenless 0-arg-op invocation" (bare `Map.empty`, `Numeric.zero-val`) is **dropped** — invoke a 0-arg op with `()`; declare a `const` to expose a bare value. Backward-compatible for existing `op()` call sites (`kb()` still invokes). In the deeper body (§Validator/§Reflection), read "the const's desugared 0-arg operation" as "the const's folded value binding"; the folding and `Constant`-fact lifecycle are unchanged.

## Depends on

- [018-expressions-and-operation-implementation](018-expressions-and-operation-implementation.md) — operation expression bodies; a `const` body reuses the same expression grammar (the const is a value binding whose body is folded at load, not a 0-arg operation — see *Design revision 2026-06-15*).
- [026-expression-evaluator](026-expression-evaluator.md) — load-time evaluator. The §Validator runs the evaluator over the body in a foldable-subset mode (see §Validator for the subset).
- [027.1-alloc-effect-and-allocator-revision](027.1-alloc-effect-and-allocator-revision.md) — fresh allocators carry `effects Modify[result]`. This is what excludes `Cell.new`, `Map.empty`, etc. from const-foldability without a special case.
- [045-effect-sets-and-expressions](045-effect-sets-and-expressions.md) — effect-row language. The foldability and bare-call rules are phrased over the declared effect row.

## Relates to

- [037-anthill-state-model](037-anthill-state-model.md) — state model for mutable resources. Originally framed `Cell.new` as effect-pure; 027.1 superseded that and is what this proposal relies on.
- [042-explicit-type-parameters-on-operations](042-explicit-type-parameters-on-operations.md) — bracketed type parameters on operations. The Phase 4 adoption of algebraic identities (`Ring.zero`, etc.) routes through the parametric-operation form and is gated on 042.
- WI-084 (driver), WI-083 (Bytes — adjacent magic-number territory), WI-156 (scaland resync).

## Affects

- Kernel-language spec §5 (new sugar form documented as §6.X under "Syntactic Sugar"), §6.
- Grammar (`grammar.js`): one new construct `Const`, with-body and bodyless. Slots into both `_body_namespace` and `_body_sort` (the same positions as `operation_declaration`).
- Resolver: term-position resolution treats a `const` as value-denoting and applies the ambiguity rule (Open Question B); see §Call-site semantics. (The bare-operation-as-function-value half is deferred — `future/first-class-operations.md`.)
- Stdlib + examples: opportunistic adoption (webots sentinels first; safety_common's `D_MIN`/`D_MAX` second).

## Motivation

Anthill currently has primitive literals (`-1`, `1.0`, `"hello"`) and named entities. There is no shape that lets a name `BROADCAST_CHANNEL` *be* the integer `-1` at every term-position use. The webots binding documents this gap explicitly:

```
-- examples/webots-modelling/lf1/webots/emitter.anthill:22-24
-- Sentinel for broadcast (mirrors webots::Emitter::CHANNEL_BROADCAST = -1).
-- TODO: model as a constant once anthill has term-level constants.
-- For now, callers pass -1 directly to set_channel.
entity BROADCAST_CHANNEL
```

The `entity BROADCAST_CHANNEL` workaround declares a name but binds it to an entity term, not to the `Int64` `-1`. The call-site `set_channel(em, BROADCAST_CHANNEL)` fails to type-check against `set_channel(em: Emitter, channel: Int64)`. Callers fall back to writing the literal `-1`, losing the name. The same shape recurs:

- Webots motor velocity-mode sentinel (`+infinity` for `setPosition`).
- C++ enum encoding values (`fact CppEnumValue(constructor: "Running", value: 0)` in `realization.anthill:31`).
- Safety-proof application parameters (`d_min: 1.0`, `d_max: 20.0`, `leader_speed_max: 8.0` in `safety_common.anthill`).
- Algebraic identity elements (`Ring.zero`, `Ring.one`, `Group.identity`) — same shape, abstract rather than concrete.

### When constants are actually needed

Ranked by drive on real lf1 / stdlib work:

| Driver | Strength |
|---|---|
| Host-binding sentinels (broadcast channel, infinity for velocity-mode) | **Strong** — no other natural fit; values come from the host API and callers must pass the primitive type. |
| Algebraic identity elements (`zero`, `one`, `identity`) | **Strong** — bodyless form is the canonical shape for abstract algebras. |
| Application-specific proof parameters | **Soft** — current "fact with named fields, rules unify on it" pattern works when values are read through queries. Becomes clunky when you want the number directly in an expression. |
| Enum-like Int64 values | **Neutral** — entity-side identity usually also wanted. |

The host-binding case and algebraic-identity case are the load-bearing drivers; the rest are nice-to-haves.

## Design

A `const` is a **value binding**: a name bound to a value — the body folded at load time (§Validator), memoized and shared across all references. (Revised 2026-06-15 — see *Design revision* above; the original "sugar for a 0-arg operation with an empty declared effect row" model is superseded.) The §Validator is what gives `const` its meaning.

### Surface form

```
Const ::= DescriptionBlock*
            [Visibility] 'const' Name ':' Type ['=' ConstExpr]
            ['meta' ':' Meta]
```

Two shapes:

```anthill
const BROADCAST_CHANNEL: Int64 = -1        -- concrete (body given)
const zero: R                            -- abstract (open obligation)
```

The type annotation is **always required**, even with body. This is deliberate: a constant is a named, typed value; the type is part of the name's contract, not an inference target. (Unlike `let` inside an operation body, which infers freely.)

**Visibility.** Constants accept the inline `Visibility` prefix (`internal`/`export`/`public`), matching the grammar's intent for operations (`grammar.js:305`) and the standing convention for sorts and entities (`grammar.js:199, 209, 218`). Per-declaration form is encouraged for constants since it sits next to the value — the reader sees `export const D_MIN: Float = 1.0` at the declaration site without scanning to a separate `export` list. The namespace-level `export` clause also lists const names (same as operations / sorts) for namespaces that prefer the centralized form.

```anthill
namespace anthill.examples.lf1.webots.Emitter
  -- Per-declaration form (recommended for const):
  export const BROADCAST_CHANNEL: Int64 = -1

  -- Or via namespace-level export list:
  export Emitter, set_channel, get_channel
  ...
end
```

### Desugaring

```anthill
const NAME: T = EXPR
-- desugars to:
operation NAME -> T
  EXPR
end
```

```anthill
const NAME: T
-- desugars to:
operation NAME -> T
-- (no body — open obligation, filled by an implementation)
```

Both forms are value bindings with no `effects` clause (the `const` grammar position admits none — an empty declared effect row). The empty row is what permits load-time folding (§Validator) and makes the bare name value-denoting (§Call-site semantics).

### Validator

`const` enforces three conditions beyond what a plain `operation` requires:

1. **Zero arguments.** Required by the surface grammar — `const NAME: T = ...` has no parameter list.
2. **Empty declared effect row.** The desugared operation has no `effects` clause (equivalently, `effects ()` once 045's empty-set syntax is in). User attempts to add one are rejected at parse time — the `const` keyword's grammar position doesn't admit an effects clause.
3. **Bounded fold** (when body is present). The body — any pure expression (condition 2) — must evaluate to a value within the fold budget (`step_cap`). See §Foldability below. Non-termination / over-budget / a dependency cycle is a load-time error naming the const.

The same foldability check applies to **every anthill-side body** that fills the obligation — whether it is the declaration body, or a body supplied later via an `Implementation` fact's rule clauses. Host-language `Implementation`s (Rust / Scala / C++) waive the check, since the kernel cannot inspect their body; the resulting `Constant` reflection fact (see §Reflection) is omitted in the host-language case until codegen has produced a folded literal it can echo back.

#### Foldability — pure + bounded (no syntactic subset) — decided 2026-06-15 (Open Question A)

A body is foldable iff it **evaluates to a value, purely, within the fold budget**. There is **no closed-grammar subset**: the body may be any expression the real evaluator (WI-179's iterative evaluator) accepts — `let`, `match`, recursion, calls to other pure operations, entity construction, references to other `const`s — provided:

- **Purity** — an empty declared effect row (condition 2). This recursively excludes allocators (`Cell.new`, `Map.empty`, `Substitution.empty`), which carry `Modify[result]` per 027.1, and any call into an effectful operation. Purity is what makes the const referentially transparent and therefore safe to memoize (§Design revision decision 3). A body that does not reduce to a value (e.g. free logical variables `?`/`?name`, an unresolved name) simply fails to fold.
- **Termination within budget** — folding runs the real evaluator under the `step_cap` runaway guard (WI-179). A body that does not reduce to a value within the cap (non-terminating, or pathologically expensive) is a load-time error ("const X exceeded the fold budget"), naming the const.

Rationale: the earlier closed-grammar "subset" (literals + prim ops + const-refs + entity construction) was a *static over-approximation* of "evaluable at load." Reusing the real evaluator + `step_cap` expresses the same intent directly, **dissolves** the old "are let-bindings in the subset?" question (the evaluator handles `let`/`match`/recursion natively), and avoids maintaining a second, drift-prone fold-only evaluator. The only static gate is purity; termination is a dynamic, budgeted check.

Folding is **eager, at load time**, in reverse-topological order of the const-dependency graph (§Cycle detection); the resulting value is memoized as the `Constant` fact (§Reflection). (A lazy, first-use variant would relax the load-time termination requirement but lose compile-time-known values — out of scope; see §Design revision decision 3.)

#### Cycle detection

After `scan_definitions` populates the symbol table but before expression typing runs, the loader builds the **const-dependency graph** — one node per `const`-declared symbol, edges to every other `const` symbol referenced from its body. Tarjan's SCC pass detects cycles; any SCC of size > 1, or a self-edge, is reported with the cycle path and rejected.

Cross-namespace forward refs are allowed (the dependency graph is built over the whole loaded set, not file-by-file). The order in which folded values are computed is the reverse topological order of the SCC quotient graph.

#### `Constant` reflection fact lifecycle

For declaration-with-body `const`, the `Constant(name, type, value)` fact is asserted at the end of fold-mode execution for that declaration — i.e. once during load, in topological order.

For bodyless `const` declarations filled by an `Implementation` fact, the fact is asserted **at Implementation pairing**: when the loader pairs an `Implementation[S]` fact with the obligation `S.NAME`, it re-runs the foldability check (§Foldability) over the supplied rule body. Success asserts the `Constant` fact; failure rejects the Implementation.

Under proposal 037's profile-keyed Implementations, multiple Implementations may coexist (one per profile). Each emits its own `Constant` fact keyed by profile — the reflection schema is `Constant(name, type, value, profile)` (profile defaults to a `default` symbol when the Implementation does not declare one). The load-time selector picks one Implementation per profile and binds the corresponding `Constant` for downstream queries.

### Call-site semantics — `const` is its value; operations are first-class; `()` applies (decided 2026-06-15)

> **Scope:** 039 normatively specifies only the **`const`** (value-binding) semantics here. The **operation** bullet — bare operation as a first-class function value, `()` as uniform application — is **deferred** to [`future/first-class-operations.md`](future/first-class-operations.md) and shown here only for the composed picture. Until it lands, operations keep today's `g()` invocation.

`()` is **uniformly application/invocation**. A bare name is the value it denotes; for an `operation` that value is the operation itself as a **first-class function** (runtime `Value::OpRef`), and for a `const` it is the bound (memoized) value.

- **Operation `f`** — `f` is the function value; `f(args)` applies it; a 0-arg op `g` is invoked `g()` (apply to the unit tuple `()`). Effects ride on the function value and are paid at application, so there is no pure-vs-effectful special case at the call site. Operations are thus passable to HOFs directly: `map(xs, increment)` (no lambda wrapper). `kb()` keeps invoking the ambient-KB op; bare `kb` is now *the function* `() -> KB`, not the KB.
- **Non-function const `K: Int64 = -1`** — `K` *is* `-1`. `K()` = "apply `-1` to `()`" = a **type error**. You write `K`, never `K()`.
- **Function const `f: (A) -> B`** — `f` is the function value; `f(a)` applies it (identically to a function-typed parameter, WI-275/441); `f()` applies to the unit tuple (a type error for a unary `f`).
- **Nullary-function const `g: () -> B`** — a **thunk**: `g` is the suspended function, `g()` forces it (applies to `()`). So `g ≠ g()`. (Const memoization builds the closure once; each `g()` still runs — see Design revision decision 3.)

This composes with the tuple model rather than adding syntax: `f(a, b)` applies to `(a, b)`, `f()` applies to the zero-element tuple `()` (unit) — no separate "zero arguments" concept.

**Bare-name resolution (Open Question B, decided 2026-06-15 — ambiguity is an error).** A `const` and a bare operation reference are both value-denoting candidates that join the **same candidate set** the resolver already arbitrates for bare names (locals, ADT variants via *variant exposure*; kernel-language §6). No precedence ladder: scope-nearest wins; a same-step tie of ≥2 candidates (e.g. a `const nil` and `List.nil` in scope) is an **ambiguous error** — qualify (`List.nil`) to disambiguate. This is §6's existing ambiguity rule (≥2 distinct symbols at a step = load/query error); the only spec addition is that `const`s and bare operation references are value-denoting in term position. No new precedence text.

```anthill
set_channel(em, BROADCAST_CHANNEL)         -- BROADCAST_CHANNEL is the Int64 -1 (a const value binding)
map(xs, increment)                          -- pass the operation directly as a function value, no lambda
let k  = kb()                               -- invoke the 0-arg op; bare `kb` would be the function () -> KB
let c  = Cell.new(0)                        -- Cell.new is an operation: invoke with (); effect paid here (027.1)
```

This **drops** the proposal's earlier "parenless 0-arg-op invocation": a 0-arg op is invoked with `()`. To expose a bare *value*, declare a `const`; to expose a *computation*, declare an `operation`. The earlier "the parens form still works for any operation" statement is replaced by "`()` is application." (The Eiffel uniform-access principle — hiding effects behind a uniform syntax — is deliberately *not* followed: a `const` is a transparent value, an `operation` is an explicit call.)

### Reflection

Every `const NAME: T = EXPR` produces, in addition to the desugared operation, an automatic reflection fact:

```
fact Constant(name:    "anthill.examples.lf1.webots.BROADCAST_CHANNEL",
              type:    Int64,
              value:   -1,
              profile: default)
```

The `profile` field exists to disambiguate between multiple `Implementation`-supplied bodies under proposal 037's profile-keyed Implementations (see §Validator → `Constant` fact lifecycle). For declaration-with-body `const`, `profile` is `default`.

For the bodyless case, no `Constant` fact is asserted at declaration time — the operation's open-obligation state is observable through the usual `Operation` / `Implementation` reflection. When an Implementation provides a foldable body, the kernel asserts the `Constant` fact at the Implementation-pairing step, keyed by the Implementation's profile.

The `Constant` fact is what codegen, IDE tooling, and KB queries use to enumerate constants. It is *additional* to — not a replacement for — the desugared operation, mirroring how proposal 022 already adds `TypeOf` facts alongside expression occurrences.

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

Call site (no change to the call-site grammar, just bare-identifier resolution):

```anthill
set_channel(my_emitter, BROADCAST_CHANNEL)   -- after fold: set_channel(my_emitter, -1)
```

### Concrete float constant — safety-proof envelope

```anthill
namespace anthill.examples.lf1.safety
  const D_MIN: Float = 1.0
  const D_MAX: Float = 20.0

  fact DistanceBounds(d_min: D_MIN, d_max: D_MAX)
  -- after fold: fact DistanceBounds(d_min: 1.0, d_max: 20.0)
end
```

Constraints can reference the constants symbolically. The bare name resolves to a 0-arg op call; under load-time fold, the call site becomes the literal value:

```anthill
constraint within_envelope: ⊥ :- pose_distance(?d), lt(?d, D_MIN)
-- after fold: constraint within_envelope: ⊥ :- pose_distance(?d), lt(?d, 1.0)
```

### Abstract constants — algebraic identity elements

```anthill
sort Ring
  sort R = ?
  const zero: R                       -- open obligation
  const one:  R

  operation add(a: R, b: R) -> R
  operation mul(a: R, b: R) -> R

  rule add_identity_left:  add(zero, ?a) = ?a
  rule add_identity_right: add(?a, zero) = ?a
  rule mul_identity_left:  mul(one, ?a)  = ?a
  rule mul_identity_right: mul(?a, one)  = ?a
end

-- A concrete instance fills the obligations:
fact Implementation[Ring[R = Int64]]
  rule zero = 0
  rule one  = 1
  rule add(?a, ?b) = anthill.prelude.Int64.add(?a, ?b)
  rule mul(?a, ?b) = anthill.prelude.Int64.mul(?a, ?b)
end
```

Note: an implementation that supplies `rule zero = some_effectful_expr` would type-check against the operation signature but fail the foldability check at the implementation-pairing step (§Validator → `Constant` fact lifecycle). This catches a class of error that today's bodyless-operation form silently admits.

### Const-expression composition (post-026)

Once proposal 026's evaluator handles arithmetic and other-const references at load time:

```anthill
const PI:        Float = 3.14159265358979
const TWO_PI:    Float = 2.0 * PI
const HALF_PI:   Float = PI / 2.0
```

Cycles (`const A = B + 1; const B = A + 1`) are detected by the SCC pass over the const-dependency graph (§Cycle detection) and rejected with a cycle-path diagnostic.

## Interaction with proposals 027.1 and 037 (allocators)

Per proposal 027.1, fresh-allocator operations carry `effects Modify[result]`:

```anthill
-- stdlib/anthill/prelude/cell.anthill:20-21
operation new(v: V) -> Cell
  effects Modify[result]
```

Their declared effect row is non-empty, so the §Validator rejects them as `const` bodies (and `Cell.new` is an operation, invoked with `()`). `const COUNTER: Cell[Int64] = Cell.new(0)` is a load-time error: "body calls operation `Cell.new` with non-empty effect row `{Modify[result]}` — not foldable."

This is the intended result. A const denotes value-level referential transparency: two reads of the same const are observationally indistinguishable. An allocator violates that — two reads of a load-time-initialised cell are the *same handle*, but the user-level semantics ("this constant has identity, mutating it from one site changes the other") rarely matches what a reader of `const COUNTER: ...` expects. If a load-time singleton is genuinely wanted, declare the operation explicitly:

```anthill
operation counter() -> Cell[Int64]
  effects Modify[result]
  = Cell.new(0)
```

…and call it at use sites. The explicit signature makes the effect visible to readers.

Map/Substitution/Stream's stdlib signatures are mid-migration to 027.1 — `cell.anthill` is up to date, `map.anthill` and `substitution.anthill` still have bare `empty()` and are tracked as a follow-up cleanup (TODO at `docs/proposals/037-anthill-state-model.md` §327). The validator's rejection rule fires off the declared effect row at the moment of fold; once the migration completes, all allocators will be rejected uniformly without 039 needing further changes.

## Equational reasoning

The proposal pivots on referential transparency: a 0-arg operation with an empty declared effect row and a foldable body denotes the same value at every occurrence. Multiple occurrences may be replaced by a shared value without changing meaning. The generativity question (`Cell.new() ≠ Cell.new()`, SML's generative functor application, `rand()`) is handled outside this proposal — 027.1's `Modify[result]` marks any operation whose call sites can't be collapsed, and the §Validator excludes those. The classical framing is Plotkin & Power's *Algebraic Operations and Generic Effects* (2003), `new : 1 → Loc` as the canonical "no input, still not pure" example; anthill's effect system encodes the same distinction via 027.1's row.

## Out of scope

- **Parametric constants** (`const empty[T]: List[T] = nil`). Falls into the operation-with-body form (`operation empty[T] -> List[T] = nil`); the `const`-keyword shorthand is intentionally monomorphic in v1. Defer. Note this escape hatch is gated on proposal 042 (bracketed type parameters on operations) landing.
- **Multi-clause "constants"**. Use the long form (`operation` + multiple `rule` clauses or a `match` body). `const` is the explicit declaration of "this name has one foldable value."
- **Cross-KB override semantics**. Can a downstream namespace redefine an imported constant? Default: no. Override mechanism is a separate proposal in proof-context / scoped-KB territory.
- **Allocator-as-const ergonomics**. The "singleton cell at load time" pattern (`const COUNTER: Cell[Int64] = Cell.new(0)` under the pre-027.1 effect model) is rejected by this proposal's validator; the explicit-operation workaround in §Interaction with proposals 027.1 and 037 covers the same need with the right effect signature visible to readers.

## Resolved questions

The following were open in earlier drafts and are now settled:

1. **Call-site sugar scope (was Q1).** The bare-identifier rule applies to any 0-arg operation with an empty declared effect row, not specifically to `const`-declared names. Clean now that 027.1 puts allocators in the parens camp via their declared row.
2. **`Constant` reflection fact (was Q2).** Add it. Small, focused, parallels `Description` and `Implementation`. See §Reflection and §Validator → `Constant` fact lifecycle for the multi-Implementation refinement.
3. **Description-block placement (was Q3).** Yes — identical treatment to operations.
4. **`const` inside an operation body (was Q4).** No — `let` already exists in body scope with the right semantics. `const` is a namespace/sort-scope declaration. Reduces grammar surface.
5. **Singleton-handle constants (was Q5).** Reject — 027.1's `Modify[result]` on allocators causes the validator to refuse `const COUNTER: Cell[Int64] = Cell.new(0)`. The workaround (explicit operation with the effect signature) is documented in §Interaction with proposals 027.1 and 037.

## Open questions

All four were **resolved 2026-06-15** (see the per-item notes below and the *Design revision* at the top). They were surfaced in the 2026-05-28 cleanup pass and gated Phase 3+4; that gate is now lifted.

A. **Foldable-subset boundary — let-bindings in const bodies? — RESOLVED 2026-06-15: there is no subset.** Foldability is now "pure + evaluates to a value within `step_cap`," run by the real evaluator (§Foldability). `let` / `match` / recursion are handled natively, so the let-binding question dissolves; e.g. `const X: Float = { let p = PI; 2.0 * p }` just folds. The only static gate is purity (empty declared row); termination is a budgeted dynamic check; dependency cycles are caught by §Cycle detection. This also drops the bespoke "fold-mode" evaluator in favour of reusing WI-179's.

B. **Bare-name precedence vs ADT-variant resolution. — RESOLVED 2026-06-15: ambiguity-is-an-error, no precedence ladder.** Kernel-language §6 declares bare names like `Open` may resolve to an ADT variant (`WorkStatus.Open`, via *variant exposure*) and a step resolving to ≥2 distinct symbols is an ambiguous load/query error. The decision: a `const` (and a bare operation reference, now a first-class function value) simply **joins that existing candidate set** — it is *not* a new precedence question. Scope-nearest still wins; a same-step tie (e.g. `const nil` and `List.nil` both in scope) is an ambiguous error you fix by qualifying. The blast radius (a colliding bare name like `nil` becoming ambiguous) is the pre-existing cost of *any* two same-short-name symbols, not new to const. Needs no new §6 precedence text — only one sentence making `const`s and bare operation references value-denoting in term position. See §Call-site semantics for the full statement (and the related value-semantics / first-class-operation decisions in the *Design revision 2026-06-15*).

C. **Foldability of Implementation-supplied bodies — host-language case. — RESOLVED 2026-06-15: reuse the realization obligation lifecycle.** A bodyless host-supplied `const` (value from the host, e.g. `webots::…::CHANNEL_BROADCAST`) is just a realization obligation (`Implementation`/`Obligation`/`CarrierBinding`), so it rides that lifecycle rather than a const-specific trust path:
   - **spec-only mode** (no codegen): assert the obligation `TrustedConstant(name, type[, profile])` (type known, value pending); uses of the const stay **symbolic** — typed against `T`, not folded to a literal. Correct for spec verification (reason about the type + that a host supplies it).
   - **codegen**: when it echoes back the host value, **discharge** to the full `Constant(name, type, value, profile)`.
   This composes with §Foldability: anthill-bodied consts fold eagerly at load (value known); host-bodied consts ride the obligation track until codegen. `TrustedConstant` *is* the obligation; `Constant` *is* the realized fact — no new mechanism.

D. **Profile-keyed `Constant` reflection — concrete schema. — RESOLVED 2026-06-15: downstream-filter, no ambient profile.** This is the host-supplied axis of C: an **anthill-bodied** const has one profile-independent value (pure body, folded once) → `profile = default`, single fact; a **host-supplied** const is the only one that can differ per target → per-profile `Constant(name, type, value, profile)` facts emitted as each profile's `Implementation` discharges. Queries match `Constant(name: "X", ?)` and get all profile variants; the **consumer filters**. No "current profile" concept is added to the resolver/typer — that is a broad new ambient context, and the driving case (lf1 webots) is single-profile, so it would be speculative. Revisit only when a genuine multi-profile const appears.

## Migration / phasing

Each phase lands independently with its own tests, except where a phase depends on another proposal landing first.

**Phase 1 — grammar + desugaring.** Add `const` to `grammar.js`, the parser/converter, and the loader. Bodyless and body forms both. Slots into `_body_namespace` and `_body_sort`. No validator yet — just sugar that produces the operation form. Test that `set_channel(em, BROADCAST_CHANNEL)` parses, desugars to the operation form, and the operation call works at runtime.

Independent of any other in-flight proposal.

**Phase 2 — call-site value-denotation.** Extend the resolver: a bare `const` reference denotes its (memoized) value; a bare `operation` reference denotes the operation as a first-class function value (`Value::OpRef`); `()` is application/invocation. Tests: bare `BROADCAST_CHANNEL` is its value; `map(xs, increment)` passes an op without a lambda; `f(a)` applies a function-valued const; `g()` forces a nullary-function const (`g ≠ g()`); `K()` on a non-function const is a type error; `kb()` still invokes; a same-step tie of ≥2 value-denoting candidates is an ambiguous load error.

Open Question B is resolved (see Open questions); no remaining precondition. NOTE: the "bare operation = first-class function value" half is a language-wide addition (runtime `Value::OpRef` exists; source-level eta + effect-row-on-op-value needs typer wiring) and may be split into its own proposal (see *Design revision 2026-06-15*).

**Phase 3 — validator.** Add the foldability check at load time. Land:
- The foldability check (§Foldability): the purity gate + `step_cap`-bounded eager fold via the real evaluator (WI-179) — no separate fold-only evaluator.
- Cycle detection over the const-dependency graph (§Cycle detection).
- `Constant` reflection-fact emission (§Validator → `Constant` fact lifecycle).
- The same check applied at `Implementation`-pairing for bodyless consts.

Preconditions: proposal 026's evaluator has a fold-mode entry point (no-environment, no-effects, returns `Result<Value, FoldError>`). Open Questions A, C, D resolved.

**Phase 4a — concrete-literal adoption.** Convert lf1 webots sentinels first (BROADCAST_CHANNEL, motor velocity-mode infinity), then safety_common's `D_MIN`/`D_MAX`. These need only Phase 1+2+3 with the primitive-literal subset of foldability; no upstream-proposal dependency.

**Phase 4b — algebraic-identity adoption.** Stdlib `Ring.zero`, `Group.identity`, etc. — the bodyless-const-over-parametric-sort case. Gated on proposal 042 (bracketed type parameters on operations) since the parametric-operation desugaring (`operation empty[T] -> List[T] = nil`) needs the bracket form in `operation_declaration`.
