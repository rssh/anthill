# 039 — Term-Level Named Constants

## Status

Draft — cleanup pass 2026-05-28: dropped stale Cell.new "effect-pure" threads (superseded by 027.1), pinned the foldable subset and cycle-detection stage, resolved the original Open Questions, surfaced four new ones (A–D) that gate Phase 3+4.

Driver is WI-084: webots binding sentinels and safety-proof magic numbers need a named, typed, single-point-of-definition shape that is unifiable as the underlying primitive type at every use site. Today's workarounds — `entity NAME` + a side fact, or unit-sort-with-coercion — fail that requirement.

## Depends on

- [018-expressions-and-operation-implementation](018-expressions-and-operation-implementation.md) — operation expression bodies. A constant is a 0-arg operation whose body is the value.
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
- Resolver: new symbol-kind check at term-position resolution (bare-call sugar for 0-arg ops with empty declared effect row — broader than just constants; see §Call-site sugar).
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

A `const` is sugar for a **0-arg operation with an empty declared effect row**, optionally with an expression body. The kernel never sees a `Const` construct — it sees the desugared operation. The §Validator is what gives `const` its meaning.

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

Both forms produce a 0-arg operation with no `effects` clause (i.e. an empty declared effect row). This is what makes the call-site sugar apply (§Call-site sugar) and what permits load-time folding (§Validator).

### Validator

`const` enforces three conditions beyond what a plain `operation` requires:

1. **Zero arguments.** Required by the surface grammar — `const NAME: T = ...` has no parameter list.
2. **Empty declared effect row.** The desugared operation has no `effects` clause (equivalently, `effects ()` once 045's empty-set syntax is in). User attempts to add one are rejected at parse time — the `const` keyword's grammar position doesn't admit an effects clause.
3. **Foldable body** (when body is present). See §Foldable subset below. A `const` whose body is not foldable is a load-time error with a pointer to the offending sub-expression.

The same foldability check applies to **every anthill-side body** that fills the obligation — whether it is the declaration body, or a body supplied later via an `Implementation` fact's rule clauses. Host-language `Implementation`s (Rust / Scala / C++) waive the check, since the kernel cannot inspect their body; the resulting `Constant` reflection fact (see §Reflection) is omitted in the host-language case until codegen has produced a folded literal it can echo back.

#### Foldable subset

A body is **foldable** iff it lies in the following closed grammar, evaluated by proposal 026's evaluator in *fold mode* (no environment, no allocation, no effects):

- **Literals** of the primitive sorts: `Int64`, `BigInt`, `Float`, `String`, `Bool`, `Char`.
- **References** to other `const`-declared names whose own bodies are foldable. (Forward references across files are allowed within one load pipeline pass; see §Cycle detection.)
- **Calls to operations whose declared effect row is empty** *and* whose body is itself foldable. This recursively excludes allocators (`Cell.new`, `Map.empty`, `Substitution.empty`) since they carry `Modify[result]` per 027.1.
- **Entity construction** with foldable arguments — `Point(x: 1.0, y: 2.0)` is foldable; an entity field set to a Cell or arena handle is not.

Explicitly **not** foldable: logical variables (`?`, `?name`); operation calls with any declared effect; expressions that depend on the evaluator's activation stack (let-bindings inside a body — discussed under §Open Questions whether to admit); KB queries; pattern matching (use the long-form operation if you need it).

Implementation note: fold mode is a designated entry point on proposal 026's evaluator that returns `Result<Value, FoldError>` instead of the streaming `LogicalStream`. The check is *static* — no runtime branch reads the value; foldability failure is a load-time diagnostic.

#### Cycle detection

After `scan_definitions` populates the symbol table but before expression typing runs, the loader builds the **const-dependency graph** — one node per `const`-declared symbol, edges to every other `const` symbol referenced from its body. Tarjan's SCC pass detects cycles; any SCC of size > 1, or a self-edge, is reported with the cycle path and rejected.

Cross-namespace forward refs are allowed (the dependency graph is built over the whole loaded set, not file-by-file). The order in which folded values are computed is the reverse topological order of the SCC quotient graph.

#### `Constant` reflection fact lifecycle

For declaration-with-body `const`, the `Constant(name, type, value)` fact is asserted at the end of fold-mode execution for that declaration — i.e. once during load, in topological order.

For bodyless `const` declarations filled by an `Implementation` fact, the fact is asserted **at Implementation pairing**: when the loader pairs an `Implementation[S]` fact with the obligation `S.NAME`, it re-runs fold mode over the supplied rule body. Success asserts the `Constant` fact; failure rejects the Implementation.

Under proposal 037's profile-keyed Implementations, multiple Implementations may coexist (one per profile). Each emits its own `Constant` fact keyed by profile — the reflection schema is `Constant(name, type, value, profile)` (profile defaults to a `default` symbol when the Implementation does not declare one). The load-time selector picks one Implementation per profile and binds the corresponding `Constant` for downstream queries.

### Call-site sugar — bare for empty-row 0-arg, parens for everything else

In term position, an identifier `Name` resolves to a 0-arg operation call when `Name` denotes an operation whose **declared effect row is empty** (no `effects` clause, or `effects ()`). For 0-arg operations with any declared effect, the explicit `Name()` form is required.

`Name` covers both short names (`BROADCAST_CHANNEL`, `zero-val`) and qualified paths (`PersistentMap.empty`, `anthill.prelude.Numeric.zero-val`). The resolver's existing dotted-path lookup runs first; the call-site sugar then applies uniformly to whatever symbol the path resolves to. As of today, a qualified bare form like `PersistentMap.empty` (no parens) is reported as an unresolved name (the dotted-path resolver returns the operation symbol but the term-position rule expects a value); Phase 2 lifts both short and qualified bare forms in one go.

```anthill
set_channel(em, BROADCAST_CHANNEL)        -- bare; BROADCAST_CHANNEL is a 0-arg op with empty row (a const)
let c = Cell.new(0)                        -- parens required: Cell.new has effects Modify[result] (027.1)
let m = Map.empty()                        -- parens required: Map.empty has effects Modify[result] (027.1)
let zv = anthill.prelude.Numeric.zero-val  -- bare; zero-val is a 0-arg op with empty row
```

This is broader than constants — it's a property of 0-arg operations with empty rows generally. `const`-declared names ride on the same rule. Cf. Scala 3's `def x = 42` (parenless) vs `def x() = 42`; the opposite of Eiffel's uniform-access principle, which hides effects and is widely cited as the wrong call.

The rule applies to the **declared** effect row, not to the inferred body-flow row. A 0-arg op declared `effects ()` whose body calls `Cell.new` is still bare-callable at the use site — the discrepancy between declared and inferred row is a separate diagnostic (proposal 045) and not this proposal's concern.

A row-polymorphic declaration (`effects ?E` with `E` unbound) is **not** an empty row; such ops require parens. This is conservative — if a future caller could instantiate `?E` to a non-empty set, the call site shouldn't be bare.

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

Their declared effect row is non-empty, so the §Validator rejects them as `const` bodies and the §Call-site sugar requires parens. `const COUNTER: Cell[Int64] = Cell.new(0)` is a load-time error: "body calls operation `Cell.new` with non-empty effect row `{Modify[result]}` — not foldable."

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

These are the live questions surfaced in the cleanup pass; the proposal can land Phase 1+2 without resolving them, but Phase 3+4 are blocked until they are.

A. **Foldable-subset boundary — let-bindings in const bodies?** §Foldable subset currently excludes let-bindings inside a body (they require the evaluator's activation stack). But `const TWO_PI: Float = 2.0 * PI` already requires the evaluator to consult the const-environment. Letting `const X: Float = { let p = PI; 2.0 * p }` work is a small extension if the foldable subset is "literals + prim ops + const-refs + entity construction + let over the same." Decide before Phase 3.

B. **Bare-name precedence vs ADT-variant resolution.** Kernel-language §6 (around line 1419-1423) declares bare names like `Open` may resolve to an ADT variant (`WorkStatus.Open`) and explicitly prefers "ambiguous error" over silent wins. Phase 2 adds 0-arg-op call as a new candidate. When the same bare name has both a 0-arg-op-with-empty-row and an ADT-variant binding in scope, what does the resolver do — ambiguous error, or new precedence rule? The cleanest answer is "ambiguous error" — but that breaks any name that happens to collide (e.g. `nil` as an ADT variant of `List` and as a 0-arg op somewhere else).

C. **Foldability of Implementation-supplied bodies — host-language case.** §Validator says host-language `Implementation`s waive the foldability check and the `Constant` fact emission is deferred to codegen echo-back. But codegen doesn't always run in the same load cycle (e.g. spec-only verification mode). Specify whether `Constant` is asserted at codegen-completion or whether a separate trust marker (e.g. `TrustedConstant`) is asserted at Implementation-pairing pending codegen confirmation.

D. **Profile-keyed `Constant` reflection — concrete schema.** §Validator → `Constant` fact lifecycle proposes `Constant(name, type, value, profile)`. The kernel-language spec doesn't yet have a "current profile" concept the resolver can scope a query against — KB queries match `Constant(name: "X", ?)` and get all profile variants. Confirm this is the wanted semantics (downstream consumer filters), or whether the resolver should pre-filter by an ambient profile binding.

## Migration / phasing

Each phase lands independently with its own tests, except where a phase depends on another proposal landing first.

**Phase 1 — grammar + desugaring.** Add `const` to `grammar.js`, the parser/converter, and the loader. Bodyless and body forms both. Slots into `_body_namespace` and `_body_sort`. No validator yet — just sugar that produces the operation form. Test that `set_channel(em, BROADCAST_CHANNEL)` parses, desugars to the operation form, and the operation call works at runtime.

Independent of any other in-flight proposal.

**Phase 2 — call-site sugar.** Extend the resolver: an identifier in term position that resolves to a 0-arg op with empty declared effect row is treated as a call. Test that bare `BROADCAST_CHANNEL` works at use sites; the parens form still works for any operation; ops with any declared effect still require parens.

Precondition: Open Question B (bare-name precedence vs ADT-variant resolution) is resolved.

**Phase 3 — validator.** Add the foldability check at load time. Land:
- The foldable-subset checker (§Foldable subset).
- Cycle detection over the const-dependency graph (§Cycle detection).
- `Constant` reflection-fact emission (§Validator → `Constant` fact lifecycle).
- The same check applied at `Implementation`-pairing for bodyless consts.

Preconditions: proposal 026's evaluator has a fold-mode entry point (no-environment, no-effects, returns `Result<Value, FoldError>`). Open Questions A, C, D resolved.

**Phase 4a — concrete-literal adoption.** Convert lf1 webots sentinels first (BROADCAST_CHANNEL, motor velocity-mode infinity), then safety_common's `D_MIN`/`D_MAX`. These need only Phase 1+2+3 with the primitive-literal subset of foldability; no upstream-proposal dependency.

**Phase 4b — algebraic-identity adoption.** Stdlib `Ring.zero`, `Group.identity`, etc. — the bodyless-const-over-parametric-sort case. Gated on proposal 042 (bracketed type parameters on operations) since the parametric-operation desugaring (`operation empty[T] -> List[T] = nil`) needs the bracket form in `operation_declaration`.
