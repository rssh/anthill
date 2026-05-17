# 039 — Term-Level Named Constants

## Status

Draft. Driver is WI-084: webots binding sentinels and safety-proof magic numbers need a named, typed, single-point-of-definition shape that is unifiable as the underlying primitive type at every use site. Today's workarounds — `entity NAME` + a side fact, or unit-sort-with-coercion — fail that requirement.

## Depends on

- [018-expressions-and-operation-implementation](018-expressions-and-operation-implementation.md) — operation expression bodies. A constant is a 0-arg operation whose body is the value.
- [026-expression-evaluator](026-expression-evaluator.md) — load-time evaluator. The validator that gates `const` runs the evaluator over the body in load-time mode.

## Relates to

- [037-anthill-state-model](037-anthill-state-model.md) — `Cell.new` is declared effect-pure today. Whether `const C: Cell[Int] = Cell.new(0)` is admissible reduces to 037's effect story for allocation; this proposal stays compatible with the 037-as-it-stands answer and with a future revision.
- WI-084 (driver), WI-083 (Bytes — adjacent magic-number territory), WI-156 (scaland resync).

## Affects

- Kernel-language spec §5 (new sugar form documented as §6.X under "Syntactic Sugar"), §6.
- Grammar (`grammar.js`): one new construct `Const`, both with body and bodyless.
- Resolver: new symbol kind check at term-position resolution (bare call sugar for pure 0-arg ops — broader than just constants; see §Call-site sugar).
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

The `entity BROADCAST_CHANNEL` workaround declares a name but binds it to an entity term, not to the `Int` `-1`. The call-site `set_channel(em, BROADCAST_CHANNEL)` fails to type-check against `set_channel(em: Emitter, channel: Int)`. Callers fall back to writing the literal `-1`, losing the name. The same shape recurs:

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
| Enum-like Int values | **Neutral** — entity-side identity usually also wanted. |

The host-binding case and algebraic-identity case are the load-bearing drivers; the rest are nice-to-haves.

## Design

A `const` is sugar for a **0-arg pure operation**, optionally with an expression body. The kernel never sees a `Const` construct — it sees the desugared operation. The validator is what gives `const` its meaning.

### Surface form

```
Const ::= DescriptionBlock*
            [Visibility] 'const' Name ':' Type ['=' ConstExpr]
            ['meta' ':' Meta]
```

Two shapes:

```anthill
const BROADCAST_CHANNEL: Int = -1        -- concrete (body given)
const zero: R                            -- abstract (open obligation)
```

The type annotation is **always required**, even with body. This is deliberate: a constant is a named, typed value; the type is part of the name's contract, not an inference target. (Unlike `let` inside an operation body, which infers freely.)

**Visibility.** Constants accept the inline `Visibility` prefix (`internal`/`export`/`public`), matching the grammar's intent for operations (`grammar.js:305`) and the standing convention for sorts and entities (`grammar.js:199, 209, 218`). Per-declaration form is encouraged for constants since it sits next to the value — the reader sees `export const D_MIN: Float = 1.0` at the declaration site without scanning to a separate `export` list. The namespace-level `export` clause also lists const names (same as operations / sorts) for namespaces that prefer the centralized form.

```anthill
namespace anthill.examples.lf1.webots.Emitter
  -- Per-declaration form (recommended for const):
  export const BROADCAST_CHANNEL: Int = -1

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

Both forms produce a 0-arg operation with no `effects` clause. The lack of effects is what makes the operation pure, what makes the call-site sugar apply, and what permits load-time folding.

### Validator

`const` enforces three conditions beyond what a plain `operation` requires:

1. **Zero arguments.** Required by the surface grammar — `const NAME: T = ...` has no parameter list.
2. **No effects.** The desugared operation has no `effects` clause; user attempts to add one are rejected at parse time (the `const` keyword's grammar position doesn't admit an effects clause).
3. **Foldable body** (when body is present). The body must be a closed expression that the load-time evaluator (proposal 026) can reduce to a single ground term. Conditions:
   - All references resolve at load time.
   - No free logical variables.
   - Only calls to other pure operations whose bodies are themselves foldable. Cycles rejected.
   - No effectful constructs.

A `const` whose body is *not* foldable is a load-time error with a pointer to the offending sub-expression.

### Call-site sugar — bare for pure 0-arg, parens for effectful

In term position, an identifier `Name` resolves to a 0-arg operation call when `Name` denotes an operation declared with no `effects` clause (or `effects ()`). For effectful 0-arg operations, the explicit `Name()` form is required.

```anthill
set_channel(em, BROADCAST_CHANNEL)       -- bare; BROADCAST_CHANNEL is a pure 0-arg op (a const)
let c = Cell.new(0)                       -- parens required for effectful ops
let m = Map.empty()                       -- parens, even though Map.empty has no effects today (037)
```

This is broader than constants — it's a property of pure 0-arg operations generally. `const`-declared names ride on the same rule. Cf. Scala 3's `def x = 42` (parenless) vs `def x() = 42`; the opposite of Eiffel's uniform-access principle (which hides effects and is widely cited as the wrong call).

Note that 037-style "pure but identity-distinguishing" allocators (`Map.empty`, `Cell.new`) sit in an interesting position under this rule: by 037's effect declaration they qualify as "pure 0-arg" and would be bare-callable. Whether the call-site sugar should *also* require empty-effect-row at *runtime* (not just at declaration), so identity-allocating ops keep their parens, is captured under Open Questions.

### Reflection

Every `const NAME: T = EXPR` produces, in addition to the desugared operation, an automatic reflection fact:

```
fact Constant(name: "anthill.examples.lf1.webots.BROADCAST_CHANNEL",
              type:  Int,
              value: -1)
```

For the bodyless case (no value known until an implementation arrives), no `Constant` fact is asserted at declaration; instead, the operation's open-obligation state is observable through the usual `Operation` / `Implementation` reflection. When an implementation provides a foldable body, the kernel asserts the `Constant` fact lazily.

The `Constant` fact is what codegen, IDE tooling, and KB queries use to enumerate constants. It is *additional* to — not a replacement for — the desugared operation, mirroring how proposal 022 already adds `TypeOf` facts alongside expression occurrences.

## Examples

### Concrete primitive constant — webots broadcast channel

```anthill
sort anthill.examples.lf1.webots.Emitter
  import anthill.prelude.{Int, Float, Unit, String, Bool, Modify}
  export Emitter, BROADCAST_CHANNEL
  export set_channel, get_channel, send

  -- Sentinel for broadcast (mirrors webots::Emitter::CHANNEL_BROADCAST = -1).
  const BROADCAST_CHANNEL: Int = -1

  operation set_channel(self: Emitter, channel: Int) -> Unit
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
fact Implementation[Ring[R = Int]]
  rule zero = 0
  rule one  = 1
  rule add(?a, ?b) = anthill.prelude.Int.add(?a, ?b)
  rule mul(?a, ?b) = anthill.prelude.Int.mul(?a, ?b)
end
```

Note: an implementation that supplies `rule zero = some_effectful_expr` would type-check against the operation signature but fail the const-validator's "implementation must be foldable, effect-free" check at the implementation-pairing step. This catches a class of error that today's bodyless-operation form silently admits.

### Const-expression composition (post-026)

Once proposal 026's evaluator handles arithmetic and other-const references at load time:

```anthill
const PI:        Float = 3.14159265358979
const TWO_PI:    Float = 2.0 * PI
const HALF_PI:   Float = PI / 2.0
```

Cycles (`const A = B + 1; const B = A + 1`) are detected by topological sort during the fold phase and rejected with a cycle-path diagnostic.

## Interaction with proposal 037 (Cell, allocators)

Proposal 037 declares allocators like `Cell.new`, `Map.empty`, `Substitution.empty` as **effect-pure but identity-distinguishing**:

> Construction is allocation, not mutation — it doesn't modify any existing Cell, so it doesn't carry `Modify[anything]`. […] Two calls to `Cell.new(0)` produce two distinct cells even with identical initial values. Identity is allocation-time, not value-time. (037 §2 / §Identity)

Under 037-as-it-stands, this proposal's validator admits `Cell.new(0)` as a `const` body — it has no effect declaration, and "foldable" reduces to "the evaluator can produce a single ground term for this call." That produces a useful semantics:

```anthill
const COUNTER: Cell[Int] = Cell.new(0)
```

This is a **singleton cell**: the body folds once at load time, allocating exactly one Cell handle; all references to `COUNTER` are that same handle. Matches the C++/Rust `static`/`constexpr`-anchored singleton pattern.

The "`Cell.new() ≠ Cell.new()`" property still holds for two *separate* call sites (`let c1 = Cell.new(0); let c2 = Cell.new(0)`) — different syntactic occurrences, different folds, different handles. A `const` collapses them: one syntactic occurrence (the const declaration), one fold, one handle.

If 037 is later revised to give `Cell.new` an explicit effect (see "Brainstorm carryover" below), the validator's "no effects" condition would reject `Cell.new(0)` as a const body and force the user to write the long form with explicit allocation context. The proposal-039 surface and desugaring remain unchanged either way; only the validator's pass/fail flips per allocator.

## Equational reasoning and generativity

The proposal pivots on a single equational fact: a 0-arg operation with no effects and a foldable body is *referentially transparent*. Multiple occurrences may be replaced by a shared value without changing meaning. This is the standard algebraic-effects framing — pure computations admit common-subexpression elimination and let-introduction freely; effectful ones don't.

When this breaks down — operations like `Cell.new`, `rand()`, SML's generative functor application — the relevant literature is:

| Work | Relevance |
|---|---|
| Pitts & Stark, *nu-calculus* (1993) | Formal calculus for fresh-name generation as an effect. |
| Milner, Tofte, Harper, *Definition of SML* (1990, '97 rev.) | Generative functor application — same shape as `Cell.new() ≠ Cell.new()` lifted to types. |
| Plotkin & Power, *Algebraic Operations and Generic Effects* (2003) | `new : 1 → Loc` as the canonical "no input, still not pure" example. |
| Plotkin & Pretnar, *Handlers of Algebraic Effects* (2009) | Handler framework underlying Frank / Eff / Koka. |
| Levy, *Call-By-Push-Value* (1999) | Syntactic value/computation distinction — a const is a value, `Cell.new()` is a computation. |
| Leijen, *Koka* (2014–) | Row-polymorphic effects with `heap` for allocation, `ndet` for randomness. |

Proposal 039 takes the conservative position: rely on the existing anthill effect-declaration mechanism to mark non-pure 0-arg operations. The deeper question of whether 037-style "pure-but-identity-distinguishing" is the right effect-system stance for anthill is out of scope here and tracked separately (see "Brainstorm carryover").

## Out of scope

- **Parametric constants** (`const empty[T]: List[T] = nil`). Falls naturally into the operation-with-body form (`operation empty[T] -> List[T] { nil }`); the `const`-keyword shorthand is intentionally monomorphic in v1. Defer.
- **Multi-clause "constants"**. Use the long form (`operation` + multiple `rule` clauses or a `match` body). `const` is the explicit declaration of "this name has one foldable value."
- **Cross-KB override semantics**. Can a downstream namespace redefine an imported constant? Default: no. Override mechanism is a separate proposal in proof-context / scoped-KB territory.
- **The `Cell.new` effect question**. Whether `Cell.new` should carry an `Alloc`/`Fresh`/`Modify[Heap]` effect is a 037 revision, not a 039 concern.

## Open questions

1. **Call-site sugar scope** — should the bare-identifier rule apply to *any* operation with no declared effects, or specifically to `const`-declared names? The proposal recommends *any pure 0-arg op*, which gives a clean rule but admits `let m = Map.empty` (no parens). The trade-off is consistency vs the loss of the visual "this call site does something" cue for identity-distinguishing allocators. **Suggested resolution**: bare for `effects ()` operations regardless of declaration form; revisit if/when 037 gets an explicit allocator effect, which would naturally re-park `Map.empty`/`Cell.new` in the parens camp.

2. **Const fact reflection — `Constant` or rely on `Operation` + body inspection?** The proposal adds a `Constant(name, type, value)` reflection fact. Alternative: don't add a new fact kind; let consumers query `Operation` facts with arity 0, no effects, and walk to the body for the value. Trade-off: ergonomics of consumer queries vs proliferating reflection-fact kinds. **Suggested resolution**: add `Constant` (small, focused, parallels `Description` and `Implementation`).

3. **Description-block placement** — does the standard `DescriptionBlock*` prefix apply to constants the same way as to other declarations? **Suggested resolution**: yes, identical to operations.

4. **`const` inside an operation body — does it exist?** Today, operation bodies have `let`-binding (proposal 018). Should there also be `const` at body scope? **Suggested resolution**: no — `let` already exists with the right semantics inside a body. `const` is a namespace/sort-scope declaration. Reduces grammar surface.

5. **Singleton-handle constants — admit or reject?** `const COUNTER: Cell[Int] = Cell.new(0)` produces a load-time-allocated singleton under 037-as-it-stands. Useful (matches `static AtomicI32` patterns); but the user-visible semantics ("this constant has identity, two references to it are the same cell") may surprise readers who expect a constant to behave like a value-typed primitive. **Suggested resolution**: admit; document explicitly as the singleton pattern. Re-litigate if 037 revises Cell.new's effect.

## Migration / phasing

**Phase 1 — grammar + desugaring.** Add `const` to `grammar.js`, the parser/converter, and the loader. Bodyless and body forms both. No validator yet — just sugar that produces the operation form. Test that `set_channel(em, BROADCAST_CHANNEL)` parses, desugars to the operation form, and the operation call works at runtime.

**Phase 2 — call-site sugar.** Extend resolver: an identifier in term position that resolves to a 0-arg op with no `effects` clause is treated as a call. Test that bare `BROADCAST_CHANNEL` works at use sites; parens form still works for any operation; effectful 0-arg ops still require parens.

**Phase 3 — validator.** Add the foldability/no-effects/no-args check at load time. Test rejection of effectful bodies and unfoldable expressions. Emit `Constant` reflection facts.

**Phase 4 — adoption.** Convert lf1 webots sentinels first (BROADCAST_CHANNEL, motor velocity-mode infinity). Then safety_common's `D_MIN`/`D_MAX`. Stdlib algebraic identities (`Ring.zero`, `Group.identity`, etc.) come with the algebra refresh, not as part of this proposal.

Each phase lands independently with its own tests.

## Brainstorm carryover

The work that surfaced this proposal also raised a question that does *not* belong here: **what effect, if any, should `Cell.new` (and `Map.empty`, `Substitution.empty`, `rand`) carry?** Today's 037 stance — pure-but-identity-distinguishing — is a non-standard choice in the algebraic-effects literature. Whether to keep it, or to introduce an `Alloc[Heap]` / `Fresh` / `ndet` effect that matches Koka / Frank / Eff, is a 037 revision worth its own proposal. This proposal stays compatible with either resolution; the validator's pass/fail flips per-allocator, but the surface and desugaring don't change.
