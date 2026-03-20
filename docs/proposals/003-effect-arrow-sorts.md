# Proposal 003: Effect Annotations on Arrow Sorts

**Status:** Merged into [002-arrow-sorts](002-arrow-sorts.md)
**Depends on:** [002-arrow-sorts](002-arrow-sorts.md)
**Affects:** Kernel Language Specification §5.4, §5.5, §5.6, §5.7, §11

## Motivation

The kernel language has an effect system (§5.5–5.7) that annotates operations with effects (`Modifies`, `Reads`, `Emits`, `Errors`, `Requires`). With arrow sorts (Proposal 002), functions become first-class values. The question arises: can a function-sorted value carry effect annotations?

This is a natural extension. An operation

```
operation op(x: A) -> R
  effects (Modifies S, Errors Err)
```

already has an implicit arrow sort `(A) => R`. The `effects` clause adds information about what side-effects `op` may perform. Making this explicit in the arrow sort — `(A) => R effect [Modifies(S), Errors(Err)]` — unifies operation signatures with function types and brings effects into the type system.

## Effectful Arrow Sort Syntax

An arrow sort may carry an effect annotation listing the effects the function may perform:

### Grammar

```
Type ::= ...
       | '(' TypeList ')' '=>' Type                               -- pure arrow
       | '(' TypeList ')' '=>' Type 'effect' '[' EffectList ']'   -- effectful arrow

TypeList   ::= (Type (',' Type)*)?
EffectList ::= Effect (',' Effect)*
```

The `effect` keyword and bracket-delimited list follow the same `Effect` productions as operation declarations (§5.5):

```
Effect ::= 'Modifies' '(' Name ')' | 'Reads' '(' Name ')'
         | 'Emits' '(' Name ')'   | 'Errors' '(' Name ')'
         | 'Requires' '(' Name ')'
```

### Examples

```
(A) => B                                      -- pure function (no effects)
(A) => B effect [Modifies(S)]                 -- stateful function
(A) => B effect [Errors(Err)]                 -- fallible function
(A) => B effect [Modifies(S), Errors(Err)]    -- stateful + fallible
() => A effect [Emits(Event)]                 -- thunk that emits events
(A) => B effect [Reads(Config)]               -- function that reads config
```

A pure arrow `(A) => B` is equivalent to `(A) => B effect []` (empty effect set).

## Consistency with Operation Declarations

An operation declaration with effects:

```
operation op(x: A, y: B) -> R
  effects (Modifies S, Errors Err)
```

has the arrow sort `(A, B) => R effect [Modifies(S), Errors(Err)]`. The `effects` clause on operations and the `effect [...]` annotation on arrow sorts express the same information. They are consistent — the `effects` clause is the declaration-level form; the arrow sort annotation is the type-level form.

When an operation name is used as a value (Proposal 002, §"Operation Names as Values"), its arrow sort includes the declared effects:

```
operation write(key: String, value: String) -> Bool
  effects (Modifies Store)

-- 'write' as a value has sort:
-- (String, String) => Bool effect [Modifies(Store)]
```

## Effect Subtyping

A function with fewer effects can be used where more effects are permitted:

> `(A) => B effect E₁` is a subtype of `(A) => B effect E₂` when `E₁ ⊆ E₂`.

In particular, a pure function `(A) => B` (empty effect set) is a subtype of any effectful arrow `(A) => B effect [...]`. This means:

- Pure functions can be passed wherever effectful functions are expected.
- A `map` operation expecting `(A) => B` (pure) rejects effectful functions — the caller must ensure purity.
- A `flatMap` operation expecting `(A) => F[T=B] effect [E]` accepts both pure and effectful continuations with effects contained in `E`.

```
operation map(fa: F[T = A], f: (A) => B) -> F[T = B]
-- f must be pure — no effects allowed

operation flatMap(fa: F[T = A], f: (A) => F[T = B]) -> F[T = B]
-- f is pure but returns an effectful computation F[T=B]
-- the effects are inside F, not on the arrow
```

## Composition Typing Rule

From §5.6, sequential composition of effectful operations yields effect union. With arrow sorts, this becomes a typing rule:

> If `f : (A) => B effect E₁` and `g : (B) => C effect E₂`, then `g . f : (A) => C effect (E₁ ∪ E₂)`.

The composed function may perform any effect that either component may perform.

## Connection to the Monadic Interpretation (§5.7)

Section 5.7 establishes that the state-passing and monadic interpretations of effectful operations are isomorphic. With effectful arrow sorts, this isomorphism becomes a type-level equivalence:

```
() => A effect [Modifies(S), Errors(Err), Emits(Ev)]
≡
M_E(A)
≡
Env → (A × Env × Ev list) + Err
```

An effectful thunk IS a monadic value. The effect annotation IS the monad.

**This equivalence is a theorem, not a design constraint.** Both the monadic style (abstract type constructor `F` from Proposal 001) and the effect-annotated style remain available as complementary tools:

- **Monadic style** (abstract `F`): for arbitrary monads (List, Parser, etc.) that don't correspond to built-in effects.
- **Effect style** (effect annotations): for the built-in effect kinds (`Modifies`, `Reads`, `Emits`, `Errors`, `Requires`) where the kernel provides semantic guarantees.

Users choose whichever is appropriate. They are interchangeable for the built-in effects.

## Effect Polymorphism

An abstract effect set allows writing code generic over effects:

```
sort E                                        -- abstract effect set

operation sequence(
  fa: () => A effect E,
  f: (A) => (() => B effect E)
) -> () => B effect E
```

This is equivalent to the monadic `flatMap` for the built-in effect monad. The abstract `E` plays the role of the abstract monad `F` — but at the effect level rather than the type-constructor level.

**Effect constraints** express requirements on the effect set:

```
-- This operation requires E to include Errors:
sort E
constraint has_errors: includes(E, Errors(Err))

operation try_or_default(
  fa: () => A effect E,
  default: A
) -> () => A effect E
```

The exact mechanism for effect constraints (sort constraints, effect subsorting, or a dedicated `includes` predicate) is left open for further design.

## The CpsMonad Hierarchy as Effects

The dotty-cps-async monad hierarchy maps to effect capabilities:

| dotty-cps-async | Effect requirement |
|---|---|
| `CpsMonad[F]` | No constraint on E (pure sequencing) |
| `CpsTryMonad[F]` | E includes `Errors(Err)` |
| `CpsEffectMonad[F]` | E includes `Modifies(...)` (delayed evaluation) |
| `CpsAsyncMonad[F]` | E includes async capability |

With effectful arrow sorts, the hierarchy can be expressed either as:
- Abstract type constructor `F` with operations (Proposal 002 style), or
- Abstract effect set `E` with effect constraints (this proposal's style).

Both are valid. The choice depends on whether the monad corresponds to built-in effects (use effect annotations) or is an arbitrary algebraic structure (use abstract `F`).

## Summary of Grammar Changes

```
-- Effectful arrow sort (extends Proposal 002):
Type ::= ...
       | '(' TypeList ')' '=>' Type 'effect' '[' EffectList ']'

EffectList ::= Effect (',' Effect)*
```

## Semantic Rules

1. `(A) => B effect E` is a sort when `A`, `B` are sorts and `E` is a valid effect list.
2. Effect subtyping: `E₁ ⊆ E₂` implies `(A) => B effect E₁ <: (A) => B effect E₂`.
3. Pure arrows are subtypes of effectful arrows: `(A) => B <: (A) => B effect E` for any `E`.
4. Composition typing: effects compose via union.
5. An operation's `effects` clause is consistent with its arrow sort's effect annotation.

## Backwards Compatibility

All existing syntax remains valid:

- `effects (...)` on operations — unchanged. The effect clause and the arrow sort annotation express the same information; they are consistent, not redundant.
- Operations without effects — their arrow sort is pure `(A) => B`, equivalent to `(A) => B effect []`.
- The state-passing interpretation (§5.6) and monadic interpretation (§5.7) — unchanged. Effect annotations on arrow sorts make these interpretations expressible at the type level but do not alter their semantics.

No existing valid program is invalidated by this change.
