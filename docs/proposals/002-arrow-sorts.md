# Proposal 002: Arrow Sorts (with Effect Annotations)

**Status:** Draft
**Depends on:** [001-sort-domain-unification](001-sort-domain-unification.md)
**Subsumes:** [003-effect-arrow-sorts](003-effect-arrow-sorts.md)
**Affects:** Kernel Language Specification §4, §5.2, §5.4, §5.5–5.7, §8.2, §11

## Motivation

Operations like `map` and `flatMap` take function arguments. In the current kernel, all operation parameters must be sort-typed — there are no function sorts. This forces **defunctionalization**: introducing auxiliary sorts and explicit `apply` operations for every function-passing pattern.

The stdlib already provides `Function{A, B}` with an `apply` operation — this works but obscures intent:

```anthill
-- Without arrow sorts (defunctionalized, current):
operation flatMap(fa: F{T = A}, k: Function{A = A, B = F{T = B}}) -> F{T = B}

-- With arrow sorts (direct):
operation flatMap(fa: F{T = A}, f: (A) -> F{T = B}) -> F{T = B}
```

Additionally, operations carry effect annotations. When functions become first-class values via arrow sorts, effect annotations should be expressible on arrow sorts too — unifying operation signatures with function types.

## Arrow Sort Syntax

If `A1, ..., An` are sorts and `R` is a sort, then `(A1, ..., An) -> R` is also a sort — the sort of functions from `A1, ..., An` to `R`.

### Grammar

```
Type ::= ...
       | '(' TypeList ')' '->' Type               -- pure arrow
       | '(' TypeList ')' '->' Type '@' Type      -- effectful arrow

TypeList ::= (Type (',' Type)*)?
```

The `@` token for effect annotation is consistent with the existing Pratt operator table, where `a -> b @ c` desugars to `arrow_effect(a, b, c)` in term position. The same syntax works in type position.

The parameter list is always parenthesized, which disambiguates `->` in type position from `->` in operation return type position:

```anthill
operation f(x: (A) -> B) -> C
--            ^---------^      arrow type (param has parens)
--                         ^^  operation return type
```

### Examples

```anthill
(Int) -> String                         -- unary function
(A) -> B                                -- polymorphic function
(A, B) -> C                             -- binary function
() -> A                                 -- thunk (nullary)
(A) -> F{T = B}                         -- Kleisli arrow
((A) -> B) -> (A) -> B                  -- higher-order function
(A) -> B @ Modifies(S)                  -- stateful function
(A) -> B @ Errors(Err)                  -- fallible function
(A) -> B @ (Modifies(S), Errors(Err))   -- stateful + fallible
() -> A @ Emits(Event)                  -- thunk that emits events
(A) -> B @ Reads(Config)               -- function that reads config
```

Arrow sorts associate to the right: `(A) -> (B) -> C` is `(A) -> ((B) -> C)`.

A pure arrow `(A) -> B` has an empty effect set. It is a subtype of any effectful arrow.

### Relationship to `Function{A, B}`

The arrow sort `(A) -> B` is sugar for `Function{A, B}` from stdlib. The existing `apply(f, x)` operation works on arrow-sorted values. The type checker treats them as equivalent:

```anthill
-- These are the same sort:
(Int) -> String
Function{A = Int, B = String}
```

## Term Application

To apply a function-sorted value, the term grammar gains term-headed application:

### Grammar

```
Term ::= ...
       | Term '(' [Term (',' Term)*] ')'      -- application
```

This generalizes the existing `Fn(name, args)` form. When the head is a variable of arrow sort, the application invokes the function:

```anthill
?f(?x)                                  -- apply function variable ?f to argument ?x
?f(?x, ?y)                              -- binary application
pure(?x)                                -- existing named application (unchanged)
bind-then(?f, ?g)(?x)                   -- chained: apply result of bind-then
```

Existing named function application `name(args)` is unchanged — it is a special case where the head is a name rather than an arbitrary term.

## Operation Names as Values

An operation name, used in a term position where an arrow sort is expected, denotes the operation as a function value:

```anthill
operation pure(a: A) -> F{T = A}

-- 'pure' in term position has sort (A) -> F{T = A}:
rule right_id: flatMap(?m, pure) = ?m
```

This is analogous to eta-expansion: the name `pure` stands for the function `lambda x -> pure(x)`.

**Disambiguation rule:** In a term `name(args)`, `name` is resolved as:
1. A named function application (existing `Fn` semantics), if `name` is a known operation/constructor name and `args` are provided.
2. A function value (eta-expanded), if `name` appears without arguments in a position expecting an arrow sort.

This is unambiguous: `pure(?x)` is application; `pure` alone (without parens) is a value.

## Consistency with Operation Declarations

An operation declaration with effects:

```anthill
operation op(x: A, y: B) -> R
  effects (Modifies(S), Errors(Err))
```

has the arrow sort `(A, B) -> R @ (Modifies(S), Errors(Err))`. The `effects` clause on operations and the `@` annotation on arrow sorts express the same information — the declaration-level form and the type-level form are consistent.

When an operation name is used as a value, its arrow sort includes the declared effects:

```anthill
operation write(key: String, value: String) -> Bool
  effects (Modifies(Store))

-- 'write' as a value has sort:
-- (String, String) -> Bool @ Modifies(Store)
```

## Effect Subtyping

A function with fewer effects can be used where more effects are permitted:

> `(A) -> B @ E1` is a subtype of `(A) -> B @ E2` when `E1 ⊆ E2`.

In particular, a pure function `(A) -> B` (empty effect set) is a subtype of any effectful arrow. This means:

- Pure functions can be passed wherever effectful functions are expected.
- A `map` expecting `(A) -> B` (pure) rejects effectful functions — the caller must ensure purity.
- A `flatMap` expecting `(A) -> F{T = B}` accepts pure continuations — the effects are inside `F`, not on the arrow.

```anthill
operation map(fa: F{T = A}, f: (A) -> B) -> F{T = B}
-- f must be pure — no effects allowed

operation flatMap(fa: F{T = A}, f: (A) -> F{T = B}) -> F{T = B}
-- f is pure but returns an effectful computation F{T = B}
-- the effects are inside F, not on the arrow
```

## Composition Typing Rule

Sequential composition of effectful functions yields effect union:

> If `f : (A) -> B @ E1` and `g : (B) -> C @ E2`, then `g . f : (A) -> C @ (E1 ∪ E2)`.

The composed function may perform any effect that either component may perform.

## Effect Polymorphism

An abstract effect set allows writing code generic over effects:

```anthill
sort E = ?                                        -- abstract effect set

operation sequence(
  fa: () -> A @ E,
  f: (A) -> (() -> B @ E)
) -> () -> B @ E
```

This is equivalent to the monadic `flatMap` for the built-in effect monad. The abstract `E` plays the role of the abstract monad `F` — but at the effect level rather than the type-constructor level.

**Effect constraints** express requirements on the effect set:

```anthill
sort E = ?
constraint has_errors: includes(E, Errors(Err))

operation try_or_default(
  fa: () -> A @ E,
  default: A
) -> () -> A @ E
```

The exact mechanism for effect constraints (sort constraints, effect subsorting, or a dedicated `includes` predicate) is left open for further design.

## Connection to the Monadic Interpretation

The state-passing and monadic interpretations of effectful operations are isomorphic. With effectful arrow sorts, this becomes a type-level equivalence:

```
() -> A @ (Modifies(S), Errors(Err), Emits(Ev))
≡
M_E(A)
≡
Env -> (A × Env × Ev list) + Err
```

An effectful thunk IS a monadic value. The effect annotation IS the monad.

**This equivalence is a theorem, not a design constraint.** Both styles remain available as complementary tools:

- **Monadic style** (abstract `F`): for arbitrary monads (List, Parser, etc.) that don't correspond to built-in effects.
- **Effect style** (`@` annotations): for the built-in effect kinds (`Modifies`, `Reads`, `Emits`, `Errors`, `Requires`) where the kernel provides semantic guarantees.

## Higher-Order Unification

Arrow sorts make the term language higher-order. Standard first-order unification is no longer sufficient — full higher-order unification is undecidable in general.

The kernel restricts to the **Miller pattern fragment**: in rules, function-sorted variables may only be applied to **distinct bound variables**. This fragment has decidable unification and is used by Isabelle, λProlog, and Twelf.

```anthill
-- Miller pattern (decidable):
rule flatMap(pure(?x), ?f) = ?f(?x)          -- OK: ?f applied to distinct variable ?x

-- Non-pattern (rejected at declaration time):
rule foo(?f) = ?f(bar(?x))                   -- rejected: ?f applied to compound term bar(?x)
```

The kernel checks this restriction when a rule is declared and rejects rules outside the pattern fragment.

## Examples

### Functor

```anthill
sort Functor
  sort F
    sort T = ?
  end
  sort A = ?
  sort B = ?

  operation map(fa: F{T = A}, f: (A) -> B) -> F{T = B}

  -- Laws
  rule identity:    map(?fa, lambda x -> x) = ?fa
  rule composition: map(map(?fa, ?f), ?g) = map(?fa, lambda x -> ?g(?f(?x)))
end
```

### CpsMonad

The full monad specification (cf. `dotty-cps-async`'s `CpsMonad[F[_]]`):

```anthill
sort CpsMonad
  sort F
    sort T = ?
  end
  sort A = ?
  sort B = ?
  sort C = ?

  operation pure(a: A) -> F{T = A}
  operation map(fa: F{T = A}, f: (A) -> B) -> F{T = B}
  operation flatMap(fa: F{T = A}, f: (A) -> F{T = B}) -> F{T = B}

  -- Derived
  operation flatten(ffa: F{T = F{T = A}}) -> F{T = A}
  rule flatten(?ffa) = flatMap(?ffa, lambda x -> x)

  -- Kleisli composition
  operation bind-then(f: (A) -> F{T = B}, g: (B) -> F{T = C})
    -> (A) -> F{T = C}
  rule bind-then(?f, ?g)(?x) = flatMap(?f(?x), ?g)

  -- Laws
  rule left_id:  flatMap(pure(?x), ?f) = ?f(?x)
  rule right_id: flatMap(?m, pure) = ?m
  rule assoc:    flatMap(flatMap(?m, ?f), ?g) = flatMap(?m, bind-then(?f, ?g))
end
```

### CpsTryMonad

Error-handling extension (cf. `dotty-cps-async`'s `CpsTryMonad[F[_]]`):

```anthill
sort CpsTryMonad
  import CpsMonad
  sort Err = ?

  operation error(e: Err) -> F{T = A}
  operation flatMapTry(fa: F{T = A}, f: (Try{T = A}) -> F{T = B}) -> F{T = B}
  operation restore(fa: F{T = A}, handler: (Err) -> F{T = A}) -> F{T = A}

  -- Laws
  rule error_left:    flatMap(error(?e), ?f) = error(?e)
  rule restore_error: restore(error(?e), ?h) = ?h(?e)
  rule restore_pure:  restore(pure(?x), ?h) = pure(?x)
end
```

### Option Monad Instance

```anthill
sort OptionMonad
  import CpsMonad where { F = Option }

  rule pure(?x) = some(?x)
  rule map(none, ?f) = none
  rule map(some(?x), ?f) = some(?f(?x))
  rule flatMap(none, ?f) = none
  rule flatMap(some(?x), ?f) = ?f(?x)
end
```

### The CpsMonad Hierarchy as Effects

The dotty-cps-async monad hierarchy maps to effect capabilities:

| dotty-cps-async | Effect requirement |
|---|---|
| `CpsMonad[F]` | No constraint on E (pure sequencing) |
| `CpsTryMonad[F]` | E includes `Errors(Err)` |
| `CpsEffectMonad[F]` | E includes `Modifies(...)` (delayed evaluation) |
| `CpsAsyncMonad[F]` | E includes async capability |

Both approaches are valid. The choice depends on whether the monad corresponds to built-in effects (use effect annotations) or is an arbitrary algebraic structure (use abstract `F`).

## Summary of Grammar Changes

```
-- Arrow sort (new Type form):
Type ::= ...
       | '(' TypeList ')' '->' Type
       | '(' TypeList ')' '->' Type '@' Type

TypeList ::= (Type (',' Type)*)?

-- Term-headed application (new Term form):
Term ::= ...
       | Term '(' [Term (',' Term)*] ')'
```

The arrow type grammar mirrors the existing Pratt operator table:
- `a -> b` in terms → `arrow(a, b)` — binary arrow
- `a -> b @ c` in terms → `arrow_effect(a, b, c)` — ternary with effect
- `(A) -> B` in types → pure arrow sort
- `(A) -> B @ E` in types → effectful arrow sort

## Semantic Rules

1. `(A1, ..., An) -> R` is a sort when all `Ai` and `R` are sorts.
2. `(A) -> B` is equivalent to `Function{A, B}` from stdlib.
3. Arrow sorts associate to the right: `(A) -> (B) -> C` = `(A) -> ((B) -> C)`.
4. An operation name in term position, where an arrow sort is expected, denotes the operation as a function value (eta-expansion).
5. Rules with function-sorted variables are restricted to the Miller pattern fragment. The kernel rejects non-pattern rules at declaration time.
6. Term application `t(args)` where `t` is a term of arrow sort type-checks when args match the parameter sorts.
7. Effect subtyping: `E1 ⊆ E2` implies `(A) -> B @ E1 <: (A) -> B @ E2`.
8. Pure arrows are subtypes of effectful arrows: `(A) -> B <: (A) -> B @ E` for any `E`.
9. Composition typing: effects compose via union.
10. An operation's `effects` clause is consistent with its arrow sort's `@` annotation.

## Backwards Compatibility

All existing syntax remains valid:

- `Fn(name, args)` term form — unchanged, is a special case of term application where the head is a name.
- `Function{A, B}` — unchanged, is the desugared form of `(A) -> B`.
- Operation declarations — unchanged. An operation `op(x: A) -> B` now also implicitly has the arrow sort `(A) -> B`.
- `effects (...)` on operations — unchanged. The declaration-level `effects` clause and the type-level `@` annotation express the same information.
- `->` and `@` in the Pratt table — unchanged. The same tokens work in both term and type position.
- Rules with only first-order variables — unchanged, trivially satisfy the Miller pattern restriction.

No existing valid program is invalidated by this change.
