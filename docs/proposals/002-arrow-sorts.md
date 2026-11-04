# Proposal 002: Arrow Sorts (with Effect Annotations)

**Canonical reference:** [`kernel-language.md` §§4.4 and 5.2](../kernel-language.md#52-sort),
including the delivered higher-kinded sort-binder extensions.

**Status:** Draft. Corrected 2026-11-03: every arrow is a `Function` (§"Correction (2026-11-03)"); kernel-language §4.4 not yet changed.
**Depends on:** [001-sort-domain-unification](001-sort-domain-unification.md)
**Subsumes:** [003-effect-arrow-sorts](003-effect-arrow-sorts.md)
**Affects:** Kernel Language Specification §4, §5.2, §5.4, §5.5–5.7, §8.2, §11

## Motivation

Operations like `map` and `flatMap` take function arguments. In the current kernel, all operation parameters must be sort-typed — there are no function sorts. This forces **defunctionalization**: introducing auxiliary sorts and explicit `apply` operations for every function-passing pattern.

The stdlib already provides `Function[A, B]` with an `apply` operation — this works but obscures intent:

```anthill
-- Without arrow sorts (defunctionalized, current):
operation flatMap(fa: F[T = A], k: Function[A = A, B = F[T = B]]) -> F[T = B]

-- With arrow sorts (direct):
operation flatMap(fa: F[T = A], f: (A) -> F[T = B]) -> F[T = B]
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
(Int64) -> String                         -- unary function
(A) -> B                                -- polymorphic function
(A, B) -> C                             -- binary function
() -> A                                 -- thunk (nullary)
(A) -> F[T = B]                         -- Kleisli arrow
((A) -> B) -> (A) -> B                  -- higher-order function
(A) -> B @ Modifies(S)                  -- stateful function
(A) -> B @ Errors(Err)                  -- fallible function
(A) -> B @ (Modifies(S), Errors(Err))   -- stateful + fallible
() -> A @ Emits(Event)                  -- thunk that emits events
(A) -> B @ Reads(Config)               -- function that reads config
```

Arrow sorts associate to the right: `(A) -> (B) -> C` is `(A) -> ((B) -> C)`.

A pure arrow `(A) -> B` has an empty effect set. It is a subtype of any effectful arrow.

### Relationship to `Function[A, B]`

The arrow sort `(A) -> B` is sugar for `Function[A, B]` from stdlib. The existing `apply(f, x)` operation works on arrow-sorted values. The type checker treats them as equivalent:

```anthill
-- These are the same sort:
(Int64) -> String
Function[A = Int64, B = String]
```

### Correction (2026-11-03): every arrow is a `Function`

The rule above says what `(A) -> B` is and nothing about `(A, B) -> C`. The implementation
answered with a parameter count carried beside the parameter type (WI-791): `(a: A, b: B) -> C`
is a function of two parameters, `((a: A, b: B)) -> C` a function of one tuple, and the two are
different types (kernel-language §4.4). The stdlib has no sort for the first. Its one function
sort is `Function[A, B, E]`, whose `apply(f, x: A)` takes one argument. This section corrects the
rule: a function takes one argument, and several parameters are one tuple.

**The rule.**

1. `(p₁: T₁, …, pₙ: Tₙ) -> R @ E` is `Function[A = (p₁: T₁, …, pₙ: Tₙ), B = R, E = E]` for
   n ≠ 1, `(p: T) -> R` is `Function[A = T, B = R]`, and `() -> R` is `Function[A = (), B = R]`.
   An arrow carries no parameter count, so `((a: A, b: B)) -> R` and `(a: A, b: B) -> R` are one
   type.
2. Two matches relate tuples, and they are different. The *tuple match* relates a value of one
   tuple type to an expected tuple type, by name, with width and permutation (kernel-language
   §4.5); it is unchanged. The *application match* relates the arguments of an application to
   its target tuple, the tuple of the function applied: a positional argument meets the target's
   component at its position, and a named argument the component with its label, as a call's
   arguments meet an operation's parameters.
3. An application keeps its written form, `f(x₁, …, xₙ)`, and `f((x₁, …, xₙ))` is the same
   application: the one tuple is the argument list. It is checked by the application match
   against `A`. At load it is converted to the tupled form, the conversion a call through a
   `Function`-typed value already gets (§4.4: a spread call "is normalized at load into its
   whole-`A` form").
4. What a callable does with the one tuple is its own. A lambda hands it to its pattern. An
   operation of several parameters takes them from its components, the spread a call through a
   `Function`-typed value already gets.
5. How many parameters a callable has is a fact about the callable, not about its type. An
   operation of k parameters, or a lambda of k binders, stands where `Function[A, B]` is
   expected when k is 1 or `A`'s component count — the rule a `Function` slot applies today
   (WI-801). It is checked where the callable becomes a value.
6. A callable stands where a function type is expected when the expected `A` reaches the
   callable's own tuple by the application match: the slot will apply it. When the two tuples
   carry the same labels, the components meet by label. Otherwise the labels are mapped by
   position, the first component to the first. A lambda's tuple is its pattern's, so
   `lambda (a: Int64, b: Int64)` has `(Int64, Int64)`, with no labels. An operation's tuple is
   its parameters, so `two(a: Int64, b: Int64)` has `(a: Int64, b: Int64)`. The run time makes
   the same match when the callable takes the tuple.

**What it does to programs.** Each program is measured on `89500f50`.

A lambda of several typed binders, with no type around it (WI-20261103-2N4QH):

```anthill
namespace q3
  import anthill.prelude.{Int64}
  operation main() -> Int64 =
    let h = lambda (s: Int64, b: Int64) -> s + b
    h("a", 1)
end
```

Today it loads and stops at run time, "type mismatch: expected Int64, got String and Int64":
the lambda's parameter is a fresh variable, so nothing checks the call. Under rule 1 `h` is
`Function[A = (…: Int64, …: Int64), B = Int64]`, and the call is refused at load, at `"a"`, as
`h(("a", 1))` is. `h(1, 2)` and `h((1, 2))` run to 3.

The same type written by hand:

```anthill
namespace q6
  import anthill.prelude.{Int64}
  operation main() -> Int64 =
    let h: (Int64, Int64) -> Int64 = lambda (s, b) -> s + b
    h(1, 2) + h((1, 2))
end
```

Today it is refused at `h((1, 2))`: "type mismatch in h.arity (op-arg): expected 2 arguments —
the parameter list this function value declares, got 1 argument". Under rule 3 the one tuple is
checked against `A = (Int64, Int64)`, and the program runs to 6.

Today's `Function` slot already takes both shapes of operation, at either spelling of the call:

```anthill
namespace fa
  import anthill.prelude.{Int64, Function}
  operation get_a(t: (a: Int64, b: Int64)) -> Int64 = t.a
  operation two(a: Int64, b: Int64) -> Int64 = a * 10 + b
  operation main() -> Int64 =
    let f: Function[A = (a: Int64, b: Int64), B = Int64] = get_a
    let g: Function[A = (a: Int64, b: Int64), B = Int64] = two
    f(1, 2)
end
```

With `main` ending in each call in turn: `f(1, 2)` runs to 1, `f((a: 1, b: 2))` to 1, `g(1, 2)`
to 12 and `g((a: 1, b: 2))` to 12. Under the rule every arrow behaves so.

**What it retires from kernel-language §4.4.** "An arrow records its parameter ARITY" (WI-791),
and the two relations the count selects — at a count other than 1 the parameter list, related
slot by slot; at 1 the sole parameter's type, related as data. "The argument count must equal
the declared arity" in "Applying a function value checks its arguments" (WI-792): rule 3 takes
its place. The note "The equivalence is not exact in one remaining respect: `Function` states no
arity", which becomes exact. And the `arity` field of `TypeExtractor.Arrow`.

**A callable where a function type is expected (rule 6).** Today a `Function` slot whose `A`
is written positionally takes a two-parameter operation and refuses one that takes a named tuple:

```anthill
namespace fd
  import anthill.prelude.{Int64, Function}
  operation get_a(t: (a: Int64, b: Int64)) -> Int64 = t.a
  operation two(a: Int64, b: Int64) -> Int64 = a * 10 + b
  operation take2(f: Function[A = (Int64, Int64), B = Int64]) -> Int64 = f(1, 2)
  operation main() -> Int64 = take2(two)
end
```

`take2(two)` runs to 12. `take2(get_a)` is refused: "expected Function[A = (_1: Int64, _2:
Int64), B = Int64, E = {}], got ((a: Int64, b: Int64)) -> Int64". Under rule 6 both stand there:
`(Int64, Int64)` reaches `(a: Int64, b: Int64)` by position, and `take2(get_a)` runs to 1.

A lambda whose binders are named otherwise than the slot's components still stands there. This
runs to 6, today and under the rule:

```anthill
namespace q8
  import anthill.prelude.{Int64, List}
  operation main() -> Int64 =
    let f = lambda (a: Int64, b: Int64) -> a + b
    List.foldLeft([1, 2, 3], 0, f)
end
```

`foldLeft`'s `f` is `(acc: Acc, x: Element) -> Acc`, and `foldLeft` applies it as `f(acc, x)`:
two positional arguments. The lambda's tuple, `(Int64, Int64)`, has no labels, so `acc` maps
to `a` and `x` to `b` by position. By the tuple match the two would not meet; that match is not
the one used here.

Parameters named in another order meet by label. This runs to 1 today, and to 7 under the rule:

```anthill
namespace fc2
  import anthill.prelude.{Int64, Function}
  operation take(f: Function[A = (x: Int64, y: Int64), B = Int64]) -> Int64 = f(7, 1)
  operation impl(y: Int64, x: Int64) -> Int64 = x
  operation main() -> Int64 = take(impl)
end
```

`take`'s `(x: Int64, y: Int64)` and `impl`'s `(y: Int64, x: Int64)` carry the same labels, so
`take`'s `x` meets `impl`'s `x`. `f(7, 1)` gives `x = 7`, and `impl` returns 7. Today the values
reach `impl` by position, `y = 7` and `x = 1`. With `y: Bool` the program is refused today. Under
the rule it loads and returns 7, the `Int64` reaching `impl`'s `Int64` parameter. Before WI-782
its arrow-slot twin loaded and returned a `Bool` from an operation declared `-> Int64`: the type
check read the parameters by name and the run time by position.

A named argument through a function value meets the value's type by label, and so reaches the
callable the same way. This runs to 1 today, and to 7 under the rule:

```anthill
namespace fe2
  import anthill.prelude.{Int64}
  operation take(f: (x: Int64, y: Int64) -> Int64) -> Int64 = f(x: 7, y: 1)
  operation impl(y: Int64, x: Int64) -> Int64 = x
  operation main() -> Int64 = take(impl)
end
```

With `f` written `Function[A = (x: Int64, y: Int64), B = Int64]` the named call is refused today,
"the type of this function value records no parameter names to bind a label to". Under rule 1
the two spellings are one type, and both load.

Tuples that do not carry the same labels are mapped by position. Each of these runs to the
value shown, today and under the rule:

```anthill
namespace fg1
  import anthill.prelude.{Int64, List}
  operation add2(a: Int64, b: Int64) -> Int64 = a + b
  operation main() -> Int64 = List.foldLeft([1, 2, 3], 0, add2)
end
```

6: `foldLeft`'s `(acc: Acc, x: Element)` shares no label with `(a: Int64, b: Int64)`, so `acc`
maps to `a` and `x` to `b`.

```anthill
namespace fh1
  import anthill.prelude.{Int64}
  operation take(f: (x: Int64, y: Int64) -> Int64) -> Int64 = f(7, 1)
  operation impl(z: Int64, x: Int64) -> Int64 = x
  operation main() -> Int64 = take(impl)
end
```

1: `(x: Int64, y: Int64)` and `(z: Int64, x: Int64)` share `x` but do not carry the same labels,
so `x` maps to `z` and `y` to `x`.

**A call of an operation by its name takes one tuple too.** Rule 3 reaches it: `add2((1, 2))`
is `add2(1, 2)`, and a named tuple meets the parameters by label, as the arguments written
separately would. The reason is a generic operation that hands a value on:

```anthill
namespace fw
  import anthill.prelude.{Int64}
  operation forward[A, B](a: A, g: (A) -> B) -> B = g(a)
  operation add2(a: Int64, b: Int64) -> Int64 = a * 10 + b
  operation get_a(t: (a: Int64, b: Int64)) -> Int64 = t.a
  operation main() -> Int64 = forward((a: 1, b: 2), add2)
end
```

Today it is refused: "type mismatch in forward.g (op-arg): expected a 1-parameter function
((a: Int64, b: Int64)) -> Int64, got a 2-parameter function (_1: Int64, _2: Int64) -> Int64".
`forward((a: 1, b: 2), get_a)` runs to 1. Under the rule both stand: `A` is `(a: Int64, b:
Int64)`, `add2`'s tuple carries the same labels, and `forward((a: 1, b: 2), add2)` runs to 12.
The direct call `add2((a: 1, b: 2))`, refused today ("expected 2 arguments — the parameter list
`fw.add2` declares, got 1 argument"), runs to 12 as well, as `g(a)` does inside `forward`.

One tuple is always the argument list, also where it is a value of the first parameter. Today
this runs to 112:

```anthill
namespace fr1
  import anthill.prelude.{Int64}
  operation r(t: (Int64, Int64), n: Int64 = 100) -> Int64 = t._1 * 10 + t._2 + n
  operation main() -> Int64 = r((1, 2))
end
```

`(1, 2)` is `t`, and `n` takes its default. Under the rule `(1, 2)` is the argument list, `t = 1`
and `n = 2`, and the call is refused at `t`. The repair names the parameter, `r(t: (1, 2))`,
which loads today and under the rule. One reading for every call: a generic first parameter,
`v[T](t: T, n: Int64 = 0)` called as `v((1, 2))`, is `T = Int64` and `n = 2`.

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
operation pure(a: A) -> F[T = A]

-- 'pure' in term position has sort (A) -> F[T = A]:
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
- A `flatMap` expecting `(A) -> F[T = B]` accepts pure continuations — the effects are inside `F`, not on the arrow.

```anthill
operation map(fa: F[T = A], f: (A) -> B) -> F[T = B]
-- f must be pure — no effects allowed

operation flatMap(fa: F[T = A], f: (A) -> F[T = B]) -> F[T = B]
-- f is pure but returns an effectful computation F[T = B]
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
sort Functor[F[T]]
  operation map[A, B](fa: F[T = A], f: (A) -> B) -> F[T = B]

  -- Laws
  rule identity:    map(?fa, lambda x -> x) = ?fa
  rule composition: map(map(?fa, ?f), ?g) = map(?fa, lambda x -> ?g(?f(?x)))
end
```

### CpsMonad

The full monad specification (cf. `dotty-cps-async`'s `CpsMonad[F[_]]`):

> **Model decided (2026-06-11), DELIVERED (2026-06-14)** — see
> `docs/design/path-dependent-types.md` §5.4. The type constructor is written in the
> MARKED enclosing-list form `sort CpsMonad[F[T]]` (WI-451), which gives `F` a backing
> var to fill (WI-452); the element types `A` / `B` / `C` are **per-operation** type
> params (`operation map[A, B](…)`), not part of the monad's identity. The
> instantiation semantics is **fill-as-requirement-discharge** (filling `F` checks/adds
> the licensing bound's requirement — concrete fill resolves it by SLD, abstract fill
> forwards it as a dict, WI-453), applications decompose **injectively** (dual to the
> non-injective projections of §5.3), licensing is **implicit** (the
> `requires CpsMonad[F]`-style bound licenses the applications; the `Applied`-clause
> form is the lowering, not the surface), and instances are retroactive **provision
> facts with op-valued bindings** (`fact CpsMonad[F = Option, pure = optionPure, …]`).
> Build: WI-383 (mechanism) + WI-451/452/453 (the marked carrier + fill) + WI-431
> (instance facts). The earlier unmarked body form (`sort CpsMonad … sort F … end`)
> still parses but loads `F` as a rigid nominal sort (never filled — a *concrete*
> structured sort, e.g. `Modify`); the marker is what distinguishes a fillable
> parameter from a concrete nested sort.

```anthill
sort CpsMonad[F[T]]
  operation pure[A](a: A) -> F[T = A]
  operation map[A, B](fa: F[T = A], f: (A) -> B) -> F[T = B]
  operation flatMap[A, B](fa: F[T = A], f: (A) -> F[T = B]) -> F[T = B]

  -- Derived
  operation flatten[A](ffa: F[T = F[T = A]]) -> F[T = A]
  rule flatten(?ffa) = flatMap(?ffa, lambda x -> x)

  -- Kleisli composition
  operation bind-then[A, B, C](f: (A) -> F[T = B], g: (B) -> F[T = C])
    -> (A) -> F[T = C]
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
  import CpsMonad          -- inherits the marked carrier F[T]
  sort Err = ?

  operation error[A](e: Err) -> F[T = A]
  operation flatMapTry[A, B](fa: F[T = A], f: (Try[T = A]) -> F[T = B]) -> F[T = B]
  operation restore[A](fa: F[T = A], handler: (Err) -> F[T = A]) -> F[T = A]

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
2. `(A) -> B` is equivalent to `Function[A, B]` from stdlib, and `(A1, ..., An) -> R` to `Function[A = (A1, ..., An), B = R]`: an arrow carries no parameter count (§"Correction (2026-11-03)").
3. Arrow sorts associate to the right: `(A) -> (B) -> C` = `(A) -> ((B) -> C)`.
4. An operation name in term position, where an arrow sort is expected, denotes the operation as a function value (eta-expansion).
5. Rules with function-sorted variables are restricted to the Miller pattern fragment. The kernel rejects non-pattern rules at declaration time.
6. Term application `t(args)` where `t` is a term of arrow sort type-checks when its arguments meet `A` by the application match — positional arguments by position, named ones by label — `t((x, y))` being the same application as `t(x, y)`; at load it is converted to the tupled form (§"Correction (2026-11-03)").
7. Effect subtyping: `E1 ⊆ E2` implies `(A) -> B @ E1 <: (A) -> B @ E2`.
8. Pure arrows are subtypes of effectful arrows: `(A) -> B <: (A) -> B @ E` for any `E`.
9. Composition typing: effects compose via union.
10. An operation's `effects` clause is consistent with its arrow sort's `@` annotation.

## Backwards Compatibility

All existing syntax remains valid:

- `Fn(name, args)` term form — unchanged, is a special case of term application where the head is a name.
- `Function[A, B]` — unchanged, is the desugared form of `(A) -> B`.
- Operation declarations — unchanged. An operation `op(x: A) -> B` now also implicitly has the arrow sort `(A) -> B`.
- `effects (...)` on operations — unchanged. The declaration-level `effects` clause and the type-level `@` annotation express the same information.
- `->` and `@` in the Pratt table — unchanged. The same tokens work in both term and type position.
- Rules with only first-order variables — unchanged, trivially satisfy the Miller pattern restriction.

No existing valid program is invalidated by this change.
