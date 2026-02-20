# Proposal 002: Arrow Sorts

**Status:** Draft
**Depends on:** [001-sort-domain-unification](001-sort-domain-unification.md)
**Affects:** Kernel Language Specification §4, §5.2, §5.4, §8.2, §11

## Motivation

Operations like `map` and `flatMap` take function arguments (`A => B`, `A => F[B]`). In the current kernel, all operation parameters must be sort-typed — there are no function sorts. This forces **defunctionalization**: introducing auxiliary sorts (`Morphism`, `KleisliArrow`) and explicit `apply` operations for every function-passing pattern.

Defunctionalization works but obscures intent:

```
-- Without arrow sorts (defunctionalized):
sort KleisliArrow
operation apply_k(k: KleisliArrow, a: A) -> F{T = B}
operation flatMap(fa: F{T = A}, k: KleisliArrow) -> F{T = B}

-- With arrow sorts (direct):
operation flatMap(fa: F{T = A}, f: (A) => F{T = B}) -> F{T = B}
```

## Arrow Sort Syntax

If `A1, ..., An` are sorts and `R` is a sort, then `(A1, ..., An) => R` is also a sort — the sort of functions from `A1, ..., An` to `R`.

### Grammar

```
Type ::= ...
       | '(' TypeList ')' '=>' Type                    -- arrow sort

TypeList ::= (Type (',' Type)*)?                       -- zero or more parameter types
```

### Examples

```
(Int) => String                         -- unary function
(A) => B                                -- polymorphic function
(A, B) => C                             -- binary function
() => A                                 -- thunk (nullary)
(A) => F{T = B}                         -- Kleisli arrow (with Proposal 001)
((A) => B) => (A) => B                  -- higher-order function
```

Arrow sorts associate to the right: `(A) => (B) => C` is `(A) => ((B) => C)`.

## Term Application

To apply a function-sorted value, the term grammar gains term-headed application:

### Grammar

```
Term ::= ...
       | Term '(' [Term (',' Term)*] ')'      -- application
```

This generalizes the existing `Fn(name, args)` form. When the head is a variable of arrow sort, the application invokes the function:

```
?f(?x)                                  -- apply function variable ?f to argument ?x
?f(?x, ?y)                              -- binary application
pure(?x)                                -- existing named application (unchanged)
bind-then(?f, ?g)(?x)                   -- chained: apply result of bind-then
```

Existing named function application `name(args)` is unchanged — it is a special case where the head is a name rather than an arbitrary term.

## Operation Names as Values

An operation name, used in a term position where an arrow sort is expected, denotes the operation as a function value:

```
operation pure(a: A) -> F{T = A}

-- 'pure' in term position has sort (A) => F{T = A}:
rule right_id: flatMap(?m, pure) = ?m
```

This is analogous to eta-expansion: the name `pure` stands for the function `?x => pure(?x)`.

**Disambiguation rule:** In a term `name(args)`, `name` is resolved as:
1. A named function application (existing `Fn` semantics), if `name` is a known operation/constructor name and `args` are provided.
2. A function value (eta-expanded), if `name` appears without arguments in a position expecting an arrow sort.

This is unambiguous: `pure(?x)` is application; `pure` alone (without parens) is a value.

## Higher-Order Unification

Arrow sorts make the term language higher-order. Standard first-order unification (§8.2) is no longer sufficient — full higher-order unification is undecidable in general.

The kernel restricts to the **Miller pattern fragment**: in rules, function-sorted variables may only be applied to **distinct bound variables**. This fragment has decidable unification and is used by Isabelle, λProlog, and Twelf.

```
-- Miller pattern (decidable):
rule flatMap(pure(?x), ?f) = ?f(?x)          -- OK: ?f applied to distinct variable ?x

-- Non-pattern (rejected at declaration time):
rule foo(?f) = ?f(bar(?x))                   -- rejected: ?f applied to compound term bar(?x)
```

The kernel checks this restriction when a rule is declared and rejects rules outside the pattern fragment.

## Examples

### Functor

```
sort Functor
  sort F
    sort T
  end
  sort A
  sort B

  operation map(fa: F{T = A}, f: (A) => B) -> F{T = B}

  -- Laws
  rule identity:    map(?fa, ?x => ?x) = ?fa
  rule composition: map(map(?fa, ?f), ?g) = map(?fa, ?x => ?g(?f(?x)))
end
```

### CpsMonad

The full monad specification (cf. `dotty-cps-async`'s `CpsMonad[F[_]]`):

```
sort CpsMonad
  sort F
    sort T
  end
  sort A
  sort B
  sort C

  operation pure(a: A) -> F{T = A}
  operation map(fa: F{T = A}, f: (A) => B) -> F{T = B}
  operation flatMap(fa: F{T = A}, f: (A) => F{T = B}) -> F{T = B}

  -- Derived
  operation flatten(ffa: F{T = F{T = A}}) -> F{T = A}
  rule flatten(?ffa) = flatMap(?ffa, ?x => ?x)

  -- Kleisli composition
  operation bind-then(f: (A) => F{T = B}, g: (B) => F{T = C})
    -> (A) => F{T = C}
  rule bind-then(?f, ?g)(?x) = flatMap(?f(?x), ?g)

  -- Laws
  rule left_id:  flatMap(pure(?x), ?f) = ?f(?x)
  rule right_id: flatMap(?m, pure) = ?m
  rule assoc:    flatMap(flatMap(?m, ?f), ?g) = flatMap(?m, bind-then(?f, ?g))
end
```

### CpsTryMonad

Error-handling extension (cf. `dotty-cps-async`'s `CpsTryMonad[F[_]]`):

```
sort CpsTryMonad
  extends CpsMonad
  sort Err

  operation error(e: Err) -> F{T = A}
  operation flatMapTry(fa: F{T = A}, f: (Try{T = A}) => F{T = B}) -> F{T = B}
  operation restore(fa: F{T = A}, handler: (Err) => F{T = A}) -> F{T = A}

  -- Laws
  rule error_left:    flatMap(error(?e), ?f) = error(?e)
  rule restore_error: restore(error(?e), ?h) = ?h(?e)
  rule restore_pure:  restore(pure(?x), ?h) = pure(?x)
end
```

### Option Monad Instance

```
sort OptionMonad
  import CpsMonad where { F = Option }

  rule pure(?x) = some(?x)
  rule map(none, ?f) = none
  rule map(some(?x), ?f) = some(?f(?x))
  rule flatMap(none, ?f) = none
  rule flatMap(some(?x), ?f) = ?f(?x)
end
```

## Summary of Grammar Changes

```
-- Arrow sort (new Type form):
Type ::= ...
       | '(' TypeList ')' '=>' Type

TypeList ::= (Type (',' Type)*)?

-- Term-headed application (new Term form):
Term ::= ...
       | Term '(' [Term (',' Term)*] ')'
```

## Semantic Rules

1. `(A1, ..., An) => R` is a sort when all `Ai` and `R` are sorts.
2. Arrow sorts associate to the right: `(A) => (B) => C` = `(A) => ((B) => C)`.
3. An operation name in term position, where an arrow sort is expected, denotes the operation as a function value (eta-expansion).
4. Rules with function-sorted variables are restricted to the Miller pattern fragment. The kernel rejects non-pattern rules at declaration time.
5. Term application `t(args)` where `t` is a term of arrow sort `(A1,...,An) => R` type-checks when `args` match `A1,...,An` and the result has sort `R`.

## Backwards Compatibility

All existing syntax remains valid:

- `Fn(name, args)` term form — unchanged, is a special case of term application where the head is a name.
- Operation declarations — unchanged. An operation `op(x: A) -> B` now also implicitly has the arrow sort `(A) => B`.
- Rules with only first-order variables — unchanged, trivially satisfy the Miller pattern restriction.

No existing valid program is invalidated by this change.
