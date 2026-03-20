# 012: Sort-Defined Syntax Sugar

## Status: Brainstorming

## Depends on: 011 (Type Resolution)

## Blocks: 010 (Query System) — query syntax may be an instance of sort-defined sugar

## Motivation

The query system proposal (010) raised the question: should query syntax (`?-`, comprehensions, `choose`/`guard`) be hardcoded in the grammar or defined by sorts? This generalizes to a broader question: can sorts declare what syntactic forms they support?

If sorts can define their own syntax sugar, then:
- `Stream` gets comprehension syntax by having `flatMap`/`guard`/`pure`
- `List` gets literal syntax `[a, b, c]` by having `cons`/`nil`
- `Query` gets `?-` syntax by being a query sort
- User-defined sorts can opt into the same mechanisms
- The grammar stays fixed; new syntax forms emerge from sort declarations

This is analogous to Scala's `for`-comprehension (works for any `Monad`), Haskell's `do`-notation (works for any `Monad`), or Rust's `for` loop (works for any `IntoIterator`).

## Core Idea

A sort doesn't define arbitrary syntax. Instead, the kernel defines a fixed set of **syntax forms** (comprehension, builder, for-each, direct-style branching, operators). A sort **opts into** a syntax form by satisfying the required interface (having the right operations). The desugaring rules are fixed per form; only the target operations vary per sort.

```
-- The kernel defines: comprehension syntax [result | generators]
-- requires: pure, flatMap, guard
-- A sort that has these operations gets comprehensions:

sort Stream {
  operation pure(x: ?T) -> Stream[T = ?T]
  operation flatMap(s: Stream[T = ?A], f: ?A -> Stream[T = ?B]) -> Stream[T = ?B]
  operation guard(cond: Bool) -> Stream[T = Unit]
  -- ^ these three unlock: [?x | ?x <- stream, guard(cond)]
}
```

## Open Questions

### OQ1. Activation Mechanism

How does a sort declare it supports a syntax form?

**OQ1.1. Implicit (structural).** If the sort has the right operations with the right signatures, sugar is automatically available. Like Scala's for-comprehension.

Pro: zero ceremony, works retroactively (add operations later, get syntax).
Con: magic — not obvious which operations unlock which syntax. Name collisions.

**OQ1.2. Explicit fact assertion.** The sort asserts a fact declaring support:

```
sort Stream {
  ...
  fact Comprehension[T = Stream]    -- "I support comprehension syntax"
}
```

The kernel checks that the required operations exist when the fact is asserted.

Pro: explicit, queryable, no magic.
Con: boilerplate — asserting the fact AND having the operations.

**OQ1.3. Spec sort satisfaction.** Define spec sorts for each syntax form:

```
-- In stdlib:
sort Comprehension {
  sort T = ?
  operation pure(x: ?A) -> T[?A]          -- abstract signature
  operation flatMap(s: T[?A], f: ...) -> T[?B]
  operation guard(cond: Bool) -> T[Unit]
}

-- A sort satisfies it:
fact Comprehension[T = Stream]
-- Kernel verifies Stream has the required operations
```

Pro: reuses the existing spec-sort mechanism. Consistent with `Eq`, `Ordered`, etc.
Con: needs proper spec-sort checking (which depends on 011 type resolution).

### OQ2. Fixed Syntax Forms

What syntax forms does the kernel provide?

**OQ2.1. Comprehension / monad syntax.**

```
[?result | ?x <- expr1, guard(cond), ?y <- expr2]
```

Desugars to nested `flatMap` + `guard` + `pure`. Available to sorts satisfying `Monad`-like interface.

Questions:
- Is `<-` the binding operator, or something else?
- Can generators include pattern matching? `[?x | cons(?x, ?xs) <- lists]`
- Is this separate from the list literal syntax `[a, b, c]`?

**OQ2.2. Builder syntax.**

```
List { 1, 2, 3 }
-- or:
Set { "a", "b", "c" }
```

Desugars to `append(append(append(empty, 1), 2), 3)` or similar. Available to sorts with `empty`/`append` (or `cons`/`nil` for lists).

**OQ2.3. Direct-style branching (choose/guard/fail).**

```
operation find_pairs() -> Stream[T = Pair]
  effects (Branches(result))
{
  ?x = choose(xs)
  ?y = choose(ys)
  guard(compatible(?x, ?y))
  pair(?x, ?y)
}
```

This is the `Branches` effect from proposal 010 OQ13.9. Is it a syntax form that sorts opt into, or a general effect mechanism?

**OQ2.4. For-each / iteration.**

```
for ?item in collection {
  process(?item)
}
```

Desugars to `msplit`-based iteration or a `forEach` operation. Available to sorts with an iteration protocol.

**OQ2.5. Pipe / chaining.**

```
stream |> filter(gt(?, 0)) |> map(double) |> collect
```

Desugars to nested function application. Available universally or only to sorts declaring support?

**OQ2.6. Operator syntax.**

```
a + b        -- desugars to add(a, b)
a == b       -- desugars to eq(a, b)
a > b        -- desugars to gt(a, b)
```

Available to sorts with the corresponding named operations. This already partially exists in the grammar (infix operators).

### OQ3. Desugaring Rules

**OQ3.1.** Are desugaring rules fixed per form (hardcoded in the compiler), or can sorts customize them?

- Fixed: simpler, predictable. The kernel defines exactly how `[?x | generators]` maps to `flatMap`/`guard`/`pure`.
- Customizable: more power, but opens the door to confusing custom semantics.

**OQ3.2.** How are desugaring rules expressed? If customizable:

```
-- Hypothetical: sort declares its own desugaring
sort Stream {
  desugar [?result | ?x <- ?expr] =
    flatMap(?expr, \?x -> pure(?result))
  desugar [?result | ?x <- ?expr, ?rest...] =
    flatMap(?expr, \?x -> [?result | ?rest...])
  desugar [?result | guard(?cond), ?rest...] =
    flatMap(guard(?cond), \_ -> [?result | ?rest...])
}
```

This is essentially a term-rewriting system. Powerful but complex.

**OQ3.3.** Can desugaring be recursive? E.g., comprehension with multiple generators desugars to nested `flatMap`, where each step re-applies the comprehension rule.

### OQ4. Type Resolution Dependency

**OQ4.1.** Desugaring needs to know the sort of an expression to determine which sugar applies. This requires type resolution (proposal 011).

Example: `[?x | ?x <- expr]` — to desugar, we need to know the sort of `expr` to find the correct `flatMap`.

**OQ4.2.** Can desugaring be deferred until after type resolution? Pipeline options:

```
-- Option A: desugar during parsing (needs type info early)
parse → desugar+resolve → load

-- Option B: desugar during loading (type info available from sort declarations)
parse → scan sorts → desugar → load facts/rules

-- Option C: desugar post-load (full KB available)
parse → scan → load → desugar → resolve
```

**OQ4.3.** Can some sugar be desugared without type info? E.g., list literals `[1, 2, 3]` always desugar to `cons(1, cons(2, cons(3, nil)))` regardless of sort. Only sort-polymorphic sugar (comprehensions) needs type info.

### OQ5. Scoping and Import

**OQ5.1.** Is syntax sugar **scoped**? If I import `Stream`, do I automatically get comprehension syntax? Or must I explicitly import the syntax?

```
import anthill.prelude.Stream              -- gets the sort
import anthill.prelude.Stream.syntax       -- also gets comprehension syntax?
```

**OQ5.2.** Can multiple sorts provide the same syntax form in the same scope? E.g., both `List` and `Stream` support comprehensions. If `[?x | ?x <- expr]` appears, which sort's `flatMap` is used? (Answer: determined by the type of `expr` — back to type resolution.)

**OQ5.3.** Can syntax sugar be **disabled**? If a user doesn't want comprehension syntax (prefers explicit `flatMap`), can they opt out?

### OQ6. Interaction with Effects

**OQ6.1.** The `Branches` effect (010 OQ13.9) enables direct-style logic programming: `choose`, `guard`, `fail` in sequential code. Is this a syntax form (sort-defined sugar) or an effect mechanism (general to all effects)?

If it's sort-defined sugar: `Stream` opts into "branching syntax" by having `choose`/`guard`/`fail`.
If it's an effect mechanism: any effect can have direct-style syntax via `effects (E)` declarations.

**OQ6.2.** Can sort-defined sugar introduce new effects? E.g., comprehension syntax on `Stream` implicitly adds `effects (Reads kb)` because querying the KB is effectful.

**OQ6.3.** Should effectful sugar be annotated? E.g.:

```
-- This comprehension has effects:
[?x | ?x <- query account(?, ?, ?)]  -- implicitly effects (Reads kb)

-- Should the sugar make this explicit?
[?x | ?x <- query account(?, ?, ?)] effects (Reads kb)
```

### OQ7. Extensibility and User-Defined Sugar

**OQ7.1.** Can users define **new syntax forms** beyond the kernel-provided ones? Or is the set of forms fixed (comprehension, builder, for-each, pipe, operators)?

Fixed set: simpler, predictable, every Anthill programmer knows the forms.
Extensible: more power, but risks fragmentation (every library defines its own syntax).

**OQ7.2.** If extensible, what's the mechanism? Term-rewriting macros? Syntax declarations in sort bodies? Something else?

**OQ7.3.** How does this interact with tree-sitter? The grammar is fixed at parse time. Sort-defined sugar operates on the parsed AST, not on raw syntax. So "new syntax" means "new interpretation of existing syntax forms," not "new grammar rules."

## Possible Design Sketch

1. The kernel defines a **fixed set of syntax forms**: comprehension, builder, for-each, operator, pipe.
2. Each form has a **spec sort** with required operations (e.g., `Comprehension` requires `pure`/`flatMap`/`guard`).
3. A sort **opts in** by asserting `fact Comprehension[T = MySort]` (or it's detected structurally).
4. Desugaring happens **during loading** (after sort declarations are scanned, before facts/rules are loaded), using the sort skeleton for type resolution.
5. Desugaring rules are **fixed per form** — sorts provide the operations, not the rules.
6. The set of forms is **fixed but growable**: new forms can be added to the kernel in future versions, but user-defined forms are not supported initially.

## References

- Scala for-comprehensions: sugar for `flatMap`/`map`/`withFilter` on any type
- Haskell do-notation: sugar for `>>=`/`return` on any `Monad`
- Rust `for` loops: sugar for `IntoIterator`
- Maude mix-fix: user-defined operator syntax in OBJ-family languages
- Anthill spec sorts: `Eq`, `Ordered`, `Numeric` in stdlib
- Proposal 010 OQ13.9 (`Branches` effect), OQ15 (sort-defined syntax sugar)
- Proposal 011 (Type Resolution) — prerequisite for sort-aware desugaring
