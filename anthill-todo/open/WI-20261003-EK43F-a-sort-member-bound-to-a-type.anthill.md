## Attributes

- id: WI-20261003-EK43F-a-sort-member-bound-to-a-type
- created: 2026-10-03T09:16:26Z

- status: Open
- status_agent: user
- status_at: 2026-10-03T09:16:26Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A SORT MEMBER BOUND TO A TYPE WITH OPEN SLOTS IS UNINHABITABLE: `sort P = Pair[?, ?]` (or `Pair[?A, ?B]`) loads clean, leaves the enclosing sort with no parameters, and refuses every value. `sort Pair { sort A = ?; sort B = ?; entity pair(a: A, b: B) }`, `sort Holder { sort P = Pair[?, ?]; entity holder(p: P) }`: `holder(p: pair(a: 1, b: "s"))` is refused 'holder.p (entity-field): expected P, got Pair[A = Int64, B = String]' (the same message for `holder(p: 5)`), and `Holder[P = Pair[A = Int64, B = String]]` is refused 'Holder … declares no type parameters'; written `Pair[?A, ?B]`, `Holder[A = Int64, B = String]` is refused the same way. MECHANISM: resolve_alias_shape (typing/sort_alias.rs:789) resolves an alias only to a GROUND shape — 'a PARAMETRIC alias (`sort PairKey = Pair[?X1, ?X2]`) with open `?` leaves … stays opaque' pending 'WI-374's per-call scheme machinery' — so P is an opaque name nothing inhabits; and the loader declares no parameter for a named `?A` inside a member binding. USER DECISION (2026-10-03): an ANONYMOUS `?` in such a binding is a FRESH slot per occurrence — `P` is any pair, as a bare `Pair` is (the 2026-10-01 bare-sort decision) — and a NAMED `?A` declares `A` a parameter of the enclosing sort, as the per-statement binder `sort ?A` does (kernel-language.md: the enclosing-list and per-statement forms 'declare the same non-rigid sort type parameters'), so `P` is `Pair[A = A, B = B]` at the instance and `Holder[A = Int64, B = String]` binds them. MEASURED identically on the trees before and after WI-20260929-0RP29's ninth and tenth passes; FOUND in the tenth pass's discussion of parameter defaults. FIX: (1) the typer reads an alias whose target leaves anonymous slots open with those slots fresh at each read (resolve_alias_shape and its readers, which take the shape as one shared term today); (2) the loader declares each named `?X` in a sort member's binding a parameter of the enclosing sort; (3) kernel-language.md §8.1's alias paragraph states both. ACCEPTANCE: `holder(p: pair(a: 1, b: "s"))` loads and runs; two `P`-typed parameters of one operation take pairs of different element types; with `Pair[?A, ?B]`, `Holder[A = Int64, B = String]` loads, a holder of `pair(a: 1, b: "s")` passes for it and one of `pair(a: "x", b: 1)` is refused; scaland mirrors it; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-10-03T09:18:13Z — feedback — user

USE (user, 2026-10-03): a pure function type gets its name through this ticket's named-slot rule applied to an ALIAS's own parameters — `sort PureFunction = Function[?A, ?B, {}]`, used as `PureFunction[A = Int64, B = Int64]` (or positionally), is `Function[Int64, Int64, {}]`, which already refuses a raising callback at the call (MEASURED). `Function[A, B]` with E unwritten stays effect-polymorphic (kernel-language.md §4.4 as corrected 2026-10-03). Add to the acceptance: PureFunction admits `inc` and refuses `boom` as `Function[Int64, Int64, {}]` does.

