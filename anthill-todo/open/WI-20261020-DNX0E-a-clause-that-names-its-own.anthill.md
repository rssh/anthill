## Attributes

- id: WI-20261020-DNX0E-a-clause-that-names-its-own
- created: 2026-10-20T07:56:45Z

- status: Open
- status_agent: user
- status_at: 2026-10-20T07:56:45Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A CLAUSE THAT NAMES ITS OWN SORT AT ITS OWN PARAMETER READS AS THAT SORT WITH THE PARAMETER LEFT OUT. The loader stores a slot a clause leaves unwritten as the required sort's own parameter (`Mark[T = Mark.T]`), which is the term a clause written inside `Mark` as `Mark[T = T]` makes, and the encoding differs by clause kind. MEASURED on 663ac457, the same on 098ce8a9. (a) `sort Tag { sort T = ?  operation tag() -> Int64 }`, `sort Mark { sort T = ?  operation mark() -> Int64  provides Tag[T = T] :- Mark[T = T] where operation tag() -> Int64 = 5 end }`, `Boom provides Mark[T = Boom]` and `operation tagAt[P](n: Int64) -> Int64 requires Tag[T = P] = Tag.tag[T = P]()`: `tagAt[P = Int64](0)` loads and answers 5 although `Mark[T = Int64]` holds nowhere — the condition read as `Mark` at any type. The same condition written on another sort (`sort MarkTag { sort T = ?  provides Tag[T = T] :- Mark[T = T] where … }`) is refused, "a provision answers it, but `Mark[T = Int64]` beneath it does not hold". (b) The provision-contract check: `sort Shows { sort T = ?  requires Named[T = T]  operation show(x: T) -> String }` and `sort Named { sort T = ?  operation name(x: T) -> String  provides Shows[T = T] :- Named[T = Foo] where … }` load clean, the contract `Named[T = Named.T]` read as open and covered by the condition `Named[T = Foo]`; with the contract on another spec (`Shows requires Other[T = T]`) the load is refused, "nothing provides `Other[T = Named.T]`". (c) A provision condition that leaves a slot unwritten: `sort Wrap { sort T = ?  provides Shows[T = T] :- Pairish[A = T] where operation show(x: T) -> String = Pairish.pa(x) end }`, with `Pairish` over `A` and `B` and `Dog provides Pairish[A = Dog, B = Int64]`, answers nothing — `Shows.show(dog())` is refused, "unresolved: Pairish[A = Dog]" — while the same requirement written at sort level (`requires Pairish[A = T]`) answers "dog-pa". THE READERS: the loader's per-clause-kind encoding of a slot left unwritten (load.rs), `is_open_requires_slot` (provision.rs), `supply_covers_demanded_keys` (dep_projection.rs). FIX DIRECTION: one representation of a slot left unwritten that no written parameter can make, read the same in every clause kind — left out of the term, as an inferred open slot is. ACCEPTANCE: (a) refused as its twin is; (b) refused as its twin is; (c) "dog-pa" as its sort-level twin answers; back-outs measured; full gate green.

