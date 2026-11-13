## Attributes

- id: WI-20261113-C2BS8-a-combinator-over-a-relation
- created: 2026-11-13T06:50:45Z

- status: Open
- status_agent: claude
- status_at: 2026-11-13T06:50:45Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A COMBINATOR OVER A RELATION WHOSE ROW IS LEFT OPEN IS REFUSED FOR AN UNDECLARED EFFECT, WHERE takeN ALONE LOADS. Over `sort People { entity person(name: String, age: Int64) }`, three `person` facts, `rule person_row(?name, ?age) :- person(name: ?name, age: ?age)` and `const people: Relation[T = (name: String, age: Int64)] = person_row`: `operation three() -> Int64 effects Error = length(people.takeN(3))` loads and answers 3, but `operation olds() -> Int64 effects Error = length(people.filter(lambda r -> r.age > 26).map(lambda r -> r.age).takeN(5))` is refused at load, "type mismatch in olds.effects (op-effects): expected declared: [Error], got undeclared effect: ?E" — and so are `people.map(ageOf).takeN(5)` and `people.filter(isOld).takeN(5)` over named operations, and `people.map(lambda r -> r.age).takeN(5)`. MEASURED on 590f4272 and on WI-20261105-P0QGF part 1 (3999aab9), identical. Written `const rows: Relation[T = (name: String, age: Int64), E = {Error}] = person_row`, the same chain answers 2 (since P0QGF; on 590f4272 it died at run time, "__req_iterable not bound" in FilteredStream.splitFirst). Found writing P0QGF's acceptance rows; not P0QGF's. Relation declares `sort E = ?`, threaded abstractly (stdlib relation.anthill), so an unwritten `E` is an open slot: either the combinator's row is read through it as takeN's `effects s.E` is, and the chain loads, or takeN alone is refused too. ACCEPTANCE: the two spellings agree, driven to their values (olds() answering 2 with E unwritten, or both refused naming E); full workspace green via rustland/scripts/test.sh.

