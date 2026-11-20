## Attributes

- id: WI-20261120-CP3KV-a-const-applied-as-a-function
- created: 2026-11-20T22:33:32Z

- status: Open
- status_agent: user
- status_at: 2026-11-20T22:33:32Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A CONST APPLIED AS A FUNCTION IS A TERM IN A CLAUSE (found writing WI-20261120-FTP2S; filed with the user 2026-11-20). Over const f: (x: Int64) -> Int64 = lambda (x: Int64) -> x + 1, rule viaF(?r) :- ?r <=> f(1) loads and answers ?r = f(1), the application kept as data with the const as its functor; the query ?r <=> f(1) answers the same. In an operation body f(1) applies the closure (2). Measured on e2fce05e with the debug CLI. To decide with the user first: a const applied in a clause evaluated as an operation body would (a const of an arrow type called), or refused at load naming the const, as a const in a data slot with a computed body is. ACCEPTANCE: each row driven to its value; the part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

