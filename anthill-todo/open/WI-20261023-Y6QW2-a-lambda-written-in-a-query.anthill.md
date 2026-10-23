## Attributes

- id: WI-20261023-Y6QW2-a-lambda-written-in-a-query
- created: 2026-10-23T17:13:13Z

- status: Open
- status_agent: claude
- status_at: 2026-10-23T17:13:13Z

- acceptance: cargo-test

- tags: resolver

## Description

A lambda written in a query pattern, and an operation's name passed as data and applied as a function at run time, are no function values: the call raises "unknown operation". MEASURED 2026-10-23 (38a260a6): over `operation applyThunk[Rho](f: () -> String @ {Rho}) -> String effects {Rho} = f()`, the query `applyThunk(lambda () -> "x", ?r)` answers one conditional answer with the fault "`applyThunk` could not be evaluated by the resolver: unknown operation: applyThunk.f" (the lambda is the reflect term `lambda_expr(pattern_tuple, …)`); and over `operation applyAt[Rho](f: (n: Int64) -> String @ {Rho}, n: Int64) -> String effects {Rho} = f(n)`, `operation pureAt(n: Int64) -> String = "p"`, `rule apply3(?p, ?a, ?b, ?r) :- ?p(?a, ?b, ?r)`, `rule viaOpRef(?r) :- apply3(applyAt, pureAt, 1, ?r)` faults the same way. ACCEPTANCE: the query answers "x" and `viaOpRef(?r)` "p", definite; an effectful lambda in a query is declined as a rule body's is (WI-20261013-R1W5A's run-time decline).

