## Attributes

- id: WI-20261023-6Q43W-in-a-query-pattern-a-nullary
- created: 2026-10-23T17:13:14Z

- status: Open
- status_agent: claude
- status_at: 2026-10-23T17:13:14Z

- acceptance: cargo-test

- tags: resolver

## Description

In a query pattern a nullary operation's call is the operation's NAME as data, so a comparison over it is decided wrongly. MEASURED 2026-10-23 (38a260a6): over `operation seven() -> Int64 = 7`, the query `?v <=> seven()` binds `?v = seven` (the name), `seven() = 7` answers NO SOLUTIONS — a refutation of a true equation — and `not(seven() = 8)` holds only by the same reading; in a rule body `rule n(?v) :- ?v <=> seven()` answers 7. The non-nullary call is read as the call in a query (`?r <=> stampOr(1)` reaches the bridge). The nullary canon makes `f()` and `f` one term (WI-20260902-CZJ2N); a query's value slot reads that term as the name. ACCEPTANCE: `?v <=> seven()` answers 7 and `seven() = 7` holds in a query, as in a rule body; an effectful nullary call in a query is declined (WI-20261013-R1W5A), `?r <=> plainStamp()` with `Clock`.

