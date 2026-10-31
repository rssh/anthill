## Attributes

- id: WI-20261023-6Q43W-in-a-query-pattern-a-nullary
- created: 2026-10-23T17:13:14Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-31T05:26:46Z

- acceptance: cargo-test

- tags: resolver

## Description

In a query pattern a nullary operation's call is the operation's NAME as data, so a comparison over it is decided wrongly. MEASURED 2026-10-23 (38a260a6): over `operation seven() -> Int64 = 7`, the query `?v <=> seven()` binds `?v = seven` (the name), `seven() = 7` answers NO SOLUTIONS — a refutation of a true equation — and `not(seven() = 8)` holds only by the same reading; in a rule body `rule n(?v) :- ?v <=> seven()` answers 7. The non-nullary call is read as the call in a query (`?r <=> stampOr(1)` reaches the bridge). The nullary canon makes `f()` and `f` one term (WI-20260902-CZJ2N); a query's value slot reads that term as the name. ACCEPTANCE: `?v <=> seven()` answers 7 and `seven() = 7` holds in a query, as in a rule body; an effectful nullary call in a query is declined (WI-20261013-R1W5A), `?r <=> plainStamp()` with `Clock`.

## Changes

### 2026-10-31T05:26:44Z — feedback — claude

DELIVERED (e10e60ea, 2026-10-31). The query converter builds a nullary operation's application as its call, as the rule-body walk does: `?v <=> seven()` binds 7, `seven() = 7` holds, and `?r <=> plainStamp()` and `not(plainStamp() = "x")` are undecided with the `Clock` fault (the negation held). A query has no typer, so at a parameter its callee declares a function type the bare name stays the function value (§5.4): `applyThunk(seven, ?r)` 7, `applyThunk(mkF)` 9 where it answered the closure. Moved, each now read as the rule body reads it: the query `holdsName(seven)` no longer meets `fact holdsName(seven)`; `applyThunk(seven(), ?r)` and `relHolds(seven, ?r)` were 7 and are undecided. A sort-named nullary operation in a bracket binding (`hb(Box[V = Positive])`) still meets its fact (found by /code-review). A bare dotted name in a data slot is unchanged (WI-20261017-FTV0Q decision (b), WI-20261030-4BXDW). Rows and back-out ledger in wi_6q43w_nullary_operation_name_test (12 rows); spec: one sentence in the rule-body evaluation section; full workspace 11,264 passed, families green plain and under the node carrier.

