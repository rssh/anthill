## Attributes

- id: WI-20261023-Y6QW2-a-lambda-written-in-a-query
- created: 2026-10-23T17:13:13Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-30T19:34:49Z

- acceptance: cargo-test

- depends_on: WI-20261030-BXMPK-a-goal-holding-a-value-with-no

- tags: resolver

## Description

A lambda written in a query pattern, and an operation's name passed as data and applied as a function at run time, are no function values: the call raises "unknown operation". MEASURED 2026-10-23 (38a260a6): over `operation applyThunk[Rho](f: () -> String @ {Rho}) -> String effects {Rho} = f()`, the query `applyThunk(lambda () -> "x", ?r)` answers one conditional answer with the fault "`applyThunk` could not be evaluated by the resolver: unknown operation: applyThunk.f" (the lambda is the reflect term `lambda_expr(pattern_tuple, …)`); and over `operation applyAt[Rho](f: (n: Int64) -> String @ {Rho}, n: Int64) -> String effects {Rho} = f(n)`, `operation pureAt(n: Int64) -> String = "p"`, `rule apply3(?p, ?a, ?b, ?r) :- ?p(?a, ?b, ?r)`, `rule viaOpRef(?r) :- apply3(applyAt, pureAt, 1, ?r)` faults the same way. ACCEPTANCE: the query answers "x" and `viaOpRef(?r)` "p", definite; an effectful lambda in a query is declined as a rule body's is (WI-20261013-R1W5A's run-time decline).

## Changes

### 2026-10-23T17:59:19Z — feedback — claude

ALSO (2026-10-23, found delivering WI-20261015-C9802, 01424c91): A QUERY RUNS NONE OF THE LOADER'S BARE-ARROW REFUSALS. Over `operation plus1(n: Int64) -> Int64 = n + 1`, `anthill query '?f <=> lambda () -> probe.q.plus1(1)'` answers `?f = arrow(lambda, 2)` — refused in a clause since C9802 (the parentheses named) — and the keyword-less `?f <=> (x) -> probe.q.plus1(x)` answers `arrow(x, plus1(x))`, refused in a clause by WI-618. `convert_query_term` has no error channel; the CLI's `scan_query_source` does. Once a query lowers a lambda, both refusals belong at the query too, through the clause's walk (`Loader::find_arrow_witness`); before that the advised parentheses would not help there.

### 2026-10-30T15:22:44Z — feedback — claude

DEPENDS ON WI-20261030-BXMPK (2026-10-30): the query half — a lambda in a query pattern lowered to the reflect term `lambda_expr(…)` — goes through `lower_leaf` (kb/execute.rs), one of the goal sites BXMPK takes off `value_to_term`. The operation-reference half is this ticket's alone: `apply1(pureOp, 4, ?r)` in a rule body faults "unknown operation: apply1.f" in one clause as through a head (measured on c541ef90, the same on 0989f81a), and the same call from an operation body answers 5.

### 2026-10-30T16:34:42Z — feedback — claude

CORRECTION to the 2026-10-30 note (measured on cf906e65, WI-20261030-BXMPK delivered): the query half does NOT go through `lower_leaf`. `anthill query 'probe.y6.applyThunk(lambda () -> "x", ?r)'` still answers the same conditional row with the residual `applyThunk(lambda_expr(pattern_tuple, "x"), ?r)` before and after BXMPK: the CLI pattern is converted by `load::convert_query_term` to an occurrence whose lambda is already the reflect term, so the fix is in that converter (read a lambda as the clause's walk does, with the loader's bare-arrow refusals, per the 2026-10-23 note). What BXMPK did fix on the query side is an OPERATION's query: `keep(f).head.c` handed a lambda or a closure answers (wi_bxmpk_goal_value_carried_test).

### 2026-10-30T19:34:50Z — feedback — claude

Delivered in 4903165d. The operation-reference half: an operation's name a rule passes as data becomes its OpRef where it is applied (at the local-call lookup and Error.reify's thunk), read through the view on every carrier — written in the call, held by a fact, carried by a column to ?p(…), bound by <=>; what the typer attached at the name (sort dictionary, the operation's own slots, spread labels) rides along through the eta mint reduce_var uses, read in a frame that binds nothing. viaOpRef(?r) answers "p", definite. The query half: a compound expression in a query pattern (lambda, if, let, match) is lowered by the clause's walk with the query's variables lent to it; applyThunk(lambda () -> "x", ?r) answers "x", definite; an effectful lambda in a query is undecided with R1W5A's run-time decline; the query scan runs the clause's bare-arrow refusals ("in a query"); the lent walk asserts no inline description. kernel-language §5.3 and §4.8 updated (user-approved). 14 rows with a back-out ledger in wi_y6qw2_function_value_from_a_rule_test; full workspace 11,232 passed, 0 failed. Moved: a query writing the compound form a fact holds now matches nothing, as the rule-body goal did (noted on WI-20260829-8VGRW). Not here, the same on the parent: a dotted operation name in a rule-body data slot (apply2(Int64.max, …), applyP(S.are_eq, …), the latter refused with the typer's internal 'a defect in the walk' text) is not read as the operation.

