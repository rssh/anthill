## Attributes

- id: WI-20261013-DEY66-068-d1b-the-per-consumer
- created: 2026-10-13T08:03:37Z

- status: Open
- status_agent: claude
- status_at: 2026-10-13T08:03:37Z

- acceptance: cargo-test

- depends_on: WI-20261013-RYDNV-068-c1d-one-classification-per

- tags: proposal-068

## Description

068 D1b — THE PER-CONSUMER REDUCTIONS RETIRE (068 §8 step 3; item 2 of WI-20260926-DSEXA): `reduce_op_value`'s call-by-name fold, `body_specialize`'s reducer and `unify_values`' evaluate-on-reach become WI-20260926-K4JGC's walker. Goal arguments are evaluated before the head match, so `unify_match_values` stays structural. AFTER C1d: the walker reads the fragments C1c types and the classification C1d fixes. ROWS: narrowing goes through a `match` on a tuple of the arguments — over `operation firstof(xs: List[T = Int64], d: Int64) -> Int64 = match (xs, d) case (cons(h, t), _) -> h case (nil, dd) -> dd`, `rule value(?r) :- firstof(?xs, 9) = 9, ?r <=> ?xs` answers the two definite rows its `match xs` spelling does (DSEXA note 2026-10-11, 3HN0N); a query pattern evaluates a nullary call — over `operation seven() -> Int64 = 7`, `?x <=> ns.seven()` answers 7 and `?x <=> ns.inc(ns.seven())` 8, and a dot in a query is dispatched (note 2026-10-11, A3FY2; 068 §6). ACCEPTANCE (cargo-test, driven): no consumer reduces an operand by its own path — the retired functions are gone, not bypassed; the rows above, each back-out at its site. CONTROLS: P7VP4's and SHED7's rows unchanged; classic-mini unchanged.

