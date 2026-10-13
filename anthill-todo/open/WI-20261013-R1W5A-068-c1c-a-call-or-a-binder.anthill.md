## Attributes

- id: WI-20261013-R1W5A-068-c1c-a-call-or-a-binder
- created: 2026-10-13T08:03:19Z

- status: Open
- status_agent: claude
- status_at: 2026-10-13T08:03:19Z

- acceptance: cargo-test

- depends_on: WI-20261013-WF14Z-068-c1b-a-rule-variable-is

- tags: proposal-068, typing

## Description

068 C1c — A CALL OR A BINDER FORM IN A RULE BODY IS TYPED AS AN OPERATION BODY IS, EQUATIONS OFF (068 §3). Part 3 of WI-20260926-7D48J. One call has one answer whatever shape the rule-body walk hands the typer. ROWS: over `sort Box { entity mk(v: Int64); operation peek(b: Box) -> Int64 = b.v; operation open(b: Box) -> Int64; rule open(?b) <=> peek(?b) @[simp] }`, the three spellings `?x <=> Box.open(Box.mk(4))`, `?x <=> Box.mk(4).open()` and the first over `sort Box[V]` agree, and `?x <=> dbl(2)` agrees with `?x <=> app(lambda (y: Int64) -> dbl(y), 2)` over `rule dbl(?n) <=> ?n + ?n @[simp]` (7D48J note 2026-10-11, 3HN0N); the lambda case as C1a decides it, on wi_3hn0n_tuple_on_rhs_test's five rows; an ordinary operation's call in a value slot is held to its parameter list — over `operation sub2(x: Int64, y: Int64) -> Int64`, `?c <=> Util.sub2(1, 5, 9)`, `Util.sub2(1, 5, bogus: 9)`, `Util.sub2(1)` and an argument of the wrong type are load errors, as the goal is since MHRN1 (note 2026-10-12); row (1) of the 2026-09-26 note (a typer `@[simp]` law whose right side calls body-less operations leaves them unpinned); `()` left by an equation in a fragment's argument (WI-20261011-7G99A, its program 5). The new load errors match C1a's count. ACCEPTANCE (cargo-test, driven): the fragments' stamps land on the stored occurrences; each row with its back-out named at its site. CONTROLS: an operation body's typing unchanged; classic-mini unchanged.

