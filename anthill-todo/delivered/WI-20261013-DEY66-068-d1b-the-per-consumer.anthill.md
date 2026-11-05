## Attributes

- id: WI-20261013-DEY66-068-d1b-the-per-consumer
- created: 2026-10-13T08:03:37Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-05T17:15:57Z

- acceptance: cargo-test

- depends_on: WI-20261013-RYDNV-068-c1d-one-classification-per

- tags: proposal-068

## Description

068 D1b — THE PER-CONSUMER REDUCTIONS RETIRE (068 §8 step 3; item 2 of WI-20260926-DSEXA): `reduce_op_value`'s call-by-name fold, `body_specialize`'s reducer and `unify_values`' evaluate-on-reach become WI-20260926-K4JGC's walker. Goal arguments are evaluated before the head match, so `unify_match_values` stays structural. AFTER C1d: the walker reads the fragments C1c types and the classification C1d fixes. ROWS: narrowing goes through a `match` on a tuple of the arguments — over `operation firstof(xs: List[T = Int64], d: Int64) -> Int64 = match (xs, d) case (cons(h, t), _) -> h case (nil, dd) -> dd`, `rule value(?r) :- firstof(?xs, 9) = 9, ?r <=> ?xs` answers the two definite rows its `match xs` spelling does (DSEXA note 2026-10-11, 3HN0N); a query pattern evaluates a nullary call — over `operation seven() -> Int64 = 7`, `?x <=> ns.seven()` answers 7 and `?x <=> ns.inc(ns.seven())` 8, and a dot in a query is dispatched (note 2026-10-11, A3FY2; 068 §6). ACCEPTANCE (cargo-test, driven): no consumer reduces an operand by its own path — the retired functions are gone, not bypassed; the rows above, each back-out at its site. CONTROLS: P7VP4's and SHED7's rows unchanged; classic-mini unchanged.

## Changes

### 2026-11-05T17:15:55Z — feedback — claude

DELIVERED (ab6d7288; 068-implementation.md §6.23, kernel-language §8.3's query paragraph). reduce_op_value's call-by-name fold is gone: every call the walker evaluates runs whole in the interpreter (unify_values had stopped evaluating with K4JGC). Decided with the user 2026-11-05: body_specialize::reduce STAYS the narrowing's one step — its alternatives need each arm's residual as code (append(?a, [3]) = [1, 3] unifies cons(?h, append(?t, [3])) with [1, 3] before asking the inner call, which is what terminates), and a strict run returns nothing of a value it waits inside; so the acceptance's 'the retired functions are gone' covers the fold. ROWS: the match on a tuple (3HN0N) — split_tuple_scrutinee narrows the one flexible component an arm tests, firstof(?xs, 9) = 9 answers the two rows its match xs twin does; the query's nullary call (A3FY2) answered already (control); a dot in a query — decided with the user: typed where the pattern is converted, by the typer's own dot dispatch ((S).seven() 7, box(v: 4).peek() 4, mk().peek() 3; each was the data dot_apply(…) bound definitely), a dot on a query variable refused with the qualified-call repair. Found and fixed: a tuple pattern read an operation body's TupleLiteral node as a definite non-match (the prover got pick(x, y) = 20 for match (x, y) case (0, _) -> 10 case _ -> 20). Delivered with it: WI-20261102-989Z0 (the fold's nested bridge) and WI-20261102-6GAS1 (a dispatch to a third sort's member, which the fold had covered for). LEFT, decided with the user: a rule-body dot on an untyped head variable still answers its text as data — its own ticket (lf1 + smt-gen). FOUND by /code-review, not changed: a dispatch through a RUN-TIME dictionary landing on a third sort's member (gen[A](x: A) requires Desc[T = A] = Desc.describe(x) at gen(leaf())) dies Internal, the same on HEAD. Rows: wi_dey66_per_consumer_reductions_test (17). Controls: P7VP4's and SHED7's rows and classic-mini unchanged. Full workspace 11,714 passed; families green on both carriers; scaland testFull 851 passed.

