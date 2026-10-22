## Attributes

- id: WI-20261008-R653S-a-paren-less-dot-on-a-sort
- created: 2026-10-08T09:06:18Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-22T15:54:41Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-055

## Description

A PAREN-LESS DOT ON A SORT-DENOTING RECEIVER CALLS, WHERE THE WRITTEN SPELLING IS REFUSED — `let t = Box; t.zero` answers 0, while `Box.zero` and `Box[V = Int64].zero` in an operation body are refused ("without parentheses is a RULE citation, and `zero` is an operation — call it `Box[…].zero()`"). Measured 2026-10-08 on fd1cf282.

WHY. WI-20260824-PAPX0's rule: a receiver that denotes a sort takes a dot as the written `Sort[…].m(…)` call does. The spellings disagree here because `Expr::DotApply` does not record whether the member was applied. `t.zero` (the loader's `try_identifier_dot_field`) and `t.zero()` (`dot_call_receiver_chain`) build the same node, so `denoted_sort_dot` (kb/typing/type_receiver.rs) cannot tell them apart. `(Box).zero` goes the same way.

WHAT. Decide with the user which reading stands: the written one (a paren-less member is a rule citation; an operation is refused) or the value dot's (`x.m` is `x.m()`), which is what a sort-denoting receiver gets today. If the written one: carry the paren-less fact to the typer's dot frame and answer as the written spelling does, a rule member included (`t.rows` is refused today as "declared in `Box` and is neither").

CONTROL. One fixture per row. An operation, a rule and a constructor member, each written, let-bound and parenthesized. Say at the test site which rows fail with the change backed out.

DONE WHEN: the three spellings give one verdict for a paren-less member; the gate is green.

## Changes

### 2026-10-22T15:54:33Z — feedback — user

USER DECISION 2026-10-22, AND DELIVERED (4dbd73db). Asked whether `Box.zero` in an operation body is the call of `zero` or refused, the user answered: 'in Box.zero V is inferred -- so it should be the same as written V' — the call `Box[V = Int64].zero` makes, V inferred where nothing binds it. Built: Box.zero, Box[V = Int64].zero, (Box).zero and let t = Box; t.zero all call zero (5 in the rows); Box.empty takes V from its use and Box[V = Int64].empty / CA.empty bind it; a namespace path (ns.Box.zero), the sort's own body (Cnt.six inside Cnt) and a const value call too; a chain past a nullary operation reads its value (Box.origin.x, Box.origin.sum()); an internal one is refused as Box.secret() is. A rule member through a receiver that denotes the sort is the relation the written spelling cites: t.rows, (Box).rows, t.rows(1), (Box).rows(1) in an operation body, (Box).rows(?x) as a rule-body goal, a bracket or an alias on it refused there as Box[V = Int64].rows(?x) is. Found while probing and fixed with it: in a rule body ?x <=> CA.zero through sort CA = Box[V = Int64] bound the term field_access(CA, zero), and 5 = CA.zero was refused as a walk's defect, where CA.zero() and (CA).zero answered 5. NOT BUILT: a member that takes arguments is the call with none, an arity error, also where a function is expected (Box.inc into (x: Int64) -> Int64), in all four spellings; the one-segment inc lifts. Rows: wi_r653s_paren_less_dot_test (11), back-outs measured per piece at its header. Full Rust gate 36 suites, 10371 passed, 0 failed; families unchanged; scaland testFull 710 + 47 passed.

### 2026-10-22T16:27:40Z — feedback — user

FOLLOW-UP DELIVERED (ef496f2c), user's go 2026-10-22 ('let fix both now'). The two items this ticket's note left: (1) a member that takes arguments, written without parentheses on a sort — Box.inc, Box[V = Int64].wrap, CA.wrap, (Box).inc, t.inc — is now its function value where one is expected, the bracket or alias binding the sort's parameters in its type, and is refused as its one-segment name is elsewhere; Box.inc() stays the arity error. (2) A one-segment name of a parametric sort's member (empty, wrap imported) fixes the sort's parameters where it stands: let b: Box[V = Int64] = empty and let f: (x: Int64) -> Int64 = wrap load, where they were refused 'got Box[V = V]' / 'got V -> V'. Spec §5.4 updated. Rows added to wi_r653s_paren_less_dot_test with back-outs E1–E7. Full Rust gate 36 suites, 10374 passed, 0 failed; families unchanged.

