## Attributes

- id: WI-20261008-R653S-a-paren-less-dot-on-a-sort
- created: 2026-10-08T09:06:18Z

- status: Open
- status_agent: claude
- status_at: 2026-10-08T09:06:18Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-055

## Description

A PAREN-LESS DOT ON A SORT-DENOTING RECEIVER CALLS, WHERE THE WRITTEN SPELLING IS REFUSED — `let t = Box; t.zero` answers 0, while `Box.zero` and `Box[V = Int64].zero` in an operation body are refused ("without parentheses is a RULE citation, and `zero` is an operation — call it `Box[…].zero()`"). Measured 2026-10-08 on fd1cf282.

WHY. WI-20260824-PAPX0's rule: a receiver that denotes a sort takes a dot as the written `Sort[…].m(…)` call does. The spellings disagree here because `Expr::DotApply` does not record whether the member was applied. `t.zero` (the loader's `try_identifier_dot_field`) and `t.zero()` (`dot_call_receiver_chain`) build the same node, so `denoted_sort_dot` (kb/typing/type_receiver.rs) cannot tell them apart. `(Box).zero` goes the same way.

WHAT. Decide with the user which reading stands: the written one (a paren-less member is a rule citation; an operation is refused) or the value dot's (`x.m` is `x.m()`), which is what a sort-denoting receiver gets today. If the written one: carry the paren-less fact to the typer's dot frame and answer as the written spelling does, a rule member included (`t.rows` is refused today as "declared in `Box` and is neither").

CONTROL. One fixture per row. An operation, a rule and a constructor member, each written, let-bound and parenthesized. Say at the test site which rows fail with the change backed out.

DONE WHEN: the three spellings give one verdict for a paren-less member; the gate is green.

