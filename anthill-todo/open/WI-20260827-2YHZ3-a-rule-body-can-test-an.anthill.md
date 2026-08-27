## Attributes

- id: WI-20260827-2YHZ3-a-rule-body-can-test-an
- created: 2026-08-27T09:30:21Z

- status: Open
- status_agent: user
- status_at: 2026-08-27T09:30:21Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A RULE BODY CAN TEST AN OPERATION'S RESULT BUT CANNOT BIND IT — so no rule can COMPUTE
anything, and the failure mode is succeed-with-unbound rather than fail.

MEASURED 2026-08-27 on the tree at WI-880, with a BODIED op and a HOST op side by side
(`operation twice(x: Int64) -> Int64 = Int64.add(x, x)`; `anthill.reflect.term_as_int`):

  form in a rule body                              bodied      host
  f(3) = 6        test against a known value       1           1
  f(3) <=> 6      unify against a known value      1           -
  f(3) <=> ?r     unify into a free variable       1, UNBOUND  1, UNBOUND
  f(3, ?r)        relational view (WI-938)         1, UNBOUND  0 solutions

So the only form that WORKS is a test against a value the rule already knows. Neither
spelling of "produce the result into a variable" binds, and the two differ from each
other only in whether a host op fails outright or succeeds vacuously.

THE DANGEROUS PART IS DOWNSTREAM FLOW, not the unbound answer itself:

  rule u2(?r) :- twice(3) <=> ?r, Int64.gt(?r, 5)     -> 1 solution, DEFINITE

`Int64.gt` on an unbound `?r` answers definitely rather than delaying, so a rule that
"computes" a value gets an unbound one that then satisfies further goals. That is the
same shape as the soundness gap WI-880 closed (a positive conclusion from a call that
never ran), one coordinate over.

WHY `<=>` DOES NOT RESCUE IT, since it is the obvious thing to reach for and WI-20260822-
F0HHB documents `=` as the non-binding one. `<=>` DOES reduce and match against a known
value (`twice(3) <=> 6` answers 1). Against a FREE variable it succeeds without binding.
Proposal 043/049's reading — unify is STRUCTURAL and never dispatches — predicts `?r`
binding to the TERM `twice(3)`; what is observed is `?_`. Which of those two it actually
is has NOT been chased and is the first thing to measure.

SCOPE / RELATION TO NEIGHBOURS. WI-20260826-VPEWK made a host op REDUCE in a rule body
and WI-880 made the reflection surface visible to that gate; both are about whether the
call runs at all. This ticket is about what happens to its RESULT, which neither touched:
the `= <known value>` row is green on both sides of both changes. WI-20260822-F0HHB (what
`=` should mean in a rule body) is the nearest neighbour and is about the same asymmetry
from the equality side.

FIRST CONSUMER, and the reason this is filed rather than noted: examples/guardians/lib/
safety.anthill's tier 1 wants `checked(?carrier, ?spec) :- SortProvidesInfo(sort_ref:
?carrier, spec: ?view), <get the base sort of ?view into ?spec>`. Every spelling of the
second goal is on the unbound side of the table above. docs/proposals/library/008-term-
view-and-operations.md §2(a) records it.

ACCEPTANCE: a rule body binds an operation's result into a free variable, in at least one
spelling, with the chosen spelling documented in kernel-language.md §5.2 beside the rows
VPEWK put there; the three currently-unbinding rows above each either bind or FAIL, and
none of them stays succeed-with-unbound; `twice(3) <=> ?r, Int64.gt(?r, 5)` no longer
answers 1 definite on an unbound `?r`; a control states which rows are green before the
change (the two `= <known value>` rows are, by design); full workspace green via
rustland/scripts/test.sh.

