## Attributes

- id: WI-20261102-ATVC1-rule-rule-implicit-arguments-a
- created: 2026-11-02T11:19:37Z

- status: Open
- status_agent: claude
- status_at: 2026-11-02T11:19:37Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing, proposal-068

## Description

RULE → RULE IMPLICIT ARGUMENTS: A GOAL OF ANOTHER RULE RECEIVES ITS CALLER'S REQUIREMENT, AND A SORT'S BRACKET ON A RULE-BODY GOAL IS READ — step S7 of WI-20260911-5G28A and its decision B row, split out (user, 2026-11-02) so that the proposal-068 umbrellas WI-20260926-DSEXA and WI-20260926-7D48J wait on this and not on the whole of 5G28A.

WHY SPLIT. DSEXA and 7D48J were wired to 5G28A on 2026-10-14 for S7 alone (5G28A's note of that day). 5G28A itself waits on WI-20260925-SHED7 and holds other open parts, so the two umbrellas waited on all of them. S7 needs the clause typing of 7D48J's parts, and those are delivered (GGXCX, WF14Z, R1W5A, RYDNV). 5G28A's 2026-10-21 row on a bound filled at the caller's own type parameter (from 0RRQP) stays there.

THE STEP (docs/design/060-implementation.md §7.3, row S7; op-to-rule-requirement-channel.md §7 step 2): every goal carries its implicit arguments through the seven goal-list constructions, written by the typer at the body edge. Today a rule goal passes its callee nothing (060-implementation §8.9 row C6).

MEASURED (5G28A, 2026-10-14, with GFS6A's fixes in the tree): over `sort Descending provides WeakOrd[T = Int64]` with `compare = sub(b, a)`, `rule cmp(?a, ?b, ?c) :- WeakOrd.compare(?a, ?b, ?c)` and `rule outer(?a, ?b, ?c) :- cmp(?a, ?b, ?c)`, an operation holding `requires WeakOrd[T = A]` that cites `cmp` answers 4 under `viaCmp[A = Int64, WeakOrd = Descending](1, 5)`, and the same through `outer` (`viaOuter[…] = outer(x, y).head.c`) answers -1, Int64's own: `outer` has no condition of its own, so the citation has nothing to fill, and `cmp`, reached as a goal of another rule, derives its dictionary from the value. A middle rule cannot state the requirement either: `require[WeakOrd]` there is refused, 'expected a body call to one of WeakOrd's operations … got no such call'. With an INFERRED condition (2026-10-08, from P7VP4): `wi_p7vp4_rule_body_requirements_test::a_rule_goal_passes_its_callee_no_dictionary` answers 4 / -4 cited directly and -1 / -1 through a second rule; with S7 it reads (4, -4, -1).

THE PATTERN EVIDENCE (5G28A, 2026-10-15; read with `TypePattern` for the retired `ErrorTag` since 2026-10-23, WI-20261016-YM8HD): a rule body whose `Error.reify` is typed at a rule variable's type has no evidence of its own; its caller has it. Rows: `either(boom("b"), 7, ?r)` and `gOpen(boom("x"), 3, ?r)` decline `Other` (a fault naming the raise, no answer) and their `0 - 1` / `0 - 3` twins answer `err(boom(…))`; the same through a second rule (`rule outer(?p, ?n, ?r) :- either(?p, ?n, ?r)`), and from an operation holding `requires TypePattern[T = P]` that cites the rule. Proposal 071 §7 open question 5 would let such a rule write its pattern instead.

DECISION B'S ROW (user, 2026-10-21): a sort's bracket on a rule-body goal has been refused at load since 2827691a (`Loader::refuse_rule_goal_receiver`, kb/load.rs; kernel-language §5.4's 'read or refused' paragraph). Lifting it is this ticket's: over `sort Wrap[T] { rule el(?x: T) :- src(?x) }`, `fact src(1)`, `fact src("a")`, the goal `Wrap[T = Int64].el(?x)` answers `1` alone and the refusal goes (rows in rule_goal_sort_bracket_refused_test; wi_5g28a_paren_less_citation_test's `…_is_refused` rows turn back into goals that answer). The other spellings measured there — the alias `WI.el(?x)` over `sort WI = Wrap[T = Int64]`, and `SortDomain[T = Colour].fill(?x)` — say what each answers.

MECHANISM, as recorded and not re-decided here: decision C (5G28A, 2026-09-12 07:18, with the user) — the type rides beside the goal, out of band, resolved from the frame at evaluation. It replaced decision B's hidden head slot, whose in-band arity change broke the spec-op dispatch bridge (the 07:14 note, §1). That note's §8 states the choice left: transitivity through a rule with no bound of its own — row (g), `rule again(?y) :- dom(?y)` inside `Wrap`, cited as `Wrap[T = Colour].again` — is the channel INHERITED by the body's goals, a dynamically scoped type environment keyed by (sort, parameter), as `Frame::child_context()` is for requires, with an inner goal's own bracket shadowing it.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven, each back-out named at its row): the WeakOrd rows through `outer` answer 4, and the P7VP4 row reads (4, -4, -1); the pattern-evidence rows; decision B's rows with the refusal removed; row (g); controls — the direct citations' answers unchanged; kernel-language §5.4 and 060-implementation §7.3 brought in line; full workspace green.

