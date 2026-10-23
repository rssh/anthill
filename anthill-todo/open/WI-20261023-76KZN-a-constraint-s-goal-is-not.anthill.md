## Attributes

- id: WI-20261023-76KZN-a-constraint-s-goal-is-not
- created: 2026-10-23T11:57:59Z

- status: Open
- status_agent: claude
- status_at: 2026-10-23T11:57:59Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A constraint's goal is not held to the goal-reading refusals a rule body is: a constant, a non-Bool const and an applied const load clean there, or report the constraint violated.

MEASURED on f0d1b88a. `const nn: Int64 = 5`, `const flag: Bool = true`, `const big: Bool = Int64.gt(nn, 3)`, `entity item(n: Int64)`, `fact item(n: 1)`, one `constraint c:` per row:

  constraint body                    loads?   a rule body's `:- <goal>`
  forall ?x: item(n: ?x) -: 42       "integrity constraint 'c' is violated"   refused, ConstantInGoalPosition
  no ?x: item(n: ?x) -: 42           loads clean                              refused, ConstantInGoalPosition
  forall ?x: item(n: ?x) -: nn       "violated"                               refused, ConstInGoalPosition (not Bool)
  no ?x: item(n: ?x) -: nn           loads clean                              refused, ConstInGoalPosition (not Bool)
  no ?x: item(n: ?x) -: flag()       loads clean                              refused, UnknownApplyFunctor ("the reference is `flag`")
  forall ?x: item(n: ?x) -: big      "violated"                               refused, ConstInGoalPosition (no load-time value)

The `no` rows pass in silence. The `forall` rows give a verdict about the facts where the defect is the constraint's text. WHY: `check_rule_body_goal_readings` (kb/typing/rule_requirements.rs) walks `kb.live_rule_ids()`, which holds rule bodies and no constraint. The `Bool` const FOLD does reach a constraint goal since WI-20260822-NDG34 (`Loader::term_walk_at_goal`), so `forall ?x: item(n: ?x) -: flag` holds.

TO DO: hold every goal a constraint proves — the invariant, the guard, a quantified body and consequent — to `check_goal_atom_reading`'s reading, with the same errors and spans. Read the slots from the one slot table (`goal_slot_readings`), not from a list. Ordinary denials are inert (§6.2), but their text is still a goal and is held the same way.

ACCEPTANCE: drive each row above and assert the refusal by its variant and name. Add the controls that answer: `-: true`, `-: flag`, `-: Int64.gt(nn, 3)`, and a Bool operation `-: is_big`, each holding under `forall` and failing under `no`. Say at the file's head which tests fail when the walk is backed out.

