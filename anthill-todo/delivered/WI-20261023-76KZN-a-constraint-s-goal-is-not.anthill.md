## Attributes

- id: WI-20261023-76KZN-a-constraint-s-goal-is-not
- created: 2026-10-23T11:57:59Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-23T20:13:04Z

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

## Changes

### 2026-10-23T17:13:26Z — feedback — claude

ROW ADDED (from WI-20261013-R1W5A, 2026-10-23, measured on 38a260a6): a constraint's goal is not held to the rule-body effect refusal either. Over `operation plainStamp() -> String effects {Clock} = now()`, `constraint noStamp :- plainStamp() = "2000"` loads, where the same goal in a rule body is refused at load ("the call `plainStamp`, which performs `Clock`, and a rule body performs no effect", `kb/typing/rule_dispatch.rs` `refuse_performed_effects`); a function handed to a relation in a constraint goal is not checked (`refuse_handed_functions`). Walking a constraint's goals with the rule-body readings, as TO DO says, reaches both. ACCEPTANCE ADDS: `noStamp` refused naming the call and `Clock`; a constraint goal handing `lambda () -> now()` to a relation refused.

### 2026-10-23T20:13:03Z — feedback — claude

DELIVERED (user decisions 2026-10-23). A constraint's goals (invariant, guard, a quantifier's condition and body) are stored as a clause with the head ⊥, kind Constraint, origin Derived, built as a rule body's atoms are (Loader::assert_constraint_goal_clause), so every rule-body pass reaches them: the goal readings, the clause typing (effect and handed-function refusals, op-arg checks — WI-20260902-65QKB's three rows now refuse), and 'names nothing'. Nothing resolves ⊥; the guard still evaluates the LogicalQuery; spec_laws still counts the constraint once. A constraint whose text the load refuses is not checked by the post-load guard (refused_constraint_guards, §8.4). The unlabeled spelling 'constraint NAME :- G' reads NAME as the invariant goal: anthill-todo's three domain constraints and five test fixtures rewritten to 'constraint NAME: false :- G' (inert, as before). The typed binder 'forall (?x: T) -: body' is removed from the grammar, converter and §6.2: its TypeOf condition named nothing and its guard matched nothing. §6.2 and §8.4 updated. Rows: wi_76kzn_constraint_goal_reading_test (back-outs at its head). Gate 10609/0; scaland testFull 748/0.

