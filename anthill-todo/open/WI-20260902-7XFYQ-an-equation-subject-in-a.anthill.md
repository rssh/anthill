## Attributes

- id: WI-20260902-7XFYQ-an-equation-subject-in-a
- created: 2026-09-02T10:47:40Z

- status: Open
- status_agent: user
- status_at: 2026-09-02T10:47:40Z

- acceptance: cargo-test, scaland-sbt-test

## Description

AN EQUATION SUBJECT IN A CONTRACT CLAUSE IS SILENT UNTIL SOMEBODY CALLS — the sibling position WI-20260902-8K4RB did not cover.

MEASURED on 8K4RB's delivered tree, three programs:

  operation guarded(n: Int64) -> Int64
    requires tauX          -- beside `rule tauX <=> 7 [simp]`
    = n

  * NEVER CALLED: `anthill load` succeeds. 2836 facts, exit 0, no diagnostic.
  * CALLED (`?r = guarded(3)`): REFUSED, but the diagnosis points at the caller —
    'expected precondition `tauX` provable at the call site, got unsatisfied
    precondition'. The precondition can never be established by ANY caller: an
    equation's clauses index under the `eq`/`unify` connective (WI-898), so `tauX`
    owns no clause. The author is sent to fix the call.
  * CONTROL, an UNDECLARED name (`requires totally_bogus_p`): refused AT LOAD with no
    call present, by `check_contract_clause_goals` (WI-20260822-59CDQ). So the pass
    exists and reaches this position; it is the QUESTION it asks that misses.

WHY 8K4RB DID NOT COVER IT, stated rather than assumed. Its refusal is raised inside
`check_goal_atom_reading` (typing.rs), the rule-body goal-READING pass, which walks
`kb.rule_body_nodes` and reaches no contract clause. `check_contract_clause_goals` asks
`undefined_query_goal_functors`, whose question is 'names nothing' and whose OTHER caller
is the CLI's explain-an-empty-result path — widening that set would make the CLI report an
equation subject as a name that does not exist, which is false. That is the one-name-two-
questions shape, so it is a seam to design and not a line to add.

AND IT IS NOT ONE MEMBER MISSING BUT THREE. The whole goal-reading family is absent at a
contract clause: `ConstantInGoalPosition` (`requires 42`) and `NonBoolOpInGoalPosition`
(`requires length(?l)`) are raised by the same pass and reach no contract clause either.
Whether the fix is to run the reading pass over contract clauses, or to give
`undefined_query_goal_functors` a per-node CLASSIFICATION its two callers read differently,
is the ticket's first question.

ACCEPTANCE: a `requires` / `ensures` clause naming an equation subject is refused AT LOAD
with no call present, naming the clause and its line:col; the same for the two sibling
members if the chosen seam covers them (say which it does not, and why). CONTROLS: the
UNDECLARED-name refusal above must keep firing with its own wording, and a legitimate
`requires` on a real predicate must keep loading AND keep gating a call — a fixture
asserting only the new refusal would pass with contract checking broken entirely.

## Changes

### 2026-09-02T10:56:05Z — feedback — user

A THIRD READER OF THE SAME SEAM, measured on 8K4RB's delivered tree: the CLI QUERY path.

  anthill query --path e1.anthill 'zz.e.tauX'      ->  'no solutions', exit 0
  anthill query --path e1.anthill 'not(zz.e.tauX)' ->  1 solution, conditional,
                                                       residual: not(field_access(...))

`main.rs`'s explain-an-empty-result path calls `undefined_query_goal_functors` for exactly
this purpose — to tell a user WHY a query came back empty — and it says nothing for an
equation subject, for the same reason `check_contract_clause_goals` does: the question the
set answers is 'names nothing'.

That makes it THREE readers of one predicate with two different questions (refuse a
contract clause / explain an empty query / — and the rule-body walk, which 8K4RB routed
elsewhere precisely to avoid widening this). It is a lower-severity reader than the
contract one — a query is interactive and the user sees the empty result — but it belongs
in the same design, because a per-node CLASSIFICATION would serve all three where a
widened SET serves none of them correctly.

