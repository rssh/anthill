## Attributes

- id: WI-20261126-QJ9NW-a-contract-clause-s-goal-that
- created: 2026-11-26T09:10:07Z

- status: Open
- status_agent: user
- status_at: 2026-11-26T09:10:07Z

- acceptance: cargo-test

## Description

A contract clause's goal that names nothing loads under a disjunction or a quantifier: `requires n < 5 | nosuch` loads clean, while `requires nosuch`, `!nosuch` and `n < 5 & nosuch` are refused.
FOUND by /code-review of WI-20261126-78B4M (86be3521a). It is pre-existing, and 78B4M's §5.4 sentence now states it as a gap ('under a disjunction or a quantifier it is not yet').
MEASURED 2026-11-26 on 74d52327c, `operation f(n: Int64, xs: List[T = Int64]) -> Int64 requires <G> = n` loaded through the CLI:
  G = nosuch                       refused, UndefinedContractGoal ('names `nosuch`, which is declared nowhere')
  G = !nosuch                      refused, the same
  G = n < 5 & nosuch               refused, the same
  G = n < 5 | nosuch               LOADS
  G = (forall ?x in xs: nosuch)    LOADS
  G = (some ?x in xs: nosuch)      LOADS
  and in the ensures list: `ensures result < 5 | nosuch` LOADS.
WHY: check_contract_clause_goals asks KnowledgeBase::undefined_query_goal_functors, whose walk follows goal branches only under a negation or a conjunction. A bare disjunction or quantifier is 'left to resolution', the right policy for its other caller, a query pattern. A contract clause is no query: its requires is proved at every call, and a disjunct or a quantifier body naming nothing is a branch that can never hold (or, in an ensures, a promise about a name nothing can query). 78B4M's data-slot refusal (UnresolvedContractName) does not reach these names either: they stand in goal slots, which it leaves to the goal check so that a name is reported once.
WHAT IS ASKED: a goal naming nothing in any goal slot of a requires or ensures clause is refused at load, under | and inside a quantifier body as at the clause. The query path's descent stays as it is: the contract check takes its own policy, or the walk takes the policy as a parameter. The discharge exemption stays: a discharge's antecedents declare hypotheses.
SIBLING: WI-20260902-7XFYQ (the goal-READING family, an equation subject / a constant / a non-Bool op in a contract clause) is the same pass asked another question; it may share the seam.
DONE WHEN: (1) the four LOADS rows above (three requires, one ensures) are refused, each naming the name once; (2) controls: a disjunct over a declared predicate loads and gates a call; a discharge's hypothesis is not refused; the query path still answers 'no solutions' for an unknown disjunct, not a load error; (3) the back-out measured and said at the rows.

