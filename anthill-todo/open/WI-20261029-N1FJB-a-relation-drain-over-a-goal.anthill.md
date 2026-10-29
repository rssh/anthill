## Attributes

- id: WI-20261029-N1FJB-a-relation-drain-over-a-goal
- created: 2026-10-29T22:47:01Z

- status: Open
- status_agent: claude
- status_at: 2026-10-29T22:47:01Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A RELATION DRAIN OVER A GOAL THAT WAITS ON A CUT SEARCH SAYS THE SEARCH FLOUNDERED. Found under WI-20260913-P9QBF (252a59db), which made a lazy search cut at its depth limit raise search_truncated(max_depth) where its stream would end; a cut BELOW a goal still surfaces as a flounder. MEASURED on 50518b13, default max_depth 100, over rule Deep(x: ?x) :- Deep(x: ?x), rule deep(?x) :- Deep(x: ?x), operation deepCount() -> Int64 effects Error = length(deep.takeN(10)), rule counted(?n) :- ?n <=> deepCount(): counted.takeN(10) raises relation_floundered(goals: [unify(Var, countDeep)]), and deep(1).negate() drained raises relation_floundered(goals: [not(deep(1))]). Neither goal waits on a variable: deepCount() raised search_truncated, which the bridge reads as a truncation below (BridgeDisposition::Truncation: the goal waits, the search is marked incomplete), and not(deep(1)) is undecided because its ground sub-search was cut (step_naf's residual-or-truncated arm). The flounder wording names a repair, bind the variable, that does not exist. WHY: the residual row carries no cause for a goal that waits on a cut. Solution::undecided carries an UnknownCause only for a builtin's Unknown answer, step_naf hands DrainVerdict::undecided up (None for a cut), and Interpreter::materialize_solution raises relation_floundered for any residual row. THE DESIGN QUESTION: where the cut rides on the waiting goal — an UnknownCause variant, or a cause of its own beside it, since UnknownCause feeds GammaVerdict::universal and a cut is no statement about a universal — and what the relation drain raises for a row whose every residual goal waits on a cut (search_truncated, the payload P9QBF added, is the obvious candidate). The raw execute face keeps the row as undecided(subst, residual) data either way. WHAT NOT TO BREAK: a goal that waits on an unbound variable still raises relation_floundered; a fault still outranks; the eager drains and NAF verdicts are unchanged. ACCEPTANCE: counted.takeN(10) and the negate drain report the cut, not a flounder; a CONTROL whose goal waits on an unbound variable still raises relation_floundered; a mixed row (one goal waiting on a cut, one on a variable) has a stated answer; cargo-test green via scripts/test.sh.

