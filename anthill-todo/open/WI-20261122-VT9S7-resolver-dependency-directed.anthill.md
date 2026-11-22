## Attributes

- id: WI-20261122-VT9S7-resolver-dependency-directed
- created: 2026-11-22T15:32:38Z

- status: Open
- status_agent: user
- status_at: 2026-11-22T15:32:38Z

- acceptance: cargo-test, scaland-sbt-test

## Description

Resolver: dependency-directed backtracking — on a failure, skip the choice points the failure does not depend on
WHO NEEDS IT. anthill-traces (outside this repository; design: its docs/design/high-level-design.md §4.4) decides contract clauses on ground values; a clause that fails is decided only by exhausting its search, and today that search re-enters choice points whose alternatives cannot change the failure. Measured there: a state-validity rule broken in a late conjunct runs out of fuel from 10 entities per kind; the same 'no' after k ground two-way disjunctions costs 2^k steps (table in WI-20261122-P6G1P).

WHAT IS THERE TODAY (read from the code on 2026-11-22). Backtracking is chronological: when a goal fails, the resolver resumes the most recent ChoicePoint frame and tries its next candidate (kb/resolve.rs), whatever that choice bound. If the failing goal does not read any variable the choice point bound — the choice was a ground disjunction, or bound a variable the failing goal never mentions — every alternative of it reaches the same failure, and so does every combination of such choice points.

WHAT IS ASKED. On a failure, resume the most recent choice point the failure DEPENDS ON — one that bound a variable read by the failing goal, transitively through the bindings it was given — and discard the independent ones between (conflict-directed backjumping: each binding remembers the choice point that made it; a failure's conflict set is the choice points of the bindings it involved; a jump merges the conflict set into the target's). It prunes only subtrees that hold no solution, so answers AND proof counts are unchanged: it can be the default, unlike the commit of WI-20261122-P6G1P, which it covers for failures (a ground goal's choice points bind nothing, so nothing depends on them). It also covers non-ground cases the commit does not: e.g. a goal binding ?c from one of n matches followed by a ground goal that fails is decided after one try, not n.

Points to settle in the design: a failure inside a negation's sub-search, and a NAF goal's own dependency set (the bindings of its goal's variables); delayed (waiting) goals woken by a binding; a search truncated by depth or fuel, which must still read as truncated, never as a refutation; residual solutions; and the step accounting of the jump.

WHAT IS NOT ASKED. Changing what a successful search enumerates: after a solution, asking for the next still resumes chronologically (a ground disjunction with two true branches stays two proofs).

DONE WHEN. Tests: the k = 16 chain of WI-20261122-P6G1P ends 'no' in linear steps with the default config; member(?c, [1, …, n]) followed by a failing ground goal is decided in O(1) retries, not n; member(?c, [1, …, n]), ?c > n - 1 still answers ?c = n; a dependency through a NAF goal and through a delayed goal each still finds its answer; and every existing resolver and relation test passes unchanged, answers and multiplicities alike.

