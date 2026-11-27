## Attributes

- id: WI-20261122-P6G1P-resolver-option-commit-to-the
- created: 2026-11-22T15:32:17Z

- status: Open
- status_agent: user
- status_at: 2026-11-22T15:32:17Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261127-AGR9S-resolver-the-continuation-is

## Description

Resolver option: commit to the first definite proof of a goal that is ground when selected
WHO NEEDS IT. anthill-traces (outside this repository; design: its docs/design/high-level-design.md §4.4) decides contract clauses on ground values through execute_typed_logical_query. A clause that holds costs one proof. A clause that FAILS after ground goals with several proofs costs the product of those proofs: on the specification it checks, a state-validity rule broken in a late conjunct runs out of fuel from 10 entities per kind, because earlier conjuncts (composite-key uniqueness, at-most-one rules: a disjunction inside forall with two or three true branches per pair) have 1 / 4 / 64 proofs at 1 / 2 / 3 entities, and the failure replays every combination.

WHAT IS THERE TODAY (read from the code on 2026-11-22). '|' is rule or(?a, ?b) :- push_choice(?a, ?b) (stdlib/anthill/kernel/kernel.anthill). The PushChoice arm of the resolver (kb/resolve.rs) stores both branches as Continuation candidates of a ChoicePoint frame, cut_barrier: None, whatever the goals are; nothing checks whether they are ground under σ. forall_in is unrolled into one conjunct per element with no commit; some_in is a choice point per element (step_bounded_quant). So when a later goal fails, backtracking re-enters every stored alternative of every ground goal before it, although an alternative of a ground goal binds nothing and leaves the same state, so it can only reach the same failure.

MEASURED, no specification involved (release build, k ground disjunctions then a goal that fails, '(...) & (1 = 2)'):
  k                        1    2    4     8      12      16
  (1 = 1) | (2 = 2)       15   39  167  2583  40999  655415 steps   (2^k)
  (1 = 1) | (1 = 2)       14   27   53   105    157     209
  !(!((1 = 1) | (2 = 2))) 13   25   49    97    145     193       (negation commits)

WHAT IS ASKED. An opt-in ResolveConfig flag (name open, e.g. commit_ground_goals). With it, a goal that is ground under σ when it is selected — a push_choice, a some_in, a forall_in instance, a call of a rule — keeps no alternatives once it has a DEFINITE proof: the choice points opened while proving it are cut (the cut barriers of proposal 033.1 / WI-568 are the mechanism; !(!(g)) shows the effect). A first proof with a residual, or a truncated attempt, keeps the alternatives, since a later definite proof may exist. Off by default: it changes proof counts (a ground (A) | (B) with both true is two proofs, and KB.execute counts proofs — dedup_answers: false, proposal 052). On KB.execute it rides on the options of WI-20261122-96QKW.

WHAT IS NOT ASKED. Changing push_choice for non-ground goals: there the second branch can bind differently and must stay. The general form — skip any choice point a failure does not depend on — is WI-20261122-VT9S7 (dependency-directed backtracking), which keeps proof counts and so could be on by default.

DONE WHEN. A test: the k = 16 chain above ends 'no' in linear steps with the flag on (within a small factor of the one-true-branch row) and in 2^k with it off (the control); (?x = 1) | (?x = 2), ?x > 1 still answers ?x = 2 with the flag on; a ground some_in with two witnesses followed by a failing goal is linear with the flag on; a ground goal whose first proof is residual and second definite answers definite with the flag on; and the existing relation-multiplicity tests (which run with the flag off) still pass.

## Changes

### 2026-11-24T10:55:25Z — feedback — user

TWO CORRECTIONS from a review of proposal 076, with the user 2026-11-24 (both reproduced on a debug build of that day; proposal 076 sections 3 and 4).

1. 'GROUND WHEN SELECTED' IS NOT ENOUGH UNDER AN ASSUMPTION WITH A FREE VARIABLE. A ground goal can bind a CALLER variable through an assumption in scope. MEASURED: fact hyp(99); rule pick(0) :- hyp(1); rule pick(0) :- hyp(2); rule t1(?x) :- (forall(?n), hyp(?x) -: pick(0)) answers ?x = 1 and ?x = 2; rule t2(?x) :- (forall(?n), hyp(?x) -: pick(0), ?x <=> 2) answers ?x = 2. pick(0) is ground and each of its proofs binds ?x through hyp(?x), so committing to its first proof loses t1's second answer and t2's only one. The condition for the commit is: ground when selected, AND every assumption in scope at the call ground under sigma (conservative; O(1) with a count of non-ground assumptions on the scope).

2. TWO OF DONE WHEN'S CONTROLS.
  - '(?x = 1) | (?x = 2), ?x > 1 still answers ?x = 2': = tests and does not bind. MEASURED: that query answers two CONDITIONAL answers (residual eq(?_, 1), gt(?_, 1) and its twin). The branches are to be written ?x <=> 1 and ?x <=> 2, which answers ?x = 2.
  - 'the k = 16 chain in 2^k with the flag off (the control)': if proposal 076's guard lands and is on by default, the failing chain is linear with the commit off too, so the control needs the guard off as well, and the chain does not tell the commit from the guard. What does: a ground goal with two proofs that SUCCEEDS, answer dedup off -- two proofs without the commit, one with it.

ALSO OPEN FOR THE COMMIT, as for the guard (proposal 076 section 10, question 3): an alternative the commit never runs sets no truncated flag and records no fault, so a search that today ends undecided because of such an alternative would end decided.

### 2026-11-24T10:56:22Z — feedback — user

DECIDED with the user 2026-11-24 (proposal 076 section 3, question 3): an alternative the commit, or 076's guard, never runs sets neither the truncated flag nor a fault. A skip is a refutation of the conjunction, since the continuation has no solution whichever proof of the goal precedes it. So a search that today ends undecided only because it walked into such an alternative and met the depth limit there ends decided: !(dead(0)) over fact g(0); rule g(?n) :- g(?n + 1); rule dead(?n) :- g(?n), 1 = 2 moves from conditional to true at --max-depth 8. This closes the 'ALSO OPEN' note above; kernel-language 8.3's wording is still to be changed with the user when it lands.

### 2026-11-27T22:46:09Z — feedback — claude

WHERE THIS LANDS (proposal 076 section 4; with the user, 2026-11-28): the commit is built at 076 Stage C, at the same exit as the guard (WI-20261122-VT9S7), opt-in on ExecuteOptions; this ticket depends on WI-20261127-AGR9S (Stage A) until Stage C has a ticket of its own. The guard, on by default, already makes the failing k = 16 chain linear with proof counts intact, so the chain does not tell the commit from the guard; what does is a ground goal with two proofs that SUCCEEDS, answer dedup off (two proofs with the guard, one with the commit). 076 corrects two of this ticket's controls: the 2^k baseline needs the guard off too, and the binding branches are written <=>, not =. The INTERIM of 076 section 4 (a ground goal handed to a nested search, the mechanism !(!(g)) uses) is NOT built ahead of the machine: the user, 2026-11-28, anthill-traces is not blocked, it has a workaround.

