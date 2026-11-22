## Attributes

- id: WI-20261122-P6G1P-resolver-option-commit-to-the
- created: 2026-11-22T15:32:17Z

- status: Open
- status_agent: user
- status_at: 2026-11-22T15:32:17Z

- acceptance: cargo-test, scaland-sbt-test

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

