## Attributes

- id: WI-20261012-KF2SD-a-predicate-of-several-clauses
- created: 2026-10-12T21:16:29Z

- status: Open
- status_agent: user
- status_at: 2026-10-12T21:16:29Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A PREDICATE OF SEVERAL CLAUSES IS READ AS ITS FIRST ONE BY THE SMT EMITTER — so a `by z3` proof whose body calls it is of the first clause alone, and a false claim proves. Found while probing WI-20261012-CDHSQ; reproduced on the tree before it (bcad34e8) and as it delivered (docs/measurements/test-infrastructure/lemma-premise-2026-10-12.txt §7 (i)).

WHAT IS THERE: a rule call in a proved body is read by `anthill-smt-gen`'s `process_body_goal` three ways, and each takes one clause of the functor: the body inlined (`try_inline_rule_call`) and the one-argument form (`translate_called_rule`) take `.find(|clause| !clause.is_fact())`, the first bodied clause; a call matched to a fact (`try_match_fact_call`) returns on the first fact its arguments agree with. A rule's body is the HYPOTHESIS of its claim, and a predicate of several clauses holds when ANY of them does: read as its first, the hypothesis is stronger than the rule states, and what is proved is less than what the record says.

MEASURED, `anthill prove --no-cache`:
  rule related(?a, ?b) :- gte(?a, ?b)
  rule related(?a, ?b) :- lte(?a, ?b)
  rule lemma: gte(?a, ?b) :- related(?a, ?b)        proof lemma by z3 end
`✓ lemma: proved (z3: unsat)` — `related(1, 2)` holds by the second clause, and `gte(1, 2)` does not. And of facts:
  fact start(5.0)
  fact start(-1.0)
  rule lemma: gte(?d, 0.0) :- start(?d)             proof lemma by z3 end
`✓ lemma: proved (z3: unsat)`.

WHAT CDHSQ HAS TO DO WITH IT: a cited lemma's premise that is a rule's predicate is now the uninterpreted relation of the predicate's name and arity, so a lemma proved of the first clause is handed to its consumer as a statement about the predicate — every clause of it. Before CDHSQ it was handed on with no premise at all.

COUNT FIRST: which calls in the proved bodies of examples/webots-modelling/lf1 and of the suites are of a functor with more than one clause that could answer them — lf1's `real_pose_at` has a base fact for each drone and a bodied step, and a call whose ground arguments select one fact has one candidate, not several — and which have a clause of another arity (`span/2` beside `span/3` is "rule call arity mismatch" today, whichever the call is).

TO DECIDE with the user, on that count: what such a call is in a proof's body — (a) REFUSED, where more than one clause can answer it; (b) the DISJUNCTION of its clauses' readings, which the emitter's binding scheme (a variable is one SMT term) does not hold as it stands; (c) the uninterpreted relation with nothing read of it, which is sound and proves less.

THE CONTROL: the two lemmas above do not prove — a COUNTEREXAMPLE or a refusal, by the decision — and fail the other way when backed out; a call that exactly one clause can answer is read as it is; lf1's verdicts are as they are, or each that is not is listed with why.

DONE WHEN: the control rows hold and fail when backed out; the documents that moved are listed; the gate is green.

