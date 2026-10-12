## Attributes

- id: WI-20261012-CDHSQ-a-cited-lemma-s-premise-that
- created: 2026-10-12T15:16:26Z

- status: Open
- status_agent: user
- status_at: 2026-10-12T15:16:26Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A CITED LEMMA'S PREMISE THAT IS A RULE'S PREDICATE IS DROPPED FROM ITS LIFT — so a conditional lemma is handed to the citing proof as an unconditional one, and a false claim proves. Found by /code-review of WI-20261012-ZZ7PH as the same defect in a LAW, where that ticket refuses it; for a lemma it is older: reproduced on the tree before it (374dda80) and as delivered (docs/measurements/test-infrastructure/law-lowering-2026-10-12.txt §6 (1), §7 (ii)).

WHAT IS THERE: `anthill-smt-gen` lifts a cited rule to `(assert (forall (…) (=> premises conclusion)))` (`lift_one_clause`), always in abstract mode. There `process_body_goal` passes over a goal whose functor has program clauses — it "CONSTRAINS nothing here, its vars stay free, and an ambient lift is what re-states it" (WI-897's comment at the branch). That is the safe direction for the CONSUMER's own body under `abstract_body`: a conjunct left out of a satisfiability check can only lose an `unsat`. In a LIFT the goal is a premise of the implication, and leaving it out weakens the antecedent — the same act WI-897 measured and made loud for a premise it could not read (`String.lte(?name, "z")` vanishing). Only the rule-call case was left silent.

MEASURED, `anthill prove --no-cache`:
  rule related(?a, ?b) :- gte(?a, ?b)
  rule lemma: gte(?a, ?b) :- related(?a, ?b)        proof lemma by z3 end
  rule bogus: gte(?c, 5.0) :- gte(0.0, ?c)          proof bogus using lemma by z3 end
`✓ lemma: proved` (its own discharge reads `related`'s body) and `✓ bogus: proved (z3: unsat)` — `c <= 0` implies `c >= 5`. The lift in `bogus`'s document is `(assert (forall ((var_0 Real) (var_1 Real)) (=> true (>= var_1 var_0))))`. The same with `proof lemma by trust(…)`.

WHAT ZZ7PH DID: for a spec's LAW the premise is not passed over — the law is not lowered, and is said (`Emitter::lowering_law`; row `a_law_whose_premise_is_a_rules_predicate_is_left_out_whole`, back-out (s)). A cited lemma is as it was.

COUNT FIRST: which cited rules of examples/webots-modelling/lf1 and of the suites have a premise that is a rule's predicate — a structured proof's conclusion cites its steps, and "structured proofs emit abstractly because they depend on their cited lifts" (`policy.rs`); of the 17 lift documents the suites emit (ZZ7PH's measurement file §4), how many lose a premise this way, and for each consumer whether its verdict holds once the premise is back.

TO DECIDE with the user, on that count: what such a premise becomes in a lift — (a) the lemma is REFUSED as not citable while it has one, as a rule with no conclusion is; (b) the predicate is an UNINTERPRETED Bool function, declared once (ZZ7PH's `Declarations`), the lift's premise and the consumer's own skipped call both written with it — which keeps the lift an implication and gives the consumer what it knows of the predicate; (c) the callee's body is read into the antecedent, which the lift's own comment refuses ("chasing the cited rule's body would condition its truth on facts the consumer doesn't quote"). And whether the `Inline` translation policy (proposal 030 δ) is what says which.

THE CONTROL: `bogus` does not prove — a COUNTEREXAMPLE or a refusal, by the decision — and fails the other way when backed out; a consumer that cites a lemma with a rule-predicate premise and HOLDS that premise in its own body still proves under (b); lf1's verdicts are as they are, or each that is not is listed with why.

DONE WHEN: the control rows hold and fail when backed out; the lifts that changed are listed; proposal 030's γ.1 says what a lift does with such a premise; the gate is green.

