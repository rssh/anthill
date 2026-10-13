## Attributes

- id: WI-20261012-CDHSQ-a-cited-lemma-s-premise-that
- created: 2026-10-12T15:16:26Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-12T21:17:46Z

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

## Changes

### 2026-10-12T21:17:30Z — feedback — user

COUNTED AND DECIDED 2026-10-12 (docs/measurements/test-infrastructure/lemma-premise-2026-10-12.txt §1–§2). THE COUNT: of the 29 lifts lf1 and the suites make — lf1 2, the emitter crate's suite 8, the CLI suite 19 — NONE has a premise that is a rule's predicate, so no consumer's verdict was at risk; the one call anything skips is a consumer's own (`step_distance_lemma`'s body, twice `distance_at_step`). lf1 has two rules with such a premise that no `by z3` proof cites (`velocity_envelope`, `step_distance_lemma`), and a probe proof citing the second proved `gte(?c, 5.0) :- gte(0.0, ?c)`. The same branch passed over a fact's predicate, a one-argument rule, a connective over goals (`or` and `and` are rules of the kernel) and the premise of a structured proof's step, each measured. DECIDED: (b) — the predicate is an UNINTERPRETED relation, the lift's premise and the consumer's own call both written with it; a consumer states only the calls of relations a cite declared, so a proof that cites no such lemma has the document it had; a call that cannot be written is refused. Not chosen: (a) refuse the cite, which leaves a step unable to state a premise that is its parent's rule call; (c) read the callee's body, which a consumer that skips its call never holds. The `Inline` policy does not say which: the premise is written so whatever its policy, and δ.4's routing is still open (proposal 030 γ.1).

### 2026-10-12T21:17:33Z — feedback — user

BUILT, REVIEWED, MEASURED AND GATED 2026-10-12/13 (measurement file §3–§8). WHAT IS BUILT: a cited lemma's premise that is a rule's predicate is `(ns.related/2 a b)`, the relation of the predicate's name and arity over the sorts of its arguments, declared once in the consumer's document (`Emitter::state_predicate_call`, `BodyIs`, `Declarations::predicates`); a proof states its own call of a relation a lemma it cites declared — the call it skips and the call it reads the body of, after the reading, so a bound argument is its value. REFUSED and not left out: named arguments, a bare name or a string for an argument, an argument nothing gives a sort under an abstract parameter, two signatures, a call inside an inlined rule that names the rule's own variable (BR7P3's collision), and in a lift a connective over goals and an entity premise's slot that is no variable. THE CONTROL: `bogus` is a COUNTEREXAMPLE, the lemma trusted or proved; a proof that holds the premise proves — concrete, through an inlined body, a fact, a one-argument rule, a nullary predicate, over a carrier, and a structured proof's parent — and a parent that does not hold its step's premise is a COUNTEREXAMPLE where it proved. WHAT MOVED: nothing that existed — the 189 documents lf1 and the two suites emit (16 + 49 + 124) are each there again to the byte; lf1's dry-run hash is ZZ7PH's. /code-review: fifteen findings, applied — among them a regression of ZZ7PH's in the same function (a definition in an inlined rule read as a condition on the caller's variable: `viol` proved), the entity slot, the inlined rule's own variable, a cite's defining rules synthesized before it is lifted, the relation named with its arity. BACK-OUTS: 23, each fails a row, and each of the 21 rows (3 emitter, 18 CLI) fails under one. WITNESSES: `WITNESS_FORMAT_VERSION` 3 → 4, decided with the user — a sidecar written by an emitter that proved too much is out of reach. GATE: scripts/test.sh exit 0, 36 result lines all ok, 9 497 passed, 0 failed, 14 ignored; scaland `sbt testFull` 672 passed — nothing of scaland's is changed, it has no lift. NOT BUILT (proposal 030 γ.1): a connective premise as the formula it is, an entity premise's literal slot as an equation, a nullary constructor as a constant of its sort — which lf1's drone-indexed predicates need to discharge a lemma about them — and a conclusion that is a rule's predicate.

### 2026-10-12T21:17:36Z — feedback — user

FILED, with the user's word, what was found here and is not of this change (measurement file §7), each reproduced on the tree before it: WI-20261012-KF2SD — a predicate of several clauses is read as its first one, facts too, so a false lemma proves; WI-20261012-V04MK — two structured proofs of one KB with a step of one name: the second's step is not found; WI-20261012-1P005 — a variable a premise names before the equation that defines it is left out of a lift's quantifier, and is the consumer's variable of the same index; WI-20261012-5613E — a step's lift names a variable of its parent's frame that the parent's document does not declare.

