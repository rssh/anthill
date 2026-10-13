## Attributes

- id: WI-20261012-KF2SD-a-predicate-of-several-clauses
- created: 2026-10-12T21:16:29Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-13T08:33:43Z

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

## Changes

### 2026-10-13T08:32:50Z — feedback — user

COUNTED AND DECIDED 2026-10-13 (docs/measurements/test-infrastructure/several-clauses-2026-10-13.txt §1–§2). THE COUNT: of the calls of a rule's predicate that the proved bodies of lf1 and of the suites meet — lf1 44 of 13 predicates, the emitter crate's suite 71 of 24, the CLI suite 114 of 39 — the ONE predicate of several clauses anything read as one is lf1's `real_pose_at/3`: two base facts and the step, whose head is all variables. Six calls, in lf1's four top-level safety proofs, EACH answered by two clauses — the drone's fact, and the step. So the ticket's guess was half right: a ground drone selects one FACT, and the step answers beside it; the four proved the claim at step 0. No call was of a predicate with a clause of another arity but in CDHSQ's own fixtures, skipped and not read. DECIDED with the user: a call more than one clause can answer is REFUSED now, and the disjunction is a ticket of its own with a motivating example (WI-20261013-1KF32); lf1 is REWRITTEN so the launch geometry is a predicate of facts alone (`initial_pose`) and the four read it; CDHSQ committed first. And, asked while the count ran: WI-20261013-PR8SP, a nullary constructor is no constant of its sort — "a problem for discharge".

### 2026-10-13T08:32:59Z — feedback — user

BUILT, REVIEWED AND MEASURED 2026-10-13 (measurement file §3–§7). WHAT IS BUILT (`anthill-smt-gen`, `Emitter::answering_clause`): a call that is read is read by the one clause of its arity whose head no argument of the call rules out — a number against another, a constructor against another; the call's own variable counts as what the frame has bound it to (a number, a construction, a fact's constructor slot), and a free variable, a variable inside a construction and a computed term rule nothing out. One: read as it was, by the fact, the one-argument form or the inlined body, which now take the clause chosen and no longer each find "the first". Several: REFUSED, naming the predicate, how many can answer and the rule the call stands in. None: refused. A clause of another arity is no candidate (`span/2` beside `span/3`). scaland's emitter reads a rule call one way and refuses the same (`SmtGen.scala`, `SeveralClausesTest`). lf1: `initial_pose` facts, `real_pose_at(0, ?drone, ?pose) :- initial_pose(?drone, ?pose)`, `initial_real`; fourteen proved, every document it had to the byte. /code-review, 14 findings: THE SAME READING IN TWO MORE PLACES, refused by the same rule — the rule being PROVED where its name is several clauses (`rule both: gte(?x, 0.0), gte(?x, 5.0) :- gte(?x, 1.0)` proved by its first head and was cited for its second), and an ENTITY PREMISE over an entity of several facts (`Mode(kind: 2.0, cap: ?c)` took the cap of kind 1); two frame leaks the first cut selected a clause by, each of which proved a false claim (a rule read by the one-argument form kept its caller's entities; a variable inside a bound construction was looked up in the wrong frame); a number in a head selected and was not read; the fact reader's two silent skips; `WITNESS_FORMAT_VERSION` 4 → 5. And found by comparing every document the two trees emit: a proof of a rule named as its namespace was of the namespace's declaration — an empty document, a COUNTEREXAMPLE of a rule that holds — and is of the rule. THE CONTROL: 6 rows in the emitter crate, 17 in `cli_tests`, 5 in scaland; 22 back-outs, each failing the rows that are about it (§4); with the emitter as it was 19 of the 23 fail and the four that pass are the controls, by design. DOCUMENTS (§5): lf1 16 of 16, the emitter crate's suite 66 of 66 and the CLI suite 177 of 178 there again to the byte; the one that moved is that namespace-named rule's. MOVED: docs/smtlib-forward-mapping.md §4.5; lf1's three safety files and PUNCHLIST.md.

### 2026-10-13T08:33:10Z — feedback — user

FOUND, AND NOT OF THIS CHANGE (measurement file §7), each run on the tree before it and as delivered. FILED with the user's word: WI-20261013-PR8SP, WI-20261013-1KF32. PUT TO THE USER AND NOT DECIDED, so not filed: (i) a second definition of a bound variable rebinds it and the first is dropped — `lte(?d, 3.0) :- ?d = 3.0, ?d = 5.0` is a COUNTEREXAMPLE of a rule whose body never holds; a hypothesis lost, never one added; (ii) a rule of several heads cannot be proved `by z3`: refused here where it was proved of its first head, and the conjunction proposal 032 specifies is not built — each clause numbers its variables by its own head first, so one clause's head is not written in another's frame; (iii) whether a labeled rule whose head is a predicate is one of its clauses for a proof that reads the predicate — built YES, which is sound, and a predicate with a lemma stated of it is then read by no proof.

