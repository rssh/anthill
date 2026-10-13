## Attributes

- id: WI-20261013-FXT2P-a-rule-of-several-heads-cannot
- created: 2026-10-13T08:43:18Z

- status: Open
- status_agent: user
- status_at: 2026-10-13T08:43:18Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A RULE OF SEVERAL HEADS CANNOT BE PROVED `by z3` — the proof is refused since WI-20261012-KF2SD, where it was proved of its first head alone; what is owed is the conjunction of its heads, and each of its clauses numbers its variables by its own head first. Filed with the user's word, 2026-10-13; KF2SD's review, finding 1 (docs/measurements/test-infrastructure/several-clauses-2026-10-13.txt §6 (1), §7 (ii)). Measured on main at 2f5666f3, `anthill prove --no-cache`, z3 4.16.0.

WHAT IT IS: `rule X: H1, H2 :- B` states both heads of the one body (proposal 032, conjunctive sugar), and is the same as `H1 :- B` beside `H2 :- B` but for the NAME: the loader makes a clause for each head under the one label, so `proof X` is one proof owed of both and `using X` hands a consumer both. Proposal 032, "Z3 backend": `(assert (and B1 ... Bm)); (assert (not (and H1 ... Hn)))`.

WHAT IS THERE (`anthill-smt-gen`, `Emitter::collect_rule`): a proof's rule is the clauses its name states, and more than one is refused — "the rule '…both' is 2 clauses — … a proof is ONE document". The LIFT goes clause by clause and is of every head (`lift_rule`), as it was.

MEASURED:
  rule both: gte(?x, 0.0), gte(?x, 5.0) :- gte(?x, 1.0)        proof both by z3 end
  rule bad:  gte(?y, 5.0) :- gte(?y, 1.0)                      proof bad using both by z3 end
BEFORE KF2SD (70fffe8f) both `✓ proved` — `both` by its first head, which the body gives, and `bad`, false at y = 1, by the second head of a lift nobody had proved. SINCE: `both` is refused and `bad` is "cite … did not prove in this run". THE COST:
  rule band: gte(?x, 5.0), lte(?x, 10.0) :- gte(?x, 5.0), lte(?x, 10.0)      proof band by z3 end
is true, was proved (of its first head), and is refused. A rule of several heads that is TRUSTED is cited as before, a clause for each head.

WHY THE HEADS ARE NOT JUST CONJOINED: the frames differ. Each clause numbers its variables by its own head first — the two lifts of `rule two: gte(?x, 0.0), gte(?y, 0.0) :- gte(?x, 1.0), gte(?y, 2.0)`:
  (forall ((var_0 Real) (var_1 Real)) (=> (and (>= var_1 1.0) (>= var_0 2.0)) (>= var_1 0.0)))
  (forall ((var_0 Real) (var_1 Real)) (=> (and (>= var_0 1.0) (>= var_1 2.0)) (>= var_1 0.0)))
`?x` is `var_1` in the first clause and `var_0` in the second. The emitter writes a variable by its index (`bindings`, `entity_bindings`, `var_sorts` are keyed by it), so the second clause's head read under the first's bindings is a claim about other variables — the family of WI-20261012-BR7P3.

TO DECIDE, how each head is read:
  (a) IN THE FIRST CLAUSE'S FRAME, through a map of variables read off the two bodies — they are one body, goal for goal — with a head's own variables fresh; the bindings, the entities and the sorts follow the map. One document, as proposal 032 has it.
  (b) A DOCUMENT FOR EACH CLAUSE, the proof proved when every one is `unsat` — which changes what a proof's record, cache key and witness are of (WI-20261013-1KF32 (3) asks the same of a call).
  (c) ONE FRAME FOR THE CLAUSES OF ONE RULE, made by the loader — the rule's variables numbered once, for every head — so the emitter needs no map; every other reader of a clause's frame sees a clause that has variables it does not name.
AND NOT THE SAME CLAIM: a PREDICATE written as several rules and proved under its name (`rule viol(?w) :- gte(?w, 1.0), lte(?w, 0.0)` beside `rule viol(?w) :- gte(?w, 0.0)`, `proof viol by z3` — it proved by its first body, and is refused by the same sentence). Its clauses have bodies of their own: the claim is of each, and (b) is the only one of the three that reads it. Kept refused, or decided here. An OBLIGATION on a rule of several clauses (`emit_obligation`) goes by the same door.

THE CONTROL: `both` is a COUNTEREXAMPLE (x = 1), and proved when backed out to the first head; `bad` does not prove; `band` proves; a rule of two heads that name different variables first, its second head false (`gte(?x, 0.0), gte(?y, 5.0) :- gte(?x, 10.0), gte(?y, 2.0)`, false at y = 2), is a COUNTEREXAMPLE — and proves if the second head is read under the first clause's indices, where its variable is `?x`; a head that reads an entity's field is read off the right variable; a rule of one head has the document it had, to the byte; lf1's verdicts are as they are. KF2SD's rows `a_proof_of_a_rule_of_several_clauses_is_refused` and `an_obligation_on_a_rule_of_several_clauses_is_refused` are turned to these verdicts, or kept for what is still refused, each said.

DONE WHEN: the control rows hold and fail when backed out; the refusal in `collect_rule` and its comment, which name no ticket today, name what is still refused and why; docs/smtlib-forward-mapping.md §4.5 says what a proof of a rule of several heads is; the documents that moved are listed; the gate is green.

