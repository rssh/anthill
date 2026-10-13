## Attributes

- id: WI-20261012-5613E-a-step-s-lift-names-a-variable
- created: 2026-10-12T21:16:38Z

- status: Open
- status_agent: user
- status_at: 2026-10-12T21:16:38Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A STEP'S LIFT NAMES A VARIABLE OF ITS PARENT'S FRAME THAT THE PARENT'S DOCUMENT DOES NOT DECLARE — so the solver answers "unknown constant var_0" where a verdict was expected. Loud, and no wrong verdict. Found by /code-review of WI-20261012-CDHSQ (docs/measurements/test-infrastructure/lemma-premise-2026-10-12.txt §6 (5), §7 (iv)); the mechanism is older than that ticket.

WHAT IS THERE: a step of a structured proof is lifted as a GROUND assertion in its parent's frame (`lift_one_clause`, `shared_arity > 0`): the block declares the variables that are the step's own, and the leading slots are taken to be declared by the consumer. The consumer — the parent's conclusion, emitted with `abstract_body` — declares a variable only where its own assertions name it (`note_free_vars`), and what stands only in a rule call it skips is named by none of them.

MEASURED, `anthill prove --no-cache`:
  rule p: gte(?x, 1.0) :- gte(?x, 0.0), other(?x, ?y)
  proof p
    rule h: gte(?x, 1.0) :- related(?x, ?y)   by trust(…)
    using h  by z3
  end
The document has `(assert (=> (….related/2 var_1 var_0) (>= var_1 1.0)))` and no `(declare-const var_0 …)`: `? p: unknown (z3 said (error "… unknown constant var_0"))`, where the answer is a COUNTEREXAMPLE (p is false at x = 0.5). Before CDHSQ the step's premise was passed over and `p` PROVED. And through a step's CONCLUSION, on the tree before CDHSQ and after alike — the same parent with the step `rule hq: gte(?y, 0.0)`: `(assert (=> true (>= var_0 0.0)))`, and the same solver error.

TO DECIDE: who declares it — the lift's block, every variable it names, with the consumer leaving out what it has declared (the block's lines are already told apart from one another in `emit_assumptions`); or the consumer, told by the lift which of its frame's variables the lift names.

THE CONTROL: the proof above is a COUNTEREXAMPLE, and a solver error when backed out; a step whose variables the parent's document already declares has the document it has, to the byte (lf1's `step_distance_lemma`, the `prove_structured_*` rows).

DONE WHEN: the control rows hold and fail when backed out; the documents that moved are listed, and none that existed has; the gate is green.

