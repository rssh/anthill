## Attributes

- id: WI-20261012-V04MK-two-structured-proofs-of-one
- created: 2026-10-12T21:16:32Z

- status: Open
- status_agent: user
- status_at: 2026-10-12T21:16:32Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TWO STRUCTURED PROOFS OF ONE KB WITH A STEP OF ONE NAME: THE SECOND'S STEP IS "NOT FOUND" — so the second proof cannot be discharged, whatever it claims. Found while writing WI-20261012-CDHSQ's rows; reproduced on the tree before it (bcad34e8) and as it delivered (docs/measurements/test-infrastructure/lemma-premise-2026-10-12.txt §7 (ii)), with no rule's predicate anywhere in the file.

MEASURED, `anthill prove --no-cache`, one file:
  rule big: gte(?x, 3.0) :- gte(?x, 5.0)
  proof big
    rule h1: gte(?x, 3.0) :- gte(?x, 5.0)  by z3
    using h1  by z3
  end
  rule small: gte(?x, 1.0) :- gte(?x, 5.0)
  proof small
    rule h1: gte(?x, 1.0) :- gte(?x, 5.0)  by z3
    using h1  by z3
  end
`✓ big: proved`, and `error: …small: rule '….small.h1' not found`. With the second step named `h2` both prove.

WHERE TO LOOK: `synthesize_step_rule` (anthill-cli/src/prove.rs) defines the step's SHORT name (`h1`) in the global scope under the step's qualified name (`<parent>.h1`) and labels the synthesized rule with the symbol that returns. A second step of the same short name is a second definition of `h1` in one scope — which symbol it returns, and what `rule_id_by_qn("<parent2>.h1")` then finds, is what to measure first. The suites did not meet it: each of their structured proofs is alone in its file, or names its steps apart.

THE CONTROL: the file above proves both; a step cited by another proof's conclusion by its qualified name is the one of that proof; and the rows that exist (`prove_structured_*`, WI-20261012-CDHSQ's `STRUCTURED`, which names its steps apart for want of this) are as they are.

DONE WHEN: the control rows hold and fail when backed out; the gate is green.

