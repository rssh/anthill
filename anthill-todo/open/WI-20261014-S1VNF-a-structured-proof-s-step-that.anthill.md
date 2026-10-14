## Attributes

- id: WI-20261014-S1VNF-a-structured-proof-s-step-that
- created: 2026-10-14T12:30:45Z

- status: Open
- status_agent: user
- status_at: 2026-10-14T12:30:45Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A STRUCTURED PROOF'S STEP THAT CITES AN EARLIER STEP DECLARES THE TWO STEPS' NEW VARIABLES UNDER ONE NAME — the solver answers "constant 'var_1' … already declared" where a verdict is owed. Found while delivering WI-20261014-FHEEK (docs/measurements/test-infrastructure/inlined-names-2026-10-14.txt §7 (i)); measured 2026-10-14 on d7a8ffcb and on 6f5262ce, `anthill prove --no-cache`, z3 5.1.0.

MEASURED:
  rule helper(?x, ?w) :- lte(?x, ?y), lte(?y, ?w)
  rule big: gte(?x, 0.0) :- gte(?x, 5.0)
  proof big
    rule h1: gte(?x, 3.0) :- gte(?x, 5.0), lte(?n, 1.0), lte(?k, 2.0)  by z3
    rule h2: gte(?x, 1.0) :- gte(?x, 3.0), helper(?x, ?m)  using h1 by z3
    using h1, h2 by z3
  end
`? big: unknown (z3 said (error "… invalid declaration, constant 'var_1' (with the given signature) already declared"))` on both trees. The claims hold.

WHAT IS THERE (`anthill-smt-gen`, `lift_one_clause`, `shared_arity > 0`): a step is lifted as a ground assertion in its parent's frame, and the block declares the step's NEW variables (index >= shared_arity) by their indices. Steps share the parent's frame, so two steps' new variables are numbered from the same `shared_arity`: h1's `?n` and h2's `?m` are both `var_1`, and h2's document — which h1's lift is spliced into — declares `var_1` twice. Since FHEEK an inlined rule's own variable in a step's document is named past the step clause's frame (`var_<n>` continued), which a cited step's new variable of that index meets the same way (here `helper`'s `?y` is `var_2`, and h1's `?k` is `var_2`).

RELATED: WI-20261012-5613E (a step's lift names a parent variable the parent's document does not declare). Its option (a) — the lift's block declares every variable it names, the consumer leaving out what it has declared — would turn this loud error into a silent one: h1's `?n` and h2's `?m` one constant. So the two are decided together, or this first.

TO DECIDE: the name a step's new variable gets in a lift (it moves the bytes of every document a step lift is spliced into, and their cache keys); e.g. past the consumer's frame and every name it has, as FHEEK named an inlined rule's own variables.

THE CONTROL: `big` proves; a step whose lift names no new variable, or whose consumer cites one step, has the document it has, to the byte (lf1's `step_distance_lemma`, the `prove_structured_*` rows).

DONE WHEN: the control rows hold and fail when backed out; the documents that moved are listed; the gate is green.

