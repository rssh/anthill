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

## Changes

### 2026-10-14T13:35:00Z — feedback — user

NAMING DECIDED (user, 2026-10-14): docs/smtlib-forward-mapping.md §7.6, Names in a Document. A step's new variable in its lift is a variable of the document that is not the proof clause's, so it continues the document's one count (var_<n>), as an inlined rule's own variable does since BR7P3. What stays to decide here is who declares it (with WI-20261012-5613E).

### 2026-11-02T11:10:31Z — feedback — claude

MERGED WITH WI-20261012-5613E (user, 2026-11-02, dependency review). The two tickets were left with one decision — who declares a step's variable in a lift — so this ticket now owns both defects, and 5613E is closed into it. 5613E's half, kept here so it is not re-derived: a step's lift names a variable of its PARENT's frame that the parent's document does not declare. The consumer — the parent's conclusion, emitted with abstract_body — declares a variable only where its own assertions name it (note_free_vars), and what stands only in a rule call it skips is named by none of them. MEASURED (anthill prove --no-cache): rule p: gte(?x, 1.0) :- gte(?x, 0.0), other(?x, ?y) with proof p { rule h: gte(?x, 1.0) :- related(?x, ?y) by trust(…); using h by z3 } emits (assert (=> (….related/2 var_1 var_0) (>= var_1 1.0))) and no (declare-const var_0 …), so z3 answers 'unknown constant var_0' where the verdict is a COUNTEREXAMPLE (p is false at x = 0.5); a step's CONCLUSION reaches it too (the same parent with rule hq: gte(?y, 0.0)). THE DECISION, now this ticket's: (a) the lift's block declares every variable it names and the consumer leaves out what it has declared — which, without this ticket's renaming, turns the 'already declared' error into a SILENT one (h1's ?n and h2's ?m one constant), so the renaming lands with it or first; or (b) the consumer declares, told by the lift which of its frame's variables the lift names. CONTROLS, both tickets': big (above) proves; p is a COUNTEREXAMPLE, and a solver error when backed out; a step whose variables the documents already declare keeps its document to the byte (lf1's step_distance_lemma, the prove_structured_* rows). Origin: /code-review of WI-20261012-CDHSQ, docs/measurements/test-infrastructure/lemma-premise-2026-10-12.txt §6 (5), §7 (iv).

