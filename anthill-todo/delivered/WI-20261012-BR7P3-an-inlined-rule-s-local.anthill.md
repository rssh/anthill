## Attributes

- id: WI-20261012-BR7P3-an-inlined-rule-s-local
- created: 2026-10-12T15:16:24Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-14T12:16:53Z

- acceptance: cargo-test, scaland-sbt-test

## Description

AN INLINED RULE'S LOCAL VARIABLES ARE THE CALLER'S OF THE SAME INDEX — so the SMT emitter proves a satisfiable body unsatisfiable. Found by /code-review of WI-20261012-ZZ7PH and not of that change: reproduced on the tree before it (374dda80) and as delivered (docs/measurements/test-infrastructure/law-lowering-2026-10-12.txt §7 (i)).

WHAT IS THERE: `anthill-smt-gen`'s `try_inline_rule_call` reads a called rule's body into the caller's document with the callee's head variables bound to the call's arguments. Its doc says the callee's local De Bruijn indices "are renamed into a per-call namespace so they don't collide with the caller's"; they are not. A callee variable that the head does not bind and the body does not define is written by `translate_expr` as `var_<i>` — its index in the CALLEE's frame — which is the name the caller's own variable of index i has. `translate_called_rule` (the one-argument call form) does the same with a fresh bindings map.

MEASURED, `anthill prove --no-cache`:
  rule helper(?x, ?w) :- lt(?x, ?y), lt(?y, ?w)
  rule r :- helper(?a, ?b), gte(?a, 5.0)            proof r by z3 end
`✓ r: proved (z3: unsat)`. The document is `(declare-const var_0 Real) (declare-const var_1 Real) (assert (< var_1 var_0)) (assert (< var_0 var_0)) (assert (>= var_1 5.0))`: the callee's `?y` and the caller's `?b` are both `var_0`. The body is satisfiable (a = 5, y = 6, b = 7).
  rule shifted(?r) :- eq(?r, ?y + 1.0), gte(?y, 0.0)
  rule c :- shifted(?v), lt(?z, 0.0), gte(?v, 0.0)  proof c by z3 end
`✓ c: proved (z3: unsat)`: `(assert (>= var_0 0.0)) (assert (< var_0 0.0))` — the callee's `?y` and the caller's `?z`. Satisfiable (y = 0, z = -1).

WHAT ZZ7PH ADDED TO IT: a variable's sort is of the frame it was inferred in, and is not carried to a name that leaks out of an inlined callee; at a declared sort the same collision is `(lt@T var_1 var_1)`, or a solver error where the two variables' sorts differ. No new silent case — where the sorts agree it is the collision above — but the fix here has the callee's sorts to carry with the renamed variable (`Emitter::var_sorts`, saved and restored around the callee in both call forms).

COUNT FIRST: which documents of examples/webots-modelling/lf1 and of the suites have a variable that leaked from an inlined callee, and in which of them it collides with a variable of the caller — lf1's proofs inline rules, and a verdict that rests on a collision is not a verdict. A temporary instrument that dumps every emitted document, run before and after (ZZ7PH's measurement file §4 has the method and the 125-document baseline), says which documents move when callee locals are renamed apart, and for each that moves whether its verdict does.

TO DECIDE with the user, on that count: the name a callee's local gets (it moves the bytes of every document with one, and so its cache key and its witness's document hash); and what is done with a proof whose verdict was a collision's.

THE CONTROL: the two reproductions are COUNTEREXAMPLE (sat), each a row that fails when the renaming is backed out; a callee whose locals do not collide today has the verdict it had; a callee's local of a declared sort is declared at that sort.

DONE WHEN: the control rows hold and fail when backed out; the documents that moved are listed with their verdicts before and after; the gate is green.

## Changes

### 2026-10-12T21:17:39Z — feedback — user

FROM WI-20261012-CDHSQ: a call stated as the relation of a cited lemma's premise is REFUSED when it stands in the body of an inlined rule and names that rule's own variable (`Emitter::state_predicate_call`, the `inlining` stack; row `a_call_in_an_inlined_rule_that_names_its_own_variable_is_refused`) — stated, it was the relation of the caller's variable of the same index, and a false claim proved (docs/measurements/test-infrastructure/lemma-premise-2026-10-12.txt §6 (3)). When the names are told apart here, that refusal goes, and the row turns: such a call is stated of a variable of its own. And a second face of the same collision was a regression of ZZ7PH's, fixed there: whether `?x = <term>` names `?x` was asked of the term's text, which in an inlined rule is in the caller's names (§6 (1)).

### 2026-10-14T12:16:47Z — feedback — user

DELIVERED (6f5262ce), with WI-20261014-FHEEK — the user's decision, 2026-10-14: an inlined rule's own variables are named apart, var_<n> continued past the clause's own. COUNTED FIRST: no lf1 or suite document wrote an inlined rule's own variable (one hit, kf2sd.mixed.at, refused as recursive), so no verdict rested on a collision and the renaming moved no document. Every variable of an inlined frame (inline_rule_call, translate_called_rule) is bound when the frame is opened — its head's to what the caller passed, the rest to names past every name of the document (name_own_variables, frame_size), on across the worlds of one document; sorts kept by those names (an own variable of T declared at T, where it was (lt@T var_1 var_1)); an unbound variable inside an inlined frame is an error. The other direction too: a construction passed into an inlined rule is closed over the caller's frame (fx(P(x: ?a), ?r) read ?a as fx's own ?w, and a false claim proved, with the renaming alone too); a variable bound to a construction written as a term is refused in both frames. The two reproductions are COUNTEREXAMPLES (rows apart, one_arg); 1KF32's helper had made three false proofs of the same collision (by_fact, by_number, by_row), COUNTEREXAMPLES now. CDHSQ's refusal of a stated call naming an inlined rule's own variable is gone and its row turned (a_call_in_an_inlined_rule_that_names_its_own_variable_is_stated_of_it: related stated of wrap2's var_2; deep a COUNTEREXAMPLE). scaland's one-argument form named apart the same. Measurement: docs/measurements/test-infrastructure/inlined-names-2026-10-14.txt.

