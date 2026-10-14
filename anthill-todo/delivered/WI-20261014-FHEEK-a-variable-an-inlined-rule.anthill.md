## Attributes

- id: WI-20261014-FHEEK-a-variable-an-inlined-rule
- created: 2026-10-14T08:41:06Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-14T12:16:40Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A VARIABLE AN INLINED RULE BINDS, WHICH ITS CALLER DEFINED ANOTHER VARIABLE BY, IS LEFT UNDECLARED — z3 answers "unknown constant" where a verdict is owed. Found while delivering WI-20261013-1KF32 (docs/measurements/test-infrastructure/disjunction-2026-10-14.txt §7 (i)); measured 2026-10-14 on main at 79a6703f and on the tree with 1KF32's change, `anthill prove --no-cache`, z3 4.16.0.

MEASURED:
  fact start(5.0)
  rule p(?x) :- start(?x)
  rule outer: gte(?e, 0.0) :- ?e = ?d + 1.0, p(?d)          proof outer by z3 end
`? outer: unknown (z3 said (error "line 8 column 21: unknown constant var_0"))` on both trees. The whole document is `(assert (not (>= (+ var_0 1.0) 0.0)))`: `var_0` is named and never declared. The claim holds (e = 6).

WHAT IS THERE (`anthill-smt-gen`): the caller's `?e` is bound to the TEXT `(+ var_0 1.0)` (`bindings`). `p` is read inlined (`inline_rule_call`): its head variable goes by the caller's name, `p`'s fact binds it to 5.0 in `p`'s frame, and the value is handed back by substitution — `caller_bindings[var_0] = 5.0` — so `var_0` is a BOUND variable, which `note_free_vars` does not declare, while `?e`'s text still names it. 1KF32's `bind_variable` equates where a variable is already named instead of substituting, which is why `lte(?d, 10.0), start(?d)` proves since; but it asks the frame it binds in (`p`'s) and the document's assertions, not the caller's definitions, and the hand-back to the caller substitutes without asking.

TO DECIDE: route the hand-back through `bind_variable` (an equation where the caller already named the variable) — the path every inlined rule's result takes to its caller, so documents may move, and 1KF32's instrument (§5 of its measurement file) says which; or a stack of the frames being read, which the helper asks.

THE CONTROL: `outer` proves; a caller that names nothing it hands an inlined rule has the document it had, to the byte (lf1 and the suites, as 1KF32 §5 measured).

DONE WHEN: the control rows hold and fail when backed out; the documents that moved are listed; the gate is green.

## Changes

### 2026-10-14T12:16:33Z — feedback — user

DELIVERED (6f5262ce), with WI-20261012-BR7P3 (the user's decision, 2026-10-14: rename apart, var_<n> continued). The ticket's program is the one-argument form (translate_called_rule), not the hand-back: its result was bound by substitution, the same defect at another site; the two-argument twin (p2) is the hand-back. Every place a variable is given a value goes through bind_variable: an equation, a one-argument result, an entity's constant, the hand-back (asked in the CALLER's frame, only where the value differs from what was passed), and 1KF32's three; a variable written in an assertion, another binding or a closed construction is equated; one defined twice is the equation of the two (?d = 3.0, ?d = 4.0 was a COUNTEREXAMPLE); an alias given a value gives it to the variable it stands for (?x = ?y, start(?x) left ?y free, a COUNTEREXAMPLE of a true claim, 79a6703f too). The helper asked the text, which collided in an inlined frame: three false claims proved on d7a8ffcb through 1KF32's sites — hence BR7P3 delivered here. The control: outer proves; a caller that writes nothing it hands on has the document it had (a row, passes either way); lf1's 16 documents byte for byte; the suites' 333 but three moved (CDHSQ's turned row, ranking.decrease_violation keeping upc_next = upc + 1, a WI-687 refusal's printed discriminant). 14 rows (wi_fheek_inlined_names_test) + 5 scaland (InlinedNamesTest), every part backed out failing a row. Measurement: docs/measurements/test-infrastructure/inlined-names-2026-10-14.txt. Gate 9815/0; scaland testFull 688+45+1. Found, not of this change: a structured step citing an earlier step declares their step-new variables twice (z3 'already declared', d7a8ffcb too) — §7 (i). It also closes WI-20261012-1P005's program (user is a COUNTEREXAMPLE, lemma by z3 proves) — put to the user.

