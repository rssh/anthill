## Attributes

- id: WI-20261014-FHEEK-a-variable-an-inlined-rule
- created: 2026-10-14T08:41:06Z

- status: Open
- status_agent: user
- status_at: 2026-10-14T08:41:06Z

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

