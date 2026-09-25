## Attributes

- id: WI-20260924-35E14-a-rule-body-operation-call
- created: 2026-09-24T15:53:12Z

- status: Open
- status_agent: user
- status_at: 2026-09-24T15:53:12Z

- acceptance: cargo-test, scaland-sbt-test

- tags: resolver

## Description

A RULE-BODY OPERATION CALL WHOSE ARGUMENT IS STILL UNBOUND ANSWERS NOTHING, SILENTLY, instead of delaying until the argument is bound — so a typed head whose body calls an operation on its own column never answers.

MEASURED 2026-09-24 on HEAD, with Colour providing Score[T = Colour] itself (score: red 1, green 2, blue 3 — one provider, the carrier's own, so no dispatch question is involved):
  rule late(x: Colour) :- Score.score(x, 3)                               no solutions
  rule early(?x) :- domain_member(?x, Colour), Score.score(?x, 3)          blue          (control: the argument bound first)
  rule unbound(?r) :- Score.score(?v, ?r)                                  no solutions  (the argument never bound)
late is proposal 060 §2.1's parameter form, the shape map-colouring is written in. The typed head's generator is APPENDED after the written body (060 §2.2), so the call runs first with x unbound — and answers an empty set: no residual, no warning. A != goal in the same position DELAYS and is re-asked, which is why map-colouring works; an operation call does not. kernel-language.md's Bool-view passage records this fall-through for the Bool view ('a call whose arguments are not ground … falls through … (no answer) … making that case delay instead is open follow-up work'); the functional-relation view (Score.score(?v, ?r)) has the same fall-through, and no ticket owned either.

WANTED: a call with an unbound argument DELAYS and rotates like any goal that cannot run yet (060's rule: 'the generated goal is ordinary: it delays on unbound operands'); it is re-asked once the argument is bound; if it never is, it flounders LOUDLY on WI-737's route — never an empty answer set.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven): late answers blue, definite; unbound answers one CONDITIONAL row carrying the call in its residual. Controls, passing either way by design: early, and a call whose argument is bound before it.

FOUND BY WI-20260911-5G28A's demo2 (060-implementation §7.3, S5): Wrap[T = X].top's clause calls Score.score(?v, 3) before the appended generator binds ?v, which is one reason its count answers 0 (wi_5g28a_rule_dictionary_test.rs, demo2_the_count_answers_zero).

