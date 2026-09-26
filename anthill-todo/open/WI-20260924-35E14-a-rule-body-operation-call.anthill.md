## Attributes

- id: WI-20260924-35E14-a-rule-body-operation-call
- created: 2026-09-24T15:53:12Z

- status: Open
- status_agent: user
- status_at: 2026-09-24T15:53:12Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260926-CYNPE-a-waiting-goal-is-re-evaluated

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

## Changes

### 2026-09-26T08:28:47Z — feedback — user

DEPENDS ON PROPOSAL 068 (WI-20260926-ACG10), decided in review 2026-09-26. Same root as WI-20260827-XBHX3, different symptom: a rule-body operation application has no SUSPENDED state, so each position improvises — the WI-580 case-split compares the unevaluated call as DATA (a wrong refutation), and the WI-938 hook treats it as a FAILURE (this ticket: 'falls through to ordinary candidate selection … (no answer)', resolve.rs around line 2854). Under 068 §2 Score.score(x) is SUSPENDED with blocker x — it rotates, is asked again once x is bound, and 'late' answers blue; 'unbound' stays suspended and ends conditional. The bridge's three decline reasons (unbound argument / no supplier / supplier tie) separate into SUSPENDED and UNREDUCED instead of one fall-through. 068's problem section carries this ticket's three rows.

