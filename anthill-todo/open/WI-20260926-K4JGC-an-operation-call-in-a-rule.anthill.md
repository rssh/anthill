## Attributes

- id: WI-20260926-K4JGC-an-operation-call-in-a-rule
- created: 2026-09-26T09:49:55Z

- status: Open
- status_agent: user
- status_at: 2026-09-26T09:49:55Z

- acceptance: cargo-test

- depends_on: WI-20260926-CYNPE-a-waiting-goal-is-re-evaluated

- tags: proposal-068

## Description

AN OPERATION CALL IN A RULE BODY IS EVALUATED OR NOT DEPENDING ON WHERE IT IS WRITTEN — the same call answers true at the top of an `=` operand, false nested under a constructor, and nothing as a goal argument; a stuck call is bound as DATA and reported as a definite answer. Proposal 068 §1.1–1.2 (step A2 of the 068/060 sequence).

MEASURED (068's problem section, `main` at fa32695e / 92e2e774; `C.tag` a bodied match, `tag(red()) = 1`; `fact p(1)`; (total, definite)):
  bb(v: String.contains("abc", "b")) = bb(v: true)      (0, 0)   truth 1
  box(v: C.tag(red())) = box(v: 1)                       (0, 0)   truth 1
  ?v <=> box(v: C.tag(red()))                            binds ?v's field to THE CALL tag(red())
  ?v <=> box(v: C.tag(red())), ?v = box(v: 1)            (0, 0)   truth 1
  box(v: C.tag(red())) === box(v: 1)                     0        truth 1
  p(C.tag(red()))                                        (0, 0)   truth 1   (head matching is structural)
  not(p(C.tag(red())))                                   (1, 1)   NAF proves a falsehood
  ?v <=> box(v: C.tag(?c))                               (1, 1)   ?v = box(v: tag(?_)) — should be conditional
  intersection({1,2}, {2}) = {2}                         (0, 0)   no implementation: undecided, not false

THE CAUSE: each consumer reduces to its own depth — `reduce_operand` the top of an operand, `unify_values` only the node its walk is at (a bind stores the rest unvisited), head matching (`unify_match_values`) nothing.

THE CHANGE (068 §1.1). ONE strategy for `<=>`, `=` / `neq`, `===`, cmp, arith, and a goal's arguments before its head is matched: evaluate each side until what is left is a variable, a SUSPENDED call or an UNREDUCED call, then work structurally. For `<=>`: a mismatch anywhere fails definitely; a variable binds; a stuck call against anything is a PENDING pair; a bind that binds a pending suspended call's blocker re-evaluates it within the same goal; identical stuck subtrees unify by reflexivity. 068 §1.2: where a bind would store a SUSPENDED call, the call becomes a fresh variable plus a pending equation — a delayed goal with WI-20260926-CYNPE's (step A1) blockers — so no binding ever holds an unevaluated call. UNREDUCED is undecided, parked (WI-20260926-CYNPE). Here a blocker is an unbound argument variable; a dictionary blocker is D1. `@[simp]` does not fire inside the evaluation (068 §5). kernel-language §8.3's `<=>` bullet ("its only evaluation is head-normalizing a node") and evaluation paragraph are updated with this ticket.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven, back-out stated at its site): every row above answers its truth column, the no-implementation rows UNDECIDED; `pair(?c, box(v: C.tag(?c))) <=> pair(red(), ?v)` answers `?v = box(v: 1)` definite; `?v <=> box(v: C.tag(?c))` answers conditionally with the pending `tag(?c)`, and definitely `box(v: 1)` once `?c = red()` follows. THE LIBRARY CONSEQUENCE, asserted at its site and owned by the Set ticket: the five `wi616_semantic_eq_test` rows over `insert`/`empty` chains become undecided (068 §2.3). CONTROLS, stated at their sites: `box(v: ?n) <=> box(v: C.tag(red()))` (1, 1) either way; the WI-580 unfold's narrowing rows (`append(?a, [3]) = [1, 3]`) unchanged; classic-mini unchanged (tiny-sat 2, alphabet-words 27/12/100, map-colouring 6).

