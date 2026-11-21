## Attributes

- id: WI-20261121-QAA6S-the-fresh-load-control-of-wi
- created: 2026-11-21T10:58:24Z

- status: Open
- status_agent: user
- status_at: 2026-11-21T10:58:24Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

THE FRESH-LOAD CONTROL OF wi_rah0z FAILS: A WITNESS WHOSE REQUIREMENT FAILS AT THE INSTANCE ANSWERS A STDLIB EQUALITY IN THE LIBRARY'S OWN LOAD, INSTEAD OF THE CARRIER'S OWN PROVISION (filed with the user 2026-11-21; found running the recipe controls of WI-20261020-NNQ1S). MEASURED on a31f1bf6 and on 20107e7a alike, so older than both of this session's changes: ANTHILL_TEST_FRESH_LOAD=1 scripts/test.sh -p anthill-core --test wi_tests -- wi_rah0z_one_recipe_test::the_outcome_entries_follow_the_switch fails; the shared base and the two-step recipe pass it, and the gate runs the shared base, so it is green there. The row loads AN_EQ_FOR_THE_STDLIBS_LIST — sort EqList { sort A = ?; requires Eq[T = A]; provides PartialEq[T = List[T = A]]; provides Eq[T = List[T = A]]; operation eq(x: List[T = A], y: List[T = A]) -> Bool = true } — and asserts that in a later load it is refused EqualityOfEarlierSort (passes) and that one-shot, in the stdlib's own load, it loads clean. One-shot it is refused: '131:102: type mismatch in anthill.prelude.PartialEq.eq.dispatch: expected matching impl for per-call bindings, got no impl matches — unresolved: anthill.prelude.Eq[T = anthill.reflect.Term]'. The position is in the derived eq members' text (load_derived_eq_members, which has no path; dumped with a temporary probe): line 131 is EffectExpression.eq's case '(guarded(l1, l2), guarded(r1, r2)) -> (if eq(l1, r1) then eq(l2, r2) else false)', column 102 the eq(l2, r2) over guarded's 'guard: List[Term]' (prelude/sort.anthill:387). anthill.reflect.Term provides PartialEq (eq = termEq, reflect.anthill:75) and no Eq. So the List[Term] comparison is resolved through EqList, whose requires Eq[T = Term] does not hold, and is refused there, rather than answered by List's own equality, which holds at Term. TO DECIDE (with the user) which is wrong: (a) dispatch — a provider whose requirement does not hold at the call's instance is no candidate there, so List[Term] takes List's own provision and the fixture loads clean as the row says; or (b) the row — a program that gives the stdlib's List a second equality inside the library's own load is refused there too, and the one-shot half of the row asserts that refusal. ACCEPTANCE: the decision recorded in kernel-language.md if it moves a rule; the row green under all three recipes (ANTHILL_TEST_FRESH_LOAD=1, ANTHILL_TEST_TWO_STEP_LOAD=1, the shared base), its fresh half driving what was decided; a row of its own for (a) or (b) with its back-out measured; full workspace green via rustland/scripts/test.sh.

