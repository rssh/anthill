## Attributes

- id: WI-20260820-4KXPD-resolver-a-choice-point-whose
- created: 2026-08-20T21:27:20Z

- status: Open
- status_agent: claude
- status_at: 2026-08-20T21:27:20Z

- acceptance: cargo-test, scaland-sbt-test

- tags: resolver

## Description

RESOLVER: a choice point whose successful candidate had a BODY is told it produced nothing, and manufactures a FLOUNDERED answer. `record_solution_in_nearest_choice_point` credits only the nearest ChoicePoint.

FOUND while delivering WI-20260820-FFPGD, and PRE-EXISTING — measured present with answer dedup both ON and OFF, so it is not that ticket's change. FFPGD's own description called this "only a counter"; it is not.

THE MECHANISM. At the goals-empty yield, `record_solution_in_nearest_choice_point` (kb/resolve.rs) walks `self.stack.iter_mut().rev()` and `return`s at the FIRST `FrameState::ChoicePoint`, incrementing its `child_solutions`. Its one reader is `step_choice_point`'s delay fallback: `if child_solutions == 0 && any_delayed { rotate the goal behind the tail }`, which on the default resolve path residualizes into a FLOUNDERED solution. So a choice point CP whose winning candidate opens a body containing any non-builtin goal never sees the credit -- that inner goal's own ChoicePoint takes it -- and if any sibling candidate of CP delayed, CP believes it proved nothing and rotates.

MEASURED, driven, not read off the source:

  namespace test.probe
    import anthill.reflect.{nonvar}
    sort N  entity g(v: Int64)    end
    sort A  entity ans(v: Int64)  end
    fact g(v: 1)
    fact g(v: 2)
    fact ans(v: 5)
    rule inner(?y, ?x) :- ans(v: ?x)                -- BODY: opens a choice point over `ans`
    rule inner(?y, ?x) :- nonvar(?x), ans(v: ?x)    -- delays (NonVar is non-reorderable), sets any_delayed
    rule top(?x) :- g(v: ?y), inner(?y, ?x)
  end

`kb.resolve(&[top(?x)], ..)` reports 4 solutions with residual lengths [0, 1, 0, 1] in PROOF mode (`dedup_answers: false`) and 3 with [0, 1, 1] in ANSWER mode. Two of them are spurious: `?x = 5` is DEFINITELY proved in each branch, and the floundered twin is a "conditional" answer to a question already answered. Replace `inner`'s first clause with the bodyless `fact inner(1, 5)` / `fact inner(2, 5)` and the residuals vanish -- the credit then reaches `inner`'s own choice point. That bodyless form is `wi_ffpgd_answer_dedup_test::a_dropped_duplicate_still_counts_as_this_choice_points_proof`, which pins the ORDERING half of this and says at its site why it must be bodyless.

WHY IT IS NOT A FOUR-LINE FIX, and this is the whole ticket. Deleting the `return` so every ancestor ChoicePoint is incremented reads obviously right -- the plural name already claims it, and every ChoicePoint on the stack at a yield IS an ancestor of the yielding frame, so "did anything under me succeed?" is exactly what the loop would answer. But the reader's contract is `produced something => DO NOT rotate`, and suppressing a rotation can LOSE REAL SOLUTIONS: the delayed candidate is delayed precisely because a var is unbound, and the rotation is what re-asks it after the caller's tail binds that var. A delayed candidate that would have succeeded on the second pass is silently dropped instead. So the change is a semantics decision in the flounder machinery (WI-519 residual honesty, WI-628 truncation, WI-629 the rotation counter, WI-670 the refutation pre-drop, WI-739 the reorderable gate all meet here), not a counter repair.

WORK: decide what the fallback's guard actually wants. Three candidates, and the ticket is to choose ONE with a measurement, not to pick the tidy-looking one:
 (a) increment EVERY ancestor ChoicePoint -- fewest spurious residuals, but needs a driven case proving no delayed candidate that would have succeeded on rotation is lost;
 (b) keep the counter as-is and make the FALLBACK ask a different question (e.g. did this frame's own subtree yield, tracked by a generation stamp rather than a count);
 (c) keep the rotation and suppress the SPURIOUS RESIDUAL instead -- a rotated-and-residualized goal whose own subtree already produced a definite solution is not an honest flounder.
Name at the chosen site which of the other two was rejected and on what measurement.

ACCEPTANCE -- DRIVE IT. (1) The fixture above returns exactly ONE solution, definite, `?x = 5`, in both proof and answer mode. (2) THE CONTROL THAT MATTERS: a case where the delayed candidate REALLY DOES need the rotation -- the caller's tail binds the var and the delayed clause then succeeds -- still yields that solution. Without this row, option (a) looks green and has silently traded two spurious residuals for a lost answer. (3) An honest flounder still flounders: `rule unbindable(?x) :- neq(?x, 1)` (the `wi739_guard_generator_delay_test` shape, where nothing can ever bind the var) keeps its residual. (4) Full workspace green, with any moved count named and its new value justified rather than re-baselined.

REFERENCE: kb/resolve.rs `record_solution_in_nearest_choice_point` (renamed from `record_solution_in_ancestors` in WI-FFPGD, precisely because the plural name hid this) and `step_choice_point`'s `child_solutions == 0 && any_delayed` arm; WI-519; WI-628; WI-629; WI-670; WI-739; WI-20260820-FFPGD.

