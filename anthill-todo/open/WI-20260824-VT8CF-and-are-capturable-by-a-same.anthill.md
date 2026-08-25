## Attributes

- id: WI-20260824-VT8CF-and-are-capturable-by-a-same
- created: 2026-08-24T12:55:39Z

- status: Open
- status_agent: user
- status_at: 2026-08-24T12:55:39Z

- acceptance: cargo-test, scaland-sbt-test

## Description

`/`, `%` AND `^` ARE CAPTURABLE BY A SAME-NAMED DECLARATION, and neither of the two mechanisms that protect the other minted operators reaches them. Found by /code-review on the WI-20260824-BFB9A diff; the obvious fix was attempted there and REFUTED by the corpus, which is the part worth reading before trying again.

THE GAP, DRIVEN. With `operation mod(a: Int64, b: Int64) -> Int64 = 99` in a namespace, a minted `7 % 2` written in that namespace reaches the local declaration and returns 99 instead of 1. No diagnostic is raised anywhere. `/` (`div`) behaves the same; `^` (`pow`) has no tier target at all, so there is nothing even to reclaim to.

WHY NEITHER MECHANISM COVERS THEM. Two guards protect minted operators and both decline these by design:
  - WI-BFB9A's rival REFUSAL only reaches a spec operation on a PARAMETRIC carrier (`typing::spec_op_parent_sort`). `Int64.div` / `Int64.mod` sit on `Int64`, which declares no `sort T = ?`, so there is no `provides Int64[T = …]` to prescribe and the refusal correctly stands down — see `check_rival_spec_operations`.
  - `reclaim_minted_operator` only reaches the POSITION-DIRECTED BOOLEANS (`or`, `not`, `and`), whose primitives are `anthill.kernel.*` / `Bool.and` and which no carrier re-implements.
So one minted-operator family has three treatments — bypass the ladder, reclaim after it, or nothing — and this ticket owns the third.

THE OBVIOUS FIX IS WRONG, MEASURED. `reclaim_minted_operator` was briefly widened from "the position-directed booleans" to "any minted operator whose primitive does not DISPATCH", spelled `spec_op_parent_sort(primitive).is_none()`. That reads correctly and is false: `Int64.div` IS a concrete operation and passes the predicate, but the OPERATOR `/` is carrier-polymorphic — `Float.div` exists — so reclaiming forced every minted `/` to the Int64 one. SIX corpus rows fell with `type mismatch in div.a (op-arg): expected Int64, got Float`: `eval_test::{m3_float_division, m3_float_division_by_zero_is_infinity, m3_float_nan_detection}` and `lf1_real_spec_test::{lf1_lower_violation_is_unsat, lf1_step_distance_bound_is_within_two_meters, lf1_upper_violation_is_unsat}`. THE LESSON IN ONE LINE: "the primitive has one meaning" is not "the operator has one target". The narrowness is now stated at the site with this measurement.

WHAT A REAL FIX HAS TO DO. Decide `/` by the CARRIER of its operands, which is what the ladder is doing today when it reaches `Float.div` — so the repair cannot be a resolution-time override keyed on the name alone. Candidates, none costed: (a) make `Int64.div`/`Float.div` a dispatched spec op on a parametric carrier, which would put them inside BFB9A's refusal and close this by construction — the largest change and the only one that removes the special case; (b) refuse a free-standing declaration of any name pratt mints an operator to, independently of whether the target dispatches, which is a rule about OPERATOR SPELLINGS rather than about spec ops and needs its own census of what that would break; (c) accept the gap and document it in kernel-language.md beside the operator table.

NOT DRIVEN: (a), (b) and (c) are code reads. FIRST STEP: census how many names pratt mints an operator to that are NOT already covered by the refusal or the reclaim — the answer decides whether this is three names or a family.

CONTROL, when it is fixed: `a_non_parametric_carriers_operation_is_not_a_spec_op` (wi_bfb9a_rival_spec_operation_test) currently RECORDS the gap — it asserts the local `mod` wins and returns 99, with a pointer here. That row inverts when this closes, and its inversion is the measurement. Drive it through an OPERATION BODY, not a rule: `:- eq(7 % 2, 1)` answers 0 definite solutions with or without the shadow, because `eq` never binds and the goal suspends, so it measures nothing.

ACCEPTANCE: a minted `%` / `/` means its carrier's operation whatever the enclosing namespace declares, or the divergence is documented at the operator table with this ticket's number; the float rows above stay green; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-08-25T07:27:51Z — feedback — claude

THE `reclaim_minted_operator` THIS TICKET IS WRITTEN AROUND IS NOT IN THE TREE, and that WIDENS this ticket rather than narrowing it. Read this before the ticket body.

WHAT HAPPENED. WI-20260824-BFB9A was withdrawn after two /code-reviews and re-implemented on 2026-08-25. The reclaim did not come back. It was scope creep on BFB9A's ask — refuse a free-standing rival of a spec operation — and its query-path half carried a live defect: a `goal_position_boolean(resolved, pos_args.len())` added to `convert_query_term_expecting`'s `Term::Fn` arm, which recurses into positional AND named args through itself, so it routed at every depth and on WRITTEN calls. Measured: a fact holding `or(true, false)` became unqueryable by ANY spelling, exit 0, no diagnostic. Its doc also carried a fabrication ("`and` is absent from `PRELUDE_QUALIFIED` where `or` / `not` are present" — `anthill.prelude.Bool.and` IS in that table, load.rs, and is the sole reason `&` was reclaimable at all).

WHAT THIS TICKET'S POPULATION IS NOW. Two treatments, not three: BYPASS THE LADDER (`minted_connective_symbol`, the carrier-agnostic connectives `<=>` / `===` — WI-888's line, which deliberately excludes `eq`) or NOTHING. So `or`, `not` and `and` join `/`, `%` and `^` in the population this ticket owns: a namespace-level `operation or(...)` captures a minted `|` exactly as `operation mod(...)` captures `%`. Whether they are one family or two is this ticket's first question rather than a settled point — the reclaim answered it "two" on a code read, and that answer left with it.

WHAT IS UNCHANGED. BFB9A's refusal reaches none of these, for the reason the ticket body already states and which is now written in kernel-language.md §5.1 with this ticket's number at it: `Bool.and`, `Int64.div`, `Int64.mod` sit on NON-PARAMETRIC carriers and `anthill.kernel.or` / `.not` on no carrier at all, so `typing::spec_op_parent_sort` answers `None` and there is no `provides` to prescribe. `check_rival_spec_operations` exists and is that leg.

THE "OBVIOUS FIX IS WRONG, MEASURED" PARAGRAPH STANDS AS A MEASUREMENT and no longer describes the tree: the six float rows really did fall under `spec_op_parent_sort(primitive).is_none()`, but the function that predicate lived in is gone, so re-reading it as "the narrowness is stated at the site" will find no site.

THE CONTROL THIS TICKET NAMES DOES EXIST: `wi_bfb9a_rival_spec_operation_test::a_non_parametric_carriers_operation_is_not_a_spec_op` records the gap — `operation mod(a, b) = 99` in a namespace, and `7 % 2` written in that namespace answers 99. Driven through an OPERATION BODY, as this ticket prescribes. That row inverts when this closes.

