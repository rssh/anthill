## Attributes

- id: WI-20261101-C580V-a-call-s-type-argument-is-not
- created: 2026-11-01T06:09:41Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-01T07:43:48Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A CALL'S TYPE ARGUMENT IS NOT INFERRED THROUGH A REQUIRES CLAUSE. Over `sort Wide { sort W = ? }`, `sort Narrow { requires Wide[W = Int64]; entity narrow }`, `sort Narrow2 { sort Q = ?; requires Wide[W = Q] }` and `operation takeAt[Y](x: Wide[W = Y]) -> Int64 = 4`, each of `takeAt(narrow())`, `takeAt(m)` with `m: Narrow2[Q = String]`, and `takeAt(n)` in `g[X](n: Narrow2[Q = X])` is refused with "expected a type for 'Y', got unconstrained" (measured 2026-11-01 on a5720275, and on its parent). The bracketed calls load: `takeAt[Int64](narrow())` loads, and `takeAt[String](narrow())` is refused since WI-20261020-G37HS, which made the typer's subsumption (`types_compatible`) read the instances a refining sort's clauses give it (`instances_through_requires`, shared with `type_admits`). Inference does not: `unify_types` (typing/unify.rs) has no refinement leg, so Y is never bound from the clause. EXPECTED: the three unbracketed calls infer Y (Int64, String, X) and load; `takeAt` over a sort whose clause names no argument (`requires Wide`) keeps its refusal; a sort with two clauses giving two instances of Wide is an explicit decision (refused as ambiguous, or the first), not a silent pick. Related: WI-20261025-27050 C6 (provision lookup does not climb a refinement with written arguments).

## Changes

### 2026-11-01T07:43:39Z — feedback — claude

DELIVERED (031d7d64). Run on the tree first (2026-11-01): the three calls refused 'expected a type for Y, got unconstrained', as written. Fix: unify reads a sort that refines an application's sort through the instance its requires clauses give it (unify::unify_through_refinement over subtype::refinement_unifiers, the instances refinement_admits_applied admits by), where exactly one answer fits — in the bare arm (unify_parameterized_with_sort_ref, which drops the caller's order) and the application arm either side first (a callback's parameter meets the declared one with the refined sort first, measured: with that direction out ap(idW) at (n: Narrow2[Q = String]) -> Z loads at Z = Int64). Found on the way and fixed: (1) a clause's parameter named as the refined sort's (requires Wide[W = List[T = W]]) paired with W by bare key, so Y was String, not List[String]; (2) the argument check reads only a ground pair, and the expected result filled what the arguments left open after it, so -> String = idW(narrow()), a let and a const loaded at a type the clause does not give. Two instances (requires Wide[W = Int64] beside Wide[W = String]): USER DECISION 2026-11-01 — the expected result decides; an argument checked while its parameter type was open is checked again once the call's inference is done (apply::recheck_arguments_left_open, after the expected result, the clauses and the defaults; a wrap the first check decided stands — the first gate found wi_rkmd4's Option-slot control refused without that). With nothing deciding, the call is refused as unconstrained and takeAt[String](b) loads. A clause naming no argument (requires Wide) keeps its refusal; a bare n: Narrow2 is its own instance and is at Y = n.Q. Rows: rustland/anthill-core/tests/include/wi_c580v_type_argument_through_requires_test.rs (9; each arm, the second direction, the dedupe and the second check backed out alone, table in its header). Spec: §8.2 and §5.4 sentences. Full workspace 11,334 passed (node carrier too), families green (node carrier too), scaland 792. /code-review (high): 7 findings — 1 fixed (the leg takes the bases its callers hold), 4 no change (a unify true is a binding, admission stays the subtype check's; TooDeep falls to a refusal by the subtype check; an actual left open is bound by the var arm), 2 skipped: the two-instance refusal reads 'unconstrained' and does not name the two instances; the second check does not re-run the callback-row check (a row left open by the arguments was not found).

