## Attributes

- id: WI-20260923-KCNA0-a-rule-body-call-whose
- created: 2026-09-23T20:45:19Z

- status: Open
- status_agent: user
- status_at: 2026-09-23T20:45:19Z

- acceptance: cargo-test

- tags: typing

## Description

A RULE-BODY CALL WHOSE REQUIREMENT NO PROVIDER COVERS — AT A PROJECTION THE CALL GROUNDS, OR AT A STRUCTURAL FORMER — LOADS CLEAN AND ABORTS A DEBUG BUILD AT EVALUATION.

FOUND by WI-20260923-N3W68 while reproducing its item #6, and outside that ticket's thirteen items: it is not a twin divergence but a gap in WI-20260917-NR6FJ's exemptions.

MEASURED (debug build of `anthill`, each program loads with zero errors, then `anthill query … 'answer(?r)'` panics in `bridge_op_to_eval` with `DeferToRequirement: requirement param __req_desc not bound in caller frame`). Fixture: `sort Desc { sort T = ?; operation tag() -> Int64 }` (body-less), `Red provides Desc[T = Red]`, `sort Blue { entity blue }` (provides nothing), `sort Box { sort E = ?; entity box(v: E) }`.
  (q1) PROJECTION GROUNDED BY THE CALL: `operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag()` + `rule answer(?r) :- pick(box(v: blue()), ?r)`. δ grounds `x.E` to `Blue` at the bridge, nothing provides `Desc[T = Blue]`, the slot is skipped, the body reads it.
  (q2) STRUCTURAL FORMER, NO PROJECTION: `operation pick2(x: Box) -> Int64 requires Desc[T = {Red}] = Desc.tag()` + `rule answer(?r) :- pick2(box(v: red()), ?r)`.
  (fwd) FORWARDED THROUGH A TYPED CALLER: `pick` requiring `Desc[T = {x.E}]`, `operation outer(b: Box) -> Int64 requires Desc[T = {b.E}] = pick(b)`, `rule answer(?r) :- outer(box(v: red()), ?r)` — the forward is admitted at load (the caller covers it, correctly), and `outer`'s own slot is then the unprovided `Desc[T = {Red}]` at the bridge.

WHY THEY ESCAPE. `check_rule_body_operation_requires` (rule_requirements.rs, WI-NR6FJ) is the load refusal for exactly this class — a written `requires Desc[T = Blue]` reached from a rule body IS refused there, "Blue provides no Desc" — but it (a) skips a PROJECTION carrier ("the caller supplies, and S8CBV's caller-coverage refusal owns the undischargeable case" — true at a typed call site, not at a rule-body goal whose arguments ground the projection), and (b) reads the carrier with `sort_functor_of_view`, which has no answer for an effect row / tuple / arrow, so a structural former is skipped too. The typed-call-site twin refuses both: q2's shape is the "STRUCTURAL FORMER … nothing provides" refusal (dict.rs), and an ungrounded projection is S8CBV's.

CONTROLS that must keep working: the same programs with a PROVIDED carrier and a bare projection (`requires Desc[T = x.E]`, `pick(box(v: red()))` from a rule body, and the forward `outer(b) requires Desc[T = b.E] = pick(b)`) each answer 7 today.

ACCEPTANCE: q1, q2 and fwd are refused at LOAD with a diagnostic naming the requirement and the carrier (preferred — the NR6FJ doc's own "at the call, at load, where the typer has both"), or, where the carrier genuinely depends on a runtime value, suspend to a NAMED residual at the bridge — never the debug abort. Driven through `load_all` and resolution, back-outs stated at the tests; the controls above green.

## Changes

### 2026-10-14T15:07:43Z — feedback — claude

RUN-TIME HALF DELIVERED by WI-20261013-GFS6A (4d22dbc2): q1, q2 and fwd each answer one undecided row whose cause is Unreduced (Solution::undecided), where a debug build aborted in bridge_op_to_eval; the controls answer 7; a body that never reads the slot runs. The bridge records an operation's own requirement that the arguments pin and no provider answers as an absence (UnavailableWhy::NoProvider) instead of skipping it, and a read of it is BridgeDisposition::Unreduced. Rows: wi_gfs6a_woven_call_waits_on_its_dictionary_test's three KCNA0 rows. WHAT IS LEFT is the preferred LOAD refusal: q2's carrier is written concretely (Desc[T = {Red}]), so it depends on no run-time value and the acceptance's run-time alternative does not cover it — NR6FJ's check_rule_body_operation_requires reads the carrier with sort_functor_of_view, which has no answer for a row; q1 and fwd are grounded by literal arguments the rule body does not type until 7D48J's clause typing.

### 2026-10-14T16:11:47Z — feedback — claude

CORRECTION (38c9e23b, decided with the user 2026-10-14): q1, q2 and fwd now FAIL — no answer, by a complete search, no fault — rather than the undecided row the note above records: a requirement the arguments fix at a type no provider answers is known not to be available, and the call has no value there (BridgeDisposition::NoProvider, Stuck::Absent). Rows: wi_gfs6a_woven_call_waits_on_its_dictionary_test's three KCNA0 rows (*_fails). The load half is unchanged and still open.

