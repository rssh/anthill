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

