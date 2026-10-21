## Attributes

- id: WI-20261021-7SR7J-check-override-refinement
- created: 2026-10-21T03:58:20Z

- status: Open
- status_agent: user
- status_at: 2026-10-21T03:58:20Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

`check_override_refinement` ADMITS AN OVERRIDE WHOSE EFFECT THE PROVISION-BOUND SPEC ROW DOES NOT COVER. `sort Box { effects Effect = ?; operation peek(b: Self) -> Int64 effects Effect }`, `sort MutBox { provides Modifiable[T = Self]; entity mb(fd: Int64); provides Box[Effect = {}]; operation peek(b: Self) -> Int64 effects Modify[b] = match b case mb(x) -> x }` LOADS (MEASURED 2026-10-20 on the WI-20260930-GJW9Z tree; the receiver written `b: MutBox` alike): at this provision the spec's row is `{}`, which covers no `Modify[b]`, and the effects leg ("effects must not widen") says nothing. The leg substitutes the provision's bindings into the spec row (`sigma_subst_type`) and refuses per atom — pinned for a `sort E = ?` bound to a LABEL sort (`wi347_override_refinement_test::a_sigma_bound_effect_row_is_compared`) — and does not, here, for an `effects E = ?` row parameter bound to a ROW; why is not investigated. This is not the leg's documented fail-open (a spec row still holding a parameter the provision leaves unbound, `provides Box`; an override atom that is itself parametric, `effects {EC}`), which stays. Since GJW9Z a call PINNED to the override is charged the override's own row, so it is precise either way; a call through an abstract receiver (`b: Box[Effect = {}]`) would be charged the spec's `{}` while `Modify[b]` runs (not measured). FOUND by WI-20260930-GJW9Z's /code-review follow-up. ACCEPTANCE: the program above is refused "effects must not widen" naming `Modify[T = b]`; the same override declaring `effects {}` loads (control); full workspace green via rustland/scripts/test.sh.

