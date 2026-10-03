## Attributes

- id: WI-20261003-GR5EN-regression-the-declaration
- created: 2026-10-03T12:31:47Z

- status: Open
- status_agent: user
- status_at: 2026-10-03T12:31:47Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

REGRESSION — THE DECLARATION RULE REFUSES A MEMBER WIDER THROUGH A PROVIDER INSIDE A TUPLE OR AN ARROW, WHICH THE TREE WI-20260929-0RP29'S EIGHTH REVIEW SAW RAN. `sort Describe { sort K = ?; operation tag(d: Describe) -> Int64 }`, `sort Box { sort T = ?; entity box(t: T); provides Describe[K = T]; operation tag(b: Box) -> Int64 = 41 }`, `sort Sp { sort T = ?; operation op(s: Sp, x: (a: Box[T = T], b: Int64)) -> Int64 }`, `sort Car { entity car(n: Int64); provides Sp[T = Int64]; operation op(c: Car, x: (a: Describe, b: Int64)) -> Int64 = Describe.tag(x.a) + 1 }`, `Sp.op(car(n: 1), (a: box(t: 5), b: 0))`: refused "'Car' provides 'Sp' but its own member 'op' does not fit 'Sp.op': parameter 2 (`x: (a: Describe, b: Int64)`) takes less than the spec's" on the ninth pass's tree (2ed85280), the tenth pass and its /simplify; RAN to 42 on the tree the eighth review saw and on the tree before the ticket (MEASURED). Likewise in an arrow's result: spec `op(s: Sp, f: (u: Int64) -> Box[T = T])`, member `op(c: Car, f: (u: Int64) -> Describe) -> Int64 = Describe.tag(f(1)) + 1`, `Sp.op(car(n: 1), lambda (u) -> box(t: u))` — refused "parameter 2 (`f: Int64 -> Describe`) takes less", ran to 42 before. The ninth review asked for regressions but probed this widening only at the top level, where it fits since the tenth pass (`x: Describe` behind `x: Box[T = T]`, part 108 of `wi_0rp29_review9_regressions_test`): that pass's `bind_along_provider_view` (typing/signature.rs) binds along a carrier's provision at the top and through same-sort applications only, ignoring variance. It is a second hand-written walk of the subtype relation beside `bind_member_vars_along`, which already descends into named-tuple fields and arrows with variance; the provider case needs a walk of its own because unification across two sorts answers `true` binding nothing (WI-344's cross-sort arm of `unify_parameterized_view`). FIX: add the provider-view arm to `bind_member_vars_along` (the carrier side chosen by its `flipped`), so every position it walks — a named tuple's fields, an arrow's parameter (contravariant) and result — binds through a provision, and delete `bind_along_provider_view`; or, deeper, make the cross-sort arm of `unify_parameterized_view` bind through the provider's view, so unification itself does. ACCEPTANCE: both programs run to 42; refused, as on every build today (MEASURED for the first): a member narrower through a provider (spec `x: (a: Describe, b: Int64)` behind member `x: (a: Box[T = Int64], b: Int64)`), and the provider in an arrow's PARAMETER the wrong way (spec `f: (u: Box[T = T]) -> Int64` behind member `f: (u: Describe) -> Int64`); part 108's rows pass; full workspace green via rustland/scripts/test.sh.

