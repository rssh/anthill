## Attributes

- id: WI-20261023-X5SB4-soundness-a-guarded-effect-on
- created: 2026-10-23T17:13:10Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-28T20:59:01Z

- acceptance: cargo-test

- tags: typing, effects

## Description

SOUNDNESS: a guarded effect on a program's own operation is dropped at a literal call that SATISFIES its guard, so an operation body that declares no such effect loads and performs it. MEASURED 2026-10-23 (38a260a6, the same on 083cb6b8): `sort Boom  entity boom(why: String)  end`, `operation safe(n: Int64) -> Int64 effects { Error[Boom] :- eq(n, 0) } = if n === 0 then Error.raise(boom("z")) else n`, `operation u0() -> Int64 = safe(0)` LOADS (no `Error` declared) and raises at run time; `operation uv(n: Int64) -> Int64 = safe(n)` is refused (the guard symbolic, kept), and the stdlib's `operation d0() -> Int64 = Int64.div(7, 0)` is refused, as it must be. `{ Clock :- eq(b, true) }` behaves the same: `operation userT() -> String = stampIf(true)` loads; `{ Clock :- eq(n, 1) }` at `stampIfN(1)` loads; and in a rule body `?s <=> stampIf(true)` loads where WI-20261013-R1W5A refuses an effectful call (its row comes back without the member), while `?s <=> stampIf(?b)` is refused. The stdlib's guard is written inside `Int64` and the program's at namespace level: the guard's `eq` may resolve to a different symbol (`Int64.eq` against `PartialEq.eq`), and `refute_guard`'s `eq ⇄ neq` swap then proves `neq(0, 0)` — NOT TRACED, a lead (`kb/typing/gamma.rs` `refute_guard`/`negate_goal`, `kb/typing/effects.rs` `guarded_atom_refuted`). ACCEPTANCE: `u0` refused naming `Error[T = Boom]`, `safe(1)` loads; `userT` refused, `stampIf(false)` loads; the rule-body `?s <=> stampIf(true)` refused by the effect check; controls `uv` refused and `Int64.div(7, 0)` refused before and after.

## Changes

### 2026-10-28T20:58:59Z — feedback — claude

Delivered with WI-20260930-AMYV4 (user approved the spec text, 2026-10-28). The ticket's programs do not import eq, so the guard named nothing and negation as failure refuted it at every ground call: AMYV4's mechanism, not Int64.eq against PartialEq.eq. With eq imported every operation-body row already held. A second defect, found on the way: a rule variable reached the guard's substitution as its raw De Bruijn index, which the resolver compares as a constant, so neq(?#0, true) was proved; rule r(?s, ?b) :- ?s <=> stampIf(?b) loaded with Clock dropped (also through ?c.stamp(?b) and an override filling a spec row parameter), and a rule-body call of an operation requiring eq(b, 0) was refused quoting eq(?#1, 0). guard_arg_term (typing/effects.rs) leaves such an argument out of both substitutions (build_call_guard_sigma, dispatched_impl_effects_of), so the guard is undecided. Rows: wi_x5sb4_guard_refutation_test.

