## Attributes

- id: WI-20261023-X5SB4-soundness-a-guarded-effect-on
- created: 2026-10-23T17:13:10Z

- status: Open
- status_agent: claude
- status_at: 2026-10-23T17:13:10Z

- acceptance: cargo-test

- tags: typing, effects

## Description

SOUNDNESS: a guarded effect on a program's own operation is dropped at a literal call that SATISFIES its guard, so an operation body that declares no such effect loads and performs it. MEASURED 2026-10-23 (38a260a6, the same on 083cb6b8): `sort Boom  entity boom(why: String)  end`, `operation safe(n: Int64) -> Int64 effects { Error[Boom] :- eq(n, 0) } = if n === 0 then Error.raise(boom("z")) else n`, `operation u0() -> Int64 = safe(0)` LOADS (no `Error` declared) and raises at run time; `operation uv(n: Int64) -> Int64 = safe(n)` is refused (the guard symbolic, kept), and the stdlib's `operation d0() -> Int64 = Int64.div(7, 0)` is refused, as it must be. `{ Clock :- eq(b, true) }` behaves the same: `operation userT() -> String = stampIf(true)` loads; `{ Clock :- eq(n, 1) }` at `stampIfN(1)` loads; and in a rule body `?s <=> stampIf(true)` loads where WI-20261013-R1W5A refuses an effectful call (its row comes back without the member), while `?s <=> stampIf(?b)` is refused. The stdlib's guard is written inside `Int64` and the program's at namespace level: the guard's `eq` may resolve to a different symbol (`Int64.eq` against `PartialEq.eq`), and `refute_guard`'s `eq ⇄ neq` swap then proves `neq(0, 0)` — NOT TRACED, a lead (`kb/typing/gamma.rs` `refute_guard`/`negate_goal`, `kb/typing/effects.rs` `guarded_atom_refuted`). ACCEPTANCE: `u0` refused naming `Error[T = Boom]`, `safe(1)` loads; `userT` refused, `stampIf(false)` loads; the rule-body `?s <=> stampIf(true)` refused by the effect check; controls `uv` refused and `Int64.div(7, 0)` refused before and after.

