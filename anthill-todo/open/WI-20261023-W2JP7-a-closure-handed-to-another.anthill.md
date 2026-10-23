## Attributes

- id: WI-20261023-W2JP7-a-closure-handed-to-another
- created: 2026-10-23T17:13:11Z

- status: Open
- status_agent: claude
- status_at: 2026-10-23T17:13:11Z

- acceptance: cargo-test

- tags: resolver

## Description

A closure handed to another relation through its head answers nothing, silently, pure or not. MEASURED 2026-10-23 (38a260a6, the same on 083cb6b8): `operation applyThunk[Rho](f: () -> String @ {Rho}) -> String effects {Rho} = f()`, `operation pureThunk() -> () -> String = lambda () -> "x"`, `rule cc(?f, ?r) :- applyThunk(?f, ?r)`, `rule viaPure(?r) :- pureThunk(?f), cc(?f, ?r)` answers NO SOLUTIONS, and `rule viaLambda(?r) :- cc(lambda () -> "x", ?r)` too; in one clause `pureThunk(?f), applyThunk(?f, ?r)` answers "x". `not(viaPure("x"))` would hold. Traced so far: `cc`'s goal finds its one candidate (`query_view` n = 1) and its body's `applyThunk` hook is never reached, so the head match with the closure (an opaque `Value::Closure`, or the lambda occurrence) fails or drops the binding (`kb/resolve.rs` candidate opening, `body_rename`). The effectful case is refused at load since WI-20261013-R1W5A (38a260a6); this is the pure one. ACCEPTANCE: `viaPure(?r)` and `viaLambda(?r)` answer "x", definite; a negation over each is decided.

