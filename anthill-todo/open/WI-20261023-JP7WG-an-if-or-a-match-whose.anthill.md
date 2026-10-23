## Attributes

- id: WI-20261023-JP7WG-an-if-or-a-match-whose
- created: 2026-10-23T17:58:41Z

- status: Open
- status_agent: user
- status_at: 2026-10-23T17:58:41Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

AN `if` OR A `match` WHOSE BRANCHES ARE LAMBDAS WITH UNANNOTATED BINDERS IS REFUSED: each lambda keeps an open parameter placeholder, and the two are not met at the join. MEASURED 2026-10-23 (01424c91), over `operation applyThunk(f: () -> Int64) -> Int64 = f()` and `operation applyOne(f: (Int64) -> Int64) -> Int64 = f(1)`: `operation q(b: Bool) -> Int64 = applyThunk(if b then lambda () -> 1 else lambda () -> 2)` is refused "type mismatch in if.rule (rule): expected ??param -> Int64, got ??param -> Int64 (these render alike but are not the same type — the difference is in a component this diagnostic does not print; please report it)"; its `match` twin (`match b case true -> lambda () -> 1 case false -> lambda () -> 2`) the same in `match.rule`; `applyOne(if b then lambda x -> x else lambda x -> 2)` "expected ??param -> ??param, got ??param -> Int64"; one lambda beside a typed function value (`else thunkOf()`, over `operation thunkOf() -> () -> Int64 = lambda () -> 3`) "expected ??param -> Int64, got () -> Int64" — so even `lambda ()` leaves its parameter open. The same through `let f = if b then … else …` and in a rule body (`?r <=> applyThunk(if true then lambda () -> 1 else lambda () -> 2)`). It loads with annotated binders (`lambda (x: Int64) -> x` against `lambda (y: Int64) -> 2`) and under `let f: () -> Int64 = if …`. ACCEPTANCE (cargo-test, driven): each refused program loads and answers (`q(true)` 1, `q(false)` 2; the `applyOne` row 1 and 2); CONTROL: branches whose types truly differ (`lambda () -> 1` against `lambda () -> "s"`) stay refused; the annotated twins answer as before.

