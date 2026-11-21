## Attributes

- id: WI-20261121-ZPZDY-a-lambda-whose-parameter-reads
- created: 2026-11-21T08:43:06Z

- status: Open
- status_agent: user
- status_at: 2026-11-21T08:43:06Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A LAMBDA WHOSE PARAMETER READS A SLOT NESTED IN A FIELD'S WRITTEN BINDING TAKES NO ARGUMENT AT ALL, WHERE AN OPERATION'S PARAMETER TAKES THE ONE THAT FITS: over `sort Box { sort T = ?; entity box(v: T) }` and `sort Hold { entity hold(f: Box[T = List[T = ?]]) }`, with `let h0 = hold(f: box(v: [1]))`, the operation `operation opn(h: Hold, k: h.f.T) -> Int64 = 42` called `opn(h0, h0.f.v)` runs to 42 and `opn(h0, [1])` is refused (`h0.f.T` is a list of an unknown element: `Hold` does not say which), but the lambda `let g = lambda (h: Hold, k: h.f.T) -> 42` refuses both — `g(h0, h0.f.v)` "type mismatch in g.k (op-arg): expected List[T = ?T], got List[T = ?T] (these render alike because `?T` is two different unknowns …)", `g(h0, [1])` "expected List[T = ?T], got List[T = Int64]" — and over `sort Hold2 { sort X = ?; entity hold2(f: Box[T = X]) }`, `lambda (h: Hold2[X = List], k: h.f.T)` refuses `g(h0, h0.f.v)` and `g(h0, [1])` alike where `h0 = hold2(f: box(v: [1]))` is a `Hold2[X = List[T = Int64]]` — measured on f7ed45c6 with the debug CLI, 2026-11-21; the plain `Hold` the same before WI-20261121-204T6. The lambda's own tuple reads `k: h.f.T` once, at its body's `h`, and the field read opens the nested slot to a pass-local rigid (`open_field_at_path`, `PathOpenings`), which the lambda's ARROW then carries as its parameter type: no argument has it. An operation reads `k: h.f.T` at the call, at the argument `h0` (`Receivers::Call`), and `h0.f.v` is read off the same path. The 204T6 rows that pin the lambda's refusal (`NESTED_SLOT_APPLIED` in `wi_204t6_lambda_sibling_projection_test`: `Hold2[X = List]`, `HoldL`, `WrapH[L = State]`, the chain `b: a.L`, `k: b.f.T`) are this. WHAT: measure whether the arrow should keep the dependent parameter `h.f.T` (read where the arrow is applied, at that application's arguments, as an arrow's own binders are, `ArrowBinders`) rather than its body-time reading. ACCEPTANCE: `g(h0, h0.f.v)` runs to 42 over `Hold`, as `opn(h0, h0.f.v)` does, and `g(h0, [1])` stays refused there, as `opn(h0, [1])` is; over `Hold2[X = List]` with `h0: Hold2[X = List[T = Int64]]`, `g(h0, [1])` runs; the 204T6 rows that pin `NESTED_SLOT_APPLIED` move to what the operation answers; full workspace green via rustland/scripts/test.sh.