## Attributes

- id: WI-20261024-DK83Q-the-typer-reads-error-t
- created: 2026-10-24T17:57:09Z

- status: Open
- status_agent: user
- status_at: 2026-10-24T17:57:09Z

- acceptance: cargo-test, scaland-sbt-test

- tags: effects

## Description

THE TYPER READS `Error[T = ?]` WRITTEN OUT AND THE BARE `Error` IT MEANS DIFFERENTLY. Found during WI-20261016-5CDN5 (proposal 071 stage (d)); the user decided there that `Error` IS `Error[T = ?]` (2026-10-24).
MEASURED (2026-10-24): `operation go() -> Int64 effects {Error[T = ?]} = 1` inside `Error.reify[T1 = Boom](lambda () -> go())` LOADS, its caller typed effect-free; the same thunk over `operation bare() -> Int64 effects Error = 0` is REFUSED ("the lambda argument declares `Error`, which the closed row does not admit"), at an inferred `T1` too. 027.4's measured table records `{Error[?]}` accepted by a `{Error[Boom], Rho}` callback slot.
WHY IT MATTERS: since stage (d) a raise carries its type, and what the host function of a row naming no payload raises carries the unknown type, caught only by a boundary whose pattern is `?`. A boundary at `Boom` that the typer lets discharge `Error[T = ?]` is one the run does not catch at: stage (d) therefore refuses a `@[host_implemented]` operation that writes `Error[T = ?]` out (LoadError::HostRaiseWithoutTypeValue, `open`). A bodied operation is safe either way — its raises are `Error.raise`'s, typed by the payload.
THE CHANGE: one reading of the two spellings in the typer — `Error[T = ?]` discharged where the bare `Error` is (by no boundary at a specific type; by a pattern at `?` once stage (e), WI-20261016-BDVYW, builds one) — and the load refusal of the written-out spelling on host operations then dropped or kept, to be decided with the user. The 027.4 table row and every row of the suite that reads `Error[?]` re-measured.
ACCEPTANCE (cargo-test via rustland/scripts/test.sh): the two programs above get one verdict; a back-out of the reconciliation fails a named row.

