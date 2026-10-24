## Attributes

- id: WI-20261024-DK83Q-the-typer-reads-error-t
- created: 2026-10-24T17:57:09Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-24T21:16:30Z

- acceptance: cargo-test, scaland-sbt-test

- tags: effects

## Description

THE TYPER READS `Error[T = ?]` WRITTEN OUT AND THE BARE `Error` IT MEANS DIFFERENTLY. Found during WI-20261016-5CDN5 (proposal 071 stage (d)); the user decided there that `Error` IS `Error[T = ?]` (2026-10-24).
MEASURED (2026-10-24): `operation go() -> Int64 effects {Error[T = ?]} = 1` inside `Error.reify[T1 = Boom](lambda () -> go())` LOADS, its caller typed effect-free; the same thunk over `operation bare() -> Int64 effects Error = 0` is REFUSED ("the lambda argument declares `Error`, which the closed row does not admit"), at an inferred `T1` too. 027.4's measured table records `{Error[?]}` accepted by a `{Error[Boom], Rho}` callback slot.
WHY IT MATTERS: since stage (d) a raise carries its type, and what the host function of a row naming no payload raises carries the unknown type, caught only by a boundary whose pattern is `?`. A boundary at `Boom` that the typer lets discharge `Error[T = ?]` is one the run does not catch at: stage (d) therefore refuses a `@[host_implemented]` operation that writes `Error[T = ?]` out (LoadError::HostRaiseWithoutTypeValue, `open`). A bodied operation is safe either way — its raises are `Error.raise`'s, typed by the payload.
THE CHANGE: one reading of the two spellings in the typer — `Error[T = ?]` discharged where the bare `Error` is (by no boundary at a specific type; by a pattern at `?` once stage (e), WI-20261016-BDVYW, builds one) — and the load refusal of the written-out spelling on host operations then dropped or kept, to be decided with the user. The 027.4 table row and every row of the suite that reads `Error[?]` re-measured.
ACCEPTANCE (cargo-test via rustland/scripts/test.sh): the two programs above get one verdict; a back-out of the reconciliation fails a named row.

## Changes

### 2026-10-24T21:16:22Z — feedback — claude

Delivered 2026-10-24 (2f9c0750). A `?` alone at a slot that declares no default is that slot left out in both lowerings of a written type (`Loader::leaves_its_slot_as_it_is`, on the new `TypeExpr::Variable.fresh`), so `Error[T = ?]`, `Error[?]` and `Error` are one type in every position, an effect label included; `?_` is a named logical variable (user) and stays.

DECIDED WITH THE USER (2026-10-24): the one verdict is that `Error` raises at a type not known, which only a boundary whose pattern is `?` catches. Over `go() -> Int64 effects {Error}`, `Error.reify[T1 = Boom](lambda () -> go())` is ACCEPTED in a caller declaring `effects {Error}` and REFUSED in one declaring none ("undeclared effect: Error"): the bare label pairs with no `Error[Boom]` in the callback's slot row (`effects::bare_against_written`, asked by `slots::solve_slot_rows`, where the actual row is known) and passes into `Rho`, as `Error[Other]` did. The load refusal of a host operation writing `Error[T = ?]` out is dropped. Spec text approved by the user: §5.4 (a default `[T = List]` is refused as `[T = List[T = ?]]` is; the sugar's family example), §5.5 (`-Permission[?]` is the bare `-Permission`, the general denial), §8.7 (the verdict above).

MERGED, THE SPELLINGS SHOWED FOUR READERS of the bare one with a gap the `?` one did not have, each given the `?` spelling's verdict through `typing::leaves_a_slot_open` (defaulted and higher-kinded slots are not open; loader-safe): a carrier provision binding `B = Other` (`Rel.mix(c, 5)` loaded), an operation default `[T = List]`, a block's `provides Store[State = List]` (a family), and the type a call's result is expected at (`let c: Car = Mk.make[E = R]()`). Fixed with it: the host-raise rule refused `go[P](p: P) effects {Error[P]} requires TypeValue[T = P]` as raising `Error[T = ?]` and advised `?P`; the parse-tree Rust generator dropped an `Error[T = ?]` effect and the Scala emitter refused it.

/code-review (xhigh, 14 findings): fixed the defaulted slot read as open, the requirement-chain cache filled mid-load, a stale comment, the duplicated `isBareHole` in scaland; refuted by measurement the masking of unconstrained-parameter refusals; kept, with reasons, the per-call expansion, the load-only clause row, the description of a dropped `?`, the generator's other sorts.

ROWS: tests/include/wi_dk83q_identical_substitution_test.rs (11), each part's back-out measured alone and listed in its header; re-pointed wi_5cdn5, wi_cbrsw, wi_80zv8 (two), wi_gbh5f, wi_gjw9z, wi_zbwmc, codegen_test, scaland BootstrapTest. RUNS: rustland/scripts/test.sh 10809 passed, 0 failed; scripts/families.sh holds, also under ANTHILL_TEST_NODE_CARRIER=1; scaland sbt testFull 1 + 47 + 762 passed.

