## Attributes

- id: WI-20260929-020TH-an-operation-level-requires
- created: 2026-09-29T20:17:31Z

- status: Open
- status_agent: user
- status_at: 2026-09-29T20:17:31Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

AN OPERATION-LEVEL `requires` OVER A TWO-HOP σ CHAIN IS LEFT UNFILLED, AND EVAL RUNS A PROVIDER AT ANOTHER BINDING. `sort User { sort S = ?; sort U = ?; operation mkS() -> Option[T = S] = none(); operation go13(o: Option[T = U], u: U, s: S) -> Int64 requires Store[State = S] = Store.peek(s) }`, the only provider `P1` at `Buf[T = Int64, N = String]` (answers `s.v + 30`), and `run(b: Buf[T = Int64, N = Bool]) = User.go13(User.mkS(), b, b)`: LOADS and runs P1 on an `N = Bool` buffer (31). The value-in-type spelling (`b: Buf[T = Int64, N = 3]`, provider at `N = 4`) runs the same way (31); two providers give a run-time tie instead of a load-time refusal. MEASURED before and after WI-20260929-WBHTM, typed and value-in-type alike. MECHANISM (from WBHTM's review): `mkS()` leaks `S` into `go13`'s `U`, so σ holds `S ↦ U ↦ …`; the op-scoped supply at the call does not refuse the unpinnable slot, the callee is entered without it, and its body's call is served by value-directed dispatch, which cannot see `N`. The sort-level twin of this chain is refused (or, value-carried, is WI-20260929-PFAGY's load-clean crash). FOUND by WI-20260929-WBHTM's /code-review (V11). ACCEPTANCE: the program refused at load naming `Store[State = Buf[T = Int64, N = Bool]]` as unsuppliable, in both spellings; full workspace green via rustland/scripts/test.sh.

