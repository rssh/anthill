## Attributes

- id: WI-20261109-5VM2G-a-bigint-division-by-a-known
- created: 2026-11-09T20:01:52Z

- status: Open
- status_agent: claude
- status_at: 2026-11-09T20:01:52Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A BIGINT DIVISION BY A KNOWN ZERO LOADS WITH NO EFFECT DECLARED: the guard of `BigInt.div` / `mod` / `rem` compares a `BigInt` divisor with the `Int64` literal `0`, and the load reads it as not zero. PROGRAM: `namespace p.dz  import anthill.prelude.{Int64, BigInt}  import anthill.prelude.BigInt.{to_bigint}  operation bz() -> BigInt = BigInt.div(to_bigint(7), to_bigint(0))  end` LOADS (measured on 356ce140 and on f894f841, the same), and at run time the host raises DivisionByZero from an operation that declares no effect. CONTROLS, each refused "expected declared: [], got undeclared effect: Error[T = DivisionByZero]": `Int64.div(7, 0)`, `Int64.div(7, Int64.sub(1, 1))` (a divisor written as a call), `operation ip(b: Int64) -> Int64 = Int64.div(7, b)` and `operation bp(b: BigInt) -> BigInt = BigInt.div(to_bigint(7), b)` (a parameter keeps the effect). So only a KNOWN BigInt zero is discharged. The guard is `effects { Error[DivisionByZero] :- PartialEq.eq(b, 0) }` (stdlib/anthill/prelude/bigint.anthill, the three division operations; their specs `Divisible.div` / `EuclideanDomain.mod` / `rem` in stdlib/anthill/prelude/division.anthill write `:- eq(b, 0)` over `T`). Written in a program, `PartialEq.eq(to_bigint(0), 0)` is refused at load ("type mismatch in eq.b (op-arg): expected BigInt, got Int64"); in a guard it is accepted, and the guard's discharge compares BigInt 0 with Int64 0, finds them apart and drops the effect. MEASURED TOO: spelling the guard `PartialEq.eq(b, to_bigint(0))` still lets `bz` load (so the discharge also reads the guard's own call `to_bigint(0)` as not equal to the divisor's value — check whether a call in a guard is evaluated before the comparison, or compared as data). TO DECIDE with the user: how a guard over a spec's `T` writes the carrier's zero (a literal `0` is an `Int64`; `Additive.zero()` is the carrier's), whether a guard is typed as a goal is (the ill-typed comparison refused at load), and whether a discharge may drop an effect on a comparison it could not evaluate. ACCEPTANCE: `bz` refused naming `Error[DivisionByZero]`, and `mod` / `rem` likewise; `BigInt.div(to_bigint(7), to_bigint(2))` with no effect declared still loads; the four controls keep their verdicts; full workspace green via rustland/scripts/test.sh.

