## Attributes

- id: WI-20260929-05ZQE-a-spec-operation-call-at-a
- created: 2026-09-29T16:04:11Z

- status: Open
- status_agent: user
- status_at: 2026-09-29T16:04:11Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A SPEC-OPERATION CALL AT A TYPE NO PROVISION COVERS LOADS AND RUNS ANOTHER BINDING'S PROVIDER. With only `Carrier provides Store[State = Buf[T = Int64]]` (member `peek(s: Buf[T = Int64]) -> Int64 = s.v`): `Store.peek(buf(v: "x"))` loads and returns the String "x" from an Int64 operation; `go2(s: Buf[T = Bool]) = Store.peek(s)` loads and returns a Bool where Int64 is declared ("main returned non-Int64 value: Bool(true)"); the self-receiver shape `peek(s: Store, x: State)` with a `Buf[T = Bool]` argument does the same. Identical on the Sep 20 build and HEAD. FOUND by WI-20260924-F3FYJ's review (a side finding of verifier V4, and its gap sweep), PRE-EXISTING and unrelated to WI-348's dropped binding (every type here is ground). Where each gets through, from code reading: WI-883 counts `Buf` as an instance through the other binding's provision, and WI-325 then sees a concrete `State`; for the self-receiver, after NoCandidates WI-606 pins the call to the carrier's own `peek`. ACCEPTANCE: each call refused at load naming the binding no provision covers, the covered twin (`buf(v: 7)` / `Buf[T = Int64]`) loading and running; full workspace green via rustland/scripts/test.sh.

