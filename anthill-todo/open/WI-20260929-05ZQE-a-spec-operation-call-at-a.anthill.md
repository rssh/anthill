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

## Changes

### 2026-09-29T20:17:58Z — feedback — user

ADDENDUM from WI-20260929-WBHTM's /code-review. (1) A call-site BRACKET naming a provider at another binding runs it too: `CB provides Store[State = Buf[T = Int64, N = Bool]]`, `use(s: Buf[T = Int64, N = String]) = Store.peek[Store = CB](s)` loads and runs CB (51) on both builds — `check_selection_bindings` (typing/slots.rs) skips a goal with ZERO candidates, a fully concrete one included, so the pin is never held against the call's binding. (2) Since WBHTM the value-in-type spelling behaves as its typed twin: the one provider at `N = 3`, `use(s: Buf[T = Int64, N = 4]) = Store.peek(s)` runs it (31), where the WI-325 walk had refused it by reading the occurrence-carried binding abstract (the same reading refused correct effect-row calls, so it could not stay); the `let`-annotated spelling `let y: Buf[T = Int64, N = 4] = s; Store.peek(y)` ran it before WBHTM too. The ACCEPTANCE should cover the bracket route and the value-in-type spelling.

