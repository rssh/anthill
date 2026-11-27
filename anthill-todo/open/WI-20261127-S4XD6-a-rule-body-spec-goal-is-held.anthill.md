## Attributes

- id: WI-20261127-S4XD6-a-rule-body-spec-goal-is-held
- created: 2026-11-27T05:09:13Z

- status: Open
- status_agent: user
- status_at: 2026-11-27T05:09:13Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A RULE-BODY SPEC GOAL IS HELD TO ITS CARRIER'S SORT, NOT TO THE APPLICATION, SO BESIDE A PROVIDER AT ANOTHER INSTANCE OF THE SAME SORT IT RUNS THAT PROVIDER. `sort Store2 { sort State = ?; operation peek2(s: State, t: State) -> Int64 }`, `CB` provides `Store2[State = Buf[T = String, N = Bool]]` (answers `s.v + 20`), `mky() -> Buf[T = Int64, N = Bool] = buf(v: 1)`: beside CB alone, `rule rr(?r) :- Store2.peek2(mky(), mky(), ?r)` LOADS and `rr(?r)` answers `?r = 21` — CB run on an Int64 buffer. The same call in an operation body (`operation oo() -> Int64 = Store2.peek2(mky(), mky())`) is refused at load: "requirement `Store2[State = Buf[T = Int64, N = Bool]]` cannot be supplied for call to `Store2.peek2`; `CB` provides `Store2` at `Buf`, but no such row answers at these bindings". MEASURED 2026-11-27 at 4b94c2ea8 (debug CLI, `anthill query`). With CA (`Buf[T = Int64, N = Bool]`, `s.v + 10`) beside CB the rule answers 11 in either declaration order, so a row that matches is found when there is one; the defect is the case where none does. A carrier of ANOTHER sort is refused in a rule body as it should be: beside `provides Store1[State = String]`, `rule rr(?r) :- Store1.peek1(5, ?r)` is refused "`Int64` provides no `Store1` … no call here can discharge it", and likewise an entity sort `P` beside a provider at `Q`. So the rule-body requirement check (kb/typing/rule_requirements.rs; its refusal names the "carrier `P`") reads the carrier's SORT and not its type arguments — the per-sort-not-per-application shape WI-20261126-QG6ZR removed for a witness provision. NOT YET TRACED: why dispatch at run time then takes CB rather than finding no row. Order-independent; no empty literal involved. FOUND while delivering WI-20260929-7XNSK (probing the rule-body route for its /code-review). ACCEPTANCE: beside CB alone the rule is refused at load, as the operation-body call is (no row answers `Store2` at `Buf[T = Int64, N = Bool]`); with CA beside CB it still loads and answers 11; the other-sort refusals stand; a row per case that resolves `rr(?r)` (or pins the refusal), with the back-out measured at its site; full workspace green via rustland/scripts/test.sh.

