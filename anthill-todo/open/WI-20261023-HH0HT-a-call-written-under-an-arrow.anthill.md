## Attributes

- id: WI-20261023-HH0HT-a-call-written-under-an-arrow
- created: 2026-10-23T17:58:48Z

- status: Open
- status_agent: user
- status_at: 2026-10-23T17:58:48Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-068

## Description

A CALL WRITTEN UNDER AN ARROW-TYPE TERM IN A RULE BODY IS EVALUATED BUT NOT TYPED, so neither of WI-20261013-R1W5A's load checks (the call typed as an operation body is, an effectful call refused by its row) reaches it. MEASURED 2026-10-23 (01424c91), over `operation plus1(n: Int64) -> Int64 = n + 1`: `rule pureUnder(?t) :- ?t <=> Int64 -> plus1(1)` answers `?t = arrow(Int64, 2)` — the call ran; `rule illTypedUnder(?t) :- ?t <=> Int64 -> plus1("a")` LOADS and faults at run time ("type mismatch: expected Int64, got Node and Int64"), leaving `arrow(Int64, plus1("a"))`, where `?t <=> plus1("a")` is refused at load ("type mismatch in plus1.n (op-arg): expected Int64, got String"). Over `operation stamp() -> String effects {Clock} = now()`, `rule underArrow(?t) :- ?t <=> Int64 -> stamp()` loads and is declined at run time (undecided, "it performs `anthill.prelude.Time.Clock`, and a rule body performs no effect"), where `?t <=> stamp()` and `?t <=> [stamp()]` are refused at load. TO DECIDE: whether a call in an arrow-type term is a value-slot call (068 §1.1 — typed and refused as the clause's other calls are) or the arrow term is a type whose calls are not evaluated. ACCEPTANCE (cargo-test, driven): the decided reading for `pureUnder`, `illTypedUnder` and `underArrow`, each row with its back-out; the `arrow-type term` rows of WI-618 (`?t <=> (Int64) -> Int64` loads) unchanged.

