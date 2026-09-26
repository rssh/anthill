## Attributes

- id: WI-20260926-Y6ZCD-an-operation-body-call-to-a
- created: 2026-09-26T12:54:23Z

- status: Open
- status_agent: user
- status_at: 2026-09-26T12:54:23Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

AN OPERATION-BODY CALL TO A MULTI-PARAMETER SPEC OPERATION DISPATCHES ON ITS CARRIER PARAMETER ALONE, and runs a provision at bindings the call's other arguments contradict. Found closing WI-20260925-PRVA2 (c).

MEASURED (main after PRVA2). `Conv[A, B]` with `conv(a: A, b: B) -> Int64`; `sort W provides Conv[A = Leaf, B = Int64]`, `W.conv` answering 9. An operation body `Conv.conv(leaf(), "s")` LOADS and answers 9 — `W.conv` run with a `String` in its `Int64` parameter. With only `W provides Conv[A = Int64, B = Int64]`, `Conv.conv(3, "km")` answers 1 the same way. The RULE-BODY twins are refused at load since PRVA2 (c) — "no provision of `Conv` binds `A = Leaf, B = String`" (`NoProvisionAtCarriers`) — and a woven rule-body read asks the same provision question at run time (`provision_admits_carriers`).

So one call is refused in a rule body and dispatched to the wrong instance in an operation body. The operation-body dispatch keys on the spec's CARRIER parameter and never checks the call's other carrier arguments against the chosen provision's bindings.

PROPOSED: the operation-body dispatch asks the provision at ALL the call's carriers, as the rule-body guard does — one question for both bodies (`provision_admits_carriers`, or the dictionary resolver at the call's full types) — and refuses at load where no provision binds them: the operation-body twin of `NoProvisionAtCarriers`.

ACCEPTANCE: both measured calls refused at load, naming the carriers no provision binds; `Conv.conv(leaf(), 4)` (the binding `W` has) still answers 9; full workspace green via rustland/scripts/test.sh; scaland testFull.

