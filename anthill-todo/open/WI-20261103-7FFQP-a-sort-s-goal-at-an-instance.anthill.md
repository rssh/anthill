## Attributes

- id: WI-20261103-7FFQP-a-sort-s-goal-at-an-instance
- created: 2026-11-03T12:06:04Z

- status: Open
- status_agent: claude
- status_at: 2026-11-03T12:06:04Z

- acceptance: cargo-test

- tags: proposal-062, typing

## Description

A SORT'S GOAL AT AN INSTANCE MADE AT AN OPERATION'S OWN TYPE PARAMETER IS OWED BY NOTHING, AND AN OPERATION'S PRECONDITION OVER A NAMED TYPE PARAMETER IS NEVER PROVABLE (proposal 062 follow-up, guardians measured.md C2). Measured on 8fd6a276, every program over

  enum TrustLevel { entity Public; entity Untrusted }
  enum Text { sort Trust = ?; requires is_entity_of(Trust, TrustLevel); entity text(raw: String) }
  operation mk[X](x: X) -> Text[X] = todo()
  operation mk0[X]() -> Text[X] = todo()

(1) THE BODY'S INSTANCE IS NOT OWED. `operation k[Y](y: Y) -> Unit = { let t = mk(y)  () }` loads, and so does `operation f() -> Unit = k(5)`, which makes a `Text[Int64]` inside `k`. In `k`'s body the goal at `Y` is not decided (a rigid is not concrete, proposal 062 Readiness), and nothing carries it to `k`'s callers: only an instance in `k`'s SIGNATURE is held at each call (`k[Y](y: Y) -> Text[Y]` refuses `k(5)`). The obligation belongs to the caller that supplies `Y` (062: "the obligation belongs to the caller"), so it must become `k`'s: answered by `k`'s own `requires` or refused at `k`, as the value-precondition route already does for a wrapper over the `?l` form — `operation k(t: Text[Trust = ?l]) -> Unit requires is_entity_of(?l, TrustLevel)` with `operation w[Z](t: Text[Z]) -> Unit = k(t)` is refused at `w`: "expected precondition `is_entity_of(?Z, TrustLevel)` declared here or provable for every instantiation".

(2) THE ROUTE (1) NEEDS DOES NOT WORK FOR A NAMED TYPE PARAMETER. `operation k[Y]() -> Unit requires is_entity_of(Y, TrustLevel) = ()` is refused at EVERY call, the holding ones included: `k[Y = Public]()`, `k[Y = TrustLevel]()`, and `k[Y](t: Text[Y]) … ` called with `mk0[X = Public]()`, each "expected precondition `is_entity_of(Y, TrustLevel)` provable at the call site, got unsatisfied precondition" — `Y` printed, and so read, unsubstituted. The `?l` form substitutes: `k(t: Text[Trust = ?l]) requires is_entity_of(?l, TrustLevel)` loads at `mk0[X = Public]()` and is refused at a `Text[Int64]` ("`is_entity_of(Int64, TrustLevel)`").

(3) FOUND, AND A READING TO SETTLE: C2's own control no longer loads. docs/measurements/guardians/d2c_callsite.anthill: `send(body: Text[L = ?l]) -> Unit requires flows_to(?l, Public)` over `fact flows_to(Public, Public)` refuses `ok() = send(banner())` (banner: `-> Text[L = Public]`) with "`flows_to(Public[], Public)` … unsatisfied": `?l` is bound to the TYPE `Public` (written as data `Public[]`, kernel-language §4.4) and the clause's and the fact's `Public` are the INSTANCE. measured.md C2 still says the control loads. A sort's goal reads the same way (§5.2: its facts are written over types, `fact flows_to(Untrusted[], Public[])`); whether a precondition over a type-level variable is to be written so too, or a type-level variable's binding read otherwise, is for the user.

ACCEPTANCE: (2) `k[Y = Public]()` and `k(mk0[X = Public]())` load under `requires is_entity_of(Y, TrustLevel)`, `k[Y = Int64]()` is refused naming `is_entity_of(Int64, TrustLevel)`; (1) `k[Y](y: Y) = { mk(y) … }` is refused at `k` unless `k`'s `requires` states the goal at `Y`, and with it `k(5)` is refused and `k(TrustLevel.Public)` loads — driven by a row that RUNS the loading program; (3) decided with the user, d2c and measured.md C2 brought in line. Controls: proposal 062's rows (wi_t70a2_sort_goal_test), the `?l` rows above, guardians green.

## Changes

### 2026-11-03T12:13:12Z — feedback — claude

(3) DECIDED with the user (2026-11-03) and DONE: a type-level variable holds a type, so the facts and the clause it is checked against are written over types — `fact flows_to(Public[], Public[])`, `requires flows_to(?l, Public[])` — as a sort's goal's are (kernel-language §4.4, §5.2); no new rule matches a type against an entity's value. docs/measurements/guardians/d2c_callsite.anthill is rewritten so (its body-less operations given `= todo()` / `= ()`): `leak()` refused with `flows_to(Untrusted[], Public[])`, `ok()` loads; measured.md C2 says so. Measured beside it: `type_value[Public]()` is no spelling of the type in a fact or a precondition — refused there, "call-site type arguments `type_value[…](…)` are not supported here" (a call written in a fact is a pattern and is not run); `Public[]` is. What remains of this ticket is (1) and (2).

