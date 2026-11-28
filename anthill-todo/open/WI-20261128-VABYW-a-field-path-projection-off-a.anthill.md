## Attributes

- id: WI-20261128-VABYW-a-field-path-projection-off-a
- created: 2026-11-28T07:59:38Z

- status: Open
- status_agent: user
- status_at: 2026-11-28T07:59:38Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A FIELD-PATH PROJECTION OFF A RECEIVER AT ITS SORT'S OWN PARAMETERS IS REFUSED IN A BODY: beside `sort Coll { sort C = ?; sort Elem = ?; operation first(c: C) -> Elem }`, `sort Wrap { sort T = ?; requires Coll[C = T]; entity wrap(v: T); operation peek(w: Self) -> w.v.Elem = Coll.first(w.v) }` is refused at `peek.return` "no `requires` bound on 'Wrap' whose carrier is this abstract type parameter declares a member 'Elem'; cannot project 'Elem'", though `Coll[C = T]` declares `Elem` and its carrier is `T` — the same with `w: Wrap[T = T]`, with the clause written `Coll[C = T, Elem = ?]` or `Coll[C = T, Elem = Int64]`, and with any body (`todo()`); measured 2026-11-28, before and after WI-20261103-95S43. The body-less declaration reads it, and so does a bare `w: Wrap`, whose field type is the materialized slot `w.T`, keyed through the parameter it names (WI-1059, `projected_param_of_sort`). Cause, read off the code: under `Self` the field `v: T` resolves to the body's RIGID for `T`, and the abstract-receiver arm of `project_type_member` keys a receiver by its own variable (`subject_key_of`: `Var::Rigid(x)` is keyed `x`), not by the parameter the rigid stands for, so no `requires` entry — written at `Wrap.T`'s canonical variable — carries the key (WI-430's carrier precision). The bare form then meets a second refusal at the call: `Coll.first(w.v)` against `-> w.v.Elem` is refused "expected `Elem` as `requires Coll[C = Wrap.T]` leaves it: any type, the instance's own, got `Elem = w.v.Elem`" — and `w.v.Elem` is that instance's own `Elem`. WHAT: key a rigid receiver by the type parameter it rigidifies, so `w.v.Elem` under `w: Self` forms the neutral the bound lends, as under `w: Wrap`; and a call whose expected type is that neutral fixes the slot the clause leaves to the clause's own instance, not to another type. ACCEPTANCE: the program loads with `w: Self`, `w: Wrap[T = T]` and `w: Wrap`, and runs at a provider (`Wrap.peek(wrap(v: bag(x: 7)))` beside `Bag provides Coll[C = Self, Elem = Int64]` with `first(b: Self) -> Int64 = b.x` answers 7); `w.v.Nope` stays refused naming `Nope`; a bound on another parameter (`sort U = ?; requires Coll[C = U]`) still lends `T`'s field nothing (WI-430); full workspace green via rustland/scripts/test.sh.

