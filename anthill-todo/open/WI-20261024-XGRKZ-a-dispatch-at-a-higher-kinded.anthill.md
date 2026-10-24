## Attributes

- id: WI-20261024-XGRKZ-a-dispatch-at-a-higher-kinded
- created: 2026-10-24T21:17:06Z

- status: Open
- status_agent: user
- status_at: 2026-10-24T21:17:06Z

- acceptance: cargo-test

- tags: typing

## Description

A DISPATCH AT A HIGHER-KINDED BINDING WRITTEN AS A BARE CONSTRUCTOR FINDS NO IMPL. Found during WI-20261024-DK83Q (user: file, 2026-10-24).
MEASURED (2026-10-24, on 05ee1554 and 2f9c0750 alike):

  sort Lift[C, F[T]]
    operation lift(c: C, x: F[T = Int64]) -> Int64
  end
  sort Car
    entity car(n: Int64)
    provides Lift[C = Self, F = Option]
    operation lift(c: Self, x: Option[T = Int64]) -> Int64 = 1
  end
  operation go() -> Int64 = Lift.lift(car(n: 1), some(1))

is refused, "Lift.lift.dispatch: expected matching impl for per-call bindings, got no impl matches", though `Car`'s member takes exactly the `F[T = Int64]` that `F = Option` makes. The ill-typed `Lift.lift(car(n: 1), 5)` and `some("s")` are refused by the same message, so nothing tells the two apart. On the carrier-parameter path the binding `F = Option` is ref-shaped and no carrier parameter, so `bind_spec_params_from_carrier_param` leaves it to the late pass (WI-383); where it is lost after that is not diagnosed. `wi_dk83q_identical_substitution_test::a_higher_kinded_binding_is_no_open_slot` pins only that the `5` stays refused.
ACCEPTANCE (cargo-test via rustland/scripts/test.sh): `go` runs, answering 1; `Lift.lift(car(n: 1), 5)` and `some("s")` refused naming the argument; the DK83Q row extended to the run.

