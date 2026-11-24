## Attributes

- id: WI-20261024-XGRKZ-a-dispatch-at-a-higher-kinded
- created: 2026-10-24T21:17:06Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-24T04:07:41Z

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

## Changes

### 2026-11-24T04:07:13Z — feedback — user

DECIDED WITH THE USER (2026-11-23): the bare `5` of `Lift.lift(car(n: 1), 5)` is `some(5)`. At `F = Option` the slot `x: F[T = Int64]` is `Option[T = Int64]`, where the some-coercion (kernel-language, "`some`-coercion (WI-408)") wraps a bare `Int64`, and `Car.lift(car(n: 1), 5)` answers the same: one reading for the spec's call and the member's. The acceptance line "`Lift.lift(car(n: 1), 5)` ... refused naming the argument" is WITHDRAWN; a bare `Int64` is refused naming the argument where no coercion reaches, at `F = List` (`Lift.lift(crate(n: 1), 5)`: "lift.x (op-arg): expected List[T = Int64], got Int64").

### 2026-11-24T04:07:27Z — feedback — user

DELIVERED (closed with the user 2026-11-24) in b1ae8f25e. Acceptance met: `go` runs, answering 1 (`wi_dk83q` a_higher_kinded_binding_is_no_open_slot, extended to the run); `some("s")` refused naming the argument, "lift.x (op-arg): expected Option[T = Int64], got Option[T = String]"; the `5` as decided above. Three parts: the dispatch routes a provision filling the higher-kinded slot with a sort that provides nothing to the resolution at `C = Car` (kb/typing/apply.rs); `bind_spec_params_from_carrier_param` binds the slot's bare constructor before the arguments are typed, where the sort declares as many parameters (kb/typing/carrier.rs, `constructor_fits_slot`); the argument check fills the head (`fill_higher_kinded_heads`, kb/typing/unify.rs), a pair holding a callable included. Rows: wi_xgrkz_higher_kinded_dispatch_test (5), each of six back-outs measured. /code-review (high): 3 findings, 2 fixed (a List of lambdas loading at an Option slot once routed; the kind guard), 1 not needed. Full workspace 12666 / 0; families green. Left, not this ticket's: a provision binding the slot to a sort of another kind (`F = Int64`) loads — filed as WI-20261124-H31PJ.

