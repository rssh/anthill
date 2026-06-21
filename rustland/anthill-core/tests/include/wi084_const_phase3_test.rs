//! WI-084 / proposal 039 — term-level named constants, **Phase 3** (value
//! source + per-symbol cache + eval hook).
//!
//! Phase 3 makes a const REFERENCE evaluate to its value: the eval hook in
//! `reduce_var` forces the const on first demand and memoizes it in
//! `Interpreter::const_cache`. The value source is either the folded anthill
//! body (run by the real evaluator under `step_cap`) or a registered host
//! reflect builtin. A `Forcing` sentinel turns a dependency cycle into a loud
//! error; a bodyless const with no builtin reports value-unavailable on demand.
//!
//! Covers the proposal's named Phase-3 checks:
//!   * bare `BROADCAST_CHANNEL` evaluates to `-1`           (`const_folds_to_its_body_value`)
//!   * `TWO_PI` folds via `PI`                              (`const_composition_folds`)
//!   * a cyclic pair errors                                 (`const_cycle_is_an_error`)
//!   * an over-budget body errors                           (`over_budget_const_body_errors`)
//!   * a host const with a registered builtin returns it    (`host_const_with_builtin_returns_value`)
//!   * a host const without one reports value-unavailable   (`host_const_without_builtin_is_unavailable`)
//!
//! NOT yet in scope (deferred): the static PURITY GATE (rejecting an effectful
//! const body, e.g. `Cell.new(0)`, at load) — tracked separately.

use anthill_core::eval::{EvalError, Value};

fn interp(src: &str) -> anthill_core::eval::Interpreter {
    crate::common::interp_for(src)
}

#[test]
fn const_folds_to_its_body_value() {
    // The load-bearing driver: a reference to `BROADCAST_CHANNEL` materializes
    // the folded `-1`.
    let mut i = interp(
        r#"
namespace test.wi084p3.basic
  import anthill.prelude.{Int64}
  const BROADCAST_CHANNEL: Int64 = -1
  operation go() -> Int64 = BROADCAST_CHANNEL
end
"#,
    );
    match i.call("test.wi084p3.basic.go", &[]) {
        Ok(Value::Int(-1)) => {}
        other => panic!("expected Int(-1) from a const reference, got {other:?}"),
    }
}

#[test]
fn const_composition_folds() {
    // `TWO_PI = 2.0 * PI` folds by forcing `PI` on demand (3.0 → 6.0). Exercises
    // the cache forcing one const from inside another's fold.
    let mut i = interp(
        r#"
namespace test.wi084p3.compose
  import anthill.prelude.{Float}
  const PI: Float = 3.0
  const TWO_PI: Float = 2.0 * PI
  operation go() -> Float = TWO_PI
end
"#,
    );
    match i.call("test.wi084p3.compose.go", &[]) {
        Ok(Value::Float(f)) => assert_eq!(f, 6.0, "2.0 * 3.0 should fold to 6.0"),
        other => panic!("expected Float(6.0) from a composed const, got {other:?}"),
    }
}

#[test]
fn const_cycle_is_an_error() {
    // `A = B; B = A`: forcing A forces B forces A (already Forcing) → ConstCycle.
    let mut i = interp(
        r#"
namespace test.wi084p3.cycle
  import anthill.prelude.{Int64}
  const A: Int64 = B
  const B: Int64 = A
  operation go() -> Int64 = A
end
"#,
    );
    match i.call("test.wi084p3.cycle.go", &[]) {
        Err(EvalError::ConstCycle { .. }) => {}
        other => panic!("expected ConstCycle for a self-dependent const pair, got {other:?}"),
    }
}

#[test]
fn over_budget_const_body_errors() {
    // A pure but non-terminating body folds under the shared `step_cap`, so it
    // surfaces as StepsExhausted rather than hanging the host.
    let mut i = interp(
        r#"
namespace test.wi084p3.budget
  import anthill.prelude.{Int64}
  operation forever() -> Int64 = forever()
  const LOOP: Int64 = forever()
  operation go() -> Int64 = LOOP
end
"#,
    );
    i.config_mut().step_cap = Some(10_000);
    match i.call("test.wi084p3.budget.go", &[]) {
        Err(EvalError::StepsExhausted { .. }) => {}
        other => panic!("expected StepsExhausted for an over-budget const fold, got {other:?}"),
    }
}

#[test]
fn let_local_shadows_const_at_eval() {
    // Eval-time precedence (the Phase-2 shadow test only checked typing): a
    // `let`-local named like a const must WIN at runtime — `reduce_var`'s
    // `find_local` fires before the const hook. Returns the local's 99, not the
    // const's 1.
    let mut i = interp(
        r#"
namespace test.wi084p3.shadow
  import anthill.prelude.{Int64}
  const N: Int64 = 1
  operation go() -> Int64 =
    let N = 99
    N
end
"#,
    );
    match i.call("test.wi084p3.shadow.go", &[]) {
        Ok(Value::Int(99)) => {}
        other => panic!("a let-local must shadow the const at eval (expected 99), got {other:?}"),
    }
}

#[test]
fn host_const_with_builtin_returns_value() {
    // A bodyless (host-supplied) const whose value comes from a registered
    // nullary reflect builtin.
    let mut i = interp(
        r#"
namespace test.wi084p3.host
  import anthill.prelude.{Int64}
  const CHANNEL_BROADCAST: Int64
  operation go() -> Int64 = CHANNEL_BROADCAST
end
"#,
    );
    i.register_builtin("test.wi084p3.host.CHANNEL_BROADCAST", |_interp, _args| {
        Ok(Value::Int(-1))
    })
    .expect("register host const builtin");
    match i.call("test.wi084p3.host.go", &[]) {
        Ok(Value::Int(-1)) => {}
        other => panic!("expected the host builtin's Int(-1), got {other:?}"),
    }
}

#[test]
fn host_const_without_builtin_is_unavailable() {
    // The same bodyless const type-checks (its declared type is known, so the
    // file loads), but with NO builtin registered its value is unavailable on
    // demand — a loud error, not a silent default.
    let mut i = interp(
        r#"
namespace test.wi084p3.unavail
  import anthill.prelude.{Int64}
  const CHANNEL_BROADCAST: Int64
  operation go() -> Int64 = CHANNEL_BROADCAST
end
"#,
    );
    match i.call("test.wi084p3.unavail.go", &[]) {
        Err(EvalError::ConstValueUnavailable { .. }) => {}
        other => panic!("expected ConstValueUnavailable for a bodyless const with no builtin, got {other:?}"),
    }
}
