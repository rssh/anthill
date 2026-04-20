//! Integration tests for M3 of the expression evaluator (WI-044).
//!
//! Covers: standard-library builtins (arithmetic, comparison, Bool, String)
//! wired into the interpreter via `eval::builtins::register_standard_builtins`
//! and driven from anthill operation bodies.

mod common;

use anthill_core::eval::Value;

use common::interp_for;

fn expect_int(v: Value) -> i64 {
    v.as_int().unwrap_or_else(|| panic!("expected Int, got {v:?}"))
}

fn expect_bool(v: Value) -> bool {
    v.as_bool().unwrap_or_else(|| panic!("expected Bool, got {v:?}"))
}

#[test]
fn m3_arithmetic_via_infix() {
    let src = r#"
namespace test.m3_arith
  operation main() -> Int = 2 + 3 * 4
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_int(interp.call("test.m3_arith.main", &[]).unwrap()), 14);
}

#[test]
fn m3_arithmetic_nested() {
    let src = r#"
namespace test.m3_nested
  operation double(n: Int) -> Int = n + n
  operation main() -> Int = double(5) * 2 - 1
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_int(interp.call("test.m3_nested.main", &[]).unwrap()), 19);
}

#[test]
fn m3_comparison_gt() {
    let src = r#"
namespace test.m3_cmp
  import anthill.prelude.Ordered.{gt}
  operation main() -> Bool = gt(7, 3)
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_bool(interp.call("test.m3_cmp.main", &[]).unwrap()), true);
}

#[test]
fn m3_comparison_via_infix() {
    let src = r#"
namespace test.m3_lt
  operation main() -> Bool = 1 < 2
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_bool(interp.call("test.m3_lt.main", &[]).unwrap()), true);
}

#[test]
fn m3_if_with_comparison() {
    let src = r#"
namespace test.m3_if_cmp
  operation max_of(a: Int, b: Int) -> Int =
    if a < b then b else a
  operation main() -> Int = max_of(4, 7)
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_int(interp.call("test.m3_if_cmp.main", &[]).unwrap()), 7);
}

#[test]
fn m3_bool_and_or_not() {
    let src = r#"
namespace test.m3_bool
  import anthill.prelude.Bool.{and, or, not}
  operation main() -> Bool = and(or(true, false), not(false))
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_bool(interp.call("test.m3_bool.main", &[]).unwrap()), true);
}

#[test]
fn m3_int_neg_abs() {
    let src = r#"
namespace test.m3_neg_abs
  import anthill.prelude.Int.{neg, abs}
  operation main() -> Int = abs(neg(42))
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_int(interp.call("test.m3_neg_abs.main", &[]).unwrap()), 42);
}

#[test]
fn m3_int_mod() {
    let src = r#"
namespace test.m3_mod
  import anthill.prelude.Int.{mod}
  operation main() -> Int = mod(17, 5)
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_int(interp.call("test.m3_mod.main", &[]).unwrap()), 2);
}

#[test]
fn m3_eq_on_ints() {
    let src = r#"
namespace test.m3_eq
  operation main() -> Bool = 3 = 3
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_bool(interp.call("test.m3_eq.main", &[]).unwrap()), true);
}

#[test]
fn m3_non_tail_recursion_accumulates_frames() {
    // Non-tail recursion: `sumUntil(n-1) + 1` wraps the recursive call in
    // `add _ 1`, so each level leaves an ApplyArgs-waiting frame on the
    // stack. TCO eliminates the intermediate dispatch frames but not the
    // pending-add frames — expected O(n) stack, same as any CEK machine.
    //
    // With cap=16 and n=100, the stack should overflow. With cap=200,
    // same program succeeds and returns n.
    let src = r#"
namespace test.m3_nontail
  import anthill.prelude.Ordered.{gt}
  operation sumUntil(n: Int) -> Int =
    if gt(n, 0) then sumUntil(n - 1) + 1 else 0
  operation main(n: Int) -> Int = sumUntil(n)
end
"#;

    // Small cap trips the DepthExceeded: non-tail recursion genuinely
    // needs ~n frames.
    let mut interp = common::interp_for(src);
    interp.set_stack_depth_cap(16);
    let err = interp.call("test.m3_nontail.main", &[Value::Int(100)]).unwrap_err();
    assert!(
        matches!(err, anthill_core::eval::EvalError::DepthExceeded { .. }),
        "expected DepthExceeded with tight cap; got {err:?}",
    );

    // With a generous cap the same program runs — confirming the limit is
    // memory, not a fundamental runtime flaw.
    let mut interp = common::interp_for(src);
    interp.set_stack_depth_cap(1000);
    let result = interp.call("test.m3_nontail.main", &[Value::Int(100)]).expect("call main");
    assert_eq!(expect_int(result), 100);
}

#[test]
fn m3_int_division() {
    // `/` desugars to `div`. Int import brings `Int.div` into scope as a
    // truncated integer division. Verifies `7 / 2 == 3` (truncation).
    let src = r#"
namespace test.m3_div
  import anthill.prelude.Int.{div}
  operation main() -> Int = 7 / 2
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_div.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 3);
}

#[test]
fn m3_int_division_by_zero() {
    let src = r#"
namespace test.m3_div0
  import anthill.prelude.Int.{div}
  operation main() -> Int = 10 / 0
end
"#;
    let mut interp = interp_for(src);
    let err = interp.call("test.m3_div0.main", &[]).unwrap_err();
    assert!(
        matches!(err, anthill_core::eval::EvalError::DivisionByZero { .. }),
        "expected DivisionByZero, got {err:?}",
    );
}

fn expect_float(v: Value) -> f64 {
    match v {
        Value::Float(f) => f,
        other => panic!("expected Float, got {other:?}"),
    }
}

#[test]
fn m3_float_arithmetic() {
    // `Numeric.add/sub/mul` dispatch on arg variants: Float/Float → Float.
    let src = r#"
namespace test.m3_float_arith
  operation main() -> Float = 1.5 + 2.25 * 2.0
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_float_arith.main", &[]).expect("call main");
    let got = expect_float(result);
    assert!((got - 6.0).abs() < 1e-9, "expected ~6.0, got {got}");
}

#[test]
fn m3_float_division() {
    let src = r#"
namespace test.m3_float_div
  import anthill.prelude.Float.{div}
  operation main() -> Float = 10.0 / 4.0
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_float_div.main", &[]).expect("call main");
    assert!((expect_float(result) - 2.5).abs() < 1e-9);
}

#[test]
fn m3_float_nan_detection() {
    // IEEE: `0.0 / 0.0 = NaN`, and `NaN != NaN` — so users detect NaN
    // via `isNaN`, not equality. `1.0 / 0.0 = +Infinity`, detected via
    // `isInfinite`. `isFinite` is true only for real-number values.
    let src = r#"
namespace test.m3_float_nan
  import anthill.prelude.Float.{div, isNaN, isInfinite, isFinite}

  operation nan_of_zero_over_zero() -> Bool = isNaN(0.0 / 0.0)
  operation inf_of_one_over_zero() -> Bool = isInfinite(1.0 / 0.0)
  operation finite_of_sum() -> Bool = isFinite(1.5 + 2.25)
  operation main() -> Bool =
    and(and(nan_of_zero_over_zero(), inf_of_one_over_zero()), finite_of_sum())
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_float_nan.main", &[]).expect("call main");
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn m3_float_division_by_zero_is_infinity() {
    // Float.div is IEEE-total: 1.0 / 0.0 = +Infinity, not an error. This
    // is the reason Float doesn't need the Error[DivisionByZero] effect
    // that Int.div carries.
    let src = r#"
namespace test.m3_float_div0
  import anthill.prelude.Float.{div}
  operation main() -> Float = 1.0 / 0.0
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_float_div0.main", &[]).expect("call main");
    assert!(expect_float(result).is_infinite(), "expected infinity");
}

#[test]
fn m3_float_addition_loses_precision_at_scale() {
    // IEEE 754 f64 has 52 mantissa bits plus the implicit leading one, so
    // numbers past ~2^53 can't represent `+1` as a distinct value. Here
    // 1e20 + 1.0 == 1e20 — the `+1` is rounded away. The grammar's
    // float_literal regex `/-?[0-9]+\.[0-9]+/` has no scientific notation,
    // so the constant is written out in full.
    let src = r#"
namespace test.m3_float_precision
  operation main() -> Bool =
    let x = 100000000000000000000.0
    x + 1.0 = x
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_float_precision.main", &[]).expect("call main");
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn m3_bigint_arithmetic() {
    // BigInt literals parse as `Literal::BigInt` (when they exceed i64);
    // the evaluator unboxes them into `Value::BigInt`. Arithmetic uses
    // num_bigint — no overflow, arbitrary precision.
    let src = r#"
namespace test.m3_bigint
  import anthill.prelude.{BigInt}
  operation main() -> BigInt =
    100000000000000000000 + 100000000000000000000
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_bigint.main", &[]).expect("call main");
    match result {
        Value::BigInt(n) => {
            assert_eq!(n.to_string(), "200000000000000000000");
        }
        other => panic!("expected BigInt, got {other:?}"),
    }
}

#[test]
fn m3_bigint_comparison() {
    let src = r#"
namespace test.m3_bigint_cmp
  import anthill.prelude.{BigInt}
  import anthill.prelude.Ordered.{gt}
  operation main() -> Bool =
    gt(200000000000000000000, 100000000000000000000)
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_bigint_cmp.main", &[]).expect("call main");
    assert_eq!(result.as_bool(), Some(true));
}

#[test]
fn m3_bigint_to_int_fits() {
    // Value that fits in i64 round-trips via to_int → Option.some.
    let src = r#"
namespace test.m3_bigint_to_int
  import anthill.prelude.{BigInt, Option, Int}
  import anthill.prelude.BigInt.{to_bigint, to_int}

  operation main() -> Int =
    match to_int(to_bigint(42))
      case some(x) -> x
      case none() -> 0
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_bigint_to_int.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 42);
}

#[test]
fn m3_int_to_float_and_bigint_to_float() {
    // Int.to_float is exact for small values; BigInt.to_float rounds to
    // nearest representable double. 1e20 fits in Float as 1.0e20.
    let src = r#"
namespace test.m3_bigint_to_float
  import anthill.prelude.BigInt.{to_float, to_bigint}

  operation main() -> Float =
    to_float(to_bigint(42)) + to_float(100000000000000000000)
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_bigint_to_float.main", &[]).expect("call main");
    // 42 + 1e20 ≈ 1e20 (the 42 is below mantissa precision); match floats
    // are approximate — assert it's at least 1e20 in magnitude.
    let f = expect_float(result);
    assert!(f >= 1.0e20, "expected ≥ 1e20, got {f}");
}

#[test]
fn m3_int_add_overflow_errors() {
    // Int arithmetic is exact — unlike Float, there's no large x where
    // x + 1 == x. Instead, the interesting edge case is overflow: i64::MAX
    // + 1 can't fit. We use checked_add, so this surfaces as
    // EvalError::Overflow rather than silently wrapping to i64::MIN. The
    // test drives via a Rust-side arg rather than a source literal, since
    // the Int literal grammar handles signed i64 but we want to be exact
    // about the boundary.
    let src = r#"
namespace test.m3_int_overflow
  operation inc(n: Int) -> Int = n + 1
  operation main() -> Int = inc(9223372036854775807)
end
"#;
    let mut interp = interp_for(src);
    let err = interp.call("test.m3_int_overflow.main", &[]).unwrap_err();
    match err {
        anthill_core::eval::EvalError::Overflow { op } => assert_eq!(op, "Numeric.add"),
        other => panic!("expected Overflow, got {other:?}"),
    }
}

#[test]
fn m3_float_comparison_and_max() {
    let src = r#"
namespace test.m3_float_cmp
  import anthill.prelude.Ordered.{max}
  operation main() -> Float = max(1.5, 2.75)
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_float_cmp.main", &[]).expect("call main");
    assert!((expect_float(result) - 2.75).abs() < 1e-9);
}

#[test]
fn m3_operator_precedence() {
    // `x + y * z + w` should parse as `(x + (y * z)) + w`. For x=1 y=2 z=3 w=4
    // the correct value is 1 + 6 + 4 = 11. Incorrect groupings give: 21
    // ((x+y)*(z+w)), 15 (x+y*(z+w)), 13 ((x+y)*z+w). Any of those would be
    // flagged by this assertion.
    let src = r#"
namespace test.m3_prec
  operation compute(x: Int, y: Int, z: Int, w: Int) -> Int =
    x + y * z + w
  operation main() -> Int = compute(1, 2, 3, 4)
end
"#;
    let mut interp = interp_for(src);
    let result = interp.call("test.m3_prec.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 11);
}

#[test]
fn m3_tco_10000_tail_calls() {
    // Classic tail-recursive countdown. Under TCO, the recursive call
    // replaces the current frame on dispatch, so activation-stack depth
    // stays at 1 regardless of N. With a cap of 16 we can still run 10000
    // iterations; if TCO were broken, push-per-call would overflow at
    // ~depth 16.
    let src = r#"
namespace test.m3_tco
  import anthill.prelude.Ordered.{gt}
  operation loop(n: Int) -> Int =
    if gt(n, 0) then loop(n - 1) else 0
  operation main() -> Int = loop(10000)
end
"#;
    let mut interp = interp_for(src);
    interp.set_stack_depth_cap(16);
    let result = interp.call("test.m3_tco.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 0);
}

#[test]
fn m3_string_concat_and_length() {
    let src = r#"
namespace test.m3_string
  import anthill.prelude.String.{concat, length}
  operation greeting() -> String = concat("hi ", "there")
  operation main() -> Int = length(greeting())
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(expect_int(interp.call("test.m3_string.main", &[]).unwrap()), 8);
}
