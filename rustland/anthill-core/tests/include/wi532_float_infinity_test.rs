//! WI-532 — Float ±infinity / NaN as host-supplied term-level constants.
//!
//! anthill has no surface literal for IEEE ±Inf or NaN, so the stdlib exposes
//! them as bodyless `const infinity / negativeInfinity / nan: Float` in
//! `sort anthill.prelude.Float`. Each value comes from a registered host
//! builtin (eval/builtins.rs) via the WI-084 host-const value source
//! (`force_const` reads `self.builtins.get(&sym)` for a `SymbolKind::Const`).
//!
//! These tests load the REAL stdlib + the real `register_standard_builtins`,
//! so they pin the whole path: const declaration → resolution/typing →
//! force_const → registered builtin → `Value::Float`.

use anthill_core::eval::Value;

fn interp(src: &str) -> anthill_core::eval::Interpreter {
    crate::common::interp_for(src)
}

#[test]
fn infinity_evaluates_to_positive_infinity() {
    // The headline driver: a bare reference to the stdlib const materializes
    // IEEE +∞ — the value anthill could not previously write.
    let mut i = interp(
        r#"
namespace test.wi532.pos
  import anthill.prelude.Float.{infinity}
  operation go() -> Float = infinity
end
"#,
    );
    match i.call("test.wi532.pos.go", &[]) {
        Ok(Value::Float(f)) => assert!(f.is_infinite() && f > 0.0, "expected +∞, got {f}"),
        other => panic!("expected Float(+∞) from the infinity const, got {other:?}"),
    }
}

#[test]
fn negative_infinity_and_nan_evaluate() {
    // The two siblings: -∞ is a finite-comparable lower bound; NaN is the
    // non-value (it is not even equal to itself, hence the dedicated predicate).
    let mut i = interp(
        r#"
namespace test.wi532.siblings
  import anthill.prelude.Float.{negativeInfinity, nan}
  operation neg() -> Float = negativeInfinity
  operation bad() -> Float = nan
end
"#,
    );
    match i.call("test.wi532.siblings.neg", &[]) {
        Ok(Value::Float(f)) => assert!(f.is_infinite() && f < 0.0, "expected -∞, got {f}"),
        other => panic!("expected Float(-∞), got {other:?}"),
    }
    match i.call("test.wi532.siblings.bad", &[]) {
        Ok(Value::Float(f)) => assert!(f.is_nan(), "expected NaN, got {f}"),
        other => panic!("expected Float(NaN), got {other:?}"),
    }
}

#[test]
fn predicates_classify_the_constants() {
    // The constants flow through the existing IEEE predicates exactly as the
    // computed values do: +∞ is infinite and not finite; NaN is NaN.
    let mut i = interp(
        r#"
namespace test.wi532.classify
  import anthill.prelude.Float.{infinity, nan, isInfinite, isFinite, isNaN}
  operation inf_is_infinite() -> Bool = isInfinite(infinity)
  operation inf_is_not_finite() -> Bool = isFinite(infinity)
  operation nan_is_nan() -> Bool = isNaN(nan)
end
"#,
    );
    assert_eq!(
        i.call("test.wi532.classify.inf_is_infinite", &[]).expect("call").as_bool(),
        Some(true),
        "isInfinite(infinity) must be true",
    );
    assert_eq!(
        i.call("test.wi532.classify.inf_is_not_finite", &[]).expect("call").as_bool(),
        Some(false),
        "isFinite(infinity) must be false",
    );
    assert_eq!(
        i.call("test.wi532.classify.nan_is_nan", &[]).expect("call").as_bool(),
        Some(true),
        "isNaN(nan) must be true",
    );
}

#[test]
fn user_const_referencing_infinity_folds() {
    // The motor-sentinel driver shape (WI-084 §Phase-4): a user const whose
    // body IS the stdlib `infinity`. Forcing it forces the host const through
    // the cache, so a velocity-mode sentinel like
    // `const VELOCITY_MODE_POSITION: Float = infinity` folds to +∞.
    let mut i = interp(
        r#"
namespace test.wi532.driver
  import anthill.prelude.Float.{infinity}
  const VELOCITY_MODE_POSITION: Float = infinity
  operation go() -> Float = VELOCITY_MODE_POSITION
end
"#,
    );
    match i.call("test.wi532.driver.go", &[]) {
        Ok(Value::Float(f)) => assert!(f.is_infinite() && f > 0.0, "expected +∞, got {f}"),
        other => panic!("expected a const-of-a-const to fold to +∞, got {other:?}"),
    }
}
