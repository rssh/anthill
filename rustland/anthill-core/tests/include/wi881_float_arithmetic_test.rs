//! WI-881 — `anthill.prelude.Float`'s arithmetic is BACKED, and the four equations in
//! `float.anthill` are settled one by one as definition-or-specification.
//!
//! THE PRE-FIX MEASUREMENT, reproduced before the change: the sort declared 32
//! operations and 8 ran. `abs(-1.5)`, `neg(1.5)`, `recip(4.0)`, `sqrt(4.0)`,
//! `floor(1.7)`, `pi()`, `tau()`, `e()` — every one died `OperationBodyMissing {
//! anthill.prelude.Float.<op> }` on a program that LOADED CLEAN. `float.anthill`'s
//! header comment argues WHY that was invisible; this file is what drives it.
//!
//! THE FOUR EQUATIONS are each settled here by a COUNTEREXAMPLE rather than by
//! argument, which is what the tests below are for:
//! [`neg_law_over_sub_is_false`] and [`abs_is_not_definable_by_comparison`] show the
//! two that are not definitions (the SIGN OF ZERO — IEEE separates `+0.0` from
//! `-0.0` while every comparison reads them equal);
//! [`the_constants_answer_in_both_nullary_call_forms`] and
//! [`a_bare_nullary_simp_head_never_fires`] show the reach limit that settled `tau`;
//! [`the_simp_definition_fires_away_from_its_sort`] is what licenses `recip` being
//! backed by its equation ALONE, with no host mapping.
//!
//! Reference: `stdlib/anthill/prelude/float.anthill`,
//! `rustland/anthill-stl/anthill/float.anthill` (`operation_map`), WI-876 (the
//! channel and its arity check), WI-880 (the host-carrier exemption that hid this),
//! WI-818 (a rule is not backing).

use anthill_core::eval::Value;

/// One driver sort, one zero-arg entry per operation under test. Everything is
/// `Float`-qualified so the call names the carrier's own member rather than an
/// inherited `Numeric` one.
const DRIVER: &str = r#"
namespace wi881.float
  import anthill.prelude.{Float, Int64, Bool}

  sort D
    import anthill.prelude.{Float, Int64, Bool}
    import anthill.prelude.Float.{nan}

    -- sign family
    operation dAbs(n: Int64) -> Float = Float.abs(0.0 - 1.5)
    operation dNeg(n: Int64) -> Float = Float.neg(1.5)

    -- rounding family (Float -> Int64, partial)
    operation dFloor(n: Int64) -> Int64 = Float.floor(1.7)
    operation dCeil(n: Int64) -> Int64 = Float.ceil(1.2)
    operation dRound(n: Int64) -> Int64 = Float.round(1.5)
    operation dFloorNaN(n: Int64) -> Int64 = Float.floor(nan)
    operation dFloorHuge(n: Int64) -> Int64 = Float.floor(Float.pow(10.0, 300.0))

    -- power / root family
    operation dSqrt(n: Int64) -> Float = Float.sqrt(4.0)
    operation dHypot(n: Int64) -> Float = Float.hypot(3.0, 4.0)
    operation dFmod(n: Int64) -> Float = Float.fmod(7.5, 2.0)
    operation dPow(n: Int64) -> Float = Float.pow(2.0, 10.0)

    -- trig family
    operation dSin(n: Int64) -> Float = Float.sin(0.0)
    operation dCos(n: Int64) -> Float = Float.cos(0.0)
    operation dTan(n: Int64) -> Float = Float.tan(0.0)
    operation dAsin(n: Int64) -> Float = Float.asin(0.0)
    operation dAcos(n: Int64) -> Float = Float.acos(1.0)
    operation dAtan(n: Int64) -> Float = Float.atan(0.0)
    operation dAtan2(n: Int64) -> Float = Float.atan2(0.0, 1.0)

    -- exp / log family
    operation dExp(n: Int64) -> Float = Float.exp(0.0)
    operation dLog(n: Int64) -> Float = Float.log(1.0)
    operation dLog10(n: Int64) -> Float = Float.log10(100.0)
    operation dLog2(n: Int64) -> Float = Float.log2(8.0)

    -- constants
    operation dPi(n: Int64) -> Float = Float.pi()
    operation dE(n: Int64) -> Float = Float.e()
    operation dTau(n: Int64) -> Float = Float.tau()

    -- the IEEE max/min pair
    operation dMax(n: Int64) -> Float = Float.max(1.0, 2.0)
    operation dMin(n: Int64) -> Float = Float.min(1.0, 2.0)
    operation dMaxNaNLeft(n: Int64) -> Float = Float.max(nan, 1.0)
    operation dMaxNaNRight(n: Int64) -> Float = Float.max(1.0, nan)
    operation dMinNaNLeft(n: Int64) -> Float = Float.min(nan, 1.0)

    -- the `[simp]`-defined pair
    operation dRecip(n: Int64) -> Float = Float.recip(4.0)

    -- IEEE partiality is a VALUE (NaN / infinity), not an error
    operation dSqrtNegIsNaN(n: Int64) -> Bool = Float.isNaN(Float.sqrt(0.0 - 1.0))
    operation dLogZeroIsInf(n: Int64) -> Bool = Float.isInfinite(Float.log(0.0))
    operation dRecipZeroIsInf(n: Int64) -> Bool = Float.isInfinite(Float.recip(0.0))

    -- signed zero: `recip` is the observation that separates -0.0 from +0.0.
    operation dNegZeroRecip(n: Int64) -> Float = Float.recip(Float.neg(0.0))
    operation dSubZeroRecip(n: Int64) -> Float = Float.recip(0.0 - 0.0)
    operation dAbsNegZeroRecip(n: Int64) -> Float = Float.recip(Float.abs(Float.neg(0.0)))
    -- the `ite(lt(?a, 0.0), neg(?a), ?a)` restatement the ticket floated for `abs`
    operation iteAbs(a: Float) -> Float = if Float.lt(a, 0.0) then Float.neg(a) else a
    operation dIteAbsNegZeroRecip(n: Int64) -> Float = Float.recip(iteAbs(Float.neg(0.0)))
  end

  -- A SECOND sort, so the `[simp]` definition is driven from somewhere that is not the
  -- declaring sort — an inlining backing must reach every call site, which is the
  -- property a host mapping gets for free and this one does not.
  sort Elsewhere
    import anthill.prelude.{Float, Int64}
    operation crossRecip(n: Int64) -> Float = Float.recip(8.0)
    operation nestedRecip(n: Int64) -> Float =
      let x = Float.recip(2.0)
      Float.recip(x)
  end

  -- The three mathematical constants, in BOTH call forms the sort advertises.
  sort Constants
    import anthill.prelude.{Float, Int64}
    import anthill.prelude.Float.{pi, e, tau}
    operation barePi(n: Int64) -> Float = pi
    operation bareE(n: Int64) -> Float = e
    operation bareTau(n: Int64) -> Float = tau
    operation parenPi(n: Int64) -> Float = pi()
    operation parenE(n: Int64) -> Float = e()
    operation parenTau(n: Int64) -> Float = tau()
  end
end
"#;

/// Drive `(entry, expected)` PAIRS on ONE interpreter, comparing within 1e-12.
///
/// Pairs, not two parallel arrays: `zip` stops at the shorter one, so a forgotten
/// expectation would silently DROP its assertion and still pass — and the expectations
/// here run to seven consecutive `0.0`s, where no reader would catch the slip.
///
/// One interpreter, not one per call, because `crate::common::interp_for` parses and
/// loads the whole stdlib each time (~0.5s). `wi876_operation_mapping_test`'s
/// `eval_all` records the same rule and why it is not a micro-optimisation. The
/// fresh-per-call discipline applies to a TRAPPED call, which poisons every later call
/// on the same interpreter — every entry here is expected to SUCCEED, and the tests
/// that expect an error build their own interpreter per call.
/// Equality first, then the tolerance: several expectations here are INFINITIES (the
/// signed-zero counterexamples observe `recip`, whose whole point is `±inf`), and
/// `(inf - inf).abs() < 1e-12` is a NaN comparison, i.e. false. Exact-then-approximate
/// covers both without a per-case flag.
fn assert_floats(cases: &[(&str, f64)]) {
    let mut interp = crate::common::interp_for(DRIVER);
    for (entry, want) in cases {
        match interp.call(entry, &[Value::Int(0)]) {
            Ok(Value::Float(got)) => assert!(
                got == *want || (got - want).abs() < 1e-12,
                "{entry}: expected {want}, got {got}"
            ),
            other => panic!("call {entry}: expected a Float, got {other:?}"),
        }
    }
}

/// The headline: one operation from every family runs. Each of these answered
/// `OperationBodyMissing` before this ticket.
#[test]
fn every_float_family_evaluates() {
    assert_floats(&[
        ("wi881.float.D.dAbs", 1.5),
        ("wi881.float.D.dNeg", -1.5),
        ("wi881.float.D.dSqrt", 2.0),
        ("wi881.float.D.dHypot", 5.0),
        ("wi881.float.D.dFmod", 1.5),
        ("wi881.float.D.dPow", 1024.0),
        ("wi881.float.D.dSin", 0.0),
        ("wi881.float.D.dCos", 1.0),
        ("wi881.float.D.dTan", 0.0),
        ("wi881.float.D.dAsin", 0.0),
        ("wi881.float.D.dAcos", 0.0),
        ("wi881.float.D.dAtan", 0.0),
        ("wi881.float.D.dAtan2", 0.0),
        ("wi881.float.D.dExp", 1.0),
        ("wi881.float.D.dLog", 0.0),
        ("wi881.float.D.dLog10", 2.0),
        ("wi881.float.D.dLog2", 3.0),
        ("wi881.float.D.dPi", std::f64::consts::PI),
        ("wi881.float.D.dE", std::f64::consts::E),
        ("wi881.float.D.dTau", std::f64::consts::TAU),
        ("wi881.float.D.dRecip", 0.25),
    ]);
}

/// `floor`/`ceil`/`round` cross to `Int64`, and that crossing is the only place the
/// two carriers stop lining up.
#[test]
fn rounding_crosses_to_int64() {
    let mut interp = crate::common::interp_for(DRIVER);
    for (entry, want) in [
        ("wi881.float.D.dFloor", 1),
        ("wi881.float.D.dCeil", 2),
        ("wi881.float.D.dRound", 2), // half away from zero
    ] {
        match interp.call(entry, &[Value::Int(0)]) {
            Ok(Value::Int(n)) => assert_eq!(n, want, "{entry}"),
            other => panic!("call {entry}: expected an Int64, got {other:?}"),
        }
    }
}

/// …and it is PARTIAL, loudly. `as i64` saturates NaN to `0` and `1e300` to
/// `i64::MAX`, which is a wrong answer that looks like a right one — the repo's
/// no-silent-fallback rule. The signature does not say the operation is partial;
/// giving it a guarded `Error` effect row is WI-882's shape.
#[test]
fn rounding_out_of_int64_domain_raises() {
    for entry in ["wi881.float.D.dFloorNaN", "wi881.float.D.dFloorHuge"] {
        let mut interp = crate::common::interp_for(DRIVER);
        match interp.call(entry, &[Value::Int(0)]) {
            Err(anthill_core::eval::EvalError::Overflow { op }) => {
                assert_eq!(op, "Float.floor")
            }
            other => panic!("{entry}: expected a loud Overflow, got {other:?}"),
        }
    }
}

/// IEEE partiality that DOES have an answer stays an answer: `sqrt` of a negative is
/// NaN, `log(0.0)` and `recip(0.0)` are infinities. Only the `Int64` crossing raises.
#[test]
fn ieee_partiality_is_a_value_not_an_error() {
    let mut interp = crate::common::interp_for(DRIVER);
    for entry in [
        "wi881.float.D.dSqrtNegIsNaN",
        "wi881.float.D.dLogZeroIsInf",
        "wi881.float.D.dRecipZeroIsInf",
    ] {
        match interp.call(entry, &[Value::Int(0)]) {
            Ok(Value::Bool(true)) => {}
            other => panic!("call {entry}: expected true, got {other:?}"),
        }
    }
}

/// `max`/`min` are the IEEE-754 `maxNum`/`minNum` — they ABSORB NaN and are
/// therefore COMMUTATIVE, which the `Ord` derivation (`if gte(a, b) then a else
/// b`) is not: with a NaN operand every comparison is false, so it answers the second
/// argument on `(nan, 1.0)` and the first on `(1.0, nan)`. That asymmetry is why
/// `Float` declares its own pair. It could not have inherited one anyway — `max`/`min`
/// live on `Ord`, `Float` provides `PartialOrd`, and before this ticket there was
/// NO way to take the maximum of two floats at all.
#[test]
fn max_min_are_ieee_and_absorb_nan() {
    assert_floats(&[
        ("wi881.float.D.dMax", 2.0),
        ("wi881.float.D.dMin", 1.0),
        ("wi881.float.D.dMaxNaNLeft", 1.0),
        ("wi881.float.D.dMaxNaNRight", 1.0),
        ("wi881.float.D.dMinNaNLeft", 1.0),
    ]);
}

/// THE `neg` LAW, settled. `rule neg(?a) <=> sub(0.0, ?a)` is FALSE, and `recip` is
/// the observation that shows it: `neg(0.0)` is `-0.0` (`recip` → `-inf`) while
/// `0.0 - 0.0` is `+0.0` (`recip` → `+inf`). So the equation is not the definition and
/// tagging it `[simp]` would have made `neg` compute the wrong sign at zero. It is
/// restated over `mul(-1.0, ?a)`, which flips the sign bit exactly, and `neg` itself
/// is backed by the host intrinsic.
#[test]
fn neg_law_over_sub_is_false() {
    assert_floats(&[
        ("wi881.float.D.dNegZeroRecip", f64::NEG_INFINITY),
        ("wi881.float.D.dSubZeroRecip", f64::INFINITY),
    ]);
}

/// …and the RESTATEMENT is true, driven on a local control because the stdlib law is
/// deliberately inert (untagged) — a specification nothing executes is a specification
/// nothing checks, so the equation's right-hand side is checked here instead. Both
/// halves matter: it must negate, AND it must produce `-0.0` at zero, which is the
/// exact input the `sub(0.0, ?a)` form got wrong.
#[test]
fn the_restated_neg_law_holds_at_signed_zero() {
    const CONTROL: &str = r#"
namespace wi881.negLaw
  import anthill.prelude.{Float, Int64}

  sort L
    import anthill.prelude.{Float, Int64}
    import anthill.prelude.Numeric.{mul}
    operation lawNeg(a: Float) -> Float
    rule lawNeg(?a) <=> mul(-1.0, ?a) [simp]

    operation drive(n: Int64) -> Float = lawNeg(2.5)
    operation driveZeroRecip(n: Int64) -> Float = Float.recip(lawNeg(0.0))
  end
end
"#;
    let mut interp = crate::common::interp_for(CONTROL);
    for (entry, want) in [
        ("wi881.negLaw.L.drive", -2.5),
        ("wi881.negLaw.L.driveZeroRecip", f64::NEG_INFINITY),
    ] {
        match interp.call(entry, &[Value::Int(0)]) {
            Ok(Value::Float(f)) => assert_eq!(f, want, "{entry}"),
            other => panic!("call {entry}: expected a Float, got {other:?}"),
        }
    }
}

/// THE `abs` LAW, settled. `abs` CLEARS the sign bit, and `-0.0` compares EQUAL to
/// `+0.0`, so no comparison-based law reaches it. The original
/// `abs(?a) <=> max(?a, neg(?a))` named `WeakOrd.max`, which no `Float` value can
/// reach; the `ite(lt(?a, 0.0), neg(?a), ?a)` restatement the ticket floated is
/// driven here and answers `-0.0` where `abs` must answer `+0.0`. The law is gone,
/// replaced by the part that is true (`abs(neg(?a)) <=> abs(?a)`), and `abs` is
/// backed by the host intrinsic.
#[test]
fn abs_is_not_definable_by_comparison() {
    assert_floats(&[
        ("wi881.float.D.dAbsNegZeroRecip", f64::INFINITY),
        // The ite restatement KEEPS the sign of -0.0, so it is not `abs`.
        ("wi881.float.D.dIteAbsNegZeroRecip", f64::NEG_INFINITY),
    ]);
}

/// THE `[simp]` DEFINITION reaches a call site OUTSIDE the declaring sort, and a
/// nested one. `recip` has no host mapping at all — `div` backs it through the
/// equation — so if the inlining did not fire everywhere, this is where it would die
/// `OperationBodyMissing`, which is the very failure the ticket exists to remove.
#[test]
fn the_simp_definition_fires_away_from_its_sort() {
    assert_floats(&[
        ("wi881.float.Elsewhere.crossRecip", 0.125),
        ("wi881.float.Elsewhere.nestedRecip", 2.0),
    ]);
}

/// INLINING IS NOT DISPATCH, and here is where the difference is observable: it is why
/// `tau` is host-backed and `recip` is not, though both equations are exact. A `[simp]`
/// head is an APPLICATION, so it matches `tau()` and NOT the BARE `tau` this sort's own
/// comment advertises as a call form. With `[simp]` alone, `pi` and `e` answered bare
/// and `tau` died `OperationBodyMissing`; three constants of one family must behave
/// alike, so all six of these run. [`a_bare_nullary_simp_head_never_fires`] isolates
/// the same limit on the head side.
#[test]
fn the_constants_answer_in_both_nullary_call_forms() {
    assert_floats(&[
        ("wi881.float.Constants.barePi", std::f64::consts::PI),
        ("wi881.float.Constants.bareE", std::f64::consts::E),
        ("wi881.float.Constants.bareTau", std::f64::consts::TAU),
        ("wi881.float.Constants.parenPi", std::f64::consts::PI),
        ("wi881.float.Constants.parenE", std::f64::consts::E),
        ("wi881.float.Constants.parenTau", std::f64::consts::TAU),
    ]);
}

/// The HEAD side of the same limit, on a local control so nothing in the stdlib moves:
/// a `[simp]` equation whose head is a BARE nullary name never fires, and the operation
/// dies `OperationBodyMissing` with the tag present. This is why all four of
/// `float.anthill`'s equations were inert, and it is the left-hand mirror of the hazard
/// `map.anthill` records on the right (`<=> none [simp]` parses as `none[simp]`).
/// `kernel-language.md`'s "Equational rules" paragraph states both.
#[test]
fn a_bare_nullary_simp_head_never_fires() {
    const CONTROL: &str = r#"
namespace wi881.nullary
  import anthill.prelude.{Int64}

  sort C
    import anthill.prelude.{Int64}
    import anthill.prelude.Numeric.{add}

    operation parenthesized() -> Int64
    rule parenthesized() <=> add(20, 20) [simp]

    operation bare() -> Int64
    rule bare <=> add(25, 25) [simp]

    operation driveParenthesized(n: Int64) -> Int64 = parenthesized()
    operation driveBare(n: Int64) -> Int64 = bare()
  end
end
"#;
    let mut interp = crate::common::interp_for(CONTROL);
    match interp.call("wi881.nullary.C.driveParenthesized", &[Value::Int(0)]) {
        Ok(Value::Int(40)) => {}
        other => panic!("a parenthesized nullary [simp] head must fire; got {other:?}"),
    }
    let mut interp = crate::common::interp_for(CONTROL);
    match interp.call("wi881.nullary.C.driveBare", &[Value::Int(0)]) {
        Err(anthill_core::eval::EvalError::OperationBodyMissing { name, .. }) => {
            assert_eq!(name, "wi881.nullary.C.bare")
        }
        other => panic!("a bare nullary [simp] head must not fire; got {other:?}"),
    }
}
