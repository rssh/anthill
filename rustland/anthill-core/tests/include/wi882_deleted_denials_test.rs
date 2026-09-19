//! WI-882 — the CONTROL for twelve deleted denial constraints.
//!
//! WHAT WAS DELETED and why it needs a control at all. `int64.anthill`,
//! `float.anthill` and `division.anthill` each stated operation preconditions as
//! plain `constraint invariant :- guard` denials. A plain denial is INERT — §8.4,
//! and `load_constraint`'s `ConstraintBody::Denial` arm says so in its own comment:
//! it is stored as reflected structure and never registered with the guard engine,
//! so only the quantified forms reach `check_all_guards`. TWELVE such rows therefore
//! stated nothing that fired, and WI-882 deleted them all. (The ticket counts
//! "the 11" — it inventoried `int64` and `float` before `division.anthill`'s
//! `mod_nonneg` was written, and that row is the twelfth.)
//!
//! EIGHT OF THE TWELVE WERE NOT MERELY REDUNDANT — THEY WERE FALSE, and that is what
//! this file pins. An inert channel is very good at hiding a wrong claim: nothing
//! ever evaluates it, so nothing ever contradicts it, and it survives in the source
//! reading as specification. The delete is only safe if the behaviour the deleted
//! rows contradicted is held down by a test, otherwise the same claim comes back as
//! prose in a comment and no one notices.
//!
//! WHAT FAILS IF THE DELETE IS BACKED OUT: nothing here, and that is the point — a
//! restored denial is still inert, so it cannot make an assertion fail. These tests
//! fail instead if the DECISION is reversed in a channel that DOES fire. MEASURED,
//! by building the reversal: restating `mod_positive` as a live `requires gt(b, 0)`
//! on `Int64.mod` turns [`euclidean_mod_accepts_a_negative_divisor`] red at LOAD,
//! three times over — `expected precondition gt(-3, 0) provable at the call site,
//! got unsatisfied precondition`, once per negative divisor in [`DRIVER`].
//!
//! THAT EXPERIMENT ALSO REFUTED THE REVERSAL OUTRIGHT, which is a better argument for
//! the delete than this file's own assertions. The same build produced a FOURTH load
//! error nobody wrote a call site for: `'anthill.prelude.Int64' overrides
//! 'anthill.prelude.EuclideanDomain.mod' but does not refine it: it strengthens the
//! precondition`. `Int64.mod` is an override of the spec operation, an override may
//! only WEAKEN a precondition, and `EuclideanDomain.mod` declares none — so
//! `gt(b, 0)` is not a thing `Int64.mod` is permitted to say in the live channel AT
//! ALL. The denial channel accepted it only because it was inert. (`mod_nonneg`, on
//! `EuclideanDomain` itself, would have been admissible there and is false for the
//! same Euclidean reason — hence both rows going, not just the carrier's.)
//!
//! [`the_resolver_agrees_with_eval_on_a_negative_divisor`] did NOT go red under that
//! reversal, and it is worth saying so rather than letting a reader assume the two
//! `mod` tests move together. It resolves `EuclideanDomain.mod` — the spec operation,
//! which is where the resolver's `BuiltinTag::Mod` is keyed — so a precondition added
//! to the `Int64` CARRIER does not gate it. What it pins is the ENGINE AGREEMENT (the
//! thing WI-875 established and the ticket's 2026-09-16 correction doubted), not the
//! precondition decision. A control that does not control what its neighbours control
//! is worth naming, because that is the one way a control fails silently.
//!
//! [`the_remaining_float_denials_restricted_a_total_operation`] shares [`DRIVER`]
//! with the `mod` test, so it goes red under that reversal collaterally, at load
//! rather than on its own subject. Its own subject fails if `Float.div`, `log10` or
//! `log2` is given a domain guard.
//!
//! HALF THE FLOAT SIX ARE PINNED ELSEWHERE, deliberately not duplicated here:
//! `wi881_float_arithmetic_test::ieee_partiality_is_a_value_not_an_error` drives
//! `sqrt(-1.0)`, `log(0.0)` and `recip(0.0)` and asserts each ANSWERS rather than
//! raising, which is exactly why `sqrt_nonneg` / `log_positive` / `recip_nonzero`
//! had nothing to guard. The other three — `div_float_nonzero`, `log10_positive`,
//! `log2_positive` — had no out-of-domain pin anywhere (`wi881` drives `log10` and
//! `log2` only at 100.0 and 8.0, which those rows PERMITTED), so their subjects are
//! added below. All six then have one.
//!
//! THE REMAINING FOUR need no control. `div_nonzero_primary` / `div_nonzero` /
//! `rem_nonzero` restated the live `Error[DivisionByZero]` row that
//! `wi066_division_effect_test` drives, so deleting them removed a copy and left
//! the original. `in_bounds` was guardless and quantified over every `Int64`; there
//! is no call site or assertion at which it could ever have been checked.
//!
//! Reference: `docs/kernel-language.md` §6.2 / §8.4, WI-875 (which made the two
//! engines agree on `mod`), WI-881 (which backed `Float` with the IEEE intrinsics
//! and so made the six float denials false).

use anthill_core::eval::Value;
use anthill_core::kb::term_view::TermView;

/// `Int64.mod`, `Float.div` and the two logarithms, at the arguments the deleted rows
/// forbade — each written as the LITERAL the constraint's guard named, so what is
/// absent is absent against the exact shape that would have triggered it.
const DRIVER: &str = r#"
namespace wi882.denials
  import anthill.prelude.{Int64, Float, Bool}

  sort D
    import anthill.prelude.{Int64, Float, Bool}

    -- `mod_positive: gt(?b, 0) :- mod(?_, ?b)` forbade every one of these.
    operation dModNeg(n: Int64) -> Int64 = Int64.mod(5, -3)
    operation dModNegOne(n: Int64) -> Int64 = Int64.mod(5, -1)
    operation dModNegDividend(n: Int64) -> Int64 = Int64.mod(-5, -3)
    -- the CONTROL: a positive divisor, which the deleted row permitted. It answers
    -- the same way, so the row was not selecting a working subset of anything.
    operation dModPos(n: Int64) -> Int64 = Int64.mod(5, 3)

    -- `div_float_nonzero: neq(?b, 0.0) :- div(?_, ?b)` forbade this one.
    operation dDivZeroIsInf(n: Int64) -> Bool = Float.isInfinite(Float.div(1.0, 0.0))
    operation dDivZeroSign(n: Int64) -> Float = Float.div(1.0, 0.0)
    -- IEEE's other zero-divisor case: 0/0 is NaN, not an infinity and not an error.
    operation dZeroOverZeroIsNaN(n: Int64) -> Bool = Float.isNaN(Float.div(0.0, 0.0))

    -- `log10_positive` / `log2_positive` forbade these. At 0.0 the answer is -inf;
    -- at a negative argument it is NaN. `wi881` drives both operations only INSIDE
    -- the domain those rows allowed, so these two arguments are what refutes them.
    operation dLog10ZeroIsInf(n: Int64) -> Bool = Float.isInfinite(Float.log10(0.0))
    operation dLog2NegIsNaN(n: Int64) -> Bool = Float.isNaN(Float.log2(0.0 - 4.0))
  end
end
"#;

/// THE ANSWER IS THE HEAD VARIABLE, bound by `mod`'s own third (result) argument —
/// so the test reads the value the resolver COMPUTED rather than a literal it merely
/// matched. `rule p(2) :- mod(5, -3, 2)` would also decide, but its answer comes back
/// as the head term and would pass while saying only "the goal did not fail"; what is
/// under test is which number comes out. NOT `?m = 1` in the body either
/// (WI-20260822-WZX6B): `=` is `PartialEq.eq`, a test that never binds, so that idiom
/// SUSPENDS and `definite_unary` counts zero.
const RESOLVER_DRIVER: &str = r#"
namespace wi882.resolver
  import anthill.prelude.{Int64}
  import anthill.prelude.EuclideanDomain.{mod}

  rule modNeg(?r) :- mod(5, -3, ?r)
  rule modNegOne(?r) :- mod(5, -1, ?r)
  rule modNegDividend(?r) :- mod(-5, -3, ?r)
  rule modPos(?r) :- mod(5, 3, ?r)
end
"#;

/// EUCLIDEAN `mod` IS DEFINED FOR A NEGATIVE DIVISOR, which is what makes
/// `constraint mod_positive: gt(?b, 0) :- mod(?_, ?b)` a false statement rather than
/// a redundant one. It was not a duplicate of `mod`'s `Error[DivisionByZero]` row —
/// that row forbids only ZERO, this forbade every `b < 0` — so deleting it on the
/// "pure duplication" reading would have dropped a claim silently. The claim is
/// dropped on purpose: the implementation contradicts it.
///
/// The result stays NON-NEGATIVE throughout, which is the property `mod` actually
/// owes and the one `division.anthill` still states in prose.
#[test]
fn euclidean_mod_accepts_a_negative_divisor() {
    let mut interp = crate::common::interp_for(DRIVER);
    for (entry, want) in [
        ("wi882.denials.D.dModNeg", 2),
        // `x mod -1` is 0 for every x. This reaches WI-875's explicit `-1` arm but
        // NOT the input that motivated it: `5.rem_euclid(-1)` would answer 0 without
        // the arm too, and only `i64::MIN` can reach the trap. That case is
        // `wi875_arithmetic_overflow_test`'s and is deliberately not restated here —
        // what this row pins is that a `-1` divisor is LEGAL, which is the
        // `mod_positive` claim.
        ("wi882.denials.D.dModNegOne", 0),
        ("wi882.denials.D.dModNegDividend", 1),
        // CONTROL: passes with and without the delete, by design.
        ("wi882.denials.D.dModPos", 2),
    ] {
        match interp.call(entry, &[Value::Int(0)]) {
            Ok(Value::Int(got)) => assert_eq!(got, want, "{entry}"),
            other => panic!("call {entry}: expected Int({want}), got {other:?}"),
        }
    }
}

/// THE SAME QUESTION AT THE OTHER DOOR. The ticket's 2026-09-16 correction recorded
/// the two engines as disagreeing about `mod`, which would have left "is a negative
/// divisor legal?" answerable two ways. WI-875 settled it — both are `rem_euclid`
/// with the same explicit `-1` arm — so the delete rests on one behaviour, not on
/// picking a favourite engine. `definite_unary`, not `query_unary`: a floundered
/// answer is a suspension and must never be counted as a decision.
#[test]
fn the_resolver_agrees_with_eval_on_a_negative_divisor() {
    let mut kb = crate::common::load_kb_with_stdlib_only(RESOLVER_DRIVER);
    for (goal, want) in [
        ("wi882.resolver.modNeg", 2),
        ("wi882.resolver.modNegOne", 0),
        ("wi882.resolver.modNegDividend", 1),
        // CONTROL: passes with and without the delete, by design.
        ("wi882.resolver.modPos", 2),
    ] {
        // READ THROUGH `TermView::literal_int64`, not by matching `Value::Int`. A
        // resolver answer arrives as whatever carrier bound it — here a `Value::Term`
        // holding the `Int64` literal, where eval hands back a native `Value::Int` —
        // and `literal_int64` is the carrier-neutral question both answer (the
        // representation note in CLAUDE.md; it is the same read `int_mod` itself
        // performs on its operands). Hard-matching one carrier would have made this
        // test report a false disagreement between the two engines, which is the
        // exact claim it exists to settle.
        //
        // The slice pattern keeps "exactly one definite answer" inside the assertion:
        // an index would pass just as happily on two.
        let answers = crate::common::definite_unary(&mut kb, goal);
        let [v] = answers.as_slice() else {
            panic!("{goal}: expected exactly one definite answer, got {answers:?}")
        };
        let got = v
            .literal_int64(&kb)
            .unwrap_or_else(|| panic!("{goal}: expected an Int64 answer, got {v:?}"));
        assert_eq!(got, want, "{goal}: the resolver must agree with eval");
    }
}

/// THE THREE FLOAT SUBJECTS `wi881` DOES NOT COVER. `Float.div` by zero is an IEEE
/// infinity (and `0.0 / 0.0` a NaN), `log10(0.0)` is -inf, `log2(-4.0)` is NaN —
/// never an error — so `div_float_nonzero`, `log10_positive` and `log2_positive`
/// each restricted a domain the operation does not restrict. `float_div` is
/// literally `x / y` on `f64`; the logarithms are `f64::log10` / `f64::log2`.
///
/// `sqrt(-1.0)`, `log(0.0)` and `recip(0.0)` — the other three rows' subjects — are
/// pinned by `wi881_float_arithmetic_test::ieee_partiality_is_a_value_not_an_error`
/// and are deliberately not repeated here.
#[test]
fn the_remaining_float_denials_restricted_a_total_operation() {
    let mut interp = crate::common::interp_for(DRIVER);
    for entry in [
        "wi882.denials.D.dDivZeroIsInf",
        "wi882.denials.D.dZeroOverZeroIsNaN",
        "wi882.denials.D.dLog10ZeroIsInf",
        "wi882.denials.D.dLog2NegIsNaN",
    ] {
        match interp.call(entry, &[Value::Int(0)]) {
            Ok(Value::Bool(true)) => {}
            other => panic!("call {entry}: expected Bool(true), got {other:?}"),
        }
    }
    // The SIGN too, so "it answered something" cannot pass for "it answered +inf":
    // an `Err` and a NaN both fail this, and a NaN would fail it even against itself.
    match interp.call("wi882.denials.D.dDivZeroSign", &[Value::Int(0)]) {
        Ok(Value::Float(got)) => assert_eq!(got, f64::INFINITY, "1.0 / 0.0"),
        other => panic!("call dDivZeroSign: expected Float(inf), got {other:?}"),
    }
}
