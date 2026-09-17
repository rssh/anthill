//! WI-875 — no arithmetic input panics either engine, and overflow is a FAULT
//! rather than a refutation.
//!
//! Before this, four inputs behaved four different ways (all measured on the
//! WI-863 build): resolver `add` overflow PANICKED in debug and WRAPPED in release;
//! eval `mod`/`rem` at `(i64::MIN, -1)` panicked in debug AND release (remainder
//! overflow traps unconditionally); resolver `div`/`mod` at the same input answered
//! `no solutions`. The unifying rule is in [`ArithOutcome`]'s doc: the resolver may
//! answer `no solution` only where it knows NO ANSWER EXISTS; where an answer exists
//! that the carrier cannot hold, it must fault.
//!
//! That splits the inputs into three classes, and the tests below are organised by
//! them. The class boundary is the whole point, so each test names which side it is
//! pinning — a test that passed under the old behaviour too is marked CONTROL.

use crate::common::{anthill, fixtures_dir};

/// Same shape as `wi863_operator_arithmetic_test::query` — the `-p` KB is just a
/// non-empty target the CLI requires; the arithmetic is builtin-registered
/// regardless of what it contains.
fn query(pattern: &str) -> crate::common::Output {
    let kb = fixtures_dir("wi754").join("props.anthill");
    anthill(&[
        "query",
        "-p",
        kb.to_str().unwrap(),
        "-i",
        "anthill.prelude.Divisible.{div}",
        "-i",
        "anthill.prelude.EuclideanDomain.{mod}",
        "-i",
        "anthill.prelude.Additive.{add, sub}",
        "-i",
        "anthill.prelude.Multiplicative.{mul}",
        pattern,
    ])
}

const MIN: &str = "-9223372036854775808";
const MAX: &str = "9223372036854775807";

/// The fault's own sentence, so a test asserting "it faulted" cannot be satisfied by
/// some unrelated warning.
fn assert_overflow_fault(out: &crate::common::Output, p: &str) {
    assert_eq!(out.code, 0, "`{p}` must not crash; stderr:\n{}", out.stderr);
    assert!(
        out.has_diagnostic("warning:", "overflowed its carrier"),
        "`{p}` must FAULT naming the overflow; stderr:\n{}",
        out.stderr
    );
    assert!(
        out.has_stdout_line("no solutions"),
        "`{p}` produces no value; stdout:\n{}",
        out.stdout
    );
}

// ── Class 3: an answer exists, the carrier cannot hold it → FAULT ─────────

/// `add`/`sub`/`mul` overflow. THIS IS THE PANIC THE TICKET WAS FILED FOR: the int
/// slots were `|a, b| Some(a + b)`, so `add(i64::MAX, 1, ?r)` panicked in debug
/// (`attempt to add with overflow`) and wrapped to a silently wrong answer in
/// release. Back the change out and this test dies by PANIC, not by assertion.
#[test]
fn total_op_overflow_faults_rather_than_panicking() {
    for p in [
        &format!("add({MAX}, 1, ?r)"),
        &format!("sub({MIN}, 1, ?r)"),
        &format!("mul({MAX}, 2, ?r)"),
    ] {
        assert_overflow_fault(&query(p), p);
    }
}

/// `i64::MIN / -1` is the quotient 2^63, which Int64 cannot hold — so `div` is class
/// 3 even though its `mod` twin is not. Was `no solutions` with no diagnostic, i.e.
/// indistinguishable from the zero-divisor case below.
#[test]
fn min_over_negative_one_div_faults() {
    let p = &format!("div({MIN}, -1, ?r)");
    assert_overflow_fault(&query(p), p);
}

/// **The reason class 3 may not be a plain `Failure`.** `ReduceFaults::fault` sets
/// `truncated` alongside the message, so negation-as-failure above an overflow is
/// left UNDISCHARGED. Without it `not(add(MAX, 1, 0))` would answer a confident
/// `true` — asserting that `i64::MAX` has no successor, which is a wrong answer
/// rather than a true one.
#[test]
fn negation_over_an_overflow_is_not_a_refutation() {
    let out = query(&format!(
        "anthill.kernel.not(anthill.prelude.Additive.add({MAX}, 1, 0))"
    ));
    assert_eq!(out.code, 0, "must not crash; stderr:\n{}", out.stderr);
    assert!(
        !out.has_stdout_line("true"),
        "NAF over an overflow must not answer a confident `true`; stdout:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("conditional"),
        "the negation is left undischarged; stdout:\n{}",
        out.stdout
    );
}

// ── Class 2: the answer exists and IS representable → return it ───────────

/// `x mod -1 == 0` for every `x`, `i64::MIN` included. The resolver dropped it as
/// `no solution` (`checked_rem_euclid` is `None` there) and eval PANICKED on it;
/// both now answer 0. Back the change out and the resolver half goes red on the
/// value assertion while the eval half (`eval::builtins` unit tests) panics.
#[test]
fn min_mod_negative_one_is_zero_in_the_resolver() {
    let p = &format!("mod({MIN}, -1, ?r)");
    let out = query(p);
    assert_eq!(out.code, 0, "`{p}` must run; stderr:\n{}", out.stderr);
    assert!(
        out.stdout.contains("?r = 0"),
        "`{p}` -> 0, the representable answer; stdout:\n{}",
        out.stdout
    );
    assert!(
        !out.has_diagnostic("warning:", "overflowed its carrier"),
        "an answer exists here — it must NOT fault; stderr:\n{}",
        out.stderr
    );
}

/// The ordinary negative divisor, which shares `mod`'s `-1` arm's code path but has
/// nothing to do with overflow: Euclidean `mod` is non-negative, so `5 mod -3 = 2`.
/// CONTROL — passes either way; it pins that the new `-1` arm did not disturb the
/// general negative-divisor case beside it.
#[test]
fn negative_divisor_mod_is_euclidean() {
    let out = query("mod(5, -3, ?r)");
    assert!(
        out.stdout.contains("?r = 2"),
        "Euclidean mod is non-negative: 5 mod -3 = 2; stdout:\n{}",
        out.stdout
    );
}

// ── Class 1: no answer exists → `no solution`, and it stays that way ──────

/// CONTROL, and the one that makes the split observable rather than editorial: a
/// ZERO divisor is a domain gap, not a representation limit, so it must keep
/// answering `no solutions` with NO fault — the verdict WI-20260911-0V0F7 took
/// deliberately (`resolve.rs`'s `builtin_arith` doc). Passes both with and without
/// this change by design; it goes red only if class 3's fault leaks into class 1.
#[test]
fn zero_divisor_is_still_a_silent_no_solution() {
    for p in ["div(6, 0, ?r)", "mod(7, 0, ?r)"] {
        let out = query(p);
        assert_eq!(out.code, 0, "`{p}` must run; stderr:\n{}", out.stderr);
        assert!(
            out.has_stdout_line("no solutions"),
            "`{p}` -> no solutions; stdout:\n{}",
            out.stdout
        );
        assert!(
            !out.has_diagnostic("warning:", "overflowed its carrier"),
            "a zero divisor is a DOMAIN gap, not an overflow; stderr:\n{}",
            out.stderr
        );
    }
}

/// CONTROL for the same boundary from the other side: `not` over a zero divisor is
/// still a confident `true`. This is the answer WI-0V0F7 protected — `div(1, 0, ?q)`
/// is in the relation for no `?q` and the resolver knows it — and the one that would
/// have been lost had overflow and the zero divisor been given one arm.
#[test]
fn negation_over_a_zero_divisor_still_refutes() {
    let out = query("anthill.kernel.not(anthill.prelude.Divisible.div(1, 0, 5))");
    assert!(
        out.has_stdout_line("true"),
        "NAF over a zero divisor stays a refutation; stdout:\n{}",
        out.stdout
    );
}

// ── The arithmetic that must not have moved ──────────────────────────────

/// CONTROL for the `Option` -> [`ArithOutcome`] signature change: every non-corner
/// case computes exactly as before, on each carrier the builtin serves.
#[test]
fn ordinary_arithmetic_is_unchanged() {
    for (p, want) in [
        ("add(6, 2, ?r)", "?r = 8"),
        ("sub(6, 2, ?r)", "?r = 4"),
        ("mul(6, 2, ?r)", "?r = 12"),
        ("div(7, 2, ?r)", "?r = 3"),
        ("mod(7, 2, ?r)", "?r = 1"),
        ("div(6.0, 2.0, ?r)", "?r = 3.0"),
    ] {
        let out = query(p);
        assert!(
            out.stdout.contains(want),
            "`{p}` -> `{want}`; stdout:\n{}",
            out.stdout
        );
    }
}

/// BigInt is arbitrary-precision, so the magnitude that faults on Int64 has an
/// ordinary answer there — which is what the fault message points the user at.
///
/// BOTH operands are past `i64::MAX`, and that is not incidental: a literal selects
/// its carrier on its own, so a mixed pair reaches no slot at all (see
/// [`mixing_int64_and_bigint_operands_faults`] below — an earlier draft of this test
/// wrote `add(2^63, 1, ?r)` and measured `no solutions`, which is how that second
/// bug was found). `wi863_operator_arithmetic_test::bigint_div_and_mod_compute` puts
/// both operands past the boundary for the same reason.
///
/// CONTROL for the BigInt slots' `Option` -> [`ArithOutcome`] rewrite: passes either
/// way, and goes red only if that rewrite made BigInt fault or fail.
#[test]
fn bigint_computes_where_int64_overflows() {
    let out = query("add(9223372036854775808, 9223372036854775808, ?r)");
    assert_eq!(out.code, 0, "must run; stderr:\n{}", out.stderr);
    assert!(
        out.stdout.contains("?r = 18446744073709551616"),
        "BigInt has no overflow: 2^63 + 2^63 computes; stdout:\n{}",
        out.stdout
    );
    assert!(
        !out.has_diagnostic("warning:", "overflowed its carrier"),
        "BigInt must never report an overflow; stderr:\n{}",
        out.stderr
    );
}

/// Two numbers of DIFFERENT carriers reach no slot of `builtin_arith`, and used to
/// answer a bare `no solutions` for it — the same wrong shape as the overflow this
/// ticket fixes, and reachable by following the overflow fault's own advice halfway
/// (convert ONE operand with `to_bigint` and you land here). An answer exists, so by
/// [`ArithOutcome`]'s rule the resolver must say it cannot compute it rather than
/// report the relation empty.
#[test]
fn mixing_int64_and_bigint_operands_faults() {
    for p in [
        "add(9223372036854775808, 1, ?r)",
        "add(1, 9223372036854775808, ?r)",
        "mul(2.5, 2, ?r)",
    ] {
        let out = query(p);
        assert_eq!(out.code, 0, "`{p}` must not crash; stderr:\n{}", out.stderr);
        assert!(
            out.has_diagnostic("warning:", "operands of different numeric carriers"),
            "`{p}` must FAULT naming the carrier mismatch; stderr:\n{}",
            out.stderr
        );
    }
}

/// CONTROL for the arm above: a NON-numeric operand is a different question and keeps
/// its silent `Failure`. No answer exists for an ill-typed pair, so reporting the
/// relation empty is the true verdict rather than an evasion — the same distinction
/// the zero divisor draws against overflow. Passes either way; it goes red if the
/// carrier-mismatch fault were widened to every `_`.
#[test]
fn a_non_numeric_operand_is_still_a_silent_no_solution() {
    let out = query(r#"add(1, "foo", ?r)"#);
    assert!(
        out.has_stdout_line("no solutions"),
        "a non-numeric operand -> no solutions; stdout:\n{}",
        out.stdout
    );
    assert!(
        !out.has_diagnostic("warning:", "operands of different numeric carriers"),
        "a string is not a numeric carrier; stderr:\n{}",
        out.stderr
    );
}
