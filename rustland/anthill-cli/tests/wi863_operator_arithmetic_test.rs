//! WI-863(B) — the arithmetic operators `/` `mod` `%` `div` compute in a query.
//!
//! `+` `-` `*` already resolved to the `Numeric.add`/`sub`/`mul` builtins, but
//! `/` and `mod` desugared to bare `div`/`mod`, which the resolver had no builtin
//! for — so `anthill query '6 / 2'` was refused as an unknown functor `div`
//! (misattributing the surface `/` the user actually wrote). Now `div`/`mod` are
//! resolver builtins on `Int64`, over Int and BigInt: truncated `div`, Euclidean
//! (non-negative) `mod`. PARTIAL — a zero divisor yields NO SOLUTION, the SLD
//! reading of the declared `Error[DivisionByZero] :- eq(b, 0)` (the eval
//! interpreter raises the catchable effect; SLD has no effect machinery).
//!
//! STILL not computing in a query, each pending its own resolver builtin:
//! `^`→`pow` (no Int `pow` op exists at all), prefix `-`→`neg`, `and`→`Bool.and`.

mod common;

use common::{anthill, fixtures_dir};

/// props has no bearing on the arithmetic — div/mod are builtins registered by
/// `register_builtin_tags` regardless of what a `-p` KB contains; props is
/// just a non-empty target the CLI requires.
fn query(pattern: &str) -> common::Output {
    let kb = fixtures_dir("wi754").join("props.anthill");
    anthill(&["query", "-p", kb.to_str().unwrap(), pattern])
}

/// The acceptance case: `6 / 2` no longer refuses `div` — it resolves. The 3-arg
/// form binds the quotient so the value is checked, not just "it ran".
#[test]
fn slash_divides_in_a_query() {
    let bare = query("6 / 2");
    assert_eq!(bare.code, 0, "`6 / 2` must resolve, not refuse; stderr:\n{}", bare.stderr);
    assert_eq!(bare.diagnostics("error:").count(), 0, "no refusal; stderr:\n{}", bare.stderr);

    let bound = query("div(6, 2, ?r)");
    assert!(bound.stdout.contains("?r = 3"), "6/2 = 3; stdout:\n{}", bound.stdout);
}

/// `mod` and its `%` spelling both compute, Euclidean (always non-negative).
#[test]
fn mod_computes_euclidean() {
    for p in ["7 mod 3", "7 % 3"] {
        let out = query(p);
        assert_eq!(out.code, 0, "`{p}` must resolve; stderr:\n{}", out.stderr);
        assert_eq!(out.diagnostics("error:").count(), 0, "`{p}` no refusal; stderr:\n{}", out.stderr);
    }
    // -7 mod 3 = 2 (non-negative), NOT -1 (that would be `rem`) — matches the eval
    // `Int64.mod` (rem_euclid).
    let neg = query("mod(-7, 3, ?r)");
    assert!(neg.stdout.contains("?r = 2"), "-7 mod 3 = 2 (euclidean); stdout:\n{}", neg.stdout);
}

/// `div` truncates toward zero, like the eval `Int64.div`.
#[test]
fn div_truncates_toward_zero() {
    let out = query("div(-7, 2, ?r)");
    assert!(out.stdout.contains("?r = -3"), "-7 / 2 truncates to -3; stdout:\n{}", out.stdout);
}

/// THE partiality pin: a zero divisor is NOT a value, so the goal has no result —
/// `no solutions`, exit 0. It must NOT be a refusal (the functor IS known) and NOT
/// a panic (Rust integer division by zero). This is the SLD reading of the
/// declared `Error[DivisionByZero] :- eq(b, 0)` guard firing.
#[test]
fn division_by_zero_is_no_solution_not_a_refusal() {
    for p in ["6 / 0", "div(6, 0, ?r)", "7 mod 0", "mod(7, 0, ?r)"] {
        let out = query(p);
        assert_eq!(out.code, 0, "`{p}` must run, not crash/refuse; stderr:\n{}", out.stderr);
        assert!(out.has_stdout_line("no solutions"), "`{p}` -> no solutions; stdout:\n{}", out.stdout);
        assert_eq!(out.diagnostics("error:").count(), 0, "`{p}` is not a refusal; stderr:\n{}", out.stderr);
    }
}

/// An unbound divisor is undecided, not false: `div(6, ?b, ?r)` DELAYS (a residual
/// `conditional`), it is not refused and does not wrongly report a value. Mirrors
/// how `add`/`mul` delay on an unbound operand.
#[test]
fn an_unbound_divisor_delays() {
    let out = query("div(6, ?b, ?r)");
    assert_eq!(out.code, 0, "an unbound divisor must not refuse; stderr:\n{}", out.stderr);
    assert_eq!(out.diagnostics("error:").count(), 0, "not a refusal; stderr:\n{}", out.stderr);
    assert!(
        out.stdout.contains("conditional") || out.stdout.contains("residual"),
        "an unbound divisor is undecided (conditional/residual); stdout:\n{}",
        out.stdout
    );
}

/// BigInt div/mod compute too (both operands past i64::MAX select the bigint
/// slot) — they must not silently fail while `add`/`sub`/`mul` compute on BigInt.
/// Only a zero divisor is partial for BigInt (no overflow).
#[test]
fn bigint_div_and_mod_compute() {
    let d = query("div(60000000000000000000, 20000000000000000000, ?r)");
    assert!(d.stdout.contains("?r = 3"), "6e19 / 2e19 = 3; stdout:\n{}", d.stdout);
    // 7e19 mod 2e19 = 1e19 (positive, euclidean).
    let m = query("mod(70000000000000000000, 20000000000000000000, ?r)");
    assert!(
        m.stdout.contains("?r = 10000000000000000000"),
        "7e19 mod 2e19 = 1e19; stdout:\n{}",
        m.stdout
    );
}

/// The `divExact` alias computes (qualified — it is deliberately NOT bare-name
/// resolvable, since no operator mints it; parity with the eval `Int64.divExact`).
#[test]
fn div_exact_alias_computes() {
    let out = query("anthill.prelude.Int64.divExact(6, 2, ?r)");
    assert!(out.stdout.contains("?r = 3"), "divExact(6,2) = 3; stdout:\n{}", out.stdout);
}

/// Float division rides the float slot (IEEE) — `div(6.0, 2.0)` = 3.0. This is the
/// `Float.div` behavior; the shared builtin serves it under the `div` name.
#[test]
fn float_division_computes() {
    let out = query("div(6.0, 2.0, ?r)");
    assert!(out.stdout.contains("?r = 3.0"), "6.0 / 2.0 = 3.0; stdout:\n{}", out.stdout);
}

/// The one overflow corner: `i64::MIN` over `-1`. `div` genuinely overflows (the
/// quotient `-MIN` is unrepresentable) so `no solution` is correct; `mod`'s answer
/// (0) IS representable but the CHECKED rem drops it — an accepted incompleteness
/// (the alternative, eval's unchecked `rem_euclid`, PANICS). Pinned so neither
/// path crashes nor is mistaken for a refusal.
#[test]
fn min_over_negative_one_yields_no_solution_not_a_crash() {
    for p in ["div(-9223372036854775808, -1, ?r)", "mod(-9223372036854775808, -1, ?r)"] {
        let out = query(p);
        assert_eq!(out.code, 0, "`{p}` must run (no panic/refusal); stderr:\n{}", out.stderr);
        assert!(out.has_stdout_line("no solutions"), "`{p}` -> no solutions; stdout:\n{}", out.stdout);
        assert_eq!(out.diagnostics("error:").count(), 0, "`{p}` not a refusal; stderr:\n{}", out.stderr);
    }
}

/// Regression guard for the `builtin_arith` `Option` generalization: the total
/// ops `add`/`sub`/`mul` must still compute exactly as before.
#[test]
fn add_sub_mul_still_compute() {
    for (p, want) in [
        ("add(6, 2, ?r)", "?r = 8"),
        ("sub(6, 2, ?r)", "?r = 4"),
        ("mul(6, 2, ?r)", "?r = 12"),
    ] {
        let out = query(p);
        assert!(out.stdout.contains(want), "`{p}` -> `{want}`; stdout:\n{}", out.stdout);
    }
}
