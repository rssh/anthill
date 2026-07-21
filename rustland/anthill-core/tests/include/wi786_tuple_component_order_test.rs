//! WI-786 — a tuple literal's components must reach the runtime carrier in
//! SOURCE ORDER.
//!
//! `classify_ctor_arg` (eval/eval.rs) unwraps the parser's synthetic `_N` labels
//! for positional syntax back into `Value::Tuple.pos`. It used to do that with a
//! bare `starts_with('_')` test on the label text — but identifiers may begin
//! with `_`, so a USER label like `_b` took the same branch. Such a component was
//! moved into `pos`, which carries no labels, so the name was DISCARDED and the
//! pos/named split no longer followed source order.
//!
//! Nothing observed that until WI-785 taught `match_tuple_pattern` to read a
//! tuple's components as `pos ++ named`. Then it produced silent wrong answers:
//! `lambda (p, q) -> p - q` over `(a: 3, _b: 10)` returned 7 instead of -7, and
//! an operation declared `-> Int64` returned a `String` on a clean load.
//!
//! The hazard was already known in one place: `validate_projection_labels`
//! (parse/convert.rs) rejects `_`-prefixed labels for WI-639 distributive
//! projections, with a comment naming this exact mechanism. The guard was never
//! applied to the plain tuple-literal producer, which is the common path.
//!
//! The fix narrows the unwrap on two axes — the label must be EXACTLY the
//! synthetic name for its own source index, and nothing may already have gone to
//! `named` — giving every consumer the invariant that **`pos ++ named` is source
//! order**. These tests pin that invariant end-to-end rather than by inspecting
//! the carrier, because the carrier split is precisely what is not observable
//! from source.

use crate::common::{interp_for, try_load_kb_with};

fn run_int(src: &str, op: &str) -> i64 {
    // Fresh interpreter per call — a reused one poisons later calls after a trap.
    let mut interp = interp_for(src);
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// Build `ap(f) = f(<lit>)` over a `Function[A = <ty>, B = Int64]` and drive it.
/// Delegates to the cluster's ONE builder (`common::function_slot_case`) so this
/// file and its WI-788 / WI-803 siblings stay comparable line for line — they had
/// three copies of this shape, and wi788's asserted the sameness in a comment that
/// nothing enforced.
fn tuple_case(ns: &str, ty: &str, lit: &str, lam: &str) -> String {
    crate::common::function_slot_case(ns, "Int64, Function", ty, lit, lam)
}

/// THE regression. `_b` is a user label that merely happens to start with `_`;
/// it must stay a NAMED component so `_b`'s value remains the second one.
/// Pre-fix this returned 7 — `_b` was hoisted into `pos`, ahead of `a`.
#[test]
fn user_underscore_label_keeps_source_order() {
    let src = tuple_case(
        "test.wi786u",
        "(a: Int64, _b: Int64)",
        "(a: 3, _b: 10)",
        "lambda (p, q) -> p - q",
    );
    assert_eq!(
        run_int(&src, "test.wi786u.drive"),
        -7,
        "p must bind `a` = 3 and q `_b` = 10; pre-fix `_b` was hoisted first, giving 7",
    );
}

/// Three components with the `_`-prefixed one in the MIDDLE, so a hoist is
/// visible as a digit moving rather than a sign flip. Pre-fix: 213.
#[test]
fn underscore_label_in_the_middle_keeps_source_order() {
    let src = tuple_case(
        "test.wi786m",
        "(a: Int64, _b: Int64, c: Int64)",
        "(a: 1, _b: 2, c: 3)",
        "lambda (p, q, r) -> p * 100 + q * 10 + r",
    );
    assert_eq!(run_int(&src, "test.wi786m.drive"), 123, "pre-fix the hoist gave 213");
}

/// The type-soundness consequence, which fails in a different currency: under
/// the old hoist an operation declared `-> Int64` returned `Str("ess")` with a
/// clean load, because the typer ordered components by source while eval did not.
#[test]
fn declared_int_return_cannot_yield_a_string() {
    let src = r#"
namespace test.wi786sound
  import anthill.prelude.{Int64, String, Function}
  operation ap(f: Function[A = (a: Int64, _b: String), B = Int64]) -> Int64
    = f((a: 3, _b: "ess"))
  operation drive() -> Int64
    = ap(lambda (p, q) -> p)
end
"#;
    assert!(try_load_kb_with(src).is_ok(), "fixture must load; the check is at eval");
    let mut interp = interp_for(src);
    match interp.call("test.wi786sound.drive", &[]) {
        Ok(anthill_core::eval::Value::Int(i)) => assert_eq!(i, 3, "p must bind the Int64 slot"),
        Ok(other) => panic!(
            "an operation declared -> Int64 returned {other:?} — pre-fix it returned \
             Str(\"ess\") by hoisting `_b` into the first slot",
        ),
        Err(e) => panic!("must evaluate, not trap: {e:?}"),
    }
}

/// The boundary the narrowing must not cross: genuine positional syntax still
/// unwraps into `pos`. `(3, 10)` carries the parser's `_1`/`_2`, which ARE the
/// synthetic names for their own indices.
#[test]
fn positional_syntax_still_unwraps() {
    let src = tuple_case("test.wi786p", "(Int64, Int64)", "(3, 10)", "lambda (p, q) -> p - q");
    assert_eq!(run_int(&src, "test.wi786p.drive"), -7);
}

/// `_01` is not a synthetic name — `intern_positional_label` emits `_1` with no
/// leading zeros — so it stays NAMED. Guards the digit comparison against a
/// looser `parse::<usize>()` that would treat `_01` as position 0.
#[test]
fn leading_zero_label_is_not_synthetic() {
    let src = tuple_case(
        "test.wi786z",
        "(_01: Int64, b: Int64)",
        "(_01: 3, b: 10)",
        "lambda (p, q) -> p - q",
    );
    assert_eq!(run_int(&src, "test.wi786z.drive"), -7, "`_01` must stay in source position 0");
}

/// A synthetic-looking label for the WRONG index must not be unwrapped either:
/// `_2` written first is a user label at source index 0, not the auto-name for
/// that slot. It stays named, so order is preserved.
#[test]
fn synthetic_name_for_the_wrong_index_stays_named() {
    let src = tuple_case(
        "test.wi786w",
        "(_2: Int64, b: Int64)",
        "(_2: 3, b: 10)",
        "lambda (p, q) -> p - q",
    );
    assert_eq!(run_int(&src, "test.wi786w.drive"), -7, "`_2` at index 0 is a user label");
}

/// A `_`-prefixed user label must remain reachable BY NAME — the old hoist moved
/// it into `pos`, which keeps no labels, so `t._b` could not find it.
#[test]
fn underscore_label_still_reachable_by_field_access() {
    let src = r#"
namespace test.wi786f
  import anthill.prelude.{Int64}
  operation get(t: (a: Int64, _b: Int64)) -> Int64
    = t._b
  operation drive() -> Int64
    = get((a: 3, _b: 10))
end
"#;
    assert_eq!(run_int(src, "test.wi786f.drive"), 10);
}

/// The one shape that still splits a tuple across BOTH halves: an all-named
/// source whose FIRST label happens to be the synthetic `_1`. `pos` holds a
/// source-order prefix and `named` the rest, so `pos ++ named` is still source
/// order and destructuring binds correctly. (The parser rejects mixing
/// positional and named at the source level outright, so this is the only route.)
#[test]
fn prefix_split_across_pos_and_named_still_binds_in_order() {
    let src = tuple_case(
        "test.wi786x",
        "(_1: Int64, b: Int64)",
        "(_1: 3, b: 10)",
        "lambda (p, q) -> p - q",
    );
    assert_eq!(run_int(&src, "test.wi786x.drive"), -7, "`_1` is slot 0, `b` slot 1");
}

/// The `named.is_empty()` half of the guard, which nothing else here reaches.
///
/// `_1` written SECOND is the synthetic name for index 0 — and `pos.len()` is
/// still 0 when it is classified, because `a` went to `named`. Without the
/// `named.is_empty()` condition it would therefore hoist into `pos`, and
/// `pos ++ named` would read `[10, 3]` — a silent +7.
///
/// Every other fixture in this file leaves that condition trivially true (their
/// `_`-labelled component is either first or never synthetic), so deleting the
/// condition keeps them all green. This is the one that fails.
#[test]
fn synthetic_label_after_a_named_one_stays_named() {
    let src = tuple_case(
        "test.wi786g",
        "(a: Int64, _1: Int64)",
        "(a: 3, _1: 10)",
        "lambda (p, q) -> p - q",
    );
    assert_eq!(
        run_int(&src, "test.wi786g.drive"),
        -7,
        "`a` is slot 0 and `_1` slot 1; hoisting `_1` into pos would give +7",
    );
}
