//! WI-785 — a destructuring LAMBDA must match a NAME-keyed tuple.
//!
//! `match_tuple_pattern` (eval/pattern.rs) read only `Value::Tuple.pos` and
//! compared its length against the binder count. A name-keyed tuple carries all
//! of its components in `named` and none in `pos`, so it presented as ZERO
//! components, failed the arity test, and RAISED at eval — on a program that
//! loaded clean. Exactly one corner was broken: a destructuring binder over a
//! name-keyed tuple. The three neighbours all worked, which is what the
//! `*_still_works` guards below pin.
//!
//! The sibling `match_constructor_pattern` in the same file already had the
//! right shape — `constructor_sub_values` presents positional-then-named so the
//! sub-pattern loop is keying-agnostic, plus WI-445 label resolution — so this
//! was an asymmetry between two adjacent matchers, not a missing concept.
//!
//! Indexing components positionally is sound because a named tuple is an ORDERED
//! PRODUCT — `canonicalize_record_named_args` (kb/resolve.rs) returns early for
//! one, "source order IS its identity" — AND because `pos ++ named` reproduces
//! that order, which is WI-786's invariant on `classify_ctor_arg`. The first cut
//! of this fix assumed only the former and was unsound; the shapes that exposed
//! it live in `wi786_tuple_component_order_test.rs`. `binds_in_source_order`
//! pins the binding here, since order is what would silently swap arguments.
//!
//! This does NOT re-conflate WI-775's keying distinction: that governs a tuple
//! TYPE's identity, whereas a destructuring binder list is not itself a tuple
//! and claims only "bind the i-th component".
//!
//! Distinct from WI-784 (closure ARITY — `enter_closure` is strictly unary and
//! rejects an N-argument application outright). Here the closure is applied with
//! exactly ONE argument and fails later, inside pattern matching.

use crate::common::{interp_for, try_load_kb_with};

fn run_int(src: &str, op: &str) -> i64 {
    // A FRESH interpreter per call: reusing one after a trapped call returns a
    // bogus Internal("deliver: parent frame had no awaiting state") on every
    // later call, which reads as an unrelated second failure.
    let mut interp = interp_for(src);
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// THE regression: a destructuring lambda over a name-keyed tuple. Pre-fix this
/// loaded clean and then raised a pattern-match failure.
#[test]
fn destructuring_lambda_matches_named_tuple() {
    let src = r#"
namespace test.wi785named
  import anthill.prelude.{Int64, Function}
  operation apply_tuple(f: Function[A = (acc: Int64, x: Int64), B = Int64]) -> Int64
    = f((acc: 3, x: 10))
  operation drive() -> Int64
    = apply_tuple(lambda (acc, x) -> acc - x)
end
"#;
    assert_eq!(run_int(src, "test.wi785named.drive"), -7);
}

/// The load-bearing semantic: components bind in SOURCE order. Field names are
/// spelled `x, acc` so that any re-ordering — canonicalizing the tuple like a
/// record, or reversing it — flips the result to +7, while every other test in
/// this file would still pass.
///
/// (`canonicalize_record_named_args` sorts by DECLARED field order, else by
/// interning order — never alphabetically — and `TupleLiteral` has no field
/// schema, so removing its ordered-product exemption is a no-op for a
/// two-component tuple. `tuple_order_test.rs` pins that exemption directly with
/// adversarially interned names; this test pins the BINDING that depends on it.)
#[test]
fn binds_in_source_order() {
    let src = r#"
namespace test.wi785order
  import anthill.prelude.{Int64, Function}
  operation apply_tuple(f: Function[A = (x: Int64, acc: Int64), B = Int64]) -> Int64
    = f((x: 3, acc: 10))
  operation drive() -> Int64
    = apply_tuple(lambda (p, q) -> p - q)
end
"#;
    assert_eq!(
        run_int(src, "test.wi785order.drive"),
        -7,
        "p must bind the FIRST WRITTEN component (x = 3); any re-ordering gives +7",
    );
}

/// All three spellings of the same call must agree — the named-tuple form is
/// what regressed, the other two are the controls that always worked.
#[test]
fn named_positional_and_opref_spellings_agree() {
    let named_lambda = r#"
namespace test.wi785a
  import anthill.prelude.{Int64, Function}
  operation apply_tuple(f: Function[A = (acc: Int64, x: Int64), B = Int64]) -> Int64
    = f((acc: 3, x: 10))
  operation drive() -> Int64
    = apply_tuple(lambda (acc, x) -> acc - x)
end
"#;
    let positional_lambda = r#"
namespace test.wi785b
  import anthill.prelude.{Int64, Function}
  operation apply_tuple(f: Function[A = (Int64, Int64), B = Int64]) -> Int64
    = f((3, 10))
  operation drive() -> Int64
    = apply_tuple(lambda (acc, x) -> acc - x)
end
"#;
    let named_opref = r#"
namespace test.wi785c
  import anthill.prelude.{Int64, Function}
  operation subt(t: (acc: Int64, x: Int64)) -> Int64
    = t.acc - t.x
  operation apply_tuple(f: Function[A = (acc: Int64, x: Int64), B = Int64]) -> Int64
    = f((acc: 3, x: 10))
  operation drive() -> Int64
    = apply_tuple(subt)
end
"#;
    let a = run_int(named_lambda, "test.wi785a.drive");
    let b = run_int(positional_lambda, "test.wi785b.drive");
    let c = run_int(named_opref, "test.wi785c.drive");
    assert_eq!((a, b, c), (-7, -7, -7), "all three spellings must agree (pre-fix the first raised)");
}

/// A non-destructuring binder over the same named tuple — the workaround users
/// had to reach for. Must keep working.
#[test]
fn whole_tuple_binder_still_works() {
    let src = r#"
namespace test.wi785whole
  import anthill.prelude.{Int64, Function}
  operation apply_tuple(f: Function[A = (acc: Int64, x: Int64), B = Int64]) -> Int64
    = f((acc: 3, x: 10))
  operation drive() -> Int64
    = apply_tuple(lambda t -> t.acc - t.x)
end
"#;
    assert_eq!(run_int(src, "test.wi785whole.drive"), -7);
}

/// Arity strictness must survive the widening: presenting named components
/// alongside positional ones must not let an N-component tuple match an
/// M-binder pattern. A 3-component tuple against 2 binders stays a non-match
/// (which surfaces as a raised pattern-match failure, not a wrong answer).
#[test]
fn arity_mismatch_still_refuses_to_match() {
    let src = r#"
namespace test.wi785arity
  import anthill.prelude.{Int64, Function}
  operation apply_tuple(f: Function[A = (a: Int64, b: Int64, c: Int64), B = Int64]) -> Int64
    = f((a: 1, b: 2, c: 3))
  operation drive() -> Int64
    = apply_tuple(lambda (p, q) -> p - q)
end
"#;
    // Loads clean (the arity is a runtime pattern-match property here), then
    // fails to match rather than binding the first two and dropping the third.
    assert!(try_load_kb_with(src).is_ok(), "fixture must load; the check is at eval");
    let mut interp = interp_for(src);
    assert!(
        interp.call("test.wi785arity.drive", &[]).is_err(),
        "a 3-component tuple must not match a 2-binder pattern",
    );
}
