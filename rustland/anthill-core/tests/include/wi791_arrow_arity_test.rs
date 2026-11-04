//! WI-791 — an arrow recorded its PARAMETER-LIST ARITY, so a one-tuple-parameter operation was
//! not the same type as an n-parameter one. WI-20261104-6HVXM RETIRED the count (proposal 002
//! §"Correction (2026-11-03)", kernel-language §4.4): every arrow is a `Function`, its parameter
//! list is its tuple `A`, and `((a: A, b: B)) -> R` and `(a: A, b: B) -> R` are ONE type. What
//! WI-791 refused because the counts differed is read here by the rules that replaced the count:
//!
//!   * a callable WRITTEN at a slot meets the slot's `A` by label where the two tuples carry the
//!     same labels, by position otherwise — and a callable of one parameter takes the whole tuple,
//!     which a positional slot hands it by position (`get_a(t: (a: Int64, b: Int64))` at `(Int64,
//!     Int64) -> Int64` reads `t.a` as the first component);
//!   * where neither reaches the other — labels that are no tuple's of the other, a tuple against
//!     a sort — the callable is refused with both types side by side.
//!
//! The programs are WI-791's, kept so each of its repros is pinned at the value the rule gives;
//! the bracket in each doc is what the program did before WI-20261104-6HVXM.

use crate::common::{interp_for, load_kb_with, try_load_kb_with};

fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp
        .call(op, &[])
        .unwrap_or_else(|e| panic!("call {op}: {e:?}"))
    {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// `src` loaded and its `drive` run.
fn drives(src: &str, op: &str) -> i64 {
    let mut interp = interp_for(src);
    run_int(&mut interp, op)
}

/// Assert the program is refused with a type mismatch naming both arrows, `expected …, got …`.
fn assert_refused_naming(src: &str, expected: &str, got: &str) {
    let errs = match try_load_kb_with(src) {
        Ok(_) => panic!("must NOT load: `{got}` does not stand where `{expected}` is expected"),
        Err(errs) => errs,
    };
    let wanted = format!("expected {expected}, got {got}");
    assert!(
        errs.iter()
            .any(|e| e.contains("type mismatch") && e.contains(&wanted)),
        "rejection must be a type mismatch reading `{wanted}`; got: {errs:?}",
    );
}

// ── the ticket's two repros ────────────────────────────────────

/// REPRO 1. `get_a` takes ONE tuple-typed parameter; the annotation declares a positional
/// `A`. `get_a` takes the whole tuple, and the positional `(7, 8)` reaches its `t: (a: Int64,
/// b: Int64)` by position [refused, count; before WI-791 it trapped, `t.a` finding nothing].
#[test]
fn a_one_tuple_parameter_operation_takes_a_positional_slot_by_position() {
    let src = r#"
namespace test.wi791.repro1
  import anthill.prelude.{Int64}
  operation get_a(t: (a: Int64, b: Int64)) -> Int64
    = t.a
  operation drive() -> Int64
    = let f: (_1: Int64, _2: Int64) -> Int64 = get_a
      f((7, 8))
end
"#;
    assert_eq!(drives(src, "test.wi791.repro1.drive"), 7);
}

/// REPRO 2, the DUAL. A 2-parameter operation at a one-tuple-parameter annotation, which is the
/// two-parameter `(a: Int64, b: Int64) -> Int64`: the same labels, met by label, `7 - 8`
/// [refused, count].
#[test]
fn a_two_parameter_operation_takes_the_one_tuple_spelling_by_label() {
    let src = r#"
namespace test.wi791.repro2
  import anthill.prelude.{Int64}
  operation two(a: Int64, b: Int64) -> Int64
    = a - b
  operation drive() -> Int64
    = let f: (t: (a: Int64, b: Int64)) -> Int64 = two
      f((a: 7, b: 8))
end
"#;
    assert_eq!(drives(src, "test.wi791.repro2.drive"), -1);
}

// ── the two spellings WI-782's name gate could not catch ───────

/// BYPASS 1, the positional spelling: `take2(get_a)` is proposal 002's `fd` program, 1
/// [refused, count].
#[test]
fn a_positionally_spelled_slot_takes_a_one_tuple_parameter_operation() {
    let src = r#"
namespace test.wi791.bypass1
  import anthill.prelude.{Int64}
  operation get_a(t: (a: Int64, b: Int64)) -> Int64
    = t.a
  operation take2(f: (Int64, Int64) -> Int64) -> Int64
    = f(1, 2)
  operation drive() -> Int64
    = take2(get_a)
end
"#;
    assert_eq!(drives(src, "test.wi791.bypass1.drive"), 1);
}

/// BYPASS 2, LEADING ZEROS. `_01` is a USER label (WI-790), so `(_01: Int64, _02: Int64)` names
/// its components, and `(p: Int64, q: Int64)` names others: a callable of one parameter takes
/// the whole tuple by the tuple match, which relates no two such tuples. Refused, as it was.
#[test]
fn leading_zero_component_names_do_not_make_a_parameter_list() {
    assert_refused_naming(
        r#"
namespace test.wi791.bypass2
  import anthill.prelude.{Int64}
  operation get_a(t: (_01: Int64, _02: Int64)) -> Int64
    = t._01
  operation take2(f: (p: Int64, q: Int64) -> Int64) -> Int64
    = f(1, 2)
  operation drive() -> Int64
    = take2(get_a)
end
"#,
        "(p: Int64, q: Int64) -> Int64",
        "(_01: Int64, _02: Int64) -> Int64",
    );
}

/// A 2-parameter operation at the one-tuple spelling of a positional `A`: the same type as the
/// positional list, met by position, `minus(10, 3)` [refused, count; before WI-791 it ran].
#[test]
fn a_two_parameter_operation_takes_the_positional_one_tuple_spelling() {
    let src = r#"
namespace test.wi791.spread
  import anthill.prelude.{Int64}
  operation minus(a: Int64, b: Int64) -> Int64
    = a - b
  operation take(f: ((Int64, Int64)) -> Int64) -> Int64
    = f((10, 3))
  operation drive() -> Int64
    = take(minus)
end
"#;
    assert_eq!(drives(src, "test.wi791.spread.drive"), 7);
}

// ── what must keep working ─────────────────────────────────────

/// A callback slot written `(x: T) -> Int64` at `T := (a: Int64, b: Int64)`: the sibling `v: T`
/// sees the plain tuple, and `get_a` takes it whole.
#[test]
fn type_parameter_instantiated_at_a_tuple_still_applies() {
    let src = r#"
namespace test.wi791.typaram
  import anthill.prelude.{Int64}
  operation apply1[T](f: (x: T) -> Int64, v: T) -> Int64
    = f(v)
  operation get_a(t: (a: Int64, b: Int64)) -> Int64
    = t.a
  operation drive() -> Int64
    = apply1(get_a, (a: 7, b: 8))
end
"#;
    assert_eq!(drives(src, "test.wi791.typaram.drive"), 7);
}

/// The same generic shape in the MULTI-parameter direction: a 2-parameter callback slot taking a
/// 2-parameter operation, by position.
#[test]
fn generic_two_parameter_callback_still_applies() {
    let src = r#"
namespace test.wi791.generic2
  import anthill.prelude.{Int64}
  operation apply2[T](f: (x: T, y: T) -> Int64, v: T, w: T) -> Int64
    = f(v, w)
  operation minus(a: Int64, b: Int64) -> Int64
    = a - b
  operation drive() -> Int64
    = apply2(minus, 10, 3)
end
"#;
    assert_eq!(drives(src, "test.wi791.generic2.drive"), 7);
}

/// A one-tuple-parameter arrow APPLIED: `get_a` reads `t.a` of the tuple it is handed.
#[test]
fn one_tuple_parameter_arrow_applies_end_to_end() {
    let src = r#"
namespace test.wi791.onetuple
  import anthill.prelude.{Int64}
  operation get_a(t: (a: Int64, b: Int64)) -> Int64
    = t.a
  operation drive() -> Int64
    = let f: ((a: Int64, b: Int64)) -> Int64 = get_a
      f((a: 7, b: 8))
end
"#;
    assert_eq!(drives(src, "test.wi791.onetuple.drive"), 7);
}

/// The `Function` spelling of `a_two_parameter_operation_takes_the_positional_one_tuple_spelling`,
/// which is the same type and runs alike.
#[test]
fn the_function_spelling_is_the_same_type() {
    let src = r#"
namespace test.wi791.fnspelling
  import anthill.prelude.{Int64, Function}
  operation minus(a: Int64, b: Int64) -> Int64
    = a - b
  operation take(f: Function[A = (Int64, Int64), B = Int64]) -> Int64
    = f((10, 3))
  operation drive() -> Int64
    = take(minus)
end
"#;
    assert_eq!(drives(src, "test.wi791.fnspelling.drive"), 7);
}

// ── the representation, observed through the printer ───────────

/// The two spellings are one type and PRINT alike, `(a: Int64, b: Int64) -> Int64`, and the
/// printing reparses to that type — a second generation prints the same, so nothing accumulates.
/// [Before WI-20261104-6HVXM they printed apart, `((a: Int64, b: Int64)) -> Int64` for the
/// first.]
#[test]
fn the_two_arrow_spellings_print_alike_and_round_trip() {
    fn printed_params(src: &str) -> Vec<String> {
        let kb = load_kb_with(src);
        ["test.wi791.print.one", "test.wi791.print.two"]
            .iter()
            .map(|name| {
                let sym = kb.try_resolve_symbol(name).expect("op symbol");
                let info =
                    anthill_core::kb::op_info::lookup_operation_info(&kb, sym).expect("op info");
                let (_, ty) = info.params.first().expect("callback param");
                crate::common::print_type(&kb, ty)
            })
            .collect()
    }

    let gen1 = printed_params(
        r#"
namespace test.wi791.print
  import anthill.prelude.{Int64}
  operation one(f: ((a: Int64, b: Int64)) -> Int64) -> Int64
    = f((a: 1, b: 2))
  operation two(f: (a: Int64, b: Int64) -> Int64) -> Int64
    = f(1, 2)
end
"#,
    );
    assert_eq!(
        gen1,
        vec![
            "(a: Int64, b: Int64) -> Int64",
            "(a: Int64, b: Int64) -> Int64"
        ],
        "the one-tuple-parameter and two-parameter spellings are one type",
    );

    let gen2 = printed_params(&format!(
        r#"
namespace test.wi791.print
  import anthill.prelude.{{Int64}}
  operation one(f: {}) -> Int64
    = f((a: 1, b: 2))
  operation two(f: {}) -> Int64
    = f(1, 2)
end
"#,
        gen1[0], gen1[1]
    ));
    assert_eq!(
        gen2, gen1,
        "printing must be a fixpoint — no layer may accumulate"
    );
}

/// A callback of a TYPE-PARAMETERIZED slot is checked as a written one is (WI-792): `get_a`'s
/// tuple `(a: Int64, b: Int64)` and the slot's `(x: T, y: T)` name different components, so the
/// one parameter does not take the slot's tuple. The expected side is rendered through σ, `T`
/// pinned to `Int64` by the sibling arguments (WI-1085).
#[test]
fn generic_callback_is_conformance_checked() {
    assert_refused_naming(
        r#"
namespace test.wi791.knowngap
  import anthill.prelude.{Int64}
  operation apply2[T](f: (x: T, y: T) -> Int64, v: T, w: T) -> Int64
    = f(v, w)
  operation get_a(t: (a: Int64, b: Int64)) -> Int64
    = t.a
  operation drive() -> Int64
    = apply2(get_a, 7, 8)
end
"#,
        "(x: Int64, y: Int64) -> Int64",
        "(a: Int64, b: Int64) -> Int64",
    );
}
