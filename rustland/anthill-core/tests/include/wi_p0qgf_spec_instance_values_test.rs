//! WI-20261105-P0QGF part 2 — proposal 073 §2: A VALUE TYPED AT A SPEC OVER A PARAMETER IS AN
//! INSTANCE OF IT AT THE CARRIER ITS TYPE FIXES (`docs/design/instance-values.md` §7).
//!
//! `x: Additive` holds `Additive`'s operations at `x.T`, and a call at `x.T` takes its
//! dictionary from `x`. Where the spec is expected, the spec application is the instance:
//! `Additive[T = Int64]` is the dictionary load builds by kernel-language §8.7's order, and
//! under `requires Additive[T = X]`, `Additive[T = X]` is the clause's own. Where a `Type` is
//! expected the same text is a `Type` value, as before.
//!
//! CONTROLS, measured with a temporary switch per part in one build, then removed. Every row
//! that answers a value fails with the parameter's requirement backed out (its body is
//! refused "missing `requires Additive[T = …]`"), with the application read as the instance
//! backed out (refused "type 'anthill.prelude.Type' has no member 'T'"), and with the frame's
//! slot left unfilled ("`__req_additive` not bound"); besides those, a row fails with: the
//! check of a type parameter read as a value looking inside the application (`sum2`'s `X` is
//! then refused, "nothing in scope requires `TypeValue[T = X]`"),
//! `an_application_under_the_clause_is_the_clauses_instance` and
//! `the_instance_is_passed_on`; the defaulted path's read of the requirement at a projection,
//! the three rows through `describePlus`; the bridge leaving the slot to the argument,
//! `a_rule_bodys_call_takes_the_instance` alone. `an_application_where_a_type_is_expected_is_the_type`
//! and the refusal rows of programs refused before (`a_value_of_a_provider_is_no_instance`,
//! `an_instance_is_no_value_of_its_carrier`, `a_dot_on_the_instance_stays_refused`) pass in every
//! configuration by design.

use anthill_core::eval::{Interpreter, Value};

use crate::common::{interp_for, load_errors_of, one_definite_int, show_value};

fn call(interp: &mut Interpreter, op: &str) -> Value {
    match interp.call(op, &[]) {
        Ok(v) => v,
        Err(e) => panic!("`{op}`: {e:?}"),
    }
}

fn int(interp: &mut Interpreter, op: &str) -> i64 {
    match call(interp, op) {
        Value::Int(n) => n,
        other => panic!("`{op}`: expected an Int64, got {other:?}"),
    }
}

fn shown(interp: &mut Interpreter, op: &str) -> String {
    let v = call(interp, op);
    show_value(interp.kb(), &v)
}

/// A program of `ops` beside `add2`, 073 §2's.
fn program(ns: &str, ops: &str) -> String {
    format!(
        r#"
namespace p0qgf.{ns}
  import anthill.prelude.{{Int64, Float, Additive, Type}}
  operation add2(x: Additive, a: x.T, b: x.T) -> x.T = a + b
{ops}
end
"#
    )
}

/// 073 §2's generic caller of `add2`, handing it the instance it is given.
const SUM2: &str =
    "  operation sum2[X](a: X, b: X) -> X requires Additive[T = X] = add2(Additive[T = X], a, b)\n";

/// A user's spec whose second operation has a body in the spec, and its provider.
const DESC: &str = r#"
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
    operation describePlus(x: T) -> Int64 = describe(x) + 1
  end
  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
  operation d(i: Desc, v: i.T) -> Int64 = Desc.describe(v)
  operation dPlus(i: Desc, v: i.T) -> Int64 = Desc.describePlus(v)
"#;

/// 073 §2: `ints()` answers 5, the instance built at load at `Int64`.
#[test]
fn an_application_at_a_known_type_is_the_instance_load_builds() {
    let src = program("known", "  operation ints() -> Int64 = add2(Additive[T = Int64], 2, 3)");
    assert_eq!(int(&mut interp_for(&src), "p0qgf.known.ints"), 5);
}

/// `sum2`'s `Additive[T = X]` is the instance `sum2`'s caller supplied, at `Int64` and at
/// `Float`.
#[test]
fn an_application_under_the_clause_is_the_clauses_instance() {
    let src = program(
        "clause",
        &format!(
            "{SUM2}  operation sumInts() -> Int64 = sum2(2, 3)\n  operation sumFloats() -> Float = sum2(1.5, 2.5)"
        ),
    );
    let mut interp = interp_for(&src);
    assert_eq!(int(&mut interp, "p0qgf.clause.sumInts"), 5);
    assert_eq!(shown(&mut interp, "p0qgf.clause.sumFloats"), "4.0");
}

/// `zero` takes no `T`: both spellings read `x`'s instance. Refused before, "ambiguous dispatch
/// of `anthill.prelude.Additive.zero`: 5 instances provide `anthill.prelude.Additive`".
#[test]
fn a_member_that_takes_no_carrier_reads_the_instance() {
    let src = program(
        "zero",
        "  operation zeroOf(x: Additive) -> x.T = Additive.zero[T = x.T]()
  operation zeroOfApplied(x: Additive) -> x.T = Additive[T = x.T].zero()
  operation zeroInt() -> Int64 = zeroOf(Additive[T = Int64])
  operation zeroIntApplied() -> Int64 = zeroOfApplied(Additive[T = Int64])",
    );
    let mut interp = interp_for(&src);
    assert_eq!(int(&mut interp, "p0qgf.zero.zeroInt"), 0);
    assert_eq!(int(&mut interp, "p0qgf.zero.zeroIntApplied"), 0);
}

/// Where a `Type` is expected the application is the type, as before. Passes either way.
#[test]
fn an_application_where_a_type_is_expected_is_the_type() {
    let mut interp = interp_for(
        r#"
namespace p0qgf.ty
  import anthill.prelude.{Int64, Additive, Type}
  operation asType() -> Type = Additive[T = Int64]
end
"#,
    );
    assert_eq!(shown(&mut interp, "p0qgf.ty.asType"), "Additive[T = Int64]");
}

/// The instance passed on as a value, to an operation typed at the spec and to a generic one
/// whose `requires` it answers.
#[test]
fn the_instance_is_passed_on() {
    let src = program(
        "pass",
        &format!(
            "{SUM2}  operation passOn(x: Additive, a: x.T, b: x.T) -> x.T = add2(x, a, b)
  operation passOnInts() -> Int64 = passOn(Additive[T = Int64], 2, 3)
  operation viaGeneric(x: Additive, a: x.T, b: x.T) -> x.T = sum2(a, b)
  operation viaGenericInts() -> Int64 = viaGeneric(Additive[T = Int64], 2, 3)"
        ),
    );
    let mut interp = interp_for(&src);
    assert_eq!(int(&mut interp, "p0qgf.pass.passOnInts"), 5);
    assert_eq!(int(&mut interp, "p0qgf.pass.viaGenericInts"), 5);
}

/// Two instances, each answering the calls at its own carrier.
#[test]
fn two_instances_each_answer_their_own_carrier() {
    let src = program(
        "two",
        "  operation second(x: Additive, y: Additive, a: x.T, b: y.T) -> y.T = b + b
  operation first(x: Additive, y: Additive, a: x.T, b: y.T) -> x.T = a + a
  operation secondFloat() -> Float = second(Additive[T = Int64], Additive[T = Float], 1, 2.5)
  operation firstInt() -> Int64 = first(Additive[T = Int64], Additive[T = Float], 1, 2.5)",
    );
    let mut interp = interp_for(&src);
    assert_eq!(shown(&mut interp, "p0qgf.two.secondFloat"), "5.0");
    assert_eq!(int(&mut interp, "p0qgf.two.firstInt"), 2);
}

/// An instance an operation returns, and one bound by a `let` at the spec's type.
#[test]
fn an_instance_returned_or_bound() {
    let src = program(
        "held",
        "  operation intInstance() -> Additive[T = Int64] = Additive[T = Int64]
  operation returned() -> Int64 = add2(intInstance(), 2, 3)
  operation bound() -> Int64 =
    let k: Additive[T = Int64] = Additive[T = Int64]
    add2(k, 2, 3)",
    );
    let mut interp = interp_for(&src);
    assert_eq!(int(&mut interp, "p0qgf.held.returned"), 5);
    assert_eq!(int(&mut interp, "p0qgf.held.bound"), 5);
}

/// A user's spec, and its operation with a body in the spec, reached at `i.T`.
#[test]
fn a_user_spec_and_its_spec_body_at_the_instance() {
    let src = program(
        "user",
        &format!(
            "{DESC}  operation dLeaf() -> Int64 = d(Desc[T = Leaf], leaf())
  operation dPlusLeaf() -> Int64 = dPlus(Desc[T = Leaf], leaf())"
        ),
    );
    let mut interp = interp_for(&src);
    assert_eq!(int(&mut interp, "p0qgf.user.dLeaf"), 7);
    assert_eq!(int(&mut interp, "p0qgf.user.dPlusLeaf"), 8);
}

/// A host call passes the instance as the value it is.
#[test]
fn a_host_call_passes_the_instance() {
    let src = program(
        "host",
        "  operation intInstance() -> Additive[T = Int64] = Additive[T = Int64]",
    );
    let mut interp = interp_for(&src);
    let dict = call(&mut interp, "p0qgf.host.intInstance");
    match interp.call("p0qgf.host.add2", &[dict, Value::Int(2), Value::Int(3)]) {
        Ok(Value::Int(5)) => {}
        other => panic!("expected 5, got {other:?}"),
    }
}

/// A rule body's call: the application it writes, an instance an operation returns, and a
/// spec body reached through it.
#[test]
fn a_rule_bodys_call_takes_the_instance() {
    let src = program(
        "rule",
        &format!(
            "{DESC}  operation intInstance() -> Additive[T = Int64] = Additive[T = Int64]
  rule viaRule(?r) :- ?r <=> add2(Additive[T = Int64], 2, 3)
  rule viaRuleReturned(?r) :- ?r <=> add2(intInstance(), 2, 3)
  rule viaRuleDefaulted(?r) :- ?r <=> dPlus(Desc[T = Leaf], leaf())"
        ),
    );
    let mut interp = interp_for(&src);
    let kb = interp.kb_mut();
    assert_eq!(one_definite_int(kb, "p0qgf.rule.viaRule"), Some(5));
    assert_eq!(one_definite_int(kb, "p0qgf.rule.viaRuleReturned"), Some(5));
    assert_eq!(one_definite_int(kb, "p0qgf.rule.viaRuleDefaulted"), Some(8));
}

/// A spec's operation with a body in the spec, at a requirement written at a projection: the
/// call is answered by the requirement, as the body-less one is. Refused before this change,
/// "missing `requires Desc[T = …]`", while `Desc.describe(v)` in the same body loaded.
#[test]
fn a_spec_body_at_a_written_projection_requirement() {
    let mut interp = interp_for(
        r#"
namespace p0qgf.proj
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
    operation describePlus(x: T) -> Int64 = describe(x) + 1
  end
  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
  sort Box
    sort V = ?
    entity box(v: V)
  end
  operation plus(b: Box, v: b.V) -> Int64 requires Desc[T = b.V] = Desc.describePlus(v)
  operation go() -> Int64 = plus(box(v: leaf()), leaf())
end
"#,
    );
    assert_eq!(int(&mut interp, "p0qgf.proj.go"), 8);
}

const HEAD: &str = r#"
namespace p0qgf.refused
  import anthill.prelude.{Int64, Float, Additive, Bool}
  operation add2(x: Additive, a: x.T, b: x.T) -> x.T = a + b
"#;

fn refused(body: &str) -> Vec<String> {
    let errors = load_errors_of(&format!("{HEAD}{body}\nend\n"));
    assert!(!errors.is_empty(), "expected a refusal of:\n{body}");
    errors
}

fn says(errors: &[String], text: &str) -> bool {
    errors.iter().any(|e| e.contains(text))
}

/// kernel-language §8.2: `2` is no `Additive`. Refused before too.
#[test]
fn a_value_of_a_provider_is_no_instance() {
    let errors = refused("  operation bad() -> Int64 = add2(2, 2, 3)");
    assert!(says(&errors, "expected Additive, got Int64"), "{errors:?}");
}

/// A value typed at the spec is no `T`. Refused before too, there for the missing
/// `requires`; here for the argument.
#[test]
fn an_instance_is_no_value_of_its_carrier() {
    let errors = refused("  operation bad(x: Additive, a: x.T) -> x.T = x + a");
    assert!(says(&errors, "got Additive[T = x.T]"), "{errors:?}");
}

/// 058 §3.9: no value chooses a type. The conditional's instance is at `T = ?`, and `2` is not
/// its `T`. Refused before too, there because the application was a `Type`, which is the text
/// it fails on with the application read as the instance backed out.
#[test]
fn a_conditional_over_two_instances_fixes_no_carrier() {
    let errors = refused(
        "  operation bad(c: Bool) -> Int64 =\n    add2(if c then Additive[T = Int64] else Additive[T = Float], 2, 3)",
    );
    assert!(says(&errors, "expected x.T, got Int64"), "{errors:?}");
}

/// An application that leaves the carrier unwritten is no instance: which `T` it is at is not
/// in its type. Refused before too, as a `Type`; fails with the instance reading backed out.
#[test]
fn an_application_leaving_the_carrier_unwritten_is_refused() {
    let errors = refused("  operation bad() -> Int64 = add2(Additive, 2, 3)");
    assert!(says(&errors, "`T` left unwritten"), "{errors:?}");
}

/// An application at a type no provision answers has no instance. Refused before too, as a
/// `Type`; fails with the instance reading backed out.
#[test]
fn an_application_no_provision_answers_is_refused() {
    let errors = refused("  operation bad() -> Bool = add2(Additive[T = Bool], true, false)");
    assert!(says(&errors, "expected the instance `Additive[T = Bool]`"), "{errors:?}");
}

/// `x.zero()` stays refused (decided with the user 2026-11-06): a dot passes its receiver as the
/// first argument, and `zero` takes none. Refused before too.
#[test]
fn a_dot_on_the_instance_stays_refused() {
    let errors = refused("  operation bad(x: Additive) -> x.T = x.zero()");
    assert!(says(&errors, "expected 0 arguments"), "{errors:?}");
}
