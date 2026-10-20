//! WI-20260911-VNQTR, found on the way — AN OPERATION USED AS A FUNCTION VALUE OWES WHAT A CALL
//! OF IT OWES, AND A FUNCTION VALUE IN A CONSTRUCTION'S FIELD IS TYPED AT THE INSTANCE THE
//! CONSTRUCTION STATES.
//!
//! `m[U](y: U) -> Type = app1(tyOf, y)` hands `tyOf` at `B = U` to an operation that applies
//! it. The value's dictionary is built where `tyOf` is named, from the caller's evidence, and
//! `m` holds none; the call `tyOf(y)` in the same place is refused, and the reference loaded
//! and died on a `nil` typed `List[T = Int64]`. A carrier no provision answers at was the same:
//! `app1i(stampOf, ns(n: 1))` loaded where `stampOf(ns(n: 1))` is refused. The reference parks
//! now what a call parks, and says it was used as a function value.
//!
//! A construction's field had no instance to type a function value at: `h[A = Int64](f:
//! lambda (x) -> tyOf(x))` was refused "unconstrained", its bracket notwithstanding, and `h(f:
//! tyOf)` minted `tyOf` at no type. The field is now typed at what the construction's bracket
//! and its expected type say, for a lambda and an operation name alike.
//!
//! A reference parks only what it can decide. An element still open there is read where the
//! value is applied, when the operation's parameters carry it — a sibling argument, the
//! construction the value stands in or the type its call is expected at may fix it after
//! the reference — and an element only the result names is pinned by the expected arrow's
//! result.
//!
//! BACK-OUTS, temporary switches in one build, over the whole `wi_tests` binary (7552 rows):
//!
//! * **the park at the reference off**: **4 red** —
//!   [`a_function_value_forwarding_a_parameter_is_refused_and_repaired`],
//!   [`a_function_value_at_an_unprovided_carrier_is_refused_as_the_call_is`],
//!   [`a_construction_at_the_callers_parameter_forwards_it`] and
//!   [`an_element_nothing_carries_is_refused_at_the_reference`].
//! * **an open element refused at the reference**: **1 red**,
//!   [`a_function_value_whose_instance_is_fixed_later_answers`].
//! * **the expected result not read**: **1 red**,
//!   [`an_element_only_the_result_names_is_pinned_by_the_expected_result`].
//! * **the construction's instance for an operation name only**: **2 red** —
//!   [`a_construction_types_a_function_value_at_its_instance`] and
//!   [`a_lambda_by_position_is_typed_at_the_construction_s_instance`]; **a lambda's field not
//!   looked up by position**: the second alone.
//!
//! Nothing outside this file moves under any of them.
//!
//! PASSES UNDER EVERY SWITCH, by design: [`a_function_value_at_a_stated_type_answers`].

use crate::common::{load_errors_of, replace_in_fixture};
use crate::wi_vnqtr_inline_param_forward_test::{answers, the_one_refusal};
use crate::wi_xsvcs_op_requires_forward_test::printed_repair;

const HEAD: &str = r#"
  import anthill.prelude.{Cell, Int64, String, Type, List, Option, Pair, cons, nil, some, none, pair}
  import anthill.reflect.{TypeValue}
  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = Cell[V = B]
  operation app1[A](f: (x: A) -> Type, y: A) -> Type = f(y)
"#;

fn program(ns: &str, body: &str) -> String {
    format!("namespace test.vnqtr.fv.{ns}\n{HEAD}\n{body}\nend\n")
}

/// The forward through a function value is refused at the reference, in either spelling of
/// the caller's parameter, and the clause it prints makes the `nil` answer.
#[test]
fn a_function_value_forwarding_a_parameter_is_refused_and_repaired() {
    for (ns, sig, param) in [("bracket", "m[U](y: U)", "U"), ("inline", "m(y: ?t)", "?t")] {
        let src = program(
            ns,
            &format!(
                "  operation {sig} -> Type = app1(tyOf, y)\n  operation empty() -> Type =\n    let xs: List[T = Int64] = nil\n    m(xs)"
            ),
        );
        let e = the_one_refusal(
            &src,
            &[
                &format!("`test.vnqtr.fv.{ns}.tyOf` used as a function value"),
                &format!("Declare `requires anthill.reflect.TypeValue[T = {param}]` on `test.vnqtr.fv.{ns}.m`"),
            ],
        );
        let (clause, _) = printed_repair(&e);
        let repaired = replace_in_fixture(
            &src,
            &format!("operation {sig} -> Type = app1(tyOf, y)"),
            &format!("operation {sig} -> Type {clause} = app1(tyOf, y)"),
        );
        assert_eq!(
            answers(&repaired, &[&format!("test.vnqtr.fv.{ns}.empty")]),
            ["Cell[V = List[T = Int64]]"],
            "{ns}"
        );
    }
}

/// A function value at a carrier no provision answers at is refused as the call is.
#[test]
fn a_function_value_at_an_unprovided_carrier_is_refused_as_the_call_is() {
    let src = r#"
namespace test.vnqtr.fv.unprovided
  import anthill.prelude.{Int64}
  sort Stamp
    sort T = ?
    operation stamp() -> Int64
  end
  sort NoStamp
    entity ns(n: Int64)
  end
  operation stampOf[B](x: B) -> Int64 requires Stamp[T = B] = Stamp.stamp[T = B]()
  operation app1i[A](f: (x: A) -> Int64, y: A) -> Int64 = f(y)
  operation go() -> Int64 = app1i(stampOf, ns(n: 1))
end
"#;
    the_one_refusal(
        src,
        &[
            "`test.vnqtr.fv.unprovided.stampOf` used as a function value",
            "no impl provides test.vnqtr.fv.unprovided.Stamp",
        ],
    );
}

/// A function value in a construction's field is typed at the instance the construction
/// states — by its bracket, or by the type it is expected at — and answers; a lambda and an
/// operation name alike.
#[test]
fn a_construction_types_a_function_value_at_its_instance() {
    let src = program(
        "ctor",
        r#"  sort H[A]
    entity h(f: (x: A) -> Type)
  end
  operation apply(v: H[A = Int64]) -> Type =
    match v
      case h(g) -> g(1)
  operation etaBr() -> Type = apply(h[A = Int64](f: tyOf))
  operation lamBr() -> Type = apply(h[A = Int64](f: lambda (x) -> tyOf(x)))
  operation mk() -> H[A = Int64] = h(f: tyOf)
  operation mkLam() -> H[A = Int64] = h(f: lambda (x) -> tyOf(x))
  operation etaExp() -> Type = apply(mk())
  operation lamExp() -> Type = apply(mkLam())"#,
    );
    assert_eq!(
        answers(
            &src,
            &[
                "test.vnqtr.fv.ctor.etaBr",
                "test.vnqtr.fv.ctor.lamBr",
                "test.vnqtr.fv.ctor.etaExp",
                "test.vnqtr.fv.ctor.lamExp"
            ]
        ),
        ["Cell[V = Int64]", "Cell[V = Int64]", "Cell[V = Int64]", "Cell[V = Int64]"]
    );
}

/// A construction at the caller's own parameter forwards it through the function value, and
/// is refused for it, as the call would be.
#[test]
fn a_construction_at_the_callers_parameter_forwards_it() {
    let src = program(
        "ctorfwd",
        r#"  sort H[A]
    entity h(f: (x: A) -> Type)
  end
  operation m[U](y: U) -> H[A = U] = h(f: tyOf)"#,
    );
    the_one_refusal(&src, &["Declare `requires anthill.reflect.TypeValue[T = U]` on `test.vnqtr.fv.ctorfwd.m`"]);
}

/// CONTROL, passes either way: a function value at a slot that states its type was always
/// given its dictionary there.
#[test]
fn a_function_value_at_a_stated_type_answers() {
    let src = program(
        "stated",
        "  operation app3(f: (x: Int64) -> Type) -> Type = f(1)\n  operation go() -> Type = app3(tyOf)",
    );
    assert_eq!(load_errors_of(&src), Vec::<String>::new());
    assert_eq!(answers(&src, &["test.vnqtr.fv.stated.go"]), ["Cell[V = Int64]"]);
}

/// A function value whose instance is fixed AFTER its reference answers: by a sibling
/// argument of the call it is passed to, a list's or an option's element, the construction
/// it stands in at a call's parameter. The element is open where `tyOf` is named, and the
/// arguments the value is applied to carry it, so it is read where the value is applied.
/// Refused at the reference as "an element nothing pins", each of these, which ran, was
/// refused (MEASURED).
#[test]
fn a_function_value_whose_instance_is_fixed_later_answers() {
    let src = program(
        "later",
        r#"  sort H[A]
    entity h(f: (x: A) -> Type)
  end
  operation apply(v: H[A = Int64]) -> Type =
    match v
      case h(g) -> g(1)
  operation applyO[X](y: X, o: Option[T = (x: X) -> Type]) -> Type =
    match o
      case some(g) -> g(y)
      case none() -> Int64
  operation applyL[X](y: X, gs: List[T = (x: X) -> Type]) -> Type =
    match gs
      case cons(g, rest) -> g(y)
      case nil() -> Int64
  operation inCtor() -> Type = apply(h(f: tyOf))
  operation inOption() -> Type = applyO("s", some(tyOf))
  operation inList() -> Type = applyL(5, [tyOf])"#,
    );
    assert_eq!(
        answers(
            &src,
            &["test.vnqtr.fv.later.inCtor", "test.vnqtr.fv.later.inOption", "test.vnqtr.fv.later.inList"]
        ),
        ["Cell[V = Int64]", "Cell[V = String]", "Cell[V = Int64]"]
    );
}

/// An element only the result names is pinned by the type the value is expected at, as a call
/// at that type pins it: `mkP` lifted against an arrow returning `Option[T = String]` is at `X
/// = String`. It loaded and died, "`__req_typevalue` not bound", its dictionary minted at no
/// type (MEASURED).
#[test]
fn an_element_only_the_result_names_is_pinned_by_the_expected_result() {
    let src = program(
        "ret",
        r#"  operation mkP[X](x: Int64) -> Pair[A = Type, B = Option[T = X]] requires TypeValue[T = X] = pair(X, none())
  operation app2(f: (x: Int64) -> Pair[A = Type, B = Option[T = String]]) -> Type =
    match f(1)
      case pair(t, o) -> t
  operation viaValue() -> Type = app2(mkP)"#,
    );
    assert_eq!(answers(&src, &["test.vnqtr.fv.ret.viaValue"]), ["String"]);
}

/// CONTROL for the two rows above: an element no parameter of the operation carries, and no
/// expected type fixes, is fixed by nothing a call of the value could pass, and is refused at
/// the reference — `tv[V](n: Int64) requires TypeValue[T = V]` lifted against `(n: Int64) ->
/// Type` loaded and died before function values parked anything.
#[test]
fn an_element_nothing_carries_is_refused_at_the_reference() {
    let src = program(
        "uncarried",
        r#"  operation tv[V](n: Int64) -> Type requires TypeValue[T = V] = Cell[V = V]
  operation app1i(f: (n: Int64) -> Type, n: Int64) -> Type = f(n)
  operation go() -> Type = app1i(tv, 0)"#,
    );
    the_one_refusal(&src, &["`test.vnqtr.fv.uncarried.tv` used as a function value", "is unconstrained"]);
}

/// A lambda in a construction's field is typed at the construction's instance written by
/// position as written by name, and whatever its sibling is. By position it had no hint
/// unless a sibling was a call or an operation name: the field it stood in was read off a
/// table only those looked up (MEASURED).
#[test]
fn a_lambda_by_position_is_typed_at_the_construction_s_instance() {
    let src = program(
        "pos",
        r#"  sort H2[A]
    entity h2(f: (x: A) -> Type, n: Int64)
  end
  operation apply2(v: H2[A = Int64]) -> Type =
    match v
      case h2(g, n) -> g(n)
  operation named() -> H2[A = Int64] = h2(f: lambda (x) -> tyOf(x), n: 1)
  operation positional() -> H2[A = Int64] = h2(lambda (x) -> tyOf(x), 1)
  operation bracket() -> Type = apply2(h2[A = Int64](lambda (x) -> tyOf(x), 2))
  operation goNamed() -> Type = apply2(named())
  operation goPositional() -> Type = apply2(positional())"#,
    );
    assert_eq!(
        answers(
            &src,
            &["test.vnqtr.fv.pos.goNamed", "test.vnqtr.fv.pos.goPositional", "test.vnqtr.fv.pos.bracket"]
        ),
        ["Cell[V = Int64]", "Cell[V = Int64]", "Cell[V = Int64]"]
    );
}
