//! An operation of several parameters as a function value, at an arrow that LABELS its
//! parameters.
//!
//! `Box` requires `O: WeakOrd[T = T]` and `cmp(x: Self, y: Self)` reads it. Passed where
//! `(p: Box[T = Int64, O = Descending], q: Box[T = Int64, O = Descending]) -> Int64` is
//! expected, `cmp` was refused: "`Box.cmp` used as a function value to have a satisfiable
//! `requires` … unsatisfiable `Box` requirement for bare operation `Box.cmp`". The same
//! arrow written without labels, `(Box[…], Box[…]) -> Int64`, loaded and answered 4.
//!
//! A reference to an operation is given its requirement's dictionary where it is written,
//! at the types the expected arrow says. Those are read by unifying the expected arrow's
//! parameters with the operation's own, and an operation of two parameters lifts to
//! `(_1: A, _2: B) -> R`. Unified as two DATA tuples, `(p: …, q: …)` and `(_1: …, _2: …)`
//! share no label: nothing was pinned and no dictionary could be built. The check that
//! admits the reference relates the two as parameter lists, by position
//! (`arrow_params_compatible`), and the pin relates them the same way now
//! (`unify_arrow_params`, in `eta_op_scoped_dicts`).
//!
//! It was not about two values of the operation's sort: any operation of two or more
//! parameters on a sort with a requirement was refused at a labelled arrow, and one of
//! one parameter never was — a single parameter's slot is its type, not a list.
//!
//! ## Back-out
//!
//! With the pin put back to a plain unify of the two tuples, all five rows of this file
//! fail, each at its labelled arrow, and no other of the 306 rows run with them (the
//! files that lift an operation to a function value or state a requirement on one —
//! wi420, wi775, wi782, wi787, wi1083, wi1087, wi1091, wi_0k8wd and that family; measured
//! 2026-10-13).
//!
//! PASS EITHER WAY, BY DESIGN, inside the rows: the arrow without labels, the lambda in
//! [`a_labelled_arrow_takes_an_operation_of_two_parameters`], and the positional half of
//! [`an_arrow_that_leaves_the_requirement_unwritten_is_refused_alike`].

use anthill_core::eval::{Interpreter, Value};
use crate::common::load_errors_of;

/// Two opposite orders of `Int64` beside its own and an order of `String` by length; `Box`,
/// one named requirement; `Bag`, the same requirement unnamed; `Pair2`, two named
/// requirements on one sort.
const DECLS: &str = r#"
  import anthill.prelude.{Int64, String, Ord, WeakOrd, Function}
  import anthill.prelude.Numeric.{sub}

  sort Descending
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end
  sort Ascending
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(a, b)
  end
  sort ByLength
    provides Ord[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(a.length(), b.length())
  end

  sort Box
    sort T = ?
    requires O: WeakOrd[T = T]
    entity box(a: T)
    operation cmp(x: Self, y: Self) -> Int64 = WeakOrd.compare(x.a, y.a)
    operation against(x: Self, n: T) -> Int64 = WeakOrd.compare(x.a, n)
    operation under(n: T, x: Self) -> Int64 = WeakOrd.compare(n, x.a)
  end
  sort Bag
    sort T = ?
    requires WeakOrd[T = T]
    entity bag(a: T)
    operation cmpBag(x: Self, y: Self) -> Int64 = WeakOrd.compare(x.a, y.a)
  end
  sort Pair2
    sort K = ?
    sort V = ?
    requires OK: WeakOrd[T = K]
    requires OV: WeakOrd[T = V]
    entity entry(k: K, v: V)
    operation keys(p: Self, q: Self) -> Int64 = WeakOrd.compare(p.k, q.k)
    operation vals(p: Self, q: Self) -> Int64 = WeakOrd.compare(p.v, q.v)
  end
"#;

/// A `Driver` holding `ops`.
fn program(ns: &str, ops: &str) -> String {
    format!(
        "namespace {ns}\n{DECLS}
  sort Driver
    import {ns}.Box.{{box, cmp, against, under}}
    import {ns}.Bag.{{bag, cmpBag}}
    import {ns}.Pair2.{{entry, keys, vals}}
{ops}  end
end
"
    )
}

/// `Driver.<op>()` on a FRESH interpreter, which panics on a dirty load.
fn value(src: &str, ns: &str, op: &str) -> i64 {
    let mut interp: Interpreter = crate::common::interp_for(src);
    match interp.call(&format!("{ns}.Driver.{op}"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{ns}.Driver.{op}: expected an Int64, got {other:?}"),
    }
}

/// THE REPORT'S PROGRAM: `cmp` takes two boxes. 3 against 7 is 4 under `Descending` and
/// -4 under `Ascending`. Labelled with names of the arrow's own, with the operation's
/// names, with the operation's names in the other order — an arrow's parameters are
/// taken by position — and as `Function[A = (p: …, q: …), B = …]`. The arrow without
/// labels and the lambda are the controls.
#[test]
fn a_labelled_arrow_takes_an_operation_of_two_parameters() {
    for (ov, expected) in [("Descending", 4), ("Ascending", -4)] {
        let ns = format!("fnlabel.two.{}", ov.to_lowercase());
        let b = format!("Box[T = Int64, O = {ov}]");
        let src = program(
            &ns,
            &format!(
                "    operation mk(n: Int64) -> {b} = box(a: n)
    operation labelled(f: (p: {b}, q: {b}) -> Int64, x: {b}, y: {b}) -> Int64 = f(x, y)
    operation ownNames(f: (x: {b}, y: {b}) -> Int64, x: {b}, y: {b}) -> Int64 = f(x, y)
    operation otherOrder(f: (y: {b}, x: {b}) -> Int64, x: {b}, y: {b}) -> Int64 = f(x, y)
    operation asFunction(f: Function[A = (p: {b}, q: {b}), B = Int64], x: {b}, y: {b}) -> Int64 = f(x, y)
    operation positional(f: ({b}, {b}) -> Int64, x: {b}, y: {b}) -> Int64 = f(x, y)
    operation runLabelled() -> Int64 = labelled(cmp, mk(3), mk(7))
    operation runOwnNames() -> Int64 = ownNames(cmp, mk(3), mk(7))
    operation runOtherOrder() -> Int64 = otherOrder(cmp, mk(3), mk(7))
    operation runAsFunction() -> Int64 = asFunction(cmp, mk(3), mk(7))
    operation runPositional() -> Int64 = positional(cmp, mk(3), mk(7))
    operation runLambda() -> Int64 = labelled(lambda (a, b) -> cmp(a, b), mk(3), mk(7))
"
            ),
        );
        for op in [
            "runLabelled",
            "runOwnNames",
            "runOtherOrder",
            "runAsFunction",
            "runPositional",
            "runLambda",
        ] {
            assert_eq!(value(&src, &ns, op), expected, "`{op}` under `O = {ov}`");
        }
    }
}

/// NOT ONLY TWO VALUES OF ITS SORT: a box and a number, in either order. 3 against 7 is 4
/// under `Descending`, and 7 against 3 is -4.
#[test]
fn a_labelled_arrow_takes_an_operation_with_a_parameter_of_another_type() {
    let ns = "fnlabel.mixed";
    let b = "Box[T = Int64, O = Descending]";
    let src = program(
        ns,
        &format!(
            "    operation mk(n: Int64) -> {b} = box(a: n)
    operation boxFirst(f: (p: {b}, n: Int64) -> Int64, x: {b}) -> Int64 = f(x, 7)
    operation boxLast(f: (n: Int64, p: {b}) -> Int64, x: {b}) -> Int64 = f(7, x)
    operation runAgainst() -> Int64 = boxFirst(against, mk(3))
    operation runUnder() -> Int64 = boxLast(under, mk(3))
"
        ),
    );
    assert_eq!(value(&src, ns, "runAgainst"), 4, "`against(x: Self, n: T)`");
    assert_eq!(value(&src, ns, "runUnder"), -4, "`under(n: T, x: Self)`");
}

/// TWO NAMED REQUIREMENTS, each read at its own: the keys by length, `"bob"` against
/// `"amyy"` -1; the values 3 against 7 by `OV`.
#[test]
fn a_labelled_arrow_takes_an_operation_of_a_sort_with_two_requirements() {
    for (ov, expected) in [("Descending", 4), ("Ascending", -4)] {
        let ns = format!("fnlabel.pair.{}", ov.to_lowercase());
        let t = format!("Pair2[K = String, V = Int64, OK = ByLength, OV = {ov}]");
        let src = program(
            &ns,
            &format!(
                "    operation mk(k: String, v: Int64) -> {t} = entry(k: k, v: v)
    operation ap(f: (p: {t}, q: {t}) -> Int64, x: {t}, y: {t}) -> Int64 = f(x, y)
    operation runKeys() -> Int64 = ap(keys, mk(\"bob\", 3), mk(\"amyy\", 7))
    operation runVals() -> Int64 = ap(vals, mk(\"bob\", 3), mk(\"amyy\", 7))
"
            ),
        );
        assert_eq!(value(&src, &ns, "runKeys"), -1, "the keys by `OK = ByLength`, `OV = {ov}`");
        assert_eq!(value(&src, &ns, "runVals"), expected, "the values by `OV = {ov}`");
    }
}

/// THE REQUIREMENT WITHOUT A NAME, answered by `Int64`'s own order: 3 is below 7.
#[test]
fn a_labelled_arrow_takes_an_operation_of_a_sort_with_an_unnamed_requirement() {
    let ns = "fnlabel.unnamed";
    let b = "Bag[T = Int64]";
    let src = program(
        ns,
        &format!(
            "    operation mk(n: Int64) -> {b} = bag(a: n)
    operation labelled(f: (p: {b}, q: {b}) -> Int64, x: {b}, y: {b}) -> Int64 = f(x, y)
    operation positional(f: ({b}, {b}) -> Int64, x: {b}, y: {b}) -> Int64 = f(x, y)
    operation runLabelled() -> Int64 = labelled(cmpBag, mk(3), mk(7))
    operation runPositional() -> Int64 = positional(cmpBag, mk(3), mk(7))
"
        ),
    );
    assert_eq!(value(&src, ns, "runLabelled"), -1, "labelled");
    assert_eq!(value(&src, ns, "runPositional"), -1, "without labels");
}

/// AN ARROW THAT LEAVES THE NAMED REQUIREMENT UNWRITTEN IS REFUSED, WITH LABELS AS
/// WITHOUT. `Box[T = Int64]` says no provider, and `Int64` has two here: the reference
/// cannot be given a dictionary. Without labels that was the refusal already; with them
/// the refusal was the one for a requirement nothing could satisfy, which named no
/// provider.
#[test]
fn an_arrow_that_leaves_the_requirement_unwritten_is_refused_alike() {
    let b = "Box[T = Int64]";
    for (ns, params) in [
        ("fnlabel.unwritten.labelled", format!("(p: {b}, q: {b})")),
        ("fnlabel.unwritten.positional", format!("({b}, {b})")),
    ] {
        let errors = load_errors_of(&program(
            ns,
            &format!(
                "    operation mk(n: Int64) -> Box[T = Int64, O = Descending] = box(a: n)
    operation ap(f: {params} -> Int64, x: {b}, y: {b}) -> Int64 = f(x, y)
    operation run() -> Int64 = ap(cmp, mk(3), mk(7))
"
            ),
        ));
        let joined = errors.join("\n");
        for token in [
            "used as a function value",
            "ambiguous among providers",
            "anthill.prelude.Int64",
            &format!("{ns}.Descending"),
        ] {
            assert!(
                joined.contains(token),
                "`{params} -> Int64`: the refusal names `{token}`; got {errors:#?}"
            );
        }
    }
}
