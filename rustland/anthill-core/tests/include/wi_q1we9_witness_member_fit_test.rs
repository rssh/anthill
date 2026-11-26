//! WI-20261126-Q1WE9 — A WITNESS'S OWN MEMBER SUPPLIES A CARRIER IT WITNESSES ONLY WHERE IT FITS
//! THERE (kernel-language §8.7, *A member that does not fit is no supplier*).
//!
//! `Point` is a composite, with an `eq` of its own — derived, or written as `eq(a: Point, b:
//! Point)` — and it is also the WITNESS of `Other`'s equality: its provisions `PartialEq[T =
//! Other]` and `Eq[T = Other]`. The witness route took the provider's own member as a supplier
//! of every carrier the provider witnesses, its fit decided once for the provider, at any of its
//! provisions — and `Point.eq` fits at `Point`. MEASURED before the change, one load of the three
//! sources each time:
//!
//! * with `eq = Other.oeq` bound by the provision: refused, an ambiguous dispatch between
//!   `Point.eq` and `Other.oeq` — at the call for the derived member, at load as well for the
//!   written one;
//! * with nothing bound and a written `Point.eq` answering `true`: LOADED, and `eq(o(n: 1),
//!   o(n: 2))` answered `true` — `Point.eq` handed `Other`'s values, where the fields differ.
//!
//! The witness's member is now judged at the witness's provision for each carrier it witnesses
//! (`typing::record_members_that_supply_nothing`, read through `typing::witness_own_op`):
//! `Point.eq` takes `Point`s and supplies no `Other`. So the binding answers alone, and with no
//! binding nothing answers `Other` — WI-20261121-TV0PA's refusal, which now names the member it
//! passed over.
//!
//! WHAT FAILS WHEN (each measured by making the change and running this file):
//!
//! * the witness verdict left empty (`set_witness_members_that_supply_nothing` given nothing):
//!   the two `…_answers_beside_…` rows and both `…_answers_nothing_…` rows, and
//!   `wi_szkv7_later_equality_test::an_earlier_sort_witnessing_a_later_ones_equality_is_accepted`.
//! * the refusal not naming the passed-over member (`passed_over` left empty): both
//!   `…_answers_nothing_…` rows.
//!
//! WI-20261126-DHB0C moved one row: a written `Point.eq(a: Point, b: Point)` with no provision of
//! `Point`'s own is the author's equality of `Point`s, and is held to writing one, as a `Point`
//! that witnesses nothing is. It loaded here only because the provider's verdict was reached at
//! its witness provision first, where the member does not fit. The written-member row writes
//! `provides PartialEq[T = Point]`, and `a_written_eq_with_no_provision_of_its_own_is_held_to_one`
//! is the refusal without it.
//!
//! `a_witness_whose_eq_takes_the_witnessed_values_still_answers` passes through both BY DESIGN:
//! it is the witness the route is for, and the control that the verdict passes it.

use anthill_core::eval::value::Value;
use anthill_core::eval::{self, Interpreter};
use anthill_core::kb::KnowledgeBase;

use crate::common::try_load_kb_with_files;

/// `Point`, with `point_member` among its declarations, in `test.q1we9.<ns>`.
fn point(ns: &str, point_member: &str) -> String {
    format!(
        "namespace test.q1we9.{ns}\n  import anthill.prelude.{{Int64, Bool, PartialEq}}\n  sort Point\n    \
         entity point(x: Int64, y: Int64)\n{point_member}  end\nend\n"
    )
}

/// `Other`, declared in `Point`'s namespace, with `Point`'s provisions of its equality —
/// binding `eq` as `binding` writes (`""` for none).
fn witness(ns: &str, binding: &str) -> String {
    format!(
        "namespace test.q1we9.{ns}.Point\n  import anthill.prelude.{{Eq, PartialEq, Bool, Int64}}\n  \
         sort Other\n    entity o(n: Int64)\n    operation oeq(a: Other, b: Other) -> Bool = true\n  \
         end\n  provides PartialEq[T = Other{binding}]\n  provides Eq[T = Other]\nend\n"
    )
}

/// The calls each row drives: `other()` compares two `Other`s whose fields differ, `point()` two
/// `Point`s that differ.
fn probe(ns: &str) -> String {
    format!(
        "namespace test.q1we9.{ns}.chk\n  import anthill.prelude.{{Bool}}\n  sort Check\n    \
         import anthill.prelude.PartialEq.{{eq}}\n    \
         operation other() -> Bool = eq(test.q1we9.{ns}.Point.Other.o(n: 1), test.q1we9.{ns}.Point.Other.o(n: 2))\n    \
         operation point() -> Bool = eq(test.q1we9.{ns}.Point.point(x: 1, y: 2), test.q1we9.{ns}.Point.point(x: 1, y: 3))\n  \
         end\nend\n"
    )
}

fn load(ns: &str, point_member: &str, binding: &str) -> Result<KnowledgeBase, Vec<String>> {
    let (p, w, c) = (point(ns, point_member), witness(ns, binding), probe(ns));
    try_load_kb_with_files(&[p.as_str(), w.as_str(), c.as_str()])
}

fn bool_of(kb: KnowledgeBase, op: &str) -> bool {
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp);
    match interp.call(op, &anthill_core::eval::HostValue::all(&[])).map(|h| h.value) {
        Ok(Value::Bool(b)) => b,
        other => panic!("`{op}` did not run to a Bool: {other:?}"),
    }
}

/// `(other(), point())` of the program, which must load.
fn answers(ns: &str, point_member: &str, binding: &str) -> (bool, bool) {
    let kb = load(ns, point_member, binding).unwrap_or_else(|e| panic!("{ns} must load: {e:#?}"));
    let other = bool_of(kb.deep_clone().expect("copy"), &format!("test.q1we9.{ns}.chk.Check.other"));
    (other, bool_of(kb, &format!("test.q1we9.{ns}.chk.Check.point")))
}

const WRITTEN_FALSE: &str = "    operation eq(a: Point, b: Point) -> Bool = false\n";
/// `Point`'s written `eq` with the provision of its own it is held to (WI-20261126-DHB0C).
const WRITTEN_FALSE_PROVIDED: &str =
    "    provides PartialEq[T = Point]\n    operation eq(a: Point, b: Point) -> Bool = false\n";
const WRITTEN_TRUE: &str = "    operation eq(a: Point, b: Point) -> Bool = true\n";

/// The ticket's program: `Point`'s `eq` derived, and the provision binding `Other.oeq`. `Other`'s
/// `eq` is the binding, `true` where the fields differ; `Point`'s is its derived one.
#[test]
fn a_witness_binding_the_eq_answers_beside_its_derived_member() {
    assert_eq!(answers("derived", "", ", eq = Other.oeq"), (true, false));
}

/// The same with `Point`'s `eq` written: no tie with the binding, and `Point` compares by its own.
/// `Point` writes its own `provides PartialEq[T = Point]`, as any composite writing an `eq` of its
/// own does (WI-20261126-DHB0C, the next row).
#[test]
fn a_witness_binding_the_eq_answers_beside_its_written_member() {
    assert_eq!(answers("written", WRITTEN_FALSE_PROVIDED, ", eq = Other.oeq"), (true, false));
}

/// WI-20261126-DHB0C — A WRITTEN `eq` WITH NO PROVISION OF ITS OWN IS HELD TO ONE, whatever its
/// sort witnesses. `Point.eq(a: Point, b: Point)` is the author's equality of `Point`s, so nothing
/// is derived for `Point` (§8.3, a boundary), and with no `provides PartialEq` for `Point` a
/// comparison of two is refused, as it is for a `Point` that witnesses nothing. This program loaded
/// before DHB0C only because the provider's verdict on `Point.eq` was reached at its witness
/// provision `PartialEq[T = Other]` first, where the member does not fit, so the derivation gave
/// `Point` a `PartialEq` the written `eq` then backed. Fails with that change backed out.
#[test]
fn a_written_eq_with_no_provision_of_its_own_is_held_to_one() {
    match load("bare", WRITTEN_FALSE, ", eq = Other.oeq") {
        Ok(_) => panic!("`Point`'s own `eq` with no provision of `Point`'s must be refused"),
        Err(errors) => assert!(
            errors.iter().any(|e| e.contains("PartialEq[T = test.q1we9.bare.Point]")),
            "refused at the comparison of two `Point`s: {errors:#?}"
        ),
    }
}

/// `Point.eq` written to answer `true`, nothing bound: it was handed `Other`'s values and
/// answered `true`. It takes `Point`s, so nothing answers `Other`, and the load says so naming it.
#[test]
fn a_witness_whose_written_eq_takes_its_own_values_answers_nothing_for_another() {
    assert_passed_over("wtrue", WRITTEN_TRUE);
}

/// The same with `Point`'s `eq` derived.
#[test]
fn a_witness_whose_derived_eq_takes_its_own_values_answers_nothing_for_another() {
    assert_passed_over("dnone", "");
}

fn assert_passed_over(ns: &str, point_member: &str) {
    let errors = match load(ns, point_member, "") {
        Err(errors) => errors,
        Ok(_) => panic!("{ns}: nothing answers `Other`'s `eq`, and the load must say so"),
    };
    let other = format!("test.q1we9.{ns}.Point.Other");
    let member = format!("`test.q1we9.{ns}.Point.eq`");
    assert!(
        errors.iter().any(|e| {
            e.contains(&format!("`{other}`'s equality is provided by the witness"))
                && e.contains("none is written that takes")
                && e.contains(&member)
        }),
        "{ns}: refused as no `eq` answering `{other}`, naming {member}: {errors:#?}"
    );
}

/// THE CONTROL: a witness whose `eq` takes the witnessed sort's values is the witness the route
/// is for, and still answers. Passes either way by design.
#[test]
fn a_witness_whose_eq_takes_the_witnessed_values_still_answers() {
    let src = "namespace test.q1we9.ok\n  import anthill.prelude.{Eq, PartialEq, Int64, Bool}\n  \
               sort Other\n    entity o(n: Int64)\n  end\n  \
               sort W\n    provides PartialEq[T = Other]\n    provides Eq[T = Other]\n    \
               operation eq(a: Other, b: Other) -> Bool = true\n  end\n  \
               sort Check\n    import anthill.prelude.PartialEq.{eq}\n    \
               operation other() -> Bool = eq(Other.o(n: 1), Other.o(n: 2))\n  end\nend\n";
    let kb = try_load_kb_with_files(&[src]).unwrap_or_else(|e| panic!("must load: {e:#?}"));
    assert!(bool_of(kb, "test.q1we9.ok.Check.other"), "`W.eq` answers `Other`'s equality");
}
