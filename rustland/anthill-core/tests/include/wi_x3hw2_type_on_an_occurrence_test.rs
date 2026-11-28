//! WI-20261128-X3HW2 — THREE READERS THAT READ A TYPE ON THE TERM CARRIER ALONE, found by the
//! node-carrier control (`ANTHILL_TEST_NODE_CARRIER=1`, `rustland/CLAUDE.md`), under which six
//! `anthill-core` rows changed verdict. Each is proved here WITHOUT the switch: a type alias
//! written bare rides an occurrence on its own (`TypeNode::Aliased`), as the switch puts every
//! sort, and each row writes the type through one where the reader reads it.
//!
//! THE RULE. A reader of a type gives one answer for the type, whichever carrier it rides.
//!
//! BEFORE, each MEASURED on the rows below with the fix backed out:
//!
//!   * the application a dictionary is for (`typing::dictionary_application_view`) was read
//!     off a binding that is a term alone, and a binding on an occurrence left the dictionary
//!     with none (`Dictionary(impl: W)`, no `at`). A provider at two applications that
//!     supplies an operation apart at them was then refused at run, "a dictionary names its
//!     provider, not the application it is for". Under the switch: the four rows of
//!     `wi_cxr5b_dictionary_application_test` (two), `wi_cxr5b_own_two_applications_test` and
//!     `wi_qg6zr_witness_at_the_application_test`.
//!   * the provider a bracket names for a `Self` result (`check_apply_call`, the arm of
//!     §5.4's second amendment) was typed at what the call fixed only where the fixed type
//!     was a term: `Src.make[Src = Ones, T = I]()` over `sort I = Int64` was `Ones[T = o.T]`,
//!     and a use at `Ones[T = Int64]` was refused. Under the switch:
//!     `wi_cxr5b_concrete_bracket_test::a_bracketed_self_result_is_the_provider_at_what_the_call_fixed`.
//!   * a later load's provision was told from a sealed one by its ROW
//!     (`eq_derive::EqualityProvision`). A fact head that is a term and one that is an
//!     occurrence dedup in two spaces (`KnowledgeBase::value_fact_dedup`, WI-815, kept), so a
//!     restatement written through an alias of a provision an earlier load DERIVED was a
//!     second row, and the equality closure refused it, "its own provision of `Eq` for it is
//!     new". It is keyed by the row's head through the carrier-neutral view now. Under the
//!     switch: `wi_szkv7_later_equality_test::a_later_restatement_of_a_derived_provision_is_accepted`.
//!
//! CONTROLS — MEASURED 2026-11-28, each fix backed out on its own:
//!
//!   `dictionary_application_view` reading a term alone — FAIL:
//!     a_requirement_written_through_an_alias_is_dispatched_at_its_application
//!     a_dictionary_built_at_a_type_written_through_an_alias_carries_its_application
//!   the bracketed `Self` result built from terms alone — FAIL:
//!     a_bracket_fixing_a_type_through_an_alias_types_the_provider_at_it
//!   the equality closure keyed by the row — FAIL:
//!     a_later_restatement_through_an_alias_of_a_derived_provision_is_accepted
//!
//!   `the_written_out_twins_answer_alike` passes either way, by design: it is each row's
//!   program with the type written out, which every reader above read already.

use anthill_core::eval::{self, HostValue, Interpreter, Value};
use anthill_core::kb::load::LoadOptions;

use crate::common::{expect_loaded, interp_for, load_in_a_later_call, load_kb_with, show_value};

fn int(interp: &mut Interpreter, entry: &str) -> i64 {
    match interp.call(entry, &HostValue::all(&[])).map(|h| h.value) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{entry}` answered no Int64: {other:?}"),
    }
}

/// `WB` provides `Coll` at two applications one `C` apart in `Elem`, supplying `first` apart
/// at them; `viaInt` requires the `Elem = Int64` one, written `elem`.
fn coll_program(ns: &str, elem: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort I = Int64
  sort Coll
    sort C = ?
    sort Elem = ?
    operation first(c: C) -> Elem
  end
  sort Foo
    entity foo
  end
  sort WB
    provides Coll[C = Foo, Elem = Int64, first = WB.f1]
    provides Coll[C = Foo, Elem = String, first = WB.f2]
    operation f1(c: Foo) -> Int64 = 1
    operation f2(c: Foo) -> String = "two"
  end
  operation viaInt[X](x: X) -> Int64 requires Coll[C = X, Elem = {elem}] = Coll.first(x)
  operation viaStr[X](x: X) -> String requires Coll[C = X, Elem = String] = Coll.first(x)
  operation go() -> Int64 = viaInt(foo) + 10 * String.length(viaStr(foo))
end
"#
    )
}

/// The dispatch through a requirement whose binding is written through an alias reads the
/// application the binding names. FAILS backed out: refused at run, "a dictionary names its
/// provider, not the application it is for".
#[test]
fn a_requirement_written_through_an_alias_is_dispatched_at_its_application() {
    let ns = "wix3hw2.req";
    assert_eq!(int(&mut interp_for(&coll_program(ns, "I")), &format!("{ns}.go")), 31);
}

/// `Tag` provided at `T = Foo` and `T = Bar`, `tag` supplied apart; `dFoo` builds the
/// dictionary at `Tag[T = {foo}]`.
fn tag_program(ns: &str, foo: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.Int64
  import anthill.realization.runtime.Dictionary
  sort Tag
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort Foo
    entity foo
  end
  sort F = Foo
  sort Bar
    entity bar
  end
  sort WT
    provides Tag[T = Foo, tag = WT.tagFoo]
    provides Tag[T = Bar, tag = WT.tagBar]
    operation tagFoo(x: Foo) -> Int64 = 1
    operation tagBar(x: Bar) -> Int64 = 2
  end
  operation dFoo() -> Tag[T = {foo}] = Dictionary.instance[Tag[T = {foo}]]()
end
"#
    )
}

/// The dictionary built at `Tag[T = F]`, `F` an alias of `Foo`, carries the application it is
/// for, and `resolveOp` answers the member bound there. FAILS backed out, at the printed
/// dictionary: `Dictionary(impl: WT)`, no `at`.
#[test]
fn a_dictionary_built_at_a_type_written_through_an_alias_carries_its_application() {
    const DICT: &str = "anthill.realization.runtime.Dictionary";
    let ns = "wix3hw2.dict";
    let mut interp = interp_for(&tag_program(ns, "F"));
    let d = interp.call(&format!("{ns}.dFoo"), &HostValue::all(&[])).map(|h| h.value).expect("dFoo");
    let d = interp.carried(d);
    let printed = show_value(interp.kb(), &d);
    assert!(printed.contains("at: SortView(") && printed.contains("T: Foo"), "the dictionary: {printed}");
    let spec_op = crate::common::symbol_term(&mut interp, &format!("{ns}.Tag.tag"));
    let resolved = interp
        .call(&format!("{DICT}.resolveOp"), &HostValue::all(&[d, spec_op]))
        .map(|h| h.value)
        .expect("resolveOp");
    let Value::OpRef { op, .. } = resolved else {
        panic!("expected an OpRef, got {resolved:?}");
    };
    assert_eq!(interp.kb().qualified_name_of(op), format!("{ns}.WT.tagFoo"));
}

/// The self-representing `Src`, provided by `Ones` at its own `T`, and `useAt` taking a
/// `Ones[T = Int64]`; `go` binds `Src.make[Src = Ones, T = {t}]()` and hands it to `useAt`.
fn src_program(ns: &str, t: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort I = Int64
  sort Src
    sort T = ?
    operation next(s: Self) -> Int64
    operation make() -> Self
  end
  sort Ones
    sort T = ?
    entity ones
    provides Src[T = T]
    operation next(s: Ones) -> Int64 = 1
    operation make() -> Self = ones
  end
  sort Twos
    sort T = ?
    entity twos
    provides Src[T = T]
    operation next(s: Twos) -> Int64 = 2
    operation make() -> Self = twos
  end
  operation useAt(o: Ones[T = Int64]) -> Int64 = 3
  sort Driver
    operation go() -> Int64 =
      let o = Src.make[Src = Ones, T = {t}]()
      useAt(o)
  end
end
"#
    )
}

/// A bracket fixing `T` through an alias types the `Self` result at it: `o` is a `Ones[T =
/// Int64]`. FAILS backed out: refused at load, "expected Ones[T = Int64], got Ones[T = o.T]".
#[test]
fn a_bracket_fixing_a_type_through_an_alias_types_the_provider_at_it() {
    let ns = "wix3hw2.src";
    assert_eq!(int(&mut interp_for(&src_program(ns, "I")), &format!("{ns}.Driver.go")), 3);
}

/// `Point`, whose equality its load derives, and `Pt`, an alias of it.
const POINT: &str = r#"
namespace wix3hw2.eq
  import anthill.prelude.{Int64}
  sort Point
    entity point(x: Int64, y: Int64)
  end
  sort Pt = Point
end
"#;

/// A later load restating the derived `PartialEq` and `Eq` of `Point`, writing it `point`.
fn restatement(point: &str) -> String {
    format!(
        "namespace wix3hw2.eq.Point\n  \
           import anthill.prelude.{{Eq, PartialEq}}\n  \
           import wix3hw2.eq.{{Pt}}\n  \
           provides PartialEq[T = {point}]\n  \
           provides Eq[T = {point}]\n\
         end\n"
    )
}

/// What `eq` answers over two equal points and two that differ, after the restatement.
const PROBE: &str = r#"
namespace wix3hw2.eq.check
  import anthill.prelude.{Bool}
  import wix3hw2.eq.{Point}
  import wix3hw2.eq.Point.{point}
  sort Check
    import anthill.prelude.PartialEq.{eq}
    operation check() -> Bool =
      if eq(point(x: 1, y: 2), point(x: 1, y: 3)) then false
      else eq(point(x: 1, y: 2), point(x: 1, y: 2))
  end
end
"#;

fn restated_then_checked(point: &str) -> bool {
    let mut kb = load_kb_with(POINT);
    expect_loaded(load_in_a_later_call(&mut kb, &restatement(point), LoadOptions::default()));
    expect_loaded(load_in_a_later_call(&mut kb, PROBE, LoadOptions::default()));
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp);
    match interp.call("wix3hw2.eq.check.Check.check", &HostValue::all(&[])).map(|h| h.value) {
        Ok(Value::Bool(b)) => b,
        other => panic!("`check` did not run to a Bool: {other:?}"),
    }
}

/// A restatement through an alias of what the earlier load derived is no change to the
/// sort's equality (kernel-language §8.3): the later load is accepted and `eq` answers as
/// before. FAILS backed out: refused, "its own provision of `Eq` for it is new; its own
/// provision of `PartialEq` for it is new".
#[test]
fn a_later_restatement_through_an_alias_of_a_derived_provision_is_accepted() {
    assert!(restated_then_checked("Pt"));
}

/// CONTROL: each program above with the type written out. Passes either way, by design.
#[test]
fn the_written_out_twins_answer_alike() {
    assert_eq!(int(&mut interp_for(&coll_program("wix3hw2.req.out", "Int64")), "wix3hw2.req.out.go"), 31);
    let ns = "wix3hw2.dict.out";
    let mut interp = interp_for(&tag_program(ns, "Foo"));
    let d = interp.call(&format!("{ns}.dFoo"), &HostValue::all(&[])).map(|h| h.value).expect("dFoo");
    let d = interp.carried(d);
    assert!(show_value(interp.kb(), &d).contains("at: SortView("), "{}", show_value(interp.kb(), &d));
    assert_eq!(int(&mut interp_for(&src_program("wix3hw2.src.out", "Int64")), "wix3hw2.src.out.Driver.go"), 3);
    assert!(restated_then_checked("Point"));
}
