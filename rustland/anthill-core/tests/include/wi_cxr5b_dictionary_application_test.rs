//! WI-20261122-CXR5B — A DICTIONARY CARRIES THE APPLICATION IT IS FOR, where its provider provides
//! the spec at more than one (decision 1 of `docs/design/spec-carrier-set.md`).
//!
//! A dictionary named its provider and nothing else, `Dictionary(impl: W)`. A provider that
//! provides one spec at two applications and supplies an operation apart at them — `W provides
//! Tag[T = Foo, tag = tagFoo]` and `Tag[T = Bar, tag = tagBar]` — loaded, and a call through a
//! generic `requires` died at run: "a dictionary names its provider, not the application it is
//! for". Since step 3 the applications are told apart by every type-var, so a provider binding
//! `Coll[C = Foo, Elem = Int64]` and `Coll[C = Foo, Elem = String]` died the same way. Such a
//! dictionary now holds the application under an `at` key, `Dictionary(impl: W, at:
//! SortView(Tag, T = Foo))`, on its three carriers; the dispatch, `Dictionary.resolveOp` and
//! `Dictionary.ops` read the operation off the provision there; `Dictionary.at` reads it.
//!
//! WHAT FAILS IF THIS IS BACKED OUT, and what passes either way, is said at each row. MEASURED
//! 2026-11-22: each call row marked FAILS was refused at run, "cannot dispatch through the
//! dictionary"; the reflect row failed at the printed dictionary, which held no `at`.

use anthill_core::eval::{HostValue, Interpreter, Value};

use crate::common::{interp_for, show_value};

fn int(interp: &mut Interpreter, entry: &str) -> i64 {
    match interp.call(entry, &HostValue::all(&[])).map(|h| h.value) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{entry}` answered no Int64: {other:?}"),
    }
}

/// `Tag[T]`, `Foo`, `Bar` and a provider `WT` writing `provs`, with `viaReq` dispatching through
/// a generic `requires`.
fn tag_program(ns: &str, tag_decl: &str, provs: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.Int64
  import anthill.realization.runtime.Dictionary
  sort Tag
    sort T = ?
    {tag_decl}
  end
  sort Foo
    entity foo
  end
  sort Bar
    entity bar
  end
  sort WT
{provs}
  end
  operation viaReq[X](x: X) -> Int64 requires Tag[T = X] = Tag.tag(x)
  operation go() -> Int64 = viaReq(foo) + 10 * viaReq(bar)
  operation dFoo() -> Tag[T = Foo] = Dictionary.instance[Tag[T = Foo]]()
end
"#
    )
}

const APART: &str = r#"    provides Tag[T = Foo, tag = WT.tagFoo]
    provides Tag[T = Bar, tag = WT.tagBar]
    operation tagFoo(x: Foo) -> Int64 = 1
    operation tagBar(x: Bar) -> Int64 = 2"#;

/// A generic call reaches the member each application binds. FAILS backed out: refused at run.
#[test]
fn a_call_through_a_requires_runs_the_member_of_the_application_its_dictionary_is_for() {
    let ns = "wicxr5bda.apart";
    let mut interp = interp_for(&tag_program(ns, "operation tag(x: T) -> Int64", APART));
    assert_eq!(int(&mut interp, &format!("{ns}.go")), 21);
}

/// A defaulted operation bound at one application runs the binding there and the default at the
/// other. FAILS backed out: refused at run.
#[test]
fn a_defaulted_operation_bound_at_one_application_runs_its_default_at_the_other() {
    let ns = "wicxr5bda.default";
    let provs = r#"    provides Tag[T = Foo, tag = WT.tagFoo]
    provides Tag[T = Bar]
    operation tagFoo(x: Foo) -> Int64 = 1"#;
    let mut interp = interp_for(&tag_program(ns, "operation tag(x: T) -> Int64 = 0", provs));
    assert_eq!(int(&mut interp, &format!("{ns}.go")), 1);
}

/// Two applications at one `C` that bind `Elem` apart (step 3's grouping): the call's `Elem`
/// chooses. FAILS backed out: refused at run.
#[test]
fn two_applications_apart_in_a_type_var_the_operation_does_not_take_a_value_of() {
    let ns = "wicxr5bda.elem";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
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
  operation viaInt[X](x: X) -> Int64 requires Coll[C = X, Elem = Int64] = Coll.first(x)
  operation viaStr[X](x: X) -> String requires Coll[C = X, Elem = String] = Coll.first(x)
  operation go() -> Int64 = viaInt(foo) + 10 * String.length(viaStr(foo))
end
"#
    );
    let mut interp = interp_for(&src);
    assert_eq!(int(&mut interp, &format!("{ns}.go")), 31);
}

/// The reflect faces read the application: `Dictionary.at` is the spec view, and `resolveOp`
/// and `ops` answer the member bound there, as the dispatch does. FAILS backed out, at the printed
/// dictionary, which held no `at` (and the accessor is new).
#[test]
fn the_reflect_faces_read_the_application_the_dispatch_reads() {
    const DICT: &str = "anthill.realization.runtime.Dictionary";
    let ns = "wicxr5bda.reflect";
    let mut interp = interp_for(&tag_program(ns, "operation tag(x: T) -> Int64", APART));
    let d = interp.call(&format!("{ns}.dFoo"), &HostValue::all(&[])).map(|h| h.value).expect("dFoo");
    let d = interp.carried(d);

    let printed = show_value(interp.kb(), &d);
    assert!(printed.contains("at: SortView(") && printed.contains("T: Foo"), "the dictionary: {printed}");
    let at = interp.call(&format!("{DICT}.at"), &HostValue::all(&[d.clone()])).map(|h| h.value).expect("at");
    let at = show_value(interp.kb(), &at);
    assert!(
        at.starts_with("some(") && at.contains("SortView(") && at.contains("T: Foo") && !at.contains("Bar"),
        "`Dictionary.at` of a provider at two applications: {at}"
    );

    let spec_op = crate::common::symbol_term(&mut interp, &format!("{ns}.Tag.tag"));
    let resolved = interp
        .call(&format!("{DICT}.resolveOp"), &HostValue::all(&[d.clone(), spec_op]))
        .map(|h| h.value)
        .expect("resolveOp");
    let Value::OpRef { op, .. } = resolved else {
        panic!("expected an OpRef, got {resolved:?}");
    };
    assert_eq!(interp.kb().qualified_name_of(op), format!("{ns}.WT.tagFoo"));

    let ops = interp.call(&format!("{DICT}.ops"), &HostValue::all(&[d])).map(|h| h.value);
    assert!(ops.is_ok(), "`ops` answers where `resolveOp` does: {ops:?}");
}

/// CONTROL: a provider at ONE application carries none, and answers as before. Its call and its
/// printed dictionary pass either way, by design; MEASURED backed out, the row fails only at the
/// `Dictionary.at` read, the accessor being new.
#[test]
fn a_provider_at_one_application_carries_none() {
    const DICT: &str = "anthill.realization.runtime.Dictionary";
    let ns = "wicxr5bda.one";
    let provs = r#"    provides Tag[T = Foo, tag = WT.tagFoo]
    operation tagFoo(x: Foo) -> Int64 = 1"#;
    let src = tag_program(ns, "operation tag(x: T) -> Int64", provs).replace(" + 10 * viaReq(bar)", "");
    let mut interp = interp_for(&src);
    assert_eq!(int(&mut interp, &format!("{ns}.go")), 1);
    let d = interp.call(&format!("{ns}.dFoo"), &HostValue::all(&[])).map(|h| h.value).expect("dFoo");
    let d = interp.carried(d);
    assert!(!show_value(interp.kb(), &d).contains("at:"), "the dictionary: {}", show_value(interp.kb(), &d));
    let at = interp.call(&format!("{DICT}.at"), &HostValue::all(&[d])).map(|h| h.value).expect("at");
    assert!(show_value(interp.kb(), &at).starts_with("none"), "{}", show_value(interp.kb(), &at));
}

/// CONTROL: a provider supplying ALIKE at its two applications — its own member — answers at
/// both. Its dictionaries carry the application now, which the dispatch does not need. Passes
/// either way, by design.
#[test]
fn a_provider_supplying_alike_at_two_applications_answers_at_both() {
    let ns = "wicxr5bda.alike";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.Int64
  sort Desc
    sort T = ?
    operation name() -> Int64
  end
  sort Foo
    entity foo
  end
  sort Bar
    entity bar
  end
  sort W
    provides Desc[T = Foo]
    provides Desc[T = Bar]
    operation name() -> Int64 = 3
  end
  operation viaDict[X]() -> Int64 requires Desc[T = X] = Desc.name[T = X]()
  operation go() -> Int64 = viaDict[X = Foo]() + 10 * viaDict[X = Bar]()
end
"#
    );
    let mut interp = interp_for(&src);
    assert_eq!(int(&mut interp, &format!("{ns}.go")), 33);
}
