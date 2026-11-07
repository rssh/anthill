//! WI-20260902-40KSW — a dotted name written where a value is, and given no value by any
//! reading, is refused ONCE, saying what the name is: a namespace has no value, a segment
//! names nothing, or a segment is `internal` to a scope the text is not written in. It was
//! refused once per SEGMENT, each segment told "expected resolved name, got unresolved" —
//! a namespace, a sort and a constructor among them that resolved.
//!
//! Measured on a3082618 (`zz.inner` a namespace, `zz.Q` a sort holding `internal sort Sec`
//! and `internal const hidden`), the same in both bodies:
//!
//! | written | before | after |
//! |---|---|---|
//! | `zz.inner = 7` | 2 × "unresolved" | 1, `zz.inner` is a namespace |
//! | `zz = 7` | 1 × "unresolved" | 1, `zz` is a namespace |
//! | `zz.nosuch.x = 7` | 3 × "unresolved" | 1, `zz` declares no `nosuch` |
//! | `nosuch.x = 7` | 2 × "unresolved" | 1, no `nosuch` is visible |
//! | `zz.Q.Sec`, `zz.Q.hidden.x` | 1 / 2 × "unresolved" | 1, internal to `zz.Q` |
//!
//! The rows that already answered once — a rule, a constructor, a sort by a path — keep
//! their errors ([`the_names_with_a_reading_keep_it`]), and so does a name no scope has,
//! written alone ([`a_name_alone_that_names_nothing_keeps_its_refusal`]).
//!
//! WHICH ROWS FAIL WITH A PART BACKED OUT, each alone, measured with temporary switches:
//!   * the typer's rung over the chain (`dotted_name_without_value` answering `None`):
//!     [`a_namespace_by_a_path_is_refused_once_as_a_namespace`],
//!     [`a_path_that_names_nothing_is_refused_once`],
//!     [`a_first_segment_that_names_nothing_is_refused_once`],
//!     [`an_internal_name_by_a_path_is_refused_as_internal`] — both bodies of each —
//!     [`a_written_field_access_call_keeps_its_argument`], whose first argument is a
//!     dotted name, and [`every_value_position_reads_the_name_whole`].
//!   * the namespace arm of `check_bare_ref`: [`a_namespace_alone_is_refused_as_a_namespace`].
//!   * the operation-body walk's dot stamp on the chain it did not read: the
//!     operation-body half of the five rows of the rung.
//!   * a sort prefix read as the chain's first segment:
//!     [`an_internal_name_by_a_path_is_refused_as_internal`].
//!
//! [`the_names_with_a_reading_keep_it`], [`a_name_alone_that_names_nothing_keeps_its_refusal`]
//! and [`a_value_prefix_is_read_as_before`] pass either way, by design: they are the bound.

use crate::common::{assert_refused_naming, interp_for, load_errors_of};
use anthill_core::eval::Value;

const DECL: &str = "\
namespace zz
  import anthill.prelude.Int64
  sort Color
    entity red
  end
  sort P
    entity pt(x: Int64, y: Int64)
  end
  sort Q
    const origin: P = P.pt(3, 4)
    internal const hidden: P = P.pt(3, 4)
    internal sort Sec
      entity sx
    end
  end
end
namespace zz.inner
  fact b(1)
  rule rel(1) :- b(1)
end
";

/// `body` compared with `7`, in a rule body and in an operation body.
fn both_bodies(ns: &str, body: &str) -> [(&'static str, Vec<String>); 2] {
    let rule = load_errors_of(&format!(
        "{DECL}namespace {ns}r\n  import anthill.prelude.Int64\n  rule r(1) :- {body} = 7\nend\n"
    ));
    let op = load_errors_of(&format!(
        "{DECL}namespace {ns}o\n  import anthill.prelude.{{Int64, Bool}}\n  \
         operation viaOp() -> Bool = {body} = 7\nend\n"
    ));
    [("rule body", rule), ("operation body", op)]
}

/// One error, naming each of `tokens`, and none calling a name unresolved.
#[track_caller]
fn refused_once(errs: &[String], tokens: &[&str], why: &str) {
    assert_eq!(errs.len(), 1, "{why}: one error for the one written name, got {errs:#?}");
    assert_refused_naming(errs, tokens, why);
    assert!(
        !errs[0].contains("unresolved"),
        "{why}: a name that resolved is not called unresolved: {errs:#?}"
    );
}

#[test]
fn a_namespace_by_a_path_is_refused_once_as_a_namespace() {
    for (at, errs) in both_bodies("k40a", "zz.inner") {
        refused_once(&errs, &["`zz.inner` is a namespace", "has no value"], at);
    }
}

#[test]
fn a_namespace_alone_is_refused_as_a_namespace() {
    for (at, errs) in both_bodies("k40b", "zz") {
        refused_once(&errs, &["`zz` is a namespace", "has no value"], at);
    }
}

#[test]
fn a_path_that_names_nothing_is_refused_once() {
    for (at, errs) in both_bodies("k40c", "zz.nosuch.x") {
        refused_once(
            &errs,
            &["`zz.nosuch.x` names nothing", "the namespace `zz` declares no `nosuch`"],
            at,
        );
    }
    // Deeper, the prefix named is the longest one that resolved.
    for (at, errs) in both_bodies("k40d", "zz.inner.nosuch.y") {
        refused_once(&errs, &["the namespace `zz.inner` declares no `nosuch`"], at);
    }
}

#[test]
fn a_first_segment_that_names_nothing_is_refused_once() {
    for (at, errs) in both_bodies("k40e", "nosuch.x") {
        refused_once(
            &errs,
            &["`nosuch.x` names nothing", "no `nosuch` is visible in scope", "import"],
            at,
        );
    }
}

/// The addendum's program: `probe.Hid.Sec` from another namespace is refused as its import
/// is, and so is a hidden const read by a path.
#[test]
fn an_internal_name_by_a_path_is_refused_as_internal() {
    for (body, name) in [("zz.Q.Sec", "'Sec'"), ("zz.Q.hidden.x", "'hidden'")] {
        for (at, errs) in both_bodies("k40f", body) {
            refused_once(&errs, &[name, "is internal to 'zz.Q'"], &format!("{at}: {body}"));
        }
    }
    let probe = "\
namespace probe
  import anthill.prelude.Int64
  sort Hid
    internal sort Sec
      entity sx
    end
  end
end
";
    let errs = load_errors_of(&format!(
        "{probe}namespace user\n  import anthill.prelude.{{Int64, Type}}\n  \
         operation nm(t: Type) -> Int64 = 1\n  operation useIt() -> Int64 = nm(probe.Hid.Sec)\nend\n"
    ));
    refused_once(&errs, &["'Sec' is internal to 'probe.Hid'", "scope 'user"], "nm(probe.Hid.Sec)");
    let import = load_errors_of(&format!(
        "{probe}namespace user\n  import anthill.prelude.Int64\n  import probe.Hid.Sec\nend\n"
    ));
    assert_refused_naming(&import, &["is internal to 'probe.Hid'"], "the import's twin");
}

/// The bound: a name with a reading is typed as that reading, once, as before.
#[test]
fn the_names_with_a_reading_keep_it() {
    for (body, expected) in [
        ("zz.inner.rel", "expected Relation["),
        ("zz.Color.red", "expected Color, got Int64"),
        ("zz.Color", "expected Type, got Int64"),
    ] {
        for (at, errs) in both_bodies("k40g", body) {
            assert_eq!(errs.len(), 1, "{at}: {body}: {errs:#?}");
            assert!(errs[0].contains("eq.b (op-arg)") && errs[0].contains(expected), "{at}: {body}: {errs:#?}");
        }
    }
}

/// The bound: a name no scope has, written alone, keeps the refusal it had.
#[test]
fn a_name_alone_that_names_nothing_keeps_its_refusal() {
    for (at, errs) in both_bodies("k40h", "nosuch") {
        assert_eq!(errs.len(), 1, "{at}: {errs:#?}");
        assert!(errs[0].contains("nosuch.name") && errs[0].contains("unresolved"), "{at}: {errs:#?}");
    }
}

/// The bound: a written `anthill.reflect.field_access(…)` is a call, so its second argument
/// is an argument, typed as a value; its first, a dotted name, is that name.
#[test]
fn a_written_field_access_call_keeps_its_argument() {
    let errs = load_errors_of(&format!(
        "{DECL}namespace k40i\n  import anthill.prelude.Int64\n  \
         operation g() -> Int64 = anthill.reflect.field_access(zz.inner, nosuch)\nend\n"
    ));
    assert_eq!(errs.len(), 2, "{errs:#?}");
    assert!(errs[0].contains("`zz.inner` is a namespace"), "{errs:#?}");
    assert!(errs[1].contains("nosuch.name") && errs[1].contains("unresolved"), "{errs:#?}");
}

/// The bound: a path whose prefix is a value reads a field of it, as before.
#[test]
fn a_value_prefix_is_read_as_before() {
    let mut interp = interp_for(&format!(
        "{DECL}namespace k40j\n  import anthill.prelude.Int64\n  \
         operation go() -> Int64 = zz.Q.origin.x\nend\n"
    ));
    match interp.call("k40j.go", &[]) {
        Ok(Value::Int(n)) => assert_eq!(n, 3),
        other => panic!("expected 3, got {other:?}"),
    }
}

/// Every place a value is written meets the one refusal: a const's value, a constraint
/// body, a lambda in either body, a call's argument, and a `@[simp]` right-hand side where
/// a call fires it — the text typed as the rule's, from the rule's scope.
#[test]
fn every_value_position_reads_the_name_whole() {
    for (at, decls) in [
        ("const", "  const c: Int64 = zz.inner"),
        ("constraint", "  fact val(1)\n  constraint k1: val(?v) :- val(?v), ?v = zz.inner"),
        ("rule lambda", "  rule r(?f) :- ?f = lambda (x: Int64) -> zz.inner"),
        (
            "operation lambda",
            "  operation h() -> Function[A = Int64, B = Int64] = lambda (x: Int64) -> zz.inner",
        ),
        ("argument", "  operation id(x: Int64) -> Int64 = x\n  operation g() -> Int64 = id(zz.inner)"),
        (
            "simp right-hand side",
            "  operation f() -> Int64\n  rule f() <=> zz.inner @[simp]\n  operation g() -> Int64 = f()",
        ),
    ] {
        let errs = load_errors_of(&format!(
            "{DECL}namespace k40k\n  import anthill.prelude.{{Int64, Function}}\n{decls}\nend\n"
        ));
        refused_once(&errs, &["`zz.inner` is a namespace"], at);
    }
}
