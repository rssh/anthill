//! PROVISIONS WRITTEN AT A TUPLE TYPE, AND `NamedTuple` (proposal 004's extension, open question
//! 2, decided with the user 2026-11-17). No sort provides `NamedTuple`: a tuple type is
//! `NamedTuple` applied to its components and is written only as tuple syntax. A provision of
//! another spec at a tuple type is a sort's like any other, and a written `PartialEq` there
//! answers in place of the tuple's derived one, as a sort's written equality does in place of
//! its derived one. Before, `W provides PartialEq[T = (Int64, String)]` loaded and was never
//! read: the derived instance answered every goal at a tuple.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches in one build, then removed. The control is every switch
//! unset: every row passes.
//!
//! * The derived instance answering where a written row does (`typing::synth`'s
//!   `written_at_tuple` answering false): [`a_provision_written_at_a_tuple_type_answers`]
//!   fails, every equality at `(Int64, String)` answering `false`, and
//!   [`an_eq_under_a_written_partial_eq_is_not_derived`], its `Eq` derived.
//! * The derived `Eq` laid out over a written `PartialEq` (the `Eq` check in
//!   `tuple_instance`): [`an_eq_under_a_written_partial_eq_is_not_derived`] fails, `lawful`
//!   loading.
//! * A rule body's equality pinned to the written member compared component by component
//!   (`resolve`'s `sem_eq_values_at`, the unpinned arm taken for any pin but `NamedTuple`'s):
//!   [`a_provision_written_at_a_tuple_type_answers`] fails at its rule body.
//! * No refusal of `provides NamedTuple` (`typing::written_named_tuple_provisions`):
//!   [`no_sort_provides_named_tuple`] fails, the sort that writes `namedTupleEq` loading.
//!   The provider-operations check owing such a provision its operation (`coherence`'s
//!   `check_provider_operations`, its `NamedTuple` skip): the same row fails, told twice.
//! * `=`'s component refusal asked at a tuple a written row answers (`apply`'s
//!   `tuple_equality_is_written` filter): [`a_written_row_answers_where_a_component_has_no_equality`]
//!   fails, refused at its arrow.
//! * The key check reading a tuple by its components whatever its `PartialEq` is
//!   (`coherence`'s `unlawful_eq_part`): [`a_tuple_key_with_a_written_equality_is_judged_whole`]
//!   fails, both keys accepted.
//!
//! [`a_spec_of_the_programs_at_a_tuple_answers`] passes under every switch, by design: a
//! provision of a program's own spec at a tuple was answered before.

use anthill_core::eval::Value;

use crate::common::{assert_refused_naming, interp_for, load_errors_of, load_kb_with, pattern_answer_counts};

fn src(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String, List, Map, NamedTuple, PartialEq, Eq}}
  operation same[A](x: A, y: A) -> Bool requires PartialEq[T = A] = PartialEq.eq(x, y)
  operation lawful[A](x: A, y: A) -> Bool requires Eq[T = A] = PartialEq.eq(x, y)
{body}
end
"#
    )
}

/// `W`'s `eq` holds of every two pairs at `(Int64, String)`.
const W: &str = "  sort W\n    entity w\n    provides PartialEq[T = (Int64, String)]\n    \
                 operation eq(a: (Int64, String), b: (Int64, String)) -> Bool = true\n  end\n";

fn bool_of(interp: &mut anthill_core::eval::Interpreter, entry: &str) -> bool {
    match interp.call(entry, &[]) {
        Ok(Value::Bool(b)) => b,
        other => panic!("{entry}: expected a Bool, got {other:?}"),
    }
}

/// A `PartialEq` written at `(Int64, String)` answers there: a call of `PartialEq.eq`, `=`, a
/// requirement-generic `same`, a list of such pairs, and a rule body. At another tuple type —
/// other components, or other labels — the derived instance answers.
#[test]
fn a_provision_written_at_a_tuple_type_answers() {
    let ns = "test.tuplewritten.t1";
    let program = src(
        ns,
        &format!(
            "{W}  operation call() -> Bool = PartialEq.eq((1, \"s\"), (2, \"t\"))\n  \
             operation infix() -> Bool = (1, \"s\") = (2, \"t\")\n  \
             operation generic() -> Bool = same((1, \"s\"), (2, \"t\"))\n  \
             operation list() -> Bool = [(1, \"s\")] = [(2, \"t\")]\n  \
             operation other() -> Bool = (1, true) = (2, false)\n  \
             operation labelled() -> Bool = (a: 1, b: \"s\") = (a: 2, b: \"t\")\n  \
             rule holds() :- (1, \"s\") = (2, \"t\")"
        ),
    );
    let mut interp = interp_for(&program);
    for (entry, want) in [
        ("call", true),
        ("infix", true),
        ("generic", true),
        ("list", true),
        ("other", false),
        ("labelled", false),
    ] {
        assert_eq!(bool_of(&mut interp, &format!("{ns}.{entry}")), want, "`{entry}`");
    }
    let mut kb = load_kb_with(&program);
    assert_eq!(pattern_answer_counts(&mut kb, &format!("{ns}.holds()")), (1, 1));
}

/// Under a written `PartialEq` the tuple's `Eq` is not derived — its law is the writer's to
/// state — so `lawful` at the pair is refused, naming the written provision; with `Eq` written
/// beside it, it runs, through `W`'s `eq`.
#[test]
fn an_eq_under_a_written_partial_eq_is_not_derived() {
    let ns = "test.tuplewritten.t2";
    let errs = load_errors_of(&src(
        ns,
        &format!("{W}  operation g() -> Bool = lawful((1, \"s\"), (2, \"t\"))"),
    ));
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert_refused_naming(
        &errs,
        &["the tuple's `PartialEq` is a written provision", "write `provides anthill.prelude.Eq[…]` at the tuple"],
        "Eq under a written PartialEq",
    );
    let written_eq = W.replace(
        "    provides PartialEq[T = (Int64, String)]\n",
        "    provides PartialEq[T = (Int64, String)]\n    provides Eq[T = (Int64, String)]\n",
    );
    let program = src(ns, &format!("{written_eq}  operation g() -> Bool = lawful((1, \"s\"), (2, \"t\"))"));
    let mut interp = interp_for(&program);
    assert!(bool_of(&mut interp, &format!("{ns}.g")));
}

/// A provision of a program's own spec at a tuple type answers, as it did.
#[test]
fn a_spec_of_the_programs_at_a_tuple_answers() {
    let ns = "test.tuplewritten.t3";
    let program = src(
        ns,
        "  sort Show\n    sort T = ?\n    operation show(x: T) -> String\n  end\n  \
         operation sh[A](x: A) -> String requires Show[T = A] = Show.show(x)\n  \
         sort W\n    entity w\n    provides Show[T = (Int64, String)]\n    \
         operation show(x: (Int64, String)) -> String = \"pair\"\n  end\n  \
         operation g() -> String = sh((1, \"s\"))",
    );
    let mut interp = interp_for(&program);
    match interp.call(&format!("{ns}.g"), &[]) {
        Ok(Value::Str(s)) => assert_eq!(&*s, "pair"),
        other => panic!("expected \"pair\", got {other:?}"),
    }
}

/// No sort provides `NamedTuple`, with its member written or not, and the refusal is the one
/// told: no operation is owed for a clause that may not be written.
#[test]
fn no_sort_provides_named_tuple() {
    let ns = "test.tuplewritten.t4";
    for member in [
        "    operation namedTupleEq(a: NamedTuple, b: NamedTuple) -> Bool = true\n",
        "",
    ] {
        let errs = load_errors_of(&src(
            ns,
            &format!("  sort Pt\n    entity pt(x: Int64, y: Int64)\n    provides NamedTuple\n{member}  end"),
        ));
        assert_eq!(errs.len(), 1, "{member:?}: {errs:#?}");
        assert_refused_naming(
            &errs,
            &[&format!("'{ns}.Pt' writes `provides anthill.prelude.NamedTuple`"), "no sort provides `NamedTuple`"],
            "provides NamedTuple",
        );
    }
}

/// `=` at a tuple whose component has no `PartialEq` is refused naming the component, and
/// answers where a `PartialEq` is written at the tuple type: the written instance is the
/// tuple's, and its components are not asked.
#[test]
fn a_written_row_answers_where_a_component_has_no_equality() {
    let ns = "test.tuplewritten.t5";
    let call = "  operation g() -> Bool = (1, lambda (x: Int64) -> x) = (2, lambda (x: Int64) -> x)";
    let errs = load_errors_of(&src(ns, call));
    assert_refused_naming(&errs, &["anthill.prelude.PartialEq[T = Int64 -> Int64]"], "no written row");
    let arrow_w = "  sort W\n    entity w\n    provides PartialEq[T = (Int64, (Int64) -> Int64)]\n    \
                   operation eq(a: (Int64, (Int64) -> Int64), b: (Int64, (Int64) -> Int64)) -> Bool = true\n  end\n";
    let program = src(ns, &format!("{arrow_w}{call}"));
    let mut interp = interp_for(&program);
    assert!(bool_of(&mut interp, &format!("{ns}.g")));
}

/// A `Map` key at a tuple whose `PartialEq` is written is judged whole, as a sort with a
/// written equality is: refused with no `Eq` at it (also inside a `List`), accepted with `Eq`
/// written beside it. A tuple key with no written row is still read by its components.
#[test]
fn a_tuple_key_with_a_written_equality_is_judged_whole() {
    let ns = "test.tuplewritten.t6";
    let keys = "  operation h(m: Map[K = (Int64, String), V = Int64]) -> Int64 = 1\n  \
                operation nested(m: Map[K = List[T = (Int64, String)], V = Int64]) -> Int64 = 1\n  \
                operation other(m: Map[K = (Int64, Bool), V = Int64]) -> Int64 = 1";
    let errs = load_errors_of(&src(ns, &format!("{W}{keys}")));
    assert_eq!(errs.len(), 2, "{errs:#?}");
    for key in ["`K = (_1: Int64, _2: String)`", "`K = anthill.prelude.List[T = (_1: Int64, _2: String)]`"] {
        assert_refused_naming(&errs, &[key, "so it is not a lawful key"], key);
    }
    let written_eq = W.replace(
        "    provides PartialEq[T = (Int64, String)]\n",
        "    provides PartialEq[T = (Int64, String)]\n    provides Eq[T = (Int64, String)]\n",
    );
    let errs = load_errors_of(&src(ns, &format!("{written_eq}{keys}")));
    assert!(errs.is_empty(), "{errs:#?}");
}
