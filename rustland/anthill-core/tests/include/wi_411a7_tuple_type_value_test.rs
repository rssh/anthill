//! A TUPLE PROVIDES `TypeValue` WHERE EACH OF ITS COMPONENTS DOES (WI-20261116-411A7; proposal
//! 004, "Extension (2026-11-16): a tuple is a `NamedTuple`", stage 2). The instance is
//! `NamedTuple`'s, `Dictionary(d1 … dn, impl: NamedTuple, labels: (l1, …, ln))`: one
//! sub-dictionary per component in the type's own order, and the labels beside them, so
//! `type_value` reads the type back off its evidence. Before, a tuple had no instance:
//! `type_value[T = (a: Int64, b: String)]()` and `tyOf((1, "s"))` were refused at load as "a
//! STRUCTURAL FORMER". An arrow still has none (WI-20261021-VF8GT), and a tuple has no type
//! pattern (WI-20261116-HWD8A decides one).
//!
//! The ticket's `PartialEq.eq(type_value[T = (a: Int64, b: String)](), (a: Int64, b: String))`
//! is not written here: a tuple written as a value is a tuple of `Type` values, `(a: Type, b:
//! Type)`, refused as `eq`'s second argument. The equality is asked between two answers.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches in one build, then removed. The control is every switch
//! unset: every row passes, on both carriers (`ANTHILL_TEST_NODE_CARRIER=1`).
//!
//! * No `TypeValue` branch in `typing::synth`'s `tuple_instance`: every row fails, a tuple's
//!   `TypeValue` refused at load (and `raise((1, 2))` with it).
//! * The labels not read in `type_of_type_value_dictionary`: [`a_tuples_type_value_answers_its_type`],
//!   [`two_answers_at_one_tuple_type_compare`], [`a_generic_reader_is_handed_a_tuples_dictionary`]
//!   and [`a_tuple_over_a_callers_parameter_needs_its_evidence`] fail, the answer read as a sort's.
//! * `resolve_at_goal`'s exit on no provision row kept for a tuple (`typing::carrier`): the
//!   first three of those fail, and [`a_component_without_an_instance_is_named`] at its
//!   bracket, a call of `type_value` at a tuple refused at its dispatch.
//! * No refusal of a pattern at a tuple (`typing::synth`'s `tuple_pattern_refusal`):
//!   [`a_tuple_has_no_type_pattern`] fails, `admits` at a tuple loading. Its `Foo` and `Bar`
//!   rows failed with the guard first written, keyed on the resolution path: they were
//!   refused, the derived `TypeValue` of each reaching a tuple through the sort's own
//!   `requires`.
//! * A tuple not read through in the caller-evidence refusal (`caller_writeable_application`):
//!   [`a_tuple_over_a_callers_parameter_needs_its_evidence`] fails, `tyOf((x, 1))` over an `E`
//!   with no evidence loading (it then panics when run).
//! * A tuple at `TypeValue` or `PartialEq` read as the former itself in `former_carrier`:
//!   [`a_component_without_an_instance_is_named`] fails, the refusal saying nothing provides the
//!   spec at the tuple, and [`a_tuple_over_a_callers_parameter_needs_its_evidence`], told of a
//!   former where it lacks a clause.
//! * The labels dropped on one carrier of the dictionary — the term (`dep_projection`'s
//!   `labelled_dictionary_term`), the occurrence (`node_occurrence`'s `Expr::Dictionary`) or
//!   the value (`Dictionary::build_labelled`): each fails
//!   [`the_dictionary_carries_the_tuples_labels`] and the four rows that read an answer.
//!
//! The last case of [`a_component_without_an_instance_is_named`], an arrow alone, holds under
//! every switch, by design: an arrow was refused before.

use anthill_core::eval::{Interpreter, Value};
use anthill_core::kb::KnowledgeBase;

use crate::common::{assert_refused_naming, interp_for, load_errors_of, load_kb_with, pattern_answer_counts, print_type};

fn src(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String, Type, List, Cell, PartialEq, Error, Result}}
  import anthill.reflect.{{TypeValue, TypePattern}}
  import anthill.realization.runtime.{{Dictionary}}
  sort Box
    sort V = ?
    entity box(v: V)
  end
  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = TypeValue.type_value[T = B]()
  operation pairOf[E](x: E) -> Type requires TypeValue[T = E] = TypeValue.type_value[T = (E, Int64)]()
  operation same[A](x: A, y: A) -> Bool requires PartialEq[T = A] = PartialEq.eq(x, y)
{body}
end
"#
    )
}

/// The `Type` `entry` answers, printed, on a fresh interpreter.
fn type_of(interp: &mut Interpreter, entry: &str) -> String {
    let v = interp
        .call(entry, &[])
        .unwrap_or_else(|e| panic!("{entry}: {e:?}"));
    print_type(interp.kb(), &v)
}

fn bool_of(interp: &mut Interpreter, entry: &str) -> bool {
    match interp.call(entry, &[]) {
        Ok(Value::Bool(b)) => b,
        other => panic!("{entry}: expected a Bool, got {other:?}"),
    }
}

/// T4: a bracket at a tuple answers the tuple type, named and positional, its labels in the
/// written order, nested, the unit, and inside a sort's application.
#[test]
fn a_tuples_type_value_answers_its_type() {
    let ns = "test.r411a7.t1";
    let program = src(
        ns,
        "  operation named() -> Type = TypeValue.type_value[T = (a: Int64, b: String)]()\n  \
         operation positional() -> Type = TypeValue.type_value[T = (Int64, String)]()\n  \
         operation order() -> Type = TypeValue.type_value[T = (b: Int64, a: String)]()\n  \
         operation nested() -> Type = TypeValue.type_value[T = (Int64, (a: Bool, b: String))]()\n  \
         operation unit() -> Type = TypeValue.type_value[T = ()]()\n  \
         operation inBox() -> Type = TypeValue.type_value[T = Box[V = (Int64, String)]]()",
    );
    let mut interp = interp_for(&program);
    for (entry, want) in [
        ("named", "(a: Int64, b: String)"),
        ("positional", "(Int64, String)"),
        ("order", "(b: Int64, a: String)"),
        ("nested", "(Int64, (a: Bool, b: String))"),
        ("unit", "Unit"),
        ("inBox", "Box[V = (Int64, String)]"),
    ] {
        assert_eq!(type_of(&mut interp, &format!("{ns}.{entry}")), want, "`{entry}`");
    }
}

/// Two answers at one tuple type are equal; at a tuple with other labels, or the same labels
/// in another order, they are not.
#[test]
fn two_answers_at_one_tuple_type_compare() {
    let ns = "test.r411a7.t2";
    let program = src(
        ns,
        "  operation ab() -> Type = TypeValue.type_value[T = (a: Int64, b: String)]()\n  \
         operation same1() -> Bool = PartialEq.eq(ab(), tyOf((a: 1, b: \"x\")))\n  \
         operation positional() -> Bool = PartialEq.eq(ab(), tyOf((1, \"x\")))\n  \
         operation reordered() -> Bool = PartialEq.eq(ab(), TypeValue.type_value[T = (b: String, a: Int64)]())",
    );
    let mut interp = interp_for(&program);
    for (entry, want) in [("same1", true), ("positional", false), ("reordered", false)] {
        assert_eq!(bool_of(&mut interp, &format!("{ns}.{entry}")), want, "`{entry}`");
    }
}

/// A generic reader is handed a tuple's dictionary: `tyOf((1, "s"))`, a named tuple, a list of
/// tuples, a type expression reading the parameter (`Cell[V = B]`); a component at a type
/// parameter takes the caller's dictionary (`pairOf(true)`), two generic levels down too.
#[test]
fn a_generic_reader_is_handed_a_tuples_dictionary() {
    let ns = "test.r411a7.t3";
    let program = src(
        ns,
        "  operation outer[E](x: E) -> Type requires TypeValue[T = E] = pairOf(x)\n  \
         operation cellOf[B](x: B) -> Type requires TypeValue[T = B] = Cell[V = B]\n  \
         operation cell() -> Bool = PartialEq.eq(cellOf((1, 2)), Cell[V = (Int64, Int64)])\n  \
         operation cellApart() -> Bool = PartialEq.eq(cellOf((1, 2)), Cell[V = (Int64, String)])\n  \
         operation pair() -> Type = tyOf((1, \"s\"))\n  \
         operation named() -> Type = tyOf((a: 1, b: \"s\"))\n  \
         operation list() -> Type = tyOf([(a: 1, b: true)])\n  \
         operation param() -> Type = pairOf(true)\n  \
         operation twoLevels() -> Type = outer(\"s\")",
    );
    let mut interp = interp_for(&program);
    for (entry, want) in [
        ("pair", "(Int64, String)"),
        ("named", "(a: Int64, b: String)"),
        ("list", "List[T = (a: Int64, b: Bool)]"),
        ("param", "(Bool, Int64)"),
        ("twoLevels", "(String, Int64)"),
    ] {
        assert_eq!(type_of(&mut interp, &format!("{ns}.{entry}")), want, "`{entry}`");
    }
    for (entry, want) in [("cell", true), ("cellApart", false)] {
        assert_eq!(bool_of(&mut interp, &format!("{ns}.{entry}")), want, "`{entry}`");
    }
}

/// A tuple with a component that has no instance has none, and the refusal names the
/// component: an arrow, at `TypeValue` and at `PartialEq`, nested in a tuple, inside a list.
/// An arrow alone is refused as before.
#[test]
fn a_component_without_an_instance_is_named() {
    let ns = "test.r411a7.t4";
    let component = "nothing provides it at its component `Int64 -> Int64`";
    for (body, tokens) in [
        (
            "  operation g() -> Type = tyOf((1, lambda (x: Int64) -> x))",
            vec!["its carrier `(_1: Int64, _2: Int64 -> Int64)` is a tuple", component],
        ),
        (
            "  operation g() -> Type = tyOf((1, (true, lambda (x: Int64) -> x)))",
            vec![component],
        ),
        (
            "  operation g(f: (Int64) -> Int64) -> Bool = same((1, f), (1, f))",
            vec!["which provides `anthill.prelude.PartialEq` where each of its components does", component],
        ),
        (
            "  operation g() -> Type = TypeValue.type_value[T = (Int64, (Int64) -> Int64)]()",
            vec!["unresolved: anthill.reflect.TypeValue[T = Int64 -> Int64]", "an arrow has none"],
        ),
        (
            "  operation g() -> Type = tyOf([(1, lambda (x: Int64) -> x)])",
            vec!["has a STRUCTURAL FORMER — an arrow — among its type arguments"],
        ),
        (
            "  operation g() -> Type = tyOf(lambda (x: Int64) -> x)",
            vec!["its carrier is `Int64 -> Int64`, a STRUCTURAL FORMER"],
        ),
    ] {
        let errs = load_errors_of(&src(ns, body));
        assert_eq!(errs.len(), 1, "{body}: {errs:#?}");
        assert_refused_naming(&errs, &tokens, body);
    }
}

/// A tuple over a caller's type parameter needs the caller's evidence for the parameter, and
/// the refusal says which: `TypeValue[T = E]`, not the tuple's. With it, the call runs.
#[test]
fn a_tuple_over_a_callers_parameter_needs_its_evidence() {
    let ns = "test.r411a7.t5";
    for body in [
        "  operation g[E](x: E) -> Type = tyOf((x, 1))",
        "  operation g[E](x: E) -> Type = tyOf((a: x, b: (x, 2)))",
        "  operation g[E](x: E) -> Type = tyOf((1, [x]))",
    ] {
        let errs = load_errors_of(&src(ns, body));
        assert_eq!(errs.len(), 1, "{body}: {errs:#?}");
        assert_refused_naming(
            &errs,
            &["holds `E`, a type parameter of the CALLING operation", "Declare `requires anthill.reflect.TypeValue[T = E]`"],
            body,
        );
    }
    let program = src(
        ns,
        "  operation g[E](x: E) -> Type requires TypeValue[T = E] = tyOf((a: x, b: [(x, 1)]))\n  \
         operation whole[E](x: E) -> Type requires TypeValue[T = (E, Int64)] = tyOf((x, 1))\n  \
         operation h() -> Type = g(true)\n  \
         operation w() -> Type = whole(\"s\")",
    );
    let mut interp = interp_for(&program);
    assert_eq!(type_of(&mut interp, &format!("{ns}.h")), "(a: Bool, b: List[T = (Bool, Int64)])");
    assert_eq!(type_of(&mut interp, &format!("{ns}.w")), "(String, Int64)");
}

/// A tuple has no type pattern: `admits` at a tuple, at a type holding one, through a generic
/// caller, and an `Error.reify` over a tuple payload are refused at load. `Error.raise((1, 2))`
/// loads, since `raise` asks only `TypeValue`. A pattern at a sort still answers, a sort whose
/// own `requires` asks a tuple's `TypeValue` included, and a rule body's goal of `TypeValue` at
/// a tuple holds where `TypePattern`'s does not.
#[test]
fn a_tuple_has_no_type_pattern() {
    let ns = "test.r411a7.t6";
    let no_pattern = "a tuple has no type pattern, at a tuple or inside a type that holds one";
    for (body, token) in [
        (
            "  operation g() -> Bool = TypePattern.admits[T = (Int64, Int64)](TypeValue.type_value[T = Int64]())",
            no_pattern,
        ),
        (
            "  operation g() -> Bool = TypePattern.admits[T = List[T = (Int64, Int64)]](TypeValue.type_value[T = Int64]())",
            no_pattern,
        ),
        (
            "  operation g[E](x: E) -> Bool requires TypeValue[T = E] = TypePattern.admits[T = (E, Int64)](TypeValue.type_value[T = Int64]())",
            no_pattern,
        ),
        (
            "  operation boom() -> Int64 effects Error[T = (Int64, Int64)] = Error.raise((1, 2))\n  \
             rule caught(?x) :- Error.reify(lambda () -> boom(), ?x)",
            "nothing provides `anthill.reflect.TypePattern` at it",
        ),
    ] {
        let errs = load_errors_of(&src(ns, body));
        assert_eq!(errs.len(), 1, "{body}: {errs:#?}");
        assert_refused_naming(&errs, &[token], body);
    }
    let program = src(
        ns,
        "  operation boom() -> Int64 effects Error[T = (Int64, Int64)] = Error.raise((1, 2))\n  \
         operation atSort() -> Bool = TypePattern.admits[T = Int64](TypeValue.type_value[T = Int64]())\n  \
         sort Foo\n    requires TypeValue[T = (Int64, Int64)]\n    entity foo\n  end\n  \
         sort Bar\n    sort V = ?\n    requires TypeValue[T = (V, Int64)]\n    entity bar(v: V)\n  end\n  \
         operation atFoo() -> Bool = TypePattern.admits[T = Foo](TypeValue.type_value[T = Foo]())\n  \
         operation atBar() -> Bool = TypePattern.admits[T = Bar[V = Bool]](TypeValue.type_value[T = Bar[V = Bool]]())\n  \
         rule pattern() :- TypePattern[T = (Int64, Int64)]\n  \
         rule value() :- TypeValue[T = (Int64, Int64)]",
    );
    let mut interp = interp_for(&program);
    for entry in ["atSort", "atFoo", "atBar"] {
        assert!(bool_of(&mut interp, &format!("{ns}.{entry}")), "`{entry}`");
    }
    let mut kb = load_kb_with(&program);
    assert_eq!(pattern_answer_counts(&mut kb, &format!("{ns}.value()")), (1, 1));
    assert_eq!(pattern_answer_counts(&mut kb, &format!("{ns}.pattern()")), (0, 0));
}

/// The local names of `Dictionary.labels(d)`'s answer: `None` for `none()`, the list's symbols
/// for `some(…)`.
fn labels_of(interp: &mut Interpreter, d: Value) -> Option<Vec<String>> {
    let answer = interp
        .call("anthill.realization.runtime.Dictionary.labels", &[d])
        .expect("Dictionary.labels");
    let kb: &KnowledgeBase = interp.kb();
    let child = |v: &Value, name: &str| match v {
        Value::Entity { named, .. } => named
            .iter()
            .find(|(s, _)| kb.local_name_of(*s) == name)
            .map(|(_, c)| c.clone())
            .unwrap_or_else(|| panic!("no `{name}` child on {v:?}")),
        other => panic!("expected an entity, got {other:?}"),
    };
    let functor = |v: &Value| match v {
        Value::Entity { functor, .. } => kb.local_name_of(*functor).to_owned(),
        other => panic!("expected an entity, got {other:?}"),
    };
    match functor(&answer).as_str() {
        "none" => None,
        "some" => {
            let mut node = child(&answer, "value");
            let mut read = Vec::new();
            while functor(&node) == "cons" {
                match child(&node, "head") {
                    Value::SymbolRef(s) => read.push(kb.local_name_of(s).to_owned()),
                    other => panic!("a label is not a Symbol: {other:?}"),
                }
                node = child(&node, "tail");
            }
            assert_eq!(functor(&node), "nil");
            Some(read)
        }
        other => panic!("expected an Option, got `{other}`"),
    }
}

/// A tuple's `TypeValue` dictionary carries the tuple's labels, in its type's order, the
/// positional ones as `_1`, `_2`; a sort's dictionary and a tuple's `PartialEq` dictionary
/// carry none.
#[test]
fn the_dictionary_carries_the_tuples_labels() {
    let ns = "test.r411a7.t7";
    let program = src(
        ns,
        "  operation named() -> TypeValue[T = (b: Int64, a: String)] = Dictionary.instance[TypeValue[T = (b: Int64, a: String)]]()\n  \
         operation positional() -> TypeValue[T = (Int64, String)] = Dictionary.instance[TypeValue[T = (Int64, String)]]()\n  \
         operation atSort() -> TypeValue[T = Box[V = Int64]] = Dictionary.instance[TypeValue[T = Box[V = Int64]]]()\n  \
         operation equality() -> PartialEq[T = (a: Int64, b: String)] = Dictionary.instance[PartialEq[T = (a: Int64, b: String)]]()",
    );
    let mut interp = interp_for(&program);
    for (entry, want) in [
        ("named", Some(vec!["b", "a"])),
        ("positional", Some(vec!["_1", "_2"])),
        ("atSort", None),
        ("equality", None),
    ] {
        let d = interp
            .call(&format!("{ns}.{entry}"), &[])
            .unwrap_or_else(|e| panic!("{entry}: {e:?}"));
        let want = want.map(|w| w.into_iter().map(str::to_owned).collect::<Vec<_>>());
        assert_eq!(labels_of(&mut interp, d), want, "`{entry}`");
    }
}
