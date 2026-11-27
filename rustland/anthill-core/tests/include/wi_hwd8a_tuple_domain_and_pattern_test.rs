//! A TUPLE PROVIDES `SortDomain`, AND A TYPE PATTERN AT A TUPLE ADMITS BY `<:` (WI-20261116-HWD8A;
//! proposal 004, "Extension (2026-11-16): a tuple is a `NamedTuple`", stage 3, open question 1).
//!
//! A tuple's domain is the tuples of its components' domains, in the type's order. It is built
//! where a sort's is: from a type in the resolver (a typed head, a typed query variable, a
//! condition's sub), at a citation (`typing::sort_domain_route`), in a sort's derived `fill`
//! for a field of tuple type (`kb::fill_derive`), and as the instance a written `requires
//! SortDomain[T = X]` is handed (`typing::synth`'s `tuple_instance`). Its dictionary is
//! `NamedTuple`'s: its `Fillable` holds each component's `SortDomain` and the tuple's labels,
//! and its `SortDomain` holds that `Fillable` in its chain's slot. A type pattern at a tuple
//! admits a type as every pattern does, where the type is a subtype of an instance of it, and
//! `<:` at a tuple is by label with width and permutation (kernel-language §4.5).
//!
//! Before, a typed head at a tuple was one conditional answer with `domain(?_, (Colour,
//! Size))` left over, a sort with a tuple field had no domain, `requires SortDomain[T = X]` at
//! a tuple was refused at load, and a pattern at a tuple was refused at load.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches in one build, then removed. The control is every switch
//! unset: every row passes, on both carriers (`ANTHILL_TEST_NODE_CARRIER=1`).
//!
//! * Two tuples not compared by label in `type_pattern`'s `below` (`tuple_below`), answered
//!   `false`: [`a_tuple_pattern_catches_by_label`] and [`what_was_refused_as_no_tuple_pattern_answers`]
//!   (the width and permutation boundaries leave their label undeclared, `generic` answers
//!   `false`), [`a_tuple_pattern_admits_by_label`] (`width`),
//!   [`a_pattern_with_other_labels_lets_the_raise_pass`] and
//!   [`a_rule_body_boundary_infers_a_tuple_pattern`] (nothing caught).
//! * Two tuples not compared as one type in `equal`: [`a_tuple_pattern_admits_by_label`]
//!   (`sameInBox` answers `false`).
//! * No least pattern of two tuples (`joined_tuple`): [`a_rule_body_boundary_infers_a_tuple_pattern`],
//!   its three two-raise rules refused as labels "which no one sort heads".
//! * `fill_open_slots` not through a tuple: [`a_tuple_pattern_admits_by_label`], `(a: Option)`
//!   refused at load, `Option`'s `T` left without a `TypeValue`.
//! * The stage-2 refusal of a pattern at a tuple put back (`tuple_pattern_refusal`): every
//!   pattern row is refused at load, and [`a_tuple_holding_an_arrow_is_still_refused`] is
//!   refused without naming the arrow.
//! * No tuple evidence in the resolver (`domain_evidence_of_type`): a typed head, a typed query
//!   variable, a tuple field and a citation each answer one conditional row,
//!   `domain(?_, (Colour, Size))` left over.
//! * A bound tuple read by unifying it with the type's tuple, not by label
//!   (`tuple_fill_goal`): [`a_bound_tuple_is_checked_by_label`], the wider value is refused.
//! * A construction's `labels` dropped where the resolver evaluates it (`domain_evidence`):
//!   [`a_sort_with_a_tuple_field_has_a_domain`], `Pair[V = Colour]` floundering.
//! * A tuple's `SortDomain` dictionary not unwrapped to its `Fillable`
//!   (`tuple_fillable_dictionary`): [`a_requirement_at_a_tuple_is_answered`], the count raising.
//! * A tuple bound not fillable in the typer (`rules::bound_is_fillable`): the typed head, the
//!   typed query variable and the clause citing `any` answer one conditional row.
//! * A tuple field not fillable in the derivation (`fill_derive::field_fillable`), or filled
//!   through its type where it holds the sort's parameter (`evidence`):
//!   [`a_sort_with_a_tuple_field_has_a_domain`], `Holder` with no domain, `Pair[V = Colour]`'s
//!   tuple left unfilled.
//! * No route at a tuple (`typing::sort_domain_route`): [`a_citation_routes_a_tuples_domain`],
//!   `Wrap[T = (Colour, Size)].el` raising where it is counted.
//! * No `SortDomain` or `Fillable` instance at a tuple (`tuple_instance`):
//!   [`a_requirement_at_a_tuple_is_answered`] refused at load as a structural former (with the
//!   `Fillable` instance alone taken out, at `fillableAt`'s call), and
//!   [`a_tuple_holding_an_arrow_is_still_refused`] refused without naming the arrow.
//! * `TypePattern` not read through tuples in the former refusal (`dict::reads_through_tuples`):
//!   `wi_n31xx_type_value_read_rule_test`'s `Option` holding an arrow is told of "a tuple or an
//!   arrow".
//!
//! * No refusal of a `SortDomain` written at a tuple (`typing::written_tuple_provisions`'s second
//!   half): [`a_written_sort_domain_at_a_tuple_is_refused`], the four programs loading clean.
//!
//! [`a_tuple_holding_an_arrow_is_still_refused`] is refused under every switch, by design: an
//! arrow has no instance before or after; what moves is the text, which names the arrow.

use anthill_core::eval::{Interpreter, Value};

use crate::common::{assert_refused_naming, interp_for, load_errors_of, load_kb_with, pattern_answer_counts, show_value};

fn src(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String, Option, List, Error, EmptyStream, Result}}
  import anthill.reflect.{{TypeValue, TypePattern, SortDomain, Fillable, type_admits}}
  sort Colour
    entity red
    entity green
    entity blue
  end
  sort Size
    entity small
    entity large
  end
  sort Box
    sort V = ?
    entity box(v: V)
  end
  sort Wrap[T]
    entity wrap(v: T)
    rule el(?x: T) :- true
  end
{body}
end
"#
    )
}

/// What `entry` answers, shown, on a fresh interpreter's run of it.
fn shown(interp: &mut Interpreter, entry: &str) -> String {
    let v = interp
        .call(entry, &anthill_core::eval::HostValue::all(&[])).map(|h| h.value)
        .unwrap_or_else(|e| panic!("{entry}: {e:?}"));
    show_value(interp.kb(), &v)
}

/// `goal` with `COLOUR` and `SIZE` written as the namespace's sorts: a query names a
/// constructor by its qualified name.
fn qualified(ns: &str, goal: &str) -> String {
    goal.replace("COLOUR", &format!("{ns}.Colour"))
        .replace("SIZE", &format!("{ns}.Size"))
}

fn int_of(interp: &mut Interpreter, entry: &str) -> i64 {
    match interp.call(entry, &anthill_core::eval::HostValue::all(&[])).map(|h| h.value) {
        Ok(Value::Int(n)) => n,
        other => panic!("{entry}: expected an Int64, got {other:?}"),
    }
}

fn bool_of(interp: &mut Interpreter, entry: &str) -> bool {
    match interp.call(entry, &anthill_core::eval::HostValue::all(&[])).map(|h| h.value) {
        Ok(Value::Bool(b)) => b,
        other => panic!("{entry}: expected a Bool, got {other:?}"),
    }
}

/// `Result`'s `err`, as a query names it.
const ERR: &str = "anthill.prelude.Result.err";

const BOOM: &str = "  operation boom() -> Int64 effects Error[T = (a: Int64, b: String)] = Error.raise((a: 1, b: \"x\"))\n";

/// A boundary at a tuple catches a raise of a tuple it admits: the same type, a narrower one by
/// width (`(a: Int64)`), and the same labels in another order. The raised value is caught as
/// it was raised.
#[test]
fn a_tuple_pattern_catches_by_label() {
    let ns = "test.hwd8a.p1";
    let program = src(
        ns,
        &format!(
            "{BOOM}  operation same() -> Result[T = Int64, E = (a: Int64, b: String)] =\n    \
             Error.reify[T1 = (a: Int64, b: String)](lambda () -> boom())\n  \
             operation width() -> Result[T = Int64, E = (a: Int64)] =\n    \
             Error.reify[T1 = (a: Int64)](lambda () -> boom())\n  \
             operation permuted() -> Result[T = Int64, E = (b: String, a: Int64)] =\n    \
             Error.reify[T1 = (b: String, a: Int64)](lambda () -> boom())\n"
        ),
    );
    let mut interp = interp_for(&program);
    for entry in ["same", "width", "permuted"] {
        assert_eq!(
            shown(&mut interp, &format!("{ns}.{entry}")),
            r#"err(error: (a: 1, b: "x"))"#,
            "`{entry}`"
        );
    }
}

/// A boundary whose pattern has another label, or is positional (`_1`, `_2`), does not admit
/// `(a: Int64, b: String)`: the raise passes it to the caller's boundary, and where the caller
/// does not declare the label the typer leaves it in the row, refused as undeclared.
#[test]
fn a_pattern_with_other_labels_lets_the_raise_pass() {
    let ns = "test.hwd8a.p4";
    let program = src(
        ns,
        &format!(
            "{BOOM}  operation positional() -> Result[T = Int64, E = (Int64, String)] effects Error[T = (a: Int64, b: String)] =\n    \
             Error.reify[T1 = (Int64, String)](lambda () -> boom())\n  \
             operation outer() -> Result[T = Result[T = Int64, E = (Int64, String)], E = (a: Int64, b: String)] =\n    \
             Error.reify[T1 = (a: Int64, b: String)](lambda () -> positional())\n"
        ),
    );
    let mut interp = interp_for(&program);
    assert_eq!(
        shown(&mut interp, &format!("{ns}.outer")),
        r#"err(error: (a: 1, b: "x"))"#,
        "the inner boundary does not catch it, the outer one does"
    );
    for pattern in ["(Int64, String)", "(a: Int64, c: String)"] {
        let body = format!(
            "{BOOM}  operation g() -> Result[T = Int64, E = {pattern}] =\n    \
             Error.reify[T1 = {pattern}](lambda () -> boom())\n"
        );
        let errs = load_errors_of(&src("test.hwd8a.p4b", &body));
        assert_refused_naming(&errs, &["undeclared effect: Error[T = (a: Int64, b: String)]"], &body);
    }
}

/// `TypePattern.admits` at a tuple, and the reflect test it runs (`type_admits`): width and
/// permutation admit, other labels do not, and an open slot inside a tuple admits every type
/// there. Under an invariant parameter (`Box`'s `V`, no variance fact) two tuples are equal
/// only as one type: the same labels in the same order.
#[test]
fn a_tuple_pattern_admits_by_label() {
    let ns = "test.hwd8a.p6";
    let program = src(
        ns,
        "  operation width() -> Bool = TypePattern.admits[T = (a: Int64)](TypeValue.type_value[T = (a: Int64, b: String)]())\n  \
         operation positional() -> Bool = TypePattern.admits[T = (Int64, String)](TypeValue.type_value[T = (a: Int64, b: String)]())\n  \
         operation openSlot() -> Bool = TypePattern.admits[T = (a: Option)](TypeValue.type_value[T = (a: Option[T = Int64])]())\n  \
         operation otherComponent() -> Bool = TypePattern.admits[T = (a: String)](TypeValue.type_value[T = (a: Int64, b: String)]())\n  \
         operation insideSort() -> Bool = TypePattern.admits[T = List[T = (a: Int64)]](TypeValue.type_value[T = List[T = (b: String, a: Int64)]]())\n  \
         operation sameInBox() -> Bool = type_admits(Box[V = (a: Int64, b: String)], Box[V = (a: Int64, b: String)])\n  \
         operation reorderedInBox() -> Bool = type_admits(Box[V = (a: Int64, b: String)], Box[V = (b: String, a: Int64)])\n  \
         operation widerInBox() -> Bool = type_admits(Box[V = (a: Int64)], Box[V = (a: Int64, b: String)])\n  \
         operation sortAtTuple() -> Bool = type_admits(Colour, TypeValue.type_value[T = (a: Int64)]())\n",
    );
    let mut interp = interp_for(&program);
    for (entry, want) in [
        ("width", true),
        ("positional", false),
        ("openSlot", true),
        ("otherComponent", false),
        ("insideSort", true),
        ("sameInBox", true),
        ("reorderedInBox", false),
        ("widerInBox", false),
        ("sortAtTuple", false),
    ] {
        assert_eq!(bool_of(&mut interp, &format!("{ns}.{entry}")), want, "`{entry}`");
    }
}

/// A rule body's boundary infers its pattern from the labels its thunk raises (kernel-language
/// §5.4's least pattern): one tuple is itself, and two are the labels both have — joined
/// component by component, open where two components have no one pattern, and the tuple of no
/// components where they share no label. Each answer is the raised value. Before, two tuples
/// were refused as labels "which no one sort heads".
#[test]
fn a_rule_body_boundary_infers_a_tuple_pattern() {
    let ns = "test.hwd8a.p5";
    let program = src(
        ns,
        &format!(
            "{BOOM}  rule caught(?x) :- Error.reify(lambda () -> boom(), ?x)\n  \
             operation boomP() -> Int64 effects Error[T = (b: String, a: Int64, c: Bool)] = Error.raise((b: \"y\", a: 2, c: true))\n  \
             operation boomS() -> Int64 effects Error[T = (a: String)] = Error.raise((a: \"s\"))\n  \
             operation boomZ() -> Int64 effects Error[T = (z: Bool)] = Error.raise((z: true))\n  \
             operation pickP(f: Bool) -> Int64 effects {{Error[T = (a: Int64, b: String)], Error[T = (b: String, a: Int64, c: Bool)]}} =\n    \
             if f then boom() else boomP()\n  \
             operation pickS(f: Bool) -> Int64 effects {{Error[T = (a: Int64, b: String)], Error[T = (a: String)]}} =\n    \
             if f then boom() else boomS()\n  \
             operation pickZ(f: Bool) -> Int64 effects {{Error[T = (a: Int64, b: String)], Error[T = (z: Bool)]}} =\n    \
             if f then boom() else boomZ()\n  \
             rule shared(?f, ?x) :- Error.reify(lambda () -> pickP(?f), ?x)\n  \
             rule clash(?f, ?x) :- Error.reify(lambda () -> pickS(?f), ?x)\n  \
             rule disjoint(?f, ?x) :- Error.reify(lambda () -> pickZ(?f), ?x)\n"
        ),
    );
    let mut kb = load_kb_with(&program);
    let raised_ab = format!("{ns}.caught({ERR}(error: (a: 1, b: \"x\")))");
    assert_eq!(pattern_answer_counts(&mut kb, &raised_ab), (1, 1), "{raised_ab}");
    for (rule, other) in [
        ("shared", r#"(b: "y", a: 2, c: true)"#),
        ("clash", r#"(a: "s")"#),
        ("disjoint", "(z: true)"),
    ] {
        for (f, raised) in [("true", r#"(a: 1, b: "x")"#), ("false", other)] {
            let q = format!("{ns}.{rule}({f}, {ERR}(error: {raised}))");
            assert_eq!(pattern_answer_counts(&mut kb, &q), (1, 1), "{q}");
        }
    }
}

/// What WI-20261116-411A7 refused, as "a tuple has no type pattern", answers: `admits` at a tuple
/// and at a sort holding one asked of `Int64` (no tuple is a sort), through a generic caller at
/// `(E, Int64)`, a rule-body boundary over a positional tuple payload, and a rule body's goal of
/// `TypePattern` at a tuple. A pattern at a sort whose own `requires` asks a tuple's `TypeValue`
/// answers as before.
#[test]
fn what_was_refused_as_no_tuple_pattern_answers() {
    let ns = "test.hwd8a.t6";
    let program = src(
        ns,
        "  operation atTuple() -> Bool = TypePattern.admits[T = (Int64, Int64)](TypeValue.type_value[T = Int64]())
           operation inList() -> Bool = TypePattern.admits[T = List[T = (Int64, Int64)]](TypeValue.type_value[T = Int64]())
           operation g[E](x: E) -> Bool requires TypeValue[T = E] = TypePattern.admits[T = (E, Int64)](TypeValue.type_value[T = (E, Int64)]())
           operation generic() -> Bool = g(true)
           operation boomPair() -> Int64 effects Error[T = (Int64, Int64)] = Error.raise((1, 2))
           rule caught(?x) :- Error.reify(lambda () -> boomPair(), ?x)
           sort Foo
    requires TypeValue[T = (Int64, Int64)]
    entity foo
  end
           sort Bar
    sort V = ?
    requires TypeValue[T = (V, Int64)]
    entity bar(v: V)
  end
           operation atFoo() -> Bool = TypePattern.admits[T = Foo](TypeValue.type_value[T = Foo]())
           operation atBar() -> Bool = TypePattern.admits[T = Bar[V = Bool]](TypeValue.type_value[T = Bar[V = Bool]]())
           rule pattern() :- TypePattern[T = (Int64, Int64)]
",
    );
    let mut interp = interp_for(&program);
    for (entry, want) in [
        ("atTuple", false),
        ("inList", false),
        ("generic", true),
        ("atFoo", true),
        ("atBar", true),
    ] {
        assert_eq!(bool_of(&mut interp, &format!("{ns}.{entry}")), want, "`{entry}`");
    }
    let mut kb = load_kb_with(&program);
    for goal in [format!("caught({ERR}(error: (1, 2)))"), "pattern()".to_string()] {
        assert_eq!(pattern_answer_counts(&mut kb, &format!("{ns}.{goal}")), (1, 1), "`{goal}`");
    }
}

/// A tuple with an arrow component still has no instance (WI-20261021-VF8GT): a pattern at it and
/// a `SortDomain` at it are refused at load, naming the component.
#[test]
fn a_tuple_holding_an_arrow_is_still_refused() {
    let ns = "test.hwd8a.arrow";
    for (body, tokens) in [
        (
            "  operation g() -> Bool = TypePattern.admits[T = (Int64, (Int64) -> Int64)](TypeValue.type_value[T = Int64]())\n",
            &["anthill.reflect.TypeValue[T = Int64 -> Int64]", "an arrow has none"][..],
        ),
        (
            "  operation countAt[X]() -> Int64 effects {Error} requires SortDomain[T = X] = Wrap[T = X].el.takeN(9).length()\n  \
             operation g() -> Int64 effects {Error} = countAt[X = (Int64, (Int64) -> Int64)]()\n",
            &["nothing provides it at its component `Int64 -> Int64`"][..],
        ),
    ] {
        let errs = load_errors_of(&src(ns, body));
        assert_refused_naming(&errs, tokens, body);
    }
}

/// A head typed at a tuple enumerates the tuples of its components' domains, in the type's
/// order: positional, labelled, inside `Option` (`none` and six), nested (twelve), as a list's
/// element. A component of a type with no cases (`Int64`) keeps its conformance check, so
/// `(Colour, Int64)` answers as a sort with those two fields does — three answers, each
/// conditional. `Bool` was this row's example of such a type until WI-20260911-5TK6B gave it a
/// clause per literal: `(Colour, Bool)` and the sort with those fields now answer six, each
/// definite. `?x <=> (red, 3)` answers it; `?x = (red, 3)` tests and never binds, so its
/// `Int64` stays a residual, and the other colours are refuted.
#[test]
fn a_typed_head_at_a_tuple_enumerates_its_domain() {
    let ns = "test.hwd8a.s1";
    let program = src(
        ns,
        "  sort P\n    entity p(c: Colour, b: Bool)\n  end\n  \
         sort Q\n    entity q(c: Colour, n: Int64)\n  end\n  \
         rule two(?x: (Colour, Size)) :- true\n  \
         rule named(?x: (c: Colour, s: Size)) :- true\n  \
         rule opt(?x: Option[T = (Colour, Size)]) :- true\n  \
         rule nest(?x: (Colour, (Size, Size))) :- true\n  \
         rule lst(?x: List[T = (Colour, Size)]) :- ?x <=> [?a]\n  \
         rule withBool(?x: (Colour, Bool)) :- true\n  \
         rule sortWithBool(?x: P) :- true\n  \
         rule withInt(?x: (Colour, Int64)) :- true\n  \
         rule sortWithInt(?x: Q) :- true\n  \
         rule unified(?x: (Colour, Int64)) :- ?x <=> (Colour.red, 3)\n  \
         rule tested(?x: (Colour, Int64)) :- ?x = (Colour.red, 3)\n  \
         rule unit(?x: ()) :- true\n  \
         operation firstTwo() -> (Colour, Size) effects {Error, Error[EmptyStream]} = two.head.x\n  \
         operation countTwo() -> Int64 effects {Error} = two.takeN(9).length()\n",
    );
    let mut kb = load_kb_with(&program);
    for (goal, want) in [
        ("two(?x)", (6, 6)),
        ("named(?x)", (6, 6)),
        ("opt(?x)", (7, 7)),
        ("nest(?x)", (12, 12)),
        ("lst(?x)", (6, 6)),
        ("withBool(?x)", (6, 6)),
        ("sortWithBool(?x)", (6, 6)),
        ("withInt(?x)", (0, 3)),
        ("sortWithInt(?x)", (0, 3)),
        ("unified(?x)", (1, 1)),
        ("unified((COLOUR.red, 3))", (1, 1)),
        ("tested(?x)", (0, 1)),
        ("unit(?x)", (1, 1)),
    ] {
        let goal = qualified(ns, goal);
        assert_eq!(pattern_answer_counts(&mut kb, &format!("{ns}.{goal}")), want, "`{goal}`");
    }
    let mut interp = interp_for(&program);
    assert_eq!(shown(&mut interp, &format!("{ns}.firstTwo")), "(red, small)");
    assert_eq!(int_of(&mut interp, &format!("{ns}.countTwo")), 6);
}

/// A bound value is checked by label, as a tuple is read: the same labels in another order, and
/// a wider tuple, are members; a value whose component is of another sort is not.
#[test]
fn a_bound_tuple_is_checked_by_label() {
    let ns = "test.hwd8a.s2";
    let program = src(
        ns,
        "  rule two(?x: (Colour, Size)) :- true\n  \
         rule named(?x: (c: Colour, s: Size)) :- true\n  \
         rule permuted(?x: (a: Colour, b: Size)) :- ?x <=> (b: Size.small, a: Colour.red)\n",
    );
    let mut kb = load_kb_with(&program);
    for (goal, want) in [
        ("two((COLOUR.red, SIZE.small))", (1, 1)),
        ("two((COLOUR.red, COLOUR.red))", (0, 0)),
        ("named((s: SIZE.small, c: COLOUR.red))", (1, 1)),
        ("named((c: COLOUR.red, s: SIZE.small, z: 1))", (1, 1)),
        ("permuted(?x)", (1, 1)),
    ] {
        let goal = qualified(ns, goal);
        assert_eq!(pattern_answer_counts(&mut kb, &format!("{ns}.{goal}")), want, "`{goal}`");
    }
}

/// A typed query variable at a tuple is filled as a typed head is (proposal 010.1 §3.1).
#[test]
fn a_typed_query_variable_at_a_tuple_enumerates() {
    let ns = "test.hwd8a.q";
    let mut kb = load_kb_with(&src(ns, "  rule anyOf(?c) :- true\n"));
    let goal = format!("{ns}.anyOf(?c: ({ns}.Colour, {ns}.Size))");
    assert_eq!(pattern_answer_counts(&mut kb, &goal), (6, 6), "{goal}");
}

/// A sort with a field of tuple type has a domain, its field filled as a tuple: `holder`'s six,
/// and `Pair[V = Colour]`'s six, where the tuple holds the sort's parameter.
#[test]
fn a_sort_with_a_tuple_field_has_a_domain() {
    let ns = "test.hwd8a.s3";
    let program = src(
        ns,
        "  sort Holder\n    entity holder(t: (Colour, Size))\n  end\n  \
         sort Pair\n    sort V = ?\n    entity pair(t: (V, Size))\n  end\n  \
         rule h(?x: Holder) :- true\n  \
         rule pr(?x: Pair[V = Colour]) :- true\n",
    );
    let mut kb = load_kb_with(&program);
    for (goal, want) in [
        ("h(?x)", (6, 6)),
        ("h(HOLDER.holder(t: (COLOUR.blue, SIZE.large)))", (1, 1)),
        ("pr(?x)", (6, 6)),
    ] {
        let goal = qualified(ns, goal).replace("HOLDER", &format!("{ns}.Holder"));
        assert_eq!(pattern_answer_counts(&mut kb, &format!("{ns}.{goal}")), want, "`{goal}`");
    }
}

/// A citation at a tuple routes its domain: `Wrap[T = (Colour, Size)].el`, cited from an
/// operation, fills `el`'s `?x` through the tuple's dictionary, and a clause typed at a tuple
/// citing one whose bound is a type variable hands it its own.
#[test]
fn a_citation_routes_a_tuples_domain() {
    let ns = "test.hwd8a.s4";
    let program = src(
        ns,
        "  rule any(?x: ?t) :- true\n  \
         rule cited(?x: (Colour, Size)) :- any(?x)\n  \
         rule anyl(?x: List[T = ?t]) :- ?x <=> [?a]\n  \
         rule citedList(?x: List[T = (Colour, Size)]) :- anyl(?x)\n  \
         operation pairs() -> Int64 effects {Error} = Wrap[T = (Colour, Size)].el.takeN(9).length()\n",
    );
    let mut interp = interp_for(&program);
    assert_eq!(int_of(&mut interp, &format!("{ns}.pairs")), 6);
    let mut kb = load_kb_with(&program);
    for goal in ["cited(?x)", "citedList(?x)"] {
        assert_eq!(pattern_answer_counts(&mut kb, &format!("{ns}.{goal}")), (6, 6), "`{goal}`");
    }
}

/// A written `requires SortDomain[T = X]` is answered at a tuple: `countAt[X = (Colour, Size)]`
/// counts six, through `NamedTuple`'s dictionary, which `Wrap`'s `el` reads through its chain's
/// `Fillable` slot; inside `Option` seven, a labelled tuple holding an `Option` nine, nested
/// twelve, `()` one, inside `Wrap` six. A `requires Fillable[T = X]` at a tuple is answered too:
/// nothing reads a `Fillable` dictionary but a fill, so the row drives its resolution, the call
/// that needs it running.
#[test]
fn a_requirement_at_a_tuple_is_answered() {
    let ns = "test.hwd8a.s5";
    let program = src(
        ns,
        "  operation countAt[X]() -> Int64 effects {Error} requires SortDomain[T = X] =\n    \
         Wrap[T = X].el.takeN(20).length()\n  \
         operation pairs() -> Int64 effects {Error} = countAt[X = (Colour, Size)]()\n  \
         operation optPairs() -> Int64 effects {Error} = countAt[X = Option[T = (Colour, Size)]]()\n  \
         operation labelled() -> Int64 effects {Error} = countAt[X = (a: Colour, b: Option[T = Size])]()\n  \
         operation nested() -> Int64 effects {Error} = countAt[X = (Colour, (Size, Size))]()\n  \
         operation unit() -> Int64 effects {Error} = countAt[X = ()]()\n  \
         operation wrapped() -> Int64 effects {Error} = countAt[X = Wrap[T = (Colour, Size)]]()\n  \
         operation fillableAt[X](x: X) -> Int64 requires Fillable[T = X] = 1\n  \
         operation fillablePair() -> Int64 = fillableAt((Colour.red, Size.small))\n",
    );
    let mut interp = interp_for(&program);
    for (entry, want) in [
        ("pairs", 6),
        ("optPairs", 7),
        ("labelled", 9),
        ("nested", 12),
        ("unit", 1),
        ("wrapped", 6),
        ("fillablePair", 1),
    ] {
        assert_eq!(int_of(&mut interp, &format!("{ns}.{entry}")), want, "`{entry}`");
    }
}

/// No `SortDomain` may be written at a tuple type (user, 2026-11-17): the derived instance answers
/// there, and a written one would never be read. Refused at load, one error per provider and
/// type — at a tuple, at an alias of one, at a labelled tuple, and on a conditional row over a
/// parameter. A `SortDomain` written at a sort loads as before, a sort holding a tuple among its
/// arguments included; that control passes either way by design.
#[test]
fn a_written_sort_domain_at_a_tuple_is_refused() {
    let ns = "test.hwd8a.w";
    let refused = src(
        ns,
        "  sort Pair = (Colour, Colour)\n  \
         sort W\n    entity w\n    provides SortDomain[T = (Colour, Colour)]\n  end\n  \
         sort Al\n    entity al\n    provides SortDomain[T = Pair]\n  end\n  \
         sort Lab\n    entity lab\n    provides SortDomain[T = (a: Colour)]\n  end\n  \
         sort Cond\n    sort A = ?\n    entity cond(a: A)\n    provides SortDomain[T = (A, Int64)] :- SortDomain[T = A]\n  end\n",
    );
    let errs = load_errors_of(&refused);
    assert_eq!(errs.len(), 4, "{errs:#?}");
    for provider in ["W", "Al", "Lab", "Cond"] {
        let token = format!("'{ns}.{provider}' writes `provides anthill.reflect.SortDomain[T = (");
        assert!(errs.iter().any(|e| e.contains(&token)), "`{provider}`: {errs:#?}");
    }
    assert!(errs.iter().all(|e| e.contains("none may be written at a tuple type")), "{errs:#?}");
    let at_sorts = src(
        ns,
        "  sort V\n    entity v\n    provides SortDomain[T = Colour]\n  end\n  \
         sort Inside\n    entity inside\n    provides SortDomain[T = Option[T = (Colour, Colour)]]\n  end\n",
    );
    assert_eq!(load_errors_of(&at_sorts), Vec::<String>::new(), "a SortDomain at a sort loads");
}
