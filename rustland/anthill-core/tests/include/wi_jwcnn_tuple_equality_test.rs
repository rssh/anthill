//! A TUPLE PROVIDES `PartialEq`, AND `Eq`, THROUGH A DERIVED MEMBER THAT IS A DICTIONARY
//! (WI-20261116-JWCNN; proposal 004, "Extension (2026-11-16): a tuple is a `NamedTuple`"). A
//! tuple type is the sort `NamedTuple` applied to its components. It provides `PartialEq` where
//! each component's type does and `Eq` where each provides `Eq`; the instance is
//! `Dictionary(d1 … dn, impl: NamedTuple)`, one sub-dictionary per component, and its `eq`
//! compares the components through their own members. Before, a tuple had no sort to carry a
//! provision: `=` at a tuple was compared component by component with no member, each through
//! the equality index (which reads a value's constructor), a requirement at a tuple was refused
//! as "a STRUCTURAL FORMER", and a sort applied to a tuple derived no equality.
//!
//! Each row is over a `Pt` whose own `eq` compares `x` alone, so `pt(1, 2)` and `pt(1, 9)` are
//! equal by it and apart by structure: an answer of `true` is `Pt`'s member.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches in one build, then removed. The control is every switch
//! unset: every row passes.
//!
//! * No tuple instance (`typing::synth`'s `tuple_instance`): every row fails, the standard
//!   library itself refused at a tuple's `=` ("no impl provides `PartialEq[T = (_1: String,
//!   _2: String)]`"), since `=` at a tuple is now dispatched as any call of a member is.
//! * The dispatch not reaching it (`resolve_at_goal`'s exit on no provision row):
//!   [`a_typed_tuple_equality_reads_its_components_members`] and
//!   [`a_tuples_law_is_its_components`] fail, refused at load.
//! * The call pinned without the dictionary (`classify_pin_or_apply_within`): the same two
//!   fail, `namedTupleEq` entered with no dictionary.
//! * The resolver splitting a pinned tuple equality into components (`sem_eq_values_at`):
//!   [`a_typed_tuple_equality_reads_its_components_members`] fails, its rule body reading the
//!   index twice.
//! * No entry for the tuple's member (`dictionary_owed_to`): the same row fails, at its rule
//!   body.
//! * A host member bridged through a dictionary not handed it (`call_op_bridged`): that row
//!   fails at its rule body, and [`a_requirement_at_a_tuple_is_handed_its_dictionary`] at the
//!   nested tuple.
//! * A tuple as a type argument deriving nothing (`eq_derive::field_conditions`):
//!   [`a_sort_applied_to_a_tuple_derives_its_equality`] fails at `Holder`.
//! * Each pair of a pinned tuple's components not compared at its own member
//!   (`resolve::tuple_component_pins`, the tuple's member run through the bridge instead):
//!   [`a_decided_component_decides_a_tuple_with_an_unbound_one`] fails, `(?a, 3) = (1, 4)` a
//!   residual.
//! * A tuple's `Eq` dictionary holding its components' dictionaries rather than the tuple's
//!   `PartialEq` dictionary in the slot `Eq`'s chain gives it (`typing::synth`'s
//!   `tuple_instance`): [`an_eq_requirement_at_a_tuple_is_handed_its_dictionary`] fails, `Pt`'s
//!   `eq` handed the whole tuple (`match_failed`), the body's projection to `PartialEq` landing
//!   on the first component's dictionary.
//! * A derived `NonEq` row carrying `PartialEq[q]` for each condition of the carrier's
//!   `PartialEq`, not the condition as derived (`eq_derive::derive_conditional_noneq`):
//!   [`a_sort_needing_a_lawful_parameter_loads`] fails, refused at load.
//!
//! * The tuple's member pairing the values' components by position and count, not by the
//!   dictionary's labels (`eval::builtins::named_tuple_eq`): [`a_value_wider_than_its_tuple_type_is_compared_at_its_labels`]
//!   fails, `namedTupleEq: the tuples have 3 components and the dictionary 2`.
//! * The resolver's pinned compare pairing them so (`resolve::tuple_component_pins`'s labels
//!   unread): the same row fails at its rule body.
//! * No labels on the tuple's `PartialEq` dictionary (`typing::synth`'s `tuple_instance`):
//!   every row comparing a tuple at run time fails, `namedTupleEq` entered with a dictionary
//!   holding no labels.
//!
//! [`a_tuple_with_a_component_without_equality_is_refused`] passes under every switch but the
//! first, by design: the refusals it asserts held before.
//!
//! THE INDEX READS ARE NO LONGER COUNTED (WI-20261105-CBRD2, part 5r): every run-time reader of
//! the equality index is gone, and its counter with them, so no comparison can be decided by
//! reading a value's constructor there. A back-out above that fails "on the index reads" is of
//! code that no longer exists; the rows keep their verdicts.

use anthill_core::eval::Value;

use crate::common::{interp_for, load_errors_of, load_kb_with, pattern_answer_counts};

fn src(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String, Float, List, Map, Relation, PartialEq, Eq}}
  sort Pt
    entity pt(x: Int64, y: Int64)
    provides PartialEq[T = Pt]
    provides Eq[T = Pt]
    operation eq(a: Pt, b: Pt) -> Bool =
      match a case pt(ax, ay) -> match b case pt(bx, by) -> PartialEq.eq(ax, bx)
  end
  operation same[A](a: A, b: A) -> Bool requires PartialEq[T = A] = PartialEq.eq(a, b)
{body}
end
"#
    )
}

/// `entry`'s `Bool` answer, on a fresh interpreter.
fn run(src: &str, entry: &str) -> bool {
    let mut interp = interp_for(src);
    match interp.call(entry, &anthill_core::eval::HostValue::all(&[])).map(|h| h.value) {
        Ok(Value::Bool(b)) => b,
        other => panic!("{entry}: expected a Bool, got {other:?}"),
    }
}

/// The query `pattern`'s `(definite, total)` answers.
fn ask(kb: &mut anthill_core::kb::KnowledgeBase, pattern: &str) -> (usize, usize) {
    pattern_answer_counts(kb, pattern)
}

/// T1: `(pt(1, 2), 3) = (pt(1, 9), 3)` holds through `Pt`'s `eq`, and `(pt(1, 2), 3) = (pt(2,
/// 2), 3)` does not, in a rule body, an operation body and a query, the index read by none.
#[test]
fn a_typed_tuple_equality_reads_its_components_members() {
    let ns = "test.jwcnn.t1";
    let program = src(
        ns,
        "  rule holds() :- (pt(1, 2), 3) = (pt(1, 9), 3)\n  \
         rule apart() :- (pt(1, 2), 3) = (pt(2, 2), 3)\n  \
         operation op() -> Bool = (pt(1, 2), 3) = (pt(1, 9), 3)\n  \
         operation opApart() -> Bool = (pt(1, 2), 3) = (pt(2, 2), 3)",
    );
    let mut kb = load_kb_with(&program);
    let pt = |x: i64, y: i64| format!("{ns}.Pt.pt({x}, {y})");
    for (pattern, want) in [
        (format!("{ns}.holds()"), (1, 1)),
        (format!("{ns}.apart()"), (0, 0)),
        (format!("({}, 3) = ({}, 3)", pt(1, 2), pt(1, 9)), (1, 1)),
        (format!("({}, 3) = ({}, 3)", pt(1, 2), pt(2, 9)), (0, 0)),
    ] {
        assert_eq!(ask(&mut kb, &pattern), want, "`{pattern}`");
    }
    for (entry, want) in [("op", true), ("opApart", false)] {
        assert_eq!(run(&program, &format!("{ns}.{entry}")), want, "`{entry}`");
    }
}

/// T2: `same[A] requires PartialEq[T = A]` called with two tuples is handed the tuple's
/// dictionary — a pair, a named tuple, one passed with its labels in another order, a nested
/// tuple, the unit — and answers through `Pt`'s `eq`.
#[test]
fn a_requirement_at_a_tuple_is_handed_its_dictionary() {
    let ns = "test.jwcnn.t2";
    let program = src(
        ns,
        "  operation pair() -> Bool = same((pt(1, 2), 3), (pt(1, 9), 3))\n  \
         operation pairApart() -> Bool = same((pt(1, 2), 3), (pt(2, 2), 3))\n  \
         operation named() -> Bool = same((a: pt(1, 2), b: 3), (a: pt(1, 9), b: 3))\n  \
         operation cmpAt(x: (a: Pt, b: Int64), y: (a: Pt, b: Int64)) -> Bool = same(x, y)\n  \
         operation permuted() -> Bool = cmpAt((b: 3, a: pt(1, 2)), (a: pt(1, 9), b: 3))\n  \
         operation nested() -> Bool = same(((pt(1, 2), 3), 4), ((pt(1, 9), 3), 4))\n  \
         operation unit() -> Bool = same((), ())",
    );
    for (entry, want) in [
        ("pair", true),
        ("pairApart", false),
        ("named", true),
        ("permuted", true),
        ("nested", true),
        ("unit", true),
    ] {
        assert_eq!(run(&program, &format!("{ns}.{entry}")), want, "`{entry}`");
    }
}

/// T3: a sort applied to a tuple derives its equality through the tuple's instance — `List[T =
/// (Pt, Int64)]`, and an entity whose field is typed so.
#[test]
fn a_sort_applied_to_a_tuple_derives_its_equality() {
    let ns = "test.jwcnn.t3";
    let program = src(
        ns,
        "  sort Holder\n    entity holder(xs: List[T = (Pt, Int64)])\n  end\n  \
         rule listHolds() :- [(pt(1, 2), 3)] = [(pt(1, 9), 3)]\n  \
         rule listApart() :- [(pt(1, 2), 3)] = [(pt(2, 9), 3)]\n  \
         operation holderEq() -> Bool = holder(xs: [(pt(1, 2), 3)]) = holder(xs: [(pt(1, 9), 3)])",
    );
    let mut kb = load_kb_with(&program);
    assert_eq!(ask(&mut kb, &format!("{ns}.listHolds()")), (1, 1));
    assert_eq!(ask(&mut kb, &format!("{ns}.listApart()")), (0, 0));
    assert_eq!(run(&program, &format!("{ns}.holderEq")), true);
}

/// T7, T8, T5: a tuple with a component providing no `PartialEq` has none, and `PartialEq.eq`
/// at it is refused; `(Int64, Float)` provides no `Eq`, so it is no `Map` key; `(Int64, Bool)`
/// is one.
#[test]
fn a_tuple_with_a_component_without_equality_is_refused() {
    let errs = load_errors_of(&src(
        "test.jwcnn.t7",
        "  rule rel(?x) :- ?x <=> 1\n  \
         operation t7(a: (Int64, Relation[T = (x: Int64), E = {}]), \
         b: (Int64, Relation[T = (x: Int64), E = {}])) -> Bool = PartialEq.eq(a, b)",
    ));
    assert!(
        errs.len() == 1 && errs[0].contains("PartialEq") && errs[0].contains("Relation"),
        "{errs:?}"
    );
    let errs = load_errors_of(&src(
        "test.jwcnn.t8",
        "  operation t8(m: Map[K = (Int64, Float), V = Int64]) -> Int64 = 0",
    ));
    assert!(errs.len() == 1 && errs[0].contains("Hash") && errs[0].contains("Float"), "{errs:?}");
    let errs = load_errors_of(&src(
        "test.jwcnn.t5",
        "  operation t5(m: Map[K = (Int64, Bool), V = Int64]) -> Int64 = 0",
    ));
    assert!(errs.is_empty(), "{errs:?}");
}

/// A tuple's law is its components': `(nan, 1)` is not equal to itself, `Float`'s `eq` being
/// IEEE, and `(1, "a")` is.
#[test]
fn a_tuples_law_is_its_components() {
    let ns = "test.jwcnn.law";
    let program = src(
        ns,
        "  operation nanPair() -> Bool = (Float.div(0.0, 0.0), 1) = (Float.div(0.0, 0.0), 1)\n  \
         operation plain() -> Bool = (1, \"a\") = (1, \"a\")",
    );
    assert_eq!(run(&program, &format!("{ns}.nanPair")), false);
    assert_eq!(run(&program, &format!("{ns}.plain")), true);
}

/// A sort whose equality needs one of its parameters lawful — a field `s: Set[T = F]`, its
/// `PartialEq` conditioned on `Eq[F]` — loads, the key a parameter, a tuple over one or a `Pair`
/// over one alike: the `NonEq` row derived beside it carries that condition as derived. It
/// carried `PartialEq[F]`, which does not entail `Eq[F]`, and the sort was refused ("provides
/// `NonEq` … but only under `Eq[T = F]`"); a tuple there reached it once a tuple as a type
/// argument derived. Its equality answers at a lawful `F`.
#[test]
fn a_sort_needing_a_lawful_parameter_loads() {
    for (n, key) in ["F", "(a: F, b: Int64)", "Pair[A = F, B = Int64]"].into_iter().enumerate() {
        let ns = format!("test.jwcnn.lawful{n}");
        let program = format!(
            "namespace {ns}\n  import anthill.prelude.{{Int64, Bool, Set, Pair}}\n  \
             sort G\n    sort F = ?\n    entity g(s: Set[T = {key}])\n  end\nend\n"
        );
        let errs = load_errors_of(&program);
        assert!(errs.is_empty(), "`s: Set[T = {key}]`: {errs:?}");
    }
    let ns = "test.jwcnn.lawfuleq";
    let program = format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, Bool, Set}}\n  \
         sort G\n    sort F = ?\n    entity g(s: Set[T = F])\n  end\n  \
         operation same() -> Bool = g(s: {{1, 2}}) = g(s: {{1, 2}})\n  \
         operation apart() -> Bool = g(s: {{1, 2}}) = g(s: {{1, 3}})\nend\n"
    );
    assert_eq!(run(&program, &format!("{ns}.same")), true);
    assert_eq!(run(&program, &format!("{ns}.apart")), false);
}

/// A rule's `=` at a tuple holding an unbound component is decided by a component that is: `(?a,
/// 3) = (1, 4)` fails at its second, `(?a, 3) = (1, 3)` answers once `?a` is bound. Each pair is
/// compared at the member its sub-dictionary names, not the tuple's member waiting for both
/// operands to be ground.
#[test]
fn a_decided_component_decides_a_tuple_with_an_unbound_one() {
    let ns = "test.jwcnn.unbound";
    let mut kb = load_kb_with(&src(
        ns,
        "  fact v(1)\n  rule apart(?a) :- (?a, 3) = (1, 4)\n  rule bound(?a) :- (?a, 3) = (1, 3), v(?a)",
    ));
    assert_eq!(ask(&mut kb, &format!("{ns}.apart(?a)")), (0, 0));
    assert_eq!(ask(&mut kb, &format!("{ns}.bound(?a)")), (1, 1));
}

/// An `Eq` requirement at a tuple is handed the tuple's `Eq` dictionary where each component
/// provides `Eq`, and is refused where one does not (`Float`).
#[test]
fn an_eq_requirement_at_a_tuple_is_handed_its_dictionary() {
    let ns = "test.jwcnn.eqreq";
    let decl = "  operation sameEq[A](a: A, b: A) -> Bool requires Eq[T = A] = PartialEq.eq(a, b)\n";
    let program = src(ns, &format!("{decl}  operation pair() -> Bool = sameEq((pt(1, 2), 3), (pt(1, 9), 3))"));
    assert_eq!(run(&program, &format!("{ns}.pair")), true);
    let errs = load_errors_of(&src(
        "test.jwcnn.eqreqf",
        &format!("{decl}  operation floats() -> Bool = sameEq((1, 0.5), (1, 0.5))"),
    ));
    assert!(errs.len() == 1 && errs[0].contains("Eq") && errs[0].contains("Float"), "{errs:?}");
}

/// A VALUE WIDER THAN ITS TUPLE TYPE IS COMPARED AT THE TYPE'S LABELS (kernel-language §4.5:
/// `<:` is by label with width and permutation, and every reader of a tuple reads by label). The
/// tuple's `PartialEq` dictionary carries the type's labels, and its member reads each value's
/// component by them: through `(Int64, String)`, `(1, "s", true)` and `(1, "s", false)` are
/// equal, and `(2, "s", true)` is not; through `(a: Int64, b: String)` a permuted value and a
/// wider one in another order are equal; and so inside a tuple, a list, an `=` in an operation
/// body and one in a rule body. Before, the member paired the values' components by position
/// and count, and each of these raised `namedTupleEq: the tuples have 3 components and the
/// dictionary 2` (the rule body: undecided). The `Pt` component is compared by its own member.
#[test]
fn a_value_wider_than_its_tuple_type_is_compared_at_its_labels() {
    let ns = "test.jwcnn.width";
    let program = src(
        ns,
        "  operation pos(x: (Int64, String), y: (Int64, String)) -> Bool = PartialEq.eq(x, y)\n  \
         operation eqWider() -> Bool = pos((1, \"s\", true), (1, \"s\", false))\n  \
         operation eqVisibleDiffers() -> Bool = pos((1, \"s\", true), (2, \"s\", true))\n  \
         operation named(x: (a: Pt, b: String), y: (a: Pt, b: String)) -> Bool = PartialEq.eq(x, y)\n  \
         operation eqPermuted() -> Bool = named((b: \"s\", a: pt(1, 2)), (a: pt(1, 9), b: \"s\"))\n  \
         operation eqNamedWider() -> Bool = named((a: pt(1, 2), b: \"s\", c: 3), (c: 4, b: \"s\", a: pt(1, 2)))\n  \
         operation nested(x: ((Int64, String), Int64), y: ((Int64, String), Int64)) -> Bool = PartialEq.eq(x, y)\n  \
         operation eqNestedWider() -> Bool = nested(((1, \"s\", true), 2), ((1, \"s\", false), 2))\n  \
         operation list(x: List[T = (a: Int64)], y: List[T = (a: Int64)]) -> Bool = PartialEq.eq(x, y)\n  \
         operation eqListWider() -> Bool = list([(a: 1, b: 2)], [(a: 1, b: 3)])\n  \
         operation op(x: (a: Int64), y: (a: Int64)) -> Bool = x = y\n  \
         operation eqOpWider() -> Bool = op((a: 1, b: 2), (a: 1, b: 3))\n  \
         operation wideA() -> (a: Int64) = (a: 1, b: 2)\n  \
         operation wideB() -> (a: Int64) = (b: 3, a: 1)\n  \
         operation wideC() -> (a: Int64) = (a: 2, b: 2)\n  \
         rule ruleSame() :- wideA() = wideB()\n  \
         rule ruleApart() :- wideA() = wideC()",
    );
    for (entry, want) in [
        ("eqWider", true),
        ("eqVisibleDiffers", false),
        ("eqPermuted", true),
        ("eqNamedWider", true),
        ("eqNestedWider", true),
        ("eqListWider", true),
        ("eqOpWider", true),
    ] {
        assert_eq!(run(&program, &format!("{ns}.{entry}")), want, "`{entry}`");
    }
    let mut kb = load_kb_with(&program);
    assert_eq!(ask(&mut kb, &format!("{ns}.ruleSame()")), (1, 1), "ruleSame");
    assert_eq!(ask(&mut kb, &format!("{ns}.ruleApart()")), (0, 0), "ruleApart");
}

/// `neq` at a tuple type is `PartialEq`'s body run with the tuple's instance, `NamedTuple`'s
/// built from its components': `false` for two values equal at the type's labels, `true` for two
/// that differ there, in an operation body and as a rule-body goal. A tuple has no sort to read
/// a carrier off, so the call was given no instance: it died when run, `var_ref(__req_self)
/// unbound`, and the goal was undecided. FAILS with the carrier of a tuple-typed argument read
/// as nothing again (`carrier_param_receiver`).
#[test]
fn neq_at_a_tuple_type_runs_at_the_tuples_instance() {
    let ns = "test.jwcnn.neq";
    let program = src(
        ns,
        "  import anthill.prelude.PartialEq.{neq}\n  \
         operation wideA() -> (a: Int64) = (a: 1, b: 2)\n  \
         operation wideB() -> (a: Int64) = (a: 1, b: 3)\n  \
         operation wideC() -> (a: Int64) = (a: 2, b: 2)\n  \
         operation nq(x: (a: Int64), y: (a: Int64)) -> Bool = PartialEq.neq(x, y)\n  \
         operation sameNq() -> Bool = nq(wideA(), wideB())\n  \
         operation apartNq() -> Bool = nq(wideA(), wideC())\n  \
         rule ruleSame() :- neq(wideA(), wideB())\n  \
         rule ruleApart() :- neq(wideA(), wideC())",
    );
    assert_eq!(run(&program, &format!("{ns}.sameNq")), false, "sameNq");
    assert_eq!(run(&program, &format!("{ns}.apartNq")), true, "apartNq");
    let mut kb = load_kb_with(&program);
    assert_eq!(ask(&mut kb, &format!("{ns}.ruleSame()")), (0, 0), "ruleSame");
    assert_eq!(ask(&mut kb, &format!("{ns}.ruleApart()")), (1, 1), "ruleApart");
}
