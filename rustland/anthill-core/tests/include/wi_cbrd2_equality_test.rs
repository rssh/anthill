//! AN EQUALITY IS ITS CARRIER'S MEMBER (WI-20261105-CBRD2, proposal 073 §5's §5.3 sentence,
//! decided with the user 2026-11-09 and 2026-11-12). `=` (`PartialEq.eq`) and `!=` are read as
//! any call of a spec's member is: at a type the clause fixes, the carrier's member; at a type
//! parameter the clause declares `PartialEq` for, the member its citation's dictionary names; at a
//! type the clause leaves open and declares nothing for, refused at load, in a rule body and in
//! a query. A `Term` provides `PartialEq` (decided with the user 2026-11-14), and a tuple's
//! equality is its components'.
//!
//! ## What fails with each part backed out
//!
//! Measured with temporary switches in one build, then removed. The control is every switch
//! unset: every row passes.
//!
//! * `PartialEq.eq` counted as host-implemented again (`host_implements`):
//!   [`an_equality_at_an_open_type_is_refused`], [`a_querys_equality_is_typed_where_it_is_read`],
//!   [`a_tuples_equality_is_its_components`] (the function component loads),
//!   [`an_applied_higher_kinded_field_derives_no_equality`] (two holders compared load) and
//!   JEE0E's `an_untyped_neq_goal_is_refused_and_a_declared_one_answers`;
//! * the hand-off to the clause skipping it as a builtin (`leave_to_the_clause`,
//!   `dispatch_to_the_clause`): [`an_equality_at_an_open_type_is_refused`];
//! * the weave reading no woven `=` (`woven_goal_has_reader`, `inferred_demand`):
//!   [`an_equality_at_an_open_type_is_refused`];
//! * the resolver reading no woven `=` (`woven_equality`):
//!   [`an_equality_under_a_declared_requirement_reads_the_citations_dictionary`], and the rows of
//!   WI-616, WI-837 and WI-859 rewritten to declare the requirement — eleven, each answering
//!   nothing;
//! * a query's `=` owing no instance (`owes_an_instance`):
//!   [`a_querys_equality_is_typed_where_it_is_read`];
//! * a query's variables not typed as a clause's are (`query_goal_var_types`):
//!   [`a_querys_equality_is_typed_where_it_is_read`], four rows of 6Q43W and CBRD2's
//!   `an_equality_beside_a_typed_call_is_not_typed_as_a_call`;
//! * a query's untyped variable not given a type of its own (the fresh variable in
//!   `typed_spec_op_calls`): [`a_querys_equality_is_typed_where_it_is_read`] (a tie, not "a
//!   query has no caller") and CBRD2's `a_querys_spec_op_call_at_a_type_nothing_provides_or_fixes_is_refused`
//!   (measured before the anonymous `?` was given an open type too, which that row also reads);
//! * `=` at a tuple owing an instance at the tuple (`tuple_component_without_equality`'s caller,
//!   `equality_by_components`): [`a_tuples_equality_is_its_components`], nine rows of 7G99A and
//!   one of 6Q43W;
//! * a tuple literal untyped by the clause walk (`Expr::TupleLit` in
//!   `collect_occurrence_type_constraints`): [`a_tuples_equality_is_its_components`];
//! * an applied higher-kinded field read as a condition over the parameter (`field_conditions`):
//!   [`an_applied_higher_kinded_field_derives_no_equality`], two rows of QV5W5 and WI-452's
//!   `marked_carrier_in_entity_field_loads_clean`;
//! * a field typed by a tuple deriving nothing (`field_conditions`):
//!   [`a_tuples_equality_is_its_components`] and 7G99A's
//!   `an_entity_an_operation_built_with_unit_equals_the_one_a_rule_writes`;
//! * a query's construction holding a call read off its value (`holds_an_operation_call`):
//!   WI-616's `buried_override_suspends_instead_of_structural_verdict`.
//! * the refusals proposing no `===` (`structural_equality_hint`):
//!   [`an_equality_at_an_open_type_is_refused`] (its rule rows and its operation-body rows) and
//!   [`a_querys_equality_is_typed_where_it_is_read`].
//!
//! [`a_term_compares_by_its_structure`] passes under each, by design: its subject is the
//! library's provision, and without it each of its rules is refused at load, `Term` providing
//! no `PartialEq` (measured before the provision was written).

use anthill_core::kb::term_view::TermView;
use anthill_core::kb::KnowledgeBase;

/// `Pt`'s own `eq` compares `x` alone, so `pt(1, 2)` and `pt(1, 9)` are equal by it and apart
/// by structure: an answer of `true` is `Pt`'s member.
const PT: &str = r#"
  sort Pt
    entity pt(x: Int64, y: Int64)
    provides PartialEq[T = Pt]
    provides Eq[T = Pt]
    operation eq(a: Pt, b: Pt) -> Bool =
      match a case pt(ax, ay) -> match b case pt(bx, by) -> PartialEq.eq(ax, bx)
  end
"#;

fn program(ns: &str, body: &str) -> String {
    format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, Bool, Float, String, PartialEq, Eq}}\n\
         {PT}{body}end\n"
    )
}

/// `(definite, total)` answers of the query `pattern`, written in full.
fn answers(kb: &mut KnowledgeBase, pattern: &str) -> (usize, usize) {
    crate::common::pattern_answer_counts(kb, pattern)
}

/// AT A TYPE THE CLAUSE LEAVES OPEN, AND DECLARES NOTHING FOR, AN EQUALITY IS REFUSED: as a goal,
/// as `!=`, under `not`, at a variable only the body binds, and at the `T` of a sort that
/// requires nothing. Each loaded and was decided by the value's sort when the goal ran. The
/// refusal proposes `===`, as an operation body's `=` at a type parameter it requires nothing
/// for does; a call of another spec's member at an open type is not told it.
#[test]
fn an_equality_at_an_open_type_is_refused() {
    for (rule, why) in [
        ("rule same(?a, ?b) :- ?a = ?b", "a rule takes no dictionary it does not declare"),
        ("rule same(?a, ?b) :- eq(?a, ?b)", "a rule takes no dictionary it does not declare"),
        ("rule same(?a, ?b) :- ?a != ?b", "a rule takes no dictionary it does not declare"),
        ("rule same(?a, ?b) :- not(?a = ?b)", "a rule takes no dictionary it does not declare"),
        ("rule same(?r) :- ?a = ?b, ?r <=> 1", "no head column of the clause reaches"),
        (
            "sort Scope\n    sort T = ?\n    rule same(?a: T, ?b: T) :- ?a = ?b\n  end",
            "a rule takes no dictionary it does not declare",
        ),
    ] {
        let src = program("test.cbrd2eq.open", &format!("  import anthill.prelude.PartialEq.{{eq}}\n  {rule}\n"));
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&src),
            &["same.body", "PartialEq", why, STRUCTURAL],
            rule,
        );
    }
    // An operation body's `=` at a type parameter it requires nothing for proposes it too.
    for (n, body) in ["a = b", "a != b"].into_iter().enumerate() {
        let src = program(
            &format!("test.cbrd2eq.op{n}"),
            &format!("  operation same[T](a: T, b: T) -> Bool = {body}\n"),
        );
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&src),
            &["same", "PartialEq", STRUCTURAL],
            body,
        );
    }
    let other = program(
        "test.cbrd2eq.other",
        "  sort Desc\n    sort T = ?\n    operation describe(x: T) -> Int64\n  end\n  \
         sort Leaf\n    entity leaf\n    provides Desc[T = Leaf]\n    \
         operation describe(x: Leaf) -> Int64 = 7\n  end\n  \
         rule d(?x, ?r) :- Desc.describe(?x, ?r)\n",
    );
    let errs = crate::common::load_errors_of(&other);
    crate::common::assert_refused_naming(&errs, &["d.body", "Desc", "a rule takes no dictionary"], "describe");
    assert!(errs.iter().all(|e| !e.contains("===")), "{errs:?}");
}

/// What a refusal of an equality no type reaches proposes.
const STRUCTURAL: &str = "`===` compares any two values structurally";

/// …AND DECLARED AT THE HEAD'S TYPE PARAMETER IT READS THE CITATION'S DICTIONARY: `eqG(pt(1, 2),
/// pt(1, 9))` holds through `Pt`'s own `eq`, which structure does not; `!=` is its negation; a
/// sort's `requires` its citation fixes passes it as well; and a value slot reads it too.
#[test]
fn an_equality_under_a_declared_requirement_reads_the_citations_dictionary() {
    let src = program(
        "test.cbrd2eq.declared",
        r#"
  rule eqG[A](?a: A, ?b: A) :- PartialEq[T = A], ?a = ?b
  rule neqG[A](?a: A, ?b: A) :- PartialEq[T = A], ?a != ?b
  rule valueG[A](?a: A, ?b: A, ?r) :- PartialEq[T = A], ?r <=> (?a = ?b)
  sort Holder
    sort T = ?
    requires PartialEq[T = T]
    rule same(?a: T, ?b: T) :- ?a = ?b
  end
  rule guarded() :- eqG(pt(1, 2), pt(1, 9))
  rule apart() :- eqG(pt(1, 2), pt(2, 2))
  rule nGuarded() :- neqG(pt(1, 2), pt(1, 9))
  rule nApart() :- neqG(pt(1, 2), pt(2, 2))
  rule ints() :- eqG(3, 3)
  rule intsApart() :- eqG(3, 4)
  rule nans() :- eqG(0.0 / 0.0, 0.0 / 0.0)
  rule viaSort() :- Holder[T = Pt].same(pt(1, 2), pt(1, 9))
  rule inValue(?r) :- valueG(pt(1, 2), pt(1, 9), ?r)
"#,
    );
    let mut kb = crate::common::load_kb_with(&src);
    for (goal, want) in [
        ("guarded()", (1, 1)),
        ("apart()", (0, 0)),
        ("nGuarded()", (0, 0)),
        ("nApart()", (1, 1)),
        ("ints()", (1, 1)),
        ("intsApart()", (0, 0)),
        ("nans()", (0, 0)),
        ("viaSort()", (1, 1)),
    ] {
        assert_eq!(answers(&mut kb, &format!("test.cbrd2eq.declared.{goal}")), want, "`{goal}`");
    }
    assert_eq!(
        crate::common::query_unary(&mut kb, "test.cbrd2eq.declared.inValue")
            .iter()
            .map(|(v, definite)| (crate::common::scalar_bool(&kb, v), *definite))
            .collect::<Vec<_>>(),
        [(Some(true), true)],
        "`?r <=> (?a = ?b)` at `Pt`"
    );
}

/// A QUERY'S EQUALITY IS TYPED WHERE IT IS READ: at the type its operands fix it is the
/// carrier's member (`pt(1, 2) = pt(1, 9)` through `Pt`'s `eq`, `!=` its negation), and a
/// variable is at the type the query's goals give it (`?x = 3` waits on `?x` at `Int64`). One
/// nothing types is refused where the query is read, proposing `===`: `?a = ?b`, `?a != ?b`.
#[test]
fn a_querys_equality_is_typed_where_it_is_read() {
    let mut kb = crate::common::load_kb_with(&program("test.cbrd2eq.query", ""));
    let pt = |x: i64, y: i64| format!("test.cbrd2eq.query.Pt.pt({x}, {y})");
    assert_eq!(answers(&mut kb, &format!("{} = {}", pt(1, 2), pt(1, 9))), (1, 1));
    assert_eq!(answers(&mut kb, &format!("{} != {}", pt(1, 2), pt(1, 9))), (0, 0));
    assert_eq!(answers(&mut kb, &format!("{} = {}", pt(1, 2), pt(2, 2))), (0, 0));
    assert_eq!(answers(&mut kb, "?x = 3"), (0, 1), "`?x = 3` waits on `?x`");
    assert_eq!(answers(&mut kb, "3 = ?x"), (0, 1), "`3 = ?x` waits on `?x`");
    for open in ["?a = ?b", "?a != ?b"] {
        crate::common::assert_refused_naming(
            &crate::common::query_pattern_refusals(&mut kb, open),
            &["anthill.prelude.PartialEq", "a query has no caller", STRUCTURAL],
            open,
        );
    }
}

/// A `Term` PROVIDES `PartialEq`, ITS STRUCTURE: two terms built alike are equal, two built
/// apart are not, and a term that is a `Float` compares as one (`as_term(nan)` is not equal to
/// itself) while code holding a `nan` equals itself — the answers `=` gave terms before.
#[test]
fn a_term_compares_by_its_structure() {
    let src = r#"
namespace test.cbrd2eq.term
  import anthill.prelude.{Int64, Float, Bool}
  import anthill.reflect.{Term, make_fn, as_term}
  operation addT() -> Term = make_fn("anthill.prelude.Int64.add", [as_term(1), as_term(2)])
  operation subT() -> Term = make_fn("anthill.prelude.Int64.sub", [as_term(1), as_term(2)])
  operation nanT() -> Term = make_fn("anthill.prelude.Float.add", [as_term(0.0 / 0.0), as_term(1.0)])
  operation bareNan() -> Term = as_term(0.0 / 0.0)
  rule same() :- ?t <=> addT(), ?u <=> addT(), ?t = ?u
  rule apart() :- ?t <=> addT(), ?u <=> subT(), ?t = ?u
  rule codeNan() :- ?t <=> nanT(), ?u <=> nanT(), ?t = ?u
  rule bare() :- ?t <=> bareNan(), ?u <=> bareNan(), ?t = ?u
  operation opBare() -> Bool = bareNan() = bareNan()
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    for (goal, want) in [("same()", (1, 1)), ("apart()", (0, 0)), ("codeNan()", (1, 1)), ("bare()", (0, 0))] {
        assert_eq!(answers(&mut kb, &format!("test.cbrd2eq.term.{goal}")), want, "`{goal}`");
    }
    let mut interp = crate::common::interp_for(src);
    let got = interp.call("test.cbrd2eq.term.opBare", &[]).expect("runs");
    assert_eq!(got.literal_bool(interp.kb()), Some(false), "`as_term(nan) = as_term(nan)`");
}

/// A TUPLE'S EQUALITY IS ITS COMPONENTS': no instance at the tuple and one at each component —
/// `(n, 1) = (n, 1)` is false for a `nan`, `() = ()` holds, a function component is refused —
/// and a variable `<=>` binds to a tuple is of the tuple's type, in a clause and in a query.
#[test]
fn a_tuples_equality_is_its_components() {
    let src = r#"
namespace test.cbrd2eq.tuple
  import anthill.prelude.{Int64, Float, Bool, Unit}
  operation nan() -> Float = 0.0 / 0.0
  operation withNan() -> Bool =
    let n = nan()
    (n, 1) = (n, 1)
  operation plain() -> Bool = (1.5, 1) = (1.5, 1)
  operation units() -> Bool = () = ()
  rule bound(?r) :- ?t <=> (1, 2), ?u <=> (1, 2), ?t = ?u, ?r <=> 1
  sort U
    entity u(v: Unit, n: Int64)
  end
  operation mk() -> U = U.u(v: (), n: 4)
  rule unitField() :- ?x <=> mk(), ?x = U.u(v: (), n: 4)
  rule unitFieldApart() :- ?x <=> mk(), ?x = U.u(v: (), n: 5)
end
"#;
    let mut interp = crate::common::interp_for(src);
    for (op, want) in [("withNan", false), ("plain", true), ("units", true)] {
        let got = interp.call(&format!("test.cbrd2eq.tuple.{op}"), &[]).expect("runs");
        assert_eq!(got.literal_bool(interp.kb()), Some(want), "`{op}`");
    }
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(crate::common::pattern_last_ints(&mut kb, "test.cbrd2eq.tuple.bound(?r)"), [1]);
    assert_eq!(answers(&mut kb, "test.cbrd2eq.tuple.unitField()"), (1, 1));
    assert_eq!(answers(&mut kb, "test.cbrd2eq.tuple.unitFieldApart()"), (0, 0));
    assert_eq!(answers(&mut kb, "anthill.kernel.and(?v <=> (1, 2), ?v = (1, 2))"), (1, 1));
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(
            "namespace test.cbrd2eq.fns\n  import anthill.prelude.{Int64, Bool}\n  \
             operation fns() -> Bool = (lambda (x: Int64) -> x, 1) = (lambda (x: Int64) -> x, 1)\nend\n",
        ),
        &["PartialEq", "Int64 -> Int64"],
        "a function component",
    );
}

/// A SORT WHOSE FIELD IS A HIGHER-KINDED PARAMETER APPLIED DERIVES NO EQUALITY: `PartialEq[F]`
/// says nothing of `F[T = A]`, so the derivation gives `Holder` none: the program loads and runs
/// where its derived member was refused, and two holders compared are refused.
#[test]
fn an_applied_higher_kinded_field_derives_no_equality() {
    let src = "\
namespace test.cbrd2eq.hk
  import anthill.prelude.{Int64, List}
  sort Holder[F[T] = List, A]
    entity holder(xs: F[T = A])
  end
  operation n(h: Holder[A = Int64]) -> Int64 = 5
  operation go() -> Int64 = n(holder(xs: [1, 2, 3]))
end
";
    let mut interp = crate::common::interp_for(src);
    let got = interp.call("test.cbrd2eq.hk.go", &[]).expect("runs");
    assert_eq!(crate::common::scalar_int(interp.kb(), &got), Some(5));
    let compared = src.replace(
        "end\n",
        "  operation cmp() -> Bool = holder(xs: [1]) = holder(xs: [1])\nend\n",
    );
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&compared.replace("{Int64, List}", "{Int64, List, Bool}")),
        &["Holder", "provides no `anthill.prelude.PartialEq`"],
        "two holders compared: `Holder` derives no `PartialEq`",
    );
}
