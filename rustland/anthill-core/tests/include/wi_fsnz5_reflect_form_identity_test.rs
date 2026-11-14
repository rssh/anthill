//! WI-20260904-FSNZ5 — A REFLECT FORM IS KEYED BY ITS DECLARATION, NOT BY ITS NAME'S LAST
//! SEGMENT.
//!
//! `materialize_from_handle` reads nineteen reflect forms as something other than a generic
//! application: the literal leaves, `var_ref`, the control-flow and proof forms, `apply` /
//! `constructor` / `dot_apply` / `apply_within` / `requirement_at_sort`, and the three
//! collection literals. It decided which functor is a form by the last segment of the
//! functor's qualified name, so every operation or entity of the same short name, in any
//! scope, was read as the form. `node_occurrence::ReflectForm::of` now compares the
//! qualified name with the form's address.
//!
//! MEASURED BEFORE / AFTER (`anthill query` on the fixtures below):
//!
//! ```text
//!   row                                                   before                after
//!   Box.apply(box(0), 1) = 1        / = 2                 load error (arity 0)  1 / 0
//!   Box.constructor(box(0), 1) = 1  / = 2                 load error            1 / 0
//!   ?r <=> constructor(lambda () -> "x"), bare/qualified  ?r = constructor      "x"
//!   ?r <=> apply(lambda () -> "y")                        load error (arity 0)  "y"
//!   ?x <=> int_lit(value: 3)   (int_lit adds 1)           3                     4
//!   int_lit(value: 3) = 4      / = 3                      0 / 1                 1 / 0
//!   entity TupleLiteral / ListLiteral / if_expr as data   load error            as twin
//!   if_expr(…) with only `Expr` imported                  loads, matches none   refused
//! ```
//!
//! BACKED OUT, measured — `ReflectForm::of` comparing the last segments again
//! (`qn.rsplit('.').next() == form.address().rsplit('.').next()`): every test in this file
//! fails except `every_reflect_form_names_its_declaration` and
//! `a_bounded_quantifier_walks_only_a_lists_cells`. The first passes either way BY DESIGN:
//! it is the rot guard for the address table, so a renamed or moved declaration fails there
//! by name instead of silently disabling an arm. The second is the bounded quantifier's own
//! reading of list cells, and fails alone when that walk reads `cons` / `nil` by their local
//! names again.

use anthill_core::eval::value::Value;
use anthill_core::kb::node_occurrence::{
    is_reflect_form_functor, value_as_occurrence, Expr, ReflectForm,
};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

/// DEFINITE solutions of a ground goal.
fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

/// An expected answer: `Value` has no `PartialEq`.
#[derive(Debug)]
enum Want {
    Str(&'static str),
    Int(i64),
}

/// `qn(?r)` has one definite answer, and it is `want`.
fn assert_answer(kb: &mut KnowledgeBase, qn: &str, want: Want) {
    let sols = crate::common::query_unary(kb, qn);
    assert_eq!(sols.len(), 1, "{qn}: one solution expected, got {sols:?}");
    let (v, definite) = sols.into_iter().next().unwrap();
    assert!(definite, "{qn}: the solution must be definite, got {v:?}");
    let ok = match (&v, &want) {
        (Value::Str(got), Want::Str(w)) => got == w,
        (Value::Int(got), Want::Int(w)) => got == w,
        _ => false,
    };
    assert!(ok, "{qn}: answered {v:?}, expected {want:?}");
}

/// Every form's address names the declaration the standard load makes, and that
/// declaration is the form: a rename in `reflect.anthill` or `desugar_target` without the
/// table fails here naming the form.
#[test]
fn every_reflect_form_names_its_declaration() {
    let kb = crate::common::load_stdlib_kb();
    for form in ReflectForm::ALL {
        let sym = kb
            .try_resolve_symbol(form.address())
            .unwrap_or_else(|| panic!("{form:?}: `{}` names nothing", form.address()));
        assert_eq!(ReflectForm::of(&kb, sym), Some(form), "{form:?}");
    }
}

/// The ticket's measurement, driven: the two stdlib operations named `apply` are not the
/// reflect `apply` form, which is.
#[test]
fn an_operation_named_like_a_form_is_not_the_form() {
    let kb = crate::common::load_stdlib_kb();
    for (qn, want) in [
        ("anthill.reflect.Expr.apply", true),
        ("anthill.reflect.Substitution.apply", false),
        ("anthill.prelude.Function.apply", false),
    ] {
        let sym = kb
            .try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("`{qn}` must resolve"));
        assert_eq!(is_reflect_form_functor(&kb, sym), want, "{qn}");
    }
}

const BOX: &str = r#"
namespace fsnz5.bx
  import anthill.prelude.{Int64}
  sort Box
    entity box(v: Int64)
    operation apply(b: Box, n: Int64) -> Int64 = n
    operation constructor(b: Box, n: Int64) -> Int64 = n
  end
  operation int_lit(value: Int64) -> Int64 = value + 1
  operation var_ref(name: Int64) -> Int64 = name + 2
  rule ap(1)     :- Box.apply(box(0), 1) = 1
  rule ap_no(1)  :- Box.apply(box(0), 1) = 2
  rule ct(1)     :- Box.constructor(box(0), 1) = 1
  rule ct_no(1)  :- Box.constructor(box(0), 1) = 2
  rule lit(1)    :- int_lit(value: 3) = 4
  rule lit_no(1) :- int_lit(value: 3) = 3
  rule vr(1)     :- var_ref(name: 3) = 5
  rule vr_no(1)  :- var_ref(name: 3) = 3
end
"#;

/// A user operation named like a form is CALLED in a rule body, in both polarities. Before,
/// `apply` / `constructor` did not load (the call was read as the form and found none of
/// its fields), and `int_lit(value: 3)` was read as the literal `3`.
#[test]
fn a_user_operation_named_like_a_form_is_called_in_a_rule_body() {
    let mut kb = crate::common::load_kb_with(BOX);
    for (row, want) in [
        ("ap", 1),
        ("ap_no", 0),
        ("ct", 1),
        ("ct_no", 0),
        ("lit", 1),
        ("lit_no", 0),
        ("vr", 1),
        ("vr_no", 0),
    ] {
        assert_eq!(
            answers(&mut kb, &format!("fsnz5.bx.{row}(1)")),
            want,
            "{row}"
        );
    }
}

/// `<=>` evaluates every operation application in its operands, so it is handed the call:
/// bare and qualified, `constructor` answers what its lambda returns, as its renamed twin
/// does. Before, both answered `?r = constructor`.
#[test]
fn a_call_named_like_a_form_is_evaluated_by_unify() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace fsnz5.rf
  import anthill.prelude.{String, Int64}
  operation constructor(f: () -> String) -> String = f()
  operation construct(f: () -> String) -> String = f()
  operation apply(f: () -> String) -> String = f()
  operation int_lit(value: Int64) -> Int64 = value + 1
  rule k1(?r) :- ?r <=> constructor(lambda () -> "x")
  rule k2(?r) :- ?r <=> fsnz5.rf.constructor(lambda () -> "x")
  rule twin(?r) :- ?r <=> construct(lambda () -> "x")
  rule m1(?r) :- ?r <=> apply(lambda () -> "y")
  rule n1(?r) :- ?r <=> int_lit(value: 3)
end
"#,
    );
    for (qn, want) in [
        ("fsnz5.rf.twin", Want::Str("x")),
        ("fsnz5.rf.k1", Want::Str("x")),
        ("fsnz5.rf.k2", Want::Str("x")),
        ("fsnz5.rf.m1", Want::Str("y")),
        ("fsnz5.rf.n1", Want::Int(4)),
    ] {
        assert_answer(&mut kb, qn, want);
    }
}

/// A user ENTITY named like a form is data, as its renamed twin is: it loads, a fact holding
/// it is found by a rule body that writes it. Before, the module did not load ("expected
/// surface expression, got bottom").
#[test]
fn a_user_entity_named_like_a_form_is_data() {
    // The second program is the renamed twin, in a namespace of its own name.
    for suffix in ["", "X"] {
        let src = r#"
namespace fsnz5.en@
  import anthill.prelude.{Int64}
  sort TupleLiteral@
    entity TupleLiteral@(a: Int64)
  end
  sort Lw
    entity ListLiteral@(x: Int64)
  end
  sort Ie
    entity if_expr@(cond: Int64)
  end
  fact holds_t(TupleLiteral@(a: 1))
  fact holds_l(ListLiteral@(x: 2))
  fact holds_i(if_expr@(cond: 3))
  rule t(?v) :- holds_t(TupleLiteral@(a: ?v))
  rule l(?v) :- holds_l(ListLiteral@(x: ?v))
  rule i(?v) :- holds_i(if_expr@(cond: ?v))
end
"#
        .replace('@', suffix);
        let mut kb = crate::common::load_kb_with(&src);
        for (rule, want) in [("t", 1), ("l", 2), ("i", 3)] {
            assert_answer(
                &mut kb,
                &format!("fsnz5.en{suffix}.{rule}"),
                Want::Int(want),
            );
        }
    }
}

/// `value_as_occurrence` asks the same question for an `Entity` and for a `Term`, so both
/// carriers of a user `int_lit(value: 7)` are the application and both carriers of the
/// reflect form are the literal. Before, the user's read as the literal `7` from both.
#[test]
fn both_carriers_read_a_user_functor_named_like_a_form_as_an_application() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace fsnz5.vo
  import anthill.prelude.{Int64}
  entity int_lit(value: Int64)
end
"#,
    );
    let value_f = kb.intern("value");
    for (qn, is_form) in [
        ("fsnz5.vo.int_lit", false),
        ("anthill.reflect.Expr.int_lit", true),
    ] {
        let functor = kb
            .try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("`{qn}` must resolve"));
        let seven = kb.alloc(Term::Const(Literal::Int(7)));
        let mut named: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> = SmallVec::new();
        named.push((value_f, seven));
        let term = kb.alloc(Term::Fn {
            functor,
            pos_args: SmallVec::new(),
            named_args: named,
        });
        let entity = Value::Entity {
            functor,
            pos: std::rc::Rc::from(Vec::new().as_slice()),
            named: std::rc::Rc::from(vec![(value_f, Value::Int(7))].as_slice()),
        };
        for (carrier, v) in [("term", Value::term(term)), ("entity", entity)] {
            let occ = value_as_occurrence(&mut kb, &v);
            let read = occ.as_expr();
            if is_form {
                assert!(
                    matches!(read, Some(Expr::Const(Literal::Int(7)))),
                    "{qn} ({carrier}): the reflect form is its literal, got {read:?}"
                );
            } else {
                assert!(
                    matches!(read, Some(Expr::Apply { functor: f, .. }) if *f == functor),
                    "{qn} ({carrier}): a user functor is its application, got {read:?}"
                );
            }
        }
    }
}

/// A form's name with only the enum imported names nothing, and is refused as any unknown
/// name in a rule-body term is — `if_expr` as `int_lit` already was. Before, `if_expr(…)`
/// was read as the form by its last segment, escaped the refusal (which reads applications)
/// and loaded a rule that matched nothing.
#[test]
fn a_form_name_not_imported_is_refused_as_any_unknown_name() {
    for (name, pattern) in [
        (
            "if_expr",
            "if_expr(cond: ?c, then_branch: ?t, else_branch: ?el)",
        ),
        ("int_lit", "int_lit(value: ?)"),
    ] {
        let src = format!(
            r#"
namespace fsnz5.un
  import anthill.reflect.{{NodeOccurrence, Expr, occurrence_term}}
  rule probe(?e) :- occurrence_term(?e, {pattern})
end
"#
        );
        let errs = crate::common::load_errors_of(&src);
        assert!(
            errs.len() == 1 && errs[0].contains(&format!("rule-body term `{name}` names nothing")),
            "{name}: {errs:#?}"
        );
    }
}

/// THE SAME READING OF LIST CELLS: a bounded quantifier walks a collection by the qualified
/// name of each cell's constructor, so a `cons` / `nil` another sort declares is no list and
/// the quantifier waits on it, as on its renamed twin; a `List` is walked. Before, the
/// quantifier read any `cons` / `nil` by its local name and `mine_some` answered. Found on
/// the way: the walk is the one that read `ListLiteral` by its local name too.
#[test]
fn a_bounded_quantifier_walks_only_a_lists_cells() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace fsnz5.bq
  import anthill.prelude.{Int64, List}
  sort MyL
    entity nil
    entity cons(head: Int64, tail: MyL)
  end
  fact mine(cons(head: 1, tail: cons(head: 2, tail: nil)))
  fact theirs([1, 2])
  rule mine_some(1)   :- mine(?l), (some ?x in ?l: ?x = 2)
  rule theirs_some(1) :- theirs(?l), (some ?x in ?l: ?x = 2)
  rule theirs_none(1) :- theirs(?l), (some ?x in ?l: ?x = 3)
end
"#,
    );
    for (row, want) in [("mine_some", 0), ("theirs_some", 1), ("theirs_none", 0)] {
        assert_eq!(
            answers(&mut kb, &format!("fsnz5.bq.{row}(1)")),
            want,
            "{row}"
        );
    }
}
