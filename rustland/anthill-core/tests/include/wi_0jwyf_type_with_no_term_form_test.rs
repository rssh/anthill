//! WI-20261030-0JWYF — A TYPE WITH NO TERM FORM IS AN ERROR, NOT A DROPPED VALUE. Every site
//! that lowered a type (or a value in one) to a term and could not, dropped it or put a
//! placeholder in its place: a `⊥` under a `debug_assert!` (silent in release), a fresh
//! variable, a `false`, the type returned as it was. Now a reader whose question can be asked
//! of a value reads through the view, and one whose destination holds a term `expect`s it,
//! with what it read named (`value_to_term`'s doc has the argument and the measurement).
//!
//! The one place a program writes a type with no term form is a `domain(?x, T)` goal's `T`
//! in a clause — `lambda () -> 1`, an `if` — which the grammar admits because the goal's
//! operands are terms. The clause typing narrowed nothing from it and the goal held of
//! nothing, so `domain(?v, lambda () -> 1)` loaded and answered no rows, and
//! `not(domain(?v, lambda () -> 1))` held. It is refused at the `T`, wherever the goal stands.
//!
//! ## Back-out
//!
//! Each part put back as it was, under a switch of its own, one build (measured 2026-10-30):
//!
//! | put back | fails |
//! |---|---|
//! | the `domain` goal's `T` dropped (`constrain_domain_test` returns) | every `a_domain_goal_…_is_refused` row |
//! | the refusal only at a committed goal, as the narrowing is | `…_under_a_negation_…`, `…_in_a_disjunction_…`, `…_under_a_discharge_…` (a constraint's body is walked as committed goals) |
//! | a type's part with no term form lowered to `⊥` (`type_node_to_term`) | `a_type_holding_an_if_has_no_term`, `a_type_applied_to_an_if_has_no_term` (a debug-build panic) |
//!
//! The controls — [`a_domain_goal_over_a_type_answers_either_way`],
//! [`a_domain_goal_over_a_variable_loads_either_way`] and
//! [`a_type_holding_a_literal_lowers_either_way`] — pass under every one by design.

use std::rc::Rc;

use crate::common::{load_errors_of, load_kb_with, query_unary};
use anthill_core::eval::Value;
use anthill_core::kb::node_occurrence::{value_to_term, Expr, NodeOccurrence, TypeChild};
use anthill_core::kb::term::{Literal, Term};
use anthill_core::span::{SourceId, SourceSpan};

/// The errors of `src`, asserted to hold one refusal of a `domain` goal's `T`, of `form`, at
/// `line:col` — the location an embedded source's error starts with.
fn assert_domain_type_refused(src: &str, form: &str, at: &str) {
    let errors = load_errors_of(src);
    let expected = format!("expected a type, got {form}, which is no type");
    let at = format!("{at} ");
    assert!(
        errors
            .iter()
            .any(|e| e.starts_with(&at) && e.contains("domain-goal") && e.contains(&expected)),
        "`{expected}` at {at}, got {errors:#?}"
    );
}

const HEAD: &str = r#"
namespace test.jwyf.domain
  import anthill.prelude.{Int64, String}
  import anthill.kernel.{domain, or}
  fact one(1)
"#;

fn program(body: &str) -> String {
    format!("{HEAD}{body}\nend\n")
}

#[test]
fn a_domain_goal_whose_type_is_a_lambda_is_refused() {
    assert_domain_type_refused(
        &program("  rule r(?v) :- ?v <=> 1, domain(?v, lambda () -> 1)"),
        "a lambda",
        "6:38:",
    );
}

#[test]
fn a_domain_goal_whose_type_is_an_if_is_refused() {
    assert_domain_type_refused(
        &program("  rule r(?v) :- ?v <=> 1, domain(?v, if true then Int64 else String)"),
        "an `if`",
        "6:38:",
    );
}

#[test]
fn a_domain_goal_under_a_negation_whose_type_is_a_lambda_is_refused() {
    assert_domain_type_refused(
        &program("  rule r(?v) :- ?v <=> 1, not(domain(?v, lambda () -> 1))"),
        "a lambda",
        "6:42:",
    );
}

#[test]
fn a_domain_goal_in_a_disjunction_whose_type_is_a_lambda_is_refused() {
    assert_domain_type_refused(
        &program("  rule r(?v) :- ?v <=> 1, or(domain(?v, lambda () -> 1), domain(?v, Int64))"),
        "a lambda",
        "6:41:",
    );
}

#[test]
fn a_domain_goal_under_a_discharge_whose_type_is_an_if_is_refused() {
    assert_domain_type_refused(
        &program(
            "  rule r(?v) :- ?v <=> 1, (forall(?w), one(?w) -: domain(?w, if true then Int64 else String))",
        ),
        "an `if`",
        "6:62:",
    );
}

#[test]
fn a_domain_goal_in_a_constraint_whose_type_is_a_lambda_is_refused() {
    assert_domain_type_refused(
        &program("  constraint c: no ?x: one(?x) -: domain(?x, lambda () -> 1)"),
        "a lambda",
        "6:46:",
    );
}

/// CONTROL — a `domain` goal over a written type loads and holds where the value is one.
#[test]
fn a_domain_goal_over_a_type_answers_either_way() {
    let mut kb = load_kb_with(&program("  rule r(?v) :- ?v <=> 1, domain(?v, Int64)"));
    let answers = query_unary(&mut kb, "test.jwyf.domain.r");
    assert!(
        matches!(answers.as_slice(), [(Value::Int(1), true)]),
        "r(?v) answers 1, got {answers:?}"
    );
}

/// CONTROL — a `domain` goal over a variable is the run's to decide, and loads.
#[test]
fn a_domain_goal_over_a_variable_loads_either_way() {
    let errors =
        load_errors_of(&program("  rule r(?v, ?t) :- ?v <=> 1, ?t <=> Int64, domain(?v, ?t)"));
    assert!(errors.is_empty(), "loads clean, got {errors:#?}");
}

// ── the lowering itself: a type whose part has no term form has none ─────────────────────

fn span() -> SourceSpan {
    SourceSpan::new(SourceId::from_raw(0), 0, 0)
}

fn expr(e: Expr) -> Rc<NodeOccurrence> {
    NodeOccurrence::new_expr(e, span(), None)
}

/// `if true then 1 else 2`, as a clause or a body holds it.
fn an_if() -> Rc<NodeOccurrence> {
    expr(Expr::If {
        condition: expr(Expr::Const(Literal::Bool(true))),
        then_branch: expr(Expr::Const(Literal::Int(1))),
        else_branch: expr(Expr::Const(Literal::Int(2))),
    })
}

/// A value in a type that is an `if` has no term form, so the type has none: `Err`, which
/// its reader decides on. It was a `⊥` standing in that part, behind a `debug_assert!`.
#[test]
fn a_type_holding_an_if_has_no_term() {
    let mut kb = load_kb_with(&program(""));
    let denoted = kb.make_denoted_occ(an_if(), span(), None);
    assert!(
        value_to_term(&mut kb, &Value::Node(denoted)).is_err(),
        "a denoted `if` has no term form"
    );
}

/// …and so has a type applied to one: the part's `None` is the whole type's.
#[test]
fn a_type_applied_to_an_if_has_no_term() {
    let mut kb = load_kb_with(&program(""));
    let denoted = kb.make_denoted_occ(an_if(), span(), None);
    let list = kb.make_sort_ref_by_name("anthill.prelude.List");
    let t = kb.intern("T");
    let applied =
        kb.make_parameterized_occ(TypeChild::Interned(list), vec![(t, TypeChild::Node(denoted))], span(), None);
    assert!(
        value_to_term(&mut kb, &Value::Node(applied)).is_err(),
        "`List[T = denoted(if …)]` has no term form"
    );
}

/// CONTROL — a literal in a type lowers, as it always did: `denoted(3)`.
#[test]
fn a_type_holding_a_literal_lowers_either_way() {
    let mut kb = load_kb_with(&program(""));
    let denoted = kb.make_denoted_occ(expr(Expr::Const(Literal::Int(3))), span(), None);
    let t = value_to_term(&mut kb, &Value::Node(denoted)).expect("a denoted literal lowers");
    let Term::Fn { named_args, .. } = kb.get_term(t).clone() else {
        panic!("`denoted(3)` is an application, got {:?}", kb.get_term(t))
    };
    assert!(
        named_args
            .iter()
            .any(|(_, a)| matches!(kb.get_term(*a), Term::Const(Literal::Int(3)))),
        "the literal is the denoted value, got {named_args:?}"
    );
}
