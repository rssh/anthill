//! WI-20261015-C9802 — A LAMBDA WRITTEN WHERE A TERM IS EXPECTED IS REFUSED, NAMING THE
//! PARENTHESES (kernel-language.md §4.8). An infix operand, a dot receiver, a `match`
//! scrutinee, an `if` condition and a set element are `Term` positions; there `lambda` is not
//! the keyword (§2.5), so `?f <=> lambda () -> plus1(1)` read as the call `lambda()` under the
//! arrow-type operator. Before, that rule loaded and answered `?f = arrow(lambda, 2)`, the body
//! evaluated where it stood, and `?f <=> lambda () -> plus1(1), applyThunk(?f, ?r)` faulted at
//! run time and left `applyThunk(arrow(lambda, 2), ?_)`. With a binder in the parameter
//! (`lambda (x) -> …`) or in an operation body it was refused, advising the `lambda` keyword
//! the author had written.
//!
//! A `lambda` the program declares is that declaration, and stays one.

use crate::common::{load_kb_with, query_unary, shown_rows, unrendered_load_errors_of};
use anthill_core::eval::Value;
use anthill_core::kb::load::LoadError;

const HEADER: &str = "namespace test.c9802
  operation plus1(n: Int64) -> Int64 = n + 1
  operation applyThunk(f: () -> Int64) -> Int64 = f()
  operation applyOne(f: (Int64) -> Int64) -> Int64 = f(1)
";

fn with(clauses: &str) -> String {
    format!("{HEADER}  {clauses}\nend\n")
}

/// Each clause, beside [`HEADER`], is refused once at its `lambda`, the parentheses named
/// first. Every row fails with the check switched off (measured 2026-10-23): the first five
/// load, and the rest are refused for something else, as the comments say.
const REFUSED: [&str; 15] = [
    // The ticket's two rules.
    "rule bareOnly(?f) :- ?f <=> lambda () -> plus1(1)",
    "rule bare(?r) :- ?f <=> lambda () -> plus1(1), applyThunk(?f, ?r)",
    "rule setElement(?s) :- ?s <=> {lambda () -> plus1(1)}",
    "rule openBody(?f, ?y) :- ?f <=> lambda () -> ?y",
    "@[simp] rule thunkOf(?x) <=> lambda () -> ?x",
    // The goal `arrow` names nothing.
    "rule leftSide(?r) :- lambda () -> plus1(1) <=> ?f, applyThunk(?f, ?r)",
    // `lambda()` typed as a call to an unknown functor.
    "rule thunkSum(?r) :- ?r <=> 1 + lambda () -> 2",
    "rule nested(?r) :- ?r <=> applyThunk(if true then (1 + lambda () -> 2) else 3)",
    // The parameter resolves to nothing, and the advice is the keyword.
    "rule param(?r) :- ?f <=> lambda (x) -> plus1(x), applyOne(?f, ?r)",
    "rule typed(?r) :- ?f <=> lambda (x: Int64) -> plus1(x), applyOne(?f, ?r)",
    // The term `lambda` names nothing.
    "fact holdsSum(1 + lambda () -> 2)",
    // An operation body and a const value: the advice is the keyword.
    "operation infixOperand() -> Int64 = 1 + lambda () -> 2",
    "operation scrutinee() -> Int64 = match lambda () -> 1 case _ -> 2",
    "operation condition() -> Int64 = if lambda () -> true then 1 else 2",
    "const k: Int64 = 1 + lambda () -> 2",
];

#[test]
fn a_lambda_without_parentheses_in_a_term_position_is_refused_at_its_lambda() {
    for clause in REFUSED {
        let src = with(clause);
        let errors = unrendered_load_errors_of(&src);
        let spans: Vec<_> = errors
            .iter()
            .filter_map(|e| match e.peel() {
                LoadError::LambdaInTermPosition { span } => Some(*span),
                _ => None,
            })
            .collect();
        assert!(
            matches!(spans.as_slice(), [span] if src[span.start as usize..].starts_with("lambda")),
            "{clause}: refused once, at its `lambda`: {errors:?}"
        );
        assert!(
            errors[0]
                .to_string()
                .contains("is put in parentheses: `(lambda … -> …)`"),
            "{clause}: the parentheses named first: {}",
            errors[0]
        );
    }
}

/// CONTROL, passing either way by design: in parentheses the lambda is a closure, and it runs
/// — bound by `<=>` and applied, and handed out through a relation's column.
#[test]
fn the_parenthesized_lambda_runs() {
    let mut kb = load_kb_with(&with(
        "rule paren(?r) :- ?f <=> (lambda () -> plus1(1)), applyThunk(?f, ?r)\n  \
         rule parenOnly(?f) :- ?f <=> (lambda () -> plus1(1))\n  \
         rule viaColumn(?r) :- parenOnly(?f), applyThunk(?f, ?r)",
    ));
    for relation in ["test.c9802.paren", "test.c9802.viaColumn"] {
        let rows = shown_rows(&mut kb, relation);
        assert!(
            matches!(rows.as_slice(), [(v, true)] if v.as_str() == "2"),
            "{relation}: one definite answer, 2: {rows:?}"
        );
    }
}

/// CONTROL: a `lambda` the program declares is a name (§2.5), and is called — the check reads
/// only a `lambda` that resolves to nothing. Fails with that test dropped; passes before.
#[test]
fn a_declared_lambda_is_called() {
    let mut kb = load_kb_with(&with(
        "operation lambda(x: Int64) -> Int64 = x + 40\n  \
         rule arrowOf(?t) :- ?t <=> lambda(1) -> Int64",
    ));
    let rows = query_unary(&mut kb, "test.c9802.arrowOf");
    let [(Value::Entity { functor, pos, .. }, true)] = rows.as_slice() else {
        panic!("one definite answer, a value of the arrow: {rows:?}");
    };
    assert!(
        kb.qualified_name_of(*functor) == "arrow" && matches!(&pos[..], [Value::Int(41), _]),
        "the declared `lambda` called, its value in the arrow: {} {pos:?}",
        kb.qualified_name_of(*functor)
    );
}

/// CONTROL: a `lambda` that is a name of something — a field read through its receiver, a
/// binder, a declaration two imports reach — is not refused as a lambda without parentheses.
/// Passes before; each failed on a draft of this change, whose walk did not skip a field
/// name or scope a binder and counted an ambiguous `lambda` as undeclared (measured
/// 2026-10-23).
#[test]
fn a_lambda_that_is_a_name_is_not_refused() {
    let mut kb = load_kb_with(&with(
        "sort Holder\n    entity holder(lambda: Int64)\n  end\n  \
         fact holder(3)\n  \
         rule fieldArrow(?t) :- holder(?h), ?t <=> ?h.lambda -> Int64\n  \
         rule binderNamed(?t) :- ?t <=> applyOne(lambda lambda -> 1) -> Int64",
    ));
    for relation in ["test.c9802.fieldArrow", "test.c9802.binderNamed"] {
        let rows = query_unary(&mut kb, relation);
        assert!(
            matches!(rows.as_slice(), [(_, true)]),
            "{relation}: one definite answer: {rows:?}"
        );
    }
    let errors = unrendered_load_errors_of(
        "namespace test.c9802.a1\n  operation lambda(x: Int64) -> Int64 = x\nend\n\
         namespace test.c9802.a2\n  operation lambda(x: Int64) -> Int64 = x\nend\n\
         namespace test.c9802.a3\n  import test.c9802.a1.*\n  import test.c9802.a2.*\n  \
         rule amb(?t) :- ?t <=> lambda(1) -> Int64\nend\n",
    );
    assert!(
        !errors.is_empty()
            && errors
                .iter()
                .all(|e| matches!(e.peel(), LoadError::AmbiguousSymbol { .. })),
        "an ambiguous `lambda` is reported as ambiguous, and only so: {errors:?}"
    );
}

/// CONTROL, passing either way by design: a keyword-less lambda keeps its own refusal and its
/// advice, in an operation body and in a rule body.
#[test]
fn a_keyword_less_lambda_keeps_its_refusal() {
    let errors = unrendered_load_errors_of(&with("operation op() -> Int64 = applyOne((x) -> x)"));
    assert!(
        matches!(
            errors.first().map(LoadError::peel),
            Some(LoadError::ArrowTermInExprPosition { .. })
        ),
        "{errors:?}"
    );
    let errors = unrendered_load_errors_of(&with("rule ra(?r) :- applyOne((x) -> plus1(x), ?r)"));
    assert!(
        matches!(
            errors.first().map(LoadError::peel),
            Some(LoadError::BareArrowInLogicPosition { .. })
        ),
        "{errors:?}"
    );
}
