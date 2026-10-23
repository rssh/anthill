//! WI-20261015-C9802 and WI-20261023-2F9HY — WHERE A LAMBDA NEEDS ITS PARENTHESES
//! (kernel-language.md §4.8). After an infix operator it needs none: `?f <=> lambda () -> e`
//! is the lambda `?f <=> (lambda () -> e)` is, and its body is the rest of the chain. Where
//! a term is expected otherwise — before an infix operator, as the operand of `not`, a dot
//! receiver, a `match` scrutinee, an `if` condition, a set element — it is written in
//! parentheses, and without them it is refused at its `lambda`, naming them: there
//! `lambda` is not the keyword (§2.5), and `lambda () -> e` read as the call `lambda()`
//! under the arrow-type operator.
//!
//! Before C9802 every bare spelling here read so: `?f <=> lambda () -> plus1(1)` answered
//! `?f = arrow(lambda, 2)`, the body evaluated where it stood. C9802 refused them all; 2F9HY
//! made the operand after an operator a lambda, in both parsers (tree-sitter's
//! `infix_term`, scaland's `infixOperand`; the shared parity case
//! `lambda_as_infix_operand`).
//!
//! A `lambda` the program declares is that declaration where `lambda` is not the keyword.

use crate::common::{load_kb_with, query_unary, shown_rows, unrendered_load_errors_of};
use anthill_core::kb::load::LoadError;

const HEADER: &str = "namespace test.c9802
  operation plus1(n: Int64) -> Int64 = n + 1
  operation applyThunk(f: () -> Int64) -> Int64 = f()
  operation applyOne(f: (Int64) -> Int64) -> Int64 = f(1)
";

fn with(clauses: &str) -> String {
    format!("{HEADER}  {clauses}\nend\n")
}

/// A rule body written bare after an operator, its parenthesized twin, and the answer both
/// give (`None`: the twin's answer, whatever it is). Every bare body is refused on
/// 01424c91, where an operand after an operator took no lambda; the twins load there.
const ONE_CLAUSE: [(&str, &str, Option<&str>); 6] = [
    (
        "?f <=> lambda () -> plus1(1), applyThunk(?f, ?r)",
        "?f <=> (lambda () -> plus1(1)), applyThunk(?f, ?r)",
        Some("2"),
    ),
    (
        "?f <=> lambda (x) -> plus1(x), applyOne(?f, ?r)",
        "?f <=> (lambda (x) -> plus1(x)), applyOne(?f, ?r)",
        Some("2"),
    ),
    (
        "?f <=> lambda (x: Int64) -> plus1(x), applyOne(?f, ?r)",
        "?f <=> (lambda (x: Int64) -> plus1(x)), applyOne(?f, ?r)",
        Some("2"),
    ),
    // The body is the rest of the chain, and the `,` ends it.
    (
        "?f <=> lambda x -> x + 10, applyOne(?f, ?r)",
        "?f <=> (lambda x -> x + 10), applyOne(?f, ?r)",
        Some("11"),
    ),
    // `=` tests: both spellings leave the same residual.
    (
        "?f = lambda () -> plus1(1), applyThunk(?f, ?r)",
        "?f = (lambda () -> plus1(1)), applyThunk(?f, ?r)",
        None,
    ),
    (
        "?f <=> lambda () -> 1, ?r <=> 2",
        "?f <=> (lambda () -> 1), ?r <=> 2",
        Some("2"),
    ),
];

#[test]
fn a_lambda_after_an_infix_operator_is_the_lambda_its_parentheses_write() {
    for (bare, paren, answer) in ONE_CLAUSE {
        let mut kb = load_kb_with(&with(&format!(
            "rule bare(?r) :- {bare}\n  rule paren(?r) :- {paren}"
        )));
        // An unbound answer is a fresh variable, numbered per query: compared as one.
        let shape = |rows: Vec<(String, bool)>| -> Vec<(String, bool)> {
            rows.into_iter()
                .map(|(v, d)| {
                    (
                        if v.starts_with("Var(") {
                            "?".to_owned()
                        } else {
                            v
                        },
                        d,
                    )
                })
                .collect()
        };
        let bare_rows = shape(shown_rows(&mut kb, "test.c9802.bare"));
        let paren_rows = shape(shown_rows(&mut kb, "test.c9802.paren"));
        assert_eq!(
            bare_rows, paren_rows,
            "{bare}: one clause with its parenthesized twin"
        );
        if let Some(answer) = answer {
            assert!(
                matches!(bare_rows.as_slice(), [(v, true)] if v.as_str() == answer),
                "{bare}: one definite answer, {answer}: {bare_rows:?}"
            );
        }
    }
}

/// The lambda runs where it is handed on: through a relation's column, as an `@[simp]`
/// equation's right side, and as an operation's body after a `requires` clause, where `=`
/// still opens the body. The first two are refused on 01424c91, the third passes there.
#[test]
fn a_lambda_after_an_operator_runs_where_it_is_handed() {
    let mut kb = load_kb_with(&with(
        "rule giveOnly(?f) :- ?f <=> lambda () -> plus1(1)\n  \
         rule viaColumn(?r) :- giveOnly(?f), applyThunk(?f, ?r)\n  \
         operation thunkOf(x: Int64) -> () -> Int64\n  \
         rule thunkOf(?x) <=> lambda () -> ?x @[simp]\n  \
         rule viaSimp(?r) :- ?r <=> applyThunk(thunkOf(5))\n  \
         operation contract(x: Int64) -> (Int64) -> Int64 requires x > 0 = lambda y -> y + x\n  \
         rule viaContract(?r) :- ?r <=> applyOne(contract(5))",
    ));
    for (relation, answer) in [
        ("test.c9802.viaColumn", "2"),
        ("test.c9802.viaSimp", "5"),
        ("test.c9802.viaContract", "6"),
    ] {
        let rows = shown_rows(&mut kb, relation);
        assert!(
            matches!(rows.as_slice(), [(v, true)] if v.as_str() == answer),
            "{relation}: one definite answer, {answer}: {rows:?}"
        );
    }
}

/// Each clause, beside [`HEADER`], is refused once at its `lambda`, the parentheses named
/// first. Every row fails with the check switched off — measured 2026-10-23 on the check's
/// parent, 49a4902c, where these positions parse as they do now: the two set elements
/// loaded, the left operand and the operand of `not` named the goal `arrow` as nothing, the
/// scrutinee and the condition advised the `lambda` keyword.
const REFUSED: [&str; 6] = [
    "rule setElement(?s) :- ?s <=> {lambda () -> plus1(1)}",
    "rule openSetElement(?s, ?y) :- ?s <=> {lambda () -> ?y}",
    "rule leftSide(?r) :- lambda () -> plus1(1) <=> ?f, applyThunk(?f, ?r)",
    "rule notOperand() :- not lambda () -> true",
    "operation scrutinee() -> Int64 = match lambda () -> 1 case _ -> 2",
    "operation condition() -> Int64 = if lambda () -> true then 1 else 2",
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

/// CONTROL: after an operator the lambda is a value, typed as one — `1 + lambda () -> 2`
/// adds a function to a number, and is refused for that, not as a lambda without
/// parentheses. On 01424c91 it was refused as one.
#[test]
fn a_lambda_operand_is_typed_as_a_function() {
    for clause in [
        "rule thunkSum(?r) :- ?r <=> 1 + lambda () -> 2",
        "operation infixOperand() -> Int64 = 1 + lambda () -> 2",
    ] {
        let errors = unrendered_load_errors_of(&with(clause));
        assert!(
            !errors.is_empty()
                && errors
                    .iter()
                    .all(|e| !matches!(e.peel(), LoadError::LambdaInTermPosition { .. }))
                && errors[0]
                    .to_string()
                    .contains("type mismatch in add.b (op-arg): expected Int64, got ")
                && errors[0].to_string().contains(" -> Int64"),
            "{clause}: a type mismatch on `+`: {errors:?}"
        );
    }
}

/// CONTROL: where `lambda` is not the keyword, a `lambda` the program declares is a name
/// (§2.5), and is called — the check reads only a `lambda` that resolves to nothing. Fails
/// with that test dropped (measured 2026-10-23 with a temporary switch); passes before.
#[test]
fn a_declared_lambda_is_called() {
    let mut kb = load_kb_with(&with(
        "operation lambda(x: Int64) -> Int64 = x + 40\n  \
         rule arrowOf(?s) :- ?s <=> {lambda(1) -> Int64}",
    ));
    let rows = query_unary(&mut kb, "test.c9802.arrowOf");
    let rendered: Vec<_> = rows.iter().map(|(v, d)| (format!("{v:?}"), *d)).collect();
    assert!(
        matches!(rendered.as_slice(), [(v, true)] if v.contains("Int(41)")),
        "the declared `lambda` called, its value in the set's arrow: {rendered:?}"
    );
}

/// CONTROL: a `lambda` that is a name of something — a field read through its receiver, a
/// binder, a declaration two imports reach — is not refused as a lambda without parentheses.
/// Passes before; each failed on a draft of C9802, whose walk did not skip a field name or
/// scope a binder and counted an ambiguous `lambda` as undeclared (measured 2026-10-23).
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
         rule amb(?s) :- ?s <=> {lambda(1) -> Int64}\nend\n",
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
