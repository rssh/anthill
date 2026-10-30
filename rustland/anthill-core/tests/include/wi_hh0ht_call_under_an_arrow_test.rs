//! WI-20261023-HH0HT — A CALL WRITTEN IN AN ARROW TERM IN A RULE BODY IS A CALL IN A VALUE
//! SLOT (user, 2026-10-30): typed, and refused, as the clause's other calls are, and its value
//! is what the arrow holds. An arrow in a rule body is a type written as a term, and what it
//! holds is data, as a tuple's components are (kernel-language §5.3): a sort name there is a
//! type value, and the arrow itself is no call. Before, the clause typing skipped the arrow's
//! interior while the evaluator ran the calls in it: `?t <=> Int64 -> plus1("a")` loaded and
//! faulted at run time, leaving `arrow(Int64, plus1("a"))`, and `?t <=> Int64 -> stamp()`
//! loaded and was declined at run time, where `?t <=> plus1("a")` and `?t <=> stamp()` are
//! refused at load.
//!
//! Under `=` an arrow is a value of `Type`, as a sort name is: `(Int64 -> Int64) = (Int64 ->
//! Int64)` was refused at load, "type mismatch in arrow.apply: … unknown functor".
//!
//! ## Back-out
//!
//! Each piece made a no-op in place under a switch of its own, one build (measured 2026-10-30;
//! each clause of the refusal row loaded on the parent, 987a525d):
//!
//! | backed out | fails |
//! |---|---|
//! | the walk: an arrow's components are no data (`child_body_positions`) | `a_call_in_an_arrow_is_typed_as_a_call`, `a_dot_in_an_arrow_is_dispatched`, `an_arrow_under_an_equality_is_a_type_value` (the effect then named by `PartialEq.eq`, not by the call in the arrow) |
//! | the clause typing: an arrow's components are not walked (`type_written_as_term`) | `a_variable_a_call_in_an_arrow_reads_is_typed_by_it` |
//! | the typer: an arrow under `=` is a value of `Type` (`check_apply_iter`) | `an_arrow_under_an_equality_is_a_type_value` |
//!
//! CONTROLS, green under every back-out: `a_pure_call_in_an_arrow_answers_its_value` (the
//! evaluator ran the call before), `an_arrow_of_types_is_unchanged`,
//! `an_arrow_in_a_lambda_body_keeps_the_operation_body_reading`.

use crate::common::{assert_refused_naming, load_errors_of, load_kb_with, shown_rows};

const PROGRAM: &str = r#"
namespace test.hh0ht
  import anthill.prelude.{Int64, String, Bool}
  import anthill.prelude.Time.{now, Clock}

  operation plus1(n: Int64) -> Int64 = n + 1
  operation stamp() -> String effects {Clock} = now()
  entity box(v: Int64)
  sort Holder
    entity holder(h: Int64)
  end
"#;

fn with(clauses: &str) -> String {
    format!("{PROGRAM}\n  {clauses}\nend\n")
}

/// The load's errors without their `line:col:` prefix: a twin's call stands at another column.
fn unlocated_errors(src: &str) -> Vec<String> {
    load_errors_of(src)
        .into_iter()
        .map(|e| match e.split_once(": ") {
            Some((at, rest)) if at.chars().all(|c| c.is_ascii_digit() || c == ':') => {
                rest.to_string()
            }
            _ => e,
        })
        .collect()
}

/// CONTROL, passing either way by design: the evaluator ran a call in an arrow before. Its
/// value is what the arrow holds, at every place in it.
#[test]
fn a_pure_call_in_an_arrow_answers_its_value() {
    let mut kb = load_kb_with(&with(
        "rule result(?t) :- ?t <=> Int64 -> plus1(1)\n  \
         rule param(?t) :- ?t <=> (plus1(1)) -> Int64\n  \
         rule inBox(?t) :- ?t <=> Int64 -> box(v: plus1(1))",
    ));
    for (relation, value) in [
        ("test.hh0ht.result", "arrow(Int64, 2)"),
        ("test.hh0ht.param", "arrow(2, Int64)"),
        ("test.hh0ht.inBox", "arrow(Int64, box(v: 2))"),
    ] {
        assert_eq!(
            shown_rows(&mut kb, relation),
            vec![(value.to_string(), true)],
            "{relation}"
        );
    }
}

/// Each clause is refused at load, as its twin outside the arrow is — the message is the
/// twin's. Each loaded before and faulted, or was declined, at run time.
#[test]
fn a_call_in_an_arrow_is_typed_as_a_call() {
    for (clause, twin, tokens) in [
        (
            "rule illTyped(?t) :- ?t <=> Int64 -> plus1(\"a\")",
            "rule illTyped(?t) :- ?t <=> plus1(\"a\")",
            &["plus1.n (op-arg): expected Int64, got String"][..],
        ),
        (
            "rule effectful(?t) :- ?t <=> Int64 -> stamp()",
            "rule effectful(?t) :- ?t <=> stamp()",
            &["the call `test.hh0ht.stamp`", "Clock"][..],
        ),
        (
            "rule inData(?t) :- ?t <=> Int64 -> box(v: plus1(\"a\"))",
            "rule inData(?t) :- ?t <=> box(v: plus1(\"a\"))",
            &["plus1.n (op-arg): expected Int64, got String"][..],
        ),
        (
            "rule inParam(?t) :- ?t <=> (plus1(\"a\")) -> Int64",
            "rule inParam(?t) :- ?t <=> (plus1(\"a\"), Int64)",
            &["plus1.n (op-arg): expected Int64, got String"][..],
        ),
        (
            "rule inRow(?t) :- ?t <=> (Int64) -> Int64 @ {stamp()}",
            "rule inRow(?t) :- ?t <=> {stamp()}",
            &["the call `test.hh0ht.stamp`", "Clock"][..],
        ),
        (
            "rule inBranch(?t) :- (?t <=> Int64 -> plus1(\"a\")) | ?t <=> 1",
            "rule inBranch(?t) :- (?t <=> plus1(\"a\")) | ?t <=> 1",
            &["plus1.n (op-arg): expected Int64, got String"][..],
        ),
    ] {
        let errors = unlocated_errors(&with(clause));
        assert_refused_naming(&errors, tokens, clause);
        assert_eq!(errors.len(), 1, "{clause}: refused once: {errors:?}");
        assert_eq!(
            errors,
            unlocated_errors(&with(twin)),
            "{clause}: refused as its twin `{twin}` is"
        );
    }
}

/// A variable a call in an arrow reads is typed by the call's parameter, as the twin's is, so
/// a caller handing it a `String` is refused at the column. It loaded before.
#[test]
fn a_variable_a_call_in_an_arrow_reads_is_typed_by_it() {
    for clause in [
        "rule r(?x, ?t) :- ?t <=> Int64 -> plus1(?x)\n  rule s(?t) :- r(\"a\", ?t)",
        "rule r(?x, ?t) :- ?t <=> plus1(?x)\n  rule s(?t) :- r(\"a\", ?t)",
    ] {
        assert_refused_naming(
            &load_errors_of(&with(clause)),
            &["r._1 (rule-column): expected Int64, got String"],
            clause,
        );
    }
    let mut kb = load_kb_with(&with(
        "rule r(?x, ?t) :- ?t <=> Int64 -> plus1(?x)\n  rule s(?t) :- r(4, ?t)",
    ));
    assert_eq!(
        shown_rows(&mut kb, "test.hh0ht.s"),
        vec![("arrow(Int64, 5)".to_string(), true)]
    );
}

/// A dot in an arrow is dispatched as in a value slot. Before, it was kept as data:
/// `arrow(holder(h: 3).h, Int64)`.
#[test]
fn a_dot_in_an_arrow_is_dispatched() {
    let mut kb = load_kb_with(&with(
        "rule fieldArrow(?t) :- ?b <=> holder(3), ?t <=> ?b.h -> Int64",
    ));
    assert_eq!(
        shown_rows(&mut kb, "test.hh0ht.fieldArrow"),
        vec![("arrow(3, Int64)".to_string(), true)]
    );
}

/// Under `=` an arrow is a value of `Type`, as a sort name is, compared by its parts; a call
/// in it is typed there as well. Each clause was refused before, "unknown functor" `arrow`.
#[test]
fn an_arrow_under_an_equality_is_a_type_value() {
    let mut kb = load_kb_with(&with(
        "rule same(?r) :- (Int64 -> Int64) = (Int64 -> Int64), ?r <=> 1\n  \
         rule other(?r) :- not((Int64 -> Int64) = (Int64 -> String)), ?r <=> 1\n  \
         rule bound(?t) :- ?t <=> (Int64 -> Int64), ?t = (Int64 -> Int64)\n  \
         rule evaluated(?r) :- (Int64 -> plus1(1)) = (Int64 -> 2), ?r <=> 1",
    ));
    for (relation, value) in [
        ("test.hh0ht.same", "1"),
        ("test.hh0ht.other", "1"),
        ("test.hh0ht.bound", "arrow(Int64, Int64)"),
        ("test.hh0ht.evaluated", "1"),
    ] {
        assert_eq!(
            shown_rows(&mut kb, relation),
            vec![(value.to_string(), true)],
            "{relation}"
        );
    }
    let errors = load_errors_of(&with("rule eff(?t) :- (Int64 -> stamp()) = ?t"));
    assert_refused_naming(&errors, &["the call `test.hh0ht.stamp`", "Clock"], "eff");
    assert_eq!(errors.len(), 1, "refused once: {errors:?}");
    let errors = load_errors_of(&with("rule ill(?t) :- ?t = (Int64 -> plus1(\"a\"))"));
    assert_refused_naming(
        &errors,
        &["plus1.n (op-arg): expected Int64, got String"],
        "ill",
    );
}

/// CONTROL, passing either way by design: an arrow of types, its row and its variables, loads
/// and answers as written (WI-618's rows are in `wi618_bare_arrow_logic_test`).
#[test]
fn an_arrow_of_types_is_unchanged() {
    let mut kb = load_kb_with(&with(
        "rule plain(?t) :- ?t <=> (Int64) -> Int64\n  \
         rule named(?t) :- ?t <=> (a: Int64) -> String\n  \
         rule row(?t) :- ?t <=> (Int64) -> Int64 @ {Clock}\n  \
         rule vars(?t) :- ?t <=> (?a -> ?b), ?a <=> Int64, ?b <=> Bool",
    ));
    for (relation, value) in [
        ("test.hh0ht.plain", "arrow(Int64, Int64)"),
        ("test.hh0ht.named", "arrow((a: Int64), String)"),
        ("test.hh0ht.row", "arrow_effect(Int64, Int64, {Clock})"),
        ("test.hh0ht.vars", "arrow(Int64, Bool)"),
    ] {
        assert_eq!(
            shown_rows(&mut kb, relation),
            vec![(value.to_string(), true)],
            "{relation}"
        );
    }
}

/// CONTROL, passing either way by design: what stands under a compound expression is written
/// as an operation body is, where an arrow names no value — so `lambda t -> (t -> t)` is
/// refused naming the arrow, as before (`wi_fc2x4_lambda_in_a_rule_test`).
#[test]
fn an_arrow_in_a_lambda_body_keeps_the_operation_body_reading() {
    let errors = load_errors_of(&with("rule value(?y) :- ?y <=> (lambda t -> (t -> t))"));
    assert_refused_naming(&errors, &["arrow", "unknown functor"], "lambda body");
}
