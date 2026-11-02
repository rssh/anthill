//! WI-20260827-4XXSD — a host function is run on VALUES, never on a call that did not
//! run or on a parameter's name.
//!
//! WHERE THE DEFECT LIVED ON 2026-11-02. The ticket's own rows are written in a rule
//! body, and there proposal 068's evaluation (WI-20260926-K4JGC) evaluates a call's
//! arguments first and does not run a call whose argument is stuck; WI-20260827-W1YKH made
//! `term_field` read every carrier. So those rows answer their truth on the tree as found
//! ([`the_rule_body_rows_answer_their_value`]). The defect was alive one level down, in
//! `reduce_op_value`'s call-by-name FOLD of an operation body a rule calls: the fold hands
//! the calls of the body to the host functions inside it unevaluated, and the body's
//! parameters it does not substitute at all when they are spelled bare (`n` is an
//! `Expr::VarRef`, which the fold never binds; only `?n` is a variable). A host function
//! declaring a `Term` parameter reads either as data. Measured on the tree as found, every
//! argument ground, every answer DEFINITE, where the interpreter running the same
//! operation answers the truth:
//!
//!   viaAdd1() = term_to_string(as_term(Int64.add(1, 2)))     "add(1, 2)"      truth "3"
//!   viaG7()   = term_to_string(as_term(g(7)))                 "add(x, 1)"      truth "8"
//!   viaFst(1, 2), body term_to_string(as_term(a))             "a"              truth "1"
//!   viaInt(1),    body term_as_int(as_term(n))                none             truth some(1)
//!   not(viaInt(1) = some(1))                                  1 — NAF proves a falsehood
//!   app(S.twice), body term_to_string(as_term(f(3)))          "f(3)"           truth "6"
//!
//! THE REPAIR, two gates (`kb/resolve.rs`):
//!   g1 — `collect_param_var_bindings` reports a body that names a parameter where the
//!        fold cannot bind it — a reference, or the callee of an application — and
//!        `reduce_op_value` does not fold it: the depth-0 bridge runs the operation whole,
//!        as it runs a COMPLEX body.
//!   g2 — `bridge_op_to_eval` refuses an argument of the fold's that still holds a written
//!        call anywhere in it (`value_holds_call`), beside its ground check, which a call
//!        over ground arguments passes; at depth 0, where the evaluator hands evaluated
//!        arguments, a debug build asserts it. The needs-dictionary arm's own top-level
//!        check is gone into it.
//!
//! BACK-OUT LEDGER, measured in one build with a temporary switch per gate; each test
//! compares its whole table in one assertion, and its doc gives each row's back-out answer:
//!   g1 backed out — FAIL: `a_folded_body_hands_on_the_argument_not_the_parameter_name`,
//!     `naf_over_a_folded_host_call_is_sound`, `the_rule_answers_what_the_interpreter_
//!     answers`.
//!   g2 backed out — FAIL: `a_host_call_in_a_folded_body_reads_the_value_not_the_call`,
//!     `the_rule_answers_what_the_interpreter_answers`, `a_form_and_an_unimplemented_call_
//!     are_no_values` (its `if` row; measured at HEAD, where neither gate stands).
//!   both backed out — FAIL as well: `either_gate_alone_closes_a_call_over_a_parameter`.
//!     Each gate closes its rows alone, by design: g1 stops the fold of a body naming its
//!     parameter, and g2 refuses the call that fold leaves.
//!   PASS EITHER WAY, by design — the controls: `the_rule_body_rows_answer_their_value`
//!     (the ticket's f1/f2/f4 and the `some(…)`-wrapped rows of its 2026-08-27 note, closed
//!     by K4JGC and W1YKH), `wi880_guards_hold`, `a_call_the_bridge_decides_still_answers`
//!     (the note's `pick(g())`, which the first attempt's gate turned into a suspension),
//!     and the `Set` row of `a_form_and_an_unimplemented_call_are_no_values`.
//!
//! TWO ROWS ARE BLIND, recorded so they are not read as witnesses: `term_as_int(
//! term_field(as_term(some(7)), "value"))` answers `none()` before the 068 evaluation and
//! after — before from reading the un-run call, after because `term_field`'s value is the
//! `Option` wrapper, which is no `Int64` term — and its `= some(7)` is 0 both ways.
//!
//! WI-20261013-DEY66 retires the fold. With it go g1 and every argument g2 refuses today:
//! the evaluator never hands the bridge a call.

use anthill_core::eval::Value;

// Answers of `qn(?r)`, each rendered and marked whether it is definite.
use crate::common::shown_rows as rows;

const FOLD: &str = r#"
namespace t4x.fold
  import anthill.prelude.{Int64, String, Bool, Option, List}
  import anthill.prelude.Option.{some, none}
  import anthill.reflect.{Term, term_to_string, as_term, term_as_int, term_functor_name, make_fn}

  sort S
    operation twice(n: Int64) -> Int64 = Int64.mul(n, 2)
  end

  operation g(x: Int64) -> Int64 = Int64.add(x, 1)

  -- A call left standing in a folded body (g2).
  operation viaAdd1() -> String = term_to_string(as_term(Int64.add(1, 2)))
  operation viaG7() -> String = term_to_string(as_term(g(7)))
  operation viaMk2() -> String =
    term_to_string(make_fn("anthill.prelude.Int64.add", [as_term(1), as_term(2)]))

  -- A parameter named where the fold cannot bind it (g1).
  operation viaFst(a: Int64, b: Int64) -> String = term_to_string(as_term(a))
  operation viaTerm(n: Int64) -> String = term_to_string(as_term(n))
  operation viaName(n: Int64) -> Option[T = String] = term_functor_name(as_term(n))
  operation viaInt(n: Int64) -> Option[T = Int64] = term_as_int(as_term(n))
  operation app(f: (n: Int64) -> Int64) -> String = term_to_string(as_term(f(3)))
  operation viaApp() -> String = app(lambda (n: Int64) -> Int64.mul(n, 2))

  -- A call over a parameter: either gate closes it.
  operation viaAddP(n: Int64) -> String = term_to_string(as_term(Int64.add(n, 2)))
  operation viaG(n: Int64) -> String = term_to_string(as_term(g(n)))
  operation viaAdd(n: Int64) -> String = term_to_string(as_term(Int64.add(n, 0)))
  operation viaIntAdd(n: Int64) -> Option[T = Int64] = term_as_int(as_term(Int64.add(n, 1)))

  -- Controls: a scalar host function, a `let` the fold never enters.
  operation viaLen(n: Int64) -> Int64 = String.length(Int64.to_string(Int64.add(n, 10)))
  operation viaLet(n: Int64) -> String =
    let m = n
    term_to_string(as_term(m))

  rule add1(?r) :- ?r <=> viaAdd1()
  rule g7(?r) :- ?r <=> viaG7()
  rule mk2(?r) :- ?r <=> viaMk2()
  rule fst(?r) :- ?r <=> viaFst(1, 2)
  rule term(?r) :- ?r <=> viaTerm(1)
  rule name(?r) :- ?r <=> viaName(1)
  rule int(?r) :- ?r <=> viaInt(1)
  rule int_holds(1) :- viaInt(1) = some(1)
  rule int_refuted(1) :- not(viaInt(1) = some(1))
  rule ho(?r) :- ?r <=> app(S.twice)
  rule ho_app(?r) :- ?r <=> viaApp()
  rule addp(?r) :- ?r <=> viaAddP(1)
  rule gp(?r) :- ?r <=> viaG(1)
  rule add(?r) :- ?r <=> viaAdd(1)
  rule intadd(?r) :- ?r <=> viaIntAdd(1)
  rule intadd_holds(1) :- viaIntAdd(1) = some(2)
  rule intadd_refuted(1) :- not(viaIntAdd(1) = some(2))
  rule len(?r) :- ?r <=> viaLen(1)
  rule letm(?r) :- ?r <=> viaLet(1)
end
"#;

/// Each relation's answers, rendered and marked definite — the whole table compared in one
/// assertion, so a back-out shows every row's answer and not only the first that moved.
fn table(rels: &[&str]) -> Vec<(String, Vec<(String, bool)>)> {
    let mut kb = crate::common::load_kb_with(FOLD);
    rels.iter()
        .map(|rel| (rel.to_string(), rows(&mut kb, &format!("t4x.fold.{rel}"))))
        .collect()
}

fn expected(rows: &[(&str, &[(&str, bool)])]) -> Vec<(String, Vec<(String, bool)>)> {
    rows.iter()
        .map(|(rel, answers)| {
            let answers = answers.iter().map(|(v, d)| (v.to_string(), *d)).collect();
            (rel.to_string(), answers)
        })
        .collect()
}

/// g2: a call the fold leaves standing reaches no host function.
///
/// g2 backed out: add1 "add(1, 2)" (`as_term` ran on the un-run builtin call), g7 "g(7)"
/// (with g1 out too, g's folded body with its parameter unsubstituted, "add(x, 1)"), mk2
/// the `make_fn(…)` call printed. Each definite.
#[test]
fn a_host_call_in_a_folded_body_reads_the_value_not_the_call() {
    assert_eq!(
        table(&["add1", "g7", "mk2"]),
        expected(&[
            ("add1", &[("\"3\"", true)]),
            ("g7", &[("\"8\"", true)]),
            ("mk2", &[("\"add(1, 2)\"", true)]),
        ]),
    );
}

/// g1: a body naming a parameter where the fold cannot bind it is run, not folded.
///
/// g1 backed out: fst "a" and term "n" — the parameter's name (term is the ticket's
/// 2026-10-26 note); name some("var_ref"), the reflected reference to `n` (the term `1` has
/// no functor); ho and ho_app "f(3)", the call through the function-typed parameter.
#[test]
fn a_folded_body_hands_on_the_argument_not_the_parameter_name() {
    assert_eq!(
        table(&["fst", "term", "name", "ho", "ho_app"]),
        expected(&[
            ("fst", &[("\"1\"", true)]),
            ("term", &[("\"1\"", true)]),
            ("name", &[("none", true)]),
            ("ho", &[("\"6\"", true)]),
            ("ho_app", &[("\"6\"", true)]),
        ]),
    );
}

/// The unsound row. g1 backed out: int none (`term_as_int` read the reference to `n`),
/// int_holds no row, and int_refuted 1 DEFINITE — the negation of a true equation proved.
#[test]
fn naf_over_a_folded_host_call_is_sound() {
    assert_eq!(
        table(&["int", "int_holds", "int_refuted"]),
        expected(&[
            ("int", &[("some(value: 1)", true)]),
            ("int_holds", &[("1", true)]),
            ("int_refuted", &[]),
        ]),
    );
}

/// A call over a parameter: g1 stops the fold of the body naming the parameter, g2 refuses
/// the call that fold leaves; either alone closes it, so these fail only with both out.
///
/// Both backed out: addp "add(n, 2)", gp "add(x, 1)", add "add(n, 0)", intadd none,
/// intadd_holds no row, intadd_refuted 1 DEFINITE.
#[test]
fn either_gate_alone_closes_a_call_over_a_parameter() {
    assert_eq!(
        table(&["addp", "gp", "add", "intadd", "intadd_holds", "intadd_refuted"]),
        expected(&[
            ("addp", &[("\"3\"", true)]),
            ("gp", &[("\"2\"", true)]),
            ("add", &[("\"1\"", true)]),
            ("intadd", &[("some(value: 2)", true)]),
            ("intadd_holds", &[("1", true)]),
            ("intadd_refuted", &[]),
        ]),
    );
}

/// Every operation above, run by the interpreter: the rule answers what it answers. Fails
/// with either gate out.
#[test]
fn the_rule_answers_what_the_interpreter_answers() {
    let cases: [(&str, &str, Vec<Value>); 14] = [
        ("add1", "viaAdd1", vec![]),
        ("g7", "viaG7", vec![]),
        ("mk2", "viaMk2", vec![]),
        ("fst", "viaFst", vec![Value::Int(1), Value::Int(2)]),
        ("term", "viaTerm", vec![Value::Int(1)]),
        ("name", "viaName", vec![Value::Int(1)]),
        ("int", "viaInt", vec![Value::Int(1)]),
        ("ho_app", "viaApp", vec![]),
        ("addp", "viaAddP", vec![Value::Int(1)]),
        ("gp", "viaG", vec![Value::Int(1)]),
        ("add", "viaAdd", vec![Value::Int(1)]),
        ("intadd", "viaIntAdd", vec![Value::Int(1)]),
        ("len", "viaLen", vec![Value::Int(1)]),
        ("letm", "viaLet", vec![Value::Int(1)]),
    ];
    let rels: Vec<&str> = cases.iter().map(|(rel, _, _)| *rel).collect();
    let from_rules = table(&rels);
    let mut interp = crate::common::interp_for(FOLD);
    let from_interp: Vec<(String, Vec<(String, bool)>)> = cases
        .iter()
        .map(|(rel, op, args)| {
            let v = interp
                .call(&format!("t4x.fold.{op}"), args)
                .unwrap_or_else(|e| panic!("the interpreter runs `{op}`: {e}"));
            (rel.to_string(), vec![(crate::common::show_value(interp.kb(), &v), true)])
        })
        .collect();
    assert_eq!(from_rules, from_interp, "the rule and the interpreter disagree");
}

/// The ticket's own rows, written in a rule body: the evaluation closed them before this
/// change, and they pass either way.
#[test]
fn the_rule_body_rows_answer_their_value() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace t4x.rule
  import anthill.prelude.{Int64, String, Bool, Option, List}
  import anthill.prelude.Option.{some}
  import anthill.reflect.{Term, term_field, term_functor_name, term_to_string, as_term, term_as_int}

  sort Box
    entity box(v: Int64)
  end

  rule f1(?t) :- term_field(as_term(some(7)), "value") <=> ?t
  rule f2(?n) :- term_functor_name(term_field(as_term(some(7)), "value")) <=> ?n
  rule f4(?s) :- term_to_string(term_field(as_term(some(7)), "value")) <=> ?s
  rule w1(?s) :- term_to_string(as_term(some(term_field(as_term(some(7)), "value")))) <=> ?s
  rule w2(?s) :- term_to_string(as_term(some(Int64.add(1, 2)))) <=> ?s
  rule w3(?s) :- term_to_string(as_term([Int64.add(1, 2)])) <=> ?s
  rule w5(?s) :- term_functor_name(as_term(Int64.add(1, 2))) <=> ?s
  rule w6(?s) :- term_as_int(as_term(Int64.add(1, 2))) <=> ?s
  rule u1(?s) :- term_to_string(as_term(box(7).v)) <=> ?s
end
"#,
    );
    let mut row = |rel: &str| -> String {
        match rows(&mut kb, &format!("t4x.rule.{rel}")).as_slice() {
            [(v, true)] => v.clone(),
            other => panic!("`{rel}` must answer one definite row, got {other:?}"),
        }
    };
    // `term_field` answers an `Option[T = Term]`; f2 and f4 read that value. On
    // 2026-08-27 they read the un-run call: some("term_field") and its printed text.
    assert_eq!(row("f1"), "some(value: 7)");
    assert_eq!(row("f2"), "some(value: \"some\")");
    assert_eq!(row("f4"), "\"some(value: 7)\"");
    // The 2026-08-27 note's rows, a call one constructor deep; they printed the call then.
    assert_eq!(row("w1"), "\"some(value: some(value: 7))\"");
    assert_eq!(row("w2"), "\"some(value: 3)\"");
    assert_eq!(row("w3"), "\"[3]\"");
    // The note's builtin leg: some("add"), none, and the desugared `field_access(…)` then.
    assert_eq!(row("w5"), "none", "the term `3` has no functor");
    assert_eq!(row("w6"), "some(value: 3)");
    assert_eq!(row("u1"), "\"7\"");
}

/// WI-880's guards, unmoved.
#[test]
fn wi880_guards_hold() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace t4x.wi880
  import anthill.prelude.{Int64, Option}
  import anthill.prelude.Option.{some, none}
  import anthill.reflect.{term_as_int, as_term}

  rule holds(1) :- term_as_int(as_term(7)) = some(7)
  rule wrong(1) :- term_as_int(as_term(7)) = none()
end
"#,
    );
    assert_eq!(crate::common::definite_unary(&mut kb, "t4x.wi880.holds").len(), 1);
    assert!(rows(&mut kb, "t4x.wi880.wrong").is_empty());
}

/// A call whose argument is itself a call still answers: the evaluator runs `g()` first
/// and the bridge decides `pick`. The ticket's first attempt refused it at the bridge,
/// where its arguments were not yet evaluated, and turned 42 into a suspension.
#[test]
fn a_call_the_bridge_decides_still_answers() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace t4x.pick
  import anthill.prelude.{Int64, Bool}

  operation pick(x: Int64) -> Int64 = if Int64.gt(1, 0) then 42 else x
  operation g() -> Int64 = 7
  rule p(?r) :- pick(g()) <=> ?r
end
"#,
    );
    assert_eq!(rows(&mut kb, "t4x.pick.p"), vec![("42".to_string(), true)]);
}

/// A form and a call with no implementation are no values either.
///
/// `viaIf`'s argument is an `if` form. The fold handed it to `as_term` as it stood: g2
/// backed out (measured at HEAD), iff answered "if gt(1, 0) then 1 else 2", definite. The
/// ticket's 2026-08-27 note recorded, unverified, that such an argument reaches
/// `occurrence_to_term`'s assertion; it does not — the printer reads the form.
///
/// `Set.insert` / `Set.empty` have no implementation — the shape the note asked a control
/// to be built from. Written in a rule the call is UNREDUCED, no host function reads it,
/// and no definite answer comes back, either way. (Written in an operation body it is
/// refused at load, so the fold never meets it.)
#[test]
fn a_form_and_an_unimplemented_call_are_no_values() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace t4x.form
  import anthill.prelude.{Int64, String, Bool, Set}
  import anthill.reflect.{Term, term_to_string, as_term}

  operation viaIf() -> String = term_to_string(as_term(if Int64.gt(1, 0) then 1 else 2))
  rule iff(?r) :- ?r <=> viaIf()
  rule set_rule(?r) :- ?r <=> term_to_string(as_term(Set.insert(Set.empty(), 1)))
end
"#,
    );
    assert_eq!(rows(&mut kb, "t4x.form.iff"), vec![("\"1\"".to_string(), true)]);
    let set_rule = rows(&mut kb, "t4x.form.set_rule");
    assert!(
        !set_rule.is_empty() && set_rule.iter().all(|(_, definite)| !definite),
        "an unimplemented call is undecided, never a definite answer: {set_rule:?}"
    );
}
