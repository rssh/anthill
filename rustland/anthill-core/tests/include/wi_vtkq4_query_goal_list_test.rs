//! WI-20261127-VTKQ4 — A PARENTHESIZED GOAL LIST IN A QUERY IS THE CONJUNCTION OF ITS GOALS
//! (kernel-language §5.3), as in a rule body, so an `=` in it is typed where the query is read
//! (§8.3).
//!
//! BEFORE (measured 2026-11-27 at 548b79fec, `anthill query`): the query walk read `(g₁, …, gₙ)`
//! as the tuple at every position, where the clause walk has read it as the conjunction since
//! d72b59670. The typer descends only a connective's goal slots, so an `=` in a branch's list was
//! reached by no type: `(1 = 1, 1 > 0) | (0 = 1, 1 <= 0)` answered nothing, INCOMPLETE, with "no
//! type reached the comparison" on each `eq`. And a tuple heads no clause, so a branch holding a
//! list failed with no diagnostic — `(pos(1), pos(2)) | false` answered nothing — and under `not`
//! it held. A query built as a value from a pattern takes the same converter
//! (`load::convert_patterns_untyped`), so `execute_typed_logical_query_with` met the same tuple.
//!
//! THE CONTRACT CLAUSE, the same defect at another walk: `requires (x > 0, x < 10)` was stored as
//! the tuple, so the call-site check read a precondition no call establishes or refutes —
//! `inRange(20)` loaded and ran, where `requires x > 0 & x < 10` refused it — and a clause handed
//! to a query carried the tuple. That is how anthill-traces met the defect: its contract evaluator
//! gives an `ensures (result = true, live(…)) | (result = false, !live(…))` clause, its places
//! bound, to `execute_typed_logical_query_with`, and each `eq` was left undecided.
//!
//! Every row runs the query or the call: a written query through `load::convert_query_terms` and
//! the resolver, a value one through `execute_typed_logical_query_with` and
//! `refute_typed_logical_query_with`, a contract through the call that is held to it.
//!
//! BACK-OUT (measured, each half alone):
//! * `convert_query_term_expecting` without its `query_goal_list` call: FAIL —
//!   `each_ticket_row_is_decided_as_a_written_query`, `each_ticket_row_is_decided_as_a_value_query`,
//!   `a_refuted_branch_list_is_refuted_not_undecided`,
//!   `a_goal_list_is_a_conjunction_at_every_query_goal_position`,
//!   `a_negated_goal_list_is_the_negated_conjunction`, `a_named_tuple_is_no_query_goal`.
//! * `convert_term_inner` without its `contract_goal_list` call: FAIL —
//!   `a_contract_goal_list_is_held_at_the_call`, `a_named_tuple_is_no_contract_goal`,
//!   `a_contract_clause_handed_to_a_query_is_decided`.
//!
//! PASS either way, by design — `a_parenthesized_list_in_a_query_value_position_is_a_tuple`, the
//! half of the rule the change leaves as it was, and `a_contract_written_with_and_is_held_at_the_call`,
//! the spelling the list now reads as.

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::execute::{ExecuteOptions, Refutation};
use anthill_core::kb::load::QueryPattern;
use anthill_core::kb::reflect_reader::read_operations;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::print::TermPrinter;

use crate::common::{load_errors_of, load_kb_with, query_goals, query_pattern_refusals, query_unary, run_time_goals};

const SRC: &str = "namespace vtkq4\n  rule pos(?x) :- ?x > 0\nend\n";

/// The ticket's rows, each holding at one branch: an `=` in a conjunction that is a branch of a
/// disjunction, at `Int64` and at `Bool`, beside a comparison or a rule goal, in either branch.
const TICKET_ROWS: &[&str] = &[
    "(1 = 1) | (0 = 1)",
    "(true = true) | (false = true)",
    "(1 = 1, 1 > 0) | (0 = 1, 1 <= 0)",
    "(true = true, 1 > 0) | (false = true, 1 <= 0)",
    "(1 = 1, vtkq4.pos(1)) | (0 = 1, vtkq4.pos(0))",
    "(1 = 1) | (0 = 1, 1 > 0)",
    "(1 > 0, 1 = 1) | (0 = 1)",
    "(1 > 0) | (1 = 1, 0 > 1)",
];

/// The written query `pattern` over `kb`: its definite answers, and every answer that is not
/// definite or fault the search recorded, rendered.
fn written(kb: &mut KnowledgeBase, pattern: &str) -> (usize, Vec<String>) {
    let goals = query_goals(kb, &[pattern]);
    let (sols, stats) = kb.resolve_with_stats(&goals, &ResolveConfig::default());
    let mut undecided: Vec<String> = stats.errors.iter().map(|e| e.message.clone()).collect();
    if stats.truncated || stats.out_of_fuel {
        undecided.push("the search was cut".to_string());
    }
    for sol in sols.iter().filter(|s| !s.is_definite()) {
        let r: Vec<String> = sol.residual.iter().map(|v| TermPrinter::new(kb).print_value(v)).collect();
        undecided.push(format!("residual {r:?}"));
    }
    (sols.iter().filter(|s| s.is_definite()).count(), undecided)
}

/// `pattern` built at run time and handed over as a `LogicalQuery` value.
fn value_query(kb: &mut KnowledgeBase, pattern: &str) -> Value {
    let goal: QueryPattern = run_time_goals(kb, &[pattern]).remove(0);
    pattern_query(kb, Value::Node(goal))
}

/// `goal` as the `LogicalQuery` value `pattern_query(term: goal)`.
fn pattern_query(kb: &mut KnowledgeBase, goal: Value) -> Value {
    let functor: Symbol = kb
        .try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query")
        .expect("`pattern_query` resolves");
    let term = kb.intern("term");
    Value::Entity {
        functor,
        pos: Vec::new().into(),
        named: vec![(term, goal)].into(),
    }
}

/// The value query `q` through the typed execute: its definite answers, and every answer that is
/// not definite or fault the search recorded, rendered.
fn executed(kb: &mut KnowledgeBase, q: &Value) -> (usize, Vec<String>) {
    let mut stream = kb
        .execute_typed_logical_query_with(q, &ExecuteOptions::default())
        .unwrap_or_else(|e| panic!("the query types; got {e:?}"));
    let mut definite = 0;
    let mut undecided = Vec::new();
    loop {
        match stream.next_solution(kb) {
            Ok(Some(answer)) if answer.is_definite() => definite += 1,
            Ok(Some(answer)) => {
                let r: Vec<String> = answer.residual.iter().map(|v| TermPrinter::new(kb).print_value(v)).collect();
                undecided.push(format!("residual {r:?}"));
            }
            Ok(None) => break,
            Err(e) => {
                undecided.push(format!("{e:?}"));
                break;
            }
        }
    }
    undecided.extend(stream.stats().errors.iter().map(|e| e.message.clone()));
    (definite, undecided)
}

/// The value query `q`'s verdict through the typed refutation.
fn verdict(kb: &mut KnowledgeBase, q: &Value) -> String {
    match kb.refute_typed_logical_query_with(q, &ExecuteOptions::default()) {
        Err(e) => format!("refused: {e}"),
        Ok(outcome) => match outcome.verdict {
            Refutation::Answered(_) => "answered".to_string(),
            Refutation::Refuted(_) => "refuted".to_string(),
            Refutation::Undecided(u) => format!("undecided: {u:?}"),
        },
    }
}

/// Every ticket row, written as a query, answers once, definitely, and nothing is left undecided.
#[test]
fn each_ticket_row_is_decided_as_a_written_query() {
    let mut kb = load_kb_with(SRC);
    for row in TICKET_ROWS {
        assert_eq!(written(&mut kb, row), (1, Vec::new()), "`{row}`");
    }
}

/// Every ticket row, built as a value from its pattern and handed to the typed execute, answers
/// once, definitely; the refutation of the same value answers it.
#[test]
fn each_ticket_row_is_decided_as_a_value_query() {
    let mut kb = load_kb_with(SRC);
    for row in TICKET_ROWS {
        let q = value_query(&mut kb, row);
        assert_eq!(executed(&mut kb, &q), (1, Vec::new()), "`{row}`");
        assert_eq!(verdict(&mut kb, &q), "answered", "`{row}`");
    }
}

/// A disjunction neither branch of which holds is REFUTED, as written and as a value: each `=` in
/// a list is decided, so no branch is left undecided. Before, the search ended INCOMPLETE.
#[test]
fn a_refuted_branch_list_is_refuted_not_undecided() {
    let mut kb = load_kb_with(SRC);
    for row in ["(0 = 1, 1 > 0) | (2 = 3)", "(1 = 1, 1 > 2) | (0 = 1, vtkq4.pos(1))"] {
        assert_eq!(written(&mut kb, row), (0, Vec::new()), "`{row}`");
        let q = value_query(&mut kb, row);
        assert_eq!(executed(&mut kb, &q), (0, Vec::new()), "`{row}`");
        assert_eq!(verdict(&mut kb, &q), "refuted", "`{row}`");
    }
}

/// EVERY QUERY GOAL POSITION reads the list as the conjunction — a branch, a nested list, a
/// quantifier's body — and `()` is the empty conjunction, `true`. The holding list answers once,
/// the one with a failing goal not at all.
#[test]
fn a_goal_list_is_a_conjunction_at_every_query_goal_position() {
    let mut kb = load_kb_with(SRC);
    for (row, answers) in [
        ("(vtkq4.pos(1), vtkq4.pos(2)) | false", 1),
        ("(vtkq4.pos(1), vtkq4.pos(0)) | false", 0),
        ("false | (vtkq4.pos(1), vtkq4.pos(2), vtkq4.pos(3))", 1),
        ("((vtkq4.pos(1), vtkq4.pos(2)), vtkq4.pos(3)) | false", 1),
        ("(forall ?z in [1]: (vtkq4.pos(1), vtkq4.pos(2)))", 1),
        ("(forall ?z in [1]: (vtkq4.pos(1), vtkq4.pos(0)))", 0),
        ("() | false", 1),
    ] {
        assert_eq!(written(&mut kb, row), (answers, Vec::new()), "`{row}`");
        let q = value_query(&mut kb, row);
        assert_eq!(executed(&mut kb, &q), (answers, Vec::new()), "`{row}` as a value");
    }
}

/// A NEGATED LIST IS THE NEGATED CONJUNCTION: it holds where the goals do not all hold, and fails
/// where they do. Before, the tuple's failure was read as a disproof, and every row held.
#[test]
fn a_negated_goal_list_is_the_negated_conjunction() {
    let mut kb = load_kb_with(SRC);
    for (row, answers) in [
        ("not((vtkq4.pos(1), vtkq4.pos(2)))", 0),
        ("not((vtkq4.pos(1), vtkq4.pos(0)))", 1),
        ("not(vtkq4.pos(1), vtkq4.pos(2))", 0),
    ] {
        assert_eq!(written(&mut kb, row), (answers, Vec::new()), "`{row}`");
    }
}

/// A NAMED tuple is no goal list: its labels name components. Refused where the query is read,
/// with the sentence a clause's goal gets, where before it failed in silence.
#[test]
fn a_named_tuple_is_no_query_goal() {
    let mut kb = load_kb_with(SRC);
    let refusals = query_pattern_refusals(&mut kb, "(a: vtkq4.pos(1), b: vtkq4.pos(2)) | false");
    assert!(
        refusals.iter().any(|r| r.contains("a named tuple is not a goal")),
        "the named tuple is refused; got {refusals:?}"
    );
}

/// IN A VALUE POSITION THE LIST IS A TUPLE: an operand of `<=>` holds `(1, 2)`, which `(?r, 2)`
/// takes apart. Passes either way by design: the half of the rule the change leaves as it was.
#[test]
fn a_parenthesized_list_in_a_query_value_position_is_a_tuple() {
    let mut kb = load_kb_with(SRC);
    let goals = query_goals(&mut kb, &["?t <=> (1, 2)", "?t <=> (?r, 2)", "?r = 1"]);
    let (sols, stats) = kb.resolve_with_stats(&goals, &ResolveConfig::default());
    assert!(stats.errors.is_empty(), "{:?}", stats.errors);
    assert_eq!(sols.iter().filter(|s| s.is_definite()).count(), 1);
}

/// The contract rows: a precondition written as a goal list, and negated; a postcondition whose
/// branches are goal lists, the clause anthill-traces checks.
const CONTRACTS: &str = r#"
namespace vtkq4c
  import anthill.prelude.{Int64, Bool}
  rule live(?x) :- ?x > 0
  sort Ops
    operation inRange(x: Int64) -> Int64
      requires (x > 0, x < 10)
      = x
    operation outOfRange(x: Int64) -> Int64
      requires not(x > 0, x < 10)
      = x
    operation inRangeAnd(x: Int64) -> Int64
      requires x > 0 & x < 10
      = x
    operation outOfRangeAnd(x: Int64) -> Int64
      requires not(x > 0 & x < 10)
      = x
    operation isLive(x: Int64) -> Bool
      ensures (result = true, live(x)) | (result = false, !live(x))
  end
"#;

/// `CONTRACTS` with `rule r(?y) :- ?y <=> Ops.<call>`: its load errors, or the answers of `r`.
fn call(call: &str) -> Result<Vec<i64>, Vec<String>> {
    let src = format!("{CONTRACTS}  rule r(?y) :- ?y <=> Ops.{call}\nend\n");
    let errors = load_errors_of(&src);
    if !errors.is_empty() {
        return Err(errors);
    }
    let mut kb = load_kb_with(&src);
    Ok(query_unary(&mut kb, "vtkq4c.r")
        .into_iter()
        .map(|(v, definite)| match (v, definite) {
            (Value::Int(n), true) => n,
            other => panic!("`{call}`: expected a definite Int64, got {other:?}"),
        })
        .collect())
}

/// Is `result` the call-site refusal of a precondition?
fn refused_at_the_call(result: &Result<Vec<i64>, Vec<String>>) -> bool {
    matches!(result, Err(errors) if errors.iter().any(|e| e.contains("provable at the call site")))
}

/// A PRECONDITION WRITTEN AS A GOAL LIST is held at the call as the conjunction: a call it
/// refutes is refused at load, and one it establishes runs. Before, both loaded and ran.
#[test]
fn a_contract_goal_list_is_held_at_the_call() {
    assert!(refused_at_the_call(&call("inRange(20)")), "{:?}", call("inRange(20)"));
    assert_eq!(call("inRange(5)"), Ok(vec![5]));
    assert!(refused_at_the_call(&call("outOfRange(5)")), "{:?}", call("outOfRange(5)"));
    assert_eq!(call("outOfRange(20)"), Ok(vec![20]));
}

/// The same precondition written with `&` is held the same way. Passes either way by design: it
/// is the spelling the list reads as.
#[test]
fn a_contract_written_with_and_is_held_at_the_call() {
    assert!(refused_at_the_call(&call("inRangeAnd(20)")), "{:?}", call("inRangeAnd(20)"));
    assert_eq!(call("inRangeAnd(5)"), Ok(vec![5]));
    assert!(refused_at_the_call(&call("outOfRangeAnd(5)")), "{:?}", call("outOfRangeAnd(5)"));
    assert_eq!(call("outOfRangeAnd(20)"), Ok(vec![20]));
}

/// A NAMED tuple in a contract clause is no goal list, refused as at a clause's goal.
#[test]
fn a_named_tuple_is_no_contract_goal() {
    let src = "namespace vtkq4n\n  import anthill.prelude.{Int64}\n  sort Ops\n    \
               operation f(x: Int64) -> Int64\n      requires (a: x > 0, b: x < 10)\n      = x\n  \
               end\nend\n";
    let errors = load_errors_of(src);
    assert!(
        errors.iter().any(|e| e.contains("a named tuple is not a goal")),
        "the named tuple is refused; got {errors:?}"
    );
}

/// `term` with each `var_ref(name: p)` of `places` replaced by its value — a contract clause's
/// places bound, as a contract evaluator binds them before it asks the clause.
fn bind_places(kb: &mut KnowledgeBase, term: TermId, places: &[(&str, TermId)]) -> TermId {
    match kb.get_term(term).clone() {
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } => {
            if kb.local_name_of(functor) == "var_ref" {
                if let [(_, name)] = named_args.as_slice() {
                    if let Term::Ref(p) | Term::Ident(p) = kb.get_term(*name) {
                        let p = kb.local_name_of(*p).to_string();
                        if let Some(&(_, value)) = places.iter().find(|(n, _)| *n == p) {
                            return value;
                        }
                    }
                }
            }
            let pos_args = pos_args.iter().map(|&a| bind_places(kb, a, places)).collect();
            let named_args = named_args.iter().map(|&(k, a)| (k, bind_places(kb, a, places))).collect();
            kb.alloc(Term::Fn {
                functor,
                pos_args,
                named_args,
            })
        }
        _ => term,
    }
}

/// THE ANTHILL-TRACES ROUTE: `isLive`'s `ensures` read off its `OperationInfo` record, its places
/// bound, handed to the typed execute as `pattern_query(term: …)`. Each binding is decided — the
/// clause holds at a live `x` with `result = true` and at a dead one with `result = false`, and is
/// refuted otherwise — with nothing undecided. Before, the clause held tuples and each `eq` in
/// them was reached by no type.
#[test]
fn a_contract_clause_handed_to_a_query_is_decided() {
    let mut kb = load_kb_with(&format!("{CONTRACTS}end\n"));
    let ops = kb.try_resolve_symbol("vtkq4c.Ops").expect("`Ops` resolves");
    let records = read_operations(&mut kb, ops).expect("Ops' operations read");
    let ensures = records
        .iter()
        .find(|r| TermPrinter::new(&kb).print_term(r.name).trim_matches('"').ends_with("isLive"))
        .and_then(|r| r.ensures.first().cloned())
        .expect("`isLive` has an `ensures` clause");
    let Value::Term { id: clause, .. } = ensures else {
        panic!("`isLive`'s clause is a term; got {ensures:?}");
    };
    for (x, result, holds) in [(5, true, true), (5, false, false), (0, false, true), (0, true, false)] {
        let x_term = kb.alloc(Term::Const(Literal::Int(x)));
        let result_term = kb.alloc(Term::Const(Literal::Bool(result)));
        let bound = bind_places(&mut kb, clause, &[("x", x_term), ("result", result_term)]);
        let q = pattern_query(&mut kb, Value::term(bound));
        let row = format!("x = {x}, result = {result}");
        assert_eq!(executed(&mut kb, &q), (usize::from(holds), Vec::new()), "{row}");
        assert_eq!(verdict(&mut kb, &q), if holds { "answered" } else { "refuted" }, "{row}");
    }
}
