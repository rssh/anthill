//! WI-20261023-W2JP7 — A FUNCTION HANDED TO A RELATION THROUGH ITS HEAD REACHES THE CLAUSE.
//! A head match binds on every carrier the goal is written on, and a binding rides into the
//! clause as the value it is: a closure an operation returned, a lambda written as the goal's
//! argument, either of them inside an entity. Before, `with_fresh_vars` lowered each binding
//! to a term, and one with no term form marked the match contradictory, so the clause was
//! dropped in silence: `viaPure(?r)` and `viaLambda(?r)` answered nothing and
//! `not(viaPure("x"))` held. WI-20261015-8Z5TK is the same mechanism, met by other programs
//! (a clause that never applies the function, a disjunction whose lambda-free branch was lost
//! with it); its programs are the `z5tk_` rows.
//!
//! ## Back-out
//!
//! Each part put back as it was — the binding lowered to a term, one with no term form the
//! match's contradiction — under a switch of its own, one build, `anthill-core`'s unit tests,
//! `resolve_tests` and `wi_tests` run under each (measured 2026-10-30):
//!
//! | put back | fails |
//! |---|---|
//! | the whole change, at every binding | every row here but the two controls; `wi_7ypgm_goal_walk_flatness_test::a_head_match_over_an_entity_goal_interns_nothing` (grew 2); `kb::tests::with_fresh_vars_carries_a_carrier_with_no_term_form`, `kb::tests::prove_rule_predicate_holds_over_an_operand_with_no_term_form` |
//! | at a clause's slot (the rename of a rule's De Bruijn variable) | `a_closure_an_operation_returned_reaches_the_clause`, `a_lambda_written_in_the_goal_reaches_the_clause`, `a_closure_inside_an_entity_reaches_the_clause`, `a_clause_without_a_body_matches_a_closure`, `a_closure_reaches_each_branch_of_an_or`, `a_closure_inside_a_tuple_reaches_the_clause`, `a_closure_reaches_a_clause_through_another`, the three `z5tk_` rows that are not its control; the 7YPGM row and the two unit tests above |
//! | at a fact's own variable (the rename of a head written with global variables) | `a_clause_without_a_body_matches_a_closure`, `a_nonlinear_head_hands_the_closure_back`, `a_fact_with_an_omitted_field_matches_a_closure` |
//! | at a caller's link | none. No producer puts a value with no term form in a head subterm a caller's variable binds: over the whole workspace the links off the term carrier were one occurrence and one entity, both lowered. The link walk reads every carrier because nothing before it lowers a link any more |
//! | the resolver's debug assertion that a link is a term, a variable or an entity | 13 rows of `wi_tests`, `a_nonlinear_head_hands_the_closure_back` among them: a link now carries the value the match bound |
//!
//! The controls, [`the_call_in_one_clause_answers_either_way`] and
//! [`z5tk_the_twins_answer_either_way`], pass under every one of them by design.

use crate::common::{load_kb_with, query_unary};
use anthill_core::eval::Value;

const PROGRAM: &str = r#"
namespace test.w2jp7
  import anthill.prelude.{String}

  entity Box(f: () -> String)
  entity Holder(f: () -> String, tag: String)

  operation applyThunk[Rho](f: () -> String @ {Rho}) -> String effects {Rho} = f()
  operation pureThunk() -> () -> String = lambda () -> "x"
  operation boxed() -> Box = Box(f: lambda () -> "b")

  rule cc(?f, ?r) :- applyThunk(?f, ?r)
  rule viaPure(?r) :- pureThunk(?f), cc(?f, ?r)
  rule viaLambda(?r) :- cc(lambda () -> "x", ?r)
  rule oneClause(?r) :- pureThunk(?f), applyThunk(?f, ?r)

  rule notPure(1) :- not(viaPure("x"))
  rule notPureY(1) :- not(viaPure("y"))
  rule notLambda(1) :- not(viaLambda("x"))
  rule notLambdaY(1) :- not(viaLambda("y"))

  rule unbox(Box(f: ?f), ?r) :- applyThunk(?f, ?r)
  rule viaBox(?r) :- pureThunk(?f), unbox(Box(f: ?f), ?r)
  rule viaBoxed(?r) :- boxed(?b), unbox(?b, ?r)

  fact two(?f, "second")
  rule two(?f, ?r) :- applyThunk(?f, ?r)
  rule viaTwo(?r) :- pureThunk(?f), two(?f, ?r)

  fact same(?f, ?f)
  rule viaSame(?r) :- pureThunk(?f), same(?f, ?g), applyThunk(?g, ?r)

  fact Holder(tag: "t")
  rule viaHolder(?t) :- pureThunk(?f), Holder(f: ?f, tag: ?t)

  rule viaOr(?r) :- pureThunk(?f), (cc(?f, ?r) | applyThunk(?f, ?r))
  rule unt((?f, ?n), ?r) :- applyThunk(?f, ?r)
  rule viaTuple(?r) :- pureThunk(?f), unt((?f, 1), ?r)
  rule down(0, ?f, ?r) :- applyThunk(?f, ?r)
  rule down(1, ?f, ?r) :- down(0, ?f, ?r)
  rule viaRecursion(?r) :- pureThunk(?f), down(1, ?f, ?r)
end
"#;

/// Every answer of `test.w2jp7.<name>(?r)`, each asserted definite.
fn answers(name: &str) -> Vec<Value> {
    let mut kb = load_kb_with(PROGRAM);
    query_unary(&mut kb, &format!("test.w2jp7.{name}"))
        .into_iter()
        .map(|(v, definite)| {
            assert!(definite, "`{name}` answered {v:?} undecided");
            v
        })
        .collect()
}

fn strings(name: &str) -> Vec<String> {
    let mut out: Vec<String> = answers(name)
        .into_iter()
        .map(|v| match v {
            Value::Str(s) => s,
            other => panic!("`{name}` answered {other:?}, not a string"),
        })
        .collect();
    out.sort();
    out
}

#[test]
fn a_closure_an_operation_returned_reaches_the_clause() {
    assert_eq!(strings("viaPure"), ["x"]);
    assert!(answers("notPure").is_empty(), "`not(viaPure(\"x\"))` must fail, decided");
}

#[test]
fn a_lambda_written_in_the_goal_reaches_the_clause() {
    assert_eq!(strings("viaLambda"), ["x"]);
    assert!(answers("notLambda").is_empty(), "`not(viaLambda(\"x\"))` must fail, decided");
}

/// CONTROL: the same call in one clause, no head between the function and the call; and a
/// negation over a value the function does not give, which holds whether the clause is
/// reached or dropped.
#[test]
fn the_call_in_one_clause_answers_either_way() {
    assert_eq!(strings("oneClause"), ["x"]);
    assert_eq!(answers("notPureY").len(), 1, "`not(viaPure(\"y\"))` must hold, decided");
    assert_eq!(answers("notLambdaY").len(), 1, "`not(viaLambda(\"y\"))` must hold, decided");
}

#[test]
fn a_closure_inside_an_entity_reaches_the_clause() {
    assert_eq!(strings("viaBox"), ["x"]);
    assert_eq!(strings("viaBoxed"), ["b"]);
}

/// The fact is matched by the closure as the rule is: both clauses answer.
#[test]
fn a_clause_without_a_body_matches_a_closure() {
    assert_eq!(strings("viaTwo"), ["second", "x"]);
}

/// `same(?f, ?f)` binds its slot to the closure through the first argument and hands it to
/// the caller's `?g` through the second.
#[test]
fn a_nonlinear_head_hands_the_closure_back() {
    assert_eq!(strings("viaSame"), ["x"]);
}

/// `Holder(tag: "t")` stands with a variable in its omitted field, matched by the closure.
#[test]
fn a_fact_with_an_omitted_field_matches_a_closure() {
    assert_eq!(strings("viaHolder"), ["t"]);
}

/// A `|` is the stdlib's `or` rule, so each branch reaches its goal through a head match.
#[test]
fn a_closure_reaches_each_branch_of_an_or() {
    assert_eq!(strings("viaOr"), ["x", "x"]);
}

#[test]
fn a_closure_inside_a_tuple_reaches_the_clause() {
    assert_eq!(strings("viaTuple"), ["x"]);
}

/// Two head matches in a row: `down(1, …)` hands the closure to `down(0, …)`.
#[test]
fn a_closure_reaches_a_clause_through_another() {
    assert_eq!(strings("viaRecursion"), ["x"]);
}

// ── WI-20261015-8Z5TK, the same mechanism: its programs, each answering as its one-body
// twin does; the twins are the control row.

const PROGRAM_8Z5TK: &str = r#"
namespace test.z5tk
  import anthill.prelude.{Int64}

  operation pureOp(n: Int64) -> Int64 = n + 1
  operation mkPure() -> () -> Int64 = lambda () -> pureOp(1)
  operation apply0[T](f: () -> T) -> T = f()
  rule applyIt(?f, ?r) :- apply0(?f, ?r)

  rule viaClosure(?r) :- mkPure(?f), applyIt(?f, ?r)
  rule viaLambda(?r) :- applyIt(lambda () -> pureOp(1), ?r)
  rule viaOneBody(?r) :- mkPure(?f), apply0(?f, ?r)

  rule anyF(?f, ?n) :- ?n <=> 1
  rule anyFive(?n) :- anyF(5, ?n)
  rule anyClosure(?n) :- mkPure(?f), anyF(?f, ?n)

  rule lambdaOr(?r) :- apply0(lambda () -> pureOp(1), ?r) | (?r <=> 0)
  rule plainOr(?r) :- (?r <=> 7) | (?r <=> 0)
end
"#;

/// Every answer of `test.z5tk.<name>(?r)`, each definite, as sorted integers.
fn ints(name: &str) -> Vec<i64> {
    let mut kb = load_kb_with(PROGRAM_8Z5TK);
    let mut out: Vec<i64> = query_unary(&mut kb, &format!("test.z5tk.{name}"))
        .into_iter()
        .map(|(v, definite)| match (v, definite) {
            (Value::Int(n), true) => n,
            (other, definite) => panic!("`{name}` answered {other:?} (definite: {definite})"),
        })
        .collect();
    out.sort();
    out
}

#[test]
fn z5tk_a_function_value_reaches_a_clause_through_its_head() {
    assert_eq!(ints("viaClosure"), [2]);
    assert_eq!(ints("viaLambda"), [2]);
}

/// No call is needed: the clause never applies `?f`.
#[test]
fn z5tk_a_clause_that_ignores_the_function_still_answers() {
    assert_eq!(ints("anyClosure"), [1]);
}

/// The lambda-free branch was lost with the lambda's.
#[test]
fn z5tk_a_disjunction_keeps_both_branches() {
    assert_eq!(ints("lambdaOr"), [0, 2]);
}

/// CONTROL: the one-body twin, a clause handed a number, and a disjunction with no lambda.
#[test]
fn z5tk_the_twins_answer_either_way() {
    assert_eq!(ints("viaOneBody"), [2]);
    assert_eq!(ints("anyFive"), [1]);
    assert_eq!(ints("plainOr"), [0, 7]);
}
