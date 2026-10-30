//! WI-20261023-Y6QW2 — A FUNCTION A RULE OR A QUERY HANDS AN OPERATION IS APPLIED.
//!
//! AN OPERATION'S NAME passed as data is applied as the operation (kernel-language §5.3).
//! `apply1(inc, 4, ?r)` handed `apply1` the name on the occurrence carrier — and a fact or a
//! column carried it on the term carrier to `?p(…)` — and the apply site fell through to
//! operation resolution: "unknown operation: apply1.f", the goal undecided. The name becomes
//! its `OpRef` where it is applied (`Interpreter::op_ref_of_applied_name`), with the
//! dictionary the typer attached at it (`contains`, which requires `Eq`).
//!
//! A COMPOUND EXPRESSION IN A QUERY PATTERN is read as a clause reads it
//! (`load::query_compound_expression`): the query converter built the parser's positional
//! marker, `lambda_expr(pattern_tuple, "x")`, which is no function value, and bound `?y` to
//! `if_expr(…)` where a rule body evaluates the `if`. The query's variables are the form's
//! (`?s` in `lambda () -> ?s`), and an effectful lambda is declined at run time as a rule
//! body's goal is (WI-20261013-R1W5A). The query scan holds a bare `->` to the clause's
//! refusals (`load::query_arrow_errors`).
//!
//! A query that writes the form a fact holds (`p(lambda x -> 1)` over `fact p(lambda x ->
//! 1)`) now matches nothing, as the rule-body goal of the same text already did; it matched
//! through the shared marker. Which of the two readings is right is WI-20260829-8VGRW's open
//! question; the row here asserts that the query and the rule body give one answer.
//!
//! ## Back-out
//!
//! Each piece made a no-op under a switch of its own, one build, this file run under each
//! (measured 2026-10-30):
//!
//! | backed out | fails |
//! |---|---|
//! | an operation's name made its `OpRef` where it is applied (`applied_operation_name`) | `an_operation_name_passed_through_a_column_is_applied`, `an_operation_name_handed_to_an_operation_is_applied`, `an_operation_name_in_a_function_slot_is_applied`, `a_requiring_operation_passed_by_name_is_applied`, `the_dictionary_at_the_name_decides_what_no_argument_value_can` |
//! | the sort's dictionary at the name | `the_dictionary_at_the_name_decides_what_no_argument_value_can` (`boxSum`) |
//! | the operation's own slots at the name | `the_dictionary_at_the_name_decides_what_no_argument_value_can` (`viaSum`) |
//! | a query's compound expression lowered by the clause's walk (`query_compound_expression`) | `a_lambda_written_in_a_query_is_applied`, `a_query_variable_inside_a_lambda_is_the_patterns`, `a_compound_expression_in_a_query_is_evaluated`, `an_effectful_lambda_in_a_query_is_declined`, `a_query_and_a_rule_body_read_a_compound_form_alike` |
//! | the query's variables lent to that walk | `a_query_variable_inside_a_lambda_is_the_patterns` |
//! | the bare-arrow refusals at the query scan (`query_arrow_errors`) | `a_bare_arrow_in_a_query_is_refused_as_in_a_clause` |
//! | a description in the lent walk asserted nowhere (`Loader::lent_to_query`) | `a_description_in_a_query_lambda_is_asserted_nowhere` |
//!
//! NOT DRIVEN, and said rather than claimed: what the typer attached at the name is read in a
//! frame that binds nothing; read in the callee's frame instead, no row fails. The typer
//! refuses a rule's operation reference whose dictionary would forward a slot of an
//! enclosing frame (a rule in a `requires` sort passing its sibling is refused, "have the
//! enclosing sort `requires` it"), so what reaches the apply reads no frame.
//!
//! CONTROLS, green under every back-out: `a_lambda_written_in_a_rule_body_is_applied`,
//! `a_name_the_callee_returns_stays_the_name`.

use crate::common::{load_kb_with, query_pattern_term, query_unary};
use anthill_core::eval::Value;
use anthill_core::kb::load;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term_view::{TermView, ViewHead};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

const PROGRAM: &str = r#"
namespace test.y6
  import anthill.prelude.{List, Int64, Bool, Function, String}
  import anthill.prelude.List.{contains}

  operation applyThunk[Rho](f: () -> String @ {Rho}) -> String effects {Rho} = f()
  operation applyAt[Rho](f: (n: Int64) -> String @ {Rho}, n: Int64) -> String effects {Rho} = f(n)
  operation pureAt(n: Int64) -> String = "p"
  operation apply1(f: (n: Int64) -> Int64, n: Int64) -> Int64 = f(n)
  operation inc(n: Int64) -> Int64 = n + 1
  operation use_pair(f: Function[A = (List[T = Int64], Int64), B = Bool], x: Int64, xs: List[T = Int64]) -> Bool =
    f((xs, x))

  rule apply3(?p, ?a, ?b, ?r) :- ?p(?a, ?b, ?r)
  rule viaOpRef(?r) :- apply3(applyAt, pureAt, 1, ?r)
  rule direct(?r) :- apply1(inc, 4, ?r)
  fact handler(inc)
  rule viaFact(?r) :- handler(?f), apply1(?f, 4, ?r)
  rule viaBound(?r) :- ?f <=> inc, apply1(?f, 10, ?r)
  rule member2(?r) :- use_pair(contains, 2, [1, 2, 3], ?r)
  rule member9(?r) :- use_pair(contains, 9, [1, 2, 3], ?r)
  rule handsBack(?r) :- ?r <=> inc
  rule viaLambda(?r) :- apply1(lambda (x: Int64) -> x * 2, 4, ?r)

  fact p(lambda x -> 1)
  rule written(?n) :- p(lambda x -> 1), ?n <=> 1
end
"#;

/// The one answer of `test.y6.<name>(?r)`, which must be definite.
fn the_answer(kb: &mut KnowledgeBase, name: &str) -> Value {
    let rows = query_unary(kb, &format!("test.y6.{name}"));
    match rows.as_slice() {
        [(v, true)] => v.clone(),
        other => panic!("{name}: one definite answer, got {other:?}"),
    }
}

/// The answers of a query pattern, how many are definite, and the search's messages.
fn run_query(kb: &mut KnowledgeBase, pattern: &str) -> (usize, usize, Vec<String>) {
    let goal = query_pattern_term(kb, pattern);
    let (solutions, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    let definite = solutions.iter().filter(|s| s.residual.is_empty()).count();
    let messages = stats.errors.iter().map(|e| e.message.clone()).collect();
    (solutions.len(), if stats.truncated { 0 } else { definite }, messages)
}

/// A query pattern answers once, definitely.
fn assert_holds(kb: &mut KnowledgeBase, pattern: &str) {
    let (all, definite, messages) = run_query(kb, pattern);
    assert!(
        all == 1 && definite == 1,
        "{pattern}: one definite answer, got {all} ({definite} definite): {messages:?}"
    );
}

/// The query scan's verdict on `pattern`, rendered — the CLI's `fact <pattern>` source.
fn scan_errors(kb: &mut KnowledgeBase, pattern: &str) -> Vec<String> {
    let parsed = parse::parse(&format!("fact {pattern}")).expect("the pattern parses");
    let errors = load::scan_query_definitions(kb, &[&parsed]);
    load::LoadError::render_all(&errors).collect()
}

/// THE ACCEPTANCE, the operation-reference half: `?p(?a, ?b, ?r)` over `applyAt` and the name
/// `pureAt` answers "p", definitely.
#[test]
fn an_operation_name_passed_through_a_column_is_applied() {
    let mut kb = load_kb_with(PROGRAM);
    assert!(matches!(the_answer(&mut kb, "viaOpRef"), Value::Str(s) if s == "p"));
}

/// The name written in the call, held by a fact, and bound by `<=>`: each is applied.
#[test]
fn an_operation_name_handed_to_an_operation_is_applied() {
    let mut kb = load_kb_with(PROGRAM);
    for (name, want) in [("direct", 5), ("viaFact", 5), ("viaBound", 11)] {
        assert!(
            matches!(the_answer(&mut kb, name), Value::Int(n) if n == want),
            "{name} answers {want}"
        );
    }
}

/// WI-20260904-833DK's program: the name in a `Function`-typed slot of a call written in a
/// value slot, at one parameter and at two spread from a tuple (`spread_eta_args`, by the
/// labels the typer attached at the name).
#[test]
fn an_operation_name_in_a_function_slot_is_applied() {
    let src = r#"
namespace test.y6.dk
  import anthill.prelude.{Int64, Function}
  operation inc1(n: Int64) -> Int64 = n + 1
  operation apply1(f: Function[A = Int64, B = Int64], n: Int64) -> Int64 = f(n)
  rule value(?r) :- ?r <=> apply1(inc1, 2)
  operation sum2op(a: Int64, b: Int64) -> Int64 = a + b
  operation apply2(f: Function[A = (a: Int64, b: Int64), B = Int64], p: (a: Int64, b: Int64)) -> Int64 = f(p)
  rule value2(?r) :- ?r <=> apply2(sum2op, (a: 1, b: 2))
end
"#;
    let mut kb = load_kb_with(src);
    for name in ["value", "value2"] {
        let rows = query_unary(&mut kb, &format!("test.y6.dk.{name}"));
        assert!(matches!(rows.as_slice(), [(Value::Int(3), true)]), "{name} answers 3: {rows:?}");
    }
}

/// An operation that requires `Eq`, passed by name, answers both ways.
#[test]
fn a_requiring_operation_passed_by_name_is_applied() {
    let mut kb = load_kb_with(PROGRAM);
    assert!(matches!(the_answer(&mut kb, "member2"), Value::Bool(true)));
    assert!(matches!(the_answer(&mut kb, "member9"), Value::Bool(false)));
}

/// Two providers and an empty list: no argument value says which `Zeroable` instance runs,
/// so what the typer built at the name from the expected arrow answers 3 at `Sum` and 5 at
/// `Prod` — the operation's own slot for `zeroOf`'s `requires`, the sort's dictionary for
/// `Box`'s.
#[test]
fn the_dictionary_at_the_name_decides_what_no_argument_value_can() {
    const DICT_PROGRAM: &str = r#"
namespace test.y6.dict
  import anthill.prelude.{Int64, List}

  sort Zeroable
    sort T = ?
    operation zero() -> Int64
  end
  sort Sum
    entity sum
    provides Zeroable[T = Sum]
    operation zero() -> Int64 = 3
  end
  sort Prod
    entity prod
    provides Zeroable[T = Prod]
    operation zero() -> Int64 = 5
  end

  operation zeroOf[X](xs: List[T = X]) -> Int64 requires Zeroable[T = X] = Zeroable.zero[T = X]()
  operation applyS(f: (xs: List[T = Sum]) -> Int64, xs: List[T = Sum]) -> Int64 = f(xs)
  operation applyP(f: (xs: List[T = Prod]) -> Int64, xs: List[T = Prod]) -> Int64 = f(xs)
  rule viaSum(?r) :- applyS(zeroOf, [], ?r)
  rule viaProd(?r) :- applyP(zeroOf, [], ?r)

  sort Box
    import anthill.prelude.{Int64, List}
    sort E = ?
    requires Zeroable[T = E]
    operation zeroIn(xs: List[T = E]) -> Int64 = Zeroable.zero[T = E]()
  end
  import test.y6.dict.Box.{zeroIn}
  rule boxSum(?r) :- applyS(zeroIn, [], ?r)
  rule boxProd(?r) :- applyP(zeroIn, [], ?r)
end
"#;
    let mut kb = load_kb_with(DICT_PROGRAM);
    for (name, want) in [("viaSum", 3), ("viaProd", 5), ("boxSum", 3), ("boxProd", 5)] {
        let rows = query_unary(&mut kb, &format!("test.y6.dict.{name}"));
        assert!(
            matches!(rows.as_slice(), [(Value::Int(n), true)] if *n == want),
            "{name} answers {want}: {rows:?}"
        );
    }
}

/// CONTROL: a lambda written in a rule body was applied before this ticket.
#[test]
fn a_lambda_written_in_a_rule_body_is_applied() {
    let mut kb = load_kb_with(PROGRAM);
    assert!(matches!(the_answer(&mut kb, "viaLambda"), Value::Int(8)));
}

/// CONTROL: a name nothing applies is converted nowhere — the rule binds the name.
#[test]
fn a_name_the_callee_returns_stays_the_name() {
    let mut kb = load_kb_with(PROGRAM);
    let inc = kb.try_resolve_symbol("test.y6.inc").expect("inc resolves");
    let v = the_answer(&mut kb, "handsBack");
    assert!(
        matches!(
            TermView::head(&v, &kb),
            ViewHead::Functor { functor, pos_arity: 0, named_arity: 0 } if functor == inc
        ),
        "the name: {v:?}"
    );
}

/// THE ACCEPTANCE, the query half: a lambda written in a query pattern is a function value.
#[test]
fn a_lambda_written_in_a_query_is_applied() {
    let mut kb = load_kb_with(PROGRAM);
    assert_holds(&mut kb, r#"test.y6.applyThunk(lambda () -> "x", "x")"#);
    assert_holds(&mut kb, r#"test.y6.applyAt(lambda (n) -> test.y6.pureAt(n), 3, "p")"#);
    let (all, _, _) = run_query(&mut kb, r#"test.y6.applyThunk(lambda () -> "x", "y")"#);
    assert_eq!(all, 0, "the lambda's value is \"x\", not \"y\"");
}

/// A variable the lambda names is the query's.
#[test]
fn a_query_variable_inside_a_lambda_is_the_patterns() {
    let mut kb = load_kb_with(PROGRAM);
    assert_holds(&mut kb, r#"?s <=> "z" & test.y6.applyThunk(lambda () -> ?s, "z")"#);
}

/// An `if`, a `let` and a `match` written in a query are evaluated, as in a rule body.
#[test]
fn a_compound_expression_in_a_query_is_evaluated() {
    let mut kb = load_kb_with(PROGRAM);
    for pattern in [
        "10 <=> (if 1 = 1 then 10 else 20)",
        "6 <=> (let a = 5  a + 1)",
        "100 <=> (match 1 case 1 -> 100 case _ -> 200)",
    ] {
        assert_holds(&mut kb, pattern);
    }
}

/// An effectful lambda in a query is declined at run time, as a rule body's goal is: the
/// answer is undecided and the decline names the effect.
#[test]
fn an_effectful_lambda_in_a_query_is_declined() {
    let mut kb = load_kb_with(PROGRAM);
    let (all, definite, messages) =
        run_query(&mut kb, "test.y6.applyThunk(lambda () -> anthill.prelude.Time.now(), ?r)");
    assert!(all == 1 && definite == 0, "one undecided answer: {all}, {definite} definite");
    assert!(
        messages.iter().any(|m| m
            .contains("it performs `anthill.prelude.Time.Clock`, and a rule body performs no effect")),
        "the decline is reported: {messages:?}"
    );
}

/// A query declares nothing: an inline description inside a lambda it writes asserts no
/// `DescriptionInfo`, which the clause's walk would emit for a clause.
#[test]
fn a_description_in_a_query_lambda_is_asserted_nowhere() {
    let mut kb = load_kb_with(PROGRAM);
    let described = r#"anthill.reflect.DescriptionInfo(content: "the y6 text")"#;
    assert_holds(&mut kb, r#"?s <=> "z" & test.y6.applyThunk(lambda () -> ?s {< the y6 text >}?, "z")"#);
    let (after, _, _) = run_query(&mut kb, described);
    assert_eq!(after, 0, "the query asserted a description");
}

/// A keyword-less `->` in a query is refused as in a clause, at the top and inside a lambda.
#[test]
fn a_bare_arrow_in_a_query_is_refused_as_in_a_clause() {
    let mut kb = load_kb_with(PROGRAM);
    for (pattern, binder) in [
        ("?f <=> (x) -> test.y6.pureAt(x)", "x"),
        ("?f <=> (lambda (x) -> (y) -> test.y6.pureAt(y))", "y"),
    ] {
        let errors = scan_errors(&mut kb, pattern);
        let want = format!("in a query: `->` builds an arrow-type term, but `{binder}` does not resolve");
        assert!(errors.iter().any(|e| e.contains(&want)), "{pattern}: {errors:?}");
    }
    assert!(scan_errors(&mut kb, "?f <=> (lambda (x) -> test.y6.pureAt(x))").is_empty());
}

/// A query writing the compound form a fact holds answers what the rule-body goal of the same
/// text answers — nothing (WI-20260829-8VGRW) — and a variable finds the fact.
#[test]
fn a_query_and_a_rule_body_read_a_compound_form_alike() {
    let mut kb = load_kb_with(PROGRAM);
    let (in_rule, _, _) = run_query(&mut kb, "test.y6.written(?n)");
    let (in_query, _, _) = run_query(&mut kb, "test.y6.p(lambda x -> 1)");
    assert_eq!((in_rule, in_query), (0, 0));
    assert_holds(&mut kb, "test.y6.p(?f)");
}
