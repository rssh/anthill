//! A NULLARY OPERATION'S NAME IS READ IN A RULE BODY AND IN A QUERY AS IN AN OPERATION BODY
//! (kernel-language §5.4, "The two readings of a bare operation name"): its call, and where a
//! function is expected and its result is not one, the function value.
//!
//! WI-20261023-6Q43W — IN A QUERY a nullary operation's call was its NAME as data: over
//! `operation seven() -> Int64 = 7`, `?v <=> seven()` bound `?v = seven`, `seven() = 7`
//! answered nothing, and `not(plainStamp() = "x")` held over an effectful `plainStamp`. The
//! query converter applied the nullary canon to the call (`load::nullary_query_canon`), so
//! the evaluator met the bare name. Now the call is built, written with parentheses or alone,
//! as the rule-body walk builds it; with no typer to read the slot, the bare name at a
//! parameter its callee declares a function type stays the name, which the call applies.
//!
//! WI-20261013-R1W5A — IN A RULE BODY the bare name at a function-typed parameter was
//! refused, "applyThunk.f: expected () -> Int64, got Int64", where the operation body's
//! `applyThunk(seven)` answers 7: the walk builds the name as its call, and the typer read it
//! as one written with parentheses. The call node is marked written without them, so the
//! typer reads it as it reads `Box.zero` (`paren_less_member_as_function`); the clause typing
//! holds no call result there; and the reference the typer stores is applied as the
//! operation at run time (`applied_operation_name`). A relation's column is read with the
//! call, as before: the dispatch walk types a goal on a relation without its column types.
//!
//! In a quoted `Term` field the name is the term, in a rule body as in a query: the rule
//! body's `q(t: seven)` met no `fact q(t: seven)`.
//!
//! ## Back-out
//!
//! Each piece made a no-op under a switch of its own, one build, this file run under each
//! (measured 2026-10-31):
//!
//! | backed out | fails |
//! |---|---|
//! | the call written with parentheses (`nullary_query_canon`) | `a_nullary_call_in_a_query_is_its_value`, `an_effectful_nullary_call_in_a_query_is_declined`, `a_call_written_with_parentheses_is_no_function` (its query, which answered 7) |
//! | the bare name's call (`query_resolved_name`) | `a_bare_nullary_name_in_a_query_is_its_call`, `a_nullary_name_at_a_query_function_parameter_is_the_function` (`mkF`), `a_query_and_a_rule_body_read_a_named_fact_alike` |
//! | the name at a function parameter (`query_function_value_arguments`) | `a_nullary_name_at_a_query_function_parameter_is_the_function` |
//! | the walk's mark (`build_body_atom_occurrence_inner`'s tail) | `a_nullary_name_at_a_function_parameter_is_the_function`, `an_effectful_function_value_is_refused_by_its_row` |
//! | the clause typing's position (`nullary_name_as_function`) | `a_nullary_name_at_a_function_parameter_is_the_function`, `an_effectful_function_value_is_refused_by_its_row` |
//! | the reference applied (`applied_operation_name`'s `VarRef`) | `a_nullary_name_at_a_function_parameter_is_the_function` |
//! | the quoted field's name (`body_resolved_name_expr`) | `a_nullary_name_in_a_quoted_term_field_is_the_term` |
//! | a bracket binding's call read as its name (`query_type_context_binding`) | `a_nullary_name_in_a_bracket_binding_is_the_name` (measured on the tree before that arm, by the CLI) |
//!
//! CONTROLS, green under every back-out: `a_nullary_name_elsewhere_is_its_call`,
//! `a_relation_column_reads_the_call`.

use crate::common::{
    assert_refused_naming, load_errors_of, load_kb_with, query_pattern_term, query_unary,
    shown_rows, supply_invocation_imports,
};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

const PROGRAM: &str = r#"
namespace test.nq
  import anthill.prelude.{Int64, String, Bool, Unit, Function}
  import anthill.prelude.Time.{now, Clock}
  import anthill.reflect.Term

  sort Thunk = () -> Int64
  operation seven() -> Int64 = 7
  operation stampN() -> Int64 effects {Clock} = 3
  operation plainStamp() -> String effects {Clock} = now()
  operation mkF() -> () -> Int64 = lambda () -> 9
  operation applyThunk(f: () -> Int64) -> Int64 = f()
  operation applyE[Rho](f: () -> Int64 @ {Rho}) -> Int64 effects {Rho} = f()
  operation applyAny[T](x: T) -> T = x
  operation applyT(f: Thunk) -> Int64 = f()
  operation applyFn(f: Function[A = Unit, B = Int64]) -> Int64 = f(())
  operation two(a: Int64, f: () -> Int64) -> Int64 = a + f()
  entity q(t: Term)
  fact q(t: seven)
  fact isSeven(7)
  fact holdsName(seven)
  rule relHolds(?f, ?r) :- applyThunk(?f, ?r)

  rule bareValue(?r) :- ?r <=> seven
  rule atTypeParameter(?r) :- ?r <=> applyAny(seven)
  rule resultIsAFunction(?r) :- ?r <=> applyThunk(mkF)
  rule quoted(?r) :- q(t: seven), ?r <=> 1
  rule viaName(?r) :- holdsName(seven), ?r <=> 1
"#;

/// The rule-body rows of R1W5A, each beside its operation-body twin.
const CLAUSES: &str = r#"
  operation oThunk() -> Int64 = applyThunk(seven)
  operation oAlias() -> Int64 = applyT(seven)
  operation oFunction() -> Int64 = applyFn(seven)
  operation oLabel() -> Int64 = two(f: seven, a: 1)
  operation oRow() -> Int64 = applyE(seven)

  rule goalThunk(?r) :- applyThunk(seven, ?r)
  rule valueThunk(?r) :- ?r <=> applyThunk(seven)
  rule viaAlias(?r) :- ?r <=> applyT(seven)
  rule viaFunction(?r) :- ?r <=> applyFn(seven)
  rule viaLabel(?r) :- ?r <=> two(f: seven, a: 1)
  rule viaResultLabel(?r) :- two(f: seven, a: 1, result: ?r)
  rule viaRow(?r) :- ?r <=> applyE(seven)
  rule inArithmetic(?r) :- ?r <=> applyThunk(seven) + 1

"#;

fn with(clauses: &str) -> String {
    format!("{PROGRAM}\n{clauses}\nend\n")
}

/// The program, with the clauses that hand a function parameter the bare name when `fn_values`.
fn loaded(fn_values: bool) -> KnowledgeBase {
    load_kb_with(&with(if fn_values { CLAUSES } else { "" }))
}

/// `test.nq.<relation>(?r)`'s answers, rendered.
fn rows(kb: &mut KnowledgeBase, relation: &str) -> Vec<(String, bool)> {
    shown_rows(kb, &format!("test.nq.{relation}"))
}

fn one(value: &str) -> Vec<(String, bool)> {
    vec![(value.to_string(), true)]
}

/// The answers of a query pattern, how many are definite, and the search's messages.
fn run_query(kb: &mut KnowledgeBase, pattern: &str) -> (usize, usize, Vec<String>) {
    let goal = query_pattern_term(kb, pattern);
    let (solutions, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    let definite = solutions.iter().filter(|s| s.residual.is_empty()).count();
    let messages = stats.errors.iter().map(|e| e.message.clone()).collect();
    (solutions.len(), if stats.truncated { 0 } else { definite }, messages)
}

fn assert_holds(kb: &mut KnowledgeBase, pattern: &str) {
    let (all, definite, messages) = run_query(kb, pattern);
    assert!(
        all == 1 && definite == 1,
        "{pattern}: one definite answer, got {all} ({definite} definite): {messages:?}"
    );
}

fn assert_undecided(kb: &mut KnowledgeBase, pattern: &str, message: &str) {
    let (all, definite, messages) = run_query(kb, pattern);
    assert!(
        all == 1 && definite == 0,
        "{pattern}: one undecided answer, got {all} ({definite} definite)"
    );
    assert!(
        messages.iter().any(|m| m.contains(message)),
        "{pattern}: the fault `{message}` is reported: {messages:?}"
    );
}

/// The query of the ticket: the call written with parentheses is its value, wherever the
/// value is read.
#[test]
fn a_nullary_call_in_a_query_is_its_value() {
    let mut kb = loaded(false);
    for pattern in [
        "(?v <=> test.nq.seven()) & (?v = 7)",
        "test.nq.seven() = 7",
        "(?v <=> (1, test.nq.seven())) & (?v = (1, 7))",
        "test.nq.isSeven(test.nq.seven())",
        "(test.nq.isSeven(8) | test.nq.isSeven(test.nq.seven()))",
    ] {
        assert_holds(&mut kb, pattern);
    }
}

/// Written alone it is the call too, as in a rule body.
#[test]
fn a_bare_nullary_name_in_a_query_is_its_call() {
    let mut kb = loaded(false);
    supply_invocation_imports(&mut kb, &["test.nq.*"]);
    for pattern in ["(?v <=> seven) & (?v = 7)", "seven = 7", "isSeven(seven)"] {
        assert_holds(&mut kb, pattern);
    }
}

/// An effectful one is declined at run time, as a rule body's goal no typer sees is: the
/// answer is undecided and the decline names the effect. The negation held.
#[test]
fn an_effectful_nullary_call_in_a_query_is_declined() {
    let mut kb = loaded(false);
    let clock = "it performs `anthill.prelude.Time.Clock`, and a rule body performs no effect";
    assert_undecided(&mut kb, "?r <=> test.nq.plainStamp()", clock);
    assert_undecided(&mut kb, r#"not(test.nq.plainStamp() = "x")"#, clock);
}

/// At a parameter its callee declares a function type, the bare name is the function, in a
/// query as in an operation body; a nullary operation whose result is that function is its
/// call (`mkF`, which answered the closure).
#[test]
fn a_nullary_name_at_a_query_function_parameter_is_the_function() {
    let mut kb = loaded(false);
    supply_invocation_imports(&mut kb, &["test.nq.*"]);
    for pattern in [
        "applyThunk(seven, ?r) & (?r = 7)",
        "(?r <=> applyT(seven)) & (?r = 7)",
        "(?r <=> two(f: seven, a: 1)) & (?r = 8)",
        "(?r <=> applyThunk(mkF)) & (?r = 9)",
    ] {
        assert_holds(&mut kb, pattern);
    }
}

/// The rule-body rows of R1W5A: the bare name at a function-typed parameter answers what the
/// operation-body twin does, at an arrow, an alias, a `Function`, a labelled parameter, a row
/// parameter, and under arithmetic. Each clause was refused.
#[test]
fn a_nullary_name_at_a_function_parameter_is_the_function() {
    let mut kb = loaded(true);
    for (twin, value) in [
        ("oThunk", "7"),
        ("oAlias", "7"),
        ("oFunction", "7"),
        ("oLabel", "8"),
        ("oRow", "7"),
    ] {
        let answers: Vec<_> = query_unary(&mut kb, &format!("test.nq.{twin}"))
            .into_iter()
            .map(|(v, definite)| (crate::common::show_value(&kb, &v), definite))
            .collect();
        assert_eq!(answers, one(value), "the operation body's {twin}");
    }
    for (relation, value) in [
        ("goalThunk", "7"),
        ("valueThunk", "7"),
        ("viaAlias", "7"),
        ("viaFunction", "7"),
        ("viaLabel", "8"),
        ("viaResultLabel", "8"),
        ("viaRow", "7"),
        ("inArithmetic", "8"),
    ] {
        assert_eq!(rows(&mut kb, relation), one(value), "{relation}");
    }
}

/// CONTROL, passing either way by design: anywhere else the name is its call — a value, a
/// type parameter the call does not pin to a function, a parameter whose function its
/// result already is.
#[test]
fn a_nullary_name_elsewhere_is_its_call() {
    let mut kb = loaded(false);
    assert_eq!(rows(&mut kb, "bareValue"), one("7"));
    assert_eq!(rows(&mut kb, "atTypeParameter"), one("7"));
    assert_eq!(rows(&mut kb, "resultIsAFunction"), one("9"));
}

/// Handed to a function parameter whose row it fixes, an effectful one is held to that row:
/// refused for its effect, as the call would be.
#[test]
fn an_effectful_function_value_is_refused_by_its_row() {
    for clause in [
        "rule eff(?r) :- ?r <=> applyE(stampN)",
        "rule effGoal(?r) :- applyE(stampN, ?r)",
    ] {
        let errors = load_errors_of(&with(clause));
        assert_refused_naming(&errors, &["the call `test.nq.applyE`", "Clock"], clause);
        assert_eq!(errors.len(), 1, "{clause}: refused once: {errors:?}");
    }
}

/// A call written with parentheses is the call, so at a function parameter it is no function:
/// refused in a rule body as in an operation body, before and after. A query has no typer, and
/// its call faults at run time; it answered 7, the name applied.
#[test]
fn a_call_written_with_parentheses_is_no_function() {
    for src in [
        with("rule paren(?r) :- applyThunk(seven(), ?r)"),
        with("operation oParen() -> Int64 = applyThunk(seven())"),
    ] {
        assert_refused_naming(&load_errors_of(&src), &["applyThunk.f", "expected () -> Int64"], &src);
    }
    let mut kb = loaded(false);
    supply_invocation_imports(&mut kb, &["test.nq.*"]);
    assert_undecided(&mut kb, "applyThunk(seven(), ?r)", "unknown operation: test.nq.applyThunk.f");
}

/// CONTROL, refused either way by design: a relation's column is read with the call, which
/// does not fit the column's function type. The dispatch walk types a goal on a relation
/// without its columns' types, so no function value is made there.
#[test]
fn a_relation_column_reads_the_call() {
    let clause = "rule viaRelation(?r) :- relHolds(seven, ?r)";
    assert_refused_naming(
        &load_errors_of(&with(clause)),
        &["seven.return (op-return): expected Int64, got () -> Int64"],
        clause,
    );
}

/// In a field of type `Term` the name is the term it spells, in a rule body as in a query, and
/// meets the fact that holds it. The rule body's goal met nothing.
#[test]
fn a_nullary_name_in_a_quoted_term_field_is_the_term() {
    let mut kb = loaded(false);
    assert_eq!(rows(&mut kb, "quoted"), one("1"));
    supply_invocation_imports(&mut kb, &["test.nq.*"]);
    assert_holds(&mut kb, "q(t: seven)");
}

/// A relation's argument is a value slot, so the name is its call there and does not meet a
/// fact holding the name: in a rule body, and now in a query, which met it.
#[test]
fn a_query_and_a_rule_body_read_a_named_fact_alike() {
    let mut kb = loaded(false);
    assert_eq!(rows(&mut kb, "viaName"), Vec::<(String, bool)>::new());
    supply_invocation_imports(&mut kb, &["test.nq.*"]);
    let (all, _, _) = run_query(&mut kb, "holdsName(seven)");
    assert_eq!(all, 0, "the query reads the name as the rule body does");
}

/// In a bracket's binding the name is the name, read in its type context: a sort that shares
/// its name with a nullary operation is the sort's type face there, in a query as in a rule
/// body. Found by `/code-review`: built as the call, the query `hb(Box[V = Positive])` met
/// nothing where it met the fact (measured with the binding reader's call arm absent).
#[test]
fn a_nullary_name_in_a_bracket_binding_is_the_name() {
    let mut kb = load_kb_with(
        r#"
namespace test.nqb
  import anthill.prelude.{Int64}
  sort Positive
    sort T = ?
  end
  operation Positive() -> Int64 = 1
  sort Box
    sort V = ?
  end
  fact hb(Box[V = Positive])
  rule viaRule(?r) :- hb(Box[V = Positive]), ?r <=> 1
end
"#,
    );
    assert_eq!(shown_rows(&mut kb, "test.nqb.viaRule"), one("1"));
    supply_invocation_imports(&mut kb, &["test.nqb.*"]);
    assert_holds(&mut kb, "hb(Box[V = Positive])");
    assert_holds(&mut kb, "(?v <=> Positive) & (?v = 1)");
}
