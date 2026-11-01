//! A DOTTED OPERATION NAME IS READ IN A RULE BODY AND IN A QUERY AS ITS ONE-SEGMENT NAME IS
//! (kernel-language §5.4, "The two readings of a bare operation name"; §6.7): at a
//! function-typed parameter of a call it is the function value, typed and run as `twice` is.
//!
//! WI-20261030-4BXDW, measured on 2c0ae33e and again on ada4cdad, over `apply1(f: (n: Int64) ->
//! Int64, n: Int64)` and `sort S  operation twice(n: Int64) -> Int64 = n * 2  end`: the goal
//! `apply1(S.twice, 3, ?r)` loaded clean and was undecided, "unknown operation:
//! test.dn.apply1.f", the call holding the `field_access(S, twice)` chain; the value slot
//! `?r <=> apply1(S.twice, 3)` was refused with the typer's internal-defect text ("a defect in
//! the walk that built this occurrence"), the walk reaching the chain's segments; and
//! `apply2(Int64.max, 3, 9, ?r)` loaded and was undecided, where the one-segment `max` is
//! refused at load. The operation body's `apply1(S.twice, 3)` and the imported `twice` answered 6.
//!
//! The reading is the user's (2026-11-01, WI-20261017-FTV0Q's decision (b), TYPE-DIRECTED):
//! where the callee's parameter is function-typed the dotted name is the operation; a data
//! slot elsewhere — a fact's column, a relation goal's argument — keeps the chain §6.7 keeps.
//!
//! The pieces. The typer reads a rule body's dotted operation name as the operation body
//! reads the call its loader lowers the name to (`visit.rs`, `dotted_citation_operation` →
//! `member_as_function`), and the fragment it stores holds the reference the evaluator
//! applies — or, for a nullary operation that is its call there, the call itself, which the
//! fragment makes (`?r <=> idv(S.seven)` passed `idv` the chain). A member through a type
//! alias is read at the alias's bindings. A generic function parameter hands the name its
//! arrow as a hint (`is_hof_shaped`). A goal holding such a name is a call, typed whole
//! (`holds_a_type_as_the_rules_term` no longer counts it a type). The clause typing holds no
//! call result at a function value written so (`operation_name_as_function`), which inside a
//! form is the member the operation body's walk lowers the name to. The chain's member is the
//! name it spells even where that name is in scope by itself (`Loader::in_member_name`).
//!
//! Then the rows the user asked fixed inline (2026-11-01, "Fix inline"), and the second
//! `/code-review`'s: a fact pattern's field declared `Term` holds an operation's name as the
//! term it spells, in either spelling (`check_bare_ref`'s quoted-field arm, and
//! `quoted_field_hint`, which hands the field's `Term` to the name). The clause typing reads a
//! dotted nullary name as its call (`collect_occurrence_type_constraints`), so `?f <=> S.seven`
//! beside `applyThunk(?f)` is refused as `?f <=> seven` is. The term walk a fact rides reads a
//! chain's member as a name too, so a member named like an imported const is not folded to its
//! value, and goal and fact still match. A query, which has no typer, makes a dotted name the
//! operation at a parameter its callee declares a function type and the node its one-segment
//! name is at any other (`query_function_value_arguments`' `dotted_op`, read off the written
//! name — `<=>` is such a callee too); and it refuses a call that does not fill its parameter
//! list by the typer's own verdict (`typing::query_call_arity_error`), with two refusals of its
//! own: a parameter left out for its default, and a goal's `result:` label.
//!
//! ## Back-out
//!
//! Each piece made a no-op, one at a time, this file run under each from a temporary binary
//! (measured 2026-11-01, after the second review; the restored baseline 26 passed):
//!
//! | backed out | fails |
//! |---|---|
//! | the typer's reading (`visit.rs`'s rung back to the nullary call only) | `a_dotted_operation_name_at_a_function_parameter_is_the_function`, `…_at_a_generic_function_parameter_…`, `a_body_less_operation_named_dotted_is_refused_at_the_argument`, `a_dotted_operation_name_with_no_arrow_denotes_nothing`, `a_member_through_an_alias_is_read_at_its_bindings`, `a_dotted_nullary_name_at_a_type_parameter_is_its_call`, `a_member_name_in_scope_is_still_the_member`, `a_member_named_like_a_const_in_scope_is_still_the_member`, `a_body_less_spec_operation_takes_a_dotted_operation_name`, `an_operation_name_in_a_quoted_field_is_the_term`, `an_operation_term_parameter_is_no_quoted_field` |
//! | the nullary call node (the rung's `push_visit_at` of the call, back to `check_bare_ref` on the chain) | `a_dotted_nullary_name_at_a_type_parameter_is_its_call`, `a_member_name_in_scope_is_still_the_member`, `a_member_named_like_a_const_in_scope_is_still_the_member` |
//! | the goal is a call (`holds_a_type_as_the_rules_term`'s exemption) | `a_dotted_operation_name_at_a_function_parameter_is_the_function`, `…_at_a_generic_function_parameter_…`, `a_body_less_operation_named_dotted_is_refused_at_the_argument`, `a_member_through_an_alias_is_read_at_its_bindings`, `a_member_name_in_scope_is_still_the_member`, `a_member_named_like_a_const_in_scope_is_still_the_member` |
//! | the hint (`is_hof_shaped`'s dotted arm) | `a_dotted_operation_name_at_a_generic_function_parameter_is_the_function` |
//! | the clause typing's carve-out (back to a nullary name written alone) | `a_dotted_operation_name_inside_a_form_is_the_function`, `…_at_a_function_parameter_…`, `…_at_a_generic_function_parameter_…`, `a_body_less_spec_operation_takes_a_dotted_operation_name`, `a_member_name_in_scope_is_still_the_member`, `a_member_named_like_a_const_in_scope_is_still_the_member` |
//! | the clause typing's reading of the chain as a name (`parts`) | `a_dotted_nullary_name_bound_to_a_variable_is_its_call` |
//! | the member's name in the clause walk (`in_member_name` never set there) | `a_member_name_in_scope_is_still_the_member`, `a_member_named_like_a_const_in_scope_is_still_the_member`, `a_dotted_nullary_name_bound_to_a_variable_is_its_call` |
//! | the member's name in the term walk (`member_chain` never set) | `a_member_named_like_a_const_in_scope_is_still_the_member` |
//! | the alias's receiver type (`dotted_citation_operation`'s `recv_type` `None`) | `a_member_through_an_alias_is_read_at_its_bindings` |
//! | the quoted-field arm (`check_bare_ref`) | `an_operation_name_in_a_quoted_field_is_the_term` |
//! | the quoted field's hint (`quoted_field_hint` never asked) | `an_operation_name_in_a_quoted_field_is_the_term` |
//! | the query's operation (`dotted_op` never asked) | `a_dotted_operation_name_in_a_query_is_the_function`, `a_dotted_nullary_name_alone_in_a_query_is_its_call`, `a_dotted_nullary_name_at_a_query_argument_is_its_call`, `a_dotted_operation_name_at_a_query_value_argument_is_its_name`, `a_query_member_name_in_scope_is_still_the_member` |
//! | the query's nullary call at an argument | `a_dotted_nullary_name_alone_in_a_query_is_its_call`, `a_dotted_nullary_name_at_a_query_argument_is_its_call`, `a_query_member_name_in_scope_is_still_the_member` |
//! | the query's name at a value argument | `a_dotted_operation_name_at_a_query_value_argument_is_its_name` |
//! | the query's arity refusal (`query_call_arity_refusal` answers nothing) | `a_query_call_that_cannot_fill_its_parameters_is_refused`, `a_query_call_that_leaves_a_default_out_is_refused`, `a_query_goal_with_a_result_label_is_refused` |
//! | its left-out default | `a_query_call_that_leaves_a_default_out_is_refused` |
//! | its goal's `result:` label | `a_query_goal_with_a_result_label_is_refused` |
//!
//! Three pieces of the second round failed no row and were removed rather than kept: the dotted
//! rung's own quoted-field arm (`check_bare_ref`'s answers through `member_as_function`), and,
//! in a query, marking the chain written and converting its member as a name (the argument
//! rewrite above reads the written name, and `?r <=> S.seven` is an argument of `<=>`).
//!
//! CONTROLS, green under every back-out by design: `the_operation_body_answers_the_same`,
//! `a_dotted_nullary_name_alone_is_its_call`, `a_relation_argument_keeps_the_chain`,
//! `the_one_segment_names_are_refused_alike`, `a_query_call_to_a_capture_operation_is_not_refused`.

use crate::common::{
    assert_refused_naming, load_errors_of, load_kb_with, query_pattern_refusals as query_refusals,
    query_pattern_term, query_unary, shown_rows, supply_invocation_imports,
};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

const PROGRAM: &str = r#"
namespace test.dn
  import anthill.prelude.{Int64}

  operation apply1(f: (n: Int64) -> Int64, n: Int64) -> Int64 = f(n)
  operation apply2(f: (a: Int64, b: Int64) -> Int64, a: Int64, b: Int64) -> Int64 = f(a, b)
  operation applyThunk(f: () -> Int64) -> Int64 = f()
  operation idv[X](x: X) -> X = x
  operation applyG[A, B](f: (a: A) -> B, x: A) -> B = f(x)
  operation thunkG[X](f: () -> X) -> X = f()
  operation g(n: Int64 = 5) -> Int64 = n + 1
  operation cap[R](x: Int64, ...rest: R) -> Int64 = x
  sort S
    operation twice(n: Int64) -> Int64 = n * 2
    operation seven() -> Int64 = 7
  end
  sort Box[V]
    operation wrap(x: V) -> V = x
  end
  sort CA = Box[V = Int64]

  operation oTwice() -> Int64 = apply1(S.twice, 3)
  operation oSeven() -> Int64 = applyThunk(S.seven)
  operation oAlias() -> Int64 = apply1(CA.wrap, 3)

  fact holds(S.twice)
  fact isSeven(7)
  rule heldName(?r) :- holds(S.twice), ?r <=> 1
  rule bareSeven(?r) :- ?r <=> S.seven
  rule sevenAtTypeParameter(?r) :- ?r <=> idv(S.seven)
"#;

/// The rule-body rows of the ticket, each a spelling of one call with a function argument.
const CLAUSES: &str = r#"
  rule goalTwice(?r) :- apply1(S.twice, 3, ?r)
  rule valueTwice(?r) :- ?r <=> apply1(S.twice, 3)
  rule inArithmetic(?r) :- ?r <=> apply1(S.twice, 3) + 1
  rule viaLabel(?r) :- ?r <=> apply1(n: 3, f: S.twice)
  rule viaResultLabel(?r) :- apply1(n: 3, f: S.twice, result: ?r)
  rule goalSeven(?r) :- applyThunk(S.seven, ?r)
  rule valueSeven(?r) :- ?r <=> applyThunk(S.seven)
  rule goalAlias(?r) :- apply1(CA.wrap, 3, ?r)
  rule valueAlias(?r) :- ?r <=> apply1(CA.wrap, 3)
"#;

/// The same at a generic function parameter.
const GENERIC: &str = r#"
  rule goalGeneric(?r) :- applyG(S.twice, 3, ?r)
  rule valueGeneric(?r) :- ?r <=> applyG(S.twice, 3)
  rule thunkGeneric(?r) :- ?r <=> thunkG(S.seven)
  rule thunkGenericGoal(?r) :- thunkG(S.seven, ?r)
"#;

/// A fact pattern's field declared `Term` holds what is written there: the operation's name,
/// dotted or by its one-segment name, matched against the fact holding it.
const QUOTED: &str = r#"
  import anthill.reflect.{Term}
  import test.dn.S.{twice}
  entity held(t: Term)
  fact held(t: S.twice)
  fact held(t: S.seven)
  fact held(t: twice)
  rule findTwice(?r) :- held(t: S.twice), ?r <=> 1
  rule findSeven(?r) :- held(t: S.seven), ?r <=> 1
  rule findOneSegment(?r) :- held(t: twice), ?r <=> 1
"#;

/// The same inside a form.
const FORMS: &str = r#"
  rule inIf(?r) :- ?r <=> (if true then apply1(S.twice, 3) else 0)
  rule inLambda(?r) :- ?r <=> apply1(lambda n -> apply1(S.twice, n), 3)
"#;

fn with(clauses: &str) -> String {
    format!("{PROGRAM}\n{clauses}\nend\n")
}

fn rows(kb: &mut KnowledgeBase, relation: &str) -> Vec<(String, bool)> {
    shown_rows(kb, &format!("test.dn.{relation}"))
}

fn one(value: &str) -> Vec<(String, bool)> {
    vec![(value.to_string(), true)]
}

const DEFECT: &str = "a defect in the walk";

/// `src`'s refusals, of which one names each of `tokens` and starts at the line and column of
/// the first `at` on the line holding `clause`; none is the typer's internal-defect text.
fn assert_refused_at(src: &str, clause: &str, at: &str, tokens: &[&str]) {
    let errors = load_errors_of(src);
    assert_refused_naming(&errors, tokens, clause);
    assert!(
        errors.iter().all(|e| !e.contains(DEFECT)),
        "{clause}: no internal-defect text: {errors:?}"
    );
    let line = src
        .lines()
        .position(|l| l.contains(clause))
        .unwrap_or_else(|| panic!("the fixture holds `{clause}`"))
        + 1;
    let col = src.lines().nth(line - 1).unwrap().find(at).unwrap() + 1;
    assert!(
        errors.iter().any(|e| e.starts_with(&format!("{line}:{col}:"))),
        "{clause}: refused at the argument `{at}`, {line}:{col}: {errors:?}"
    );
}

/// One definite answer to a query pattern.
fn assert_holds(kb: &mut KnowledgeBase, pattern: &str) {
    let goal = query_pattern_term(kb, pattern);
    let (solutions, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    let definite = solutions.iter().filter(|s| s.residual.is_empty()).count();
    let messages: Vec<String> = stats.errors.iter().map(|e| e.message.clone()).collect();
    assert!(
        solutions.len() == 1 && definite == 1 && !stats.truncated,
        "{pattern}: one definite answer, got {} ({definite} definite): {messages:?}",
        solutions.len()
    );
}

/// The rows of the ticket: the goal, the value slot, under arithmetic, by label and by
/// `result:`, a nullary operation whose result is no function, and a member through a type
/// alias — each answers what its operation-body twin does. The goals were undecided, "unknown
/// operation: test.dn.apply1.f"; the value slots were refused with the internal-defect text.
#[test]
fn a_dotted_operation_name_at_a_function_parameter_is_the_function() {
    let mut kb = load_kb_with(&with(CLAUSES));
    for (relation, value) in [
        ("goalTwice", "6"),
        ("valueTwice", "6"),
        ("inArithmetic", "7"),
        ("viaLabel", "6"),
        ("viaResultLabel", "6"),
        ("goalSeven", "7"),
        ("valueSeven", "7"),
        ("goalAlias", "3"),
        ("valueAlias", "3"),
    ] {
        assert_eq!(rows(&mut kb, relation), one(value), "{relation}");
    }
}

/// Through a type alias the member is read at the bindings the alias fixes, as the operation
/// body reads it: `CB.wrap` over `sort CB = Box[V = String]` is no `(n: Int64) -> Int64`, in the
/// goal and in the value slot. The operation body's spelling is refused either way by design.
#[test]
fn a_member_through_an_alias_is_read_at_its_bindings() {
    for clause in [
        "rule goalCB(?r) :- apply1(CB.wrap, 3, ?r)",
        "rule valueCB(?r) :- ?r <=> apply1(CB.wrap, 3)",
        "operation oCB() -> Int64 = apply1(CB.wrap, 3)",
    ] {
        let src = with(&format!("  sort CB = Box[V = String]\n  {clause}"));
        assert_refused_naming(
            &load_errors_of(&src),
            &["apply1.f", "expected Int64 -> Int64, got String -> String"],
            clause,
        );
    }
}

/// At a GENERIC function parameter (`applyG[A, B](f: (a: A) -> B, …)`, `thunkG[X](f: () -> X)`)
/// the arrow reaches the name as the hint a one-segment name is given (`is_hof_shaped`): the
/// argument refused as denoting nothing, and the nullary one was the call, undecided at run
/// time. Found by `/code-review`.
#[test]
fn a_dotted_operation_name_at_a_generic_function_parameter_is_the_function() {
    let mut kb = load_kb_with(&with(GENERIC));
    for (relation, value) in [
        ("goalGeneric", "6"),
        ("valueGeneric", "6"),
        ("thunkGeneric", "7"),
        ("thunkGenericGoal", "7"),
    ] {
        assert_eq!(rows(&mut kb, relation), one(value), "{relation}");
    }
}

/// Inside a form — an `if`, a lambda's body — the operation body's walk lowers the dotted name to
/// the member written without parentheses, and the clause typing holds no call result there
/// (`operation_name_as_function`): it was refused, "twice.return (op-return): expected Int64, got
/// Int64 -> Int64", where `twice` answers (measured on ada4cdad). Found by `/code-review`.
#[test]
fn a_dotted_operation_name_inside_a_form_is_the_function() {
    let mut kb = load_kb_with(&with(FORMS));
    assert_eq!(rows(&mut kb, "inIf"), one("6"));
    assert_eq!(rows(&mut kb, "inLambda"), one("6"));
}

/// The member of a dotted name is the name it spells, also where that name is in scope by
/// itself: with `S.{seven}` imported the walk built it as `seven()`, so the chain spelled no name
/// and each spelling was refused, "r.body (rule): expected String, got Int64" (measured on
/// ada4cdad, `?r <=> S.seven` too). Found by `/code-review`.
#[test]
fn a_member_name_in_scope_is_still_the_member() {
    let mut kb = load_kb_with(&with(
        "  import test.dn.S.{seven}
  rule viaImport(?r) :- applyThunk(S.seven, ?r)
  rule importAtTypeParameter(?r) :- ?r <=> idv(S.seven)
  rule importAlone(?r) :- ?r <=> S.seven",
    ));
    for relation in ["viaImport", "importAtTypeParameter", "importAlone"] {
        assert_eq!(rows(&mut kb, relation), one("7"), "{relation}");
    }
}

/// A body-less spec operation's function parameter takes the name as an operation's does, in the
/// value slot and as the goal: it was refused, "runIt.f (op-arg): expected () -> Int64, got
/// Int64". Found by `/code-review`.
#[test]
fn a_body_less_spec_operation_takes_a_dotted_operation_name() {
    let mut kb = load_kb_with(
        r#"
namespace test.dsp
  import anthill.prelude.{Int64}
  sort Runner
    sort C = ?
    operation runIt(c: C, f: () -> Int64) -> Int64
  end
  sort Box
    entity box(v: Int64)
    provides Runner[C = Box]
    operation runIt(c: Box, f: () -> Int64) -> Int64 = f()
  end
  sort S
    operation seven() -> Int64 = 7
  end
  rule valueRun(?r) :- ?r <=> Runner.runIt(box(v: 1), S.seven)
  rule goalRun(?r) :- Runner.runIt(box(v: 1), S.seven, ?r)
end
"#,
    );
    for relation in ["valueRun", "goalRun"] {
        assert_eq!(shown_rows(&mut kb, &format!("test.dsp.{relation}")), one("7"), "{relation}");
    }
}

/// In a fact pattern a field declared `Term` holds the term written there, so an operation's
/// name is that name, in both spellings, and finds the fact holding it (`check_bare_ref`'s
/// quoted-field arm, and the hint that hands the field's `Term` to the name). Each goal on an
/// operation that takes arguments was refused at load — the dotted one with the internal-defect
/// text, the one-segment one as denoting nothing — while the fact it searches for loaded.
/// `findSeven` is the nullary operation's, which answered before (6Q43W). Found by
/// `/code-review`; the user, 2026-11-01: "Fix inline".
#[test]
fn an_operation_name_in_a_quoted_field_is_the_term() {
    let mut kb = load_kb_with(&with(QUOTED));
    for relation in ["findTwice", "findSeven", "findOneSegment"] {
        assert_eq!(rows(&mut kb, relation), one("1"), "{relation}");
    }
}

/// An operation's `Term` parameter in a call typed whole is no quoted field — the call evaluates
/// its arguments, and the name has no value there — so it is refused as the one-segment name is,
/// at the argument; it was refused with the internal-defect text, the walk reaching the chain's
/// segments.
#[test]
fn an_operation_term_parameter_is_no_quoted_field() {
    let clause = "rule viaOp(?r) :- ?r <=> quote1(S.twice)";
    let src = with(&format!(
        "  import anthill.reflect.{{Term}}\n  operation quote1(t: Term) -> Int64 = 1\n  {clause}"
    ));
    assert_refused_at(&src, clause, "S.twice", &["twice.function-value"]);
}

/// In a query a nullary operation's dotted name is its call where it is written alone — the
/// argument of `<=>` — and where it is an operation's argument that expects no function, as in a
/// rule body. They bound the name `seven` and passed the chain to `idv` (measured on ada4cdad).
/// Asked of a relation, `isSeven(?r)`, which matches what `?r` holds: a comparison `?r = 7`
/// reduces its operand, and held for the name and the chain alike.
#[test]
fn a_dotted_nullary_name_alone_in_a_query_is_its_call() {
    let mut kb = load_kb_with(&with(""));
    assert_holds(&mut kb, "(?r <=> test.dn.S.seven) & test.dn.isSeven(?r)");
}

/// …and so it is at an operation's argument that expects no function.
#[test]
fn a_dotted_nullary_name_at_a_query_argument_is_its_call() {
    let mut kb = load_kb_with(&with(""));
    assert_holds(&mut kb, "(?r <=> test.dn.idv(test.dn.S.seven)) & test.dn.isSeven(?r)");
}

/// The member of a query's dotted name is the name it spells, also where an invocation import
/// puts that name in scope by itself: the name is read off the written chain.
#[test]
fn a_query_member_name_in_scope_is_still_the_member() {
    let mut kb = load_kb_with(&with(""));
    supply_invocation_imports(&mut kb, &["test.dn.*", "test.dn.S.{seven}"]);
    assert_holds(&mut kb, "(?r <=> S.seven) & isSeven(?r)");
}

/// A query has no typer, so a call that does not fill its parameter list is refused where the
/// pattern is converted, by the verdict the clause spelling gets at load
/// (`typing::query_call_arity_error`): `S.twice()` was folded to the name and applied
/// (`apply1(S.twice(), 3, ?r)` answered 6), `S.twice(1, 2)` was read by its first argument
/// (answered 2), and a `result:` label in a value slot was dropped (`idv(x: 3, result: 4)`
/// answered 3). The well-formed call is the control.
#[test]
fn a_query_call_that_cannot_fill_its_parameters_is_refused() {
    let mut kb = load_kb_with(&with(""));
    for (pattern, tokens) in [
        ("test.dn.apply1(test.dn.S.twice(), 3, ?r)", ["twice.arity", "got 0 arguments"]),
        ("?r <=> test.dn.S.twice(1, 2)", ["twice.arity", "got 2 arguments"]),
        ("?r <=> test.dn.idv(x: 3, result: 4)", ["idv.result", "names no parameter"]),
    ] {
        assert_refused_naming(&query_refusals(&mut kb, pattern), &tokens, pattern);
    }
    assert!(query_refusals(&mut kb, "?r <=> test.dn.S.twice(3)").is_empty());
    assert_holds(&mut kb, "(?r <=> test.dn.S.twice(3)) & (?r = 6)");
}

/// A query reads a goal's result as one more positional argument, and no `result:` label: such a
/// goal answered nothing, where the clause `apply1(n: 3, f: S.twice, result: ?r)` answers 6. Now
/// refused, saying how to write it.
#[test]
fn a_query_goal_with_a_result_label_is_refused() {
    let mut kb = load_kb_with(&with(""));
    assert_refused_naming(
        &query_refusals(&mut kb, "test.dn.apply1(test.dn.S.twice, 3, result: ?r)"),
        &["apply1.result", "a query reads no `result:` column"],
        "the labelled result",
    );
}

/// CONTROL, passing either way by design: an operation with a variadic capture is not judged by
/// the query's check, whose labels the typed call folds into the capture — `cap(1)` and
/// `cap(1, a: 2, b: 3)` convert, as the clause `?r <=> cap(1)` loads.
#[test]
fn a_query_call_to_a_capture_operation_is_not_refused() {
    let mut kb = load_kb_with(&with("  rule viaCap(?r) :- ?r <=> cap(1)"));
    assert_eq!(rows(&mut kb, "viaCap"), one("1"));
    for pattern in ["?r <=> test.dn.cap(1)", "?r <=> test.dn.cap(1, a: 2, b: 3)"] {
        assert!(query_refusals(&mut kb, pattern).is_empty(), "{pattern} converts");
    }
}

/// Where no function is expected, a query's dotted name that takes arguments is the name its
/// one-segment spelling is: `idv(S.twice)` binds `twice`, as `idv(twice)` does, where it bound
/// the chain `field_access(S, twice)`.
#[test]
fn a_dotted_operation_name_at_a_query_value_argument_is_its_name() {
    let mut kb = load_kb_with(&with("  fact named(twice)\n  import test.dn.S.{twice}"));
    assert_holds(&mut kb, "(?r <=> test.dn.idv(test.dn.S.twice)) & test.dn.named(?r)");
}

/// A parameter's default is filled by the typer (proposal 069), and no typer runs on a query, so
/// a query's call that leaves a defaulted parameter out is refused, saying so: `?r <=> g()` over
/// `g(n: Int64 = 5)` bound the name `g`, and `apply1(g(), 3, ?r)` applied `g` to 3 (answered 4),
/// where the clause `?r <=> g()` answers 6. The argument written is the control.
#[test]
fn a_query_call_that_leaves_a_default_out_is_refused() {
    let mut kb = load_kb_with(&with("  rule viaDefault(?r) :- ?r <=> g()"));
    assert_eq!(rows(&mut kb, "viaDefault"), one("6"));
    for pattern in ["?r <=> test.dn.g()", "test.dn.apply1(test.dn.g(), 3, ?r)"] {
        assert_refused_naming(
            &query_refusals(&mut kb, pattern),
            &["g.n", "a query has no typer to fill a parameter's default"],
            pattern,
        );
    }
    assert_holds(&mut kb, "(?r <=> test.dn.g(1)) & (?r = 2)");
}

/// The clause typing reads a dotted nullary name as its call, as `seven` is read: `?f <=> S.seven`
/// beside `applyThunk(?f)` is refused at load as `?f <=> seven` is, where it loaded and was
/// undecided at run time — the chain had been constrained as a `field_access` application, whose
/// result pinned nothing (measured on ada4cdad). Found by `/code-review`.
#[test]
fn a_dotted_nullary_name_bound_to_a_variable_is_its_call() {
    for (clause, at) in [
        ("rule viaVar(?r) :- ?f <=> S.seven, ?r <=> applyThunk(?f)", "S.seven"),
        (
            "import test.dn.S.{seven}\n  rule viaVarOne(?r) :- ?f <=> seven, ?r <=> applyThunk(?f)",
            "seven",
        ),
    ] {
        let rule = clause.lines().last().unwrap().trim();
        assert_refused_at(&with(clause), rule, at, &["seven.return", "expected Int64, got () -> Int64"]);
    }
}

/// A dotted name's member is the name it spells also where it names a const in scope by itself:
/// with a const `seven` imported the member was folded to the const's value (`field_access(S,
/// 100)`), so `?r <=> S.seven` bound that, `applyThunk(S.seven, ?r)` was undecided and
/// `idv(S.seven)` was refused with the internal-defect text (measured on ada4cdad). The fact the
/// goal searches for is built by the same reading, so it still matches. Found by `/code-review`.
#[test]
fn a_member_named_like_a_const_in_scope_is_still_the_member() {
    let mut kb = load_kb_with(&format!(
        "{}\nnamespace test.dnc
  import anthill.prelude.{{Int64}}
  const seven: Int64 = 100
end
namespace test.dnu
  import anthill.prelude.{{Int64}}
  import test.dn.{{S, idv, applyThunk}}
  import test.dnc.{{seven}}
  fact heldC(S.seven)
  rule constAlone(?r) :- ?r <=> S.seven
  rule constThunk(?r) :- applyThunk(S.seven, ?r)
  rule constAtTypeParameter(?r) :- ?r <=> idv(S.seven)
  rule constFact(?r) :- heldC(S.seven), ?r <=> 7
end
",
        with("")
    ));
    for relation in ["constAlone", "constThunk", "constAtTypeParameter", "constFact"] {
        assert_eq!(shown_rows(&mut kb, &format!("test.dnu.{relation}")), one("7"), "{relation}");
    }
}

/// CONTROL, passing either way by design: the operation body's spelling of the same calls.
#[test]
fn the_operation_body_answers_the_same() {
    let mut kb = load_kb_with(&with(""));
    for (twin, value) in [("oTwice", "6"), ("oSeven", "7"), ("oAlias", "3")] {
        let answers: Vec<_> = query_unary(&mut kb, &format!("test.dn.{twin}"))
            .into_iter()
            .map(|(v, definite)| (crate::common::show_value(&kb, &v), definite))
            .collect();
        assert_eq!(answers, one(value), "the operation body's {twin}");
    }
}

/// An operation with no body has no function value, so `Int64.max` at a function parameter is
/// refused at load, at the argument, as `max` is: the goal loaded clean and was undecided, the
/// value slot was refused with the internal-defect text.
#[test]
fn a_body_less_operation_named_dotted_is_refused_at_the_argument() {
    for clause in [
        "rule goalMax(?r) :- apply2(Int64.max, 3, 9, ?r)",
        "rule valueMax(?r) :- ?r <=> apply2(Int64.max, 3, 9)",
    ] {
        assert_refused_at(&with(clause), clause, "Int64.max", &["max.function-value", "carries no body"]);
    }
}

/// Where no function type is written to lift it against, a dotted operation that takes
/// arguments denotes nothing, as `twice` does: refused at the argument. It was refused with
/// the internal-defect text.
#[test]
fn a_dotted_operation_name_with_no_arrow_denotes_nothing() {
    let clause = "rule atTypeParameter(?r) :- ?r <=> idv(S.twice)";
    assert_refused_at(
        &with(clause),
        clause,
        "S.twice",
        &["twice.function-value", "expected a slot declaring the arrow to lift this operation against"],
    );
}

/// CONTROL, refused either way by design: the one-segment twins of the two refusals above say
/// what the dotted names now say.
#[test]
fn the_one_segment_names_are_refused_alike() {
    for (clause, at, token) in [
        (
            "import anthill.prelude.Int64.{max}\n  rule goalMax(?r) :- apply2(max, 3, 9, ?r)",
            "max",
            "carries no body",
        ),
        (
            "import test.dn.S.{twice}\n  rule atTypeParameter(?r) :- ?r <=> idv(twice)",
            "twice",
            "expected a slot declaring the arrow to lift this operation against",
        ),
    ] {
        let rule = clause.lines().last().unwrap().trim();
        assert_refused_at(&with(clause), rule, at, &[token]);
    }
}

/// CONTROL, passing either way by design: a nullary operation's dotted name alone is its call.
#[test]
fn a_dotted_nullary_name_alone_is_its_call() {
    let mut kb = load_kb_with(&with(""));
    assert_eq!(rows(&mut kb, "bareSeven"), one("7"));
}

/// At a type parameter the call does not pin to a function, a nullary operation's dotted name
/// is its call too, as `idv(seven)` is. It passed `idv` the chain, which answered
/// `field_access(S, seven)` (measured on ada4cdad): the call's stored fragment held the chain,
/// which only the resolver reduces, and an operation body never does.
#[test]
fn a_dotted_nullary_name_at_a_type_parameter_is_its_call() {
    let mut kb = load_kb_with(&with(""));
    assert_eq!(rows(&mut kb, "sevenAtTypeParameter"), one("7"));
}

/// CONTROL, passing either way by design: a relation's argument is a data slot, which keeps the
/// chain the fact holds (§6.7), in a rule body and in a query.
#[test]
fn a_relation_argument_keeps_the_chain() {
    let mut kb = load_kb_with(&with(""));
    assert_eq!(rows(&mut kb, "heldName"), one("1"));
    assert_holds(&mut kb, "test.dn.holds(test.dn.S.twice)");
}

/// A query has no typer, so the parameter's declared type decides: at a function-typed one the
/// dotted name is the operation, written qualified or through an invocation import, at a
/// nullary operation whose result is no function, and through a type alias. Each was
/// undecided, "unknown operation: test.dn.apply1.f".
#[test]
fn a_dotted_operation_name_in_a_query_is_the_function() {
    let mut kb = load_kb_with(&with(""));
    for pattern in [
        "test.dn.apply1(test.dn.S.twice, 3, ?r) & (?r = 6)",
        "(?r <=> test.dn.apply1(test.dn.S.twice, 3)) & (?r = 6)",
        "test.dn.applyThunk(test.dn.S.seven, ?r) & (?r = 7)",
        "test.dn.apply1(test.dn.CA.wrap, 3, ?r) & (?r = 3)",
    ] {
        assert_holds(&mut kb, pattern);
    }
    supply_invocation_imports(&mut kb, &["test.dn.*"]);
    assert_holds(&mut kb, "apply1(S.twice, 3, ?r) & (?r = 6)");
}
