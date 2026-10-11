//! WI-20261011-CR6GD — clauses answer a goal, not a call (kernel-language.md §5.3).
//!
//! THE RULE. `operation open(b: Box) -> Int64` beside `rule open(mk(v: ?v), ?v) :- true`
//! is one definition written relationally. The goal `Box.open(Box.mk(4), ?x)` resolves
//! through the clause. A call in an operation body, `Box.open(Box.mk(4))`, names the
//! operation, and a call runs a body, a host function or a builtin: this operation has
//! none, and the call is refused where it is written. A carrier's `eq` written as clauses
//! is the one operation a call runs by proving it. In an operation body the clauses are
//! reached as a relation — a rule alone, cited by name (proposal 052).
//!
//! BEFORE. The call loaded clean and died at run time, `operation has no body: …Box.open
//! — … no builtin, and no rule clause indexed under it`: a message naming a missing
//! clause, about an operation with one.
//!
//! A RULE BODY IS NOT JUDGED. There the spelling is a goal the clauses answer, or a term
//! kept as data — matched against a head, handed to a predicate that calls it — and each
//! answers as it did. A call a rule body needs the value of still waits, saying nothing.
//!
//! EVERY ROW HAS ITS OWN SOURCE: a row that shares a fixture with another measures the
//! fixture.
//!
//! CONTROLS — each measured by backing the named piece out and running this file.
//!
//!   THE REFUSAL OUT (`check_apply_iter`'s `clause_defined_own_operation` arm) and the
//!   run-time message as it was. FAIL, each loading clean:
//!     a_call_in_an_operation_body_is_refused
//!     a_call_of_a_predicate_is_refused_and_names_its_goal
//!     the_advised_goal_is_spelled_as_the_clauses_are_written
//!     a_dot_on_the_value_is_refused
//!     an_imported_name_is_refused
//!     a_call_inside_the_sort_is_refused
//!     a_call_under_a_lambda_is_refused
//!     a_call_in_a_const_is_refused
//!     a_call_in_a_match_guard_is_refused
//!     a_namespaces_operation_is_refused
//!     a_parametric_sorts_operation_is_refused
//!     a_caller_generic_in_the_content_is_refused
//!   FAIL, on the message:
//!     a_host_entry_is_told_the_operation_is_defined_by_clauses
//!     an_operation_with_nothing_is_told_it_has_no_clause — a pin of the new text
//!
//!   THE RULE-BODY GATE OUT (`in_rule_body` not asked, so a rule body is judged too). FAIL:
//!     a_parametric_sorts_goal_answers
//!     a_parametric_sorts_term_kept_as_data_is_matched
//!     a_call_in_a_rule_bodys_value_position_waits_as_it_did
//!     a_lambda_in_a_rule_body_is_not_judged
//!   and `wi_rm247_data_sort_equation_test::a_clause_backed_operation_is_reached_from_-
//!   a_rule_body`. A plain sort's rule-body term is not handed to the call's check, so
//!     a_term_kept_as_data_is_matched_against_a_head
//!     a_goal_passed_as_data_is_still_called
//!   pass with the gate out; they FAILED under the first cut of this change, which also
//!   refused the application in every data slot of a rule body.
//!
//!   ONE LEG OF `clause_defined_own_operation` OUT. FAIL:
//!     nothing executable — a_bodied_operation_with_a_lemma_under_it_is_still_called
//!     no provider can supply it — a_provided_sorts_operation_is_the_providers
//!     not a carrier's `eq` — a_carriers_eq_written_as_clauses_still_runs
//!
//!   THE CLAUSE READING OF THE ADVISED GOAL OUT (no result column, whatever the heads). FAIL:
//!     a_call_in_an_operation_body_is_refused
//!     the_advised_goal_is_spelled_as_the_clauses_are_written
//!
//!   PASS with all of it backed out, by design — what the change must not move:
//!     the_goal_answers_through_the_clauses
//!     the_goals_so_spelled_answer
//!     a_goal_under_a_connective_is_still_a_goal
//!     an_equation_beside_the_clauses_defines_the_call
//!   and the repairs the refusal advises, each run:
//!     the_advised_body_runs
//!     the_advised_rule_alone_is_cited_as_a_relation
//!     the_advised_predicate_alone_is_cited_as_a_relation
//!   (the third, the goal spelling, is `the_goal_answers_through_the_clauses`).
//!
//!   NOT ADVISED, though `an_equation_beside_the_clauses_defines_the_call` runs: a
//!   `@[simp]` equation defines the call only where its left-hand side matches the call
//!   as written. Measured, `rule open(mk(v: ?v)) <=> ?v @[simp]` rewrites
//!   `Box.open(Box.mk(4))` and not `Box.open(b)` after `let b = Box.mk(4)`, which loads
//!   clean and dies `OperationBodyMissing`. (It did not rewrite the first either, when
//!   this refusal was written: see the positional section below.)
//!
//!   NOT COVERED. An operation of a sort with no constructor is left to its dispatch: a
//!   provider may supply it, and the call is judged with the carrier in hand. A bare
//!   operation name passed as a function value is no application and is not judged here;
//!   the function-value rule already refuses one that carries no body.
//!
//! A CONSTRUCTOR WRITTEN WITH POSITIONAL ARGUMENTS — found while delivering the above, on
//! the repair it first advised (an equation). An operation body's `Box.mk(4)` was read, as
//! a term, in the shape it is written: `mk(4)`, beside the `mk(v: ?v)` every pattern and
//! every other carrier holds (docs/design/entity-term-mapping.md). Two readers take the
//! node as a term before it is evaluated. The `@[simp]` matcher reads its view: `rule
//! open(mk(v: ?v)) <=> ?v @[simp]` did not fire on `Box.open(Box.mk(4))`, which loaded
//! clean and died `OperationBodyMissing`. A call-site precondition reads its term twin:
//! `requires Pair.big(p)` was not provable at `need(Pair.pair(7, 2))`, a load error on a
//! program whose named twin loads. View and twin now present the canonical entity form.
//!
//!   CONTROLS — measured by having `positional_ctor_fields`, the gate of the canonical
//!   form, answer `None`.
//!   FAIL, each dying `OperationBodyMissing`:
//!     an_equation_fires_on_a_positional_constructor
//!     an_equation_written_positionally_fires_too
//!     a_positional_argument_takes_the_field_no_name_took
//!     a_positional_constructor_under_another_is_read_too
//!     an_imported_constructor_name_is_read_too
//!     a_parametric_sorts_constructor_is_read_too
//!   FAIL, refused at load for an unprovable precondition:
//!     a_precondition_is_proved_at_a_positional_constructor
//!   With the VIEW's four readers alone answering as written, the six equation rows
//!   fail and the precondition row passes; with the TWIN alone, the reverse.
//!
//!   PASS either way, by design:
//!     the_named_spelling_fires_as_it_did
//!     a_precondition_that_does_not_hold_is_still_refused — refused before for the shape,
//!       now for the fact; the row says which by naming the clause as judged.
//!
//!   WHAT ELSE IT MOVED: a `@[simp]` rule headed by a constructor now rewrites a
//!   positionally written construction where a body is typed, so behind a seal a later
//!   load's such rule is refused — `wi_9bkz4_sealed_bodies_test::a_simp_rule_over_a_-
//!   construction_is_refused_behind_a_seal`, the row written to fail on that day.
//!
//!   NOT COVERED, each measured with the change in place. An application written all
//!   NAMED and out of declaration order (`Pair.pair(b: 2, a: 7)`) is still read as
//!   written and matches neither reader: telling it from a canonical one takes the field
//!   list at every read (WI-20261011-12VZB). A constructor of no field written bare (`Color.code(red)` under
//!   `rule code(red) <=> 1 @[simp]`) is not matched by the equation, though its
//!   precondition is proved: the node is a `var_ref`, its twin is the name and its view
//!   is not, a difference kept on purpose at the lowering boundary. An equation with a
//!   constructor pattern does not see through a binding (`let b = Box.mk(4)` then
//!   `Box.open(b)`): it rewrites the call as written.

use anthill_core::eval::Value;

use crate::common::{
    assert_refused_naming, interp_for, load_errors_of, load_kb_with, query_unary, run_int64,
};

/// `lib.<ns>.Box`, a data sort holding `members`; `outside` is written in `test.<ns>`,
/// which imports the sort.
fn boxed(ns: &str, members: &str, outside: &str) -> String {
    format!(
        "namespace lib.{ns}\n  import anthill.prelude.{{Int64, Bool}}\n  sort Box\n    entity mk(v: Int64)\n{members}\n  end\nend\nnamespace test.{ns}\n  import anthill.prelude.{{Int64, Bool, List, Error}}\n  import anthill.prelude.List.{{length}}\n  import lib.{ns}.Box\n{outside}\nend\n"
    )
}

/// The two operations the ticket is about: a predicate and a value, each defined by a
/// clause and by nothing else. `full` holds above 3, so it has an instance on each side.
const CLAUSES: &str = "    operation full(b: Box) -> Bool\n    rule full(mk(v: ?v)) :- ?v > 3\n    operation open(b: Box) -> Int64\n    rule open(mk(v: ?v), ?v) :- true";

/// The refusal, by what the back-out makes disappear: the operation, and the sentence.
#[track_caller]
fn assert_call_refused(src: &str, op: &str) {
    assert_refused_naming(
        &load_errors_of(src),
        &[op, "defined by clauses alone"],
        "a call of a clause-defined operation",
    );
}

#[track_caller]
fn assert_runs(src: &str, entry: &str, expected: i64) {
    assert_eq!(run_int64(src, entry), Ok(expected), "{entry}");
}

// ── the call is refused where it is written ─────────────────────────────────

#[test]
fn a_call_in_an_operation_body_is_refused() {
    let errs = load_errors_of(&boxed(
        "cr6gdcall",
        CLAUSES,
        "  operation go() -> Int64 = Box.open(Box.mk(4))",
    ));
    // The goal that does answer is named with the result as one more column.
    assert_refused_naming(
        &errs,
        &["lib.cr6gdcall.Box.open", "defined by clauses alone", "`open(…, ?result)`"],
        "the ticket's value program",
    );
}

#[test]
fn a_call_of_a_predicate_is_refused_and_names_its_goal() {
    let errs = load_errors_of(&boxed(
        "cr6gdpred",
        CLAUSES,
        "  operation go() -> Int64 = if Box.full(Box.mk(4)) then 1 else 0",
    ));
    assert_refused_naming(
        &errs,
        &["lib.cr6gdpred.Box.full", "defined by clauses alone", "`full(…)`"],
        "the ticket's predicate program",
    );
    // A predicate's goal is written at its own arity: no result column is advised.
    assert!(!errs.join(" | ").contains("?result"), "{errs:?}");
}

/// The advised goal is read off the heads written, not off the return type: a `Bool`
/// operation given its result as a column is asked with that column, and an operation
/// of no parameter is asked with the result alone.
#[test]
fn the_advised_goal_is_spelled_as_the_clauses_are_written() {
    let errs = load_errors_of(&boxed(
        "cr6gdspell",
        "    operation odd(b: Box) -> Bool\n    rule odd(mk(v: 1), true) :- true\n    rule odd(mk(v: 2), false) :- true",
        "  operation four() -> Int64\n  rule four(4) :- true\n  operation go() -> Int64 = if Box.odd(Box.mk(1)) then four() else 0",
    ));
    assert_refused_naming(
        &errs,
        &["`odd(…, ?result)`", "`four(?result)`"],
        "the goal each refusal advises",
    );
}

/// …and each of those goals answers.
#[test]
fn the_goals_so_spelled_answer() {
    let mut kb = load_kb_with(&boxed(
        "cr6gdspellg",
        "    operation odd(b: Box) -> Bool\n    rule odd(mk(v: 1), true) :- true\n    rule odd(mk(v: 2), false) :- true",
        "  operation four() -> Int64\n  rule four(4) :- true\n  rule r(?x) :- four(?x)\n  rule o(?x) :- Box.odd(Box.mk(2), ?x)",
    ));
    let r = query_unary(&mut kb, "test.cr6gdspellg.r");
    assert!(matches!(r.as_slice(), [(Value::Int(4), true)]), "{r:?}");
    let o = query_unary(&mut kb, "test.cr6gdspellg.o");
    assert!(matches!(o.as_slice(), [(Value::Bool(false), true)]), "{o:?}");
}

#[test]
fn a_dot_on_the_value_is_refused() {
    assert_call_refused(
        &boxed(
            "cr6gddot",
            CLAUSES,
            "  operation go() -> Int64 =\n    let b = Box.mk(4)\n    b.open()",
        ),
        "Box.open",
    );
}

#[test]
fn an_imported_name_is_refused() {
    assert_call_refused(
        &boxed(
            "cr6gdimp",
            CLAUSES,
            "  import lib.cr6gdimp.Box.{open}\n  operation go() -> Int64 =\n    let b = Box.mk(4)\n    open(b)",
        ),
        "Box.open",
    );
}

#[test]
fn a_call_inside_the_sort_is_refused() {
    let members = format!("{CLAUSES}\n    operation twice(b: Box) -> Int64 = open(b) + open(b)");
    assert_call_refused(
        &boxed(
            "cr6gdin",
            &members,
            "  operation go() -> Int64 = Box.twice(Box.mk(4))",
        ),
        "Box.open",
    );
}

/// The binder's type is not known when the call under it is read; the refusal does not
/// depend on it.
#[test]
fn a_call_under_a_lambda_is_refused() {
    assert_call_refused(
        &boxed(
            "cr6gdlam",
            CLAUSES,
            "  operation go() -> Int64 =\n    let f = lambda b -> Box.open(b)\n    f(Box.mk(4))",
        ),
        "Box.open",
    );
}

/// A constant's value is computed by the same evaluator.
#[test]
fn a_call_in_a_const_is_refused() {
    assert_call_refused(
        &boxed(
            "cr6gdconst",
            CLAUSES,
            "  const c: Int64 = Box.open(Box.mk(4))",
        ),
        "Box.open",
    );
}

/// A guard of a `match` is a value the arm is chosen by, not a goal.
#[test]
fn a_call_in_a_match_guard_is_refused() {
    assert_call_refused(
        &boxed(
            "cr6gdguard",
            CLAUSES,
            "  operation go(b: Box) -> Int64 =\n    match b\n      case mk(v: n) | Box.full(b) -> n\n      case _ -> 0",
        ),
        "Box.full",
    );
}

/// An operation a namespace declares is the namespace's own, as a data sort's is its sort's.
#[test]
fn a_namespaces_operation_is_refused() {
    assert_call_refused(
        &boxed(
            "cr6gdns",
            "",
            "  operation open(b: Box) -> Int64\n  rule open(Box.mk(v: ?v), ?v) :- true\n  operation go() -> Int64 = open(Box.mk(4))",
        ),
        "test.cr6gdns.open",
    );
}

/// `lib.<ns>.Box[V]`: the same sort with a parameter. Its body-less operation is the
/// sort's own all the same (WI-20261011-RM247), so the call is typed down another path.
fn boxed_in(ns: &str, outside: &str) -> String {
    format!(
        "namespace lib.{ns}\n  import anthill.prelude.{{Int64, Bool}}\n  sort Box\n    sort V = ?\n    entity mk(v: V)\n    operation open(b: Box[V]) -> V\n    rule open(mk(v: ?v), ?v) :- true\n  end\nend\nnamespace test.{ns}\n  import anthill.prelude.Int64\n  import lib.{ns}.Box\n{outside}\nend\n"
    )
}

#[test]
fn a_parametric_sorts_operation_is_refused() {
    assert_call_refused(
        &boxed_in("cr6gdpar", "  operation go() -> Int64 = Box.open(Box.mk(4))"),
        "Box.open",
    );
}

#[test]
fn a_caller_generic_in_the_content_is_refused() {
    assert_call_refused(
        &boxed_in(
            "cr6gdgen",
            "  operation at[X](b: Box[V = X]) -> X = Box.open(b)\n  operation go() -> Int64 = at(Box.mk(4))",
        ),
        "Box.open",
    );
}

// ── a rule body is not judged ───────────────────────────────────────────────
//
// A rule body is relational. The same spelling there is a goal, or a term kept as data,
// and each of these answers as it did. The first cut of this change refused them: the
// plain sort's rows by a check of every data slot, the parametric sort's by the call's
// own check asked without `in_rule_body`.

/// A term is matched against a head that names the operation: nothing is called.
#[test]
fn a_term_kept_as_data_is_matched_against_a_head() {
    let mut kb = load_kb_with(&boxed(
        "cr6gdterm",
        CLAUSES,
        "  rule un(Box.open(?b), ?b) :- true\n  rule r(?x) :- un(Box.open(Box.mk(4)), ?b), ?b <=> Box.mk(v: ?x)",
    ));
    let r = query_unary(&mut kb, "test.cr6gdterm.r");
    assert!(matches!(r.as_slice(), [(Value::Int(4), true)]), "{r:?}");
}

/// The same term of a parametric sort, which IS handed to the typer where it stands.
#[test]
fn a_parametric_sorts_term_kept_as_data_is_matched() {
    let mut kb = load_kb_with(&boxed_in(
        "cr6gdtermp",
        "  rule un(Box.open(?b), ?b) :- true\n  rule r(?x) :- un(Box.open(Box.mk(4)), ?b), ?b <=> Box.mk(v: ?x)",
    ));
    let r = query_unary(&mut kb, "test.cr6gdtermp.r");
    assert!(matches!(r.as_slice(), [(Value::Int(4), true)]), "{r:?}");
}

/// A goal handed to a predicate as data is called there, and the clauses answer it.
#[test]
fn a_goal_passed_as_data_is_still_called() {
    let mut kb = load_kb_with(&boxed(
        "cr6gdmeta",
        CLAUSES,
        "  rule call1(?g) :- ?g\n  rule high(?x) :- ?x <=> 1, call1(Box.full(Box.mk(4)))\n  rule low(?x) :- ?x <=> 1, call1(Box.full(Box.mk(1)))",
    ));
    let high = query_unary(&mut kb, "test.cr6gdmeta.high");
    assert!(matches!(high.as_slice(), [(Value::Int(1), true)]), "{high:?}");
    let low = query_unary(&mut kb, "test.cr6gdmeta.low");
    assert!(low.is_empty(), "{low:?}");
}

/// A call where a rule body needs its VALUE does not run, and the goal waits, as it did:
/// one answer, conditional. That it says nothing is not this change's.
#[test]
fn a_call_in_a_rule_bodys_value_position_waits_as_it_did() {
    let mut kb = load_kb_with(&boxed_in(
        "cr6gdwait",
        "  rule w(?x) :- ?x <=> Box.open(Box.mk(4))",
    ));
    let w = query_unary(&mut kb, "test.cr6gdwait.w");
    assert!(matches!(w.as_slice(), [(_, false)]), "{w:?}");
}

/// A lambda written in a rule body is typed as a unit, with the rule body's reading.
/// What such a rule answers is not this change's; that it loads is.
#[test]
fn a_lambda_in_a_rule_body_is_not_judged() {
    let errs = load_errors_of(&boxed(
        "cr6gdrlam",
        CLAUSES,
        "  rule allm(?b, ?f) :- ?f(?b)\n  rule r(?x) :- ?x <=> 1, allm(Box.mk(4), lambda (b) -> Box.full(b))",
    ));
    assert!(errs.is_empty(), "{errs:?}");
}

// ── the goal is not a call ──────────────────────────────────────────────────

/// The ticket's two rule-body rows: the value at arity + 1, the predicate at its own.
#[test]
fn the_goal_answers_through_the_clauses() {
    let mut kb = load_kb_with(&boxed(
        "cr6gdgoal",
        CLAUSES,
        "  rule r(?x) :- Box.open(Box.mk(4), ?x)\n  rule held(?x) :- ?x <=> 1, Box.full(Box.mk(4))\n  rule low(?x) :- ?x <=> 1, Box.full(Box.mk(1))",
    ));
    let r = query_unary(&mut kb, "test.cr6gdgoal.r");
    assert!(matches!(r.as_slice(), [(Value::Int(4), true)]), "{r:?}");
    let held = query_unary(&mut kb, "test.cr6gdgoal.held");
    assert!(matches!(held.as_slice(), [(Value::Int(1), true)]), "{held:?}");
    let low = query_unary(&mut kb, "test.cr6gdgoal.low");
    assert!(low.is_empty(), "{low:?}");
}

/// A parametric sort's goal IS handed to the typer, as the call of its operation is, and
/// is told from a call by where it stands.
#[test]
fn a_parametric_sorts_goal_answers() {
    let mut kb = load_kb_with(&boxed_in(
        "cr6gdparg",
        "  rule r(?x) :- Box.open(Box.mk(4), ?x)",
    ));
    let r = query_unary(&mut kb, "test.cr6gdparg.r");
    assert!(matches!(r.as_slice(), [(Value::Int(4), true)]), "{r:?}");
}

/// A goal under negation and in a branch of a disjunction is a goal, not an argument.
#[test]
fn a_goal_under_a_connective_is_still_a_goal() {
    let mut kb = load_kb_with(&boxed(
        "cr6gdconn",
        CLAUSES,
        "  rule none(?x) :- ?x <=> 1, not(Box.full(Box.mk(1)))\n  rule some(?x) :- ?x <=> 1, not(Box.full(Box.mk(4)))\n  rule alt(?x) :- ?x <=> 1, (Box.full(Box.mk(1)) | Box.full(Box.mk(9)))",
    ));
    let none = query_unary(&mut kb, "test.cr6gdconn.none");
    assert!(matches!(none.as_slice(), [(Value::Int(1), true)]), "{none:?}");
    let some = query_unary(&mut kb, "test.cr6gdconn.some");
    assert!(some.is_empty(), "{some:?}");
    let alt = query_unary(&mut kb, "test.cr6gdconn.alt");
    assert!(matches!(alt.as_slice(), [(Value::Int(1), true)]), "{alt:?}");
}

// ── what a call does run ────────────────────────────────────────────────────

/// A carrier's `eq` written as clauses is run by proving them — the one such operation.
/// Called by name from an operation body, and through `=`.
#[test]
fn a_carriers_eq_written_as_clauses_still_runs() {
    let src = "namespace test.cr6gdeq\n  import anthill.prelude.{Int64, Bool, PartialEq, Eq}\n  sort Color\n    entity red\n    entity blue\n    operation ceq(a: Color, b: Color) -> Bool\n    rule ceq(red, red) :- true\n    rule ceq(blue, blue) :- true\n    provides PartialEq[T = Color, eq = ceq]\n    provides Eq[T = Color]\n  end\n  import test.cr6gdeq.Color.{red, blue}\n  operation same() -> Int64 = if Color.ceq(red, red) then 1 else 0\n  operation other() -> Int64 = if Color.ceq(red, blue) then 1 else 0\n  operation infix() -> Int64 = if red = blue then 1 else 0\nend\n";
    assert_runs(src, "test.cr6gdeq.same", 1);
    assert_runs(src, "test.cr6gdeq.other", 0);
    assert_runs(src, "test.cr6gdeq.infix", 0);
}

/// An equation that defines the operation replaces the call before it is judged; the
/// clauses beside it still answer the goal.
#[test]
fn an_equation_beside_the_clauses_defines_the_call() {
    let src = boxed(
        "cr6gdsimp",
        "    operation peek(b: Box) -> Int64 = b.v\n    operation open(b: Box) -> Int64\n    rule open(?b) <=> peek(?b) @[simp]\n    rule open(mk(v: ?v), ?v) :- true",
        "  operation go() -> Int64 = Box.open(Box.mk(4))\n  rule r(?x) :- Box.open(Box.mk(4), ?x)",
    );
    assert_runs(&src, "test.cr6gdsimp.go", 4);
    let mut kb = load_kb_with(&src);
    let r = query_unary(&mut kb, "test.cr6gdsimp.r");
    assert!(matches!(r.as_slice(), [(Value::Int(4), true)]), "{r:?}");
}

/// A sort with no constructor may be provided, and a call written against it runs the
/// member the provider supplies, whatever clauses the sort writes under its own operation.
#[test]
fn a_provided_sorts_operation_is_the_providers() {
    let src = "namespace test.cr6gdprov\n  import anthill.prelude.Int64\n  sort Shape\n    sort T = ?\n    operation area(s: T) -> Int64\n    rule area(?s, 7) :- true\n  end\n  sort Sq\n    entity sq(n: Int64)\n    provides Shape[T = Sq]\n    operation area(s: Sq) -> Int64 = 9\n  end\n  operation go() -> Int64 = Shape.area(Sq.sq(1))\nend\n";
    assert_runs(src, "test.cr6gdprov.go", 9);
}

/// A clause under an operation that has a body is a lemma about it (§8.6), and the call
/// runs the body.
#[test]
fn a_bodied_operation_with_a_lemma_under_it_is_still_called() {
    assert_runs(
        &boxed(
            "cr6gdlem",
            "    operation size(b: Box) -> Int64 = b.v\n    rule size(mk(v: 0)) :- true",
            "  operation go() -> Int64 = Box.size(Box.mk(4))",
        ),
        "test.cr6gdlem.go",
        4,
    );
}

// ── the repairs the refusal advises ─────────────────────────────────────────

/// "Give the operation a body." Its goal at arity + 1 is then derived from the body.
#[test]
fn the_advised_body_runs() {
    let src = boxed(
        "cr6gdbody",
        "    operation open(b: Box) -> Int64 = b.v",
        "  operation go() -> Int64 = Box.open(Box.mk(4))\n  rule r(?x) :- Box.open(Box.mk(4), ?x)",
    );
    assert_runs(&src, "test.cr6gdbody.go", 4);
    let mut kb = load_kb_with(&src);
    let r = query_unary(&mut kb, "test.cr6gdbody.r");
    assert!(matches!(r.as_slice(), [(Value::Int(4), true)]), "{r:?}");
}

/// "Write them as a rule alone — no `operation` line, a variable for each head argument —
/// and cite the rule as a relation." Applying it binds the first column; the row that is
/// left carries the result, read here by the filter that keeps it and the one that drops it.
/// The search is the relation's, and its `Error` effect is the caller's to declare.
#[test]
fn the_advised_rule_alone_is_cited_as_a_relation() {
    // In the sort, with nothing declared; and in a namespace, with its columns typed.
    let in_sort = boxed(
        "cr6gdrel",
        "    rule open(?b, ?v) :- ?b <=> mk(v: ?v)",
        "  operation rows() -> Int64 effects {Error} = length(Box.open(Box.mk(4)).takeN(5))\n  operation four() -> Int64 effects {Error} = length(Box.open(Box.mk(4)).where(lambda r -> r.v = 4).takeN(5))\n  operation five() -> Int64 effects {Error} = length(Box.open(Box.mk(4)).where(lambda r -> r.v = 5).takeN(5))",
    );
    assert_runs(&in_sort, "test.cr6gdrel.rows", 1);
    assert_runs(&in_sort, "test.cr6gdrel.four", 1);
    assert_runs(&in_sort, "test.cr6gdrel.five", 0);
    let in_namespace = boxed(
        "cr6gdreln",
        "",
        "  rule open(?b: Box, ?v: Int64) :- ?b <=> Box.mk(v: ?v)\n  operation four() -> Int64 effects {Error} = length(open(Box.mk(4)).where(lambda r -> r.v = 4).takeN(5))\n  operation five() -> Int64 effects {Error} = length(open(Box.mk(4)).where(lambda r -> r.v = 5).takeN(5))",
    );
    assert_runs(&in_namespace, "test.cr6gdreln.four", 1);
    assert_runs(&in_namespace, "test.cr6gdreln.five", 0);
}

/// The same repair for a predicate: with every column bound the relation has a row where
/// the predicate holds and none where it does not.
#[test]
fn the_advised_predicate_alone_is_cited_as_a_relation() {
    let src = boxed(
        "cr6gdrelp",
        "    rule full(?b) :- ?b <=> mk(v: ?v), ?v > 3",
        "  operation high() -> Int64 effects {Error} = length(Box.full(Box.mk(4)).takeN(5))\n  operation low() -> Int64 effects {Error} = length(Box.full(Box.mk(1)).takeN(5))",
    );
    assert_runs(&src, "test.cr6gdrelp.high", 1);
    assert_runs(&src, "test.cr6gdrelp.low", 0);
}

// ── the message at run time ─────────────────────────────────────────────────

/// A host that enters the operation directly is past the load's refusal. It is told what
/// the operation is — defined, by clauses a call does not run — and not that it has none.
#[test]
fn a_host_entry_is_told_the_operation_is_defined_by_clauses() {
    let mut interp = interp_for(
        "namespace test.cr6gdhost\n  import anthill.prelude.Int64\n  operation four() -> Int64\n  rule four(4) :- true\nend\n",
    );
    let err = interp
        .call("test.cr6gdhost.four", &[])
        .expect_err("nothing runs a call of it");
    let msg = err.to_string();
    assert!(msg.contains("operation has no body: test.cr6gdhost.four"), "{msg}");
    assert!(msg.contains("defined by the clauses indexed under it"), "{msg}");
    assert!(!msg.contains("no rule clause"), "{msg}");
    assert!(!msg.contains("No clause is indexed"), "{msg}");
}

/// The other side of that message: no clause, and it says so apart from what a call runs.
#[test]
fn an_operation_with_nothing_is_told_it_has_no_clause() {
    let mut interp = interp_for(
        "namespace test.cr6gdnone\n  import anthill.prelude.Int64\n  operation ping() -> Int64\nend\n",
    );
    let err = interp
        .call("test.cr6gdnone.ping", &[])
        .expect_err("nothing defines it");
    let msg = err.to_string();
    assert!(msg.contains("operation has no body: test.cr6gdnone.ping"), "{msg}");
    assert!(msg.contains("No clause is indexed under it either"), "{msg}");
    assert!(!msg.contains("defined by the clauses"), "{msg}");
}

// ── a constructor written with positional arguments ─────────────────────────

/// `lib.<ns>` with a one-field `Box`, a two-field `Pair` and an `Outer` that holds one,
/// each with an operation defined by an equation over its constructor's NAMED pattern;
/// `outside` is written in `test.<ns>`.
fn shaped(ns: &str, outside: &str) -> String {
    format!(
        "namespace lib.{ns}\n  import anthill.prelude.{{Int64, Bool}}\n  sort Box\n    entity mk(v: Int64)\n    operation open(b: Box) -> Int64\n    rule open(mk(v: ?v)) <=> ?v @[simp]\n  end\n  sort Pair\n    entity pair(a: Int64, b: Int64)\n    operation first(p: Pair) -> Int64\n    rule first(pair(a: ?a, b: ?b)) <=> ?a @[simp]\n    rule big(pair(a: ?a, b: ?b)) :- ?a > 3\n  end\n  sort Outer\n    entity wrap(p: Pair, n: Int64)\n    operation inner(o: Outer) -> Int64\n    rule inner(wrap(p: pair(a: ?a, b: ?b), n: ?n)) <=> ?b @[simp]\n  end\nend\nnamespace test.{ns}\n  import anthill.prelude.{{Int64, Bool}}\n  import lib.{ns}.{{Box, Pair, Outer}}\n{outside}\nend\n"
    )
}

/// The program the equation advice ran into: the constructor written as most are.
#[test]
fn an_equation_fires_on_a_positional_constructor() {
    assert_runs(
        &shaped("cr6gdpos", "  operation go() -> Int64 = Box.open(Box.mk(4))"),
        "test.cr6gdpos.go",
        4,
    );
}

/// The left-hand side written positionally is the same pattern: the load names its field.
#[test]
fn an_equation_written_positionally_fires_too() {
    let src = "namespace test.cr6gdposl\n  import anthill.prelude.Int64\n  sort Box\n    entity mk(v: Int64)\n    operation open(b: Box) -> Int64\n    rule open(mk(?v)) <=> ?v @[simp]\n  end\n  operation go() -> Int64 = Box.open(Box.mk(4))\nend\n";
    assert_runs(src, "test.cr6gdposl.go", 4);
}

/// The rank rule, on both mixed spellings: a positional argument takes the first
/// declared field that no named argument took — `pair(2, a: 7)` puts 2 in `b`.
#[test]
fn a_positional_argument_takes_the_field_no_name_took() {
    let src = shaped(
        "cr6gdmix",
        "  operation both() -> Int64 = Pair.first(Pair.pair(7, 2))\n  operation tail() -> Int64 = Pair.first(Pair.pair(7, b: 2))\n  operation lead() -> Int64 = Pair.first(Pair.pair(2, a: 7))",
    );
    assert_runs(&src, "test.cr6gdmix.both", 7);
    assert_runs(&src, "test.cr6gdmix.tail", 7);
    assert_runs(&src, "test.cr6gdmix.lead", 7);
}

#[test]
fn a_positional_constructor_under_another_is_read_too() {
    assert_runs(
        &shaped(
            "cr6gdnest",
            "  operation go() -> Int64 = Outer.inner(Outer.wrap(Pair.pair(7, 2), 9))",
        ),
        "test.cr6gdnest.go",
        2,
    );
}

#[test]
fn an_imported_constructor_name_is_read_too() {
    assert_runs(
        &shaped(
            "cr6gdbare",
            "  import lib.cr6gdbare.Pair.{pair}\n  operation go() -> Int64 = Pair.first(pair(7, 2))",
        ),
        "test.cr6gdbare.go",
        7,
    );
}

/// A sort with a parameter, and the standard library's own: `some(6)` is how nearly
/// every `Option` in an operation body is written.
#[test]
fn a_parametric_sorts_constructor_is_read_too() {
    let src = "namespace test.cr6gdgen\n  import anthill.prelude.{Int64, Option}\n  import anthill.prelude.Option.{some}\n  sort Gen\n    sort V = ?\n    entity g(v: V)\n    operation un(x: Gen[V]) -> V\n    rule un(g(v: ?v)) <=> ?v @[simp]\n  end\n  operation unopt(o: Option[T = Int64]) -> Int64\n  rule unopt(some(?x)) <=> ?x @[simp]\n  operation own() -> Int64 = Gen.un(Gen.g(5))\n  operation std() -> Int64 = unopt(some(6))\nend\n";
    assert_runs(src, "test.cr6gdgen.own", 5);
    assert_runs(src, "test.cr6gdgen.std", 6);
}

/// The other reader: the argument's term twin, which a call-site precondition is proved
/// over. The clause's head names the fields; the call does not.
#[test]
fn a_precondition_is_proved_at_a_positional_constructor() {
    let src = shaped(
        "cr6gdpre",
        "  operation need(p: Pair) -> Int64\n    requires Pair.big(p)\n  = p.a\n  operation go() -> Int64 = need(Pair.pair(7, 2))\n  operation mixed() -> Int64 = need(Pair.pair(2, a: 7))",
    );
    assert_runs(&src, "test.cr6gdpre.go", 7);
    assert_runs(&src, "test.cr6gdpre.mixed", 7);
}

/// …and where the fact does not hold the call is still refused, for the fact: the clause
/// is named as it was judged, in the canonical form.
#[test]
fn a_precondition_that_does_not_hold_is_still_refused() {
    let errs = load_errors_of(&shaped(
        "cr6gdpren",
        "  operation need(p: Pair) -> Int64\n    requires Pair.big(p)\n  = p.a\n  operation go() -> Int64 = need(Pair.pair(1, 2))",
    ));
    assert_refused_naming(&errs, &["need.requires", "big("], "a precondition that fails");
}

/// The spelling that always matched.
#[test]
fn the_named_spelling_fires_as_it_did() {
    let src = shaped(
        "cr6gdnamed",
        "  operation one() -> Int64 = Box.open(Box.mk(v: 4))\n  operation two() -> Int64 = Pair.first(Pair.pair(a: 7, b: 2))",
    );
    assert_runs(&src, "test.cr6gdnamed.one", 4);
    assert_runs(&src, "test.cr6gdnamed.two", 7);
}
