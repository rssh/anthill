//! WI-20261011-3HN0N — a tuple, a set or a list on the right-hand side of a `@[simp]`
//! equation is the value the same text builds in an operation body
//! (kernel-language.md §5.3).
//!
//! THE RULE. A rule's text keeps a collection literal as the node a clause is matched on;
//! an operation body writes the same text as a constructor over the literal's entity, and
//! that is the node the typer checks against an expected type and eval constructs. A fired
//! equation puts a rule's text into an operation body, so the typer reads the
//! literal there as the constructor and the typed body keeps it
//! (`typing::literal_as_constructor`). The text written as an operation body is, is an
//! operation's body, a const's value, and what stands under a compound expression of a
//! rule body — a lambda, an `if`, a `let`, a `match`: the loader builds the three with
//! one walk. A rule body's own term stays the rule's text.
//!
//! BEFORE. `operation both(a: Int64) -> (Int64, Int64)` with `rule both(?a) <=> (?a, ?a)
//! @[simp]` loaded clean and every call died in eval, `internal evaluator error: unhandled
//! Expr variant`. The same for a set (`<=> {?a, 5}`) and for a list its position does not
//! lower to a spine. An empty tuple did not get that far: it was typed as a tuple of no
//! components where the body-written `()` was the sort `Unit`, and the load was refused.
//! Since WI-20261011-7G99A `Unit` is the tuple of no components, so the two nodes are typed
//! alike.
//!
//! EVERY ROW HAS ITS OWN SOURCE: a row that shares a fixture with another measures the
//! fixture.
//!
//! CONTROLS — measured with the reading backed out of `visit_type`, again on the tree of
//! WI-20261011-7G99A.
//!
//!   FAIL, each loading clean and dying in eval on the literal's node:
//!     a_positional_tuple_on_the_right_hand_side_runs
//!     a_named_tuple_on_the_right_hand_side_runs
//!     a_tuple_under_a_constructor_runs
//!     a_distributed_projection_is_the_body_written_value
//!     a_set_on_the_right_hand_side_is_the_body_written_set
//!     a_list_named_by_its_constructor_is_the_body_written_list
//!     a_list_where_another_collection_is_declared_is_the_body_written_list
//!     a_tuple_handed_to_a_call_on_the_right_hand_side_runs
//!     a_const_holds_a_rewritten_tuple
//!     a_sorts_equation_reached_by_a_dot_runs
//!     a_generic_operations_tuple_runs
//!     a_lambda_in_an_operation_body_returns_a_rewritten_tuple
//!     a_lambda_with_an_untyped_binder_returns_a_rewritten_tuple
//!     a_match_guard_reads_a_rewritten_tuple
//!     a_match_arm_reads_a_rewritten_tuple
//!   FAIL, the query dying where the resolver hands the lambda to eval:
//!     a_lambda_in_a_rule_body_returns_a_rewritten_tuple
//!     a_lambda_with_an_untyped_binder_in_a_rule_body_returns_a_rewritten_tuple
//!     a_lambda_in_a_rule_body_reaches_a_sorts_equation
//!
//!   PASS with the change backed out, by design — what it must not move:
//!     the_tuple_written_in_the_operations_body_runs
//!     a_list_lowered_to_its_spine_is_the_body_written_list — a rule's text holds it as
//!       the spine's constructors applied, which eval already constructs
//!     a_tuple_a_rule_body_writes_is_an_argument_as_before
//!     a_lambda_a_rule_body_writes_returns_its_own_tuple — the loader builds what stands
//!       under a lambda as it builds an operation body
//!     a_tuple_in_a_goal_is_matched_as_written
//!     a_rule_bodys_own_empty_tuple_is_unit — both nodes type `()` as `Unit`
//!   PASS either way since 7G99A, which made `()` `Unit` on either node and a tuple one
//!   value on either carrier:
//!     an_empty_tuple_on_the_right_hand_side_is_unit
//!     a_lambda_in_a_rule_body_returns_the_unit_an_equation_leaves
//!     a_rewritten_positional_tuple_is_the_body_written_value — with the reading backed
//!       out, eval hands the literal's node back, and it reads as the tuple the body
//!       builds; the rows that read a component are the control
//!     a_rewritten_named_tuple_is_the_body_written_value — likewise
//!     a_rewritten_tuple_under_a_constructor_is_the_body_written_value — likewise
//!     a_tuple_in_a_tuple_is_the_body_written_value — likewise
//!     a_tuple_named_by_its_constructor_is_the_body_written_value — likewise
//!     a_tuple_a_guard_took_from_a_fact_runs — likewise
//!     a_tuple_a_guard_built_runs — likewise
//!   PASS either way already on 7G99A's parent:
//!     a_rewritten_tuple_is_destructured_by_a_pattern
//!     a_set_in_a_field_is_the_body_written_set
//!     an_if_condition_reads_a_rewritten_tuple
//!     the_components_of_a_rewritten_tuple_keep_their_order
//!
//!   THE RULE BODY'S OWN TERM. The reading stops at the rule's own term — measured with
//!   it made everywhere the typer meets the node. FAIL:
//!     wi285_unrec_test::collection_literal_frames_assemble_types — the type is no longer
//!       on the node the rule wrote
//!   Every other row of this file passes either way (re-measured on 7G99A's tree; the
//!   workspace was measured with the reading's change).
//!
//!   NOT A ROW. The C++ generator lowers the literal's node as it lowers the constructor:
//!   a header generated for a sort whose operation calls `both` is the same text before
//!   and after, `return {4, 4};`.

use anthill_core::eval::{self, Interpreter, Value};
use anthill_core::kb::term_view::views_structurally_equal;

use crate::common::{load_kb_with, query_unary, run_int64};

/// `test.<name>`, holding `body`, with the prelude names the rows use.
fn ns(name: &str, body: &str) -> String {
    format!(
        "namespace test.{name}\n  import anthill.prelude.{{Int64, Bool, Option, List, Set, Stream, Function, Unit}}\n  import anthill.prelude.Option.{{some, none}}\n{body}\nend\n"
    )
}

/// The operation the ticket is about, and a reader of its value.
const BOTH: &str = "  operation both(a: Int64) -> (Int64, Int64)\n  rule both(?a) <=> (?a, ?a) @[simp]\n  operation fstof(p: (Int64, Int64)) -> Int64 = p._1\n";

#[track_caller]
fn assert_runs(src: &str, entry: &str, expected: i64) {
    assert_eq!(run_int64(src, entry), Ok(expected), "{entry}");
}

/// `test.<name>.go` calls the operation an equation defines and `test.<name>.gotwin` the
/// one whose body writes the same text: both run, and to one value.
#[track_caller]
fn assert_the_body_written_value(name: &str, src: &str) {
    let mut interp = Interpreter::new(load_kb_with(src));
    eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    let rewritten = interp
        .call(&format!("test.{name}.go"), &[])
        .unwrap_or_else(|e| panic!("the equation's value: {e:?}"));
    let written = interp
        .call(&format!("test.{name}.gotwin"), &[])
        .unwrap_or_else(|e| panic!("the body-written value: {e:?}"));
    assert!(
        views_structurally_equal(interp.kb(), &rewritten, &written),
        "the equation gives {rewritten:?}, the body {written:?}"
    );
}

#[track_caller]
fn assert_answers_four(src: &str, rule: &str) {
    let mut kb = load_kb_with(src);
    let answers = query_unary(&mut kb, rule);
    assert!(
        matches!(answers.as_slice(), [(Value::Int(4), true)]),
        "{rule}: {answers:?}"
    );
}

// ── the three programs of the ticket ────────────────────────────────────────

#[test]
fn a_positional_tuple_on_the_right_hand_side_runs() {
    assert_runs(
        &ns("hn0npos", &format!("{BOTH}  operation go() -> Int64 = fstof(both(4))")),
        "test.hn0npos.go",
        4,
    );
}

#[test]
fn a_named_tuple_on_the_right_hand_side_runs() {
    assert_runs(
        &ns(
            "hn0nnamed",
            "  operation both(a: Int64) -> (x: Int64, y: Int64)\n  rule both(?a) <=> (x: ?a, y: ?a) @[simp]\n  operation fstof(p: (x: Int64, y: Int64)) -> Int64 = p.x\n  operation go() -> Int64 = fstof(both(4))",
        ),
        "test.hn0nnamed.go",
        4,
    );
}

#[test]
fn a_tuple_under_a_constructor_runs() {
    assert_runs(
        &ns(
            "hn0nunder",
            "  operation both(a: Int64) -> Option[T = (Int64, Int64)]\n  rule both(?a) <=> some((?a, ?a)) @[simp]\n  operation go() -> Int64 =\n    match both(4)\n      case some(p) -> p._1\n      case none -> 0",
        ),
        "test.hn0nunder.go",
        4,
    );
}

/// The twin the ticket measured: the tuple written in the operation's own body.
#[test]
fn the_tuple_written_in_the_operations_body_runs() {
    assert_runs(
        &ns(
            "hn0ntwin",
            "  operation both(a: Int64) -> (Int64, Int64) = (a, a)\n  operation fstof(p: (Int64, Int64)) -> Int64 = p._1\n  operation go() -> Int64 = fstof(both(4))",
        ),
        "test.hn0ntwin.go",
        4,
    );
}

// ── the value is the one the body-written text builds ───────────────────────

#[test]
fn a_rewritten_positional_tuple_is_the_body_written_value() {
    assert_the_body_written_value(
        "hn0nvpos",
        &ns(
            "hn0nvpos",
            "  operation both(a: Int64) -> (Int64, Int64)\n  rule both(?a) <=> (?a, 5) @[simp]\n  operation twin(a: Int64) -> (Int64, Int64) = (a, 5)\n  operation go() -> (Int64, Int64) = both(4)\n  operation gotwin() -> (Int64, Int64) = twin(4)",
        ),
    );
}

/// The order of a positional tuple's components is its identity: each is read where it
/// was written, by its label and by a pattern.
#[test]
fn the_components_of_a_rewritten_tuple_keep_their_order() {
    assert_runs(
        &ns(
            "hn0norder",
            "  operation both(a: Int64) -> (Int64, Int64)\n  rule both(?a) <=> (?a, 1) @[simp]\n  operation go() -> Int64 =\n    let p = both(5)\n    let q = both(9)\n    match q\n      case (x, y) -> (p._1 - p._2) * 10 + (x - y) - 44",
        ),
        "test.hn0norder.go",
        4,
    );
}

/// A tuple written by its constructor's name carries its components positionally, in a
/// rule's own term and in an operation body.
#[test]
fn a_tuple_named_by_its_constructor_is_the_body_written_value() {
    assert_the_body_written_value(
        "hn0nvname",
        "namespace test.hn0nvname\n  import anthill.prelude.Int64\n  import anthill.reflect.TupleLiteral\n  operation both(a: Int64) -> (Int64, Int64)\n  rule both(?a) <=> TupleLiteral(?a, 5) @[simp]\n  operation twin(a: Int64) -> (Int64, Int64) = TupleLiteral(a, 5)\n  operation go() -> (Int64, Int64) = both(4)\n  operation gotwin() -> (Int64, Int64) = twin(4)\nend\n",
    );
}

#[test]
fn a_rewritten_named_tuple_is_the_body_written_value() {
    assert_the_body_written_value(
        "hn0nvnamed",
        &ns(
            "hn0nvnamed",
            "  operation both(a: Int64) -> (x: Int64, y: Int64)\n  rule both(?a) <=> (x: ?a, y: 5) @[simp]\n  operation twin(a: Int64) -> (x: Int64, y: Int64) = (x: a, y: 5)\n  operation go() -> (x: Int64, y: Int64) = both(4)\n  operation gotwin() -> (x: Int64, y: Int64) = twin(4)",
        ),
    );
}

#[test]
fn a_rewritten_tuple_under_a_constructor_is_the_body_written_value() {
    assert_the_body_written_value(
        "hn0nvunder",
        &ns(
            "hn0nvunder",
            "  operation both(a: Int64) -> Option[T = (Int64, Int64)]\n  rule both(?a) <=> some((?a, 5)) @[simp]\n  operation twin(a: Int64) -> Option[T = (Int64, Int64)] = some((a, 5))\n  operation go() -> Option[T = (Int64, Int64)] = both(4)\n  operation gotwin() -> Option[T = (Int64, Int64)] = twin(4)",
        ),
    );
}

#[test]
fn a_tuple_in_a_tuple_is_the_body_written_value() {
    assert_the_body_written_value(
        "hn0nvnest",
        &ns(
            "hn0nvnest",
            "  operation both(a: Int64) -> ((Int64, Int64), Int64)\n  rule both(?a) <=> ((?a, 5), ?a) @[simp]\n  operation twin(a: Int64) -> ((Int64, Int64), Int64) = ((a, 5), a)\n  operation go() -> ((Int64, Int64), Int64) = both(4)\n  operation gotwin() -> ((Int64, Int64), Int64) = twin(4)",
        ),
    );
}

/// `()` in an operation body is `Unit`, and so is the one an equation leaves there. The
/// load was refused: the literal's node was typed as a tuple of no components.
#[test]
fn an_empty_tuple_on_the_right_hand_side_is_unit() {
    assert_the_body_written_value(
        "hn0nvunit",
        &ns(
            "hn0nvunit",
            "  operation both(a: Int64) -> Unit\n  rule both(?a) <=> () @[simp]\n  operation twin(a: Int64) -> Unit = ()\n  operation go() -> Unit = both(4)\n  operation gotwin() -> Unit = twin(4)",
        ),
    );
}

/// `?p.(x, y)` is the tuple of the two fields, in a rule's text as in an operation body.
#[test]
fn a_distributed_projection_is_the_body_written_value() {
    assert_the_body_written_value(
        "hn0nvproj",
        "namespace test.hn0nvproj\n  import anthill.prelude.Int64\n  sort P\n    entity mk(x: Int64, y: Int64)\n  end\n  operation both(p: P) -> (x: Int64, y: Int64)\n  rule both(?p) <=> ?p.(x, y) @[simp]\n  operation twin(p: P) -> (x: Int64, y: Int64) = p.(x, y)\n  operation go() -> (x: Int64, y: Int64) = both(P.mk(4, 5))\n  operation gotwin() -> (x: Int64, y: Int64) = twin(P.mk(4, 5))\nend\n",
    );
}

// ── the other two literals ──────────────────────────────────────────────────

/// A set literal keeps one of each element, here as in an operation body.
#[test]
fn a_set_on_the_right_hand_side_is_the_body_written_set() {
    assert_the_body_written_value(
        "hn0nvset",
        &ns(
            "hn0nvset",
            "  operation both(a: Int64) -> Set[T = Int64]\n  rule both(?a) <=> {?a, 5, ?a} @[simp]\n  operation twin(a: Int64) -> Set[T = Int64] = {a, 5, a}\n  operation go() -> Set[T = Int64] = both(4)\n  operation gotwin() -> Set[T = Int64] = twin(4)",
        ),
    );
}

#[test]
fn a_set_in_a_field_is_the_body_written_set() {
    assert_the_body_written_value(
        "hn0nvsetf",
        "namespace test.hn0nvsetf\n  import anthill.prelude.{Int64, Set}\n  sort H\n    entity holder(s: Set[T = Int64])\n  end\n  operation both(a: Int64) -> H\n  rule both(?a) <=> H.holder({?a, 5}) @[simp]\n  operation twin(a: Int64) -> H = H.holder({a, 5})\n  operation go() -> H = both(4)\n  operation gotwin() -> H = twin(4)\nend\n",
    );
}

/// A list written by its constructor's name is not lowered to the spine in a rule's text.
#[test]
fn a_list_named_by_its_constructor_is_the_body_written_list() {
    assert_the_body_written_value(
        "hn0nvlistn",
        "namespace test.hn0nvlistn\n  import anthill.prelude.{Int64, List}\n  import anthill.reflect.ListLiteral\n  operation both(a: Int64) -> List[T = Int64]\n  rule both(?a) <=> ListLiteral(?a, 5) @[simp]\n  operation twin(a: Int64) -> List[T = Int64] = ListLiteral(a, 5)\n  operation go() -> List[T = Int64] = both(4)\n  operation gotwin() -> List[T = Int64] = twin(4)\nend\n",
    );
}

/// Nor is a `[…]` in a position that declares another collection (§4.6).
#[test]
fn a_list_where_another_collection_is_declared_is_the_body_written_list() {
    assert_the_body_written_value(
        "hn0nvlists",
        "namespace test.hn0nvlists\n  import anthill.prelude.{Int64, Stream}\n  sort H\n    entity holder(s: Stream[T = Int64])\n  end\n  operation both(a: Int64) -> H\n  rule both(?a) <=> H.holder([?a, 5]) @[simp]\n  operation twin(a: Int64) -> H = H.holder([a, 5])\n  operation go() -> H = both(4)\n  operation gotwin() -> H = twin(4)\nend\n",
    );
}

/// A `[…]` with no such declaration is the spine in a rule's text, and ran before.
#[test]
fn a_list_lowered_to_its_spine_is_the_body_written_list() {
    assert_the_body_written_value(
        "hn0nvlist",
        &ns(
            "hn0nvlist",
            "  operation both(a: Int64) -> List[T = Int64]\n  rule both(?a) <=> [?a, 5] @[simp]\n  operation twin(a: Int64) -> List[T = Int64] = [a, 5]\n  operation go() -> List[T = Int64] = both(4)\n  operation gotwin() -> List[T = Int64] = twin(4)",
        ),
    );
}

// ── every place the rewritten call stands ───────────────────────────────────

#[test]
fn a_tuple_handed_to_a_call_on_the_right_hand_side_runs() {
    assert_runs(
        &ns(
            "hn0narg",
            "  operation fstof(p: (Int64, Int64)) -> Int64 = p._1\n  operation first(a: Int64) -> Int64\n  rule first(?a) <=> fstof((?a, 0)) @[simp]\n  operation go() -> Int64 = first(4)",
        ),
        "test.hn0narg.go",
        4,
    );
}

#[test]
fn a_rewritten_tuple_is_destructured_by_a_pattern() {
    assert_runs(
        &ns(
            "hn0npat",
            "  operation both(a: Int64) -> (Int64, Int64)\n  rule both(?a) <=> (?a, 1) @[simp]\n  operation go() -> Int64 =\n    match both(3)\n      case (x, y) -> x + y",
        ),
        "test.hn0npat.go",
        4,
    );
}

#[test]
fn a_const_holds_a_rewritten_tuple() {
    assert_runs(
        &ns(
            "hn0nconst",
            &format!("{BOTH}  const c: (Int64, Int64) = both(4)\n  operation go() -> Int64 = c._1"),
        ),
        "test.hn0nconst.go",
        4,
    );
}

#[test]
fn a_sorts_equation_reached_by_a_dot_runs() {
    assert_runs(
        "namespace test.hn0ndot\n  import anthill.prelude.Int64\n  sort Box\n    entity mk(v: Int64)\n    operation pair(b: Box) -> (Int64, Int64)\n    rule pair(?b) <=> (?b.v, ?b.v) @[simp]\n  end\n  operation go() -> Int64 =\n    let b = Box.mk(4)\n    let p = b.pair()\n    p._1\nend\n",
        "test.hn0ndot.go",
        4,
    );
}

#[test]
fn a_generic_operations_tuple_runs() {
    assert_runs(
        &ns(
            "hn0ngen",
            "  operation both[T](a: T) -> (T, T)\n  rule both(?a) <=> (?a, ?a) @[simp]\n  operation go() -> Int64 =\n    let p = both(4)\n    p._1",
        ),
        "test.hn0ngen.go",
        4,
    );
}

#[test]
fn a_lambda_in_an_operation_body_returns_a_rewritten_tuple() {
    assert_runs(
        &ns(
            "hn0nlam",
            &format!("{BOTH}  operation go() -> Int64 =\n    let f = lambda (y: Int64) -> both(y)\n    let p = f(4)\n    p._1"),
        ),
        "test.hn0nlam.go",
        4,
    );
}

#[test]
fn a_lambda_with_an_untyped_binder_returns_a_rewritten_tuple() {
    assert_runs(
        &ns(
            "hn0nlamu",
            &format!("{BOTH}  operation app(f: Function[A = Int64, B = (Int64, Int64)], a: Int64) -> Int64 =\n    let p = f(a)\n    p._1\n  operation go() -> Int64 = app(lambda y -> both(y), 4)"),
        ),
        "test.hn0nlamu.go",
        4,
    );
}

#[test]
fn an_if_condition_reads_a_rewritten_tuple() {
    assert_runs(
        &ns(
            "hn0nif",
            &format!("{BOTH}  operation go() -> Int64 = if fstof(both(4)) > 3 then 4 else 0"),
        ),
        "test.hn0nif.go",
        4,
    );
}

#[test]
fn a_match_guard_reads_a_rewritten_tuple() {
    assert_runs(
        &ns(
            "hn0nguard",
            &format!("{BOTH}  operation go() -> Int64 =\n    match 4\n      case x | fstof(both(x)) > 3 -> x\n      case _ -> 0"),
        ),
        "test.hn0nguard.go",
        4,
    );
}

#[test]
fn a_match_arm_reads_a_rewritten_tuple() {
    assert_runs(
        &ns(
            "hn0narm",
            &format!("{BOTH}  operation go() -> Int64 =\n    match 4\n      case x ->\n        let p = both(x)\n        p._2"),
        ),
        "test.hn0narm.go",
        4,
    );
}

// ── a tuple the equation's guard bound ──────────────────────────────────────

/// The right-hand side is a variable, and what the guard bound it to is a fact's tuple:
/// a rule's text, arriving through the binding and not through the equation's own text.
#[test]
fn a_tuple_a_guard_took_from_a_fact_runs() {
    assert_the_body_written_value(
        "hn0nvfact",
        &ns(
            "hn0nvfact",
            "  rule pairof(4, (4, 5)) :- true\n  operation both(a: Int64) -> (Int64, Int64)\n  rule bg: both(?a) = ?p :- pairof(?a, ?p) @[simp]\n  operation twin(a: Int64) -> (Int64, Int64) = (a, 5)\n  operation go() -> (Int64, Int64) = both(4)\n  operation gotwin() -> (Int64, Int64) = twin(4)",
        ),
    );
}

#[test]
fn a_tuple_a_guard_built_runs() {
    assert_the_body_written_value(
        "hn0nvguard",
        &ns(
            "hn0nvguard",
            "  operation both(a: Int64) -> (Int64, Int64)\n  rule bg: both(?a) = ?p :- ?p <=> (?a, 5) @[simp]\n  operation twin(a: Int64) -> (Int64, Int64) = (a, 5)\n  operation go() -> (Int64, Int64) = both(4)\n  operation gotwin() -> (Int64, Int64) = twin(4)",
        ),
    );
}

// ── a rule body ─────────────────────────────────────────────────────────────

/// What stands under a lambda is evaluated, in a rule body too: the equation fires there
/// where the rule is loaded, and eval runs what it left.
#[test]
fn a_lambda_in_a_rule_body_returns_a_rewritten_tuple() {
    assert_answers_four(
        &ns(
            "hn0nrlam",
            &format!("{BOTH}  operation app(f: Function[A = Int64, B = (Int64, Int64)], a: Int64) -> Int64 =\n    let p = f(a)\n    p._1\n  rule value(?r) :- ?r <=> app(lambda (y: Int64) -> both(y), 4)"),
        ),
        "test.hn0nrlam.value",
    );
}

/// The binder has no written type: the lambda is typed where the call's slot is read.
#[test]
fn a_lambda_with_an_untyped_binder_in_a_rule_body_returns_a_rewritten_tuple() {
    assert_answers_four(
        &ns(
            "hn0nrlamu",
            &format!("{BOTH}  operation app(f: Function[A = Int64, B = (Int64, Int64)], a: Int64) -> Int64 =\n    let p = f(a)\n    p._1\n  rule value(?r) :- ?r <=> app(lambda y -> both(y), 4)"),
        ),
        "test.hn0nrlamu.value",
    );
}

/// The text under a lambda of a rule body is typed as an operation body is: the `()` an
/// equation leaves there is `Unit`. The rule was refused at load, the lambda typed
/// `Int64 -> ()`.
#[test]
fn a_lambda_in_a_rule_body_returns_the_unit_an_equation_leaves() {
    assert_answers_four(
        "namespace test.hn0nrunitl\n  import anthill.prelude.{Int64, Unit, Function}\n  sort Box\n    entity mk(v: Int64)\n    operation nothing(b: Box) -> Unit\n    rule nothing(?b) <=> () @[simp]\n  end\n  operation appu(f: Function[A = Int64, B = Unit], a: Int64) -> Int64 =\n    let u = f(a)\n    a\n  rule value(?r) :- ?r <=> appu(lambda (y: Int64) -> Box.mk(y).nothing(), 4)\nend\n",
        "test.hn0nrunitl.value",
    );
}

#[test]
fn a_lambda_in_a_rule_body_reaches_a_sorts_equation() {
    assert_answers_four(
        "namespace test.hn0nrsort\n  import anthill.prelude.{Int64, Function}\n  sort Box\n    entity mk(v: Int64)\n    operation pair(b: Box) -> (Int64, Int64)\n    rule pair(?b) <=> (?b.v, ?b.v) @[simp]\n  end\n  operation app(f: Function[A = Int64, B = (Int64, Int64)], a: Int64) -> Int64 =\n    let p = f(a)\n    p._1\n  rule value(?r) :- ?r <=> app(lambda (y: Int64) -> Box.pair(Box.mk(y)), 4)\nend\n",
        "test.hn0nrsort.value",
    );
}

/// A tuple a rule body writes as a call's argument is the rule's own term.
#[test]
fn a_tuple_a_rule_body_writes_is_an_argument_as_before() {
    assert_answers_four(
        &ns(
            "hn0nrarg",
            "  operation fstof(p: (Int64, Int64)) -> Int64 = p._1\n  rule value(?r) :- ?r <=> fstof((4, 5))",
        ),
        "test.hn0nrarg.value",
    );
}

#[test]
fn a_lambda_a_rule_body_writes_returns_its_own_tuple() {
    assert_answers_four(
        &ns(
            "hn0nrown",
            "  operation app(f: Function[A = Int64, B = (Int64, Int64)], a: Int64) -> Int64 =\n    let p = f(a)\n    p._1\n  rule value(?r) :- ?r <=> app(lambda (y: Int64) -> (y, y), 4)",
        ),
        "test.hn0nrown.value",
    );
}

/// A tuple in a goal is matched against the facts as it is written: under an entity, the
/// atom the typer checks, and under a plain relation, the one it does not.
#[test]
fn a_tuple_in_a_goal_is_matched_as_written() {
    let src = "namespace test.hn0nrgoal\n  import anthill.prelude.Int64\n  sort Held\n    entity held(p: (Int64, Int64))\n  end\n  fact Held.held(p: (4, 5))\n  fact kept((4, 5))\n  rule value(?r) :- Held.held(p: (?r, 5))\n  rule other(?r) :- kept((?r, 5))\n  rule none(?r) :- Held.held(p: (5, ?r))\nend\n";
    assert_answers_four(src, "test.hn0nrgoal.value");
    assert_answers_four(src, "test.hn0nrgoal.other");
    let mut kb = load_kb_with(src);
    let none = query_unary(&mut kb, "test.hn0nrgoal.none");
    assert!(none.is_empty(), "{none:?}");
}

/// `()` written in a goal is the rule's own term, and a tuple of no components: `Unit`, as
/// the body-written `()` is. It meets the `Unit` field of the fact it matches.
#[test]
fn a_rule_bodys_own_empty_tuple_is_unit() {
    assert_answers_four(
        "namespace test.hn0nrunit\n  import anthill.prelude.{Int64, Unit}\n  sort U\n    entity u(v: Unit, n: Int64)\n  end\n  fact U.u(v: (), n: 4)\n  rule value(?r) :- U.u(v: (), n: ?r)\nend\n",
        "test.hn0nrunit.value",
    );
}
