//! WI-20261017-JRHZ0 — `anthill.prelude.todo() -> Nothing`, THE BODY OF AN OPERATION NOT
//! WRITTEN YET (kernel-language.md §5.4, *An operation not written yet has the body
//! `todo()`*; the user's decisions 2026-10-17).
//!
//! WI-20260909-M8QWJ refuses an operation nothing can run, so a signature-only stub needs a
//! body, and its fixtures were given SELF-CALLS — `stub(x) = stub(x)` — which loop for ever
//! when called: tail recursion is O(1) frames and the suites set no step cap. MEASURED: such
//! a stub called from `anthill run` ran 60 s until killed, where before M8QWJ it died
//! "operation has no body" at once. `todo()` is a body for any signature, because `Nothing`
//! conforms to every type, and reaching it is a fault:
//!
//!   * a call faults with `EvalError::NotImplemented`, naming the operation whose body
//!     called it — a tail call too, though a tail call may replace its frame, and for a
//!     lambda the operation that wrote it, not the one that applied it;
//!   * outside every effect row, so `Error.reify` does not catch it;
//!   * from a rule body, a FAULT of the goal (`BridgeDisposition::Fault`) — reported, and
//!     the answer never definite — not a refutation;
//!   * the program loads clean, with no warning, and what does not reach the hole runs.
//!
//! The C++ backend's refusal is `anthill-cpp-gen/tests/unsupported_test.rs`
//! (`a_todo_body_is_refused_naming_its_operation`).
//!
//! BACKED OUT, MEASURED (2026-10-17), one at a time: `prelude_todo` raising
//! `EvalError::Internal` instead reds the six rows about the fault
//! (`a_call_that_reaches_todo_faults_naming_its_operation`,
//! `a_tail_call_of_a_hole_names_the_operation_that_holds_it`,
//! `a_hole_in_a_lambda_names_the_operation_that_wrote_it`,
//! `no_error_boundary_catches_a_hole`, `a_rule_body_goal_over_a_hole_is_a_reported_fault`,
//! `the_disposition_of_a_hole_is_a_fault`); `NotImplemented` moved to
//! `BridgeDisposition::Schedule` reds `a_rule_body_goal_over_a_hole_is_a_reported_fault` and
//! `the_disposition_of_a_hole_is_a_fault`, the other six green; a closure frame given
//! its caller's `op` again (`enter_closure`, the pre-ticket rule) reds
//! `a_hole_in_a_lambda_names_the_operation_that_wrote_it` alone.
//!
//! PASS EITHER WAY, BY DESIGN: `todo_is_a_body_for_every_signature_shape` (a typing claim
//! `Nothing` already made true; it is here so a change to the bottom sort's conformance
//! reds it), `an_unimported_todo_is_refused` (the prelude is not implicit, WI-909), and
//! the controls inside the rows — the part of a program that does not reach the hole runs,
//! and `Error.reify` still catches a real raise.

use anthill_core::eval::{BridgeDisposition, EvalError, Value};
use anthill_core::kb::resolve::ResolveConfig;

use crate::common::{interp_for, load_errors_of, load_kb_with, load_outcome};

const RUN: &str = r#"
namespace jr.run
  import anthill.prelude.{Int64, todo}

  operation stub(x: Int64) -> Int64 = todo()
  operation tail() -> Int64 = stub(1)
  operation nested() -> Int64 = stub(1) + 1
  operation fine() -> Int64 = 7
end
"#;

#[track_caller]
fn assert_not_implemented(result: Result<Value, EvalError>, running: &str, why: &str) {
    match result {
        Err(EvalError::NotImplemented { running: Some(op) }) if op == running => {}
        other => panic!("{why}: expected NotImplemented naming `{running}`, got {other:?}"),
    }
}

#[test]
fn a_call_that_reaches_todo_faults_naming_its_operation() {
    let mut interp = interp_for(RUN);
    let result = interp.call("jr.run.nested", &[]);
    let rendered = match &result {
        Err(e) => e.to_string(),
        Ok(v) => panic!("a call through the hole returned {v:?}"),
    };
    assert_not_implemented(result, "jr.run.stub", "a non-tail call of the hole");
    assert_eq!(rendered, "not implemented: `jr.run.stub` reached `todo()`");
    // CONTROL: the hole is only where it is reached — the rest of the program runs.
    assert!(matches!(interp.call("jr.run.fine", &[]), Ok(Value::Int(7))));
}

#[test]
fn a_tail_call_of_a_hole_names_the_operation_that_holds_it() {
    let mut interp = interp_for(RUN);
    // `tail`'s call of `stub` and `stub`'s of `todo` are both in tail position: a frame
    // a tail call replaces must still leave the holder on top when the builtin runs.
    assert_not_implemented(
        interp.call("jr.run.tail", &[]),
        "jr.run.stub",
        "a tail call of the hole",
    );
}

/// A lambda's frame reports the operation that WROTE the lambda (`Closure::written_in`),
/// a lambda nested in another included — not `apply1`, which applies both. Before, a
/// closure frame took its caller's `op`, and the hole named `jr.lam.apply1`.
#[test]
fn a_hole_in_a_lambda_names_the_operation_that_wrote_it() {
    let mut interp = interp_for(
        r#"
namespace jr.lam
  import anthill.prelude.{Int64, todo}

  operation apply1(f: (x: Int64) -> Int64, x: Int64) -> Int64 = f(x)
  operation writer() -> Int64 = apply1(lambda (x: Int64) -> todo(), 1)
  operation nested() -> Int64 =
    apply1(lambda (x: Int64) -> apply1(lambda (x: Int64) -> todo(), x), 1)
end
"#,
    );
    assert_not_implemented(interp.call("jr.lam.writer", &[]), "jr.lam.writer", "a lambda");
    assert_not_implemented(
        interp.call("jr.lam.nested", &[]),
        "jr.lam.nested",
        "a lambda written inside a lambda",
    );
}

/// The hole is not a domain failure, so no `Error` boundary is a place for it to go: a
/// thunk that both raises and reaches a hole has its raise caught and its hole passed on.
#[test]
fn no_error_boundary_catches_a_hole() {
    let mut interp = interp_for(
        r#"
namespace jr.reify
  import anthill.prelude.{Int64, String, Bool, Error, Result, todo}
  import anthill.prelude.Result.{ok, err}

  operation stub(x: Int64) -> Int64 = todo()
  operation risky(b: Bool) -> Int64 effects Error[String] =
    if b then Error.raise("boom") else stub(1)
  operation guarded(b: Bool) -> Int64 =
    match Error.reify(lambda () -> risky(b))
      case ok(v) -> v
      case err(e) -> 42
  operation raised() -> Int64 = guarded(true)
  operation holed() -> Int64 = guarded(false)
end
"#,
    );
    // CONTROL: the boundary is live — it catches the raise.
    assert!(
        matches!(interp.call("jr.reify.raised", &[]), Ok(Value::Int(42))),
        "Error.reify must catch a real raise"
    );
    assert_not_implemented(
        interp.call("jr.reify.holed", &[]),
        "jr.reify.stub",
        "a hole inside an Error.reify thunk",
    );
}

#[test]
fn a_rule_body_goal_over_a_hole_is_a_reported_fault() {
    let mut kb = load_kb_with(
        r#"
namespace jr.rule
  import anthill.prelude.{Int64, todo}

  operation stub(x: Int64) -> Int64 = todo()
  rule r(?x) :- ?x = stub(1)
end
"#,
    );
    let goal = crate::common::query_pattern_term(&mut kb, "jr.rule.r(?x)");
    let (sols, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    let errors: Vec<String> = stats.errors.iter().map(|e| e.message.clone()).collect();
    assert!(
        errors
            .iter()
            .any(|e| e.contains("`jr.rule.stub` reached `todo()`")),
        "the goal's fault must name the hole's holder; got {errors:?}"
    );
    // NOT A REFUTATION: the clause stays, as one answer conditional on the goal the call
    // could not reduce — dropped, it would read as `r` holding of nothing.
    assert_eq!(sols.len(), 1, "the clause is kept, not refuted");
    assert!(
        !sols[0].is_definite(),
        "and its answer is not definite — the call never returned a value"
    );
}

#[test]
fn the_disposition_of_a_hole_is_a_fault() {
    let mut interp = interp_for(RUN);
    let err = interp
        .call("jr.run.stub", &[Value::Int(1)])
        .expect_err("the hole has no value");
    assert!(matches!(err, EvalError::NotImplemented { .. }), "{err:?}");
    assert_eq!(err.bridge_disposition(interp.kb()), BridgeDisposition::Fault);
}

/// Every awkward shape M8QWJ's migration met — an operation's own type parameter, a
/// return-only variable, an open row, a `requires`, an arrow and a named tuple result, a
/// member of a parametric sort, a declared effect — and the load says nothing.
#[test]
fn todo_is_a_body_for_every_signature_shape() {
    let warnings = load_outcome(
        r#"
namespace jr.shapes
  import anthill.prelude.{Int64, String, List, Stream, Eq, Cell, Modify, todo}

  operation a(x: Int64) -> Int64 = todo()
  operation b[A](x: A) -> A = todo()
  operation c() -> List[T = ?A] = todo()
  operation d() -> Stream[T = Int64, E = ?E] = todo()
  operation e() -> List[T = ?C] requires Eq[T = ?C] = todo()
  operation f(g: (Int64) -> Int64) -> (Int64) -> Int64 = todo()
  operation h(x: Int64) -> (a: Int64, b: String) = todo()
  operation m(c: Cell[V = Int64]) -> Int64 effects Modify[c] = todo()

  sort Box
    sort V = ?
    entity box(v: V)
    operation open(h: Box[V]) -> V = todo()
  end
end
"#,
    )
    .rendered_warnings()
    .expect("every shape loads");
    assert!(warnings.is_empty(), "a hole loads without a warning: {warnings:#?}");
}

#[test]
fn an_unimported_todo_is_refused() {
    let errs = load_errors_of(
        "namespace jr.noimp\n  import anthill.prelude.{Int64}\n  \
         operation stub(x: Int64) -> Int64 = todo()\nend\n",
    );
    crate::common::assert_refused_naming(
        &errs,
        &["todo", "import the namespace that declares"],
        "`todo` is a prelude name like any other",
    );
}
