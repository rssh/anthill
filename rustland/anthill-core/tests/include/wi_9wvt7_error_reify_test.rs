//! WI-20260908-9WVT7 / proposal 027.4 — `Error.reify` and `Result`: anthill code
//! CATCHING a raise, end to end.
//!
//! Before this, nothing in the language could catch anything — measured, no operation
//! anywhere in `stdlib/anthill/` reified an effect, so every operation declaring
//! `effects Error` was uncatchable from anthill. This file drives the whole layer:
//! `Error.reify(lambda () -> …)` runs a thunk behind a boundary frame, a raise inside it
//! aborts THERE and arrives as `err(payload)`, and the payload is read back AS A VALUE.
//!
//! WHY EVERY ROW HERE RUNS. `match` arms are not checked against the scrutinee's sort —
//! measured, `operation f(b: Boom) -> Int64 = match b case other(n) -> n`, where `other`
//! belongs to an unrelated sort, LOADS CLEAN. So an acceptance that only destructures the
//! recovered payload proves nothing at load time. Each test below calls the operation and
//! asserts the value that comes back.
//!
//! WHAT FAILS WHEN THE BOUNDARY IS BACKED OUT — MEASURED, by disabling the
//! `AwaitState::ReifyBoundary` dispatch arm in `dispatch_resolved_operation` so
//! `Error.reify` falls through to the ordinary routes: 8 failed, 2 passed. Every row
//! that CALLS `reify` dies `OperationBodyMissing { name: "anthill.prelude.Error.reify" }`
//! — the declaration has no body and no builtin, which is exactly why the boundary
//! cannot be either.
//!
//! PASS EITHER WAY BY DESIGN, and each is here for a different reason:
//!
//!   * `a_row_without_error_is_still_refused` measures the TYPER — the discharge is in
//!     the SIGNATURE (WI-329) and needs no runtime. It is what stops a future change
//!     that catches at run time while quietly ceasing to discharge at load time.
//!   * `an_unreified_raise_still_escapes` measures that `reify` is the ONLY thing that
//!     catches: the layer must not have turned every raise into a value.
//!
//! `a_non_raised_error_is_not_caught` is a control of the third kind — it fails under
//! the back-out too (its `reify` call is gone with the rest), so it does not separate
//! the boundary from nothing. What it separates is the boundary from a WIDER one: it
//! goes red the moment recovery accepts anything but `EvalError::Raised`, which no
//! other row here would notice.

use anthill_core::eval::{EvalError, Interpreter, Value};

/// The whole fixture. One program, driven by many entry points, so the tests share a
/// single stdlib load per `interp_for` rather than each paying for its own dialect of
/// the same three declarations.
const PROGRAM: &str = r#"
namespace test.reify
  import anthill.prelude.Result
  import anthill.prelude.Result.{ok, err}
  import anthill.prelude.{Int64, String, Error, Result, List}
  import anthill.prelude.List.{cons, nil}
  import anthill.reflect.{KB, LoadFailed}

  sort Boom
    entity boom(why: String)
  end

  -- The raiser. Its row DECLARES its payload, which is what lets a typed `reify`
  -- accept it: a body that does not say what it raises cannot be reified into a
  -- typed `Result` soundly (027.4 §"A bare label").
  operation mayFail(n: Int64) -> Int64 effects {Error[Boom]} =
    if n < 0 then Error.raise(boom("negative")) else n + 1

  -- THE ACCEPTANCE. `caught` declares NO effects: the label is discharged by the
  -- boundary, not passed to the caller.
  operation caught() -> Result[E = Boom, T = Int64] =
    Error.reify(lambda () -> mayFail(0 - 1))

  -- Control (c) of the ticket: a body that does not raise returns the `ok` arm.
  -- Its row still MENTIONS `Error[Boom]` — statically it may raise, dynamically it
  -- does not — which is what the boundary is asked to tell apart.
  operation returned() -> Result[E = Boom, T = Int64] =
    Error.reify(lambda () -> mayFail(41))

  -- The recovered value destructured IN ANTHILL, which is a different claim from
  -- reading the entity from Rust: it says the boundary built a value whose SHAPE IS
  -- ITS IDENTITY, matching what the constructor syntax builds (WI-20260827-T2470).
  operation describe(r: Result[E = Boom, T = Int64]) -> String =
    match r
      case ok(_)  -> "ok"
      case err(e) -> match e
                       case boom(w) -> w

  operation caughtWhy() -> String = describe(caught())
  operation returnedTag() -> String = describe(returned())

  -- Control (a): the same call OUTSIDE a boundary still raises. Note it must
  -- DECLARE the effect — which is the load-time half of the same control.
  operation uncaught() -> Int64 effects {Error[Boom]} = mayFail(0 - 1)

  -- NESTING. `innerRecovers` holds a boundary of its own, so while the outer thunk
  -- runs there are two on the stack. The inner one must win.
  operation innerRecovers() -> Int64 =
    match Error.reify(lambda () -> mayFail(0 - 1))
      case ok(v)  -> v
      case err(_) -> 7

  operation nestedInnerWins() -> Result[E = Boom, T = Int64] =
    Error.reify(lambda () -> mayFail(innerRecovers()))

  operation nestedOuterCatches() -> Result[E = Boom, T = Int64] =
    Error.reify(lambda () -> mayFail(0 - 1 - innerRecovers()))

  -- THE MONAD LAYER, which is what separates this from a try/catch: the caught
  -- value is data, so it maps. All three witnesses of the `provides` are driven —
  -- `map`, `flatMap` and `pure` — because a witness no test calls keeps passing
  -- when its body regresses to resolving at nothing.
  --
  -- `pure` is spelled `resultPure[P = Boom](…)` and not through a receiver, for the
  -- reason the `provides` names it explicitly: `Monad.pure` is RESULT-DETERMINED —
  -- it has no `Result` argument to dispatch on — so there is nothing to dot-dispatch
  -- from. `P` is written because it reaches no argument either, and the expected
  -- type does not propagate into a lambda's body; `Option`'s `optionPure[A](a: A)`
  -- never provokes it only because `Option` has one parameter, not two.
  operation mappedOk() -> Result[E = Boom, T = Int64] =
    Error.reify(lambda () -> mayFail(41)).map(lambda (x: Int64) -> x * 2)

  operation mappedErr() -> Result[E = Boom, T = Int64] =
    Error.reify(lambda () -> mayFail(0 - 1)).map(lambda (x: Int64) -> x * 2)

  operation flatMappedOk() -> Result[E = Boom, T = Int64] =
    Error.reify(lambda () -> mayFail(41)).flatMap(lambda (x: Int64) -> Result.resultPure[P = Boom](x * 2))

  operation flatMappedErr() -> Result[E = Boom, T = Int64] =
    Error.reify(lambda () -> mayFail(0 - 1)).flatMap(lambda (x: Int64) -> Result.resultPure[P = Boom](x * 2))

  -- THE ISOMORPHISM. `Result.reflect` puts the value back into the effect channel;
  -- reifying that again must return the same `err`.
  operation reifiedReflect() -> Result[E = Boom, T = Int64] =
    Error.reify(lambda () -> Result.reflect(caught()))

  -- THE DRIVER 027.4 NAMES. `KB.loaded` loads candidate source into a discardable
  -- layer and raises `load_failed(diagnostics)`; a checker's whole job is to catch
  -- that and report them. It is the reason the effect is worth having, and it is
  -- catchable only because its row was retyped from bare `Error` to
  -- `Error[LoadFailed]` — a typed `reify` refuses a body that does not say what it
  -- raises.
  --
  -- THE DIAGNOSTICS ARE THE ANSWER, WHICH IS WHY THIS CARRIES THE PROSE. Each one is
  -- already located and already names the CHECK that ran and what it wanted — that is
  -- what a repair loop feeds back to a model. A checker that answered a COUNT would
  -- prove a list of the right length arrived and nothing about its content, and a
  -- model reading "1" learns nothing about what to fix.
  operation firstDiagnostic(ds: List[T = String]) -> String =
    match ds
      case nil()      -> "load failed with no diagnostics"
      case cons(d, _) -> d

  operation checkSource(src: String) -> String =
    match Error.reify(lambda () -> KB.loaded(cons(src, nil)))
      case ok(_)  -> "loaded"
      case err(e) -> match e
                       case load_failed(ds) -> firstDiagnostic(ds)

  operation goodSource() -> String = checkSource("namespace ok.one end")
  operation unparsableSource() -> String = checkSource("namespace broken.")
  operation illTypedSource() -> String =
    checkSource("namespace u.x  operation f(n: Int64) -> String = n  end")

  -- NAME CAPTURE. A parameter merely NAMED `reify`, holding something callable.
  -- `dispatch_call_with_requirements_inner`'s local lookup matches by SHORT NAME,
  -- so before the fix this parameter captured the qualified `Error.reify(...)`
  -- below and `runIt` ran in the boundary's place.
  operation runIt(t: () -> Int64 @ {Error[Boom]}) -> Result[E = Boom, T = Int64] = ok(999)

  operation shadowed(reify: (() -> Int64 @ {Error[Boom]}) -> Result[E = Boom, T = Int64])
      -> Result[E = Boom, T = Int64] =
    Error.reify(lambda () -> mayFail(0 - 1))

  operation shadowTest() -> Result[E = Boom, T = Int64] = shadowed(runIt)

  -- Unbounded non-tail recursion, for the depth-cap control. `Error[Boom]` is in the
  -- row only so a `reify` will accept it as a body.
  operation deep(n: Int64) -> Int64 effects {Error[Boom]} =
    if n < 0 then Error.raise(boom("negative")) else deep(n + 1) + 1

  operation deepInsideBoundary() -> Result[E = Boom, T = Int64] =
    Error.reify(lambda () -> deep(0))
end
"#;

fn interp() -> Interpreter {
    crate::common::interp_for(PROGRAM)
}

#[track_caller]
fn short_name(interp: &Interpreter, v: &Value) -> String {
    let sym = crate::common::entity_functor(interp.kb(), v)
        .unwrap_or_else(|| panic!("expected an entity, got {v:?}"));
    let qn = interp.kb().qualified_name_of(sym);
    qn.rsplit('.').next().unwrap_or(&qn).to_string()
}

#[track_caller]
fn field(interp: &Interpreter, v: &Value, name: &str, rank: usize) -> Value {
    crate::common::entity_field(interp.kb(), v, name, rank)
}

#[track_caller]
fn int_of(interp: &Interpreter, v: &Value) -> i64 {
    crate::common::scalar_int(interp.kb(), v)
        .unwrap_or_else(|| panic!("expected an Int64 leaf, got {v:?}"))
}

#[track_caller]
fn str_of(interp: &Interpreter, v: &Value) -> String {
    crate::common::scalar_str(interp.kb(), v)
        .unwrap_or_else(|| panic!("expected a String leaf, got {v:?}"))
}

/// The recovered payload's `why` — asserted through the `err` arm, so a test that
/// reads it has proved the boundary put the RAISED value there and not, say, a
/// same-shaped default.
#[track_caller]
fn err_why(interp: &Interpreter, result: &Value) -> String {
    assert_eq!(short_name(interp, result), "err", "expected the err arm");
    let payload = field(interp, result, "error", 0);
    assert_eq!(short_name(interp, &payload), "boom");
    str_of(interp, &field(interp, &payload, "why", 0))
}

#[track_caller]
fn ok_value(interp: &Interpreter, result: &Value) -> i64 {
    assert_eq!(short_name(interp, result), "ok", "expected the ok arm");
    int_of(interp, &field(interp, result, "value", 0))
}

/// THE ACCEPTANCE. A raise inside the boundary is caught there and arrives as
/// `err(boom("negative"))` — the payload the raiser built, read back as a value.
#[test]
fn a_raise_inside_the_boundary_becomes_the_err_arm() {
    let mut interp = interp();
    let r = interp
        .call("test.reify.caught", &[])
        .expect("a raise inside a reify boundary is caught, not propagated");
    assert_eq!(err_why(&interp, &r), "negative");
}

/// Control (c). The same operation, the same declared row, no raise at run time:
/// the boundary must deliver `ok(42)` rather than treat "may raise" as "did".
#[test]
fn a_body_that_does_not_raise_becomes_the_ok_arm() {
    let mut interp = interp();
    let r = interp
        .call("test.reify.returned", &[])
        .expect("a body that does not raise returns normally");
    assert_eq!(ok_value(&interp, &r), 42);
}

/// The boundary-built value is destructured BY ANTHILL, which reading it from Rust
/// does not establish: `case err(e)` matching means the boundary produced the same
/// canonical entity shape `err(x)` written in source produces — the positional→named
/// desugar plus declared-field canonicalization (WI-20260827-T2470). Build it by hand
/// instead of through `finish_constructor` and this row is where it shows.
#[test]
fn anthill_destructures_the_recovered_result() {
    let mut interp = interp();
    let why = interp
        .call("test.reify.caughtWhy", &[])
        .expect("the err arm destructures in anthill");
    assert_eq!(str_of(&interp, &why), "negative");

    let tag = interp
        .call("test.reify.returnedTag", &[])
        .expect("the ok arm destructures in anthill");
    assert_eq!(str_of(&interp, &tag), "ok");
}

/// Control (a). Outside a boundary the very same call still raises, and the payload
/// still reaches the host — so the boundary is what catches, not some new default.
///
/// PASSES EITHER WAY under a back-out of the boundary — MEASURED. It is the row that
/// says the layer did not turn every raise into a value.
#[test]
fn an_unreified_raise_still_escapes() {
    let mut interp = interp();
    let err = interp
        .call("test.reify.uncaught", &[])
        .expect_err("a raise outside every boundary propagates");
    match err {
        EvalError::Raised { payload } => {
            assert_eq!(short_name(&interp, &payload), "boom");
            assert_eq!(str_of(&interp, &field(&interp, &payload, "why", 0)), "negative");
        }
        other => panic!("expected EvalError::Raised, got {other:?}"),
    }
}

/// Nesting, and the direction that separates "innermost" from "any": with two
/// boundaries live, the inner one catches. `innerRecovers` answers 7, so the outer
/// thunk computes `mayFail(7) = 8` and the outer boundary sees a normal return.
///
/// If the outer boundary caught instead, this would be `err(boom("negative"))` —
/// which is exactly the second row's expectation, so the two together pin the choice
/// rather than one of them passing by luck.
#[test]
fn the_innermost_boundary_catches() {
    let mut interp = interp();
    let r = interp
        .call("test.reify.nestedInnerWins", &[])
        .expect("the inner boundary catches, the outer returns normally");
    assert_eq!(ok_value(&interp, &r), 8);
}

/// The other direction: a boundary that has already answered does not linger. The
/// inner `reify` completes (returning 7), and the raise that happens AFTER it must
/// find the outer boundary — not a stale inner one, and not nothing at all.
#[test]
fn a_completed_boundary_does_not_catch_a_later_raise() {
    let mut interp = interp();
    let r = interp
        .call("test.reify.nestedOuterCatches", &[])
        .expect("the outer boundary catches what the inner one no longer can");
    assert_eq!(err_why(&interp, &r), "negative");
}

/// THE MONAD LAYER. `reify` hands back a `Result`, so the caught computation is
/// ordinary data: `map` runs on the `ok` arm and short-circuits on `err`, preserving
/// the payload. That is the difference between a monad layer and a try/catch, and it
/// is `Result`'s `provides Monad[M = Result[E = E], …]` dispatching on a
/// boundary-built receiver.
#[test]
fn the_reified_result_is_a_monad() {
    let mut interp = interp();
    let ok = interp
        .call("test.reify.mappedOk", &[])
        .expect("map over a reified ok");
    assert_eq!(ok_value(&interp, &ok), 84);

    let bad = interp
        .call("test.reify.mappedErr", &[])
        .expect("map over a reified err short-circuits");
    assert_eq!(err_why(&interp, &bad), "negative");

    // `flatMap` and `pure` — the other two witnesses of the same `provides`. Driven
    // here and nowhere else in the tree: without these two rows, a regression that
    // left `resultFlatMap` / `resultPure` resolving at nothing would keep the suite
    // green, since `map` alone is what the boundary tests exercise.
    let chained = interp
        .call("test.reify.flatMappedOk", &[])
        .expect("flatMap over a reified ok, through pure");
    assert_eq!(ok_value(&interp, &chained), 84);

    let short = interp
        .call("test.reify.flatMappedErr", &[])
        .expect("flatMap over a reified err short-circuits");
    assert_eq!(err_why(&interp, &short), "negative");
}

/// THE ISOMORPHISM (047 §3). `Result.reflect` injects a `Result` back into the effect
/// channel — `err(e)` becomes `Error.raise(e)` — so reifying a reflect returns the
/// value it started from. Round-tripping is what makes `raise`/`reify` a pair rather
/// than a one-way catch.
#[test]
fn reify_of_reflect_returns_the_same_result() {
    let mut interp = interp();
    let r = interp
        .call("test.reify.reifiedReflect", &[])
        .expect("reflect raises inside the boundary and is caught again");
    assert_eq!(err_why(&interp, &r), "negative");
}

/// THE DRIVER, END TO END, AND THE REASON THE LAYER EXISTS: a scoped load's
/// diagnostics caught IN ANTHILL. `anthill.reflect.KB.loaded` raises
/// `load_failed(diagnostics)`; before this, the guardians example's `LoadChecker.check`
/// was host-bound Rust for exactly one irreducible reason — its
/// `Err(e) => load_failure_to_rejected(interp, e)` arm — and this is that arm, written
/// in anthill.
///
/// It is also what the `KB.loaded` RETYPE bought. With the row left as a bare `Error`,
/// this program does not load at all: measured, "the lambda argument declares `Error`,
/// which the closed row does not admit" — a typed `reify` refuses a body that does not
/// say what it raises. So this row fails under a back-out of the retype at LOAD time,
/// not at run time, which is the whole point of the retype.
#[test]
fn a_scoped_loads_diagnostics_are_caught_in_anthill() {
    let mut interp = interp();
    let good = interp
        .call("test.reify.goodSource", &[])
        .expect("a source that loads takes the ok arm");
    assert_eq!(
        str_of(&interp, &good),
        "loaded",
        "a candidate that loads must reach `ok`, not `err`"
    );

    // A PARSE failure: located, and it says WHICH candidate — a checker handed several
    // sources needs that to attribute the failure, and a model needs it to find the line.
    let unparsable = interp
        .call("test.reify.unparsableSource", &[])
        .expect("a source that does NOT parse is caught, not propagated");
    let unparsable = str_of(&interp, &unparsable);
    for want in ["source 0", "1:1", "syntax error", "namespace broken."] {
        assert!(
            unparsable.contains(want),
            "the caught diagnostic must carry `{want}`, got: {unparsable}"
        );
    }

    // A TYPE failure, which is the shape that makes the payload worth catching: it names
    // the CHECK that ran (`f.return (op-return)`) and both sides of what it wanted. That
    // is a repair instruction, not a verdict — and it is what a COUNT would have thrown
    // away.
    let ill_typed = interp
        .call("test.reify.illTypedSource", &[])
        .expect("a source that does not TYPE is caught the same way");
    let ill_typed = str_of(&interp, &ill_typed);
    for want in ["f.return", "op-return", "expected String", "got Int64"] {
        assert!(
            ill_typed.contains(want),
            "the caught diagnostic must carry `{want}`, got: {ill_typed}"
        );
    }
}

/// A LOCAL NAMED `reify` DOES NOT CAPTURE `Error.reify`. The local lookup in
/// `dispatch_call_with_requirements_inner` matches by SHORT NAME, so a parameter
/// called `reify` that holds something callable used to win — and this is worse than
/// the wrong answer WI-455 describes, because the DISCHARGE was granted on the
/// resolved signature: `shadowed` declares NO effects, and with the local winning the
/// raise escapes an operation the typer certified effect-free.
///
/// `runIt` answers `ok(999)` without ever calling its thunk, so the two outcomes are
/// distinguishable as VALUES rather than by whether the process survives. MEASURED,
/// with the hoisted test disabled so only `dispatch_resolved_operation`'s copy runs:
/// `assertion left == right failed: expected the err arm / left: "ok" / right: "err"`.
#[test]
fn a_local_named_reify_does_not_capture_the_boundary() {
    let mut interp = interp();
    let r = interp
        .call("test.reify.shadowTest", &[])
        .expect("the qualified Error.reify is not captured by a same-named local");
    assert_eq!(err_why(&interp, &r), "negative");
}

/// A boundary is a handler for the `Error` EFFECT, not a catch-all for interpreter
/// faults. `DepthExceeded` arises inside `stack.push` — on the very path the recovery
/// hook sits on — so it is the one that measures the `Raised`-only guard rather than
/// bypassing it. (`StepsExhausted` would not: `run()` returns it before the trampoline
/// reaches a step at all.)
///
/// MEASURED: this row FAILS under a back-out of the boundary like every other caller
/// of `reify` (`OperationBodyMissing`), so it does not separate the boundary from
/// nothing. It separates it from a WIDER boundary — it goes red the moment recovery
/// accepts anything but `EvalError::Raised`, which is a regression no other row here
/// would catch.
#[test]
fn a_non_raised_error_is_not_caught() {
    // The cap goes in at CONSTRUCTION, not through `config_mut()`. `with_config`
    // sizes the `ActivationStack` from `config.depth_cap` once and the stack keeps
    // its own copy, so a later `config_mut().depth_cap = Some(64)` changes the
    // config and nothing else — measured, this test then ran to the 1,000,000-frame
    // default and took over 60 seconds to assert the same thing.
    let mut interp = anthill_core::eval::Interpreter::with_config(
        crate::common::load_kb_with(PROGRAM),
        anthill_core::eval::EvalConfig {
            depth_cap: Some(64),
            ..Default::default()
        },
    );
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    let err = interp
        .call("test.reify.deepInsideBoundary", &[])
        .expect_err("a depth overflow is not an Error effect and must not be caught");
    assert!(
        matches!(err, EvalError::DepthExceeded { .. }),
        "expected DepthExceeded to pass through the boundary, got {err:?}"
    );
}

/// The load-time control (b) of the ticket, and the one row here that needs no
/// runtime: the label is discharged BY THE SIGNATURE. `caught` declares no effects
/// and loads; the same body without the boundary is refused as an undeclared effect.
///
/// PASSES EITHER WAY under a back-out of the boundary — MEASURED. This is the TYPER's
/// half, which WI-329 delivered and 027.4's fix (a) unblocked. It is here so that a
/// future change which makes `reify` catch at run time while quietly ceasing to
/// DISCHARGE at load time cannot pass.
#[test]
fn a_row_without_error_is_still_refused() {
    let unreified = PROGRAM.replace(
        "operation uncaught() -> Int64 effects {Error[Boom]} = mayFail(0 - 1)",
        "operation uncaught() -> Int64 = mayFail(0 - 1)",
    );
    assert_ne!(unreified, PROGRAM, "the fixture line must still be there");
    match crate::common::try_load_kb_with(&unreified) {
        Ok(_) => panic!("an undeclared, unreified `Error[Boom]` must not load"),
        Err(errs) => {
            let joined = errs.join("\n");
            assert!(
                joined.contains("undeclared effect") && joined.contains("Error"),
                "expected an undeclared-effect refusal, got:\n{joined}"
            );
        }
    }
}
