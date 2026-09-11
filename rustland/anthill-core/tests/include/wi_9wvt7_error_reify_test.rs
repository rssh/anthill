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
//! `Error.reify` falls through to the ordinary routes: EVERY row that calls `reify` dies
//! `OperationBodyMissing { name: "anthill.prelude.Error.reify" }` — the declaration has no
//! body and no builtin, which is exactly why the boundary cannot be either. The two that
//! survive are named below.
//!
//! A COUNT IS NOT WRITTEN HERE ON PURPOSE. Tallies in this header drifted twice — one
//! said "8 failed, 2 passed" and one "3 failed, 12 passed" against a file that has had
//! 11, 12, 20 and now 21 rows — and a tally nobody can reproduce makes the next
//! re-measurement unable to tell a new regression from stale arithmetic. What a back-out
//! owes is the SET, which is what each row states at its own site.
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
//!
//! THE NARROWING — "catch only the payload this boundary is typed at" — is measured
//! separately, by making `payload_matches` return `true` unconditionally (the old
//! carrier-only rule, "is this a raise"). The rows that go red are exactly the ones about
//! a boundary NOT catching something:
//! `a_boundary_declines_a_payload_it_is_not_typed_at`,
//! `each_raise_reaches_the_boundary_typed_at_it`,
//! `a_host_raise_is_not_mistaken_for_the_declared_payload`,
//! `a_narrowed_boundary_does_not_steal_an_unreadable_payload`,
//! `a_reify_at_an_operations_own_type_parameter_catches` (its declining third row) and
//! `a_declined_raise_leaves_the_interpreter_usable` (whose `expect_err` stops erring).
//! Every other row is about a boundary catching its OWN payload, which both rules agree
//! on.

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

  -- TWO LABELS, ONE CHANNEL. `twoWays` raises `Boom` on one branch and `Other` on the
  -- other, and its row says both. A `reify` discharges the ONE it is typed at, so the
  -- other stays in the caller's row — which the typer enforces (a caller omitting it is
  -- refused, measured) and which the RUNTIME must honour too.
  sort Other
    entity other(n: Int64)
  end

  operation twoWays(n: Int64) -> Int64 effects {Error[Boom], Error[Other]} =
    if n < 0 then Error.raise(boom("negative")) else Error.raise(other(n))

  operation innerAtBoom(n: Int64) -> Result[E = Boom, T = Int64] effects {Error[Other]} =
    Error.reify(lambda () -> twoWays(n))

  -- NESTED AT DIFFERENT PAYLOADS. The inner boundary takes `Boom`, the outer takes the
  -- `Other` the inner declined. This is anthill's answer to a multi-catch: the row
  -- names the labels, and one `reify` per label composes as `Result` layers.
  operation nestedAtTwoPayloads(n: Int64)
      -> Result[E = Other, T = Result[E = Boom, T = Int64]] =
    Error.reify(lambda () -> innerAtBoom(n))

  operation boomGoesToInner() -> Result[E = Other, T = Result[E = Boom, T = Int64]] =
    nestedAtTwoPayloads(0 - 1)
  operation otherGoesToOuter() -> Result[E = Other, T = Result[E = Boom, T = Int64]] =
    nestedAtTwoPayloads(7)

  -- A LONE boundary at `Boom` around the same body: the `Other` branch has nowhere to
  -- go, so it must ESCAPE this operation carrying its own payload — which is what the
  -- declared `effects {Error[Other]}` on `innerAtBoom` already promises.
  operation declinedEscapes() -> Result[E = Boom, T = Int64] effects {Error[Other]} =
    innerAtBoom(7)

  -- A HOST raise — `Error[MatchFailed]` from a guard-exhaustible match — inside a
  -- boundary typed at `Boom`. Pattern coverage is total, so this LOADS; every guard
  -- can still decline at run time.
  operation guardExhaustible(n: Int64) -> Int64 effects {Error[Boom]} =
    match n
      case k | k > 0 -> k

  operation hostRaiseInsideBoundary() -> Result[E = Boom, T = Int64] =
    Error.reify(lambda () -> guardExhaustible(0 - 5))

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

  -- A GENERIC boundary. `catchIt` reifies at ITS OWN type parameter, so at the reify
  -- call site `T1` is the skolem `P` and only the CALL to `catchIt` says what `P` is.
  -- The frame's type-argument channel carries `P = Boom` there, and
  -- `collect_closed_type_args` grounds `T1` against it before the dispatch.
  operation catchIt[P](body: () -> Int64 @ {Error[P]}) -> Result[E = P, T = Int64] =
    Error.reify(body)

  operation viaGeneric() -> Result[E = Boom, T = Int64] =
    catchIt(lambda () -> mayFail(0 - 1))

  operation viaGenericOk() -> Result[E = Boom, T = Int64] =
    catchIt(lambda () -> mayFail(41))

  -- A GENERIC boundary that must DECLINE. `catchItEsc` discharges its OWN `P` and leaves
  -- `Error[Other]` in its caller's row, so an `Other` raised inside it has to travel past
  -- it. This is the row that needs `P` ground: a boundary that cannot be narrowed catches
  -- wide, so it would swallow the `Other`.
  operation catchItEsc[P](body: () -> Int64 @ {Error[P], Error[Other]})
      -> Result[E = P, T = Int64] effects {Error[Other]} =
    Error.reify(body)

  operation genericDeclines() -> Result[E = Boom, T = Int64] effects {Error[Other]} =
    catchItEsc(lambda () -> twoWays(7))

  operation genericDeclineOuter() -> Result[E = Other, T = Result[E = Boom, T = Int64]] =
    Error.reify(lambda () -> genericDeclines())

  -- A TUPLE payload. A tuple type's head is the ENTITY `TypeExtractor.NamedTuple`, which
  -- names no sort, so this boundary CANNOT be narrowed and must catch wide — as every
  -- boundary did before the narrowing existed.
  operation raisesTuple(n: Int64) -> Int64 effects {Error[(a: Int64, b: String)]} =
    Error.raise((a: n, b: "neg"))

  operation caughtTuple() -> Result[E = (a: Int64, b: String), T = Int64] =
    Error.reify(lambda () -> raisesTuple(0 - 1))

  -- NESTED, AT A READABLE AND AN UNREADABLE PAYLOAD. `innerAtBoom` is WRITTEN at `Boom`
  -- around a body that raises both a `Boom` and a tuple, so the typer makes it declare the
  -- tuple label as escaping — the row saying it discharged only `Boom`. The tuple must
  -- therefore reach the outer boundary, the one typed at it.
  operation boomOrTuple(n: Int64) -> Int64 effects {Error[Boom], Error[(a: Int64, b: String)]} =
    if n < 0 then Error.raise(boom("neg")) else Error.raise((a: n, b: "tup"))

  operation tupleInnerAtBoom(n: Int64) -> Result[E = Boom, T = Int64]
      effects {Error[(a: Int64, b: String)]} =
    Error.reify[T1 = Boom](lambda () -> boomOrTuple(n))

  operation nestedAtBoth(n: Int64)
      -> Result[E = (a: Int64, b: String), T = Result[E = Boom, T = Int64]] =
    Error.reify(lambda () -> tupleInnerAtBoom(n))

  operation nestedTupleEscapes()
      -> Result[E = (a: Int64, b: String), T = Result[E = Boom, T = Int64]] =
    nestedAtBoth(7)

  operation nestedBoomCaught()
      -> Result[E = (a: Int64, b: String), T = Result[E = Boom, T = Int64]] =
    nestedAtBoth(0 - 1)

  -- The generic boundary reached through a RULE BODY. The bridge pushes a frame with an
  -- EMPTY type-argument channel, so nothing can ground `P` — the boundary is un-narrowable
  -- there and must still answer. `viaPlainRule` is the same call at a concrete payload.
  rule viaGenericRule(?r) :- catchIt(lambda () -> mayFail(0 - 1), ?r)
  rule viaPlainRule(?r) :- caught(?r)

  -- SUBSUMPTION AT THE BOUNDARY. `Narrow` refines `Boom`, and `Error`'s payload is
  -- declared `Covariant`, so a body raising `Error[Narrow]` conforms to a boundary
  -- WRITTEN at `Boom` and the typer DISCHARGES the label — `wideCatch` declares no
  -- effects and the fixture loads. A runtime decline would then let the raise escape an
  -- operation already typed effect-free.
  sort Narrow
    requires Boom
    entity narrow(n: Int64)
  end

  operation raisesNarrow() -> Int64 effects {Error[Narrow]} =
    Error.raise(narrow(3))

  -- `[T1 = Boom]` is what makes the boundary WIDER than the raiser. Left to inference,
  -- `T1` comes from the body's row and the boundary is at `Narrow` — which is the
  -- control below.
  operation wideCatch() -> Result[E = Boom, T = Int64] =
    Error.reify[T1 = Boom](lambda () -> raisesNarrow())

  operation narrowCatch() -> Result[E = Boom, T = Int64] =
    Error.reify(lambda () -> raisesNarrow())
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

/// THE BOUNDARY CATCHES WHAT IT IS TYPED AT, AND ONLY THAT — the rule the row already
/// states statically. `innerAtBoom` is `-> Result[E = Boom, T = Int64] effects
/// {Error[Other]}`: the typer discharged `Error[Boom]` and left `Error[Other]` for the
/// caller, and REFUSES a caller that omits it (measured: "undeclared effect: Error[T =
/// Other]"). So an `Other` raised inside that boundary must travel past it.
///
/// MEASURED BEFORE THE NARROWING, and this is why it is not a theoretical concern: the
/// boundary caught on the error's CARRIER — "is this a raise" — so it swallowed the
/// `Other` into a `Result[E = Boom]`, and the caller's `case boom(w)` then died
/// `match_failed(scrutinee: other(n: 7))` — a match failure on a value that could never
/// legally be there. Now it escapes as `Raised { other(n: 7) }`, recoverable and with
/// its real payload.
#[test]
fn a_boundary_declines_a_payload_it_is_not_typed_at() {
    let mut interp = interp();
    let err = interp
        .call("test.reify.declinedEscapes", &[])
        .expect_err("a payload the boundary is not typed at must travel past it");
    match err {
        EvalError::Raised { payload } => {
            assert_eq!(
                short_name(&interp, &payload),
                "other",
                "the escaping raise must carry its OWN payload, not a coerced one"
            );
            assert_eq!(int_of(&interp, &field(&interp, &payload, "n", 0)), 7);
        }
        other => panic!("expected the declined raise to propagate, got {other:?}"),
    }
}

/// THE TWO-WAY CASE, which is what "handle only ours" buys: two boundaries at different
/// payloads, and each raise reaches the one typed at it. Anthill needs no multi-catch
/// form for this — the effect ROW is the list of labels, and one `reify` per label
/// composes as nested `Result`s.
///
/// The two rows pin the choice between them rather than either passing by luck: swap
/// the rule back to "innermost wins" and BOTH answer through the inner boundary, so the
/// second row reads `ok(err(other(…)))` instead of `err(other(…))`.
#[test]
fn each_raise_reaches_the_boundary_typed_at_it() {
    let mut interp = interp();

    // `Boom` — the INNER boundary's payload. The outer sees a normal return.
    let inner = interp
        .call("test.reify.boomGoesToInner", &[])
        .expect("a Boom is caught by the inner boundary");
    assert_eq!(
        short_name(&interp, &inner),
        "ok",
        "the outer boundary saw no raise"
    );
    let nested = field(&interp, &inner, "value", 0);
    assert_eq!(err_why(&interp, &nested), "negative");

    // `Other` — declined by the inner, caught by the OUTER.
    let outer = interp
        .call("test.reify.otherGoesToOuter", &[])
        .expect("an Other travels past the inner boundary to the outer");
    assert_eq!(
        short_name(&interp, &outer),
        "err",
        "the outer boundary is the one typed at Other"
    );
    let payload = field(&interp, &outer, "error", 0);
    assert_eq!(short_name(&interp, &payload), "other");
    assert_eq!(int_of(&interp, &field(&interp, &payload, "n", 0)), 7);
}

/// A HOST RAISE IS NOT MISTAKEN FOR THE DECLARED PAYLOAD. `raise_match_failed` puts an
/// `Error[MatchFailed]` on the same channel, and nothing puts that label in the row —
/// so under the old carrier-only rule a boundary typed at `Boom` swallowed it, and the
/// caller's destructuring then failed on it. Measured before the narrowing, the
/// observable was a `match_failed` nested inside another `match_failed`; now the
/// original escapes with its real scrutinee.
///
/// This is the same repair as the two rows above rather than a second mechanism, which
/// is the point: "only ours" answers both the two-label case and the host-raise case.
#[test]
fn a_host_raise_is_not_mistaken_for_the_declared_payload() {
    let mut interp = interp();
    let err = interp
        .call("test.reify.hostRaiseInsideBoundary", &[])
        .expect_err("a MatchFailed is not a Boom, so the boundary must decline it");
    match err {
        EvalError::Raised { payload } => assert_eq!(
            short_name(&interp, &payload),
            "match_failed",
            "the escaping raise must still be the MatchFailed, undisturbed"
        ),
        other => panic!("expected the host raise to propagate, got {other:?}"),
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

/// A GENERIC BOUNDARY IS TYPED AT WHAT ITS CALLER PASSED — the case the narrowing could
/// not answer until the type-argument channel was closed.
///
/// `catchIt[P]` reifies at its own parameter, so the typer resolves `T1` to `P` at that
/// call site: correct, and useless to the runtime on its own, because what `P` stands for
/// is decided by the CALLER. `collect_closed_type_args` grounds it from the frame
/// (`P = Boom`) before the dispatch, so the boundary installs at a payload sort like any
/// other.
///
/// THE THIRD ROW IS THE ONE THAT DRIVES IT, and the first two say why it is needed. An
/// un-narrowable boundary catches WIDE (see `AwaitState::ReifyBoundary::payload`), so
/// `viaGeneric` and `viaGenericOk` pass with or without the grounding — a boundary that
/// catches everything still catches its own `Boom`. Only a boundary that must DECLINE
/// separates the two: `catchItEsc` discharges `P` and leaves `Error[Other]` for its
/// caller, so with `P` ground the `Other` travels out to `genericDeclineOuter`, and
/// without it the inner boundary swallows the `Other` into a `Result[E = Boom]` and the
/// outer sees `ok`.
#[test]
fn a_reify_at_an_operations_own_type_parameter_catches() {
    let mut interp = interp();

    let caught = interp
        .call("test.reify.viaGeneric", &[])
        .expect("a boundary typed at the enclosing operation's `P` catches a `Boom`");
    assert_eq!(short_name(&interp, &caught), "err");
    assert_eq!(err_why(&interp, &caught), "negative");

    let fine = interp
        .call("test.reify.viaGenericOk", &[])
        .expect("the same generic boundary still delivers `ok` when nothing raises");
    assert_eq!(short_name(&interp, &fine), "ok");
    assert_eq!(int_of(&interp, &field(&interp, &fine, "value", 0)), 42);

    let outer = interp
        .call("test.reify.genericDeclineOuter", &[])
        .expect("the label the generic boundary does not discharge reaches the outer one");
    assert_eq!(
        short_name(&interp, &outer),
        "err",
        "a generic boundary at `Boom` must DECLINE an `Other` — `ok` here means it \
         swallowed the label its own row left to its caller"
    );
    let payload = field(&interp, &outer, "error", 0);
    assert_eq!(short_name(&interp, &payload), "other");
    assert_eq!(int_of(&interp, &field(&interp, &payload, "n", 0)), 7);
}

/// A BOUNDARY THE RUNTIME CANNOT NARROW CATCHES WIDE — it does not silently decline.
///
/// A tuple type's head is `anthill.prelude.TypeExtractor.NamedTuple`, an ENTITY, so `T1`
/// here names no sort and no value's `runtime_carrier_sort` could ever equal it. Reading
/// the head without asking whether it names a sort installed a boundary that declined
/// every raise, including its own: MEASURED before the check, `caughtTuple` let its raise
/// escape `main` as `error: Tuple`, out of an operation the typer had typed effect-free.
///
/// MEASURED: back `genuine_concrete_sort` out of `payload_sort_of` and THREE rows go red
/// — this one and `a_narrowed_boundary_does_not_steal_an_unreadable_payload` for the
/// no-sort half, and `a_generic_boundary_answers_through_a_rule_body` for the type-param
/// half (a parameter passes `has_kind(_, Sort)`, which is why the check is the typer's
/// predicate and not that test alone). Every other row uses a nominal payload and narrows
/// fine either way.
#[test]
fn a_payload_the_runtime_cannot_narrow_is_still_caught() {
    let mut interp = interp();
    let caught = interp
        .call("test.reify.caughtTuple", &[])
        .expect("a tuple payload has no sort to narrow to, so the boundary catches wide");
    assert_eq!(short_name(&interp, &caught), "err");
    let payload = field(&interp, &caught, "error", 0);
    assert_eq!(
        str_of(&interp, &field(&interp, &payload, "b", 1)),
        "neg",
        "the caught payload is the raised tuple itself"
    );
}

/// A DECLINED RAISE LEAVES THE INTERPRETER USABLE — the boundary frames it walked past
/// do not stay on the stack.
///
/// `run()` drains to empty on the success path, but an `Err` return abandons whatever
/// frames were live, and until the narrowing nothing could error with a SUSPENDED frame
/// installed: any boundary beneath a raise absorbed it. A declined raise is now an
/// ordinary outcome, so the leftovers became reachable — `deliver` answers `Done` only on
/// an empty stack, so the NEXT call popped past its own base into the stale frame.
///
/// MEASURED before `truncate_to`: this second call answered
/// `Internal("deliver: parent frame had no awaiting state")` on an interpreter that
/// answered `ok(42)` when it was fresh. Every other test here builds its own `interp()`,
/// which is exactly why none of them would notice; the real caller that would is
/// `anthill-todo`'s remint loop, one `&mut Interpreter` across many calls.
///
/// The FRESH-interpreter row is the control: it passes either way, and its only job is to
/// say the second call is well-formed independently of what preceded it.
#[test]
fn a_declined_raise_leaves_the_interpreter_usable() {
    let fresh = interp().call("test.reify.returned", &[]);
    assert!(
        fresh.is_ok(),
        "control: the call is fine on a fresh interpreter"
    );

    let mut interp = interp();
    interp
        .call("test.reify.declinedEscapes", &[])
        .expect_err("the Other is declined and escapes");
    let again = interp
        .call("test.reify.returned", &[])
        .expect("the same interpreter must still answer after a raise walked past a boundary");
    assert_eq!(short_name(&interp, &again), "ok");
    assert_eq!(int_of(&interp, &field(&interp, &again, "value", 0)), 42);
}

/// THE GENERIC BOUNDARY THROUGH A RULE BODY, where nothing can ground `P` at all.
///
/// `bridge_op_to_eval` pushes a frame with an EMPTY type-argument channel (as does every
/// host `interp.call`), so `T1` arrives as a reference to `catchIt`'s own parameter and
/// stays one. That is the un-narrowable case, and it must answer — the ROW discharged the
/// label whatever the runtime can tell about the payload.
///
/// MEASURED, and this is why the check is `genuine_concrete_sort` rather than
/// `has_kind(_, Sort)` alone: a type parameter is registered as a `SymbolKind::Sort` (so
/// `x: P` routes through the type-param branch), so taking the head at face value narrowed
/// the boundary to `catchIt.P` — a symbol no value can carry — and `viaGenericRule`
/// answered **no solutions**, silently, while `viaPlainRule` (the same shape at a concrete
/// payload) answered normally. Both rows are here for that reason: the plain one passes
/// either way and is the control.
///
/// `definite_unary`, not a solution COUNT: a floundered answer is a suspension — "I could
/// not decide this" — and must never read as success. The value is asserted too, because a
/// count would stay green with `?r` bound to anything at all, including a value proving the
/// boundary did not catch.
#[test]
fn a_generic_boundary_answers_through_a_rule_body() {
    let mut interp = interp();
    for (goal, why) in [
        ("test.reify.viaGenericRule", "the generic boundary"),
        ("test.reify.viaPlainRule", "the concrete control"),
    ] {
        let answers = crate::common::definite_unary(interp.kb_mut(), goal);
        assert_eq!(
            answers.len(),
            1,
            "{why} ({goal}) must answer definitely through the bridge; \
             an empty answer set is the silent-decline failure this pins"
        );
        assert_eq!(short_name(&interp, &answers[0]), "err", "{why}: caught");
        assert_eq!(
            err_why(&interp, &answers[0]),
            "negative",
            "{why}: the payload"
        );
    }
}

/// A NARROWED BOUNDARY DOES NOT STEAL A PAYLOAD IT CANNOT READ — the nested case, which
/// is where "catch what you cannot read" turns out to be wrong.
///
/// `tupleInnerAtBoom` is written `Error.reify[T1 = Boom]` around a body raising BOTH `Boom`
/// and a tuple, and the typer requires it to declare the tuple label as ESCAPING — the row
/// saying the `Boom` boundary discharged only `Boom`. So the tuple must reach the outer
/// boundary, the one typed at it.
///
/// MEASURED when `payload_matches` caught an unreadable carrier instead of declining:
/// outer = `ok`, inner = `err(Tuple{a: 7, b: "tup"})` — the inner boundary swallowed a
/// label the row had assigned to the outer, which is the exact defect the narrowing exists
/// to close. The `Boom` row is the control: it is the inner boundary's OWN payload and
/// answers through it either way.
#[test]
fn a_narrowed_boundary_does_not_steal_an_unreadable_payload() {
    let mut interp = interp();

    let outer = interp
        .call("test.reify.nestedTupleEscapes", &[])
        .expect("the tuple label reaches the boundary typed at it");
    assert_eq!(
        short_name(&interp, &outer),
        "err",
        "`ok` here means the inner `Boom` boundary stole the tuple label"
    );
    let payload = field(&interp, &outer, "error", 0);
    assert_eq!(str_of(&interp, &field(&interp, &payload, "b", 1)), "tup");

    // The control: the inner boundary's OWN payload still answers through it.
    let own = interp
        .call("test.reify.nestedBoomCaught", &[])
        .expect("a Boom is the inner boundary's own payload");
    assert_eq!(
        short_name(&interp, &own),
        "ok",
        "the outer saw a normal return"
    );
    assert_eq!(err_why(&interp, &field(&interp, &own, "value", 0)), "neg");
}

/// A WIDER BOUNDARY ADMITS A NARROWER RAISE, because the ROW already does.
/// `Error`'s payload is declared `Covariant`, so `raisesNarrow`'s `Error[Narrow]`
/// conforms to a `reify` typed at `Error[Boom]` and the typer DISCHARGES it —
/// `wideCatch` declares no effects and the fixture loads. Equality at the runtime
/// boundary would therefore be unsound rather than merely strict: the raise would
/// escape an operation the typer has already typed effect-free.
///
/// It is `sort_sym_compatible` that answers — the typer's own sort-vs-sort predicate,
/// whose third leg is the `requires`-refinement this row needs.
///
/// THE FIRST ROW IS THE ONLY ONE THAT DRIVES IT, and the second says why. `T1` is
/// INFERRED from the body's row unless written, so a plain `Error.reify(…)` around a body
/// declaring `Error[Narrow]` is typed at `Narrow` and plain equality answers —
/// `narrowCatch` passes with or without the refinement leg, as does every other row
/// in this file. Only the WRITTEN `Error.reify[T1 = Boom]` puts a wider boundary around a
/// narrower raiser, which is the same shape
/// `an_effect_labels_argument_subsumes_where_its_sort_declares_variance` loads at the
/// type level. Measured: with the refinement leg backed out of `sort_sym_compatible`'s
/// answer here, `wideCatch`
/// fails and `narrowCatch` still passes.
#[test]
fn a_boundary_catches_a_payload_whose_sort_refines_its_own() {
    let mut interp = interp();
    let caught = interp
        .call("test.reify.wideCatch", &[])
        .expect("a `Narrow` value is caught by a boundary typed at `Boom`, which it refines");
    assert_eq!(short_name(&interp, &caught), "err");
    let payload = field(&interp, &caught, "error", 0);
    assert_eq!(
        short_name(&interp, &payload),
        "narrow",
        "the caught payload is the raised value itself, not a coerced one"
    );
    assert_eq!(int_of(&interp, &field(&interp, &payload, "n", 0)), 3);

    // The control — same value, raised under its own label, so the boundary is at
    // `Narrow` and equality suffices.
    let same = interp
        .call("test.reify.narrowCatch", &[])
        .expect("a boundary typed at `Narrow` catches a `Narrow` by equality alone");
    assert_eq!(short_name(&interp, &same), "err");
    assert_eq!(
        short_name(&interp, &field(&interp, &same, "error", 0)),
        "narrow"
    );
}
