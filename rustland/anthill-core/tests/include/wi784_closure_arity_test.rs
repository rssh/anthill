//! WI-784: a multi-binder LAMBDA is applicable with N arguments, so a lambda
//! and a named OPERATION are interchangeable as function values.
//!
//! `enter_closure` used to reject `args.len() != 1` outright, because a
//! multi-binder lambda is ONE tuple pattern (proposal 018 §"Lambda always
//! takes _one_ argument. Multiple parameters use tuple destructuring"). But
//! the stdlib applies its callbacks with N SEPARATE arguments —
//! `prelude/list.anthill`'s `foldLeft(t, f(init, h), f)` — and 018 itself
//! shows `fold(lambda (acc, x) -> …)` as intended usage. So every evaluated
//! higher-order call had to pass an operation: the OpRef arm adapts arguments
//! via `spread_eta_args`, the closure arm did not. The fix is that arm's dual,
//! `gather_closure_arg`: N arguments are gathered back into the one tuple the
//! param pattern destructures, and a nullary binder accepts zero.
//!
//! Every test here DRIVES the program end-to-end — the defect was invisible at
//! load (all of these loaded clean and trapped at eval), so a load assertion
//! proves nothing. Each case builds a FRESH `Interpreter`: after any trapped
//! call, reusing one makes every later call return a bogus
//! `Internal("deliver: parent frame had no awaiting state")`, which reads as a
//! second independent bug.
//!
//! The headline shape is an AGREEMENT test — the lambda and operation
//! spellings of the SAME call must produce the SAME value. Asserting the
//! lambda alone would be satisfied by any number that stopped trapping.

use crate::common::{interp_for, try_load_kb_with};

fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// Evaluate `op` in a fresh interpreter, asserting the program loaded clean.
fn eval_int(src: &str, op: &str) -> i64 {
    if let Err(errs) = try_load_kb_with(src) {
        panic!("expected a clean load; got: {errs:?}");
    }
    run_int(&mut interp_for(src), op)
}

/// THE HEADLINE. `f(3, 10)` against a declared `(acc: Int64, x: Int64) -> Int64`
/// slot, driven with BOTH spellings of the same callback. Pre-fix the operation
/// spelling gave `Ok(Int(-7))` and the lambda spelling trapped
/// `ArityMismatch { op: "closure", expected: 1, got: 2 }`.
#[test]
fn two_binder_lambda_and_named_operation_agree() {
    let src = r#"
namespace test.wi784.headline
  import anthill.prelude.{Int64}

  operation sub2(acc: Int64, x: Int64) -> Int64 = acc - x

  operation apply_arrow(f: (acc: Int64, x: Int64) -> Int64) -> Int64 = f(3, 10)

  operation drive_op() -> Int64 = apply_arrow(sub2)
  operation drive_lambda() -> Int64 = apply_arrow(lambda (acc, x) -> acc - x)
end
"#;
    let via_op = eval_int(src, "test.wi784.headline.drive_op");
    let via_lambda = eval_int(src, "test.wi784.headline.drive_lambda");
    assert_eq!(via_op, -7, "the operation spelling is the control and already worked");
    assert_eq!(
        via_lambda, via_op,
        "the lambda and operation spellings of the same call must agree",
    );
}

/// The idiomatic higher-order call, through the SHIPPED stdlib fold whose
/// callback is applied as `f(init, h)`. `FiniteCollection.foldLeft` is the route
/// driven here because its callback uses a plain `Element` type param. The
/// concrete `List.foldLeft` over a LITERAL was blocked one rung earlier by a
/// separate path-dependent-`xs.T` defect, which WI-793 closed — it is now driven
/// alongside this one by `list_foldleft_lambda_over_a_literal_agrees`.
#[test]
fn stdlib_foldleft_agrees_for_lambda_and_operation() {
    let src = r#"
namespace test.wi784.fold
  import anthill.prelude.{Int64}
  import anthill.prelude.FiniteCollection.{foldLeft}

  operation shift(acc: Int64, x: Int64) -> Int64 = acc * 10 + x

  operation drive_op() -> Int64 = foldLeft([1, 2, 3], 0, shift)
  operation drive_lambda() -> Int64 =
    foldLeft([1, 2, 3], 0, lambda (acc, x) -> acc * 10 + x)
end
"#;
    let via_op = eval_int(src, "test.wi784.fold.drive_op");
    let via_lambda = eval_int(src, "test.wi784.fold.drive_lambda");
    assert_eq!(via_op, 123, "the operation spelling is the control and already worked");
    assert_eq!(
        via_lambda, via_op,
        "`foldLeft(xs, 0, lambda (acc, x) -> …)` must agree with the operation spelling",
    );
}

/// The `List.foldLeft` twin of `stdlib_foldleft_agrees_for_lambda_and_operation`,
/// kept HERE (rather than only in WI-793's own suite) because this file's fold test
/// routes around `List.foldLeft` and that detour needs a live check, not a prose claim.
///
/// This was WI-784's pinned known gap, asserting the WRONG behaviour on purpose:
/// `List.foldLeft`'s callback is typed with the path-dependent `xs.T`, which over a
/// LITERAL receiver never resolved for a LAMBDA binder, so a correct program failed to
/// LOAD (`expected Int64, got xs.T`). WI-793 closed it; the assertion is now positive.
///
/// The two controls are retained because they locate the boundary, and both obvious
/// readings of the original defect were WRONG: it was not "lambdas break
/// `List.foldLeft`" (control 3 loaded), and not "list literals break `List.foldLeft`"
/// (control 1 loaded) — it took the literal AND the lambda together. Keeping them
/// means a regression names which half came back.
#[test]
fn list_foldleft_lambda_over_a_literal_agrees() {
    // 1. CONTROL — literal + named operation. Loaded even while the gap was open.
    let literal_with_operation = r#"
namespace test.wi784.listfold.op
  import anthill.prelude.{Int64, List, nil, cons}

  operation shift(acc: Int64, x: Int64) -> Int64 = acc * 10 + x

  operation drive() -> Int64 = List.foldLeft([1, 2, 3], 0, shift)
end
"#;
    // 2. WAS THE GAP — literal + lambda. Now loads AND evaluates.
    let literal_with_lambda = r#"
namespace test.wi784.listfold.lam
  import anthill.prelude.{Int64, List, nil, cons}

  operation drive() -> Int64 =
    List.foldLeft([1, 2, 3], 0, lambda (acc, x) -> acc * 10 + x)
end
"#;
    // 3. CONTROL — declared `List[T = Int64]` parameter + the SAME lambda: the
    //    declared type pinned the element even while the literal did not.
    let param_with_lambda = r#"
namespace test.wi784.listfold.param
  import anthill.prelude.{Int64, List, nil, cons}

  operation fold(xs: List[T = Int64]) -> Int64 =
    List.foldLeft(xs, 0, lambda (acc, x) -> acc * 10 + x)

  operation drive() -> Int64 = fold([1, 2, 3])
end
"#;
    let via_op = eval_int(literal_with_operation, "test.wi784.listfold.op.drive");
    let via_lambda = eval_int(literal_with_lambda, "test.wi784.listfold.lam.drive");
    let via_param = eval_int(param_with_lambda, "test.wi784.listfold.param.drive");
    assert_eq!(via_op, 123, "control 1: literal receiver + named operation");
    assert_eq!(
        via_lambda, via_op,
        "`List.foldLeft([1, 2, 3], 0, lambda (acc, x) -> …)` must agree with the \
         operation spelling — this is the assertion WI-793 flipped",
    );
    assert_eq!(
        via_param, via_op,
        "control 3: pinning the element type through a declared parameter must reach \
         the same answer as the literal receiver",
    );
}

/// The ARITY-ZERO twin: `enter_closure`'s `args.len() != 1` rejected 0 as well
/// as 2, so a nullary thunk could be built but never forced.
#[test]
fn nullary_lambda_is_forced() {
    let src = r#"
namespace test.wi784.nullary
  import anthill.prelude.{Int64}

  operation run(t: () -> Int64) -> Int64 = t()

  operation drive() -> Int64 = run(lambda () -> 5)
end
"#;
    assert_eq!(eval_int(src, "test.wi784.nullary.drive"), 5);
}

/// The arity-zero twin in the SHIPPED stdlib: `Delay` builds its thunk as
/// `delayed(lambda () -> a)` and forces it with `case delayed(t) -> t()`, so
/// the whole monad was unevaluatable. Its own suite
/// (`wi516_graded_effect_row_test.rs`) is load-only and re-declares a local
/// copy, which is why this never surfaced — so drive the stdlib's.
#[test]
fn stdlib_delay_monad_evaluates() {
    let src = r#"
namespace test.wi784.delay
  import anthill.prelude.{Int64, delayPure, delayForce}

  operation drive() -> Int64 = delayForce(delayPure(5))
end
"#;
    assert_eq!(eval_int(src, "test.wi784.delay.drive"), 5);
}

/// A CALLER-BUILT tuple still matches — the single-argument reading is
/// untouched, so `f((3, 10))` destructures as before.
///
/// This is the `Function[A, B]` spelling deliberately: WI-791 made arity-2 and
/// arity-1 distinct types, so the ARROW spelling of a one-tuple-parameter slot
/// (`((Int64, Int64)) -> Int64`) now REFUSES a 2-binder lambda at load. That
/// rejection is WI-791's and is not reverted here; `Function` states no arity
/// (`function_spelling_states_no_arity_and_still_bridges`), so it is the
/// spelling in which this program still loads.
#[test]
fn caller_built_tuple_still_matches() {
    let src = r#"
namespace test.wi784.tuplearg
  import anthill.prelude.{Int64, Function}

  operation apply_tuple(f: Function[A = (Int64, Int64), B = Int64]) -> Int64 =
    f((3, 10))

  operation drive() -> Int64 = apply_tuple(lambda (acc, x) -> acc - x)
end
"#;
    assert_eq!(eval_int(src, "test.wi784.tuplearg.drive"), -7);
}

/// The generic twin. A 2-binder lambda into a TYPE-PARAMETERIZED callback slot
/// trapped identically — and, unlike the operation-valued case pinned by
/// WI-791's `known_gap_generic_callback_arrow_is_not_conformance_checked`, this
/// one is NOT a conformance gap that WI-792 will close: the arity-2 lambda
/// genuinely MATCHES the arity-2 slot. It was only ever the closure arm.
#[test]
fn generic_callback_lambda_applies() {
    let src = r#"
namespace test.wi784.generic
  import anthill.prelude.{Int64}

  operation apply2[T](f: (x: T, y: T) -> Int64, v: T, w: T) -> Int64 = f(v, w)

  operation drive() -> Int64 = apply2(lambda (x, y) -> x - y, 3, 10)
end
"#;
    assert_eq!(eval_int(src, "test.wi784.generic.drive"), -7);
}

/// A UNARY lambda is unaffected — the single-argument path is the one that
/// already worked, and must keep working unchanged.
#[test]
fn unary_lambda_is_unaffected() {
    let src = r#"
namespace test.wi784.unary
  import anthill.prelude.{Int64}

  operation apply1(f: (x: Int64) -> Int64) -> Int64 = f(3)

  operation drive() -> Int64 = apply1(lambda x -> x - 10)
end
"#;
    assert_eq!(eval_int(src, "test.wi784.unary.drive"), -7);
}

/// A NULLARY thunk where ONE argument is passed.
///
/// WI-801 MOVED THIS ERROR FROM EVAL TO LOAD, exactly as WI-788 moved
/// `wrong_arity_application_is_still_refused_with_the_binder_count` below, and for
/// the same reason. This used to assert the program LOADED and then failed in the
/// matcher, pinning "the branch structure's one asymmetry": one argument is always
/// handed to the pattern as-is, so the arity comparison never ran and a nullary
/// thunk given an argument reached the matcher.
///
/// That corner was a CONSEQUENCE of the conformance check reading no arity at a
/// `Function` slot, not a property worth keeping. `lambda () -> 5` has type
/// `() -> Int64`; the slot is `Function[A = Int64, B = Int64]`, whose `A` is one
/// indivisible value. No call form reaches a nullary callee there — neither the
/// whole-`A` form (one argument) nor a spread (`A` has no components) — so the
/// argument is refused at LOAD now, which is the direction the repo wants.
///
/// The matcher's own binder-count guard is still exercised at eval, by
/// `a_callback_arity_the_typer_cannot_decide_still_fails_in_the_matcher` below.
#[test]
fn nullary_thunk_called_with_an_argument_is_refused_at_load() {
    let src = r#"
namespace test.wi784.nullaryarg
  import anthill.prelude.{Int64, Function}

  operation force_with_arg(t: Function[A = Int64, B = Int64]) -> Int64 = t(7)

  operation drive() -> Int64 = force_with_arg(lambda () -> 5)
end
"#;
    let errs = try_load_kb_with(src)
        .err()
        .expect("a nullary thunk at a one-argument slot must be refused at load");
    let msg = errs.join(" | ");
    assert!(
        msg.contains("mismatch"),
        "a nullary callback fits neither reading of `Function[A = Int64, B]`; got: {msg}",
    );
}

/// THE RESIDUAL EVAL-STAGE GUARD, which the load-time gate must not swallow.
///
/// WI-801 refuses a callback whose arity fits neither reading of `Function[A, …]`
/// — but only where `A`'s component count is KNOWN. At a RIGID `A` it is not, and
/// must not be guessed: a component count is exactly what instantiation supplies.
/// So this loads, reaches eval, and fails in the matcher — the path
/// `nullary_thunk_called_with_an_argument_is_refused_at_load` used to cover.
#[test]
fn a_callback_arity_the_typer_cannot_decide_still_fails_in_the_matcher() {
    let src = r#"
namespace test.wi784.rigidarity
  import anthill.prelude.{Int64, Function}

  operation ap[T](f: Function[A = T, B = T], x: T) -> T = f(x)

  operation drive() -> Int64 = ap(lambda (p, q) -> p, 5)
end
"#;
    assert!(
        try_load_kb_with(src).is_ok(),
        "a RIGID `A` states no component count, so no arity may be required of the callback",
    );
    let err = interp_for(src)
        .call("test.wi784.rigidarity.drive", &[])
        .expect_err("a 2-binder pattern must not match the scalar it is handed");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("Raised"),
        "the single argument is passed through to the MATCHER, so the 2-binder tuple \
         pattern fails against Int(5) and surfaces as a raised Error[MatchFailed]; got: {msg}",
    );
}

/// A GENUINE arity error stays loud and reports BOTH counts — the fix widens
/// what is accepted, it does not make a mismatched application silently succeed.
///
/// WI-788 MOVED THIS ERROR FROM EVAL TO LOAD, and the assertion moved with it.
/// The original ran the program: `Function` states no arity, so nothing refused
/// the call and the 2-binder closure trapped `ArityMismatch{expected: 2, got: 3}`
/// against three arguments. That "states no arity" was read as "nothing can be
/// checked", which is what left the whole `Function` slot unchecked (WI-788: an
/// argument of the WRONG TYPE was never looked at either). No slot COUNT can be
/// REQUIRED of a `Function` — `f(3, 10)` and `f((3, 10))` are both legal — but a
/// count can be OBSERVED at the call, and three arguments against a 2-component
/// `A` is refutable without requiring anything.
///
/// So the invariant this test exists for is unchanged and still pinned: the
/// diagnostic names the BINDER-derived count (2), not a hardcoded 1, alongside
/// the actual 3. Only the STAGE changed, which is the direction the repo wants —
/// a load error beats a run-time trap. WI-801 then moved the two remaining
/// eval-stage cases the same way; the matcher's own binder-count arity guard is
/// still exercised at eval by
/// `a_callback_arity_the_typer_cannot_decide_still_fails_in_the_matcher` here,
/// which reaches it through a RIGID `A` no static check may decide.
#[test]
fn wrong_arity_application_is_still_refused_with_the_binder_count() {
    let src = r#"
namespace test.wi784.wrongarity
  import anthill.prelude.{Int64, Function}

  operation apply3(f: Function[A = (Int64, Int64), B = Int64]) -> Int64 =
    f(1, 2, 3)

  operation drive() -> Int64 = apply3(lambda (x, y) -> x - y)
end
"#;
    let errs = try_load_kb_with(src)
        .err()
        .expect("applying a 2-binder lambda to 3 arguments must be refused");
    let msg = errs.join(" | ");
    // The PHRASES, not loose digits: a bare `contains("2") && contains("3")` is
    // satisfied incidentally by a span like `3:2`, so it would still pass if the
    // counts regressed to the hardcoded 1 this test exists to forbid.
    assert!(
        msg.contains("or 2 (its components spread)") && msg.contains("got 3 arguments"),
        "the diagnostic must report A's component count (2) and the supplied count (3), \
         not a hardcoded 1; got: {msg}",
    );
}



/// THE INTERCHANGEABILITY INVARIANT, as a 2x2 matrix: {named OPERATION, LAMBDA}
/// x {applied with N ARGUMENTS, applied with ONE TUPLE}. All four must agree.
///
/// Driven through `Function[A, B]`, which states no arity (WI-791), so BOTH
/// applications are legal at the slot and the type system cannot mask the
/// question — what is measured here is purely the RUNTIME's treatment of the two
/// callable kinds.
///
/// Pre-fix exactly ONE cell was broken: `lam_nargs` trapped
/// `ArityMismatch{op: "closure", expected: 1, got: 2}` while the other three
/// returned -7. That single asymmetric cell IS this ticket — the OpRef arm
/// adapted its arguments and the Closure arm did not. An operation and a lambda
/// are now adapted by the same two conventions in both directions: an operation
/// takes one tuple via `spread_eta_args`, a lambda takes n arguments via
/// `gather_closure_arg`.
#[test]
fn operations_and_lambdas_are_interchangeable_in_both_application_forms() {
    let src = r#"
namespace test.wi784.matrix
  import anthill.prelude.{Int64, Function}

  operation sub2(a: Int64, b: Int64) -> Int64 = a - b

  operation spread(f: Function[A = (Int64, Int64), B = Int64]) -> Int64 = f(3, 10)
  operation tuple_(f: Function[A = (Int64, Int64), B = Int64]) -> Int64 = f((3, 10))

  operation op_nargs()  -> Int64 = spread(sub2)
  operation op_tuple()  -> Int64 = tuple_(sub2)
  operation lam_nargs() -> Int64 = spread(lambda (a, b) -> a - b)
  operation lam_tuple() -> Int64 = tuple_(lambda (a, b) -> a - b)
end
"#;
    for cell in ["op_nargs", "op_tuple", "lam_nargs", "lam_tuple"] {
        assert_eq!(
            eval_int(src, &format!("test.wi784.matrix.{cell}")),
            -7,
            "{cell}: an operation and a lambda must agree in BOTH application forms",
        );
    }
}
