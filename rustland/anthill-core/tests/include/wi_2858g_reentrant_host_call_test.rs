//! WI-20260913-2858G — a host function that calls back into the interpreter from inside an
//! anthill body.
//!
//! A host function bound through `operation_map` may call `Interpreter::call` itself —
//! the guardians harness does, `generate` calling `Llm.complete` and `check` calling
//! `KB.loaded`. From the host's TOP LEVEL that works. From inside an anthill body it
//! faulted `Internal("deliver: parent frame had no awaiting state")`: the nested run
//! shares the activation stack, and `deliver` answered `Done` only on an EMPTY stack, so
//! the nested run's last delivery popped past its own base into the CALLER's frame —
//! mid-step, awaiting nothing.
//!
//! The fixture's host functions call back into plain anthill operations, so every value
//! asserted below can only come from the nested call having run AND its caller having
//! resumed with the result.
//!
//! THE FIX HAS TWO HALVES, AND EACH IS BACKED OUT ALONE — MEASURED, both:
//!
//!   * `deliver` ending at an EMPTY stack again (floor forced to 0) → 7 of 9 fail with the
//!     delivery fault: tail position, mid-body, two levels deep, argument/condition/guard,
//!     leaves-no-frame, the step-cap row (which gets the fault instead of
//!     `StepsExhausted`), and the uncaught-raise row — at its FOLLOW-UP call, not at the
//!     raise. `guardians_test`'s `one_round_of_the_generation_loop_answers_the_same_verdict`,
//!     which drives `guardians.attempt`, fails the same way.
//!   * a nested `interp.call` RESETTING `step_count` again (`top_level` forced true) → only
//!     `a_loop_of_re_entrant_calls_still_exhausts_the_step_cap` fails, by its timeout.
//!
//! Two pass under both BY DESIGN: the top-level control, which says the host functions
//! themselves are right, and the caught-raise row, which says the fix did not move where a
//! raise stops — `run` already truncated to the floor on the error path.

use anthill_core::eval::{EvalError, Interpreter, Value};
use anthill_core::kb::term_view::TermView;

const PROGRAM: &str = r#"
namespace test.w2858g
  import anthill.prelude.{Int64, String, Error, Result}

  sort Boom
    entity boom(why: String)
  end

  -- What the host functions call BACK INTO.
  operation inner(n: Int64) -> Int64 = n + 40
  operation innerRaises(n: Int64) -> Int64 effects {Error[Boom]} =
    Error.raise(boom("raised inside the nested call"))

  sort Host
    import anthill.prelude.{Int64, Error}
    import test.w2858g.{Boom}
    entity host
    operation bounce(n: Int64) -> Int64
    operation bounceTwice(n: Int64) -> Int64
    operation bounceRaising(n: Int64) -> Int64 effects {Error[Boom]}
  end

  provides Host language rust
    artifact "nowhere.rs"
    operation_map {
      bounce:        "w2858g_bounce",
      bounceTwice:   "w2858g_bounce_twice",
      bounceRaising: "w2858g_bounce_raising"
    }
  end

  -- THE HOST CALL WITH AN ANTHILL FRAME BENEATH IT: in tail position, and mid-body with
  -- work left to do after it answers.
  operation tail(n: Int64) -> Int64 = Host.bounce(n)
  operation continued(n: Int64) -> Int64 =
    let r = Host.bounce(n)
    r + 1

  -- TWO LEVELS: the nested call is itself a body that makes a re-entrant host call.
  operation twice(n: Int64) -> Int64 =
    let r = Host.bounceTwice(n)
    r + 1

  -- The host call resumed through OTHER wait-states than `let`: a call argument, an `if`
  -- condition, a `match` guard.
  operation add2(a: Int64, b: Int64) -> Int64 = a + b
  operation inArgument(n: Int64) -> Int64 = add2(Host.bounce(n), 1)
  operation inCondition(n: Int64) -> Int64 = if Host.bounce(n) > 41 then 1 else 0
  operation inGuard(n: Int64) -> Int64 =
    match n
      case k | Host.bounce(k) > 41 -> 1
      case _ -> 0

  -- A RAISE inside the nested call, caught by a boundary in the OUTER run ...
  operation caughtAcross() -> Result[E = Boom, T = Int64] =
    Error.reify(lambda () -> Host.bounceRaising(0))

  -- ... and one NOT caught, with an anthill frame beneath the host call.
  operation uncaughtAcross(n: Int64) -> Int64 effects {Error[Boom]} =
    let r = Host.bounceRaising(n)
    r + 1

  -- A constant-depth loop whose every pass makes a re-entrant host call.
  operation spin(n: Int64) -> Int64 =
    let r = Host.bounce(n)
    spin(r - 40)
end
"#;

/// Load [`PROGRAM`] with the three host functions registered, then build an interpreter.
fn interp() -> Interpreter {
    let kb = crate::common::try_load_kb_prepared(PROGRAM, |kb| {
        kb.register_host_fn("w2858g_bounce", 1, |interp, args| {
            interp.call("test.w2858g.inner", args)
        })
        .expect("register w2858g_bounce");
        kb.register_host_fn("w2858g_bounce_twice", 1, |interp, args| {
            interp.call("test.w2858g.continued", args)
        })
        .expect("register w2858g_bounce_twice");
        kb.register_host_fn("w2858g_bounce_raising", 1, |interp, args| {
            interp.call("test.w2858g.innerRaises", args)
        })
        .expect("register w2858g_bounce_raising");
    })
    .unwrap_or_else(|errs| panic!("the fixture must load: {errs:#?}"));
    let mut interp = Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    interp
}

#[track_caller]
fn int_answer(interp: &mut Interpreter, op: &str, n: i64) -> i64 {
    let v = interp
        .call(op, &[Value::Int(n)])
        .unwrap_or_else(|e| panic!("{op}({n}) must answer: {e:?}"));
    v.literal_int64(interp.kb())
        .unwrap_or_else(|| panic!("{op}({n}) must answer an Int64, got {v:?}"))
}

/// THE CONTROL: the host function called from the host's top level, with no anthill frame
/// beneath it. Passes with the fix and without — it is what says the host function itself
/// is right, so the rows below measure the frame beneath and nothing else.
#[test]
fn the_control_a_top_level_host_call_re_enters_cleanly() {
    let mut interp = interp();
    assert_eq!(int_answer(&mut interp, "test.w2858g.Host.bounce", 2), 42);
}

/// THE ACCEPTANCE, in tail position: `tail(2)` is the host call and nothing after it.
#[test]
fn a_host_call_in_tail_position_re_enters_and_answers() {
    let mut interp = interp();
    assert_eq!(int_answer(&mut interp, "test.w2858g.tail", 2), 42);
}

/// THE ACCEPTANCE, with work after the host call: `43` needs the caller's `let` to have
/// RESUMED with the nested call's answer — the frame the old delivery overran.
#[test]
fn a_host_call_mid_body_re_enters_and_the_caller_resumes() {
    let mut interp = interp();
    assert_eq!(int_answer(&mut interp, "test.w2858g.continued", 2), 43);
}

/// Two nested runs deep, each with a caller to resume: `twice` → host → `continued` →
/// host → `inner`. Each run must stop at ITS OWN floor, not the outermost one's.
#[test]
fn nested_re_entry_two_levels_deep_answers() {
    let mut interp = interp();
    assert_eq!(int_answer(&mut interp, "test.w2858g.twice", 2), 44);
}

/// Nothing is left behind: after a re-entrant call the stack is EMPTY. Read directly
/// because a run now ends at its own floor, so a leftover frame would not make the next
/// call fault — it would sit beneath it silently.
#[test]
fn a_re_entrant_call_leaves_no_frame_behind() {
    let mut interp = interp();
    assert_eq!(int_answer(&mut interp, "test.w2858g.continued", 2), 43);
    assert_eq!(interp.activation_depth(), 0, "the first call left a frame");
    assert_eq!(int_answer(&mut interp, "test.w2858g.continued", 5), 46);
    assert_eq!(interp.activation_depth(), 0, "the second call left a frame");
}

/// The host call resumed through a call ARGUMENT, an `if` CONDITION and a `match` GUARD —
/// each a different wait-state in `deliver` from the `let` the rows above use. The `0`
/// answers are the controls that the condition and the guard really read the value.
#[test]
fn a_host_call_resumes_through_argument_condition_and_guard() {
    let mut interp = interp();
    assert_eq!(int_answer(&mut interp, "test.w2858g.inArgument", 2), 43);
    assert_eq!(int_answer(&mut interp, "test.w2858g.inCondition", 2), 1);
    assert_eq!(int_answer(&mut interp, "test.w2858g.inCondition", 0), 0);
    assert_eq!(int_answer(&mut interp, "test.w2858g.inGuard", 2), 1);
    assert_eq!(int_answer(&mut interp, "test.w2858g.inGuard", 0), 0);
}

/// A NESTED CALL SPENDS THE OUTER RUN'S BUDGET. `spin` never ends, and every pass makes a
/// re-entrant host call; each `interp.call` used to reset `step_count`, so under a
/// `step_cap` the loop never reached it. It must stop with `StepsExhausted`.
///
/// ON A THREAD WITH A TIMEOUT, because the failure this row exists for is a HANG: without
/// the timeout a regression would stall the whole test binary rather than fail one row.
#[test]
fn a_loop_of_re_entrant_calls_still_exhausts_the_step_cap() {
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let mut interp = interp();
        interp.config_mut().step_cap = Some(20_000);
        let outcome = match interp.call("test.w2858g.spin", &[Value::Int(1)]) {
            Err(EvalError::StepsExhausted { .. }) => Ok(()),
            other => Err(format!("expected StepsExhausted, got {other:?}")),
        };
        let _ = tx.send(outcome);
    });
    match rx.recv_timeout(std::time::Duration::from_secs(120)) {
        Ok(Ok(())) => {}
        Ok(Err(why)) => panic!("{why}"),
        Err(_) => panic!("spin did not stop within 120s: a nested call is resetting the step budget"),
    }
}

/// A RAISE crosses the nested run and is caught by the OUTER run's `Error.reify`. The
/// raise path already stopped at the nested run's floor before this ticket (proposal
/// 027.4's `run` truncates to it on error), so this row is a control for the fix NOT
/// having moved raises — it must not start catching inside the nested run or lose the
/// payload.
#[test]
fn a_raise_inside_the_nested_call_reaches_the_outer_boundary() {
    let mut interp = interp();
    let r = interp
        .call("test.w2858g.caughtAcross", &[])
        .unwrap_or_else(|e| panic!("the outer boundary must catch it: {e:?}"));
    let kb = interp.kb();
    let arm = crate::common::entity_functor(kb, &r).map(|s| kb.qualified_name_of(s).to_string());
    assert_eq!(arm.as_deref(), Some("anthill.prelude.Result.err"), "got {r:?}");
    let payload = crate::common::entity_field(kb, &r, "error", 0);
    let why = crate::common::entity_field(kb, &payload, "why", 0);
    assert_eq!(
        crate::common::scalar_str(kb, &why).as_deref(),
        Some("raised inside the nested call")
    );
}

/// An uncaught raise inside the nested call, WITH an anthill frame beneath the host call,
/// surfaces to the host as that raise — not as the delivery fault, not swallowed — and
/// leaves nothing of either run behind, so the interpreter answers the next call.
#[test]
fn an_uncaught_raise_inside_the_nested_call_reaches_the_host() {
    let mut interp = interp();
    match interp.call("test.w2858g.uncaughtAcross", &[Value::Int(0)]) {
        Err(EvalError::Raised { .. }) => {}
        other => panic!("expected the raise itself, got {other:?}"),
    }
    assert_eq!(interp.activation_depth(), 0, "the raise left a frame behind");
    assert_eq!(int_answer(&mut interp, "test.w2858g.continued", 2), 43);
}
