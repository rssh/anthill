//! WI-20261027-WGJFN — A HOST'S `Error` HANDLER IS HANDED THE RAISE'S TYPE VALUE, AND WHAT IT
//! RAISES CARRIES ONE (user, 2026-10-27). The handler (proposal 027's `Error[T]` entry: one
//! that logs and re-raises) was written before a raise carried its type (proposal 071 §1.3),
//! so its throw was a raise of the unknown type: a handler that logged and re-raised made
//! `Error.reify[T1 = Boom]` miss its own `Boom`, and the raise left an operation the typer read
//! as raising nothing.
//!
//! Now the handler is handed `[payload, type_value]`, the `TypeValue` dictionary the raise
//! carries, and answers `Throw(value, type_value)`. The throw is applied where the raise's
//! type admits it, by the test a boundary runs; otherwise the run stops with a
//! `HandlerError` (`ThrowNotAdmitted`) naming both values and both types — no raise, and not
//! the old value in its place.
//!
//! ── WHICH ROWS FAIL WHEN EACH PART IS BACKED OUT ── measured 2026-10-27, each alone, over
//! this file and the rows it re-pointed (5CDN5, 9WVT7's reify, 8Y5BE, SPGBP, 0QV5A, eval) ──
//!
//! * The type value handed to the handler (`raise_typed`): here
//!   `the_handler_is_handed_the_raise_s_type_value`,
//!   `a_re_raise_at_the_type_value_it_was_handed_is_caught`,
//!   `a_value_of_the_raise_s_type_replaces_it`; and every re-pointed handler that reads
//!   `args[1]` (eval_test's wi467 and wi610, 0QV5A, 8Y5BE, SPGBP).
//! * The throw raised at the type value it gives, where it was raised at the unknown type:
//!   here `a_re_raise_at_the_type_value_it_was_handed_is_caught`,
//!   `a_value_of_the_raise_s_type_replaces_it`,
//!   `a_value_the_raise_s_type_does_not_admit_is_refused`; 5CDN5's
//!   `an_error_handler_that_rethrows_keeps_the_raise_s_type` and
//!   `a_host_raise_carries_the_type_its_caller_threads`.
//! * The admission test (`admitted_throw`): here
//!   `a_value_the_raise_s_type_does_not_admit_is_refused`; 5CDN5's two above and
//!   `an_error_handler_raising_its_own_value_through_err_is_refused`; 9WVT7's
//!   `a_clock_handler_s_throw_is_refused_where_now_declares_no_error`.
//! * A raise leaving a handler through its `Err` channel held to the raise point:
//!   5CDN5's `an_error_handler_raising_its_own_value_through_err_is_refused`.
//! * An operation whose row declares no `Error` admitting nothing
//!   (`HostRaiseType::NoErrorLabel`): 9WVT7's clock row; and, for a host function's own raise
//!   there (`host_raised_type`), 5CDN5's `a_host_raise_carries_the_type_its_caller_threads`.
//! * `Fail` answered to a raise refused as not yet supported:
//!   `a_fail_from_the_error_handler_is_not_yet_supported`.
//!
//! PASS EITHER WAY BY DESIGN: `a_rethrow_is_caught`, the control a logging handler that
//! answers `Rethrow` gives; `a_re_raise_through_err_is_caught`, a raise at the raise's own
//! type through either route; and `a_rethrow_from_a_handler_of_another_effect_is_refused`,
//! whose answer was refused before as an unsupported action.

use anthill_core::eval::dictionary::Dictionary;
use anthill_core::eval::effects::HandlerAction;
use anthill_core::eval::{EvalError, HandlerErrorReason, Interpreter, Value};
use std::cell::RefCell;
use std::rc::Rc;

const PROGRAM: &str = r#"
namespace test.wgjfn
  import anthill.prelude.{Int64, String, Error, Result}
  import anthill.prelude.Result.{ok, err}
  sort Boom
    entity boom(why: String)
  end
  sort Fatal
    entity fatal(code: Int64)
  end
  operation mayFail(n: Int64) -> Int64 effects {Error[Boom]} = Error.raise(boom(why: "x"))
  operation c(n: Int64) -> String =
    match Error.reify[T1 = Boom](lambda () -> mayFail(n))
      case ok(_) -> "ok"
      case err(e) -> e.why
  operation logged() -> Boom = boom(why: "x [logged]")
  operation mkFatal() -> Fatal = fatal(code: 1)
end
"#;

fn interp_with_error_handler(
    handler: impl FnMut(&mut Interpreter, &[Value]) -> Result<HandlerAction, EvalError> + 'static,
) -> Interpreter {
    let mut interp = crate::common::interp_for(PROGRAM);
    let mut handler = handler;
    interp
        .register_effect_handler("anthill.prelude.Error", Box::new(move |i, _op, args| handler(i, args)))
        .expect("register an Error handler");
    interp
}

fn type_value_arg(interp: &Interpreter, args: &[Value]) -> Dictionary {
    let arg = args.get(1).unwrap_or_else(|| panic!("no type value beside the payload: {args:?}"));
    Dictionary::from_value(interp.kb(), arg).unwrap_or_else(|| panic!("not a type value: {arg:?}"))
}

fn c(interp: &mut Interpreter) -> Result<String, EvalError> {
    interp
        .call("test.wgjfn.c", &[Value::Int(1)])
        .map(|v| crate::common::scalar_str(interp.kb(), &v).expect("c answers a String"))
}

/// The handler is handed the payload and the `TypeValue` dictionary of `Boom`, the type the
/// raise was made at (`mayFail`'s `Error[Boom]`).
#[test]
fn the_handler_is_handed_the_raise_s_type_value() {
    let seen: Rc<RefCell<Vec<String>>> = Rc::new(RefCell::new(Vec::new()));
    let sink = Rc::clone(&seen);
    let mut interp = interp_with_error_handler(move |i, args| {
        let type_value = type_value_arg(i, args);
        sink.borrow_mut().push(i.kb().qualified_name_of(type_value.impl_sort()).to_string());
        Ok(HandlerAction::Rethrow)
    });
    assert_eq!(c(&mut interp).expect("caught"), "x");
    assert_eq!(*seen.borrow(), vec!["test.wgjfn.Boom".to_string()]);
}

/// CONTROL: a handler that logs and answers `Rethrow` leaves the raise to the boundary.
#[test]
fn a_rethrow_is_caught() {
    let mut interp = interp_with_error_handler(|_i, _args| Ok(HandlerAction::Rethrow));
    assert_eq!(c(&mut interp).expect("caught"), "x");
}

/// A re-raise of the payload at the type value it was handed is the raise it was: the
/// boundary at `Boom` catches it. Raised at the unknown type, it left `c`.
#[test]
fn a_re_raise_at_the_type_value_it_was_handed_is_caught() {
    let mut interp = interp_with_error_handler(|i, args| {
        let type_value = type_value_arg(i, args);
        Ok(HandlerAction::Throw(args[0].clone(), type_value))
    });
    assert_eq!(c(&mut interp).expect("caught"), "x");
}

/// A value of the raise's own type replaces it, at the type value it was handed or at the
/// one the interpreter reads off the value (`Interpreter::type_value_of`).
#[test]
fn a_value_of_the_raise_s_type_replaces_it() {
    let mut interp = interp_with_error_handler(|i, args| {
        let type_value = type_value_arg(i, args);
        let logged = i.call("test.wgjfn.logged", &[])?;
        Ok(HandlerAction::Throw(logged, type_value))
    });
    assert_eq!(c(&mut interp).expect("caught"), "x [logged]");

    let mut interp = interp_with_error_handler(|i, _args| {
        let logged = i.call("test.wgjfn.logged", &[])?;
        let type_value = i.type_value_of(&logged)?;
        Ok(HandlerAction::Throw(logged, type_value))
    });
    assert_eq!(c(&mut interp).expect("caught"), "x [logged]");
}

/// A `Fatal` thrown for a raise at `Boom` is refused: the boundary at `Boom` would not catch
/// it, and `c` is typed as raising nothing. The run stops with a `HandlerError` naming both
/// values and both types; no raise leaves `c`.
#[test]
fn a_value_the_raise_s_type_does_not_admit_is_refused() {
    let mut interp = interp_with_error_handler(|i, _args| {
        let fatal = i.call("test.wgjfn.mkFatal", &[])?;
        let type_value = i.type_value_of(&fatal)?;
        Ok(HandlerAction::Throw(fatal, type_value))
    });
    match c(&mut interp) {
        Err(
            err @ EvalError::HandlerError {
                reason: HandlerErrorReason::ThrowNotAdmitted { .. },
                ..
            },
        ) => {
            let text = err.to_string();
            for part in [
                "the `anthill.prelude.Error` handler answered a raise of boom(why: \"x\") at `Boom`",
                "with a throw of fatal(code: 1) at `Fatal`",
                "which `Boom` does not admit",
            ] {
                assert!(text.contains(part), "missing {part:?} in: {text}");
            }
        }
        other => panic!("a Fatal thrown for a Boom is refused; got {other:?}"),
    }
}

/// A re-raise through the handler's `Err` channel — it calls `Error.raise` itself, which reads
/// the type off the payload — is held to the raise it answered as a `Throw` is, and admitted.
#[test]
fn a_re_raise_through_err_is_caught() {
    let mut interp = interp_with_error_handler(|i, args| {
        Err(i
            .call("anthill.prelude.Error.raise", &[args[0].clone()])
            .expect_err("a raise returns no value"))
    });
    assert_eq!(c(&mut interp).expect("caught"), "x");
}

/// `Fail` answered by the `Error` handler is an action the runtime cannot honor yet.
#[test]
fn a_fail_from_the_error_handler_is_not_yet_supported() {
    let mut interp = interp_with_error_handler(|_i, _args| Ok(HandlerAction::Fail(Value::Str("no".into()))));
    match c(&mut interp) {
        Err(EvalError::HandlerError {
            reason: HandlerErrorReason::NotYetSupported { action, .. },
            ..
        }) => assert_eq!(action, "Fail"),
        other => panic!("a Fail answered to a raise is refused; got {other:?}"),
    }
}

/// A value that does not pin its type has no type value to read off: an empty list, whose
/// element type nothing states.
#[test]
fn a_value_that_does_not_pin_its_type_has_no_type_value() {
    let mut interp = crate::common::interp_for(PROGRAM);
    let empty = interp.build_list_value(vec![], &[]).expect("an empty list");
    match interp.type_value_of(&empty) {
        Err(EvalError::RaiseTypeUnread { detail }) => {
            assert!(detail.starts_with("no type value can be read off"), "{detail}")
        }
        other => panic!("an empty list pins no type; got {other:?}"),
    }
}

/// `Rethrow` from a handler of another effect: it answers no raise.
#[test]
fn a_rethrow_from_a_handler_of_another_effect_is_refused() {
    let mut interp = crate::common::interp_for(PROGRAM);
    interp
        .register_effect_handler(
            "anthill.prelude.Time.Clock",
            Box::new(|_i, _op, _args| Ok(HandlerAction::Rethrow)),
        )
        .expect("register a Clock handler");
    let now = interp.kb().try_resolve_symbol("anthill.prelude.Time.now").expect("now");
    match interp.invoke_effect_handler("anthill.prelude.Time.Clock", now, &[]) {
        Err(EvalError::HandlerError {
            reason: HandlerErrorReason::NoRaiseToRethrow,
            op,
            ..
        }) => assert_eq!(op, "anthill.prelude.Time.now"),
        other => panic!("a Clock handler's Rethrow is refused; got {other:?}"),
    }
}
