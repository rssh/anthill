//! WI-20260908-9WVT7 (found by its review) — `Time.now` READ THE WALL CLOCK DIRECTLY, so a
//! rule body read it too.
//!
//! The SLD→eval bridge evaluates a rule-body call with an EMPTY effect registry, and that is
//! what keeps an effect out of resolution: an operation that reaches one raises, and the goal
//! is undecided (kernel-language.md, the relational views). `Time.now` was a host function
//! that answered the clock itself, asking no handler, so it RAN: `applyThunk(lambda () ->
//! now(), ?r)`, `List.mapElems` with a clock callback, a bodied `{Clock}` operation in a value
//! slot, and since rule-body `Error.reify` a thunk reading the clock, each answered a
//! DEFINITE timestamp — a different answer at each query. `Time.now` now reads `Clock`
//! through the handler the runtime registers (`effects::system_clock_handler`), as the
//! `Console` operations read theirs, so a rule body cannot read it and the goal is undecided.
//!
//! WHAT FAILS UNDER THE BACK-OUT — MEASURED: `time_now` put back to reading the clock itself
//! → `a_clock_read_in_a_rule_body_is_not_performed` (four definite timestamps) and
//! `an_operation_reads_the_clock_through_its_handler` (the frozen handler is not asked).

use anthill_core::eval::effects::{EffectHandler, HandlerAction};
use anthill_core::eval::{EvalError, Value};

const PROGRAM: &str = r#"
namespace test.clock
  import anthill.prelude.{Int64, String, Error, Result, List}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Time.{now, Clock}

  sort Boom
    entity boom(why: String)
  end

  operation stampOr(n: Int64) -> String effects {Clock, Error[Boom]} =
    if n < 0 then Error.raise(boom("negative")) else now()
  operation plainStamp() -> String effects {Clock} = now()
  operation applyThunk[Rho](f: () -> String @ {Rho}) -> String effects {Rho} = f()

  rule viaReify(?r) :- Error.reify(lambda () -> stampOr(1), ?r)
  rule viaHof(?r) :- applyThunk(lambda () -> now(), ?r)
  rule viaMap(?r) :- List.mapElems(cons(1, nil()), lambda (x) -> now(), ?r)
  rule inValueSlot(?r) :- ?r <=> plainStamp()
end
"#;

/// A `Clock` that always answers `stamp`.
fn frozen_clock(stamp: &'static str) -> EffectHandler {
    Box::new(move |_interp, _op, _args| Ok(HandlerAction::Pure(Value::Str(stamp.to_string()))))
}

/// THE DEFECT. Four rule-body routes to a clock read: each is undecided — one answer, not
/// definite — where each answered the wall clock.
#[test]
fn a_clock_read_in_a_rule_body_is_not_performed() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    for qn in [
        "test.clock.viaReify",
        "test.clock.viaHof",
        "test.clock.viaMap",
        "test.clock.inValueSlot",
    ] {
        let rows = crate::common::query_unary(&mut kb, qn);
        assert!(
            matches!(rows.as_slice(), [(_, false)]),
            "{qn}: one answer, undecided: {rows:?}"
        );
    }
}

/// An operation reads the clock through the handler its interpreter registers — a frozen one
/// here, so the answer is the handler's — and with none registered the read is refused
/// loudly, as an unhandled effect.
#[test]
fn an_operation_reads_the_clock_through_its_handler() {
    let mut interp = crate::common::interp_for(PROGRAM);
    match interp.call("test.clock.plainStamp", &[]) {
        Err(EvalError::UnhandledEffect { name, .. }) => {
            assert_eq!(name, "anthill.prelude.Time.Clock")
        }
        other => panic!("no Clock handler: an unhandled effect, got {other:?}"),
    }
    interp
        .register_effect_handler("anthill.prelude.Time.Clock", frozen_clock("2000-01-01T00:00:00Z"))
        .expect("register a frozen Clock");
    let v = interp
        .call("test.clock.plainStamp", &[])
        .expect("the frozen clock answers");
    assert_eq!(
        crate::common::scalar_str(interp.kb(), &v).as_deref(),
        Some("2000-01-01T00:00:00Z")
    );
}
