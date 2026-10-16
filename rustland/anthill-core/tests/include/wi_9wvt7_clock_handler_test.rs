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
//! A `const_map` value source is a host function too, and `time_now` named as one reads
//! the clock when the const is forced. In an operation body that is through the handler, as
//! above; a clause data slot asks for the value at LOAD, where no effect is performed, and
//! the refusal names the effect (user, 2026-10-16) where it read as an internal error —
//! the source ran over a scratch interpreter with no handler and no symbols.
//!
//! AND THE DECLINE IS REPORTED (user, 2026-10-16). Scheduled, it left a bare residual with
//! nothing said, and a drain of the relation from an operation body died
//! `relation_floundered`, which reads as an unbound variable; now each route records a
//! fault naming `anthill.prelude.Time.Clock`, and the drain fails with that reason.
//!
//! WHAT FAILS UNDER THE BACK-OUT — MEASURED: `time_now` put back to reading the clock itself
//! → `a_clock_read_in_a_rule_body_is_not_performed` (four definite timestamps) and
//! `an_operation_reads_the_clock_through_its_handler` (the frozen handler is not asked);
//! `host_source_effect` taken out of `const_slot_value` →
//! `a_clock_const_in_a_data_slot_is_refused_naming_clock` ("internal evaluator error:
//! anthill.prelude.Time.now not in scope"); an unhandled effect scheduled again, as it
//! was → `a_declined_clock_read_is_reported` (no fault) and
//! `a_drained_relation_names_the_declined_effect` (`relation_floundered`). PASSES EITHER
//! WAY BY DESIGN: `a_clock_const_in_an_operation_body_reads_the_handler`.

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

  -- A relation over the clock read, drained from an operation body.
  operation stampCount() -> Int64 effects {Error} = List.length(viaHof.takeN(10))
end
"#;

/// The rule-body routes to a clock read.
const ROUTES: [&str; 4] = [
    "test.clock.viaReify",
    "test.clock.viaHof",
    "test.clock.viaMap",
    "test.clock.inValueSlot",
];

/// A `Clock` that always answers `stamp`.
fn frozen_clock(stamp: &'static str) -> EffectHandler {
    Box::new(move |_interp, _op, _args| Ok(HandlerAction::Pure(Value::Str(stamp.to_string()))))
}

/// THE DEFECT. Four rule-body routes to a clock read: each is undecided — one answer, not
/// definite — where each answered the wall clock.
#[test]
fn a_clock_read_in_a_rule_body_is_not_performed() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    for qn in ROUTES {
        let rows = crate::common::query_unary(&mut kb, qn);
        assert!(
            matches!(rows.as_slice(), [(_, false)]),
            "{qn}: one answer, undecided: {rows:?}"
        );
    }
}

/// THE DECLINE IS REPORTED: each route records a fault naming the effect, which marks the
/// search incomplete, where it left a bare residual with nothing said.
#[test]
fn a_declined_clock_read_is_reported() {
    use anthill_core::kb::resolve::ResolveConfig;
    let mut kb = crate::common::load_kb_with(PROGRAM);
    for qn in ROUTES {
        let goal = crate::common::query_pattern_term(&mut kb, &format!("{qn}(?r)"));
        let (_, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
        assert!(
            stats.errors.iter().any(|e| e
                .message
                .contains("it performs `anthill.prelude.Time.Clock`, and a rule body performs no effect")),
            "{qn}: the declined read is named: {:?}",
            stats.errors
        );
    }
}

/// And a relation drained from an operation body fails with that reason, where it died
/// `relation_floundered(goals: …)`.
#[test]
fn a_drained_relation_names_the_declined_effect() {
    let mut interp = crate::common::interp_for(PROGRAM);
    match interp.call("test.clock.stampCount", &[]) {
        Err(EvalError::Raised { payload }) => {
            let reason = crate::common::entity_field(interp.kb(), &payload, "reason", 1);
            let reason = crate::common::scalar_str(interp.kb(), &reason)
                .unwrap_or_else(|| panic!("a reason String, got {payload:?}"));
            assert!(
                reason.contains("it performs `anthill.prelude.Time.Clock`"),
                "the drain names the effect: {reason}"
            );
        }
        other => panic!("the drain fails naming the effect, got {other:?}"),
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

/// A const whose value source is `time_now`, named in a clause data slot.
const CONST_IN_FACT: &str = r#"
namespace test.clockconst
  import anthill.prelude.{String}
  sort Stamp
    import anthill.prelude.{String}
    const buildStamp: String
  end
  provides Stamp language rust
    artifact "nowhere.rs"
    const_map {
      buildStamp: "time_now"
    }
  end
  sort Rec
    entity rec(at: String)
  end
  fact rec(at: Stamp.buildStamp)
end
"#;

/// The same const read in an operation body.
const CONST_IN_BODY: &str = r#"
namespace test.clockconst
  import anthill.prelude.{String}
  sort Stamp
    import anthill.prelude.{String}
    const buildStamp: String
  end
  provides Stamp language rust
    artifact "nowhere.rs"
    const_map {
      buildStamp: "time_now"
    }
  end
  operation stamp() -> String = Stamp.buildStamp
end
"#;

#[test]
fn a_clock_const_in_a_data_slot_is_refused_naming_clock() {
    let errs = crate::common::load_errors_of(CONST_IN_FACT);
    crate::common::assert_refused_naming(
        &errs,
        &[
            "is written in a data slot",
            "host value source \"time_now\" is `anthill.prelude.Time.now`'s host function, \
             which performs `anthill.prelude.Time.Clock`, and a load performs no effect",
        ],
        "a clock-sourced const in a fact",
    );
    assert!(
        errs.iter().all(|e| !e.contains("internal evaluator error")),
        "the cause is the effect, not the evaluator: {errs:?}"
    );
}

/// PASSES EITHER WAY BY DESIGN: an operation body folds the const when it runs, through the
/// handler the interpreter registers.
#[test]
fn a_clock_const_in_an_operation_body_reads_the_handler() {
    let mut interp = crate::common::interp_for(CONST_IN_BODY);
    interp
        .register_effect_handler("anthill.prelude.Time.Clock", frozen_clock("2000-01-01T00:00:00Z"))
        .expect("register a frozen Clock");
    let v = interp.call("test.clockconst.stamp", &[]).expect("the const is read when it runs");
    assert_eq!(
        crate::common::scalar_str(interp.kb(), &v).as_deref(),
        Some("2000-01-01T00:00:00Z")
    );
}
