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
//! the source ran over a scratch interpreter with no handler and no symbols, and asked for
//! its operation's symbol before its handler. It asks for the handler first now, so the
//! refusal is the same whatever order the files load in.
//!
//! AND THE DECLINE IS REPORTED (user, 2026-10-16). Scheduled, it left a bare residual with
//! nothing said, and a drain of the relation from an operation body died
//! `relation_floundered`, which reads as an unbound variable; now each route records a
//! fault naming `anthill.prelude.Time.Clock`, and the drain fails with that reason.
//!
//! WHAT FAILS UNDER WHICH BACK-OUT — MEASURED, each switched off alone in one build:
//!
//!   * `time_now` put back to reading the clock itself → every row that reads it:
//!     `a_clock_read_in_a_rule_body_is_not_performed` (four definite timestamps),
//!     `a_declined_clock_read_is_reported`, the three drained rows and the three other
//!     refuted-branch rows (nothing is declined),
//!     `an_operation_reads_the_clock_through_its_handler` and
//!     `a_clock_const_in_an_operation_body_reads_the_handler` (the frozen handler is not
//!     asked), and both data-slot rows (the const reads the wall clock at load).
//!   * `dispatch_effect_operation` made to resolve the operation before it takes the
//!     handler, as the dispatcher did → `a_clock_const_in_a_data_slot_is_refused_naming_clock`
//!     and `a_clock_const_in_a_data_slot_is_refused_naming_clock_ahead_of_the_stdlib`
//!     ("internal evaluator error: anthill.prelude.Time.now not in scope": the scratch
//!     interpreter a load runs the source on has an empty KB).
//!   * an unhandled effect scheduled again, as it was → `a_declined_clock_read_is_reported`
//!     (no fault), `a_drained_relation_names_the_declined_effect` (`relation_floundered`),
//!     `a_drain_reached_from_a_rule_names_the_effect_and_no_reify` (a floundered drain is
//!     no fault, so the outer goal reports nothing), and the four refuted-branch rows:
//!     `a_branch_refuted_after_a_declined_effect_is_incomplete` (complete),
//!     `a_negation_over_a_declined_effect_is_conditional` (definite),
//!     `a_drain_over_a_refuted_branch_fails_naming_the_effect` (it drains to `0`) and
//!     `a_constraint_over_a_declined_effect_does_not_load` (it loads). Their `testFirst`
//!     halves are the controls, which pass under every back-out here.
//!   * the drain's `evaluation_failure` given the `Error.reify` repair again →
//!     `a_drain_reached_from_a_rule_names_the_effect_and_no_reify`.
//!
//! PASSES UNDER ALL BUT THE FIRST, BY DESIGN: `a_clock_const_in_an_operation_body_reads_the_handler`.

use anthill_core::eval::effects::{EffectHandler, HandlerAction};
use anthill_core::eval::{EvalError, Value};
use anthill_core::kb::term_view::TermView;

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

  -- A relation over the clock read, drained from an operation body, and that operation
  -- called from a rule.
  operation stampCount() -> Int64 effects {Error} = List.length(viaHof.takeN(10))
  rule countFromRule(?n) :- ?n <=> stampCount()
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

/// And reached from a rule through the operation that drains it, the drain's failure carries
/// that fault's sentence and gets no `Error.reify` advice of its own: a declined effect is
/// not one a reify repairs.
#[test]
fn a_drain_reached_from_a_rule_names_the_effect_and_no_reify() {
    use anthill_core::kb::resolve::ResolveConfig;
    let mut kb = crate::common::load_kb_with(PROGRAM);
    let goal = crate::common::query_pattern_term(&mut kb, "test.clock.countFromRule(?n)");
    let (_, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    let messages: Vec<&str> = stats.errors.iter().map(|e| e.message.as_str()).collect();
    assert!(
        messages.iter().any(|m| m.contains("`test.clock.stampCount` could not be evaluated")
            && m.contains("it performs `anthill.prelude.Time.Clock`")),
        "the outer fault carries the declined effect: {messages:?}"
    );
    assert!(
        messages.iter().all(|m| !m.contains("Error.reify")),
        "no reify is advised for it: {messages:?}"
    );
}

/// A DECLINED EFFECT IS A FAULT, AND A FAULT MARKS THE WHOLE SEARCH INCOMPLETE from the moment
/// the goal is first tried — so a branch a later goal refutes is incomplete too, and the
/// verdict follows the goal order (user, 2026-10-16: kept as decided, the third review's F2).
/// A raise behaves so already. `effectFirst` tries the clock read before `?n > 100` refutes the
/// branch; `testFirst`, the control in every row below, refutes it first.
const REFUTED_AFTER_THE_EFFECT: &str = r#"
namespace test.clockrefuted
  import anthill.prelude.{Int64, String, List, Error}
  import anthill.prelude.Time.{now, Clock}
  sort Rec
    entity rec(n: Int64)
  end
  fact rec(n: 1)
  operation applyThunk[Rho](f: () -> String @ {Rho}) -> String effects {Rho} = f()
  rule effectFirst(?n) :- rec(n: ?n), applyThunk(lambda () -> now(), ?s), ?n > 100
  rule testFirst(?n) :- rec(n: ?n), ?n > 100, applyThunk(lambda () -> now(), ?s)
  rule notEffectFirst(?n) :- rec(n: ?n), not(effectFirst(?n))
  rule notTestFirst(?n) :- rec(n: ?n), not(testFirst(?n))
  operation countEffectFirst() -> Int64 effects {Error} = List.length(effectFirst.takeN(10))
  operation countTestFirst() -> Int64 effects {Error} = List.length(testFirst.takeN(10))
end
"#;

/// The refuted branch answers nothing, and the search says it is incomplete.
#[test]
fn a_branch_refuted_after_a_declined_effect_is_incomplete() {
    use anthill_core::kb::resolve::ResolveConfig;
    let mut kb = crate::common::load_kb_with(REFUTED_AFTER_THE_EFFECT);
    for (qn, incomplete) in [
        ("test.clockrefuted.effectFirst", true),
        ("test.clockrefuted.testFirst", false),
    ] {
        let goal = crate::common::query_pattern_term(&mut kb, &format!("{qn}(?n)"));
        let (solutions, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
        assert!(solutions.is_empty(), "{qn}: refuted, got {} answers", solutions.len());
        assert_eq!(stats.truncated, incomplete, "{qn}: incomplete");
    }
}

/// A negation over it is conditional, where the control's is definite.
#[test]
fn a_negation_over_a_declined_effect_is_conditional() {
    let mut kb = crate::common::load_kb_with(REFUTED_AFTER_THE_EFFECT);
    let rows = crate::common::query_unary(&mut kb, "test.clockrefuted.notEffectFirst");
    assert!(matches!(rows.as_slice(), [(_, false)]), "one answer, conditional: {rows:?}");
    let rows = crate::common::query_unary(&mut kb, "test.clockrefuted.notTestFirst");
    assert!(
        matches!(rows.as_slice(), [(v, true)] if v.literal_int64(&kb) == Some(1)),
        "the control: ?n = 1, definite: {rows:?}"
    );
}

/// A relation drained from an operation body fails with the declined effect's reason, where
/// the control drains to an empty list.
#[test]
fn a_drain_over_a_refuted_branch_fails_naming_the_effect() {
    let mut interp = crate::common::interp_for(REFUTED_AFTER_THE_EFFECT);
    match interp.call("test.clockrefuted.countEffectFirst", &[]) {
        Err(EvalError::Raised { payload }) => {
            let reason = crate::common::entity_field(interp.kb(), &payload, "reason", 1);
            let reason = crate::common::scalar_str(interp.kb(), &reason)
                .unwrap_or_else(|| panic!("a reason String, got {payload:?}"));
            assert!(
                reason.contains("it performs `anthill.prelude.Time.Clock`"),
                "the drain names the effect: {reason}"
            );
        }
        other => panic!("the drain fails, got {other:?}"),
    }
    let v = interp
        .call("test.clockrefuted.countTestFirst", &[])
        .expect("the control drains");
    assert_eq!(v.literal_int64(interp.kb()), Some(0));
}

/// A quantified constraint over it cannot be decided, and the program does not load; over the
/// control it loads.
#[test]
fn a_constraint_over_a_declined_effect_does_not_load() {
    let with = |constraint: &str| {
        REFUTED_AFTER_THE_EFFECT.replace("\nend\n", &format!("\n  {constraint}\nend\n"))
    };
    let errs = crate::common::load_errors_of(&with(
        "constraint c_effect_first: no ?n: rec(n: ?n) -: effectFirst(?n)",
    ));
    crate::common::assert_refused_naming(
        &errs,
        &[
            "integrity constraint 'c_effect_first' is undecidable within the resolver depth budget",
            "it performs `anthill.prelude.Time.Clock`",
        ],
        "a constraint over a declined effect",
    );
    crate::common::load_kb_with(&with(
        "constraint c_test_first: no ?n: rec(n: ?n) -: testFirst(?n)",
    ));
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
            "host value source \"time_now\" performs `anthill.prelude.Time.Clock`, and a load \
             performs no effect",
        ],
        "a clock-sourced const in a fact",
    );
    assert!(
        errs.iter().all(|e| !e.contains("internal evaluator error")),
        "the cause is the effect, not the evaluator: {errs:?}"
    );
}

/// And whatever order the files load in: the program handed to the loader BEFORE the
/// stdlib, in one call, where no file declaring `Time.now` has converted when the fact does.
#[test]
fn a_clock_const_in_a_data_slot_is_refused_naming_clock_ahead_of_the_stdlib() {
    // NOT THE RECIPE, BY NAME (WI-20261008-RAH0Z): the recipe hands the loader the stdlib
    // first — in the one call, or in a call of its own — and the subject here is the
    // program ordered BEFORE it in ONE call.
    let program = anthill_core::parse::parse(CONST_IN_FACT).expect("parse the program");
    let mut files = vec![&program];
    files.extend(crate::common::stdlib_parsed());
    let mut kb = anthill_core::kb::KnowledgeBase::new();
    let errs: Vec<String> = match anthill_core::kb::load::load_all(
        &mut kb,
        &files,
        &anthill_core::kb::load::NullResolver,
    ) {
        Ok(_) => Vec::new(),
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    };
    crate::common::assert_refused_naming(
        &errs,
        &[
            "is written in a data slot",
            "host value source \"time_now\" performs `anthill.prelude.Time.Clock`, and a load \
             performs no effect",
        ],
        "a clock-sourced const in a fact, the program first",
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
