//! WI-20260908-9WVT7 / proposal 027.4 — `Error.reify` called from a RULE BODY.
//!
//! `rule direct(?r) :- Error.reify(lambda () -> mayFail(0 - 1), ?r)` answered no solutions,
//! silently, while the same call in an operation body caught. Proposal 068 says a rule-body
//! application is evaluated by the evaluator that runs operation bodies, with the same
//! dispatch; two places did not:
//!
//!   (a) THE RESOLVER DID NOT READ THE GOAL AS A CALL. Its functional-relation view
//!       (`f(a₁…aₙ, ?r)` read as `unify(?r, f(a₁…aₙ))`) admits an operation the bridge can
//!       run — a body or a host mapping — and a parametric effect row only for a bodied
//!       one; `Error.reify` has neither, so the goal went to candidate selection and found
//!       no clause. What the bridge runs for it is the thunk it is handed, as it runs a
//!       body, so `KnowledgeBase::bridge_runs_anthill_code` answers yes for it, and its row
//!       `{Rho}` is read as a body's. (The value-slot reduction needed nothing: its
//!       body-less arm already hands a clause-less `Error.reify` to the bridge.)
//!   (b) THE BRIDGE'S HOST ENTRY HAD NO BOUNDARY. A rule-body call reaches the evaluator
//!       through `invoke_op_with_requirements`, not through the two in-body dispatch faces
//!       that install `Error.reify`'s boundary, so it found no body
//!       (`OperationBodyMissing`). It now installs the boundary as they do: the one frame
//!       the run owns is the boundary, the thunk runs above it, and the boundary's
//!       `ok` / `err` is the run's value. The payload's `ErrorTag` evidence is the one the
//!       typer stamped on the call. Entering the thunk is the run's FIRST STEP (`run_from`),
//!       so a raise there meets the boundary as any later raise does.
//!   (c) THE FAULT NAMES THE BOUNDARY. A raise out of `Error.reify` itself is a payload its
//!       boundary declined, so the bridge's fault says that, instead of advising a `reify`
//!       around the call that is one.
//!   (d) A PAYLOAD TYPE THE CALL LEAVES OPEN IS REFUSED AT LOAD (user, 2026-10-15). With no
//!       `ErrorTag` evidence the boundary would catch every payload, and a rule can declare
//!       no `requires` through which a caller could pass it; until 060's S7 threads it
//!       (WI-20260911-5G28A), the typer's `build_op_scoped_dicts` refuses the call.
//!
//! WHAT FAILS UNDER WHICH BACK-OUT — MEASURED, each switched off alone in one build:
//!
//!   * (a) backed out → `a_rule_body_reify_catches_the_raise`,
//!     `a_rule_body_reify_waits_for_its_argument`, `a_payload_the_boundary_declines_is_a_fault`
//!     (no solutions, no fault) and `an_effectful_thunk_leaves_the_goal_undecided` (no
//!     solutions: the goal is refuted, not undecided).
//!   * (b) backed out → the first three and `a_raise_on_entering_the_thunk_meets_the_boundary`:
//!     the bridge is asked and answers no body, which leaves the goal undecided — so the
//!     effectful-thunk row passes under (b), by design.
//!   * (b)'s first step backed out — an error from entering the thunk returned past the
//!     boundary, as the host entry first did → `a_raise_on_entering_the_thunk_meets_the_boundary`.
//!   * (c) backed out → `a_payload_the_boundary_declines_is_a_fault` (the generic advice).
//!   * (d) backed out → `an_open_payload_type_is_refused_where_it_is_written`: all three of
//!     its programs load clean, and `either(boom("b"), 7, ?r)` answers `err(other(n: 7))`.
//!
//! PASSES EITHER WAY BY DESIGN: `the_advised_repairs_answer` (neither repair leaves the
//! payload type open), and `the_operation_body_twin_answers_the_same` — the call wrapped
//! in an operation, for a one-label thunk. (A two-label thunk is no twin: an operation that
//! reifies at `Boom` and leaves `Error[Other]` in its own row has a concrete row, and a
//! concrete row is never a relational view.)

use anthill_core::eval::Value;
use anthill_core::kb::resolve::ResolveConfig;

const PROGRAM: &str = r#"
namespace test.rrb
  import anthill.prelude.{Int64, String, Error, Result, ConsoleOutput}
  import anthill.prelude.Console.{console, println}

  sort Boom
    entity boom(why: String)
  end

  sort Other
    entity other(n: Int64)
  end

  operation mayFail(n: Int64) -> Int64 effects {Error[Boom]} =
    if n < 0 then Error.raise(boom("negative")) else n + 1

  operation twoWays(n: Int64) -> Int64 effects {Error[Boom], Error[Other]} =
    if n < 0 then Error.raise(boom("negative")) else Error.raise(other(n))

  operation printThenBoom() -> Int64 effects {ConsoleOutput, Error[Boom]} =
    let _ = println(console(), "a side effect")
    Error.raise(boom("printed"))

  operation caught() -> Result[E = Boom, T = Int64] = Error.reify(lambda () -> mayFail(0 - 1))

  rule direct(?r) :- Error.reify(lambda () -> mayFail(0 - 1), ?r)
  rule okArm(?r) :- Error.reify(lambda () -> mayFail(41), ?r)

  -- The thunk captures a variable the caller binds.
  rule later(?x, ?r) :- Error.reify(lambda () -> mayFail(?x), ?r)
  rule laterNeg(?r) :- later(0 - 1, ?r)
  rule laterPos(?r) :- later(5, ?r)

  -- `T1` is inferred as `Boom`, so the `Other` raised here is no payload of this boundary.
  rule declined(?r) :- Error.reify(lambda () -> twoWays(7), ?r)

  rule printing(?r) :- Error.reify(lambda () -> printThenBoom(), ?r)
  rule viaOperation(?r) :- caught(?r)
end
"#;

/// A host function that RAISES AS IT IS ENTERED, for the row below: `boomNow` is
/// host-implemented and nullary, so applying a reference to it raises before any anthill
/// frame of the thunk exists. Its own load, since the mapping needs the function
/// registered before the load.
const HOST_PROGRAM: &str = r#"
namespace test.rrb
  import anthill.prelude.{Int64, String, Error, Result}

  sort Boom
    entity boom(why: String)
  end

  operation raiseNow() -> Int64 effects {Error[Boom]} = Error.raise(boom("on entry"))

  sort Host
    import anthill.prelude.{Int64, Error}
    import test.rrb.{Boom}
    entity host
    operation boomNow() -> Int64 effects {Error[Boom]} @[host_implemented]
  end

  provides Host language rust
    artifact "nowhere.rs"
    operation_map {
      boomNow: "rrb_boom_now"
    }
  end
end
"#;

#[track_caller]
fn constructor(kb: &anthill_core::kb::KnowledgeBase, v: &Value) -> String {
    crate::common::entity_functor_qn(kb, v).unwrap_or_else(|| panic!("expected an entity, got {v:?}"))
}

/// The `why` of the `boom` an `err` arm carries.
#[track_caller]
fn caught_boom(kb: &anthill_core::kb::KnowledgeBase, result: &Value) -> String {
    assert_eq!(constructor(kb, result), "anthill.prelude.Result.err");
    let payload = crate::common::entity_field(kb, result, "error", 0);
    assert_eq!(constructor(kb, &payload), "test.rrb.Boom.boom");
    let why = crate::common::entity_field(kb, &payload, "why", 0);
    crate::common::scalar_str(kb, &why).expect("`why` is a String")
}

#[track_caller]
fn ok_value(kb: &anthill_core::kb::KnowledgeBase, result: &Value) -> i64 {
    assert_eq!(constructor(kb, result), "anthill.prelude.Result.ok");
    let v = crate::common::entity_field(kb, result, "value", 0);
    crate::common::scalar_int(kb, &v).expect("`value` is an Int64")
}

/// THE ACCEPTANCE. A rule body's `Error.reify` catches the raise and answers the `err` arm;
/// a thunk that returns answers the `ok` arm.
#[test]
fn a_rule_body_reify_catches_the_raise() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    let r = crate::common::one_definite(&mut kb, "test.rrb.direct");
    assert_eq!(caught_boom(&kb, &r), "negative");
    let r = crate::common::one_definite(&mut kb, "test.rrb.okArm");
    assert_eq!(ok_value(&kb, &r), 42);
}

/// The thunk's captured variable is bound by the calling goal: the call runs once it is.
#[test]
fn a_rule_body_reify_waits_for_its_argument() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    let r = crate::common::one_definite(&mut kb, "test.rrb.laterNeg");
    assert_eq!(caught_boom(&kb, &r), "negative");
    let r = crate::common::one_definite(&mut kb, "test.rrb.laterPos");
    assert_eq!(ok_value(&kb, &r), 6);
}

/// A payload the boundary is not typed at leaves it as the raise it is, and the goal reports
/// the fault — naming the boundary's reason rather than advising a `reify` around a call that
/// is one.
#[test]
fn a_payload_the_boundary_declines_is_a_fault() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    let goal = crate::common::query_pattern_term(&mut kb, "test.rrb.declined(?r)");
    let (sols, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    assert!(
        sols.iter().all(|s| !s.is_definite()),
        "no definite answer for a raise that escaped"
    );
    let errors: Vec<String> = stats.errors.iter().map(|e| e.message.clone()).collect();
    assert_eq!(errors.len(), 1, "one fault: {errors:?}");
    for token in [
        "raised other(n: 7)",
        "The boundary catches the payload it is typed at",
    ] {
        assert!(
            errors[0].contains(token),
            "the fault names `{token}`: {}",
            errors[0]
        );
    }
}

/// A thunk with another effect (`ConsoleOutput`) is not run to an answer: the bridge's
/// effect registry is empty, so the print is not performed and the goal stays UNDECIDED —
/// one answer, not definite. Before (a) the goal was refuted instead: no answer at all.
#[test]
fn an_effectful_thunk_leaves_the_goal_undecided() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    let rows = crate::common::query_unary(&mut kb, "test.rrb.printing");
    assert!(
        matches!(rows.as_slice(), [(_, false)]),
        "one answer, undecided: {rows:?}"
    );
}

/// A raise AS THE THUNK IS ENTERED meets the boundary. The boundary is installed before the
/// thunk is applied, so a reference to a host function that raises at once is caught as a
/// lambda's raise is — in an operation body by the trampoline's recovery, and at the host
/// entry by the same recovery, the entering being the run's first step. Driven from the
/// host (`Interpreter::call`), the one route that hands the boundary such a reference: a
/// source program reads a bare nullary name as its call.
#[test]
fn a_raise_on_entering_the_thunk_meets_the_boundary() {
    let kb = crate::common::try_load_kb_prepared(HOST_PROGRAM, |kb| {
        kb.register_host_fn("rrb_boom_now", 0, |interp, _| {
            interp.call("test.rrb.raiseNow", &[])
        })
        .expect("register rrb_boom_now");
    })
    .unwrap_or_else(|errs| panic!("the fixture must load: {errs:#?}"));
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    let op = interp
        .kb()
        .try_resolve_symbol("test.rrb.Host.boomNow")
        .expect("`boomNow` is declared");
    let thunk = Value::OpRef {
        op,
        dict: None,
        named: None,
        spread_labels: None,
        op_reqs: None,
    };
    let r = interp
        .call("anthill.prelude.Error.reify", &[thunk])
        .unwrap_or_else(|e| panic!("the boundary catches a raise on entry: {e}"));
    assert_eq!(caught_boom(interp.kb(), &r), "on entry");
}

/// The three shapes whose payload type the call leaves OPEN, each its own load so one
/// refusal cannot stand for another: the payload a rule variable's type, with a second label
/// in the thunk's row and with none, and a thunk bound by another goal.
const OPEN_PAYLOAD_PROGRAMS: [(&str, &str); 3] = [
    (
        "a rule variable's type beside a second label",
        r#"
namespace test.rrbo
  import anthill.prelude.{Int64, String, Error, Result}
  sort Other
    entity other(n: Int64)
  end
  operation raiseEither[P](p: P, n: Int64) -> Int64 effects {Error[P], Error[Other]} =
    if n < 0 then Error.raise(p) else Error.raise(other(n))
  rule either(?p, ?n, ?r) :- Error.reify(lambda () -> raiseEither(?p, ?n), ?r)
end
"#,
    ),
    (
        "a rule variable's type alone",
        r#"
namespace test.rrbo
  import anthill.prelude.{Error, Result}
  rule onlyP(?p, ?r) :- Error.reify(lambda () -> Error.raise(?p), ?r)
end
"#,
    ),
    (
        "a thunk bound by another goal",
        r#"
namespace test.rrbo
  import anthill.prelude.{Int64, String, Error, Result}
  sort Boom
    entity boom(why: String)
  end
  operation mayFail(n: Int64) -> Int64 effects {Error[Boom]} =
    if n < 0 then Error.raise(boom("negative")) else n + 1
  operation mkThunk() -> () -> Int64 @ {Error[Boom]} = lambda () -> mayFail(0 - 1)
  rule viaVar(?r) :- mkThunk(?f), Error.reify(?f, ?r)
end
"#,
    ),
];

/// A rule-body `Error.reify` whose PAYLOAD TYPE THE CALL LEAVES OPEN is refused where it is
/// written. The boundary reads what it catches out of the call's `ErrorTag` evidence, and
/// with none it catches every payload: before the refusal, `either(boom("b"), 7, ?r)`
/// answered `err(other(n: 7))` DEFINITELY, the `Other` its thunk's row leaves to the caller.
/// An operation in this position declares `requires ErrorTag[T = P]`; a rule cannot, so the
/// payload type must be fixed at the call. The one-label shape is refused too, though
/// catching wide would have answered it: nothing at the call tells the two apart.
///
/// MEASURED: the rule-body gate in `build_op_scoped_dicts` backed out, all three load clean.
#[test]
fn an_open_payload_type_is_refused_where_it_is_written() {
    for (shape, src) in OPEN_PAYLOAD_PROGRAMS {
        let errs = crate::common::load_errors_of(src);
        assert_eq!(errs.len(), 1, "{shape}: one refusal, got {errs:#?}");
        crate::common::assert_refused_naming(
            &errs,
            &[
                "anthill.prelude.ErrorTag[T = T1]",
                "its carrier is the payload type this `Error.reify` catches",
                "A rule declares no `requires`",
            ],
            shape,
        );
    }
}

/// The two repairs the refusal names, each driven. PASSES EITHER WAY BY DESIGN: neither
/// leaves the payload type open, so the refusal does not reach them.
const REPAIRS_PROGRAM: &str = r#"
namespace test.rrbr
  import anthill.prelude.{Int64, String, Error, Result, ErrorTag}
  sort Boom
    entity boom(why: String)
  end
  sort Other
    entity other(n: Int64)
  end
  operation raiseEither[P](p: P, n: Int64) -> Int64 effects {Error[P], Error[Other]} =
    if n < 0 then Error.raise(p) else Error.raise(other(n))
  operation raiseOnly[P](p: P) -> Int64 effects {Error[P]} = Error.raise(p)

  -- The thunk written so its payload sort is known at the call.
  rule eitherFixed(?n, ?r) :- Error.reify(lambda () -> raiseEither(boom("b"), ?n), ?r)
  rule fixedBoom(?r) :- eitherFixed(0 - 1, ?r)
  rule fixedOther(?r) :- eitherFixed(7, ?r)

  -- The reify inside an operation that declares the requirement.
  operation catchOnly[P](p: P) -> Result[E = P, T = Int64] requires ErrorTag[T = P] =
    Error.reify(lambda () -> raiseOnly(p))
  rule onlyViaOp(?p, ?r) :- catchOnly(?p, ?r)
  rule onlyViaOpUse(?r) :- onlyViaOp(boom("q"), ?r)
end
"#;

#[test]
fn the_advised_repairs_answer() {
    let mut kb = crate::common::load_kb_with(REPAIRS_PROGRAM);
    let boom = |kb: &anthill_core::kb::KnowledgeBase, r: &Value| {
        assert_eq!(constructor(kb, r), "anthill.prelude.Result.err");
        let payload = crate::common::entity_field(kb, r, "error", 0);
        let why = crate::common::entity_field(kb, &payload, "why", 0);
        crate::common::scalar_str(kb, &why).expect("`why` is a String")
    };
    let r = crate::common::one_definite(&mut kb, "test.rrbr.fixedBoom");
    assert_eq!(boom(&kb, &r), "b");
    let r = crate::common::one_definite(&mut kb, "test.rrbr.onlyViaOpUse");
    assert_eq!(boom(&kb, &r), "q");
    // The `Other` passes the boundary typed at `Boom`: no answer, and a fault.
    let goal = crate::common::query_pattern_term(&mut kb, "test.rrbr.fixedOther(?r)");
    let (sols, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    assert!(sols.iter().all(|s| !s.is_definite()), "no definite answer");
    assert!(
        stats.errors.iter().any(|e| e.message.contains("raised other(n: 7)")),
        "the declined raise is the fault: {:?}",
        stats.errors
    );
}

/// PASSES EITHER WAY BY DESIGN — the control: the same call inside an operation body.
#[test]
fn the_operation_body_twin_answers_the_same() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    let r = crate::common::one_definite(&mut kb, "test.rrb.viaOperation");
    assert_eq!(caught_boom(&kb, &r), "negative");
}
