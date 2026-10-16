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
//!       read by the loop as every step is: an error there leaves the run truncated to its
//!       floor, and a raise there would meet the boundary as any later raise does — though
//!       nothing reaches that with a payload the boundary can read: a source program reads a
//!       bare nullary name as its call and lifts no host-implemented operation to a value,
//!       and the host's `Interpreter::call` cannot pin the payload from an operation
//!       reference, which is the refusal `an_unpinned_host_entry_is_refused_and_leaves_no_frame`
//!       drives.
//!   (c) A RAISE OUT OF THE BOUNDARY IS A FAULT, NAMING IT. A payload the boundary declined
//!       is reported as a fault of the goal whatever it is — a `load_failed` too, which
//!       elsewhere means "no answer yet" — and the message names the boundary's reason
//!       instead of advising a `reify` around the call that is one.
//!   (d) AN `ErrorTag` SLOT A RULE BODY CANNOT FILL IS REFUSED (user, 2026-10-15). With no
//!       evidence the boundary would catch every payload, including the `Error[Other]` its
//!       thunk's row leaves to the caller, and a rule-body call's `ErrorTag` is no
//!       condition its clause can be handed (until 060's S7, WI-20260911-5G28A). The typer
//!       refuses the call at load (`build_op_scoped_dicts`) when the call builds no
//!       evidence — a payload type that is a rule variable's or none, a collection whose
//!       element is open, a tuple — and the bridge keeps an `ErrorTag` slot its arguments
//!       cannot pin as an absence the boundary's read refuses, for a generic operation that
//!       reifies at its own `P` and is cited from a rule.
//!
//! WHAT FAILS UNDER WHICH BACK-OUT — MEASURED, each switched off alone in one build:
//!
//!   * (a) backed out → `a_rule_body_reify_catches_the_raise`,
//!     `a_rule_body_reify_waits_for_its_argument`, `a_payload_the_boundary_declines_is_a_fault`,
//!     `the_advised_repairs_answer` (no solutions, no fault) and
//!     `an_effectful_thunk_leaves_the_goal_undecided` (no solutions: refuted, not undecided);
//!     outside this file, the rows that reach a clock read or a scoped load through a
//!     rule-body reify (`wi_9wvt7_clock_handler_test`, `wi_9wvt7_bridged_scoped_kb_test`).
//!   * (b) backed out → the first three, `the_advised_repairs_answer` and
//!     `an_unpinned_host_entry_is_refused_and_leaves_no_frame`: the bridge is asked and answers
//!     no body, which leaves the goal undecided — so the effectful-thunk row passes under (b);
//!     outside this file, the scoped-KB row that loads through a rule-body reify.
//!   * (b)'s first step backed out — an error from entering the thunk returned past the run,
//!     as the host entry first did → `an_unpinned_host_entry_is_refused_and_leaves_no_frame`
//!     (the boundary's frame is left on the stack).
//!   * (c) backed out → `a_payload_the_boundary_declines_is_a_fault` (the generic advice; the
//!     declined `load_failed` silent).
//!   * (d)'s load refusal backed out → `an_unfilled_error_tag_is_refused_where_it_is_written`:
//!     its programs load clean, and the bridge's absence faults `either(7, 7, ?r)` when it
//!     runs. With both of (d)'s halves backed out it answers `err(other(n: 7))`, definitely.
//!   * (d)'s bridge absence backed out → `a_generic_catcher_cited_from_a_rule_faults`
//!     (`err(other(n: 7))`, definite) and `an_unpinned_host_entry_is_refused_and_leaves_no_frame`
//!     (the boundary catches every payload).
//!
//! The operation-body twin of `direct` — the same reify in an operation the rule calls — is
//! `viaPlainRule` in `wi_9wvt7_error_reify_test::a_generic_boundary_answers_through_a_rule_body`.

use anthill_core::eval::Value;
use anthill_core::kb::resolve::ResolveConfig;

const PROGRAM: &str = r#"
namespace test.rrb
  import anthill.prelude.{Int64, String, Error, Result, ConsoleOutput, List}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Console.{console, println}
  import anthill.reflect.{KB, LoadFailed}

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

  -- Raises `Boom` below zero, else loads a source that does not parse.
  operation loadOrBoom(n: Int64) -> Int64 effects {Error[Boom], Error[LoadFailed]} =
    if n < 0 then Error.raise(boom("negative"))
    else
      let _ = KB.loaded(cons("namespace zz.bad fact Nope(", nil()))
      1

  rule direct(?r) :- Error.reify(lambda () -> mayFail(0 - 1), ?r)
  rule okArm(?r) :- Error.reify(lambda () -> mayFail(41), ?r)

  -- The thunk captures a variable the caller binds.
  rule later(?x, ?r) :- Error.reify(lambda () -> mayFail(?x), ?r)
  rule laterNeg(?r) :- later(0 - 1, ?r)
  rule laterPos(?r) :- later(5, ?r)

  -- `T1` is inferred as `Boom`, so the `Other` raised here is no payload of this boundary;
  -- nor is the `load_failed` a failed scoped load raises.
  rule declined(?r) :- Error.reify(lambda () -> twoWays(7), ?r)
  rule declinedLoad(?r) :- Error.reify(lambda () -> loadOrBoom(1), ?r)

  rule printing(?r) :- Error.reify(lambda () -> printThenBoom(), ?r)
end
"#;

/// A host function that would RAISE AS IT IS ENTERED, for the row below: `boomNow` is
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
  operation fortyTwo() -> Int64 = 42

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

/// The `why` of the `boom` an `err` arm carries.
#[track_caller]
fn caught_boom(kb: &anthill_core::kb::KnowledgeBase, result: &Value) -> String {
    let payload = crate::common::result_err_payload(kb, result);
    assert_eq!(crate::common::constructor_qn(kb, &payload), "test.rrb.Boom.boom");
    let why = crate::common::entity_field(kb, &payload, "why", 0);
    crate::common::scalar_str(kb, &why).expect("`why` is a String")
}

/// The fault messages `qn(?r)` records, with no definite answer beside them.
#[track_caller]
fn faults(kb: &mut anthill_core::kb::KnowledgeBase, qn: &str) -> Vec<String> {
    let goal = crate::common::query_pattern_term(kb, &format!("{qn}(?r)"));
    let (sols, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    assert!(
        sols.iter().all(|s| !s.is_definite()),
        "{qn}: no definite answer for a raise that escaped"
    );
    stats.errors.iter().map(|e| e.message.clone()).collect()
}

/// THE ACCEPTANCE. A rule body's `Error.reify` catches the raise and answers the `err` arm;
/// a thunk that returns answers the `ok` arm.
#[test]
fn a_rule_body_reify_catches_the_raise() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    let r = crate::common::one_definite(&mut kb, "test.rrb.direct");
    assert_eq!(caught_boom(&kb, &r), "negative");
    let r = crate::common::one_definite(&mut kb, "test.rrb.okArm");
    assert_eq!(crate::common::result_ok_int(&kb, &r), 42);
}

/// The thunk's captured variable is bound by the calling goal: the call runs once it is.
#[test]
fn a_rule_body_reify_waits_for_its_argument() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    let r = crate::common::one_definite(&mut kb, "test.rrb.laterNeg");
    assert_eq!(caught_boom(&kb, &r), "negative");
    let r = crate::common::one_definite(&mut kb, "test.rrb.laterPos");
    assert_eq!(crate::common::result_ok_int(&kb, &r), 6);
}

/// A payload the boundary is not typed at leaves it as the raise it is, and the goal reports
/// the fault — naming the boundary's reason rather than advising a `reify` around a call that
/// is one; a declined `load_failed` is such a fault too.
#[test]
fn a_payload_the_boundary_declines_is_a_fault() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    let errors = faults(&mut kb, "test.rrb.declined");
    assert_eq!(errors.len(), 1, "one fault: {errors:?}");
    for token in [
        "raised other(n: 7)",
        "The boundary catches the payload it is typed at",
    ] {
        assert!(errors[0].contains(token), "the fault names `{token}`: {}", errors[0]);
    }
    let errors = faults(&mut kb, "test.rrb.declinedLoad");
    assert!(
        errors.iter().any(|e| e.contains("raised load_failed")),
        "a declined load_failed is a fault: {errors:?}"
    );
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

/// A HOST CALL whose `ErrorTag` slot its arguments do not pin is refused where the boundary
/// reads its payload, before the thunk is entered: an operation reference carries no type
/// the bridge's pinning reads (it views as the runtime sort `OpRef`, not as its arrow), so
/// the slot is an absence, as at a rule body's generic catcher above, where the boundary
/// caught every payload. The refusal leaves no frame behind — entering is the run's first
/// step, read by the loop, so the run truncates to its floor — and the interpreter answers
/// its next call.
#[test]
fn an_unpinned_host_entry_is_refused_and_leaves_no_frame() {
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
    match interp.call("anthill.prelude.Error.reify", &[thunk]) {
        Err(e @ anthill_core::eval::EvalError::UnpinnedRequirement { .. }) => {
            assert!(e.to_string().contains("pins no provider"), "{e}")
        }
        other => panic!("the unpinned payload is refused at the boundary's read, got {other:?}"),
    }
    assert_eq!(interp.activation_depth(), 0, "the refused entry leaves no frame");
    let v = interp
        .call("test.rrb.fortyTwo", &[])
        .expect("the interpreter answers its next call");
    assert_eq!(crate::common::scalar_int(interp.kb(), &v), Some(42));
}

/// The shapes whose `ErrorTag` slot the call builds no evidence for, each its own load so
/// one refusal cannot stand for another.
const UNFILLED_ERROR_TAG_PROGRAMS: [(&str, &str); 7] = [
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
    (
        "a collection whose element is open",
        r#"
namespace test.rrbo
  import anthill.prelude.{Int64, String, Error, Result, List}
  import anthill.prelude.List.{nil}
  sort Other
    entity other(n: Int64)
  end
  operation raiseEither[P](p: P, n: Int64) -> Int64 effects {Error[P], Error[Other]} =
    if n < 0 then Error.raise(p) else Error.raise(other(n))
  rule eitherNil(?n, ?r) :- Error.reify(lambda () -> raiseEither(nil(), ?n), ?r)
end
"#,
    ),
    (
        "a tuple",
        r#"
namespace test.rrbo
  import anthill.prelude.{Int64, String, Error, Result}
  sort Other
    entity other(n: Int64)
  end
  operation raiseTup(n: Int64) -> Int64 effects {Error[(Int64, Int64)], Error[Other]} =
    if n < 0 then Error.raise((n, n)) else Error.raise(other(n))
  rule tupWide(?r) :- Error.reify(lambda () -> raiseTup(7), ?r)
end
"#,
    ),
    (
        "a thunk that raises no `Error` label",
        r#"
namespace test.rrbo
  import anthill.prelude.{Int64, Error, Result}
  operation pure(n: Int64) -> Int64 = n + 1
  rule pureThunk(?r) :- Error.reify(lambda () -> pure(1), ?r)
end
"#,
    ),
    (
        "an operation named bare, read as its call",
        r#"
namespace test.rrbo
  import anthill.prelude.{Int64, String, Error, Result}
  sort Boom
    entity boom(why: String)
  end
  operation raiseNow() -> Int64 effects {Error[Boom]} = Error.raise(boom("now"))
  rule bareRaise(?r) :- Error.reify(raiseNow, ?r)
end
"#,
    ),
];

/// A rule-body call whose `ErrorTag` slot it builds no evidence for is refused where it is
/// written. The boundary reads what it catches out of that evidence, and with none it catches
/// every payload: with both of (d)'s halves backed out, `either(7, 7, ?r)` answers
/// `err(other(n: 7))` DEFINITELY — the `Other` the thunk's row leaves to the caller. The
/// one-label shapes are refused too, though catching wide would answer them: nothing at the
/// call tells the two apart.
#[test]
fn an_unfilled_error_tag_is_refused_where_it_is_written() {
    for (shape, src) in UNFILLED_ERROR_TAG_PROGRAMS {
        let errs = crate::common::load_errors_of(src);
        assert!(!errs.is_empty(), "{shape}: refused, got a clean load");
        crate::common::assert_refused_naming(
            &errs,
            &[
                "anthill.prelude.ErrorTag[T = ",
                "its carrier is the payload sort an `Error.reify` boundary catches",
                "is no condition its clause can be handed",
            ],
            shape,
        );
    }
}

/// A GENERIC operation that reifies at its own `P` (`requires ErrorTag[T = P]`), cited from a
/// rule whose arguments do not pin `P`, has its slot kept as an absence the boundary's read
/// refuses: a fault, where the boundary caught every payload. With a value of `P` among the
/// arguments the bridge pins it and the boundary narrows.
const GENERIC_CATCHER: &str = r#"
namespace test.rrbg
  import anthill.prelude.{Int64, String, Error, Result, ErrorTag}
  sort Boom
    entity boom(why: String)
  end
  sort Other
    entity other(n: Int64)
  end
  operation raiseEither[P](p: P, n: Int64) -> Int64 effects {Error[P], Error[Other]} =
    if n < 0 then Error.raise(p) else Error.raise(other(n))
  operation catchAll[P, R](body: () -> Int64 @ {Error[P], R}) -> Result[E = P, T = Int64]
      effects {R} requires ErrorTag[T = P] =
    Error.reify(body)
  operation catchWith[P, R](p: P, body: () -> Int64 @ {Error[P], R}) -> Result[E = P, T = Int64]
      effects {R} requires ErrorTag[T = P] =
    Error.reify(body)
  rule eitherA(?p, ?n, ?r) :- catchAll(lambda () -> raiseEither(?p, ?n), ?r)
  rule useA(?r) :- eitherA(boom("b"), 7, ?r)
  rule eitherW(?p, ?n, ?r) :- catchWith(?p, lambda () -> raiseEither(?p, ?n), ?r)
  rule useW(?r) :- eitherW(boom("b"), 7, ?r)
  rule useWneg(?r) :- eitherW(boom("b"), 0 - 1, ?r)
end
"#;

#[test]
fn a_generic_catcher_cited_from_a_rule_faults() {
    let mut kb = crate::common::load_kb_with(GENERIC_CATCHER);
    let errors = faults(&mut kb, "test.rrbg.useA");
    assert!(
        errors.iter().any(|e| e.contains("pins no provider")),
        "the unpinned slot is refused at its read: {errors:?}"
    );
    let errors = faults(&mut kb, "test.rrbg.useW");
    assert!(
        errors.iter().any(|e| e.contains("raised other(n: 7)")),
        "a pinned slot narrows, and the `Other` passes the boundary: {errors:?}"
    );
    let r = crate::common::one_definite(&mut kb, "test.rrbg.useWneg");
    let payload = crate::common::result_err_payload(&kb, &r);
    assert_eq!(crate::common::constructor_qn(&kb, &payload), "test.rrbg.Boom.boom");
}

/// The repairs the refusal names, each driven: the payload raised as a value of a sort the
/// call names, and an operation named bare written as a lambda that calls it.
const REPAIRS_PROGRAM: &str = r#"
namespace test.rrbr
  import anthill.prelude.{Int64, String, Error, Result}
  sort Boom
    entity boom(why: String)
  end
  sort Other
    entity other(n: Int64)
  end
  operation raiseEither[P](p: P, n: Int64) -> Int64 effects {Error[P], Error[Other]} =
    if n < 0 then Error.raise(p) else Error.raise(other(n))
  operation raiseNow() -> Int64 effects {Error[Boom]} = Error.raise(boom("now"))

  rule eitherFixed(?n, ?r) :- Error.reify(lambda () -> raiseEither(boom("b"), ?n), ?r)
  rule fixedBoom(?r) :- eitherFixed(0 - 1, ?r)
  rule fixedOther(?r) :- eitherFixed(7, ?r)
  rule lambdaFixed(?r) :- Error.reify(lambda () -> raiseNow(), ?r)
end
"#;

#[test]
fn the_advised_repairs_answer() {
    let mut kb = crate::common::load_kb_with(REPAIRS_PROGRAM);
    let why = |kb: &anthill_core::kb::KnowledgeBase, r: &Value| {
        let payload = crate::common::result_err_payload(kb, r);
        let why = crate::common::entity_field(kb, &payload, "why", 0);
        crate::common::scalar_str(kb, &why).expect("`why` is a String")
    };
    let r = crate::common::one_definite(&mut kb, "test.rrbr.fixedBoom");
    assert_eq!(why(&kb, &r), "b");
    let r = crate::common::one_definite(&mut kb, "test.rrbr.lambdaFixed");
    assert_eq!(why(&kb, &r), "now");
    // The `Other` passes the boundary typed at `Boom`: no answer, and a fault.
    let errors = faults(&mut kb, "test.rrbr.fixedOther");
    assert!(
        errors.iter().any(|e| e.contains("raised other(n: 7)")),
        "the declined raise is the fault: {errors:?}"
    );
}
