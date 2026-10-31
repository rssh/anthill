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
//!       `ok` / `err` is the run's value. The payload's `TypePattern` evidence is the one the
//!       typer stamped on the call (`ErrorTag` until WI-20261016-YM8HD). Entering the
//!       thunk is the run's FIRST STEP (`run_from`),
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
//!   (d) A PATTERN SLOT A RULE BODY CANNOT FILL IS REFUSED (user, 2026-10-15). With no
//!       evidence the boundary has no pattern to catch by and refuses to run — it caught
//!       every payload, including the `Error[Other]` its thunk's row leaves to the caller,
//!       until the second review of this ticket — and a rule-body call's slot is no
//!       condition its clause can be handed (until 060's S7, WI-20260911-5G28A). The typer
//!       refuses the call at load (`build_op_scoped_dicts`) when the call builds no
//!       evidence — a payload type that is a rule variable's or none, a tuple. (A collection
//!       whose element is open is a pattern open there since proposal 071 stage (e); its
//!       raise is refused first.) Since WI-20261016-YM8HD the slot is `TypePattern`'s, a
//!       spec with a member, so the refusal is the rule-body gate's for every such spec (a
//!       tuple getting the structural former's account, as in an operation body); until
//!       then it was `ErrorTag`'s, a marker spec, refused by a gate keyed on its name. A
//!       generic operation that reifies at its own `P` and is cited from a rule whose
//!       arguments do not pin `P` reaches the boundary with no evidence, and the boundary
//!       refuses to run.
//!
//! WHAT FAILS UNDER WHICH BACK-OUT — MEASURED, each switched off alone in one build:
//!
//!   * (a) backed out → `a_rule_body_reify_catches_the_raise`,
//!     `a_rule_body_reify_waits_for_its_argument`, `a_payload_the_boundary_declines_is_a_fault`
//!     and `the_advised_repairs_answer` (no solutions, no fault); outside this file, the rows
//!     that reach a scoped load through a rule-body reify (`wi_9wvt7_bridged_scoped_kb_test`).
//!   * (b) backed out → the first three, `the_advised_repairs_answer` and
//!     `an_unpinned_host_entry_is_refused_and_leaves_no_frame`: the bridge is asked and answers
//!     no body; outside this file, the scoped-KB row that loads through a rule-body reify and
//!     `wi_9wvt7_error_reify_test::evidence_that_names_no_payload_sort_is_refused`.
//!   * (b)'s first step backed out — an error from entering the thunk returned past the run,
//!     as the host entry first did → `an_unpinned_host_entry_is_refused_and_leaves_no_frame`
//!     (the boundary's frame is left on the stack).
//!   * (c) is reached by no source program since proposal 071 stage (e): a rule-body
//!     boundary over labels of two sorts is refused (`a_rule_body_boundary_over_two_sorts_is_refused`),
//!     and its term writes no bracket to decline one (WI-20261024-TC54R).
//!   * (d)'s load refusal backed out (measured on the `ErrorTag` gate, before
//!     WI-20261016-YM8HD) → `an_unfilled_pattern_slot_is_refused_where_it_is_written`: its
//!     programs load clean, and `either(7, 7, ?r)` is undecided at every query, the boundary
//!     refusing to run with no evidence.
//!   * the boundary's refusal of no evidence backed out (the boundary installed, catching
//!     nothing) → `an_unpinned_host_entry_is_refused_and_leaves_no_frame`. A rule body no
//!     longer reaches the boundary with no evidence: since proposal 071 stage (d) the raise in
//!     its thunk requires the payload's `TypeValue` and is refused at load first
//!     (`a_generic_catcher_cited_from_a_rule_is_refused_at_its_raise`), where until then
//!     `useA` reached the boundary and raised past it under this back-out. Until
//!     WI-20261016-YM8HD the bridge kept the slot as an absence marker for both, read by a
//!     gate keyed on `ErrorTag`; that refusal named the unpinned slot, and this one names
//!     the two routes that hand none.
//!
//! The rows that reached an effectful thunk through a rule-body reify (`printing`, and the
//! clock routes of `wi_9wvt7_clock_handler_test`) are refused at load since WI-20261013-R1W5A,
//! and were taken off the lists above by that, not by running the back-outs again: no reify of
//! an effectful thunk is left for (a), (b) or an unhandled effect scheduled again to reach. The
//! last is measured on the clock file's run-time rows.
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
    import anthill.reflect.{TypeValue}
    import test.rrb.{Boom}
    entity host
    -- A host operation that raises requires the `TypeValue` of what it raises (proposal
    -- 071 §1.3), threaded by its caller as every requirement is.
    operation boomNow() -> Int64 effects {Error[Boom]} requires TypeValue[T = Boom] @[host_implemented]
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

/// A RULE-BODY BOUNDARY OVER LABELS OF TWO SORTS IS REFUSED (proposal 071 §7 Q1, decided with
/// the user 2026-10-27): no one pattern heads `Boom` and `Other`, nor `Boom` and `LoadFailed`,
/// and a rule's own term writes no bracket to say which it catches (WI-20261024-TC54R), so the
/// refusal says to write the boundary in an operation the rule calls. Until then `T1` was the
/// first label that paired, and the other was a fault of the goal naming the boundary's reason
/// — (c) above, which a rule-body boundary reaches again once its term writes the bracket.
///
/// THE ADVISED REPAIR ANSWERS: the boundary at `Boom` in an operation the rule calls catches
/// `boom("negative")`, and the `Other` past it is a fault of the goal.
///
/// FAILS with the boundary's pattern read off one label (`fix_boundary_patterns` backed out):
/// both clauses load, `T1` the first label.
#[test]
fn a_rule_body_boundary_over_two_sorts_is_refused() {
    for clause in [
        "rule declined(?r) :- Error.reify(lambda () -> twoWays(7), ?r)",
        "rule declinedLoad(?r) :- Error.reify(lambda () -> loadOrBoom(1), ?r)",
    ] {
        let src = crate::common::replace_in_fixture(PROGRAM, "\nend\n", &format!("\n  {clause}\nend\n"));
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&src),
            &["which no one sort heads", "in an operation the rule calls"],
            clause,
        );
    }
    let src = crate::common::replace_in_fixture(
        PROGRAM,
        "\nend\n",
        "\n  operation atBoom(n: Int64) -> Result[E = Boom, T = Int64] effects {Error[Other]} =
    Error.reify[T1 = Boom](lambda () -> twoWays(n))
  rule viaOperation(?n, ?r) :- atBoom(?n, ?r)
  rule viaOperationNeg(?r) :- viaOperation(0 - 1, ?r)
  rule viaOperationPos(?r) :- viaOperation(7, ?r)
end\n",
    );
    let mut kb = crate::common::load_kb_with(&src);
    let r = crate::common::one_definite(&mut kb, "test.rrb.viaOperationNeg");
    assert_eq!(caught_boom(&kb, &r), "negative");
    let errors = faults(&mut kb, "test.rrb.viaOperationPos");
    assert!(
        errors.iter().any(|e| e.contains("raised other(n: 7)")),
        "the `Other` past the operation's boundary is a fault of the goal: {errors:?}"
    );
}

/// A thunk with another effect (`ConsoleOutput`) is refused at load, naming the effect
/// (WI-20261013-R1W5A): the reify's row is its thunk's past the caught `Error`, and a rule
/// body performs no effect. Before, the goal was undecided at run time, the print not
/// performed; before (a), refuted.
///
/// No run-time twin: a thunk reaches a rule body's `Error.reify` at run time only as a closure
/// value, one a clause reads the type of where it is made, and a closure handed to another
/// relation through its head answers nothing (reported to the user, 2026-10-23).
#[test]
fn an_effectful_thunk_is_refused_at_load() {
    for clause in [
        "rule printing(?r) :- Error.reify(lambda () -> printThenBoom(), ?r)",
        "rule printingWritten(?r: Result[T = Int64, E = Boom]) :- Error.reify(lambda () -> printThenBoom(), ?r)",
    ] {
        let src = crate::common::replace_in_fixture(PROGRAM, "\nend\n", &format!("\n  {clause}\nend\n"));
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&src),
            &["Error.reify", "performs `ConsoleOutput`, and a rule body performs no effect"],
            clause,
        );
    }
}

/// A HOST CALL whose pattern slot its arguments do not pin is refused where the boundary
/// takes its pattern, before the thunk is entered: an operation reference carries no type
/// the bridge's pinning reads (it views as the runtime sort `OpRef`, not as its arrow), so
/// no slot is derived, as at a rule body's generic catcher below. The refusal leaves no
/// frame behind — entering is the run's first step, read by the loop, so the run truncates
/// to its floor — and the interpreter answers its next call.
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
        Err(e @ anthill_core::eval::EvalError::ReifyPayloadUnread { .. }) => {
            assert!(e.to_string().contains("its caller had none to hand"), "{e}")
        }
        other => panic!("the unpinned payload is refused at the boundary, got {other:?}"),
    }
    assert_eq!(interp.activation_depth(), 0, "the refused entry leaves no frame");
    let v = interp
        .call("test.rrb.fortyTwo", &[])
        .expect("the interpreter answers its next call");
    assert_eq!(crate::common::scalar_int(interp.kb(), &v), Some(42));
}

/// The shapes whose pattern slot the call builds no evidence for, each its own load so one
/// refusal cannot stand for another.
const UNFILLED_PATTERN_PROGRAMS: [(&str, &str); 6] = [
    (
        "a rule variable's type beside a second label",
        r#"
namespace test.rrbo
  import anthill.reflect.{TypeValue}
  import anthill.prelude.{Int64, String, Error, Result}
  sort Other
    entity other(n: Int64)
  end
  operation raiseEither[P](p: P, n: Int64) -> Int64 effects {Error[P], Error[Other]}
      requires TypeValue[T = P] =
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
        "a collection whose element is open",
        r#"
namespace test.rrbo
  import anthill.reflect.{TypeValue}
  import anthill.prelude.{Int64, String, Error, Result, List}
  import anthill.prelude.List.{nil}
  sort Other
    entity other(n: Int64)
  end
  operation raiseEither[P](p: P, n: Int64) -> Int64 effects {Error[P], Error[Other]}
      requires TypeValue[T = P] =
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
  operation raiseTup(n: Int64) -> Int64 effects {Error[(Int64, Int64)]} = Error.raise((n, n))
  rule tupWide(?r) :- Error.reify(lambda () -> raiseTup(7), ?r)
end
"#,
    ),
    (
        "a spec as the payload",
        r#"
namespace test.rrbo
  import anthill.prelude.{Error, Int64, Result}
  sort Shape
    sort T = ?
    operation area(s: T) -> Int64
  end
  -- A provision makes `Shape` a spec, which has no `TypeValue`: with none, it is a sort like
  -- another, and the pattern `Shape[T = ?]` is answered, its slot open (proposal 071 §1.6).
  sort Sq
    entity sq(side: Int64)
    provides Shape[T = Sq]
    operation area(s: Sq) -> Int64 = 4
  end
  operation declaresShape() -> Int64 effects {Error[Shape]} = 1
  rule specPayload(?r) :- Error.reify(lambda () -> declaresShape(), ?r)
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
];

/// A rule-body call whose pattern slot it builds no evidence for is refused where it is
/// written — AT THE RAISE, where the thunk raises at a type the clause leaves open (proposal
/// 071 stage (d)): the raising call requires the `TypeValue` of that type, which the clause
/// pins as little as the pattern, and is refused first (the rule variable's shapes, the open
/// collection). A tuple is refused at both. Where the thunk raises nothing open — a spec as
/// the payload, no `Error` label — the refusal is the pattern's. The boundary catches by that evidence, and with none it refuses to run, so the
/// call can never answer: with (d)'s load refusal backed out the programs load and
/// `either(7, 7, ?r)` is undecided at every query. Before the boundary refused to run with
/// no evidence it caught every payload, and `either(7, 7, ?r)` answered `err(other(n: 7))`,
/// the `Other` the thunk's row leaves to the caller.
///
/// THE ACCOUNT IS THE RULE-BODY GATE'S, the one any spec with a member gets, where the call
/// leaves an element open (WI-20261016-YM8HD). "Pin the element at this call" is not a
/// bracket — a rule-body goal reads none — but a payload whose type the clause knows, which
/// `the_advised_repairs_answer` drives. Where the call pins every element it is the account
/// an operation body gives: a tuple, the structural former's; a spec, which has no `TypeValue`,
/// that no row of `TypePattern` answers. A collection whose element is open is refused at its
/// raise, the pattern open there answered since proposal 071 stage (e). FAILS
/// with the rule-body gate's two pinned arms backed out: those three shapes are told "this
/// call pins no element".
#[test]
fn an_unfilled_pattern_slot_is_refused_where_it_is_written() {
    for (shape, src) in UNFILLED_PATTERN_PROGRAMS {
        let errs = crate::common::load_errors_of(src);
        assert!(!errs.is_empty(), "{shape}: refused, got a clean load");
        let wants: &[&str] = if shape == "a tuple" {
            &[
                "anthill.reflect.TypeValue[T = (_1: Int64, _2: Int64)]",
                "anthill.reflect.TypePattern[T = (_1: Int64, _2: Int64)]",
                "a STRUCTURAL FORMER",
                "Name a sort with no tuple or arrow among its type arguments",
            ]
        } else if shape.starts_with("a rule variable's type") {
            &[
                "anthill.reflect.TypeValue[T = ",
                "nothing in the clause determines which `anthill.reflect.TypeValue` instance",
                "Pin the element at this call",
            ]
        } else if shape == "a collection whose element is open" {
            &[
                "anthill.reflect.TypeValue[T = anthill.prelude.List]",
                "no row of `anthill.reflect.TypeValue` answers here, and none may be written",
            ]
        } else if shape == "a spec as the payload" {
            &[
                "anthill.reflect.TypePattern[T = ",
                "no row of `anthill.reflect.TypePattern` answers here, and none may be written",
                "for an `Error.reify`, raise a value of one in the thunk",
            ]
        } else {
            &[
                "anthill.reflect.TypePattern[T = ",
                "nothing in the clause determines which `anthill.reflect.TypePattern` instance",
                "Pin the element at this call",
            ]
        };
        crate::common::assert_refused_naming(&errs, wants, shape);
    }
}

/// A GENERIC operation that reifies at its own `P` (`requires TypePattern[T = P]`), cited from
/// a rule whose arguments do not pin `P`, IS REFUSED AT LOAD, AT THE RAISE (proposal 071 stage
/// (d)): the thunk calls `raiseEither(?p, ?n)`, whose `requires TypeValue[T = P]` nothing in
/// the clause pins. Until stage (d) both clauses loaded; `useA` reached the boundary with no
/// evidence, refused there, and `eitherW` had the bridge pin `P` from `?p`'s value as it ran.
/// With the payload a constructor's value the clause pins `P`, and the boundary narrows: the
/// `Other` passes it, the `Boom` is caught.
const GENERIC_CATCHER: &str = r#"
namespace test.rrbg
  import anthill.reflect.{TypeValue}
  import anthill.prelude.{Int64, String, Error, Result}
  import anthill.reflect.{TypePattern}
  sort Boom
    entity boom(why: String)
  end
  sort Other
    entity other(n: Int64)
  end
  operation raiseEither[P](p: P, n: Int64) -> Int64 effects {Error[P], Error[Other]}
      requires TypeValue[T = P] =
    if n < 0 then Error.raise(p) else Error.raise(other(n))
  operation catchAll[P, R](body: () -> Int64 @ {Error[P], R}) -> Result[E = P, T = Int64]
      effects {R} requires TypePattern[T = P] =
    Error.reify(body)
  operation catchWith[P, R](p: P, body: () -> Int64 @ {Error[P], R}) -> Result[E = P, T = Int64]
      effects {R} requires TypePattern[T = P] =
    Error.reify(body)
  rule eitherA(?p, ?n, ?r) :- catchAll(lambda () -> raiseEither(?p, ?n), ?r)
  rule eitherW(?p, ?n, ?r) :- catchWith(?p, lambda () -> raiseEither(?p, ?n), ?r)
end
"#;

#[test]
fn a_generic_catcher_cited_from_a_rule_is_refused_at_its_raise() {
    let errs = crate::common::load_errors_of(GENERIC_CATCHER);
    assert_eq!(errs.len(), 2, "one refusal per clause: {errs:#?}");
    // Each clause's own refusal, located at its line: the two are not one refusal reported
    // twice.
    for clause in ["rule eitherA", "rule eitherW"] {
        let line = GENERIC_CATCHER
            .lines()
            .position(|l| l.contains(clause))
            .map(|i| i + 1)
            .unwrap_or_else(|| panic!("`{clause}` is in the fixture"));
        let refusal = errs
            .iter()
            .find(|e| e.starts_with(&format!("{line}:")))
            .unwrap_or_else(|| panic!("{clause}: a refusal at line {line}: {errs:#?}"));
        for want in [
            "anthill.reflect.TypeValue[T = test.rrbg.raiseEither.P]",
            "nothing in the clause determines which `anthill.reflect.TypeValue` instance",
        ] {
            assert!(refusal.contains(want), "{clause}: expected {want:?}; got {refusal:?}");
        }
    }
    let pinned = crate::common::replace_in_fixture(
        GENERIC_CATCHER,
        "  rule eitherA(?p, ?n, ?r) :- catchAll(lambda () -> raiseEither(?p, ?n), ?r)\n  rule eitherW(?p, ?n, ?r) :- catchWith(?p, lambda () -> raiseEither(?p, ?n), ?r)\n",
        "  rule eitherB(?n, ?r) :- catchWith(boom(\"b\"), lambda () -> raiseEither(boom(\"b\"), ?n), ?r)\n  rule useW(?r) :- eitherB(7, ?r)\n  rule useWneg(?r) :- eitherB(0 - 1, ?r)\n",
    );
    let mut kb = crate::common::load_kb_with(&pinned);
    let errors = faults(&mut kb, "test.rrbg.useW");
    assert!(
        errors.iter().any(|e| e.contains("raised other(n: 7)")),
        "a pinned slot narrows, and the `Other` passes the boundary: {errors:?}"
    );
    let r = crate::common::one_definite(&mut kb, "test.rrbg.useWneg");
    let payload = crate::common::result_err_payload(&kb, &r);
    assert_eq!(crate::common::constructor_qn(&kb, &payload), "test.rrbg.Boom.boom");
}

/// The repairs the refusal names, each driven. "Pin the element at this call": the payload
/// raised as a value of a sort the call names — a constructor's, or a rule variable's whose
/// type is written — the thunk bound by a call whose result says what it raises, and an
/// operation written as a lambda that calls it. Named bare at the thunk, the operation is the
/// function value, as in an operation body (§5.4): `bareNamed` answers as `lambdaFixed` does,
/// where it was refused, read as its call. FAILS with the walk's mark of a name written alone
/// backed out.
///
/// THE THUNK A GOAL BINDS is typed by that goal's result column since WI-20261013-WF14Z:
/// `mkThunk(?f)` makes `?f` a `() -> Int64 @ {Error[Boom]}`, so the boundary reads `Boom`.
/// Read at no type, `viaVar` was one of the shapes refused for building no evidence. FAILS
/// with the result column read as no position (`LatePosition::ResultColumn`). And a payload
/// whose type the head writes (`withBound`'s `?p: Boom`) is read by the clause since that
/// ticket, where it was refused; FAILS with the head's bound read as no position.
const REPAIRS_PROGRAM: &str = r#"
namespace test.rrbr
  import anthill.reflect.{TypeValue}
  import anthill.prelude.{Int64, String, Error, Result}
  sort Boom
    entity boom(why: String)
  end
  sort Other
    entity other(n: Int64)
  end
  operation raiseAt[P](p: P) -> Int64 effects {Error[P]} requires TypeValue[T = P] = Error.raise(p)
  operation raiseNow() -> Int64 effects {Error[Boom]} = Error.raise(boom("now"))

  rule fixedBoom(?r) :- Error.reify(lambda () -> raiseAt(boom("b")), ?r)
  rule lambdaFixed(?r) :- Error.reify(lambda () -> raiseNow(), ?r)
  rule bareNamed(?r) :- Error.reify(raiseNow, ?r)

  operation mayFail(n: Int64) -> Int64 effects {Error[Boom]} =
    if n < 0 then Error.raise(boom("negative")) else n + 1
  operation mkThunk() -> () -> Int64 @ {Error[Boom]} = lambda () -> mayFail(0 - 1)
  rule viaVar(?r) :- mkThunk(?f), Error.reify(?f, ?r)
  rule withBound(?p: Boom, ?r) :- Error.reify(lambda () -> Error.raise(?p), ?r)
  rule boundPayload(?r) :- withBound(Boom.boom("w"), ?r)
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
    let r = crate::common::one_definite(&mut kb, "test.rrbr.bareNamed");
    assert_eq!(why(&kb, &r), "now");
    let r = crate::common::one_definite(&mut kb, "test.rrbr.viaVar");
    assert_eq!(why(&kb, &r), "negative");
    let r = crate::common::one_definite(&mut kb, "test.rrbr.boundPayload");
    assert_eq!(why(&kb, &r), "w");
}
