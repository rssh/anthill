//! WI-20261016-5CDN5 (proposal 071 stage (d)) — A RAISE CARRIES ITS TYPE, and the boundary
//! admits by the whole type. Delivers WI-20260911-3MV2C.
//!
//! `Error.raise` requires `TypeValue[T = T]`, and the raised error travels with that
//! evidence (`RaisedType::Evidence`); a boundary asks its pattern's `admits` about the type
//! the evidence names, arguments and all, where until this stage it asked about the raised
//! value's head sort. A raising host operation requires the `TypeValue` of what it raises,
//! threaded to it by its caller as every requirement is, and is refused at load without the
//! clause (`LoadError::HostRaiseWithoutTypeValue`); a payload the runtime raises with no
//! operation behind it — a pattern that fails, a stream pulled — carries its sort's constant
//! (`ErrorLayer`). What the host function of a row that says only `Error` (`Error[T = ?]`)
//! raises carries the unknown type (`RaisedType::Unknown`): only a boundary whose pattern is
//! `?` catches it, and every other boundary lets it pass outward (the throwing-handler row of
//! `wi_9wvt7_error_reify_test`). Decided with the user, 2026-10-24.
//!
//! ── WHICH ROWS FAIL WHEN EACH PART IS BACKED OUT ── measured 2026-10-24, each alone ──
//!
//! * The raised type read as the payload's head sort, as stage (c) read it
//!   (`Interpreter::raised_type_value`): `nested_box_boundaries_answer_by_the_type_argument`,
//!   `a_generic_raiser_threads_the_type_of_its_payload`, `a_reflected_result_is_raised_at_its_type`,
//!   `a_host_raise_carries_the_type_its_caller_threads`,
//!   `an_error_handler_that_rethrows_keeps_the_raise_s_type`, and
//!   `wi_ym8hd_reify_type_pattern_test::a_boundary_reads_the_type_the_raise_carries` — each
//!   answers through the INNER boundary. Their two-distinct-sorts controls pass either way by
//!   design, as do the rows catching a payload of a sort with no type parameter (division,
//!   `match`).
//! * The `Error` handler's `Rethrow` typed as unknown (`Interpreter::raise_typed`):
//!   `an_error_handler_that_rethrows_keeps_the_raise_s_type`,
//!   `a_raise_holding_a_closure_is_caught_under_the_standard_handlers`. The default handler
//!   answering `Throw` of the payload instead of `Rethrow`: the second.
//! * A raise of unknown type answered as a type every pattern admits (`raised_type_value`):
//!   `an_error_handler_raising_its_own_value_raises_the_unknown_type`, the second half of
//!   `an_error_handler_that_rethrows_keeps_the_raise_s_type`, and
//!   `wi_9wvt7_error_reify_test::a_narrowed_boundary_does_not_steal_a_raise_of_unknown_type`.
//! * The `Error` handler run with the invoking builtin's channel (`run_handler`):
//!   `an_error_handler_raising_its_own_value_raises_the_unknown_type`. Another handler's
//!   `Throw` typed as unknown instead of by the operation it performs:
//!   `a_host_raise_carries_the_type_its_caller_threads` (`nestedT`).
//! * The runtime's accounts raised at the unknown type (`RaiseBy::Account`):
//!   `a_failed_match_is_caught_at_its_sort`.
//! * The load rule (`check_host_raise_types`): `a_host_operation_that_raises_states_what_it_raises`;
//!   so do a bare `Error` not counted beside a written label and the sort-level clause not
//!   searched (`host_raise_type`) — the second also `a_host_raise_carries_the_type_its_caller_threads`,
//!   whose `Thing` has a sort-level `requires`, so that an index over the op half alone reads
//!   another slot.
//! * A projected row's raise typed as unknown rather than refused (`HostRaiseType::Projected`):
//!   `a_host_raise_under_a_projected_row_is_refused`.
//! * A builtin handed no channel and no arguments (`Interpreter::call_host`): 64 rows of the
//!   reify suites — every raise, `Error.raise` being a builtin too — among them every row of
//!   this file that catches.
//! * A slot no route stamped left unfilled at the raise (`host_raised_type`'s
//!   `fill_missing_op_scoped_slots`): `wi_8y5be_interpreter_stream_failure_test`'s
//!   `a_query_that_does_not_lower_raises_malformed_query` and three rows of
//!   `wi_spgbp_scoped_kb_test` (`KB.execute`, `KB.loaded`).
//! * The bridge running a dictionary-reading callee on an argument still a call
//!   (`reduce_op_value`'s `needs_dict` arm), or `Error.reify` not read as a call left standing
//!   (`functor_leaves_an_unreduced_op_call`): `a_bridged_callee_is_not_run_on_a_call_term`,
//!   `wi_9wvt7_review5_test::a_drain_failure_raised_again_gets_no_boundary_advice`,
//!   `wi_9wvt7_review6_test::a_caught_account_is_read_and_raised_again_is_the_runtimes`.
//!
//! The load refusals of a raise at a former are the typer's, unchanged by this stage: a
//! `requires` at a structural former was refused before it, and `Error.raise` now has one.

use anthill_core::eval::{EvalError, Interpreter, Value};

/// 3MV2C's program: a boundary at `Box[V = Int64]` inside one at `Box[V = String]`, around a
/// body raising either; `nestedS(n)` raises a `Box[V = String]` for `n < 0` and a
/// `Box[V = Int64]` otherwise. `distinct(n)` is the same shape over two SORTS, the control.
const NESTED: &str = r#"
namespace test.c5
  import anthill.prelude.{Int64, String, Error, Result}
  import anthill.prelude.Result.{ok, err}
  import anthill.reflect.{TypeValue}
  sort Box
    sort V = ?
    entity box(v: V)
  end
  sort Boom
    entity boom(why: String)
  end
  sort Other
    entity other(n: Int64)
  end

  operation raiseEither(n: Int64) -> Int64 effects {Error[Box[V = Int64]], Error[Box[V = String]]} =
    if n < 0 then Error.raise(box("s")) else Error.raise(box(n))
  operation innerS(n: Int64) -> String effects {Error[Box[V = String]]} =
    match Error.reify[T1 = Box[V = Int64]](lambda () -> raiseEither(n))
      case ok(_) -> "none"
      case err(_) -> "inner"
  operation nestedS(n: Int64) -> String =
    match Error.reify[T1 = Box[V = String]](lambda () -> innerS(n))
      case ok(s) -> s
      case err(_) -> "outer"

  operation raiseSorts(n: Int64) -> Int64 effects {Error[Boom], Error[Other]} =
    if n < 0 then Error.raise(boom("s")) else Error.raise(other(n))
  operation innerD(n: Int64) -> String effects {Error[Other]} =
    match Error.reify[T1 = Boom](lambda () -> raiseSorts(n))
      case ok(_) -> "none"
      case err(_) -> "inner"
  operation distinct(n: Int64) -> String =
    match Error.reify[T1 = Other](lambda () -> innerD(n))
      case ok(s) -> s
      case err(_) -> "outer"

  -- A GENERIC raiser states the clause, and its caller threads the evidence.
  operation raiseAt[P](p: P) -> Int64 effects {Error[P]} requires TypeValue[T = P] = Error.raise(p)
  operation raiseGen(n: Int64) -> Int64 effects {Error[Box[V = Int64]], Error[Box[V = String]]} =
    if n < 0 then raiseAt(box("s")) else raiseAt(box(n))
  operation innerG(n: Int64) -> String effects {Error[Box[V = String]]} =
    match Error.reify[T1 = Box[V = Int64]](lambda () -> raiseGen(n))
      case ok(_) -> "none"
      case err(_) -> "inner"
  operation nestedG(n: Int64) -> String =
    match Error.reify[T1 = Box[V = String]](lambda () -> innerG(n))
      case ok(s) -> s
      case err(_) -> "outer"

  -- `Result.reflect` raises the payload of the `Result` it is handed, at its `E`.
  operation reflectS() -> Int64 effects {Error[Box[V = String]]} =
    Result.reflect[P = Box[V = String], A = Int64](err(box("s")))
  operation innerR() -> String effects {Error[Box[V = String]]} =
    match Error.reify[T1 = Box[V = Int64]](lambda () -> reflectS())
      case ok(_) -> "none"
      case err(_) -> "inner"
  operation nestedR() -> String =
    match Error.reify[T1 = Box[V = String]](lambda () -> innerR())
      case ok(s) -> s
      case err(_) -> "outer"
end
"#;

#[track_caller]
fn answers(interp: &mut Interpreter, op: &str, args: &[Value]) -> String {
    let v = interp
        .call(&format!("test.c5.{op}"), args)
        .unwrap_or_else(|e| panic!("{op}({args:?}): {e}"));
    crate::common::scalar_str(interp.kb(), &v).unwrap_or_else(|| panic!("{op}: {v:?}"))
}

/// THE ACCEPTANCE OF WI-20260911-3MV2C. Nested boundaries at `Box[V = Int64]` (inner) and
/// `Box[V = String]` (outer) answer through the outer one for a `Box[V = String]` raise and
/// through the inner one for a `Box[V = Int64]` raise. Until stage (d) both answered
/// `"inner"`: the raise was read as the sort `Box`, which the inner pattern admitted.
///
/// THE CONTROL, `distinct`, is the same shape over two sorts, which the head alone tells apart:
/// the inner boundary is at `Boom`, so a `Boom` answers `"inner"` and an `Other` `"outer"`,
/// with or without this stage.
#[test]
fn nested_box_boundaries_answer_by_the_type_argument() {
    let mut interp = crate::common::interp_for(NESTED);
    assert_eq!(answers(&mut interp, "nestedS", &[Value::Int(-1)]), "outer");
    assert_eq!(answers(&mut interp, "nestedS", &[Value::Int(5)]), "inner");
    assert_eq!(answers(&mut interp, "distinct", &[Value::Int(-1)]), "inner");
    assert_eq!(answers(&mut interp, "distinct", &[Value::Int(5)]), "outer");
    assert_eq!(interp.activation_depth(), 0);
}

/// A GENERIC RAISER threads the type of its payload: `raiseAt[P]` declares `requires
/// TypeValue[T = P]`, and each call site hands it the evidence of its own `P`, so the raise
/// carries `Box[V = String]` from one and `Box[V = Int64]` from the other. Without the clause
/// it is refused at load, naming the clause to add.
#[test]
fn a_generic_raiser_threads_the_type_of_its_payload() {
    let mut interp = crate::common::interp_for(NESTED);
    assert_eq!(answers(&mut interp, "nestedG", &[Value::Int(-1)]), "outer");
    assert_eq!(answers(&mut interp, "nestedG", &[Value::Int(5)]), "inner");

    let without = crate::common::replace_in_fixture(
        NESTED,
        "operation raiseAt[P](p: P) -> Int64 effects {Error[P]} requires TypeValue[T = P] = Error.raise(p)",
        "operation raiseAt[P](p: P) -> Int64 effects {Error[P]} = Error.raise(p)",
    );
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&without),
        &[
            "anthill.reflect.TypeValue[T = P]",
            "Declare `requires anthill.reflect.TypeValue[T = P]` on `test.c5.raiseAt`",
        ],
        "a generic raiser with no clause",
    );
}

/// `Result.reflect` RAISES AT ITS `E`: it declares `requires TypeValue[T = P]`, and the
/// `err(box("s"))` it is handed at `Box[V = String]` is raised at that type.
#[test]
fn a_reflected_result_is_raised_at_its_type() {
    let mut interp = crate::common::interp_for(NESTED);
    assert_eq!(answers(&mut interp, "nestedR", &[]), "outer");
}

/// AN `Error` HANDLER THAT RETHROWS THE RAISE IT WAS HANDED keeps the raise's type: a host
/// that registers one sees every raise, and its `Rethrow` lets the raise continue. A `Throw`
/// of a value is the handler's own raise, of the unknown type, and a boundary at a specific
/// type lets it pass.
#[test]
fn an_error_handler_that_rethrows_keeps_the_raise_s_type() {
    use anthill_core::eval::effects::HandlerAction;
    let mut interp = crate::common::interp_for(NESTED);
    interp
        .register_effect_handler("anthill.prelude.Error", Box::new(|_i, _op, _args| Ok(HandlerAction::Rethrow)))
        .expect("register a rethrowing Error handler");
    assert_eq!(answers(&mut interp, "nestedS", &[Value::Int(-1)]), "outer");
    assert_eq!(answers(&mut interp, "nestedS", &[Value::Int(5)]), "inner");

    interp
        .register_effect_handler(
            "anthill.prelude.Error",
            Box::new(|_i, _op, _args| Ok(HandlerAction::Throw(Value::Str("replaced".into())))),
        )
        .expect("register a replacing Error handler");
    match interp.call("test.c5.nestedS", &[Value::Int(5)]) {
        Err(EvalError::Raised { payload, .. }) => assert_eq!(
            crate::common::scalar_str(interp.kb(), &payload).as_deref(),
            Some("replaced")
        ),
        other => panic!("a replaced payload is admitted by no boundary; got {other:?}"),
    }
}

/// THE STANDARD `Error` HANDLER LETS EVERY RAISE CONTINUE WITH ITS TYPE, a payload holding an
/// opaque value too: a closure, which equals nothing, not even a copy of itself. Recognized by
/// comparing the handler's throw with the raised payload, it was retyped as unknown and passed
/// every boundary (found by /code-review). The CLI and anthill-todo run with this handler.
#[test]
fn a_raise_holding_a_closure_is_caught_under_the_standard_handlers() {
    let src = r#"
namespace test.c5cl
  import anthill.prelude.{Int64, Error, Result}
  import anthill.prelude.Result.{ok, err}
  sort Retry
    entity retry(again: () -> Int64)
  end
  operation fails() -> Int64 effects {Error[Retry]} = Error.raise(retry(lambda () -> 1))
  operation caught() -> Int64 =
    match Error.reify[T1 = Retry](lambda () -> fails())
      case ok(v) -> v
      case err(_) -> 7
end
"#;
    let mut interp = crate::common::interp_for(src);
    interp
        .register_standard_effect_handlers()
        .expect("register the standard effect handlers");
    let v = interp.call("test.c5cl.caught", &[]).expect("caught answers");
    assert_eq!(crate::common::scalar_int(interp.kb(), &v), Some(7));
}

/// A HOST OPERATION THAT RAISES STATES WHAT IT RAISES: `@[host_implemented]` with a row
/// raising `Error[X]` and no `requires TypeValue[T = X]` is refused at load, naming the
/// clause; with the clause it loads, and so does one whose row says only `Error`
/// (`Error[T = ?]`, `Error[?]` — one type), which states no payload type. Two written labels
/// are refused: a raise would have to say which it is.
#[test]
fn a_host_operation_that_raises_states_what_it_raises() {
    let program = |row: &str| {
        format!(
            r#"
namespace test.c5load
  import anthill.prelude.{{Int64, String, Error}}
  import anthill.reflect.{{TypeValue}}
  sort Boom
    entity boom(why: String)
  end
  sort Other
    entity other(n: Int64)
  end
  sort Host
    import anthill.prelude.{{Int64, Error}}
    import anthill.reflect.{{TypeValue}}
    import test.c5load.{{Boom, Other}}
    entity host
    operation go() -> Int64 {row} @[host_implemented]
  end
  provides Host language rust
    artifact "nowhere.rs"
    operation_map {{ go: "error_raise" }}
  end
end
"#
        )
    };
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program("effects {Error[Boom]}")),
        &[
            "host operation `test.c5load.Host.go` raises `Error[Boom]`",
            "Declare `requires TypeValue[T = Boom]` on `test.c5load.Host.go`",
        ],
        "no clause",
    );
    for (row, labels) in [
        (
            "effects {Error[Boom], Error[Other]} requires TypeValue[T = Boom], TypeValue[T = Other]",
            "`Error[Boom]`, `Error[Other]`",
        ),
        // A bare `Error` beside a written one is a second label, not none.
        ("effects {Error, Error[Boom]} requires TypeValue[T = Boom]", "`Error[Boom]`, `Error`"),
    ] {
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&program(row)),
            &[
                &format!("raises {labels}"),
                "a host function raising one of several would have to say which it is",
            ],
            row,
        );
    }
    // `Error[T = ?]` and `Error[?]` written out are the bare `Error` (WI-20261024-DK83Q).
    for row in [
        "effects {Error[Boom]} requires TypeValue[T = Boom]",
        "effects {Error}",
        "effects {Error[T = ?]}",
        "effects {Error[?]}",
    ] {
        let errs = crate::common::load_errors_of(&program(row));
        assert!(errs.is_empty(), "{row}: loads clean, got {errs:#?}");
    }
    // A raise at the operation's own type parameter is a written payload, answered by its
    // clause — not an open one: before DK83Q any variable payload was read as `?`, and this
    // row was refused as raising `Error[T = ?]` with its clause written.
    let generic = program("effects {Error[P]} requires TypeValue[T = P]")
        .replace("operation go()", "operation go[P](p: P)");
    let errs = crate::common::load_errors_of(&generic);
    assert!(errs.is_empty(), "a raise at `P` with its clause loads clean, got {errs:#?}");
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(
            &program("effects {Error[P]}").replace("operation go()", "operation go[P](p: P)"),
        ),
        &["host operation `test.c5load.Host.go` raises `Error[P]`", "requires TypeValue[T = P]"],
        "a raise at `P` without its clause",
    );
    // The clause may be the operation's SORT's, over its own parameter (§5.4).
    let sort_level = r#"
namespace test.c5sl
  import anthill.prelude.{Int64, Error}
  import anthill.reflect.{TypeValue}
  sort Holder
    sort V = ?
    requires TypeValue[T = V]
    entity holder(v: V)
    operation fail(x: V) -> Int64 effects {Error[V]} @[host_implemented]
  end
  provides Holder language rust
    artifact "nowhere.rs"
    operation_map { fail: "error_raise" }
  end
end
"#;
    let errs = crate::common::load_errors_of(sort_level);
    assert!(errs.is_empty(), "a sort-level clause answers: {errs:#?}");
}

/// A HOST FUNCTION'S RAISE CARRIES THE TYPE ITS CALLER THREADS. `Host.boxS` declares
/// `requires TypeValue[T = Box[V = String]]`; its host function raises a `box` it builds, and
/// the raise carries the dictionary the call handed for that clause — so the boundary at
/// `Box[V = Int64]` declines it and the one at `Box[V = String]` catches it.
const HOST_PROGRAM: &str = r#"
namespace test.c5h
  import anthill.prelude.{Int64, String, Error, Result}
  import anthill.prelude.Result.{ok, err}
  import anthill.reflect.{TypeValue}
  sort Box
    sort V = ?
    entity box(v: V)
  end
  operation mkBox() -> Box[V = String] = box("s")
  sort Host
    import anthill.prelude.{Int64, String, Error}
    import anthill.reflect.{TypeValue}
    import test.c5h.{Box}
    entity host
    operation boxS() -> Int64 effects {Error[Box[V = String]]}
      requires TypeValue[T = Box[V = String]] @[host_implemented]
  end
  provides Host language rust
    artifact "nowhere.rs"
    operation_map {
      boxS: "c5h_box_s"
    }
  end
  -- A SPEC raising two labels, and a host MEMBER raising one (restating the spec's
  -- clauses, as a member does), reached through the spec's dictionary by a generic caller:
  -- the channel is built for `Parse.parse`.
  sort Parse
    import anthill.prelude.{Int64, String, Error}
    import anthill.reflect.{TypeValue}
    import test.c5h.{Box}
    sort T = ?
    operation parse(x: T) -> Int64 effects {Error[Box[V = String]], Error[Box[V = Int64]]}
      requires TypeValue[T = Box[V = String]], TypeValue[T = Box[V = Int64]]
  end
  sort Item
    import anthill.prelude.{Int64, String, Error}
    import anthill.reflect.{TypeValue}
    import test.c5h.{Box, Parse}
    entity item(n: Int64)
    provides Parse[T = Item]
    operation parse(x: Item) -> Int64 effects {Error[Box[V = String]]}
      requires TypeValue[T = Box[V = String]], TypeValue[T = Box[V = Int64]] @[host_implemented]
  end
  provides Item language rust
    artifact "nowhere.rs"
    operation_map {
      parse: "c5h_box_s1"
    }
  end
  operation parseAny[T](x: T) -> Int64 effects {Error[Box[V = String]], Error[Box[V = Int64]]}
      requires Parse[T = T] =
    Parse.parse(x)
  operation innerP() -> String effects {Error[Box[V = String]]} =
    match Error.reify[T1 = Box[V = Int64]](lambda () -> parseAny(item(1)))
      case ok(_) -> "none"
      case err(_) -> "inner"
  operation nestedP() -> String =
    match Error.reify[T1 = Box[V = String]](lambda () -> innerP())
      case ok(s) -> s
      case err(_) -> "outer"
  -- A MEMBER WHOSE SLOT IS NAMED APART FROM ITS SPEC OPERATION'S: `Thing`'s own sort-level
  -- `requires TypeValue[…]` takes the name `__req_typevalue`, so the member's op slot is
  -- named apart from it, where `Show.show`'s is not.
  sort Show
    import anthill.prelude.{Int64, String, Error}
    import anthill.reflect.{TypeValue}
    import test.c5h.{Box}
    sort T = ?
    operation show(x: T) -> Int64 effects {Error[Box[V = String]]}
      requires TypeValue[T = Box[V = String]]
  end
  sort Thing
    import anthill.prelude.{Int64, String, Error}
    import anthill.reflect.{TypeValue}
    import test.c5h.{Box, Show}
    requires TypeValue[T = Int64]
    entity thing(n: Int64)
    provides Show[T = Thing]
    operation show(x: Thing) -> Int64 effects {Error[Box[V = String]]}
      requires TypeValue[T = Box[V = String]] @[host_implemented]
  end
  provides Thing language rust
    artifact "nowhere.rs"
    operation_map {
      show: "c5h_box_s1"
    }
  end
  operation showAny[T](x: T) -> Int64 effects {Error[Box[V = String]]} requires Show[T = T] =
    Show.show(x)
  operation innerQ() -> String effects {Error[Box[V = String]]} =
    match Error.reify[T1 = Box[V = Int64]](lambda () -> showAny(thing(1)))
      case ok(_) -> "none"
      case err(_) -> "inner"
  operation nestedQ() -> String =
    match Error.reify[T1 = Box[V = String]](lambda () -> innerQ())
      case ok(s) -> s
      case err(_) -> "outer"
  -- AN EFFECT OPERATION THAT RAISES: `tick` performs `Ticker`, whose host function hands the
  -- call to the registered handler, and the handler's throw is `tick`'s raise.
  sort Ticker
    import anthill.prelude.{Effect}
    provides Effect[T = Ticker]
  end
  sort Tick
    import anthill.prelude.{Int64, String, Error}
    import anthill.reflect.{TypeValue}
    import test.c5h.{Box, Ticker}
    entity tock
    operation tick() -> Int64 effects {Ticker, Error[Box[V = String]]}
      requires TypeValue[T = Box[V = String]] @[host_implemented]
  end
  provides Tick language rust
    artifact "nowhere.rs"
    operation_map {
      tick: "c5h_tick"
    }
  end
  operation innerT() -> String effects {Ticker, Error[Box[V = String]]} =
    match Error.reify[T1 = Box[V = Int64]](lambda () -> Tick.tick())
      case ok(_) -> "none"
      case err(_) -> "inner"
  operation nestedT() -> String effects {Ticker} =
    match Error.reify[T1 = Box[V = String]](lambda () -> innerT())
      case ok(s) -> s
      case err(_) -> "outer"
  operation innerH() -> String effects {Error[Box[V = String]]} =
    match Error.reify[T1 = Box[V = Int64]](lambda () -> Host.boxS())
      case ok(_) -> "none"
      case err(_) -> "inner"
  operation nestedH() -> String =
    match Error.reify[T1 = Box[V = String]](lambda () -> innerH())
      case ok(s) -> s
      case err(_) -> "outer"
end
"#;

#[test]
fn a_host_raise_carries_the_type_its_caller_threads() {
    // NOT THE RECIPE, BY NAME: the host function must be registered before the load, whose
    // `operation_map` names it.
    let kb = crate::common::try_load_kb_prepared(HOST_PROGRAM, |kb| {
        kb.register_host_fn("c5h_box_s", 0, |interp, _| {
            let payload = interp.call("test.c5h.mkBox", &[])?;
            Err(interp.raise_error(payload))
        })
        .expect("register c5h_box_s");
        kb.register_host_fn("c5h_box_s1", 1, |interp, _| {
            let payload = interp.call("test.c5h.mkBox", &[])?;
            Err(interp.raise_error(payload))
        })
        .expect("register c5h_box_s1");
        kb.register_host_fn("c5h_tick", 0, |interp, _| {
            let op = interp
                .kb()
                .try_resolve_symbol("test.c5h.Tick.tick")
                .expect("`tick` is declared");
            interp.invoke_effect_handler("test.c5h.Ticker", op, &[])
        })
        .expect("register c5h_tick");
    })
    .unwrap_or_else(|errs| panic!("the fixture must load: {errs:#?}"));
    let mut interp = Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    // The `Ticker` handler THROWS for the operation it performs, `tick`, at the type `tick`'s
    // row raises (`Box[V = String]`); typed as unknown, the throw passed both boundaries.
    interp
        .register_effect_handler(
            "test.c5h.Ticker",
            Box::new(|i, _op, _args| {
                let payload = i.call("test.c5h.mkBox", &[])?;
                Ok(anthill_core::eval::effects::HandlerAction::Throw(payload))
            }),
        )
        .expect("register the Ticker handler");
    // A member's raise through its spec's dictionary is typed by the member's own row — read
    // as the spec's, two written labels, it had no type to carry (found by /code-review) — and
    // `nestedQ`'s member names its slot otherwise than its spec does. The dictionary dispatch
    // hands each member a channel of its own.
    for op in ["nestedH", "nestedP", "nestedQ", "nestedT"] {
        let v = interp
            .call(&format!("test.c5h.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op}: {e}"));
        assert_eq!(crate::common::scalar_str(interp.kb(), &v).as_deref(), Some("outer"), "{op}");
    }
}

/// THE RUNTIME'S OWN RAISES ARE CAUGHT AT THEIR SORTS. `1 / 0` raises `DivisionByZero` from
/// `Int64.div`, which declares `requires TypeValue[T = DivisionByZero]`; a `match` with no arm
/// that fits raises `MatchFailed` with no operation behind it, carrying the constant the error
/// layer holds.
const RUNTIME: &str = r#"
namespace test.c5rt
  import anthill.prelude.{Int64, Error, Result, DivisionByZero, MatchFailed}
  import anthill.prelude.Result.{ok, err}
  operation divide(n: Int64) -> Int64 effects {Error[DivisionByZero]} = 10 / n
  operation caughtDiv(n: Int64) -> Int64 =
    match Error.reify[T1 = DivisionByZero](lambda () -> divide(n))
      case ok(v) -> v
      case err(_) -> 0 - 1
  operation choose(n: Int64) -> Int64 effects {Error[MatchFailed]} =
    match n
      case 1 -> 10
  operation caughtMatch(n: Int64) -> Int64 =
    match Error.reify[T1 = MatchFailed](lambda () -> choose(n))
      case ok(v) -> v
      case err(_) -> 0 - 2
end
"#;

#[test]
fn a_division_by_zero_is_caught_at_its_sort() {
    let mut interp = crate::common::interp_for(RUNTIME);
    for (op, n, want) in [("caughtDiv", 0, -1), ("caughtDiv", 5, 2)] {
        let v = interp
            .call(&format!("test.c5rt.{op}"), &[Value::Int(n)])
            .unwrap_or_else(|e| panic!("{op}({n}): {e}"));
        assert_eq!(crate::common::scalar_int(interp.kb(), &v), Some(want), "{op}({n})");
    }
}

#[test]
fn a_failed_match_is_caught_at_its_sort() {
    let mut interp = crate::common::interp_for(RUNTIME);
    for (n, want) in [(7, -2), (1, 10)] {
        let v = interp
            .call("test.c5rt.caughtMatch", &[Value::Int(n)])
            .unwrap_or_else(|e| panic!("caughtMatch({n}): {e}"));
        assert_eq!(crate::common::scalar_int(interp.kb(), &v), Some(want), "caughtMatch({n})");
    }
}

/// A RAISE AT A STRUCTURAL FORMER IS REFUSED AT THE RAISE, naming the former — and at a sort
/// holding one among its type arguments: neither has a `TypeValue`, which `Error.raise`
/// requires. (Until stage (d) the raise loaded and the boundary around it was refused.)
#[test]
fn a_raise_at_a_former_is_refused_at_the_raise() {
    for (shape, src, wants) in [
        (
            "a tuple",
            r#"
namespace test.c5f
  import anthill.prelude.{Int64, String, Error}
  operation raisesTuple(n: Int64) -> Int64 effects {Error[(a: Int64, b: String)]} =
    Error.raise((a: n, b: "s"))
end
"#,
            &[
                "anthill.reflect.TypeValue[T = (a: Int64, b: String)]",
                "cannot be supplied for call to `anthill.prelude.Error.raise`",
                "a STRUCTURAL FORMER",
            ][..],
        ),
        (
            "a sort holding a tuple",
            r#"
namespace test.c5f
  import anthill.prelude.{Int64, String, Error, Option}
  import anthill.prelude.Option.{some}
  operation raisesOpt() -> Int64 effects {Error[Option[T = (a: Int64, b: String)]]} =
    Error.raise(some((a: 1, b: "s")))
end
"#,
            &[
                "anthill.reflect.TypeValue[T = anthill.prelude.Option[T = (a: Int64, b: String)]]",
                "has a STRUCTURAL FORMER — a tuple or an arrow — among its type arguments",
            ][..],
        ),
    ] {
        let errs = crate::common::load_errors_of(src);
        assert_eq!(errs.len(), 1, "{shape}: exactly one refusal, got {errs:#?}");
        crate::common::assert_refused_naming(&errs, wants, shape);
    }
}

/// A RAISED `Term` IS REFUSED AT LOAD: `Term` has no `TypeValue` (it is no sort a type
/// value names), so a raise of one has no type to carry.
#[test]
fn a_raised_term_is_refused_at_load() {
    let src = r#"
namespace test.c5t
  import anthill.prelude.{Int64, Error, List}
  import anthill.prelude.List.{nil}
  import anthill.reflect.{Term, make_fn}
  operation viaTerm() -> Int64 effects Error[Term] =
    Error.raise(make_fn("anthill.prelude.RelationFloundered.relation_floundered", nil()))
end
"#;
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(src),
        &[
            "anthill.reflect.TypeValue[T = anthill.reflect.Term]",
            "cannot be supplied for call to `anthill.prelude.Error.raise`",
        ],
        "a raised Term",
    );
}

/// THE BRIDGE DOES NOT RUN A CALLEE ON A CALL TERM. A callee that reads a requirement slot is
/// bridged from a folded body rather than folded (WI-1037); with an argument that is still a
/// call — `Error.reify(…)`, which the fold reduces only at the depth-0 bridge of the body it
/// stands in — it ran the callee on the term, and faulted. Declined there, the body is
/// bridged whole and its arguments evaluated. Reached through `Result.reflect`, which
/// requires `TypeValue[T = P]` since this stage. `keepNR`, with no clause, folds: the control
/// that passes either way.
const BRIDGE: &str = r#"
namespace test.c5b
  import anthill.prelude.{Int64, String, Error, Result, List}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Result.{ok, err}
  import anthill.reflect.{KB, LoadFailed, TypeValue}
  sort Boom
    entity boom(why: String)
  end
  operation loadBad() -> Int64 effects Error[LoadFailed] =
    let _ = KB.loaded(cons("namespace zz.bad fact Nope(", nil()))
    1
  operation boomIt() -> Int64 effects {Error[Boom]} = Error.raise(boom("b"))
  operation reflected() -> Int64 effects Error[LoadFailed] =
    Result.reflect(Error.reify(lambda () -> loadBad()))
  operation reflectedBoom() -> Int64 effects {Error[Boom]} =
    Result.reflect(Error.reify(lambda () -> boomIt()))
  operation keep[P](r: Result[E = P, T = Int64]) -> Int64 requires TypeValue[T = P] =
    match r
      case ok(v) -> v
      case err(_) -> 7
  operation keepNR[P](r: Result[E = P, T = Int64]) -> Int64 =
    match r
      case ok(v) -> v
      case err(_) -> 7
  operation viaKeep() -> Int64 = keep(Error.reify(lambda () -> loadBad()))
  operation viaKeepNR() -> Int64 = keepNR(Error.reify(lambda () -> loadBad()))
  rule byReflect(?n) :- ?n <=> reflected()
  rule byReflectBoom(?n) :- ?n <=> reflectedBoom()
  rule byKeep(?n) :- ?n <=> viaKeep()
  rule byKeepNR(?n) :- ?n <=> viaKeepNR()
  rule direct(?n) :- ?n <=> keep(Error.reify(lambda () -> loadBad()))
end
"#;

///
/// `byReflectBoom` runs `Result.reflect` on the VALUE the boundary delivered, `err(boom("b"))`,
/// so it raises the `Boom` again — the fault the bridge reports names it; run on the term it
/// faulted `match_failed`. `byReflect`'s payload is the runtime's account of a load, whose
/// raise is no fault of the goal. `direct` is the callee written in the rule itself, whose
/// argument the goal's reduction evaluates: the control that passes either way.
#[test]
fn a_bridged_callee_is_not_run_on_a_call_term() {
    let messages = crate::common::fault_messages(BRIDGE, "test.c5b.byReflectBoom(?n)");
    assert!(
        messages.iter().any(|m| m.contains("raised boom(why: \"b\")"))
            && messages.iter().all(|m| !m.contains("match_failed")),
        "the reflected `Boom` is raised again: {messages:#?}"
    );
    for goal in ["test.c5b.byReflect(?n)", "test.c5b.byKeep(?n)", "test.c5b.byKeepNR(?n)"] {
        let messages = crate::common::fault_messages(BRIDGE, goal);
        assert!(messages.is_empty(), "{goal}: no fault: {messages:#?}");
    }
    let mut kb = crate::common::load_kb_with(BRIDGE);
    for goal in ["test.c5b.byKeep", "test.c5b.byKeepNR", "test.c5b.direct"] {
        assert_eq!(crate::common::one_definite_int(&mut kb, goal), Some(7), "{goal}");
    }
}

// ── the routes a raising builtin is reached by ────────────────────────────────────────

const F1_PROGRAM: &str = r#"
namespace test.c5f1
  import anthill.prelude.{Int64, Error, Result, DivisionByZero}
  import anthill.prelude.Result.{ok, err}
  import anthill.prelude.{Divisible}
  operation safeDiv[T](a: T, b: T) -> T effects {Error[DivisionByZero]} requires Divisible[T = T] =
    Divisible.div(a, b)
  operation viaValue(b: Int64) -> Int64 =
    match Error.reify[T1 = DivisionByZero](lambda () -> safeDiv(10, b))
      case ok(v) -> v
      case err(_) -> 0 - 1
end
"#;

/// A DIVISION THROUGH A SPEC'S DICTIONARY IS CAUGHT AT ITS SORT: `safeDiv[T]` calls
/// `Divisible.div` through the dictionary of `Divisible[T = Int64]`, which directs the call
/// to `Int64.div`'s host function, whose raise takes its type from the channel it is handed.
#[test]
fn a_division_through_a_spec_dictionary_is_caught() {
    let mut interp = crate::common::interp_for(F1_PROGRAM);
    for (n, want) in [(0, -1), (5, 2)] {
        let v = interp
            .call("test.c5f1.viaValue", &[Value::Int(n)])
            .unwrap_or_else(|e| panic!("viaValue({n}): {e}"));
        assert_eq!(crate::common::scalar_int(interp.kb(), &v), Some(want), "viaValue({n})");
    }
}

/// AN `Error` HANDLER THAT RAISES A VALUE OF ITS OWN raises it at the unknown type: a handler
/// is no host operation, and runs with no builtin's channel. Typed by the `Error.raise` that
/// invoked it, the `"wrapped"` string was caught by the boundary at `Box[V = String]` — a
/// `String` delivered inside a `Result[E = Box[V = String]]` (found by /code-review).
#[test]
fn an_error_handler_raising_its_own_value_raises_the_unknown_type() {
    let mut interp = crate::common::interp_for(NESTED);
    interp
        .register_effect_handler(
            "anthill.prelude.Error",
            Box::new(|i, _op, _args| Err(i.raise_error(Value::Str("wrapped".into())))),
        )
        .expect("register a wrapping Error handler");
    match interp.call("test.c5.nestedS", &[Value::Int(-1)]) {
        Err(EvalError::Raised { payload, .. }) => assert_eq!(
            crate::common::scalar_str(interp.kb(), &payload).as_deref(),
            Some("wrapped")
        ),
        other => panic!("the handler's own raise is of a type not known; got {other:?}"),
    }
}

/// A HOST OPERATION WHOSE ROW NAMES ITS EFFECT THROUGH A PROJECTION — `pull(s: Self) effects
/// s.E` — raises at the type the CALL resolves `s.E` to, which nothing threads to its host
/// function, and no clause can state. The raise is refused where it happens, naming why:
/// typed as unknown, it passed the boundary at `Boom` the typer had let discharge
/// `Error[Boom]`, and escaped an operation typed effect-free (found by /code-review).
const PROJECTED: &str = r#"
namespace test.c5p
  import anthill.prelude.{Int64, String, Error, Result}
  import anthill.prelude.Result.{ok, err}
  sort Boom
    entity boom(why: String)
  end
  operation mkBoom() -> Boom = boom("p")
  sort Src
    import anthill.prelude.{Int64}
    effects E = ?
    entity src(n: Int64)
    operation pull(s: Self) -> Int64 effects s.E @[host_implemented]
  end
  provides Src language rust
    artifact "nowhere.rs"
    operation_map {
      pull: "c5p_pull"
    }
  end
  operation pullBoom(s: Src[E = {Error[Boom]}]) -> Int64 effects {Error[Boom]} = Src.pull(s)
  operation caughtPull() -> Int64 =
    match Error.reify[T1 = Boom](lambda () -> pullBoom(src(1)))
      case ok(v) -> v
      case err(_) -> 7
end
"#;

#[test]
fn a_host_raise_under_a_projected_row_is_refused() {
    // NOT THE RECIPE, BY NAME: the host function must be registered before the load.
    let kb = crate::common::try_load_kb_prepared(PROJECTED, |kb| {
        kb.register_host_fn("c5p_pull", 1, |interp, _| {
            let payload = interp.call("test.c5p.mkBoom", &[])?;
            Err(interp.raise_error(payload))
        })
        .expect("register c5p_pull");
    })
    .unwrap_or_else(|errs| panic!("the fixture must load: {errs:#?}"));
    let mut interp = Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    match interp.call("test.c5p.caughtPull", &[]) {
        Err(e @ EvalError::RaiseTypeUnread { .. }) => assert!(
            e.to_string().contains("through a projection or a row variable"),
            "{e}"
        ),
        other => panic!("refused, naming the projection; got {other:?}"),
    }
}
