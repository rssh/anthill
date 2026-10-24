//! WI-20261016-YM8HD (proposal 071 stage (c)) — `Error.reify` REQUIRES `TypePattern[T = T1]`,
//! and `ErrorTag` is retired.
//!
//! The boundary keeps the dictionary of `TypePattern[T = T1]` its call is handed, and a raise
//! is caught where that dictionary's `admits` answers yes for the raised type
//! (`Interpreter::boundary_admits`). It reads no sub-dictionary by position, as the `ErrorTag`
//! boundary did (`reify_payload_sub`), so no other row of the spec could put another sort
//! where the boundary read the payload: `TypePattern` takes no written row, and `ErrorTag`
//! is gone. Until 071's stage (d) a raise carried no type, and the type asked about was the
//! raised value's head sort, its arguments left out; since that stage it is the type the
//! raise carries (`wi_5cdn5_raise_carries_its_type_test`).
//!
//! The reify rows of `wi_9wvt7_error_reify_test`, `wi_9wvt7_reify_rule_body_test`,
//! `wi_9wvt7_review5_test`, `wi_n31xx_type_value_read_rule_test` and `alias_written_name_test`
//! were re-pointed from `ErrorTag` to `TypePattern` with their verdicts unchanged; the rows
//! here are this stage's own.
//!
//! ── WHICH ROWS FAIL WHEN EACH PART IS BACKED OUT ──────────────────────────────────
//!
//! * The stdlib's `ErrorTag` put back (the sort and `Error`'s row): `error_tag_is_an_ordinary_unresolved_name`.
//! * `boundary_admits` answering `true` for every raise — the catch on the carrier alone —
//!   the rows about a boundary NOT catching: `wi_9wvt7_error_reify_test`'s narrowing list
//!   (its header names them) and `a_boundary_reads_the_type_the_raise_carries`'s
//!   control `narrowOther`.
//! * `boundary_admits` answering `false`: every row of those files in which a boundary
//!   catches, and both rows of `a_boundary_reads_the_type_the_raise_carries`.
//! * The install-time check that the dictionary is a `TypePattern` instance
//!   (`Interpreter::enter_reify_boundary`): `a_dictionary_that_is_no_pattern_is_refused_before_the_thunk_runs`,
//!   whose host rows then run the thunk.
//! * The frames of a raise discarded before a boundary is asked
//!   (`ActivationStack::discard_above_boundary`): `a_raise_at_the_depth_caps_last_frame_is_caught`.
//! * The type asked about built from the raised value's head alone, as this stage built it,
//!   is stage (d) backed out: `a_boundary_reads_the_type_the_raise_carries`'s `narrowR`.


use anthill_core::eval::EvalError;

/// F1 of WI-20260908-9WVT7's third review, the two programs as they were measured on
/// 2026-10-16: a written `ErrorTag` row was selected over `Error`'s, so a boundary read its
/// payload sort out of evidence the program forged. With `ErrorTag` at `Boom` and no
/// `TypeValue` inside, every `Error.reify` at `Boom` died at run time; with the tuple's row
/// conditioned on `TypeValue[T = Other]`, the tuple's boundary caught `other(n: 7)`.
fn f1_programs(spec: &str, import: &str) -> [(&'static str, String); 2] {
    [
        (
            "a row at the payload's sort",
            format!(
                r#"
namespace test.ym8hd.f1a
  import anthill.prelude.{{Int64, String, Error, Result}}
  import anthill.prelude.Result.{{ok, err}}
  sort Boom
    entity boom(why: String)
  end
  sort Wrapper
    import anthill.prelude.{{Type, Bool}}
    {import}
    entity wrap(n: Int64)
    provides {spec}[T = Boom]
  end
  operation mayFail(n: Int64) -> Int64 effects {{Error[Boom]}} =
    if n < 0 then Error.raise(boom("neg")) else n
  operation caught() -> Int64 =
    match Error.reify(lambda () -> mayFail(0 - 1))
      case ok(n) -> n
      case err(_) -> 22
end
"#
            ),
        ),
        (
            "a row at a tuple, conditioned on another sort",
            format!(
                r#"
namespace test.ym8hd.f1b
  import anthill.prelude.{{Int64, String, Error, Result}}
  import anthill.prelude.Result.{{ok, err}}
  sort Other
    entity other(n: Int64)
  end
  sort Wrapper
    import anthill.reflect.{{TypeValue}}
    {import}
    entity wrap(n: Int64)
    provides {spec}[T = (a: Int64, b: String)] :- TypeValue[T = Other]
  end
  operation raiseTup(n: Int64) -> Int64 effects {{Error[(a: Int64, b: String)], Error[Other]}} =
    Error.raise(other(n))
  operation tupOp(n: Int64) -> Result[E = (a: Int64, b: String), T = Int64]
      effects {{Error[Other]}} =
    Error.reify(lambda () -> raiseTup(n))
  operation run() -> Int64 =
    match Error.reify(lambda () -> tupOp(7))
      case ok(_) -> 11
      case err(_) -> 22
end
"#
            ),
        ),
    ]
}

/// `ErrorTag` NAMED IN A PROGRAM IS AN ORDINARY UNRESOLVED NAME: the spec is gone from the
/// prelude, and F1's programs are refused for naming it, as they would be for any name the
/// prelude does not declare.
///
/// FAILS with the stdlib's `ErrorTag` put back: both programs then reach the typer, the first
/// loading clean.
#[test]
fn error_tag_is_an_ordinary_unresolved_name() {
    for (shape, src) in f1_programs("ErrorTag", "import anthill.prelude.{ErrorTag}") {
        let errs = crate::common::load_errors_of(&src);
        crate::common::assert_refused_naming(
            &errs,
            &["unresolved import 'anthill.prelude.ErrorTag'"],
            shape,
        );
        crate::common::assert_refused_naming(&errs, &["unresolved name 'ErrorTag'"], shape);
    }
}

/// F1'S ROWS SPELLED WITH THE SPEC THE BOUNDARY NOW REQUIRES ARE REFUSED AT LOAD: no row of
/// `TypePattern` may be written (stage (b)'s `written_type_pattern_provisions`), so neither
/// program reaches a boundary through a written row.
///
/// PASSES EITHER WAY BY DESIGN against this stage's own change: the refusal is stage (b)'s.
/// What this stage adds is that the boundary requires the spec the refusal protects — the row
/// beside it, `f1s_first_program_without_its_row_answers_through_the_one_row`, is the
/// boundary reading that spec.
#[test]
fn f1s_rows_spelled_type_pattern_are_refused_at_load() {
    for (shape, src) in f1_programs("TypePattern", "import anthill.reflect.{TypePattern}") {
        let errs = crate::common::load_errors_of(&src);
        crate::common::assert_refused_naming(
            &errs,
            &["a `provides anthill.reflect.TypePattern[…]` is written for 'test.ym8hd."],
            shape,
        );
    }
}

/// THE CONTROL OF THE TWO ROWS ABOVE: F1's first program without its written row loads, and
/// the boundary at `Boom` catches through `TypePattern`'s one row — the value `22` is the
/// `err` arm. (The second program without its row is refused at load, a tuple having no
/// `TypePattern` instance: `wi_n31xx_type_value_read_rule_test::a_body_less_callee_is_held_to_the_former_refusal`.)
#[test]
fn f1s_first_program_without_its_row_answers_through_the_one_row() {
    let [(_, src), _] = f1_programs("TypePattern", "import anthill.reflect.{TypePattern}");
    let src = crate::common::replace_in_fixture(&src, "    provides TypePattern[T = Boom]\n", "");
    assert_eq!(crate::common::run_int64(&src, "test.ym8hd.f1a.caught"), Ok(22));
}

/// THE TYPE THE BOUNDARY ASKS ABOUT IS THE ONE THE RAISE CARRIES, its arguments with it, since
/// 071's stage (d) (WI-20261016-5CDN5). Until then it was the raised value's head sort, and
/// the verdict of every boundary was the one the head-sort comparison it replaced gave
/// (WI-20260911-3MV2C).
///
/// `narrowR(1)` is 071's measured program: `inner` is a boundary at `Boom[Reason = Int64]`
/// that leaves `Error[Boom[Reason = String]]` to its caller, and `narrowR` catches that at
/// `Boom[Reason = String]`. The raise carries `Boom[Reason = String]`, which `inner`'s pattern
/// does not admit, so the outer boundary catches it: `"outer"`. Until stage (d) the raised
/// `boom("s")` was read as the sort `Boom`, arguments left out, which `inner` admitted:
/// `"inner"` (071 §5).
///
/// THE CONTROL, `narrowOther`, is a sort the inner pattern does not admit: an `Other` raised
/// past a `Boom` boundary reaches the outer one, either way. FAILS with `boundary_admits`
/// answering `true` (`"inner"`); the first row FAILS with the raised type read as its head
/// sort, as stage (c) read it (`"inner"`).
#[test]
fn a_boundary_reads_the_type_the_raise_carries() {
    let mut interp = crate::common::interp_for(
        r#"
namespace test.ym8hd.narrow
  import anthill.prelude.{Int64, String, Error, Result}
  import anthill.prelude.Result.{ok, err}
  sort Boom
    sort Reason = ?
    entity boom(reason: Reason)
  end
  sort Other
    entity other(n: Int64)
  end
  operation raiseS() -> Int64 effects {Error[Boom[Reason = String]]} = Error.raise(boom("s"))
  operation inner() -> String effects {Error[Boom[Reason = String]]} =
    match Error.reify[T1 = Boom[Reason = Int64]](lambda () -> raiseS())
      case ok(_) -> "none"
      case err(_) -> "inner"
  operation narrowR() -> String =
    match Error.reify[T1 = Boom[Reason = String]](lambda () -> inner())
      case ok(s) -> s
      case err(_) -> "outer"

  operation raiseOther() -> Int64 effects {Error[Other]} = Error.raise(other(1))
  operation innerOther() -> String effects {Error[Other]} =
    match Error.reify[T1 = Boom[Reason = Int64]](lambda () -> raiseOther())
      case ok(_) -> "none"
      case err(_) -> "inner"
  operation narrowOther() -> String =
    match Error.reify[T1 = Other](lambda () -> innerOther())
      case ok(s) -> s
      case err(_) -> "outer"
end
"#,
    );
    for (op, want) in [("narrowR", "outer"), ("narrowOther", "outer")] {
        let v = interp
            .call(&format!("test.ym8hd.narrow.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op}: {e}"));
        assert_eq!(
            crate::common::scalar_str(interp.kb(), &v).as_deref(),
            Some(want),
            "{op}"
        );
    }
    // The boundary's answer is a value of the program, not an error: nothing is left on
    // the stack by the `admits` calls made while a raise looked for its boundary.
    assert_eq!(interp.activation_depth(), 0);
}

/// How many times the thunk of the rows below has run: `Host.tick`, a host function, counts.
static TICKS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

const STAND_IN_PROGRAM: &str = r#"
namespace test.ym8hd.standin
  import anthill.prelude.{Int64, String, Error, Result, Type, Bool}
  import anthill.prelude.Result.{ok, err}
  import anthill.reflect.{TypePattern}
  sort Boom
    entity boom(why: String)
  end
  sort Host
    import anthill.prelude.{Int64}
    entity host
    operation tick() -> Int64 @[host_implemented]
  end
  provides Host language rust
    artifact "nowhere.rs"
    operation_map {
      tick: "ym8hd_tick"
    }
  end
  sort Catcher
    sort P = ?
    requires TypePattern[T = P]
    entity catcher(n: Int64)
    operation catchIt(c: Catcher[P = P], body: () -> Int64 @ {Error[P]}) -> Result[E = P, T = Int64] =
      Error.reify(body)
  end
  -- The same, with an `admits` of its own that answers yes for every type.
  sort OwnCatcher
    sort P = ?
    requires TypePattern[T = P]
    entity ownCatcher(n: Int64)
    operation admits(t: Type) -> Bool = true
    operation catchIt(c: OwnCatcher[P = P], body: () -> Int64 @ {Error[P]}) -> Result[E = P, T = Int64] =
      Error.reify(body)
  end
  -- The same again, providing `TypeValuePattern` — so it provides `TypePattern` through it.
  sort RowCatcher
    import anthill.reflect.{TypeValuePattern}
    sort P = ?
    requires TypePattern[T = P]
    provides TypeValuePattern[T = P]
    entity rowCatcher(n: Int64)
    operation admits(t: Type) -> Bool = true
    operation catchIt(c: RowCatcher[P = P], body: () -> Int64 @ {Error[P]}) -> Result[E = P, T = Int64] =
      Error.reify(body)
  end
  operation mayFail() -> Int64 effects {Error[Boom]} =
    if Host.tick() > 0 then Error.raise(boom("x")) else 0
  operation mk() -> Catcher[P = Boom] = catcher[P = Boom](1)
  operation mkOwn() -> OwnCatcher[P = Boom] = ownCatcher[P = Boom](1)
  operation mkRow() -> RowCatcher[P = Boom] = rowCatcher[P = Boom](1)
  operation viaOp() -> Int64 =
    match Catcher.catchIt(catcher[P = Boom](1), lambda () -> mayFail())
      case ok(n) -> n
      case err(_) -> 22
end
"#;

/// A DICTIONARY THAT IS NO `TypePattern` INSTANCE IS REFUSED WHERE THE BOUNDARY WOULD BE
/// INSTALLED, BEFORE THE THUNK RUNS. A host entry into an operation of a sort that declares
/// `requires TypePattern[T = P]` seeds a stand-in over that sort for its chain
/// (`seed_entry_requirements`), and the sort provides no `TypePattern`. The thunk ticks a host
/// counter, so "before it runs" is observed, not inferred from the error.
///
/// MEASURED without the check: through `Catcher`, the thunk ran and the raise died
/// `OperationBodyMissing: anthill.reflect.TypePattern.admits`; through `OwnCatcher`, whose own
/// `admits` answers yes, the dispatch landed on it and the boundary caught every payload
/// (found by /code-review). `RowCatcher` writes `provides TypeValuePattern[T = P]`, so it
/// provides `TypePattern` through it: a check that the `impl` provides `TypePattern` passed it
/// (found by the second /code-review). The check is that the `impl` is the one row's
/// provider, `TypeValuePattern`.
///
/// THE CONTROL, `viaOp`, is the same call from an operation body, whose caller builds the
/// evidence at `Boom`: `22`, the `err` arm, the counter ticked. FAILS with the install-time
/// check backed out (the three host rows); the control passes either way.
#[test]
fn a_dictionary_that_is_no_pattern_is_refused_before_the_thunk_runs() {
    use std::sync::atomic::Ordering;
    let kb = crate::common::try_load_kb_prepared(STAND_IN_PROGRAM, |kb| {
        kb.register_host_fn("ym8hd_tick", 0, |_, _| {
            TICKS.fetch_add(1, Ordering::SeqCst);
            Ok(anthill_core::eval::Value::Int(1))
        })
        .expect("register ym8hd_tick");
    })
    .unwrap_or_else(|errs| panic!("the fixture must load: {errs:#?}"));
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");

    TICKS.store(0, Ordering::SeqCst);
    let v = interp.call("test.ym8hd.standin.viaOp", &[]).expect("the control answers");
    assert_eq!(crate::common::scalar_int(interp.kb(), &v), Some(22));
    assert_eq!(TICKS.load(Ordering::SeqCst), 1, "the control's thunk runs once");

    let op = interp
        .kb()
        .try_resolve_symbol("test.ym8hd.standin.mayFail")
        .expect("`mayFail` is declared");
    let thunk = anthill_core::eval::Value::OpRef {
        op,
        dict: None,
        named: None,
        spread_labels: None,
        op_reqs: None,
    };
    for (mk, catcher) in [("mk", "Catcher"), ("mkOwn", "OwnCatcher"), ("mkRow", "RowCatcher")] {
        let c = interp
            .call(&format!("test.ym8hd.standin.{mk}"), &[])
            .unwrap_or_else(|e| panic!("`{mk}` builds a catcher: {e}"));
        TICKS.store(0, Ordering::SeqCst);
        match interp.call(&format!("test.ym8hd.standin.{catcher}.catchIt"), &[c, thunk.clone()]) {
            Err(e @ anthill_core::eval::EvalError::ReifyPayloadUnread { .. }) => {
                let text = e.to_string();
                for want in [
                    format!("`test.ym8hd.standin.{catcher}`'s dictionary"),
                    "is no instance of `TypePattern`".to_owned(),
                ] {
                    assert!(text.contains(&want), "{catcher}: expected {want:?}; got {text}");
                }
            }
            other => panic!("{catcher}: the stand-in is refused before the thunk runs, got {other:?}"),
        }
        assert_eq!(TICKS.load(Ordering::SeqCst), 0, "{catcher}: the thunk did not run");
        assert_eq!(interp.activation_depth(), 0, "{catcher}: the refused entry leaves no frame");
    }
}

const DEEP_PROGRAM: &str = r#"
namespace test.ym8hd.deep
  import anthill.prelude.{Int64, String, Error, Result}
  import anthill.prelude.Result.{ok, err}
  sort Boom
    entity boom(why: String)
  end
  operation keep(b: Boom) -> Int64 = 0
  -- The raise is the whole body, its argument a variable, entered by a tail call: no child
  -- frame below it, so it stands at the deepest frame the computation reaches.
  operation raiseP(p: Boom) -> Int64 effects {Error[Boom]} = Error.raise(p)
  operation keepP(p: Boom) -> Int64 effects {Error[Boom]} = keep(p)
  operation caughtRaise() -> Int64 =
    let b = boom("bottom")
    match Error.reify(lambda () -> raiseP(b))
      case ok(v) -> v
      case err(_) -> 0 - 1
  operation caughtOk() -> Int64 =
    let b = boom("bottom")
    match Error.reify(lambda () -> keepP(b))
      case ok(v) -> v
      case err(_) -> 0 - 1
end
"#;

/// A RAISE AT THE DEEPEST FRAME THE DEPTH CAP ALLOWS IS CAUGHT. The boundary asks `admits`
/// on the activation stack, and asking is anthill code, which takes a frame: the frames of
/// the raise above the boundary go first (`ActivationStack::discard_above_boundary`), dead
/// whichever boundary takes the raise. So the smallest cap at which `caughtRaise()` answers
/// is the one at which `caughtOk()`, the same thunk with a call in the raise's place,
/// answers: the raise needs no frame the computation did not.
///
/// FAILS with the frames kept while the boundary is asked (found by /code-review): the raise
/// then needs one frame more, and at `caughtOk`'s cap its question dies `DepthExceeded` in
/// place of the `err` (MEASURED). THE SHAPE IS THE POINT: the raise must stand at the deepest
/// frame, so its argument is a variable and it is entered by a tail call. A recursion whose
/// base case raises `boom("bottom")` passes either way (MEASURED): the deepest frame there is a
/// child the condition or the argument was evaluated in, gone by the time the raise is made.
#[test]
fn a_raise_at_the_depth_caps_last_frame_is_caught() {
    let mut kb = Some(crate::common::load_kb_with(DEEP_PROGRAM));
    let mut smallest_cap = |op: &str| -> (usize, i64) {
        for cap in 1..400 {
            let mut interp = anthill_core::eval::Interpreter::with_config(
                kb.take().expect("the KB is handed back after every call"),
                anthill_core::eval::EvalConfig {
                    depth_cap: Some(cap),
                    ..Default::default()
                },
            );
            anthill_core::eval::builtins::register_standard_builtins(&mut interp)
                .expect("register standard eval builtins");
            let outcome = interp.call(&format!("test.ym8hd.deep.{op}"), &[]);
            let answer = match outcome {
                Ok(v) => crate::common::scalar_int(interp.kb(), &v),
                Err(EvalError::DepthExceeded { .. }) => None,
                Err(e) => panic!("{op} at cap {cap}: {e}"),
            };
            kb = Some(interp.into_kb());
            if let Some(answer) = answer {
                return (cap, answer);
            }
        }
        panic!("{op} answers at no cap below 400");
    };
    let (ok_cap, ok_answer) = smallest_cap("caughtOk");
    let (raise_cap, raise_answer) = smallest_cap("caughtRaise");
    assert_eq!(ok_answer, 0, "the non-raising thunk answers `keep`'s 0");
    assert_eq!(raise_answer, -1, "the raise is caught: the `err` arm");
    assert_eq!(
        raise_cap, ok_cap,
        "the raise is caught at the cap the computation itself needs"
    );
}
