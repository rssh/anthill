//! WI-20261016-BDVYW (proposal 071 stage (e)) — THE TYPER DISCHARGES BY THE TEST THE RUN ASKS,
//! AND BUILDS A BOUNDARY'S PATTERN AT AN OPEN SLOT. Closes WI-20261015-D2KZ5.
//!
//! A boundary's pattern is the least pattern that admits every `Error` label its thunk raises
//! (071 §7 Q1, decided with the user 2026-10-27): `Boom` over `Boom[Reason = String]` and
//! `Boom[Reason = Int64]`, its slot a pattern's open slot; the wider sort where one refines the
//! other; a bracket's open slot filled from the labels as any bracket's is from its arguments;
//! the pattern `?` over a thunk whose only `Error` label is the bare one. Labels of sorts no one
//! sort heads are refused, the call asked to say which it catches. A label is discharged where
//! the pattern admits it — the predicate the run's `admits` asks (`type_pattern.rs`) — and the
//! evidence of a pattern with an open slot is built by the typer, the slot a wildcard.
//!
//! ── WHICH ROWS FAIL WHEN EACH PART IS BACKED OUT ── measured 2026-10-27, each alone ──
//!
//! Most rows read one fixture, `PROGRAM`; a part whose absence refuses one of its operations
//! fails every row over it, which is what "the fixture's rows" means below.
//!
//! * The boundary's pattern read off the labels (`slots::fix_boundary_patterns`): the fixture's
//!   rows (`caughtWide` refused, "undeclared effect"), the two refusals of labels no one sort
//!   heads, the `?` row, `wi_dk83q_identical_substitution_test::an_open_payload_is_one_label_however_it_is_written`
//!   and `wi_9wvt7_reify_rule_body_test::a_rule_body_boundary_over_two_sorts_is_refused`.
//! * A label another label of its slot takes left to that label: `alias_written_name_test`'s
//!   `guard` row and the 20 rows of `wi_9wvt7_error_reify_test` over `catchItEsc`.
//! * A variable another label names left to §8.1's join: seven rows of
//!   `wi_rdns4_shared_row_tail_test` (`an_invariant_occurrence_fixes_a_payload_a_covariant_one_shares`
//!   among them).
//! * A closed callback row read by the row pass (`slots::slot_row`): the fixture's rows, `catchAt`'s
//!   two labels refused at its slot.
//! * The pattern asked before the one-to-one pairing (`effects::match_present_labels`): the
//!   fixture's rows, the second `Boom` left to the caller's row.
//! * The discharge by the one predicate (`effects::error_labels_discharged`): the fixture's rows,
//!   the `?` row, `wi_dk83q`'s, `alias_written_name_test`'s, `wi_9wvt7_error_reify_test`'s and one of
//!   `wi_rdns4_shared_row_tail_test`'s; read as the run reads it (an open slot of the asked type
//!   admitted, no rigid one type) instead: 49 rows across six files.
//! * The eta'd callback's check by the predicate (`effects::labels_match_by_subsumption`): the
//!   fixture's rows, the `?` row, and the spec-payload refusals of `wi_n31xx` and
//!   `wi_9wvt7_reify_rule_body_test`.
//! * A bracket's slot nothing fills closed in σ (`slots::open_pattern_slots`):
//!   `a_brackets_open_slot_is_closed_at_the_call`, which then loads and dies at run time.
//! * A `TypePattern` goal's open slot opened in the search (`synth::pattern_goal_opened`): the
//!   member called at a bracket in `a_slot_a_call_leaves_open_in_a_pattern_admits_every_type`.
//! * The evidence of an open slot (`synth::open_slot_beneath_pattern`), and the slot's type read
//!   off it at run time (`builtins::type_of_dictionary`): the rows that run a pattern with one.
//! * A pattern's open slot substituted where a call's spec is (`dict::resolve_var_value_via_subst`),
//!   and a raise of the unknown type asked about (`Interpreter::raised_type_value`): the `?` row.
//! * A pattern's open slot read as stated where a refusal asks whether a call pins its element
//!   (`dict::binding_is_pinned`): the spec-payload refusals, which then load clean.
//!
//! PASS EITHER WAY BY DESIGN: `a_boundary_at_one_instance_leaves_the_other_to_its_caller`'s
//! verdicts and `a_brackets_open_slot_over_one_label_is_that_label`'s (each also fails with a part
//! out, by the fixture), the verdicts this stage keeps.

use anthill_core::eval::{EvalError, Interpreter, Value};

/// The labels a boundary is read from, and the boundaries.
const PROGRAM: &str = r#"
namespace test.bdvyw
  import anthill.prelude.{Int64, String, Error, Result, Option}
  import anthill.prelude.Result.{ok, err}
  import anthill.reflect.{TypePattern}
  sort Boom
    sort Reason = ?
    entity boom(reason: Reason)
  end
  sort Wide
    entity broad(n: Int64)
  end
  sort Narrow
    requires Wide
    entity slim(n: Int64)
  end

  operation both(n: Int64) -> Int64
      effects {Error[Boom[Reason = String]], Error[Boom[Reason = Int64]]} =
    if n < 0 then Error.raise(boom("s")) else if n > 0 then Error.raise(boom(5)) else 0

  -- 071's acceptance: `T1` unwritten over two labels of one sort.
  operation caughtWide(n: Int64) -> Result[E = Boom, T = Int64] = Error.reify(lambda () -> both(n))
  operation wide(n: Int64) -> String =
    match caughtWide(n)
      case ok(_) -> "ok"
      case err(_) -> "caught"

  -- The bracket's open slot, filled from the labels.
  operation caughtWideW(n: Int64) -> Result[E = Boom, T = Int64] =
    Error.reify[T1 = Boom](lambda () -> both(n))
  operation wideW(n: Int64) -> String =
    match caughtWideW(n)
      case ok(_) -> "ok"
      case err(_) -> "caught"

  -- A boundary at one instance leaves the other to its caller, at load and at run time.
  operation narrowInner(n: Int64) -> String effects {Error[Boom[Reason = Int64]]} =
    match Error.reify[T1 = Boom[Reason = String]](lambda () -> both(n))
      case ok(_) -> "ok"
      case err(_) -> "inner"
  operation narrow(n: Int64) -> String =
    match Error.reify(lambda () -> narrowInner(n))
      case ok(s) -> s
      case err(_) -> "outer"

  -- One label: the bracket's slot is that label's, and the caught field is a `String`.
  operation one(n: Int64) -> Int64 effects {Error[Boom[Reason = String]]} =
    if n < 0 then Error.raise(boom("sss")) else 0
  operation oneLength(n: Int64) -> Int64 =
    match Error.reify[T1 = Boom](lambda () -> one(n))
      case ok(_) -> 0
      case err(boom(r)) -> String.length(r)

  -- The wider sort where one refines the other.
  operation wideOrNarrow(n: Int64) -> Int64 effects {Error[Narrow], Error[Wide]} =
    if n < 0 then Error.raise(slim(1)) else if n > 0 then Error.raise(broad(2)) else 0
  operation refined(n: Int64) -> String =
    match Error.reify(lambda () -> wideOrNarrow(n))
      case ok(_) -> "ok"
      case err(_) -> "caught"

  -- A generic boundary: the evidence is built at its caller and forwarded to the `reify`.
  operation catchAt[P](f: () -> Int64 @ {Error[P]}) -> Result[E = P, T = Int64]
      requires TypePattern[T = P] =
    Error.reify[T1 = P](f)
  operation viaCatchAt(n: Int64) -> String =
    match catchAt(lambda () -> both(n))
      case ok(_) -> "ok"
      case err(_) -> "caught"

  -- A bracket's slot nothing fills is open.
  operation nothingRaised() -> String =
    match Error.reify[T1 = Boom](lambda () -> 0)
      case ok(_) -> "ok"
      case err(_) -> "caught"
end
"#;

#[track_caller]
fn answers(interp: &mut Interpreter, op: &str, n: i64) -> String {
    let v = interp
        .call(&format!("test.bdvyw.{op}"), &[Value::Int(n)])
        .unwrap_or_else(|e| panic!("{op}({n}): {e}"));
    crate::common::scalar_str(interp.kb(), &v).unwrap_or_else(|| panic!("{op}: {v:?}"))
}

/// 071'S ACCEPTANCE: `caughtWide`, `T1` unwritten over a thunk raising `Boom[Reason = String]`
/// and `Boom[Reason = Int64]`, loads and catches both; so does its twin written `[T1 = Boom]`,
/// and a generic boundary its caller hands the evidence. Until this stage `T1` was the first
/// label that paired, and the second was left to the caller's row: "undeclared effect:
/// `Error[T = Boom[Reason = Int64]]`".
#[test]
fn a_boundary_over_two_instances_catches_both() {
    let mut interp = crate::common::interp_for(PROGRAM);
    for op in ["wide", "wideW", "viaCatchAt"] {
        assert_eq!(answers(&mut interp, op, -1), "caught", "{op}: boom(\"s\")");
        assert_eq!(answers(&mut interp, op, 1), "caught", "{op}: boom(5)");
        assert_eq!(answers(&mut interp, op, 0), "ok", "{op}: no raise");
    }
}

/// THE CONTROL OF THE ROW ABOVE: a boundary at `Boom[Reason = String]` leaves
/// `Error[Boom[Reason = Int64]]` to its caller — at load, where the caller must declare it, and
/// at run time, where `boom(5)` passes it to the boundary around it. PASSES EITHER WAY BY
/// DESIGN: an instance the bracket writes in full is no pattern this stage reads off labels.
#[test]
fn a_boundary_at_one_instance_leaves_the_other_to_its_caller() {
    let mut interp = crate::common::interp_for(PROGRAM);
    assert_eq!(answers(&mut interp, "narrow", -1), "inner");
    assert_eq!(answers(&mut interp, "narrow", 1), "outer");
    let undeclared = crate::common::replace_in_fixture(
        PROGRAM,
        "operation narrowInner(n: Int64) -> String effects {Error[Boom[Reason = Int64]]} =",
        "operation narrowInner(n: Int64) -> String =",
    );
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&undeclared),
        &["narrowInner.effects", "undeclared effect: Error[T = Boom[Reason = Int64]]"],
        "the label the boundary leaves",
    );
}

/// A BRACKET'S OPEN SLOT IS FILLED FROM THE LABELS, as a bracket's slot is from the arguments
/// (decided with the user 2026-10-27): over one label `Boom[Reason = String]`, `[T1 = Boom]` is
/// that label, so the field of what it catches is a `String`. PASSES EITHER WAY BY DESIGN — it
/// is the verdict this stage keeps, where the pattern exactly as written would refuse
/// `String.length(r)`.
#[test]
fn a_brackets_open_slot_over_one_label_is_that_label() {
    let mut interp = crate::common::interp_for(PROGRAM);
    let v = interp.call("test.bdvyw.oneLength", &[Value::Int(-1)]).expect("caught");
    assert!(matches!(v, Value::Int(3)), "the caught reason is the String \"sss\"; got {v:?}");
}

/// THE WIDER SORT WHERE ONE REFINES THE OTHER: over `Error[Narrow]` and `Error[Wide]`, `sort
/// Narrow requires Wide`, the pattern is `Wide`, which admits both.
#[test]
fn a_boundary_over_a_sort_and_its_refinement_is_at_the_wider() {
    let mut interp = crate::common::interp_for(PROGRAM);
    assert_eq!(answers(&mut interp, "refined", -1), "caught", "slim(1)");
    assert_eq!(answers(&mut interp, "refined", 1), "caught", "broad(2)");
}

/// A BRACKET'S SLOT NOTHING FILLS IS OPEN, and its evidence is built: `Error.reify[T1 =
/// Boom](lambda () -> 0)` was refused at load, no row of `TypePattern` answering at an open
/// slot.
#[test]
fn a_brackets_slot_nothing_fills_is_open() {
    let mut interp = crate::common::interp_for(PROGRAM);
    let v = interp.call("test.bdvyw.nothingRaised", &[]).expect("runs");
    assert_eq!(crate::common::scalar_str(interp.kb(), &v).as_deref(), Some("ok"));
}

/// THE OPEN SLOT IS AN UNKNOWN OF ITS OWN: what a boundary over `Option[T = String]` and
/// `Option[T = Int64]` catches is an `Option` whose element is of a type not known, and a use
/// that needs a `String` of it is refused at load; so is the reason of a `Boom` caught over its
/// two instances. FAILS with the pattern read off one label (`fix_boundary_patterns` backed
/// out): `T1` is the first label, `x` a `String`, and the second label is left to a caller that
/// declares none. PASSES EITHER WAY on how the slot is held — a pattern's open slot, or the slot
/// left out of the type, which a destructured scrutinee closes to an unknown too (MEASURED).
#[test]
fn a_patterns_open_slot_is_an_unknown_of_its_own() {
    for (shape, op) in [
        (
            "Option",
            "  operation either(n: Int64) -> Int64
      effects {Error[Option[T = String]], Error[Option[T = Int64]]} =
    if n < 0 then Error.raise(Option.some(\"s\")) else Error.raise(Option.some(5))
  operation widened(n: Int64) -> Int64 =
    match Error.reify(lambda () -> either(n))
      case ok(_) -> 0
      case err(Option.some(x)) -> String.length(x)
      case err(_) -> 1",
        ),
        (
            "Boom",
            "  operation widened(n: Int64) -> Int64 =
    match Error.reify(lambda () -> both(n))
      case ok(_) -> 0
      case err(boom(r)) -> String.length(r)",
        ),
    ] {
        let src = crate::common::replace_in_fixture(
            PROGRAM,
            "  -- A bracket's slot nothing fills is open.",
            &format!("{op}\n  -- A bracket's slot nothing fills is open."),
        );
        let errs = crate::common::load_errors_of(&src);
        assert_eq!(errs.len(), 1, "{shape}: the one refusal is the element's use; got {errs:#?}");
        crate::common::assert_refused_naming(&errs, &["length.s", "expected String, got ?"], shape);
    }
}

/// A BRACKET'S SLOT NOTHING FILLS IS CLOSED AT THE CALL, as one the labels leave open is: inside
/// `viaR[R]`, `Error.reify[T1 = Boom](f)` over an `f` raising only the caller's row `R` reads
/// nothing off a label, its pattern is `Boom` open at `Reason`, and what it catches has a
/// reason of a type not known — `String.length(r)` is refused. The boundary catches every
/// `Boom` there, a `boom(5)` raised through `R` included (`caught`, 0). FAILS with the slot left
/// the variable the bracket wrote (`open_pattern_slots` backed out; the evidence is still built
/// open beneath the pattern): `String.length(r)` binds it to `String`, the program loads, and
/// `viaR(lambda () -> raiseInt())` dies at run time, "expected String, got Int64" (MEASURED).
#[test]
fn a_brackets_open_slot_is_closed_at_the_call() {
    let program = |arm: &str| {
        format!(
            r#"
namespace test.bdvyw.closed
  import anthill.prelude.{{Int64, String, Error, Result}}
  import anthill.prelude.Result.{{ok, err}}
  sort Boom
    sort Reason = ?
    entity boom(reason: Reason)
  end
  operation viaR[R](f: () -> Int64 @ {{R}}) -> Int64 effects {{R}} =
    match Error.reify[T1 = Boom](f)
      case ok(n) -> n
      case {arm}
  operation raiseInt() -> Int64 effects {{Error[Boom[Reason = Int64]]}} = Error.raise(boom(5))
  operation caught() -> Int64 effects {{Error[Boom[Reason = Int64]]}} = viaR(lambda () -> raiseInt())
end
"#
        )
    };
    let errs = crate::common::load_errors_of(&program("err(boom(r)) -> String.length(r)"));
    crate::common::assert_refused_naming(&errs, &["length.s", "expected String, got ?"], "the reason read as a String");
    let mut interp = crate::common::interp_for(&program("err(_) -> 0"));
    let v = interp.call("test.bdvyw.closed.caught", &[]).expect("caught");
    assert!(matches!(v, Value::Int(0)), "the open boundary catches `boom(5)`; got {v:?}");
}

/// WI-20261015-D2KZ5: LABELS OF SORTS NO ONE SORT HEADS ARE REFUSED, and the verdict does not
/// follow the order the thunk raises them in — the two branch orders of an `if`, and an eta'd
/// callee whose row lists them in either order. Until this stage `T1` was the first label that
/// paired: one order loaded and caught the division, the other was refused for its result type.
/// The bracket, `[T1 = DivisionByZero]`, is the repair, and loads
/// (`wi_9wvt7_guarded_callback_row_test::a_guarded_label_beside_another_is_caught_at_its_own_boundary`).
#[test]
fn labels_no_one_sort_heads_are_refused_in_either_order() {
    let program = |body: &str, callee_row: &str| {
        format!(
            r#"
namespace test.bdvyw.two
  import anthill.prelude.{{Int64, String, Error, Result, DivisionByZero}}
  operation raisesBoth() -> Int64 effects {callee_row} = 10 / 0
  operation twoLabels(a: Int64, b: Int64) -> Result[E = DivisionByZero, T = Int64]
      effects {{Error[String]}} =
    {body}
end
"#
        )
    };
    let row = "{Error[DivisionByZero]}";
    for (body, callee_row) in [
        ("Error.reify(lambda () -> if a < 0 then Error.raise(\"negative\") else a / b)", row),
        ("Error.reify(lambda () -> if a >= 0 then a / b else Error.raise(\"negative\"))", row),
        ("Error.reify(raisesBoth)", "{Error[String], Error[DivisionByZero]}"),
        ("Error.reify(raisesBoth)", "{Error[DivisionByZero], Error[String]}"),
    ] {
        let errs = crate::common::load_errors_of(&program(body, callee_row));
        crate::common::assert_refused_naming(
            &errs,
            &["which no one sort heads", "`reify[T1 = …](…)`"],
            &format!("{body} over {callee_row}"),
        );
    }
}

/// TWO SORTS THAT REFINE A THIRD ARE NOT HEADED BY EITHER, and are refused as unrelated ones
/// are: the boundary is told which it catches.
#[test]
fn two_refinements_of_one_sort_are_refused() {
    let src = r#"
namespace test.bdvyw.sib
  import anthill.prelude.{Int64, Error, Result}
  sort Wide
    entity wide(n: Int64)
  end
  sort Left
    requires Wide
    entity left(n: Int64)
  end
  sort Right
    requires Wide
    entity right(n: Int64)
  end
  operation either(n: Int64) -> Int64 effects {Error[Left], Error[Right]} =
    if n < 0 then Error.raise(left(1)) else Error.raise(right(2))
  operation caught(n: Int64) -> Result[E = Wide, T = Int64] = Error.reify(lambda () -> either(n))
  operation caughtAtWide(n: Int64) -> Result[E = Wide, T = Int64] =
    Error.reify[T1 = Wide](lambda () -> either(n))
end
"#;
    let errs = crate::common::load_errors_of(src);
    crate::common::assert_refused_naming(&errs, &["which no one sort heads"], "Left and Right");
    assert_eq!(errs.len(), 1, "the bracketed twin loads; got {errs:#?}");
}

/// A TYPE PATTERN'S SLOT A CALL LEAVES OPEN IS OPEN, at any call that requires one — not only
/// at a boundary: `admitsAt[P = Boom](t)` answers by the open pattern, and so does the member
/// called at the bracket, `TypePattern.admits[T = Boom](t)`; both were refused at load, no row of
/// `TypePattern` answering there. A `TypeValue` at such a type still has no instance
/// (`wi_sqzpq_type_pattern_test::a_type_value_call_at_an_open_slot_is_refused_at_load`). The member
/// call FAILS with a `TypePattern` goal's open slots searched as written (`synth::pattern_goal_opened`).
#[test]
fn a_slot_a_call_leaves_open_in_a_pattern_admits_every_type() {
    let src = r#"
namespace test.bdvyw.slot
  import anthill.prelude.{Int64, String, Type, Bool}
  import anthill.reflect.{TypePattern}
  sort Boom
    sort Reason = ?
    entity boom(reason: Reason)
  end
  sort Other
    entity other(n: Int64)
  end
  operation admitsAt[P](t: Type) -> Bool requires TypePattern[T = P] = TypePattern.admits[T = P](t)
  operation atInt() -> Bool = admitsAt[P = Boom](Boom[Reason = Int64])
  operation atString() -> Bool = admitsAt[P = Boom[Reason = ?]](Boom[Reason = String])
  operation atOther() -> Bool = admitsAt[P = Boom](Other)
  operation direct() -> Bool = TypePattern.admits[T = Boom](Boom[Reason = Int64])
  operation directOther() -> Bool = TypePattern.admits[T = Boom](Other)
end
"#;
    let mut interp = crate::common::interp_for(src);
    for (op, want) in [
        ("atInt", true),
        ("atString", true),
        ("atOther", false),
        ("direct", true),
        ("directOther", false),
    ] {
        let v = interp
            .call(&format!("test.bdvyw.slot.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op}: {e}"));
        assert!(matches!(v, Value::Bool(b) if b == want), "{op}: want {want}, got {v:?}");
    }
}

/// A host operation whose row says only `Error`, raising a `Boom` of the program's.
const UNKNOWN: &str = r#"
namespace test.bdvyw.unknown
  import anthill.prelude.{Int64, String, Error, Result}
  import anthill.prelude.Result.{ok, err}
  sort Boom
    entity boom(why: String)
  end
  operation mkBoom() -> Boom = boom("host")
  sort Host
    import anthill.prelude.{Int64, Error}
    entity host
    operation go() -> Int64 effects {Error} @[host_implemented]
  end
  provides Host language rust
    artifact "nowhere.rs"
    operation_map {
      go: "bdvyw_go"
    }
  end
  operation catchAll() -> String =
    match Error.reify(lambda () -> Host.go())
      case ok(_) -> "ok"
      case err(_) -> "caught"
  operation atBoom() -> String effects {Error} =
    match Error.reify[T1 = Boom](lambda () -> Host.go())
      case ok(_) -> "ok"
      case err(_) -> "inner"
  operation pastBoom() -> String =
    match Error.reify(lambda () -> atBoom())
      case ok(s) -> s
      case err(_) -> "outer"
end
"#;

fn unknown_interp() -> Interpreter {
    // NOT THE RECIPE, BY NAME: the host function must be registered before the load, whose
    // `operation_map` names it.
    let kb = crate::common::try_load_kb_prepared(UNKNOWN, |kb| {
        kb.register_host_fn("bdvyw_go", 0, |interp, _| {
            let payload = interp.call("test.bdvyw.unknown.mkBoom", &[])?;
            Err(interp.raise_error(payload))
        })
        .expect("register bdvyw_go");
    })
    .unwrap_or_else(|errs| panic!("the fixture must load: {errs:#?}"));
    let mut interp = Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    interp
}

/// THE PATTERN `?`: a thunk whose only `Error` label is the bare one is reified at the pattern
/// that admits every type (decided with the user 2026-10-27), and its boundary catches what the
/// host function raises, of the unknown type (stage (d)'s `RaisedType::Unknown`). Until this
/// stage `T1` was unconstrained there and the call refused at load. A boundary at `Boom` lets
/// the same raise pass, though its payload is a `Boom`: the row said only `Error`, and the
/// `?` around it catches it.
#[test]
fn the_pattern_question_mark_catches_a_raise_of_the_unknown_type() {
    let mut interp = unknown_interp();
    for (op, want) in [("catchAll", "caught"), ("pastBoom", "outer")] {
        let v = interp
            .call(&format!("test.bdvyw.unknown.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op}: {e}"));
        assert_eq!(crate::common::scalar_str(interp.kb(), &v).as_deref(), Some(want), "{op}");
    }
    match interp.call("test.bdvyw.unknown.atBoom", &[]) {
        Err(EvalError::Raised { .. }) => {}
        other => panic!("the `Boom` boundary lets the raise of the unknown type pass; got {other:?}"),
    }
}
