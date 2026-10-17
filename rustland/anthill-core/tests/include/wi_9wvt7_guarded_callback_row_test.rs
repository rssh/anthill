//! WI-20260908-9WVT7 — `Error.reify` catches a GUARDED raise: a division by a variable, the
//! `head` of a list.
//!
//! `div` declares `effects {Error[DivisionByZero] :- eq(b, 0)}` and `List.head` declares
//! `{Error[EmptyStream] :- isEmpty(xs)}`. A call whose guard is not refuted keeps the
//! callee's `guarded(label, guard)` atom in its effects (WI-067), with the guard over the
//! callee's own parameters, and an operation's own row holds such atoms and absences as it
//! was written. `Error.reify(lambda () -> a / b)` was refused at load: "the lambda argument
//! declares `Error[T = DivisionByZero]`, which the closed row does not admit". Three repairs:
//!
//!   (1) A FUNCTION VALUE'S ROW IS WHAT APPLYING IT INCURS. `make_arrow_value` (the row of a
//!       lambda and of an eta'd operation) put every element in `present(…)`, so a guarded
//!       atom became a label named `guarded(…)` and an absence a label named `-X`; and it
//!       kept two atoms of one label (a dispatched `a / b` carries the spec operation's and
//!       the implementation's), which a reader that counts labels refused. It now reads
//!       each element as the operation boundary does (`explode_incurred_effect_row`): a
//!       guarded atom is its label, an absence nothing, and the row is a set.
//!   (2) A ROW IS A SET WHEN TWO ROWS ARE PAIRED. A label that pairs with nothing but
//!       equals, under the bindings made so far, a label of its row that did pair is that
//!       element again (`match_present_labels`), not an extra one for the other row's tail.
//!   (3) A GUARDED ATOM OF A CALLBACK SLOT ADMITS NO LABEL (proposal 048's lattice: `{E} <:
//!       {E :- g}` needs `g` entailed, and an undecided entailment refuses). The decomposition
//!       reads the slot's `E :- g` as `E`, so a callback raising `E` anywhere passed a slot
//!       that promises its operation `E` only under `g`, and the raise escaped a `main` that
//!       declares no `Error`.
//!
//! THE FIRST SHAPE OF (1) PLACED THE GUARDED ATOM BARE, and that was unsound: the atom's
//! guard names the callee's parameters, the multi-tail absorb copies a lambda's row whole
//! into a row variable, and a later call to the same operation refuted the guard with its
//! own arguments and dropped the effect. `a_guard_is_no_part_of_a_values_type` is that
//! program.
//!
//! WHAT FAILS UNDER WHICH BACK-OUT — MEASURED, each switched off alone in one build:
//!
//!   * (1) backed out → the ten rows over a guarded raise, an absence or a repeated label:
//!     every row of `CAUGHT`, `a_value_row_holds_each_label_once`,
//!     `a_slot_denying_error_refuses_a_division_callback` (the opaque label passed the
//!     denial) and `a_guarded_slot_admits_no_callback_label` (its guarded callbacks are
//!     refused for the opaque label instead, and its control is refused).
//!   * (1) with the guarded atom placed bare (the first shape) →
//!     `a_guard_is_no_part_of_a_values_type`, and `a_value_row_holds_each_label_once`,
//!     whose two atoms stay two.
//!   * (2) backed out → `labels_made_equal_by_the_pairing_are_one_element`.
//!   * (3) backed out → `a_guarded_slot_admits_no_callback_label`.
//!
//! Each fixture holds the operations one back-out refuses, so a refused load does not take
//! another repair's rows with it.
//!
//! PASSES EITHER WAY BY DESIGN: `a_raise_admitted_into_a_slot_is_not_lost` — a slot that
//! admits a guarded callback still charges its caller for what the callback raises.

use crate::common::assert_refused_naming;
use anthill_core::eval::{EvalError, Interpreter, Value};

/// The operations that need only (1).
const CAUGHT: &str = r#"
namespace test.gcb
  import anthill.prelude.{Int64, String, List, Error, Result, DivisionByZero, EmptyStream}
  import anthill.prelude.DivisionByZero.{division_by_zero}
  import anthill.prelude.List.{head, cons, nil}
  import anthill.prelude.PartialEq.{eq}

  -- `b` is a parameter, so the guard `eq(b, 0)` is not refuted and the label stays.
  operation safeDiv(a: Int64, b: Int64) -> Result[E = DivisionByZero, T = Int64] =
    Error.reify(lambda () -> a / b)

  operation safeDivLet(a: Int64, b: Int64) -> Result[E = DivisionByZero, T = Int64] =
    let f = lambda () -> a / b
    Error.reify(f)

  operation firstOf(xs: List[T = Int64]) -> Result[E = EmptyStream, T = Int64] =
    Error.reify(lambda () -> head(xs))

  operation emptyHead() -> Result[E = EmptyStream, T = Int64] = firstOf(nil)
  operation fiveHead() -> Result[E = EmptyStream, T = Int64] = firstOf(cons(5, nil))

  operation raisesDbz(who: String) -> Int64 effects {Error[DivisionByZero]} =
    Error.raise(division_by_zero(who))

  operation guardedSeven(b: Int64) -> Int64 effects {Error[DivisionByZero] :- eq(b, 0)} =
    if b === 0 then raisesDbz("guardedSeven") else 7

  -- One label twice in one lambda's row, unguarded and guarded; no dispatch.
  operation bothCopies(b: Int64) -> Result[E = DivisionByZero, T = Int64] =
    Error.reify(lambda () -> if b < 0 then raisesDbz("bothCopies") else guardedSeven(b))

  -- Two labels: the boundary is written at the guarded one, the other stays in the
  -- caller's row.
  operation twoLabels(a: Int64, b: Int64) -> Result[E = DivisionByZero, T = Int64]
      effects {Error[String]} =
    Error.reify[T1 = DivisionByZero](lambda () -> if a < 0 then Error.raise("negative") else a / b)

  -- Slots that declare the label and re-raise it: a lambda, and an eta'd guarded operation.
  operation run[Rho](f: () -> Int64 @ {Error[DivisionByZero], Rho}) -> Int64
      effects {Error[DivisionByZero], Rho} = f()

  operation viaRun(a: Int64, b: Int64) -> Int64 effects {Error[DivisionByZero]} =
    run(lambda () -> a / b)

  operation runAt(f: (Int64) -> Int64 @ {Error[DivisionByZero]}, b: Int64) -> Int64
      effects {Error[DivisionByZero]} = f(b)

  operation viaRunEta(b: Int64) -> Int64 effects {Error[DivisionByZero]} = runAt(guardedSeven, b)

  -- An absence is the callee's claim about its own body, no effect of the value.
  operation ping(x: Int64) -> Int64 effects { -Error } = x + 1
  operation runPure(f: (Int64) -> Int64 @ {}, x: Int64) -> Int64 = f(x)
  operation pingEta(x: Int64) -> Int64 = runPure(ping, x)
  operation pingLambda(x: Int64) -> Int64 = runPure(lambda (y: Int64) -> ping(y), x)
  operation pingCaught(a: Int64, b: Int64) -> Result[E = DivisionByZero, T = Int64] =
    Error.reify(lambda () -> ping(a) + a / b)

  -- A row variable's binding beside a declared label of the same name: `runE`'s incurred
  -- effects hold `Error[DivisionByZero]` twice.
  operation runE[R](f: () -> Int64 @ {R}) -> Int64 effects {Error[DivisionByZero], R} = f()
  operation viaRunE() -> Result[E = DivisionByZero, T = Int64] =
    Error.reify(lambda () -> runE(lambda () -> raisesDbz("runE")))
end
"#;

/// A provision at a function type, its closed row matched against a value's row: its own
/// fixture, because a row that keeps both atoms of `10 / x` refuses this call at load.
const PROVIDED: &str = r#"
namespace test.gcb3
  import anthill.prelude.{Int64, Error, DivisionByZero}
  sort Apply
    sort F = ?
    operation call(f: F) -> Int64
  end
  sort Q
    provides Apply[F = (Int64) -> Int64 @ {Error[DivisionByZero]}]
    operation call(f: (Int64) -> Int64 @ {Error[DivisionByZero]}) -> Int64 = 40
  end
  operation applied() -> Int64 = Apply.call(lambda (x: Int64) -> 10 / x)
end
"#;

/// The operation that needs (2): `zq`'s eta'd row is `{Error[Q], Error[DivisionByZero]}`, two
/// labels until the pairing binds `Q := DivisionByZero`.
const PAIRED: &str = r#"
namespace test.gcb2
  import anthill.prelude.{Int64, Error, Result, DivisionByZero}
  import anthill.prelude.DivisionByZero.{division_by_zero}
  operation zq[Q]() -> Int64 effects {Error[Q], Error[DivisionByZero]} =
    Error.raise(division_by_zero("zq"))
  operation caughtZq() -> Result[E = DivisionByZero, T = Int64] =
    Error.reify[T1 = DivisionByZero](zq)
end
"#;

#[track_caller]
fn call(interp: &mut Interpreter, op: &str, args: &[i64]) -> Result<Value, EvalError> {
    let args: Vec<Value> = args.iter().map(|n| Value::Int(*n)).collect();
    interp.call(op, &args)
}

/// The `op` of a `division_by_zero` payload.
#[track_caller]
fn division_op(interp: &Interpreter, payload: &Value) -> String {
    assert_eq!(
        crate::common::constructor_qn(interp.kb(), payload),
        "anthill.prelude.DivisionByZero.division_by_zero"
    );
    let op = crate::common::entity_field(interp.kb(), payload, "op", 0);
    crate::common::scalar_str(interp.kb(), &op).expect("`op` is a String")
}

/// The `op` of the `division_by_zero` an `err` arm carries.
#[track_caller]
fn caught_division(interp: &Interpreter, result: &Value) -> String {
    division_op(interp, &crate::common::result_err_payload(interp.kb(), result))
}

/// The `op` of the `division_by_zero` a raise carried out of the call.
#[track_caller]
fn raised_division(interp: &Interpreter, e: EvalError) -> String {
    let EvalError::Raised { payload, .. } = e else {
        panic!("expected EvalError::Raised, got {e:?}");
    };
    division_op(interp, &payload)
}

fn int_value(interp: &Interpreter, v: &Value) -> i64 {
    crate::common::scalar_int(interp.kb(), v)
        .unwrap_or_else(|| panic!("expected an Int64, got {v:?}"))
}

/// THE ACCEPTANCE. A division by a parameter is caught by the boundary around it, and the
/// payload `Int64.div` built arrives as the `err` arm; a non-zero divisor is the `ok` arm.
/// The `let`-held lambda is the same callback written another way.
#[test]
fn a_guarded_division_is_caught() {
    let mut interp = crate::common::interp_for(CAUGHT);
    let r = call(&mut interp, "test.gcb.safeDiv", &[7, 0]).expect("the division is caught");
    assert_eq!(caught_division(&interp, &r), "Int64.div");
    let r = call(&mut interp, "test.gcb.safeDiv", &[7, 2]).expect("no raise");
    assert_eq!(crate::common::result_ok_int(interp.kb(), &r), 3);
    let r = call(&mut interp, "test.gcb.safeDivLet", &[7, 0]).expect("a let-held lambda");
    assert_eq!(caught_division(&interp, &r), "Int64.div");
}

/// The other guarded raiser of the prelude: `List.head` of an empty list.
#[test]
fn a_guarded_head_is_caught() {
    let mut interp = crate::common::interp_for(CAUGHT);
    let r = call(&mut interp, "test.gcb.emptyHead", &[]).expect("the head of nil is caught");
    assert_eq!(crate::common::constructor_qn(interp.kb(), &r), "anthill.prelude.Result.err");
    let payload = crate::common::entity_field(interp.kb(), &r, "error", 0);
    assert_eq!(
        crate::common::constructor_qn(interp.kb(), &payload),
        "anthill.prelude.EmptyStream.empty_stream"
    );
    let r = call(&mut interp, "test.gcb.fiveHead", &[]).expect("the head of a list");
    assert_eq!(crate::common::result_ok_int(interp.kb(), &r), 5);
}

/// An unguarded and a guarded copy of one label in one lambda's row are one element of it:
/// both raises are caught by the one boundary, and the caller declares no effect.
#[test]
fn two_copies_of_one_label_are_one_element() {
    let mut interp = crate::common::interp_for(CAUGHT);
    let r = call(&mut interp, "test.gcb.bothCopies", &[-1]).expect("the unguarded raise");
    assert_eq!(caught_division(&interp, &r), "bothCopies");
    let r = call(&mut interp, "test.gcb.bothCopies", &[0]).expect("the guarded raise");
    assert_eq!(caught_division(&interp, &r), "guardedSeven");
    let r = call(&mut interp, "test.gcb.bothCopies", &[1]).expect("no raise");
    assert_eq!(crate::common::result_ok_int(interp.kb(), &r), 7);
}

/// Beside a second label, a boundary written at the guarded one catches the division and
/// lets the `String` raise past it, as the caller's row says.
#[test]
fn a_guarded_label_beside_another_is_caught_at_its_own_boundary() {
    let mut interp = crate::common::interp_for(CAUGHT);
    let r = call(&mut interp, "test.gcb.twoLabels", &[7, 0]).expect("the division is caught");
    assert_eq!(caught_division(&interp, &r), "Int64.div");
    match call(&mut interp, "test.gcb.twoLabels", &[-1, 0]).expect_err("the String escapes") {
        EvalError::Raised { payload, .. } => assert_eq!(
            crate::common::scalar_str(interp.kb(), &payload).as_deref(),
            Some("negative")
        ),
        other => panic!("expected EvalError::Raised, got {other:?}"),
    }
}

/// Not a `reify` rule: any slot that declares the label admits a guarded callback, a lambda
/// or an eta'd operation, and the raise reaches the slot's caller.
#[test]
fn a_slot_declaring_the_label_admits_a_guarded_callback() {
    let mut interp = crate::common::interp_for(CAUGHT);
    let v = call(&mut interp, "test.gcb.viaRun", &[7, 7]).expect("no raise");
    assert_eq!(int_value(&interp, &v), 1);
    let e = call(&mut interp, "test.gcb.viaRun", &[7, 0]).expect_err("the slot re-raises");
    assert_eq!(raised_division(&interp, e), "Int64.div");
    let v = call(&mut interp, "test.gcb.viaRunEta", &[3]).expect("the eta'd operation returns");
    assert_eq!(int_value(&interp, &v), 7);
    let e = call(&mut interp, "test.gcb.viaRunEta", &[0]).expect_err("the eta'd operation raises");
    assert_eq!(raised_division(&interp, e), "guardedSeven");
}

/// An absence an operation declares is no effect of it as a value: eta'd or applied in a
/// lambda it passes a closed `@ {}` slot, and a boundary around a body calling it catches.
#[test]
fn an_absence_is_no_effect_of_the_value() {
    let mut interp = crate::common::interp_for(CAUGHT);
    let v = call(&mut interp, "test.gcb.pingEta", &[4]).expect("the eta'd operation");
    assert_eq!(int_value(&interp, &v), 5);
    let v = call(&mut interp, "test.gcb.pingLambda", &[4]).expect("the lambda");
    assert_eq!(int_value(&interp, &v), 5);
    let r = call(&mut interp, "test.gcb.pingCaught", &[7, 0]).expect("the division is caught");
    assert_eq!(caught_division(&interp, &r), "Int64.div");
    let r = call(&mut interp, "test.gcb.pingCaught", &[7, 7]).expect("no raise");
    assert_eq!(crate::common::result_ok_int(interp.kb(), &r), 9);
}

/// A row variable bound beside a declared label of the same name gives one label, not two.
#[test]
fn a_label_a_row_variable_repeats_is_caught_once() {
    let mut interp = crate::common::interp_for(CAUGHT);
    let r = call(&mut interp, "test.gcb.viaRunE", &[]).expect("the raise is caught");
    assert_eq!(caught_division(&interp, &r), "runE");
}

/// A provision at `(Int64) -> Int64 @ {Error[DivisionByZero]}` answers `10 / x`, whose
/// effects hold the label twice: the provision's closed row matches the value's as a set.
#[test]
fn a_value_row_holds_each_label_once() {
    let mut interp = crate::common::interp_for(PROVIDED);
    let v = call(&mut interp, "test.gcb3.applied", &[]).expect("the provision answers");
    assert_eq!(int_value(&interp, &v), 40);
}

/// Two labels of one row that the pairing itself makes equal are one element: `Error[Q]`
/// pairs with `Error[T1 = DivisionByZero]`, and `Error[DivisionByZero]` is then that element.
#[test]
fn labels_made_equal_by_the_pairing_are_one_element() {
    let mut interp = crate::common::interp_for(PAIRED);
    let r = call(&mut interp, "test.gcb2.caughtZq", &[]).expect("the raise is caught");
    assert_eq!(caught_division(&interp, &r), "zq");
}

/// A slot whose row holds `Error[DivisionByZero] :- eq(x, 0)` promises its operation that
/// the callback raises only at `x = 0`, and the operation's own row is checked on that
/// promise: `runG` declares `:- eq(b, 0)`, so `runG(…, 5)` is typed pure. A callback raising
/// on its captured `k`, an eta'd operation raising at `x = 1`, and an unguarded raiser are
/// refused there; each loaded before and raised out of a `main` declaring no `Error`
/// (MEASURED; the unguarded one on every build before this). The same lambda into a slot
/// that declares the label unguarded loads — the control. A callback that does meet the
/// guard (`lambda (x) -> 35 / x`) is refused too: entailment between two guards is not
/// decided, and 048's rule is that an undecided entailment refuses.
#[test]
fn a_guarded_slot_admits_no_callback_label() {
    let slot = |callback: &str, extra: &str| {
        format!(
            r#"
namespace test.gcb_slot
  import anthill.prelude.{{Int64, String, Error, DivisionByZero}}
  import anthill.prelude.DivisionByZero.{{division_by_zero}}
  import anthill.prelude.PartialEq.{{eq}}
  operation runG(f: (x: Int64) -> Int64 @ {{Error[DivisionByZero] :- eq(x, 0)}}, b: Int64)
      -> Int64 effects {{Error[DivisionByZero] :- eq(b, 0)}} = f(b)
  {extra}
  operation user(k: Int64) -> Int64 = runG({callback}, 5)
end
"#
        )
    };
    let on_one = "operation onOne(x: Int64) -> Int64 effects {Error[DivisionByZero] :- eq(x, 1)} =
    if x === 1 then Error.raise(division_by_zero(\"onOne\")) else x";
    let raiser = "operation raisesDbz(who: String) -> Int64 effects {Error[DivisionByZero]} =
    Error.raise(division_by_zero(who))";
    for (callback, extra, why) in [
        (
            "lambda (x) -> 7 / k",
            "",
            "a callback raising on its captured value",
        ),
        (
            "onOne",
            on_one,
            "an eta'd operation guarded on another value",
        ),
        (
            "lambda (x) -> raisesDbz(\"twin\")",
            raiser,
            "an unguarded raiser",
        ),
    ] {
        assert_refused_naming(
            &crate::common::load_errors_of(&slot(callback, extra)),
            &["runG.f", "only under a guard"],
            why,
        );
    }
    let unguarded_slot = r#"
namespace test.gcb_slot_plain
  import anthill.prelude.{Int64, Error, DivisionByZero}
  operation runP(f: (x: Int64) -> Int64 @ {Error[DivisionByZero]}, b: Int64) -> Int64
      effects {Error[DivisionByZero]} = f(b)
  operation user(k: Int64) -> Int64 effects {Error[DivisionByZero]} = runP(lambda (x) -> 7 / k, 5)
end
"#;
    let errs = crate::common::load_errors_of(unguarded_slot);
    assert!(
        errs.is_empty(),
        "the control: an unguarded slot admits it: {errs:#?}"
    );
}

/// A slot denying `Error` refuses a division callback. Before (1) the guarded atom was a
/// label named `guarded(…)`, which no denial names, so the program loaded (MEASURED). The
/// refusal is the unconstrained row variable: binding `Rho` to the division's label is
/// what the denial forbids, as for an unguarded raiser. Without the denial the same call
/// loads — the control that the denial is what refuses. A denial of the label itself is
/// named in its own refusal.
#[test]
fn a_slot_denying_error_refuses_a_division_callback() {
    let denies = |row: &str| {
        format!(
            r#"
namespace test.gcb_deny
  import anthill.prelude.{{Int64, Error, DivisionByZero}}
  operation run5[Rho](f: () -> Int64 @ {row}) -> Int64 effects {{Rho}} = f()
  operation t(a: Int64, b: Int64) -> Int64 effects {{Error[DivisionByZero]}} =
    run5(lambda () -> a / b)
end
"#
        )
    };
    assert_refused_naming(
        &crate::common::load_errors_of(&denies("{Rho, -Error}")),
        &[
            "run5.type_arg",
            "expected a type for 'Rho', got unconstrained",
        ],
        "a slot denying Error",
    );
    let errs = crate::common::load_errors_of(&denies("{Rho}"));
    assert!(
        errs.is_empty(),
        "the control: without the denial it loads: {errs:#?}"
    );

    let denies_the_label = r#"
namespace test.gcb_deny_label
  import anthill.prelude.{Int64, String, Error, DivisionByZero}
  operation run3(f: () -> Int64 @ {Error[String], -Error[DivisionByZero]}) -> Int64
      effects {Error[String]} = f()
  operation t(a: Int64, b: Int64) -> Int64 effects {Error[String]} = run3(lambda () -> a / b)
end
"#;
    assert_refused_naming(
        &crate::common::load_errors_of(denies_the_label),
        &["to lack `Error[T = DivisionByZero]`"],
        "a slot denying the label",
    );
}

/// A GUARD IS NO PART OF A VALUE'S TYPE. With the guarded atom placed bare in the lambda's
/// row, the multi-tail absorb bound `h`'s `Rho` to that row, and the outer call `h(…, 5)`
/// refuted the inner call's guard `eq(h.d, 0)` with its own argument: `outer` loaded and
/// raised `division_by_zero(op: "h")` out of a `main` declaring no `Error` (MEASURED). The
/// value's row holding the label, the inner raise is `outer`'s to declare. And a stream whose
/// row came from such a lambda distributes a denial and a guard over it.
#[test]
fn a_guard_is_no_part_of_a_values_type() {
    let collide = r#"
namespace test.gcb_collide
  import anthill.prelude.{Int64, String, Error, DivisionByZero}
  import anthill.prelude.DivisionByZero.{division_by_zero}
  import anthill.prelude.PartialEq.{eq}
  operation raisesDbz(who: String) -> Int64 effects {Error[DivisionByZero]} =
    Error.raise(division_by_zero(who))
  operation h[Rho](f: () -> Int64 @ {Rho}, d: Int64) -> Int64
      effects {Rho, Error[DivisionByZero] :- eq(d, 0)} =
    if d === 0 then raisesDbz("h") else f()
  operation outer[R1, R2](g: () -> Int64 @ {R1}, k: () -> Int64 @ {R2}) -> Int64
      effects {R1, R2} =
    h(lambda () -> g() + k() + h(lambda () -> 1, 0), 5)
end
"#;
    assert_refused_naming(
        &crate::common::load_errors_of(collide),
        &[
            "outer.effects",
            "undeclared effect: Error[T = DivisionByZero]",
        ],
        "the inner call's raise is the caller's",
    );

    let distribute = r#"
namespace test.gcb_distribute
  import anthill.prelude.{Int64, Error, DivisionByZero, Bool, todo}
  import anthill.prelude.PartialEq.{eq}
  sort Strm
    sort T = ?
    effects E = ?
    operation each[EffP](s: Self, f: (x: Int64) -> Bool @ {EffP, -s.E}) -> Bool effects {EffP} = true
    operation obs(s: Self, d: Int64) -> Bool effects {s.E :- eq(d, 0)} = true
  end
  operation mk[R](f: () -> Int64 @ {R}) -> Strm[T = Int64, E = {R}] = todo()
  operation both[R1, R2](f: () -> Int64 @ {R1}, g: () -> Int64 @ {R2}, a: Int64, b: Int64)
      -> Bool effects {R1, R2, Error[DivisionByZero]} =
    Strm.each(mk(lambda () -> f() + g() + a / b), lambda (x: Int64) -> true)
  operation both2[R1, R2](f: () -> Int64 @ {R1}, g: () -> Int64 @ {R2}, a: Int64, b: Int64,
                          d: Int64) -> Bool effects {R1, R2, Error[DivisionByZero]} =
    Strm.obs(mk(lambda () -> f() + g() + a / b), d)
end
"#;
    let errs = crate::common::load_errors_of(distribute);
    assert!(
        errs.is_empty(),
        "a denial and a guard distribute over the row: {errs:#?}"
    );
}

/// PASSES EITHER WAY BY DESIGN. A slot that re-raises still charges its caller: a caller
/// declaring nothing is refused, before (1) at the slot and after it at its own row.
#[test]
fn a_raise_admitted_into_a_slot_is_not_lost() {
    let pure_caller = r#"
namespace test.gcb_lost
  import anthill.prelude.{Int64, Error, DivisionByZero}
  operation run[Rho](f: () -> Int64 @ {Error[DivisionByZero], Rho}) -> Int64
      effects {Error[DivisionByZero], Rho} = f()
  operation t(a: Int64, b: Int64) -> Int64 = run(lambda () -> a / b)
end
"#;
    assert_refused_naming(
        &crate::common::load_errors_of(pure_caller),
        &["DivisionByZero"],
        "a caller that declares no effect",
    );
}
