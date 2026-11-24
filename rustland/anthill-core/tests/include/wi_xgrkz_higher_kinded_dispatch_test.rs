//! WI-20261024-XGRKZ — A DISPATCH AT A HIGHER-KINDED BINDING WRITTEN AS A BARE CONSTRUCTOR.
//!
//! `sort Lift[C, F[T]]` with `Car provides Lift[C = Self, F = Option]`: `F = Option` is a
//! constructor unapplied, and `Car`'s member takes `x: Option[T = Int64]`, the `F[T = Int64]`
//! that `F = Option` makes. Before: `Lift.lift(car(n: 1), some(1))` was refused, "no impl
//! matches", and so was every other argument — the well-typed call, the ill-typed `some("s")`
//! and `5` alike — so nothing told them apart. Three parts were wrong:
//!
//! * the dispatch read `F`'s fill (`Option`) as the call's carrier, found no provision BY
//!   `Option`, and refused; `F` is no carrier of the call, only what `Car`'s provision makes
//!   it, and the call dispatches at `C = Car` (`apply.rs`, `other_provider_at_c`);
//! * `F` was bound only by the late pass, after the arguments were typed, so an argument at
//!   `F[T = Int64]` was typed with `F` free (`bind_spec_params_from_carrier_param` now binds a
//!   higher-kinded slot's bare constructor before them);
//! * the argument check read `F[T = Int64]` through the pure σ walk, which leaves the head as
//!   written, so even with `F := Option` the pair read as open and was checked against nothing
//!   (`validate_arg_against_param` fills the head, `fill_higher_kinded_heads`).
//!
//! THE BARE `5` AT `F = Option` IS `some(5)` (decided with the user, 2026-11-23): the slot is
//! `Option[T = Int64]` at that call, where the some-coercion wraps a bare `Int64`
//! (kernel-language, "`some`-coercion (WI-408)") — one reading for the spec's call and the
//! member's, `Car.lift(car(n: 1), 5)` answering the same. A bare `Int64` is refused naming the
//! argument where the constructor is one no coercion reaches: `F = List`.
//!
//! BACK-OUTS: measured, listed at the end of this file.

use crate::common::{interp_for, load_errors_of};
use anthill_core::eval::{HostValue, Value};

const SPEC: &str = r#"
namespace test.xg
  import anthill.prelude.Option.{none, some}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.{Option, Int64, String, List}
  sort Lift[C, F[T]]
    operation lift(c: C, x: F[T = Int64]) -> Int64
  end
  -- The payload, so a row reads which value the member was handed.
  sort Car
    entity car(n: Int64)
    provides Lift[C = Self, F = Option]
    operation lift(c: Self, x: Option[T = Int64]) -> Int64 =
      match x
        case some(v) -> v
        case none() -> 0
  end
  -- The head plus 100, so a row reads that `Crate`'s member ran and not `Car`'s.
  sort Crate
    entity crate(n: Int64)
    provides Lift[C = Self, F = List]
    operation lift(c: Self, x: List[T = Int64]) -> Int64 =
      match x
        case cons(h, _) -> h + 100
        case nil() -> 100
  end
"#;

/// The fixture with `go() -> Int64 = body`.
fn program(body: &str) -> String {
    format!("{SPEC}  operation go() -> Int64 = {body}\nend\n")
}

/// `go`'s answer, where the program loads.
fn answer(body: &str) -> i64 {
    let src = program(body);
    let errs = load_errors_of(&src);
    assert!(errs.is_empty(), "`{body}` loads; refused: {errs:?}");
    let mut interp = interp_for(&src);
    match interp.call("test.xg.go", &HostValue::all(&[])).map(|h| h.value) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{body}` runs to an Int64, got {other:?}"),
    }
}

/// The one refusal of the program, which must name the argument `x` and the two types.
fn refused_at_x(body: &str, expected: &str, got: &str) {
    let errs = load_errors_of(&program(body));
    assert_eq!(errs.len(), 1, "`{body}` is refused once; got {errs:?}");
    let want = format!("type mismatch in lift.x (op-arg): expected {expected}, got {got}");
    assert!(errs[0].ends_with(&want), "`{body}` is refused naming the argument\n  want: …{want}\n  got:  {}", errs[0]);
}

/// THE CAPABILITY: a call of the spec's member at a carrier whose provision binds the
/// higher-kinded slot to a bare constructor dispatches to that carrier's member and runs it.
///
/// FAILS WHEN BACKED OUT [D] (the dispatch reads `F`'s fill as the carrier: "no impl matches").
/// Passes under [B], [V] and [K] by design: a well-typed argument needs no check to run.
#[test]
fn a_dispatch_at_a_higher_kinded_binding_runs_the_carriers_member() {
    assert_eq!(answer("Lift.lift(car(n: 1), some(7))"), 7, "`Car`'s member, handed `some(7)`");
    assert_eq!(answer("Lift.lift(car(n: 1), none())"), 0, "`Car`'s member, handed `none()`");
    assert_eq!(answer("Lift.lift(crate(n: 1), [7])"), 107, "`Crate`'s member, handed `[7]`");
    assert_eq!(answer("Lift.lift(crate(n: 1), nil())"), 100, "`Crate`'s member, handed `nil()`");
}

/// An argument at `F[T = Int64]` is held to the constructor's application, `Option[T =
/// Int64]` at `Car` and `List[T = Int64]` at `Crate`, and refused naming the argument where it
/// is not one: a payload of another type, another constructor, a bare `Int64` where no
/// coercion makes it a `List`.
///
/// FAILS WHEN BACKED OUT [V] and [K] (`some("s")` loads: it is checked against nothing), and
/// [B] (`[7]` at `Car` binds `F := List` itself and is refused at the dispatch, "no provision
/// of `Lift` binds `C = Car, F = List`", not at the argument). Passes under [D] by design: the
/// argument is checked before the dispatch, which only then refuses.
#[test]
fn an_argument_is_held_to_the_constructor_the_binding_names() {
    refused_at_x("Lift.lift(car(n: 1), some(\"s\"))", "Option[T = Int64]", "Option[T = String]");
    refused_at_x("Lift.lift(car(n: 1), [7])", "Option[T = Int64]", "List[T = Int64]");
    refused_at_x("Lift.lift(crate(n: 1), 5)", "List[T = Int64]", "Int64");
    refused_at_x("Lift.lift(crate(n: 1), [\"s\"])", "List[T = Int64]", "List[T = String]");
    refused_at_x("Lift.lift(crate(n: 1), some(7))", "List[T = Int64]", "Option[T = Int64]");
}

/// A bare `Int64` at `F = Option` is `some(5)`: the slot is `Option[T = Int64]` there, and the
/// some-coercion wraps it, as it does at the member's own call (the control: `Car.lift`,
/// which nothing here changes, answers the same).
///
/// FAILS WHEN BACKED OUT [D] (refused, "no impl matches"), and [B], [V] and [K] AT THE RUN:
/// unchecked, the bare `5` is not wrapped, reaches `Car`'s member as an `Int64`, and its
/// `match` fails — the call loads and is unsound, the hole the old refusal of every call hid.
#[test]
fn a_bare_value_at_an_option_binding_is_wrapped_as_at_the_member() {
    assert_eq!(answer("Car.lift(car(n: 1), 5)"), 5, "the control: the member's own call wraps it");
    assert_eq!(answer("Lift.lift(car(n: 1), 5)"), 5, "the spec's call wraps it too");
}

/// A CALLBACK PAYLOAD: at `x: F[T = (Int64) -> Int64]` with `F = Option` the argument is held
/// to `Option[T = (Int64) -> Int64]` too. A pair holding a callable is judged on its shallow
/// form, whose head the filled constructor is, so a `List` of the lambda is refused at the
/// head and an `Option` of it runs `Car2`'s member.
///
/// FAILS WHEN BACKED OUT [C] (the head left `F` where the pair holds a callable: the `List`
/// loads, and `Car2`'s `match` would meet a list), [B], [V] and [K] (the same `List` loads,
/// the head never filled) and [D] (both refused, "no impl matches").
#[test]
fn a_callback_payload_is_held_to_the_constructor_too() {
    let src = |arg: &str| {
        format!(
            r#"
namespace test.xgc
  import anthill.prelude.Option.{{none, some}}
  import anthill.prelude.{{Option, Int64, List}}
  sort Lift2[C, F[T]]
    operation lift(c: C, x: F[T = (Int64) -> Int64]) -> Int64
  end
  sort Car2
    entity car2(n: Int64)
    provides Lift2[C = Self, F = Option]
    operation lift(c: Self, x: Option[T = (Int64) -> Int64]) -> Int64 =
      match x
        case some(f) -> f(3)
        case none() -> 0
  end
  operation go() -> Int64 = Lift2.lift(car2(n: 1), {arg})
end
"#
        )
    };
    let ok = src("some(lambda (y: Int64) -> y + 1)");
    assert!(load_errors_of(&ok).is_empty(), "an `Option` of the lambda loads: {:?}", load_errors_of(&ok));
    let mut interp = interp_for(&ok);
    match interp.call("test.xgc.go", &HostValue::all(&[])).map(|h| h.value) {
        Ok(Value::Int(4)) => {}
        other => panic!("`Car2`'s member applies the lambda to 3, got {other:?}"),
    }
    let errs = load_errors_of(&src("[lambda (y: Int64) -> y + 1]"));
    assert!(
        errs.len() == 1
            && errs[0].ends_with("lift.x (op-arg): expected Option[T = Int64 -> Int64], got List[T = Int64 -> Int64]"),
        "a `List` of the lambda is refused naming the argument; got {errs:?}"
    );
}

/// A PROVISION BINDING THE SLOT TO NO CONSTRUCTOR OF ITS KIND (`F = Int64`, a sort declaring no
/// parameter, where `F[T]` takes one) is not applied: the call keeps the dispatch's refusal it
/// had before this ticket, and no argument is checked against the malformed `Int64[T = Int64]`.
/// That such a provision LOADS is older than this ticket, and is not decided here: §5.2 asks
/// the kind of a higher-kinded parameter's default ("a sort declaring as many parameters"), and
/// says nothing of a provision's binding.
///
/// FAILS WHEN BACKED OUT [A] (the arm binding any bare sort: refused "expected Int64[T =
/// Int64], got Option[T = Int64]").
#[test]
fn a_binding_of_another_kind_is_not_applied() {
    let src = r#"
namespace test.xga
  import anthill.prelude.Option.{none, some}
  import anthill.prelude.{Option, Int64}
  sort Lift[C, F[T]]
    operation lift(c: C, x: F[T = Int64]) -> Int64
  end
  sort Num
    entity num(n: Int64)
    provides Lift[C = Self, F = Int64]
    operation lift(c: Self, x: Int64) -> Int64 = 1
  end
  operation go() -> Int64 = Lift.lift(num(n: 1), some(1))
end
"#;
    let errs = load_errors_of(src);
    assert!(
        errs.len() == 1 && errs[0].ends_with("Lift.lift.dispatch: expected matching impl for per-call bindings, got no impl matches"),
        "the call is refused at the dispatch, as before; got {errs:?}"
    );
}

// BACK-OUTS, measured on a selected run of this file and of `wi_dk83q_identical_substitution_test`
// (2026-11-23), each alone and restored after:
//
// * [D] `apply.rs`'s routing: a provision at `F`'s fill by ANOTHER provider sent to the
//   resolution only when it is a witness's (CXR5B's `witness_at_c`), so `Car`'s own provision
//   stays with the higher-kinded branch: 4 fail — the dispatch row, the bare-value row, the
//   callback row and `wi_dk83q`'s `a_higher_kinded_binding_is_no_open_slot`, each "no impl
//   matches".
// * [B] `carrier.rs`'s arm binding a higher-kinded slot's bare constructor taken out (`F` left
//   to the late pass): 3 fail — the argument row (at `[7]`), the bare-value row (at the run)
//   and the callback row.
// * [V] `args.rs`'s `fill_higher_kinded_heads` taken out of the argument check: 4 fail — the
//   argument row, the bare-value row, the callback row and
//   `a_higher_kinded_binding_is_no_open_slot`.
// * [K] DK83Q's own: `slot_is_higher_kinded` not asked at the carrier binding, so `F` binds the
//   instance `Option[T = ?]`, whose head no fill reads: the same 4 as [V].
// * [C] the head filled only where the pair holds no callable: 1 fails — the callback row.
// * [A] the arm binding any bare concrete sort at a higher-kinded slot, of any kind: 1 fails —
//   the kind row.
