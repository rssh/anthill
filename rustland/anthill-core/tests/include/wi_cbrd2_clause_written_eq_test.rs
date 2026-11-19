//! WI-20261105-CBRD2 — a typed equality at a carrier whose `eq` is written as clauses is that
//! member's: pinned to it, and run by proving its clauses. The one operation the interpreter runs
//! that way (eval's `eq_bridge_target`, WI-625) was not pinned (a pin asked for a body or a host
//! implementation, `op_is_interpretable`), so `red = blue` over `provides PartialEq[T = Color, eq = ceq]`
//! stayed the spec operation and was compared by its operands' values — the same verdict, by
//! another route. A member nothing defines is pinned too, so the call fails where it is
//! dispatched, as it does through a dictionary, rather than inside a comparison by value.
//!
//! Each row counts the equalities compared with no member the typer chose
//! (`untyped_equalities_by_this_thread`) around the run, after the load.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, then removed. The control is each switch unset: every
//! row passes.
//!
//! * An `eq` member with no body or host implementation left the spec operation, as before
//!   (`pins_an_equality_member` false): every row fails on the untyped count.
//! * The bridge confirming the pinned member off the operands' values (`eq_bridge_target`
//!   reading `sem_eq_dispatch_target`, as before) failed
//!   [`a_clause_written_member_is_pinned_and_proved`] on the index count, measured in part 5p;
//!   the reader and its count are gone since part 5r.

use anthill_core::eval::{EvalError, HostValue, Value};
use anthill_core::kb::resolve::untyped_equalities_by_this_thread;

/// Run `entry` (no arguments) over `src`; its result, and the untyped equalities the run made.
fn run(src: &str, entry: &str) -> (Result<Value, EvalError>, usize) {
    let mut interp = crate::common::interp_for(src);
    let untyped = untyped_equalities_by_this_thread();
    let got = interp.call(entry, &HostValue::all(&[])).map(|h| h.value);
    (got, untyped_equalities_by_this_thread() - untyped)
}

const COLOR: &str = "namespace cbrd2.cw.color
  import anthill.prelude.{Int64, Bool, PartialEq, Eq}
  sort Color
    entity red
    entity blue
    operation ceq(a: Color, b: Color) -> Bool
    rule ceq(red, red) :- true
    rule ceq(blue, blue) :- true
    provides PartialEq[T = Color, eq = ceq]
    provides Eq[T = Color]
  end
  import cbrd2.cw.color.Color.{red, blue}
  operation same() -> Int64 = if red = red then 1 else 0
  operation other() -> Int64 = if red = blue then 1 else 0
end
";

/// `red = red` and `red = blue` over a `ceq` written as clauses: 1 and 0, each proved through
/// `ceq`'s clauses, with no comparison by value.
#[test]
fn a_clause_written_member_is_pinned_and_proved() {
    for (entry, want) in [("cbrd2.cw.color.same", 1), ("cbrd2.cw.color.other", 0)] {
        let (got, untyped) = run(COLOR, entry);
        assert!(matches!(got, Ok(Value::Int(v)) if v == want), "{entry}: {got:?}");
        assert_eq!(untyped, 0, "{entry}: an equality compared with no member");
    }
}

/// `TotalFloat`'s `eq` is written as a clause (`rule eq(?a, ?b) :- ?a === ?b`): two NaNs are
/// equal through it, the comparison its member's.
#[test]
fn a_total_float_equality_is_its_member() {
    let src = "namespace cbrd2.cw.tf
  import anthill.prelude.{Bool, Float, TotalFloat}
  import anthill.prelude.PartialEq.{eq}
  operation nan() -> Float = 0.0 / 0.0
  operation tf() -> Bool = eq(TotalFloat(raw: nan()), TotalFloat(raw: nan()))
end
";
    let (got, untyped) = run(src, "cbrd2.cw.tf.tf");
    assert!(matches!(got, Ok(Value::Bool(true))), "{got:?}");
    assert_eq!(untyped, 0, "an equality compared with no member");
}

/// A witness's `eq` that nothing defines (an equation is not a clause): the direct call
/// `PartialEq.eq(red(), blue())` raises `OperationBodyMissing` naming the member where it is
/// dispatched, and compares nothing by value on the way.
#[test]
fn an_equality_member_nothing_defines_fails_at_its_dispatch() {
    let src = "namespace cbrd2.cw.witness
  import anthill.prelude.{Bool, Int64, PartialEq}
  sort Color
    entity red
    entity blue
  end
  sort ColorEq
    provides PartialEq[T = Color]
    operation eq(a: Color, b: Color) -> Bool
    rule eq(red, red) <=> true
  end
  operation drive() -> Int64 = if PartialEq.eq(red(), blue()) then 1 else 0
end
";
    let (got, untyped) = run(src, "cbrd2.cw.witness.drive");
    assert!(
        matches!(&got, Err(EvalError::OperationBodyMissing { name, .. }) if name == "cbrd2.cw.witness.ColorEq.eq"),
        "{got:?}"
    );
    assert_eq!(untyped, 0, "an equality compared with no member");
}
