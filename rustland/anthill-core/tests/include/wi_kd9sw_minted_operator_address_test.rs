//! WI-20260825-KD9SW — A MINTED OPERATOR NAMES ITS TARGET OUTRIGHT.
//!
//! `+` used to desugar to the SHORT functor `add`, and `kb::load`'s `PRELUDE_QUALIFIED`
//! said where that lived. Two encodings of one fact, with nothing keeping them in step —
//! and the second sat BELOW scope resolution, so a same-spelled name in scope CAPTURED
//! the operator. Every operator now carries an ADDRESS
//! (`parse::pratt::SPEC_OP_FUNCTORS`), which is WI-20260825-5W3RJ's move one table over.
//!
//! ## This file REPLACES `wi_bfb9a_rival_spec_operation_test`
//!
//! That file's subject was `load::check_rival_spec_operations`, a whole-KB pass that
//! REFUSED a free-standing `operation eq(…)` because it would silence the tier for a
//! minted `=`. Its population was exactly the twelve. With the mint naming its target,
//! there is no tier entry left to silence and the capture is UNREPRESENTABLE — so the
//! pass is deleted and its thirteen refusal rows have nothing to assert. What was worth
//! keeping is inverted here: the programs it refused now LOAD, and the operator keeps
//! its meaning anyway. `an_imported_unrelated_add_is_a_capture_not_a_rival` is the row
//! that becomes [`an_import_can_no_longer_retarget_an_operator`], and it is the one that
//! records the LANGUAGE change (kernel-language.md §5.5).
//!
//! ## WHAT FAILS WHEN THIS IS BACKED OUT
//!
//! Put the short functors back in `parse::pratt`'s tables (`functor: "add"`, …) and
//! restore the twelve `PRELUDE_QUALIFIED` entries:
//!   * `an_import_can_no_longer_retarget_an_operator` fails — `1 + 2` answers `99`
//!     again, which IS the defect.
//!   * `an_operator_needs_no_import` fails: every row loses its operation.
//!   * `a_free_standing_spec_op_name_is_legal_again` fails — the deleted pass refused it.
//!   * `a_carrier_still_dispatches_through_the_address` and
//!     `a_written_bare_name_still_resolves_by_scope` pass EITHER WAY by design. The first
//!     is the row that says absolute minting cost no polymorphism; the second is the one
//!     that says the migration this ticket imposed is about WRITTEN names only.

use crate::common::{interp_for, try_load_kb_with};

fn errs_of(src: &str) -> Vec<String> {
    try_load_kb_with(src).map(|_| Vec::new()).unwrap_or_else(|e| e)
}

fn drive(src: &str, qn: &str) -> String {
    let mut interp = interp_for(src);
    let got = interp
        .call(qn, &[])
        .unwrap_or_else(|e| panic!("{qn} must evaluate: {e:?}"));
    format!("{got:?}")
}

/// THE HEADLINE, and the row the whole ticket turns on.
///
/// With `import lib.Weird.{add}` in scope, `add(1, 2)` means the IMPORT (99) and
/// `1 + 2` means the OPERATOR (3). Before this ticket both answered 99 — measured, not
/// inferred: the tier sat below scope, so the import answered the minted functor too.
///
/// THE TWO SPELLINGS NOW DISAGREE, and that is a language change rather than a repair.
/// §5.5 used to say `a + b` desugars to `add(a, b)`; it now says an operator names its
/// operation ABSOLUTELY, and that refactoring one spelling into the other is not always
/// meaning-preserving. This row is that sentence, driven.
#[test]
fn an_import_can_no_longer_retarget_an_operator() {
    let src = r#"
namespace kd9sw.lib
  import anthill.prelude.{Int64}
  sort Weird
    entity w
    operation add(a: Int64, b: Int64) -> Int64 = 99
  end
end
namespace kd9sw.use
  import anthill.prelude.{Int64}
  import kd9sw.lib.Weird.{add}
  import anthill.prelude.Option.{some}
  operation viaOperator() -> Int64 = 1 + 2
  operation viaBareCall() -> Int64 = add(1, 2)
end
"#;
    assert!(errs_of(src).is_empty(), "the fixture must load: {:?}", errs_of(src));
    assert_eq!(
        drive(src, "kd9sw.use.viaOperator"),
        "Int(3)",
        "`1 + 2` names `..anthill.prelude.Additive.add` outright; an import of some other \
         `add` cannot reach it. Before this ticket it answered Int(99)"
    );
    assert_eq!(
        drive(src, "kd9sw.use.viaBareCall"),
        "Int(99)",
        "…while the WRITTEN name is an ordinary name and still resolves by scope — which \
         is exactly why the two spellings are no longer interchangeable"
    );
}

/// AN OPERATOR NEEDS NO IMPORT, which is the property the migration must not have cost.
///
/// All twelve, in one namespace, with no spec imported anywhere — every one computes.
#[test]
fn an_operator_needs_no_import() {
    let src = r#"
namespace kd9sw.bare
  import anthill.prelude.{Int64, Bool, Float}
  operation plus()  -> Int64 = 1 + 2
  operation minus() -> Int64 = 5 - 2
  operation times() -> Int64 = 3 * 4
  operation negate()-> Int64 = 0 - 7
  operation quot()  -> Float = 10.0 / 4.0
  operation rem()   -> Int64 = 7 % 2
  operation same()  -> Bool  = 1 = 1
  operation diff()  -> Bool  = 1 != 2
  operation less()  -> Bool  = 1 < 2
  operation le()    -> Bool  = 1 <= 2
  operation more()  -> Bool  = 2 > 1
  operation ge()    -> Bool  = 2 >= 1
end
"#;
    assert!(
        !src.contains("Additive")
            && !src.contains("PartialOrd")
            && !src.contains("PartialEq")
            && !src.contains("Divisible")
            && !src.contains("Multiplicative")
            && !src.contains("EuclideanDomain"),
        "the fixture must import NO spec — that absence is what this row measures"
    );
    assert!(errs_of(src).is_empty(), "must load: {:?}", errs_of(src));
    for (op, want) in [
        ("plus", "Int(3)"),
        ("minus", "Int(3)"),
        ("times", "Int(12)"),
        ("negate", "Int(-7)"),
        ("quot", "Float(2.5)"),
        ("rem", "Int(1)"),
        ("same", "Bool(true)"),
        ("diff", "Bool(true)"),
        ("less", "Bool(true)"),
        ("le", "Bool(true)"),
        ("more", "Bool(true)"),
        ("ge", "Bool(true)"),
    ] {
        assert_eq!(
            drive(src, &format!("kd9sw.bare.{op}")),
            want,
            "`{op}` must compute with no import in scope"
        );
    }
}

/// THE ADDRESS IS THE SPEC OP, NOT A CARRIER — so absolute minting costs no
/// polymorphism. CONTROL: passes either way, and is what says the fix did not trade
/// dispatch for uncapturability.
#[test]
fn a_carrier_still_dispatches_through_the_address() {
    let src = r#"
namespace kd9sw.cash
  import anthill.prelude.{Int64, Additive}
  sort Money
    entity money(v: Int64)
    provides Additive[T = Money]
    operation add(a: Money, b: Money) -> Money = money(v: a.v + b.v)
    operation sub(a: Money, b: Money) -> Money = money(v: a.v - b.v)
    operation neg(a: Money) -> Money = money(v: 0 - a.v)
    operation zero() -> Money = money(v: 0)
  end
  operation total() -> Int64 = (money(v: 700) + money(v: 25)).v
end
"#;
    assert!(errs_of(src).is_empty(), "must load: {:?}", errs_of(src));
    assert_eq!(
        drive(src, "kd9sw.cash.total"),
        "Int(725)",
        "`+` names the SPEC op, and the spec op is what dispatches — so a carrier \
         providing `Additive[T = Money]` answers through its own `add`"
    );
}

/// THE PROGRAM THE DELETED PASS REFUSED, now legal — and the row that separates
/// "the capture is REFUSED" from "the capture is IMPOSSIBLE".
///
/// `check_rival_spec_operations` refused a free-standing `operation mod(a, b) = 99`
/// because it would silence the tier for a minted `%`. It loads now, the two are simply
/// different operations, and `7 % 2` still answers 1.
#[test]
fn a_free_standing_spec_op_name_is_legal_again() {
    let src = r#"
namespace kd9sw.free
  import anthill.prelude.{Int64}
  operation mod(a: Int64, b: Int64) -> Int64 = 99
  operation viaOperator() -> Int64 = 7 % 2
  operation viaBareCall() -> Int64 = mod(7, 2)
end
"#;
    let errs = errs_of(src);
    assert!(
        errs.is_empty(),
        "a free-standing `mod` is no longer a rival of anything — there is no tier entry \
         left for it to silence: {errs:?}"
    );
    assert_eq!(
        drive(src, "kd9sw.free.viaOperator"),
        "Int(1)",
        "`7 % 2` is `..anthill.prelude.EuclideanDomain.mod` and answers 1"
    );
    assert_eq!(
        drive(src, "kd9sw.free.viaBareCall"),
        "Int(99)",
        "…and the local declaration answers its own callers"
    );
}

/// A WRITTEN BARE NAME STILL RESOLVES BY SCOPE, and needs to be brought into it.
///
/// This is the whole of the migration this ticket imposed: the implicit tier used to
/// answer a written `gt(a, b)` too, and with it gone such a call names the operation by
/// import. CONTROL: the refusal half passes either way (a name in no scope was always an
/// error); the ACCEPT half is what says the repair is an ordinary import and not
/// something new.
#[test]
fn a_written_bare_name_still_resolves_by_scope() {
    let without = r#"
namespace kd9sw.written1
  import anthill.prelude.{Int64, Bool}
  operation cmp(a: Int64, b: Int64) -> Bool = gt(a, b)
end
"#;
    assert!(
        errs_of(without)
            .iter()
            .any(|e| e.contains("gt") && e.contains("not in scope as a bare name")),
        "a written `gt` with nothing bringing it into scope must be refused, and the \
         message must name the repair: {:?}",
        errs_of(without)
    );
    let with = r#"
namespace kd9sw.written2
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.PartialOrd.{gt}
  operation cmp(a: Int64, b: Int64) -> Bool = gt(a, b)
  operation yes() -> Bool = cmp(2, 1)
end
"#;
    assert!(errs_of(with).is_empty(), "must load: {:?}", errs_of(with));
    assert_eq!(
        drive(with, "kd9sw.written2.yes"),
        "Bool(true)",
        "the import is the ordinary repair, and the operation runs"
    );
}
