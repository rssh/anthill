//! WI-20261121-QAA6S — A WITNESS THAT NAMES A COMPOSITE TAKES THE WHOLE OF ITS EQUALITY, IN THE
//! LOAD THAT DEFINES IT; WHERE THE WITNESS'S CONDITION DOES NOT HOLD, THE COMPOSITE HAS NONE
//! (decided with the user 2026-11-21: reading (b) of the ticket, the row was wrong).
//!
//! kernel-language.md, *Closed by the load that defines the carrier*: the load derives a
//! composite's equality "where no `eq` is supplied … and nothing at all for a sort a provision
//! already speaks for" (`eq_derive::derive_conditional_eq`: a sort whose `eq` a witness supplies is
//! a `boundary`, one a provision names is `spoken_for`). Speaking for a sort is
//! per SORT, not per instance: a witness that provides `PartialEq[T = Box[T = A]]` under
//! `requires Eq[T = A]` leaves `Box[Float]` with no equality at all — `Float` is `PartialEq` and
//! not `Eq` — where `Box`'s own derivation, `PartialEq[Box] :- PartialEq[T]`, would have covered
//! it.
//!
//! WHERE IT WAS FOUND: `wi_rah0z_one_recipe_test::the_outcome_entries_follow_the_switch` loaded
//! such a witness for the stdlib's `List` and asserted that, one-shot (in the library's own load),
//! it loads clean. It did not: the library compares a `List[Term]` (`EffectExpression.guarded`'s
//! `guard`, through the `eq` generated for its written `provides PartialEq`), `Term` is not `Eq`
//! (NaN), and the witness had switched `List`'s derivation off. MEASURED with a probe on
//! c3371cd0: on the shared base `List` derives `PartialEq` and `Eq` (one condition each);
//! one-shot it derives neither. The fixture now writes the witness in the derived shape, a
//! condition per provision, and loads clean one-shot.
//!
//! BACK-OUT, MEASURED 2026-11-21: with `derive_conditional_eq` deriving past both guards
//! (`boundary` and `spoken_for` — `spoken_for` alone changes nothing here, the witness supplies an
//! `eq` and so makes `Box` a boundary), [`a_narrow_witness_leaves_the_rest_without_equality`]
//! FAILS: `Box`'s derived rows land beside the witness's and the program is refused ("`Box`
//! provides `NonEq`, which requires `PartialEq`, and its provider `NarrowEq` was chosen, but
//! `Eq[T = Box.T]` beneath it does not hold"). The other two rows pass either way, by design:
//! they read what the witness and the derivation each answer where only one of them applies.
//!
//! NOT COVERED HERE: a witness with no `eq` of its own, where `spoken_for` is the only guard — an
//! `Eq`-only witness is not read as speaking for its carrier today (WI-20261121-TV0PA).

use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64};

/// `Box[T]` and, by `witness`, a witness that supplies its equality — `eq = true`, so an answer
/// of 1 for two DISTINCT boxes is the witness's and 0 the derivation's (structural). `floats`
/// compares two boxes of `Float`.
fn program(ns: &str, witness: &str, with_floats: bool) -> String {
    let floats = if with_floats {
        "operation floats() -> Int64 = b(eq(box(v: 1.5), box(v: 2.5)))"
    } else {
        ""
    };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Eq, PartialEq, Int64, Float, Bool}}
  import anthill.prelude.PartialEq.{{eq}}
  sort Box
    sort T = ?
    entity box(v: T)
  end
  {witness}
  operation b(t: Bool) -> Int64 = if t then 1 else 0
  operation ints() -> Int64 = b(eq(box(v: 1), box(v: 2)))
  {floats}
end
"#
    )
}

/// One `requires` for both provisions: `Box[A]` is `PartialEq` here only where `A` is `Eq`.
const NARROW: &str = r#"
  sort NarrowEq
    sort A = ?
    requires Eq[T = A]
    provides PartialEq[T = Box[T = A]]
    provides Eq[T = Box[T = A]]
    operation eq(x: Box[T = A], y: Box[T = A]) -> Bool = true
  end
"#;

/// The shape `Box` would derive: a condition per provision.
const DERIVED_SHAPE: &str = r#"
  sort WideEq
    sort A = ?
    provides PartialEq[T = Box[T = A]] :- PartialEq[T = A]
    provides Eq[T = Box[T = A]] :- Eq[T = A]
    operation eq(x: Box[T = A], y: Box[T = A]) -> Bool = true
  end
"#;

/// THE RULE: the narrow witness answers `Box[Int64]` (1: not the structural 0), and a comparison
/// of two `Box[Float]` is refused — nothing supplies their equality, the witness's `requires
/// Eq[Float]` does not hold and `Box` derived none. RED with the derivation not stepping aside,
/// at the first assertion: `Box`'s derived rows beside the witness's refuse the `ints` program.
#[test]
fn a_narrow_witness_leaves_the_rest_without_equality() {
    let ns = "wiqaa6s.narrow";
    assert_eq!(run_int64(&program(ns, NARROW, false), &format!("{ns}.ints")), Ok(1));
    let errs = load_errors(&program(ns, NARROW, true));
    assert_refused_naming(
        &errs,
        &["no impl matches", "anthill.prelude.Eq[T = anthill.prelude.Float]"],
        "a `Box[Float]` comparison beside a witness that requires `Eq` of the element",
    );
}

/// THE REPAIR the `rah0z` fixture takes: written in the derived shape, the witness covers
/// `Box[Float]` too, and answers both comparisons.
#[test]
fn a_witness_in_the_derived_shape_covers_every_element_type() {
    let ns = "wiqaa6s.wide";
    let src = program(ns, DERIVED_SHAPE, true);
    assert_eq!(run_int64(&src, &format!("{ns}.ints")), Ok(1));
    assert_eq!(run_int64(&src, &format!("{ns}.floats")), Ok(1));
}

/// THE CONTROL: with no witness, `Box`'s derived equality compares both structurally — the two
/// boxes differ, 0 each.
#[test]
fn with_no_witness_the_derivation_answers() {
    let ns = "wiqaa6s.none";
    let src = program(ns, "", true);
    assert_eq!(run_int64(&src, &format!("{ns}.ints")), Ok(0));
    assert_eq!(run_int64(&src, &format!("{ns}.floats")), Ok(0));
}
