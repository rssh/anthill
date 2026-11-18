//! THE CASE SPLIT IS STRUCTURAL, AND STARTS WHERE STRUCTURE IS THE RELATION ASKED
//! (WI-20261105-CBRD2, decided with the user 2026-11-18). The resolver solves an equation whose
//! operand is a call that cannot run yet by splitting the call's body into one continuation per
//! arm (WI-580): each arm is `unify`, structural, and each call an arm makes is pulled out into
//! a comparison of its own. It starts from a `===` goal, and from a `=` the typer pinned to the
//! member of a scalar whose equality is identity (`Int64`, `BigInt`, `String`, `Bool`, `Type`,
//! `Symbol`; not `Float`, whose `eq` is IEEE's), so a `Bool` condition (`isOne(?c)`, read as
//! `eq(isOne(?c), true)`) enumerates.
//! A `=` at any other carrier is its member's and waits for its arguments. The pulled-out
//! comparisons are `===`: they compare a call's value with what the arms build of it.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, then removed. The control is each switch unset: every row
//! passes.
//!
//! * A `=` at any carrier starting the split, as before:
//!   [`an_equality_at_a_composite_waits`] (`?a = [1]`, definite) and
//!   [`an_equality_at_float_waits`] (`?c = red`, definite).
//! * The pulled-out comparisons spelled `eq`: [`a_structural_equation_is_solved_by_the_split`]
//!   is one conditional row, `cons(head: 1, tail: ?rest)`, and one equality compared with no
//!   member — the pulled-out `eq` at `List` starts no split of its own.
//! * A `=` at a scalar not starting it: [`an_equality_at_an_identity_scalar_still_splits`]
//!   (`tagged` one conditional row).
//! * `Float`'s `=` starting it: [`an_equality_at_float_waits`] (`?c = red`, definite).
//! * A three-place equation split: [`a_verdict_column_is_never_left_unbound`] (`?c = red, ?r =
//!   ?_`, definite, for `=` and `===` alike; at HEAD for `=`).

use anthill_core::kb::resolve::untyped_equalities_by_this_thread;

const SRC: &str = r#"
namespace test.cbrd2.su
  import anthill.prelude.{Int64, Bool, Float, List}
  import anthill.prelude.List.{append}
  import anthill.prelude.PartialEq.{eq}
  sort C
    entity red
    entity green
    operation tag(c: C) -> Int64 =
      match c
        case red() -> 1
        case green() -> 2
    operation isOne(c: C) -> Bool =
      match c
        case red() -> true
        case green() -> false
    operation fval(c: C) -> Float =
      match c
        case red() -> 2.5
        case green() -> 1.0
  end
  rule solveSt(?a) :- append(?a, [3]) === [1, 3]
  rule solveEq(?a) :- append(?a, [3]) = [1, 3]
  rule tagged(?c) :- C.tag(?c) = 1
  rule ones(?c) :- C.isOne(?c)
  rule floats(?c) :- C.fval(?c) = 2.5
  rule floatsG(1) :- C.fval(red()) = 2.5
  rule column(?c, ?r) :- eq(C.tag(?c), 1, ?r)
  rule columnSt(?c, ?r) :- anthill.kernel.struct_eq(C.tag(?c), 1, ?r)
end
"#;

/// The answers of `pattern` as `(shown binding, definite)`, and the equalities compared with
/// no member while they were found.
fn rows_counting(kb: &mut anthill_core::kb::KnowledgeBase, pattern: &str) -> (Vec<(String, bool)>, usize) {
    let before = untyped_equalities_by_this_thread();
    let rows = crate::common::shown_rows(kb, &format!("test.cbrd2.su.{pattern}"));
    (rows, untyped_equalities_by_this_thread() - before)
}

/// `append(?a, [3]) === [1, 3]` is solved by the split, `?a = [1]`, each comparison it pulls out
/// a `===`.
#[test]
fn a_structural_equation_is_solved_by_the_split() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        rows_counting(&mut kb, "solveSt"),
        (vec![("cons(head: 1, tail: nil)".to_string(), true)], 0)
    );
}

/// `append(?a, [3]) = [1, 3]` is `List`'s member's and starts no split: one conditional row.
#[test]
fn an_equality_at_a_composite_waits() {
    let mut kb = crate::common::load_kb_with(SRC);
    let (rows, _) = rows_counting(&mut kb, "solveEq");
    assert!(rows.len() == 1 && !rows[0].1, "one conditional row; got {rows:?}");
}

/// A `=` at `Int64` and a `Bool` condition are identity at their scalar, and split: each
/// answers `?c = red`, comparing nothing with no member.
#[test]
fn an_equality_at_an_identity_scalar_still_splits() {
    let mut kb = crate::common::load_kb_with(SRC);
    for rel in ["tagged", "ones"] {
        assert_eq!(rows_counting(&mut kb, rel), (vec![("red".to_string(), true)], 0), "`{rel}`");
    }
}

/// A `=` at `Float` is IEEE's, not identity, and starts no split: one conditional row, where the
/// ground twin decides.
#[test]
fn an_equality_at_float_waits() {
    let mut kb = crate::common::load_kb_with(SRC);
    let (rows, _) = rows_counting(&mut kb, "floats");
    assert!(rows.len() == 1 && !rows[0].1, "one conditional row; got {rows:?}");
    let (ground, _) = rows_counting(&mut kb, "floatsG");
    assert_eq!(ground.len(), 1, "the ground twin holds: {ground:?}");
    assert!(ground[0].1, "{ground:?}");
}

/// A three-place equation's third place is its verdict's column. A split takes the equation to
/// hold, so it would leave that column unbound: `eq(C.tag(?c), 1, ?r)` answered `?c = red, ?r =
/// ?_`, definite. It is not split, and waits for `?c`.
#[test]
fn a_verdict_column_is_never_left_unbound() {
    let mut kb = crate::common::load_kb_with(SRC);
    for rel in ["column", "columnSt"] {
        let goal = crate::common::query_pattern_term(&mut kb, &format!("test.cbrd2.su.{rel}(?c, ?r)"));
        let got = kb.resolve(&[goal], &Default::default());
        assert!(
            got.iter().all(|s| !s.is_definite()),
            "`{rel}`: no definite answer with the column unbound; got {} definite",
            got.iter().filter(|s| s.is_definite()).count()
        );
    }
}
