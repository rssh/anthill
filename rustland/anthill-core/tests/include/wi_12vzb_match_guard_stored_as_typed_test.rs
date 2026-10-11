//! A match arm's guard is stored as it was typed — found while delivering
//! WI-20261011-12VZB, on the row that runs its call at every site an operation body
//! writes one.
//!
//! THE RULE. Typing an operation body rewrites it: a call a `@[simp]` equation defines is
//! replaced by the equation's right-hand side, a dot on a value by the operation it
//! names. The body that runs is the rewritten one. A guard is typed with the arm's
//! binders in scope, and is part of that body.
//!
//! BEFORE. The guard was typed and the written one was put back. `case mk(v: n) |
//! dbl(n) > 3 -> 1` under `rule dbl(?n) <=> ?n + ?n @[simp]` loaded clean and died
//! `OperationBodyMissing`, where the same call in the arm's body or in an `if` condition
//! ran. `case mk(v: n) | b.isBig() -> 1` was a load error, "expected operation declared on
//! the receiver's sort, got no such member (dot dispatch)", about an operation the sort
//! declares: the dot left in the stored guard was read again by a later pass.
//!
//! EVERY ROW HAS ITS OWN SOURCE.
//!
//! CONTROLS — measured by putting the written guard back (`typing/build.rs`, the line
//! that stores the typed one) and running this file.
//!
//!   FAIL, each dying `OperationBodyMissing`:
//!     an_equation_fires_in_a_guard
//!     an_equation_over_a_constructor_fires_in_a_guard
//!     a_guard_that_fails_after_the_rewrite_takes_the_next_arm
//!     the_arm_still_assumes_the_guard_as_it_is_written
//!     a_guard_inside_a_guard_is_stored_as_typed_too
//!   FAIL, refused at load for a member the sort declares:
//!     a_dot_call_in_a_guard_loads_and_runs
//!
//!   THE ARM'S ASSUMPTION STAYS THE WRITTEN GUARD, as an `if` assumes its condition as
//!   written: a precondition is spelled as the author spells the guard, not as an
//!   equation leaves it. Measured by assuming the typed guard instead (`typing/build.rs`,
//!   the `assume` under the line that stores it):
//!     the_arm_still_assumes_the_guard_as_it_is_written — FAILS, refused at load for a
//!       precondition the guard states.
//!
//!   PASS either way, by design:
//!     a_guard_that_nothing_rewrites_runs_as_it_did
//!     the_arms_body_is_rewritten_as_it_was
//!
//!   NOT COVERED, measured with the change in place: `case mk(v: n) | b.open() > 3` under
//!   `rule open(mk(v: ?v)) <=> ?v @[simp]` loads and dies `OperationBodyMissing`, as
//!   `Box.open(b)` does at every other site — an equation with a constructor pattern does
//!   not see through a binding. It was the dot's load error before.

use crate::common::run_int64;

/// `test.<ns>` with a one-field `Box` — a bodied predicate and an operation defined by an
/// equation over its constructor — and `dbl`, defined by an equation; then `outside`.
fn guarded(ns: &str, outside: &str) -> String {
    format!(
        "namespace test.{ns}\n  import anthill.prelude.{{Int64, Bool}}\n  sort Box\n    entity mk(v: Int64)\n    operation isBig(b: Box) -> Bool = b.v > 3\n    operation open(b: Box) -> Int64\n    rule open(mk(v: ?v)) <=> ?v @[simp]\n  end\n  import test.{ns}.Box.{{mk}}\n  operation dbl(n: Int64) -> Int64\n  rule dbl(?n) <=> ?n + ?n @[simp]\n{outside}\nend\n"
    )
}

#[track_caller]
fn assert_runs(src: &str, entry: &str, expected: i64) {
    assert_eq!(run_int64(src, entry), Ok(expected), "{entry}");
}

#[test]
fn an_equation_fires_in_a_guard() {
    assert_runs(
        &guarded(
            "grdeq",
            "  operation at(b: Box) -> Int64 =\n    match b\n      case mk(v: n) | dbl(n) > 3 -> 1\n      case _ -> 0\n  operation go() -> Int64 = at(mk(5))",
        ),
        "test.grdeq.go",
        1,
    );
}

/// The equation's pattern is a constructor, written in the guard named and positionally.
#[test]
fn an_equation_over_a_constructor_fires_in_a_guard() {
    let src = guarded(
        "grdctor",
        "  operation named(b: Box) -> Int64 =\n    match b\n      case mk(v: n) | Box.open(Box.mk(v: n)) > 3 -> 1\n      case _ -> 0\n  operation positional(b: Box) -> Int64 =\n    match b\n      case mk(v: n) | Box.open(Box.mk(n)) > 3 -> 1\n      case _ -> 0\n  operation go() -> Int64 = named(mk(5)) * 10 + positional(mk(5))",
    );
    assert_runs(&src, "test.grdctor.go", 11);
}

/// The rewritten guard decides the arm: where it is false the next arm answers.
#[test]
fn a_guard_that_fails_after_the_rewrite_takes_the_next_arm() {
    assert_runs(
        &guarded(
            "grdfalse",
            "  operation at(b: Box) -> Int64 =\n    match b\n      case mk(v: n) | dbl(n) > 3 -> 1\n      case _ -> 0\n  operation go() -> Int64 = at(mk(1))",
        ),
        "test.grdfalse.go",
        0,
    );
}

/// A dot on a value is resolved where the guard is typed, to an operation the sort
/// declares; on both sides of the predicate.
#[test]
fn a_dot_call_in_a_guard_loads_and_runs() {
    let src = guarded(
        "grddot",
        "  operation at(b: Box) -> Int64 =\n    match b\n      case mk(v: n) | b.isBig() -> 1\n      case _ -> 0\n  operation go() -> Int64 = at(mk(5)) * 10 + at(mk(1))",
    );
    assert_runs(&src, "test.grddot.go", 10);
}

/// What the arm's body is checked under is the guard as it is written: `needd` requires
/// `dbl(n) > 3` in those words, and the guard that states them discharges it — while the
/// guard that runs is the equation's `n + n > 3`.
#[test]
fn the_arm_still_assumes_the_guard_as_it_is_written() {
    assert_runs(
        &guarded(
            "grdgamma",
            "  operation needd(n: Int64) -> Int64
    requires dbl(n) > 3
  = n
  operation at(b: Box) -> Int64 =
    match b
      case mk(v: n) | dbl(n) > 3 -> needd(n)
      case _ -> 0
  operation go() -> Int64 = at(mk(5))",
        ),
        "test.grdgamma.go",
        5,
    );
}

/// A `match` written in a guard has guards of its own.
#[test]
fn a_guard_inside_a_guard_is_stored_as_typed_too() {
    assert_runs(
        &guarded(
            "grdnest",
            "  operation at(b: Box) -> Int64 =
    match b
      case mk(v: n) | (match b
                         case mk(v: k) | dbl(k) > 3 -> true
                         case _ -> false) -> 1
      case _ -> 0
  operation go() -> Int64 = at(mk(5)) * 10 + at(mk(1))",
        ),
        "test.grdnest.go",
        10,
    );
}

/// A guard typing leaves alone: a comparison of a binder, and a call of a bodied
/// operation by its name.
#[test]
fn a_guard_that_nothing_rewrites_runs_as_it_did() {
    let src = guarded(
        "grdplain",
        "  operation cmp(b: Box) -> Int64 =\n    match b\n      case mk(v: n) | n > 3 -> 1\n      case _ -> 0\n  operation call(b: Box) -> Int64 =\n    match b\n      case mk(v: n) | Box.isBig(b) -> 1\n      case _ -> 0\n  operation go() -> Int64 = cmp(mk(5)) * 1000 + cmp(mk(1)) * 100 + call(mk(5)) * 10 + call(mk(1))",
    );
    assert_runs(&src, "test.grdplain.go", 1010);
}

/// The arm's body beside a guard was always stored as typed.
#[test]
fn the_arms_body_is_rewritten_as_it_was() {
    assert_runs(
        &guarded(
            "grdbody",
            "  operation at(b: Box) -> Int64 =\n    match b\n      case mk(v: n) | n > 3 -> dbl(n)\n      case _ -> 0\n  operation go() -> Int64 = at(mk(5))",
        ),
        "test.grdbody.go",
        10,
    );
}
