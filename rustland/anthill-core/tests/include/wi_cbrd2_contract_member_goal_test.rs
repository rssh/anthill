//! A CONTRACT'S GOAL OF A SPEC'S MEMBER IS TYPED IN THE SIGNATURE (WI-20261105-CBRD2), as its
//! comparisons are: `requires Pred.ok(x)` and `effects { Boom :- Pred.ok(x) }` over `x: Leaf`,
//! `Pred` a spec whose `ok` has no body, are the call of `Leaf.ok`, and a proof of either at a
//! call — the precondition proved, the guard refuted — reads that member. Before, the proof's
//! goal reached the resolver's `Bool` view of `Pred.ok` with no pin, and the bridge found the
//! provider from the argument's value. The typed goal is kept beside the clause, as a typed
//! comparison is (`type_contract_comparisons`), and a proof carries its member onto the goal it
//! builds (`typing::clause_goal`, `carry_comparison_members`). One that does not type — `Pred` at
//! a type nothing provides it at — is refused at load.
//!
//! The verdicts are the ones the values gave, so the rows measure the reading
//! (`resolve::unpinned_spec_goals_by_this_thread`) beside them.
//!
//! ## What fails with the change backed out
//!
//! Measured with a temporary switch (no goal of a spec's member typed), then removed. The
//! control is the switch unset: every row passes.
//!
//! * [`a_precondition_naming_a_member_is_proved_at_it`] and
//!   [`a_guard_naming_a_member_is_refuted_at_it`] fail on the count, their verdicts unchanged.
//! * [`a_member_goal_at_a_type_nothing_provides_is_refused`] fails: the program loads clean.
//! * A member of another type than `Bool` left out (`Desc.describe(x, 3)`, its result-column
//!   form): [`a_precondition_naming_a_member_is_proved_at_it`] fails at it, on the count.
//!
//! [`a_generic_callees_member_goal_is_still_read_at_the_call`] passes either way by design: a
//! goal at the callee's type parameter has its member at the call's type, which no load types.

use anthill_core::kb::resolve::unpinned_spec_goals_by_this_thread;

use crate::common::{load_errors_of, load_stdlib_kb};

fn src(ns: &str, decls: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Effect}}
  sort Pred
    sort T = ?
    operation ok(x: T) -> Bool
  end
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Leaf
    entity leaf(v: Int64)
    provides Pred[T = Leaf]
    provides Desc[T = Leaf]
    operation ok(x: Leaf) -> Bool = match x case leaf(v) -> v > 2
    operation describe(x: Leaf) -> Int64 = match x case leaf(v) -> v
  end
  sort Boom
    entity Bang
    provides Effect[T = Boom]
  end
{decls}
end
"#
    )
}

/// The load's errors and the goals it read with no member, the shared base loaded first.
fn errors_and_unpinned(src: &str) -> (Vec<String>, usize) {
    drop(load_stdlib_kb());
    let before = unpinned_spec_goals_by_this_thread();
    let errs = load_errors_of(src);
    (errs, unpinned_spec_goals_by_this_thread() - before)
}

/// `f(leaf(v: 3))` proves `requires Pred.ok(x)`, its twin and `not(Pred.ok(x))`'s refusal the
/// other way; `f(leaf(v: 1))` is refused, an unsatisfied precondition; so for a member of
/// another type written with its result column, `Desc.describe(x, 3)`; a rule body's call is
/// held to it too.
#[test]
fn a_precondition_naming_a_member_is_proved_at_it() {
    for (n, (clause, arg, refused)) in [
        ("Pred.ok(x)", "leaf(v: 3)", false),
        ("Pred.ok(x)", "leaf(v: 1)", true),
        ("Pred.ok(x, true)", "leaf(v: 3)", false),
        ("Pred.ok(x, true)", "leaf(v: 1)", true),
        ("not(Pred.ok(x))", "leaf(v: 1)", false),
        ("not(Pred.ok(x))", "leaf(v: 3)", true),
        ("Desc.describe(x, 3)", "leaf(v: 3)", false),
        ("Desc.describe(x, 3)", "leaf(v: 4)", true),
    ]
    .into_iter()
    .enumerate()
    {
        let decls = format!(
            "  operation f(x: Leaf) -> Int64 requires {clause} = 1\n  operation g() -> Int64 = f({arg})"
        );
        let (errs, unpinned) = errors_and_unpinned(&src(&format!("test.cbrd2.cm.p{n}"), &decls));
        assert_eq!(unpinned, 0, "`requires {clause}` at f({arg}) read a goal with no member");
        assert_eq!(
            errs.iter().any(|e| e.contains("f.requires") && e.contains("precondition")),
            refused,
            "`requires {clause}` at f({arg}): {errs:?}"
        );
    }
    let decls = "  operation f(x: Leaf) -> Int64 requires Pred.ok(x) = 1\n  \
                 fact src(leaf(v: 3))\n  rule r(?t) :- src(?y), ?t <=> f(?y)";
    let (errs, unpinned) = errors_and_unpinned(&src("test.cbrd2.cm.rule", decls));
    assert_eq!(unpinned, 0, "the rule body's call read a goal with no member");
    assert!(errs.is_empty(), "{errs:?}");
}

/// `risky(leaf(v: 1))` under `effects { Boom :- Pred.ok(x) }` owes nothing, the guard refuted
/// at `Leaf.ok`; `risky(leaf(v: 3))` owes `Boom`.
#[test]
fn a_guard_naming_a_member_is_refuted_at_it() {
    for (n, (arg, owes)) in [("leaf(v: 1)", false), ("leaf(v: 3)", true)].into_iter().enumerate() {
        let decls = format!(
            "  operation risky(x: Leaf) -> Int64 effects {{ Boom :- Pred.ok(x) }} = 0\n  \
             operation caller() -> Int64 = risky({arg})"
        );
        let (errs, unpinned) = errors_and_unpinned(&src(&format!("test.cbrd2.cm.g{n}"), &decls));
        assert_eq!(unpinned, 0, "the guard at risky({arg}) read a goal with no member");
        assert_eq!(errs.iter().any(|e| e.contains("undeclared effect: Boom")), owes, "risky({arg}): {errs:?}");
    }
}

/// `requires Pred.ok(x)` over `x: Twig`, which provides no `Pred`, is refused at load, as the
/// call in a body would be.
#[test]
fn a_member_goal_at_a_type_nothing_provides_is_refused() {
    let decls = "  sort Twig\n    entity twig(w: Int64)\n  end\n  \
                 operation f(x: Twig) -> Int64 requires Pred.ok(x) = 1";
    let errs = load_errors_of(&src("test.cbrd2.cm.none", decls));
    assert!(
        errs.iter().any(|e| e.contains("f.requires") && e.contains("to call a member") && e.contains("provides no")),
        "{errs:?}"
    );
}

/// The control: `requires Pred.ok(x)` over `x: A` under `requires Pred[T = A]` has its member at
/// the call's type, which no load types; the call reads it from the value, as before.
#[test]
fn a_generic_callees_member_goal_is_still_read_at_the_call() {
    let decls = "  operation f[A](x: A) -> Int64 requires Pred[T = A] requires Pred.ok(x) = 1\n  \
                 operation g() -> Int64 = f(leaf(v: 3))";
    let (errs, unpinned) = errors_and_unpinned(&src("test.cbrd2.cm.gen", decls));
    assert!(errs.is_empty(), "{errs:?}");
    assert!(unpinned > 0, "the generic callee's goal is read with no member");
}
