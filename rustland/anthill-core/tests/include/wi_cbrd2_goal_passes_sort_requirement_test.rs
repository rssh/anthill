//! A GOAL PASSES THE REQUIREMENT ITS CALLEE'S SORT STATES, at a concrete type (WI-20261105-CBRD2).
//! A call in a rule of a sort, at a column typed at the sort's parameter, reads the requirement
//! the sort states there (060.1 §8.2; in a spec's own rule, the spec, §3): `sort Pred { rule
//! good(?x: T) :- ok(?x) }`. An operation's citation passed it (`sort_requirement_route`); a rule
//! body's goal, and a query, routed the callee's guards and passed this read nothing, so it
//! found the provider from the value of `?x` when the call ran
//! (`resolve::value_reads_by_this_thread`): `viaGood(?y) :- src(?y), Pred.good(?y)` with `?y` a
//! `Leaf`.
//!
//! The goal now builds the requirement at the type it puts the call's receiver at, where that
//! type is concrete, as it builds a guard's there (`rule_goal_routes::dictionary_at_goal`), and
//! is refused at load where the provisions build none; at a type parameter of the caller it
//! passes the caller's own guard of the spec there, as for a slot read (`callers_own_guard`).
//!
//! ## What fails with the change backed out
//!
//! Measured with a temporary switch, then removed, and with HEAD's source. The control is the
//! switch unset: every row passes. [`a_goal_passes_its_callees_sort_requirement`] fails on the
//! reads, one per goal; every verdict stands. [`a_requirement_nothing_provides_at_the_goal_is_refused`]
//! fails with HEAD's source, the goal loading clean. [`a_goal_at_the_callers_parameter_passes_its_guard`]
//! fails with the caller's guard not passed: a read per goal, and `viaParam[A = Leaf, Pred =
//! Other]` answering `Leaf`'s own `true` where `Other`'s is false.
//! [`an_operations_citation_is_the_control`] passes either way.

use anthill_core::kb::resolve::value_reads_by_this_thread;

use crate::common::{interp_for, load_kb_with, load_stdlib_kb, pattern_answer_counts};

/// `f`'s result and the reads for a call it answered from a value, the shared base loaded first.
fn counting<R>(f: impl FnOnce() -> R) -> (R, usize) {
    drop(load_stdlib_kb());
    let before = value_reads_by_this_thread();
    let r = f();
    (r, value_reads_by_this_thread() - before)
}

const PRED: &str = r#"
namespace test.cbrd2.ownrule
  import anthill.prelude.{Bool, Int64, Error, EmptyStream}
  sort Pred
    sort T = ?
    operation ok(x: T) -> Bool
    rule good(?x: T) :- ok(?x)
    rule goodR(?x: T, ?r) :- ok(?x, ?r)
  end
  sort Leaf
    entity leaf(v: Int64)
    provides Pred[T = Leaf]
    operation ok(x: Leaf) -> Bool = match x
      case leaf(v) -> v > 2
  end
  fact src(leaf(v: 3))
  fact src1(leaf(v: 1))
  rule viaGood(?y) :- src(?y), Pred.good(?y)
  rule viaGood1(?y) :- src1(?y), Pred.good(?y)
  rule viaGoodR(?y, ?r) :- src(?y), Pred.goodR(?y, ?r)
  operation viaOp() -> Int64 effects {Error, Error[EmptyStream]} =
    if Pred.good(Leaf.leaf(v: 3)).isEmpty() then 0 else 1
end
"#;

/// Through a rule goal and asked as a query: each verdict `Leaf`'s `ok` gives, nothing read
/// from the values.
#[test]
fn a_goal_passes_its_callees_sort_requirement() {
    let mut kb = load_kb_with(PRED);
    let ns = "test.cbrd2.ownrule";
    for (query, holds) in [
        (format!("{ns}.viaGood(?y)"), true),
        (format!("{ns}.viaGood1(?y)"), false),
        (format!("{ns}.viaGoodR(?y, true)"), true),
        (format!("{ns}.Pred.good({ns}.Leaf.leaf(v: 3))"), true),
        (format!("{ns}.Pred.good({ns}.Leaf.leaf(v: 1))"), false),
    ] {
        let (answers, reads) = counting(|| pattern_answer_counts(&mut kb, &query));
        assert_eq!(answers, if holds { (1, 1) } else { (0, 0) }, "{query}");
        assert_eq!(reads, 0, "{query}: a dictionary read off the values");
    }
}

/// An operation's citation passed the requirement already (the module doc).
#[test]
fn an_operations_citation_is_the_control() {
    let mut interp = interp_for(PRED);
    let (got, reads) = counting(|| {
        interp
            .call("test.cbrd2.ownrule.viaOp", &anthill_core::eval::HostValue::all(&[]))
            .map(|h| h.value)
    });
    assert!(matches!(got, Ok(anthill_core::eval::Value::Int(1))), "{got:?}");
    assert_eq!(reads, 0);
}

/// `Int64` provides no `Pred`: a goal putting the call's receiver there, `Pred.good(5)`, is
/// refused at load naming it, as a goal whose guard is built at a type nothing provides is.
#[test]
fn a_requirement_nothing_provides_at_the_goal_is_refused() {
    let src = PRED.replace("  rule viaGood(?y)", "  rule viaInt(1) :- Pred.good(5)\n  rule viaGood(?y)");
    let errors = crate::common::load_errors_of(&src);
    assert!(errors.iter().any(|e| e.contains("viaInt") && e.contains("Pred")), "refused, naming `Pred`: {errors:?}");
}

/// At the caller's own type parameter, the caller's guard of the spec there is what its goal
/// passes: `viaParam[A](?y: A) :- Pred[T = A], Pred.good(?y)` hands `Pred.good` the `Pred` its
/// citation chose — `Other`'s `ok`, which is false, at `viaParam[A = Leaf, Pred = Other]` — and
/// nothing is read from the value, which would give `Leaf`'s own.
#[test]
fn a_goal_at_the_callers_parameter_passes_its_guard() {
    let src = PRED
        .replace(
            "  fact src(leaf(v: 3))",
            "  sort Other\n    provides Pred[T = Leaf]\n    operation ok(x: Leaf) -> Bool = false\n  end\n  fact src(leaf(v: 3))",
        )
        .replace(
            "  rule viaGood(?y)",
            "  rule viaParam[A](?y: A) :- Pred[T = A], Pred.good(?y)\n  rule viaP(?y) :- src(?y), viaParam(?y)\n  rule viaGood(?y)",
        );
    let mut kb = load_kb_with(&src);
    let ns = "test.cbrd2.ownrule";
    for (query, holds) in [
        (format!("{ns}.viaP(?y)"), true),
        (format!("{ns}.viaParam[A = {ns}.Leaf, Pred = {ns}.Other]({ns}.Leaf.leaf(v: 3))"), false),
    ] {
        let (answers, reads) = counting(|| pattern_answer_counts(&mut kb, &query));
        assert_eq!(answers, if holds { (1, 1) } else { (0, 0) }, "{query}");
        assert_eq!(reads, 0, "{query}: a dictionary read off the values");
    }
}
