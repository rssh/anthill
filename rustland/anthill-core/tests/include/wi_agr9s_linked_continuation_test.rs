//! WI-20261127-AGR9S (proposal 076 Stage A) — THE CONTINUATION IS LINKED, NOT COPIED.
//!
//! A branch's goals are a persistent chain of scopes (`Goals` in `kb/resolve.rs`): opening a
//! body links a scope in front of what follows the goal it answers, and copies nothing. NO
//! CHANGE OF BEHAVIOUR: these rows hold on the flat copied resolvent too, and are what the
//! linked one must keep. What changed is memory, which a test of a search's answers cannot see:
//! it is measured on the CLI, peak RSS, in `docs/measurements/076-stage-a/` (the growing
//! resolvent of the second row, quadratic before, linear after). The order of every operation
//! against the flat `Vec` is held by `kb::resolve::goals_tests`.
//!
//! THE MARKERS RETIRED (076 Stage A, "what it retires"): a discharge's scope records the
//! assumptions it pushed and drops them at its exit, where a `__pop_assumption(n)` goal behind
//! its consequents did; a clause body with a top-level `!` records the call height its cut
//! commits to, where a barrier baked into `cut(B)` and a choice point tagged with it did. The
//! rows from `a_discharges_assumptions_end_at_its_scopes_exit` on drive them.
//!
//! BACK-OUT, measured 2026-11-28 in ONE run with both backed out: a side of `push_choice` opened
//! one deeper than the goal it splits, and the waiting goals turned round unreversed. It fails
//! `a_side_of_a_choice_is_no_call` and `goals_that_waited_come_round_in_the_order_they_waited`,
//! each its own change's: the order row asks no choice, and the choice row waits on nothing. The
//! growing resolvent's row passes either way, by design: it pins the answer and the proof count
//! the representation must keep.
//!
//! The retirement, measured 2026-11-28, one back-out at a time: the exit keeping the
//! assumptions it should drop fails `a_discharges_assumptions_end_at_its_scopes_exit`; a
//! discharge's scope exiting when its last goal opens a clause (before that body runs) fails
//! `a_body_opened_by_a_discharges_last_goal_runs_under_its_assumptions` and
//! `an_assumption_binds_a_callers_variable`; a clause body recording no call height (every `!`
//! to the stack floor) fails `cut_test::inner_cut_is_opaque_to_outer_or`. The cut row here
//! (`a_cut_with_an_argument_is_a_fault`) holds under all three.

use crate::common::{load_kb_with, query_pattern_term, resolve_with_messages, supply_invocation_imports};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::print::TermPrinter;

const SRC: &str = r#"
namespace wiagr9s
  import anthill.reflect.{nonvar}
  fact ok(1)
  fact left(1)
  rule viaRule(?x) :- left(?x)
  rule chain(?n) :- (?n = 0) | (?n > 0, chain(?n - 1), ok(1))
  rule waits(?x) :- not(left(?x)), not(ok(?x)), not(viaRule(?x))

  fact hyp(99)
  rule after(?y) :- (forall(?n), hyp(7) -: hyp(7)), hyp(?y)
  rule asksHyp :- hyp(7)
  rule lastCall :- (forall(?n), hyp(7) -: asksHyp)
  rule pick(0) :- hyp(1)
  rule pick(0) :- hyp(2)
  rule t1(?x) :- (forall(?n), hyp(?x) -: pick(0))
  rule t2(?x) :- (forall(?n), hyp(?x) -: pick(0), ?x <=> 2)
  rule needsHyp(?y) :- nonvar(?y), hyp(?y)
  rule wokenAtExit(?y) :- needsHyp(?y), (forall(?n), hyp(5) -: ?y <=> 5)
end
"#;

fn kb() -> KnowledgeBase {
    let mut kb = load_kb_with(SRC);
    supply_invocation_imports(&mut kb, &["wiagr9s.*"]);
    kb
}

fn definite_answers(kb: &mut KnowledgeBase, pattern: &str, config: &ResolveConfig) -> usize {
    let goal = query_pattern_term(kb, pattern);
    let (solutions, _) = kb.resolve_with_stats(&[goal], config);
    solutions.iter().filter(|s| s.is_definite()).count()
}

fn at_depth(max_depth: usize) -> ResolveConfig {
    ResolveConfig {
        max_depth,
        ..ResolveConfig::default()
    }
}

/// DEPTH IS A FIELD, NOT HOW DEEPLY SCOPES ARE NESTED (076 Stage A). Each side of
/// `push_choice` is a scope of its own, at the depth of the goal it splits, so the choice
/// answers at `max_depth` 0 (measured on the CLI before the change, 2026-11-24 and again
/// 2026-11-28: `true`). FAILS where a side's depth is counted from its nesting.
///
/// CONTROL, passing either way: a clause body is one deeper, so `viaRule(1)` is not asked at
/// depth 0 and is at depth 1.
#[test]
fn a_side_of_a_choice_is_no_call() {
    let mut kb = kb();
    assert_eq!(
        definite_answers(&mut kb, "anthill.kernel.push_choice((1 === 1), (1 === 2))", &at_depth(0)),
        1,
        "the left side holds at depth 0"
    );
    assert_eq!(definite_answers(&mut kb, "viaRule(1)", &at_depth(0)), 0);
    assert_eq!(definite_answers(&mut kb, "viaRule(1)", &at_depth(1)), 1);
}

/// THE GROWING RESOLVENT (076 § MEASURED): `ok(1)` waits behind each recursive call, so the
/// continuation at the base holds one scope a level, each linked to its caller's. One answer,
/// one proof, no residual, as on the copied resolvent — at a size the copied resolvent took
/// gigabytes for (5.06 GB at n = 4000, debug CLI).
#[test]
fn a_resolvent_that_grows_a_goal_a_level_has_one_proof() {
    let mut kb = kb();
    let goal = query_pattern_term(&mut kb, "chain(3000)");
    let config = ResolveConfig {
        max_depth: 100_000,
        // A proof count: `chain(3000)` is ground, so every proof is an answer here.
        dedup_answers: false,
        ..ResolveConfig::default()
    };
    let (solutions, stats) = kb.resolve_with_stats(&[goal], &config);
    assert!(!stats.truncated, "complete: {stats:?}");
    assert_eq!(solutions.len(), 1, "one proof");
    assert!(solutions[0].is_definite());
}

/// A GOAL THAT WAITS goes behind every other goal — behind every scope — and the goals that
/// waited come round in the order they waited. The three negations wait on `?x`, and after one
/// lap they are back in the order they were written: the residual's order. FAILS with the
/// waiting goals turned round the wrong way (two waiting goals cannot tell, so there are three).
#[test]
fn goals_that_waited_come_round_in_the_order_they_waited() {
    let mut kb = kb();
    let goal = query_pattern_term(&mut kb, "waits(?x)");
    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(solutions.len(), 1);
    let residual: Vec<String> = solutions[0]
        .residual
        .iter()
        .map(|g| TermPrinter::new(&kb).print_value(g))
        .collect();
    let order: Vec<usize> = ["left(", "ok(", "viaRule("]
        .iter()
        .map(|name| {
            residual
                .iter()
                .position(|r| r.contains(name))
                .unwrap_or_else(|| panic!("no `{name}` in the residual {residual:?}"))
        })
        .collect();
    assert_eq!(order, vec![0, 1, 2], "in the order written: {residual:?}");
}

/// THE EXIT DROPS WHAT THE SCOPE PUSHED. After `forall(?n), hyp(7) -: hyp(7)` the assumption
/// `hyp(7)` is out of scope, so the `hyp(?y)` after the discharge answers only the fact: one
/// answer, 99. FAILS where the discharge's scope keeps its assumptions past its exit (the
/// assumption then answers `hyp(?y)` with 7 as well).
#[test]
fn a_discharges_assumptions_end_at_its_scopes_exit() {
    let mut kb = kb();
    assert_eq!(definite_answers(&mut kb, "after(?y)", &ResolveConfig::default()), 1);
    assert_eq!(definite_answers(&mut kb, "after(99)", &ResolveConfig::default()), 1);
    assert_eq!(definite_answers(&mut kb, "after(7)", &ResolveConfig::default()), 0);
}

/// A SCOPE WAITS FOR ITS EXIT. The consequent `asksHyp` is the discharge's LAST goal; the body
/// it opens, `hyp(7)`, runs inside the discharge, so the assumption answers it. FAILS where the
/// discharge's scope, left with no goal of its own when its last goal opens a clause, exits
/// there and then — before the body it opened has run.
#[test]
fn a_body_opened_by_a_discharges_last_goal_runs_under_its_assumptions() {
    let mut kb = kb();
    assert_eq!(definite_answers(&mut kb, "lastCall", &ResolveConfig::default()), 1);
}

/// 076 §3's `t1` / `t2`: a ground consequent binds a CALLER variable through the assumption
/// `hyp(?x)`. `t1` answers `?x = 1` and `?x = 2`, one per clause of `pick`; in `t2` the
/// continuation of the first fails and the second is the only answer. Pinned, as the
/// assumptions moved from the frame into the continuation.
#[test]
fn an_assumption_binds_a_callers_variable() {
    let mut kb = kb();
    assert_eq!(definite_answers(&mut kb, "t1(?x)", &ResolveConfig::default()), 2);
    assert_eq!(definite_answers(&mut kb, "t1(1)", &ResolveConfig::default()), 1);
    assert_eq!(definite_answers(&mut kb, "t1(2)", &ResolveConfig::default()), 1);
    assert_eq!(definite_answers(&mut kb, "t2(?x)", &ResolveConfig::default()), 1);
    assert_eq!(definite_answers(&mut kb, "t2(2)", &ResolveConfig::default()), 1);
}

/// The cut is NOT BAKED: it stays the nullary `cut` the parser mints, and its body's scope says
/// what it cuts to. So a `cut` with an argument is no cut the resolver made, and asking one is a
/// FAULT, named — where a baked barrier used to be read off it.
#[test]
fn a_cut_with_an_argument_is_a_fault() {
    let (solutions, messages) =
        resolve_with_messages("namespace wiagr9s.cutarg\n  fact seed(1)\nend\n", "anthill.kernel.cut(1)");
    assert!(solutions.iter().all(|s| !s.is_definite()), "no definite answer");
    assert!(
        messages.iter().any(|m| m.contains("takes no argument")),
        "{messages:?}"
    );
}

/// THE ONE ANSWER THE RETIREMENT MOVED, measured on the CLI before and after (2026-11-28).
/// `needsHyp(?y)` is the CALLER's goal: its clause waits on `?y`, so it goes behind the
/// discharge. The discharge's last goal binds `?y`, and `hyp(5)` holds only as the discharge's
/// hypothesis, so `needsHyp(5)` has no proof outside it: NO ANSWER. Before 076 Stage A's
/// retirement it answered `?y = 5`: the binding came on the step whose current goal was the
/// `__pop_assumption` marker, and the woken goal went in front of it, inside the hypothesis.
/// Now the scope exits as its last goal is discharged, before anything wakes.
///
/// NOT FIXED HERE, and stated: with one more goal in the consequent (`?y <=> 5, true`) the
/// binding comes while the scope is live, the woken caller goal is moved in front of the current
/// goal, inside the scope, and is answered by the hypothesis — `?y = 5`, before and after. A
/// woken goal asked in the context it was first asked in is proposal 076 Stage B.
#[test]
fn a_caller_goal_woken_at_a_discharges_exit_is_not_answered_by_its_hypothesis() {
    let mut kb = kb();
    assert_eq!(definite_answers(&mut kb, "wokenAtExit(?y)", &ResolveConfig::default()), 0);
}
