//! A CALL NOTHING RUNS DERIVES NO DICTIONARY (WI-20261105-CBRD2; proposal 073 §1). `Set`'s
//! operations have no body, no host mapping and no provider: `Set.insert(Set.empty(), 1)` is
//! an unreduced call (kernel-language §8.3), and a comparison over one is undecided. The
//! resolver's bridge still built each such call's dictionaries from its argument values first —
//! `Set`'s `requires Eq[T]` at the element the values carry (`typing::resolve_bridge_requirements`,
//! `resolve::bridge_derivations_by_this_thread`) — and only then found nothing to enter: 84 of
//! the gate's 100 derivations (wi616, wi625, wi939, vpewk, wi880, k4jgc).
//!
//! A call whose operation runs nothing of its own, of a sort nothing provides
//! (`typing::no_call_of_it_runs`), ends where its dispatch would, `OperationBodyMissing`, before
//! anything is derived (`Interpreter::call_op_bridged`). The verdicts are the ones the run gave:
//! undecided, and a failing sibling still refutes.
//!
//! ## What fails with the change backed out
//!
//! Measured with a temporary switch, then removed. The control is the switch unset: every row
//! passes.
//!
//! * The early answer off: [`a_call_nothing_runs_derives_nothing`] fails, 5 derivations;
//!   its verdicts stand.
//! * [`a_call_something_runs_still_answers`] passes either way: the control, a call the early
//!   answer must not take.

use anthill_core::eval::Value;
use anthill_core::kb::resolve::bridge_derivations_by_this_thread;

use crate::common::{load_kb_with, load_stdlib_kb, query_unary};

/// `f`'s result and the derivations from argument values during it, the shared base loaded
/// first.
fn counting<R>(f: impl FnOnce() -> R) -> (R, usize) {
    drop(load_stdlib_kb());
    let before = bridge_derivations_by_this_thread();
    let r = f();
    (r, bridge_derivations_by_this_thread() - before)
}

/// Each row's answers, as (the value printed, definite).
fn rows(kb: &mut anthill_core::kb::KnowledgeBase, qn: &str) -> Vec<(String, bool)> {
    query_unary(kb, qn)
        .into_iter()
        .map(|(v, definite)| {
            let shown = match v {
                Value::Int(n) => n.to_string(),
                other => format!("{other:?}"),
            };
            (shown, definite)
        })
        .collect()
}

/// A comparison over `Set` calls is undecided — one conditional answer — and one beside a
/// failing goal has none; nothing is derived from the values for any of them.
#[test]
fn a_call_nothing_runs_derives_nothing() {
    let src = r#"
namespace test.cbrd2.unrun
  import anthill.prelude.{Int64, Set}
  import anthill.prelude.Set.{intersection}
  rule same(1) :- Set.insert(Set.empty(), 1) = Set.insert(Set.empty(), 1)
  rule cut(1) :- intersection({1, 2}, {2}) = {2}
  rule refuted(1) :- Set.insert(Set.empty(), 1) = Set.insert(Set.empty(), 2), 1 = 2
end
"#;
    let mut kb = load_kb_with(src);
    let ((same, cut, refuted), derivations) = counting(|| {
        (
            rows(&mut kb, "test.cbrd2.unrun.same"),
            rows(&mut kb, "test.cbrd2.unrun.cut"),
            rows(&mut kb, "test.cbrd2.unrun.refuted"),
        )
    });
    assert_eq!(same, vec![("1".to_string(), false)], "undecided over an unreduced `insert`");
    assert_eq!(cut, vec![("1".to_string(), false)], "undecided over an unreduced `intersection`");
    assert_eq!(refuted, Vec::<(String, bool)>::new(), "a failing sibling refutes the clause");
    assert_eq!(derivations, 0, "a dictionary derived for a call nothing runs");
}

/// A call something runs is not taken by the early answer: `List.contains`, which has a body,
/// and a body-less `Shape.area` that `Sq` provides, each answer definitely. Passes either way.
#[test]
fn a_call_something_runs_still_answers() {
    let src = r#"
namespace test.cbrd2.run
  import anthill.prelude.{Int64, Bool, List}
  sort Shape
    operation area(s: Self) -> Int64
  end
  sort Sq
    entity sq(n: Int64)
    provides Shape
    operation area(s: Sq) -> Int64 = match s case sq(n) -> n * n
  end
  rule has(1) :- List.contains(["z"], "z") = true
  rule four(1) :- Shape.area(sq(n: 2)) = 4
end
"#;
    let mut kb = load_kb_with(src);
    assert_eq!(rows(&mut kb, "test.cbrd2.run.has"), vec![("1".to_string(), true)]);
    assert_eq!(rows(&mut kb, "test.cbrd2.run.four"), vec![("1".to_string(), true)]);
}
