//! WI-364 — first concrete MutableCollection carrier (proposal
//! docs/proposals/library/002-iteration-collection.md, Phase 4).
//!
//! `MutableList` (stdlib/anthill/prelude/mutable_list.anthill) is a nominal
//! `mutableList(rep: Cell[V = List[T]])` wrapper: the handle is a Cell, so
//! `Modify[c]` rides the existing Cell arena + Modify handler. The provision
//! bodies pattern-match the wrapper to bind the inner cell (the WorkItemStore
//! idiom, WI-219), so the inner `Modify[rep]` is elided as a local and the
//! declared `Modify[c]` is the honest caller-visible effect.
//!
//! These tests pin the full mutable lifecycle under effect tracking:
//! new -> insert -> walk via iterator -> clear, threading ONE handle across
//! calls so the in-place mutations are observed (not a functional copy).

use anthill_core::eval::Value;
use crate::common::{interp_for, register_modify_handler};

/// Helper ops wrapping the spec calls so the Rust side can thread a single
/// handle through the lifecycle. `count`/`total` walk via `iterator`
/// (Iterable.size / foldLeft), so they exercise the read bridge end-to-end.
///
/// Two call-form choices below sidestep dispatch gaps the WI-364 probe found
/// (each filed as a follow-up; the carrier itself is unaffected):
///   - `MutableList.new()` (the carrier's own constructor) rather than the
///     abstract `MutableCollection.new()` — a NULLARY spec op whose carrier is
///     only in the result does not yet pin Element/E from the expected return
///     type (WI-508).
///   - `c.clear()` (dot form) rather than the bare `clear(c)` — a bare-call
///     value-directed dispatch of a carrier-only mutating spec op typechecks
///     but fails at eval with an arity mismatch (WI-507); the dot form is
///     correct.
/// The element is written concretely (`MutableList[T = Int64]`) so the
/// carrier-only `clear`/`size` resolve `Element` (an abstract `MutableList`
/// leaves it unbound).
const SRC: &str = r#"
namespace test.wi364.lifecycle
  import anthill.prelude.{Int64, Bool, Unit, MutableList}
  import anthill.prelude.MutableCollection.{insert, clear}
  import anthill.prelude.Iterable.{size, foldLeft}

  operation addp(a: Int64, b: Int64) -> Int64 = a + b

  operation fresh() -> MutableList[T = Int64] effects Modify[result] = MutableList.new()
  operation push(c: MutableList[T = Int64], x: Int64) -> Bool effects Modify[c] = insert(c, x)
  operation wipe(c: MutableList[T = Int64]) -> Unit effects Modify[c] = c.clear()

  -- read observations, walked through iterator(c) -> Stream
  operation count(c: MutableList[T = Int64]) -> Int64 = size(c)
  operation total(c: MutableList[T = Int64]) -> Int64 = foldLeft(c, 0, addp)
end
"#;

/// The carrier's wrapper ops typecheck (proves the stdlib carrier loaded and
/// the spec ops dispatch on the `MutableList` carrier).
#[test]
fn mutable_list_carrier_loads_clean() {
    // interp_for panics on a load/typecheck error, so a successful build is
    // the assertion (mutable_list.anthill is part of the stdlib it loads).
    let _ = interp_for(SRC);
}

/// Full mutable lifecycle under effect tracking, threading ONE handle:
/// new (empty) -> insert x2 -> walk -> clear -> walk. The same `m` is passed
/// back into each call, so the in-place mutations accumulate and `clear`
/// is observed.
#[test]
fn mutable_list_lifecycle_new_insert_walk_clear() {
    let mut interp = interp_for(SRC);
    register_modify_handler(&mut interp);

    let m = interp
        .call("test.wi364.lifecycle.fresh", &[])
        .expect("fresh allocates a mutable list");

    // fresh is empty
    let n0 = interp
        .call("test.wi364.lifecycle.count", &[m.clone()])
        .expect("count empty");
    assert_eq!(n0.as_int(), Some(0), "a fresh MutableList is empty");

    // insert two elements in place
    interp
        .call("test.wi364.lifecycle.push", &[m.clone(), Value::Int(10)])
        .expect("push 10");
    interp
        .call("test.wi364.lifecycle.push", &[m.clone(), Value::Int(20)])
        .expect("push 20");

    // walk via iterator: count and sum the contents
    let n2 = interp
        .call("test.wi364.lifecycle.count", &[m.clone()])
        .expect("count after inserts");
    assert_eq!(n2.as_int(), Some(2), "two inserts -> size 2");
    let sum = interp
        .call("test.wi364.lifecycle.total", &[m.clone()])
        .expect("total after inserts");
    assert_eq!(sum.as_int(), Some(30), "iterator walk yields 10 + 20 = 30");

    // clear in place, then walk again
    interp
        .call("test.wi364.lifecycle.wipe", &[m.clone()])
        .expect("clear");
    let n0b = interp
        .call("test.wi364.lifecycle.count", &[m])
        .expect("count after clear");
    assert_eq!(n0b.as_int(), Some(0), "clear empties the same handle");
}

/// Identity / non-aliasing: two `new()` allocations are distinct cells, so a
/// mutation to one is not observed by the other (the Cell opaque-handle
/// scheme — recursion-/multi-instance-safe, not a functor-keyed singleton).
#[test]
fn mutable_list_new_returns_distinct_handles() {
    let mut interp = interp_for(SRC);
    register_modify_handler(&mut interp);

    let a = interp.call("test.wi364.lifecycle.fresh", &[]).expect("fresh a");
    let b = interp.call("test.wi364.lifecycle.fresh", &[]).expect("fresh b");

    interp
        .call("test.wi364.lifecycle.push", &[a.clone(), Value::Int(1)])
        .expect("push into a");

    let count_a = interp.call("test.wi364.lifecycle.count", &[a]).expect("count a");
    let count_b = interp.call("test.wi364.lifecycle.count", &[b]).expect("count b");
    assert_eq!(count_a.as_int(), Some(1), "a got the insert");
    assert_eq!(count_b.as_int(), Some(0), "b is a distinct, untouched cell");
}
