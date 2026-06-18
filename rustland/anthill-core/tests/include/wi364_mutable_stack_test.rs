//! WI-364 — first concrete MutableCollection carrier (proposal
//! docs/proposals/library/002-iteration-collection.md, Phase 4).
//!
//! `MutableStack` (stdlib/anthill/prelude/mutable_stack.anthill) is a nominal
//! `mutableStack(rep: Cell[V = List[T]])` wrapper (head of the list = top):
//! the handle is a Cell, so `Modify[s]` rides the existing Cell arena + Modify
//! handler. The provision bodies pattern-match the wrapper to bind the inner
//! cell (the WorkItemStore idiom, WI-219), so the inner `Modify[rep]` is elided
//! as a local and the declared `Modify[s]` is the honest caller-visible effect.
//!
//! These tests pin the full mutable lifecycle under effect tracking, threading
//! ONE handle across calls so the in-place mutations are observed:
//!   - the stack API: push -> top -> pop (LIFO, read+mutate) -> empty pop;
//!   - the collection view: size (walk via iterator) and clear.

use anthill_core::eval::Value;
use crate::common::{interp_for, register_modify_handler};

/// Helper ops wrapping the calls so the Rust side can thread a single handle.
/// `popOr`/`peekOr` collapse the `Option[T]` result to an `Int64` (with a
/// sentinel for empty) so the assertions stay simple; `depth` walks via
/// `iterator` (Iterable.size), exercising the read bridge.
///
/// Two call-form choices sidestep dispatch gaps the WI-364 probe found (each a
/// filed follow-up; the carrier itself is unaffected): `MutableStack.new()`
/// (the carrier's own constructor) rather than the abstract
/// `MutableCollection.new()` (WI-508, nullary result-only carrier), and
/// `s.clear()` (dot) rather than the bare `clear(s)` (WI-507, carrier-only
/// mutating spec op eval-arity). The element is concrete
/// (`MutableStack[T = Int64]`) so the carrier-only `clear`/`size` resolve
/// `Element`.
const SRC: &str = r#"
namespace test.wi364.stack
  import anthill.prelude.{Int64, Bool, Unit, MutableStack}
  import anthill.prelude.Option.{none, some}
  import anthill.prelude.MutableCollection.{insert, clear}
  import anthill.prelude.Iterable.{size}

  operation fresh() -> MutableStack[T = Int64] effects Modify[result] = MutableStack.new()
  operation pushN(s: MutableStack[T = Int64], x: Int64) -> Unit effects Modify[s] = MutableStack.push(s, x)

  -- the MutableCollection view of adding (insert returns the "was new" witness)
  operation addColl(s: MutableStack[T = Int64], x: Int64) -> Bool effects Modify[s] = insert(s, x)

  operation popOr(s: MutableStack[T = Int64], d: Int64) -> Int64 effects Modify[s] =
    match MutableStack.pop(s)
      case some(x) -> x
      case none() -> d

  operation peekOr(s: MutableStack[T = Int64], d: Int64) -> Int64 =
    match MutableStack.top(s)
      case some(x) -> x
      case none() -> d

  operation depth(s: MutableStack[T = Int64]) -> Int64 = size(s)
  operation wipe(s: MutableStack[T = Int64]) -> Unit effects Modify[s] = s.clear()
end
"#;

/// The carrier loads and its ops typecheck/dispatch on `MutableStack`.
#[test]
fn mutable_stack_carrier_loads_clean() {
    let _ = interp_for(SRC);
}

/// Full mutable lifecycle, threading ONE handle: new -> push x3 -> top/pop
/// (LIFO) -> size -> clear. The same `s` is passed back into each call, so the
/// in-place mutations accumulate and `pop`/`clear` are observed.
#[test]
fn mutable_stack_lifecycle_push_pop_lifo() {
    let mut interp = interp_for(SRC);
    register_modify_handler(&mut interp);

    let s = interp.call("test.wi364.stack.fresh", &[]).expect("fresh");

    let depth = |i: &mut anthill_core::eval::Interpreter, h: &Value| {
        i.call("test.wi364.stack.depth", &[h.clone()]).expect("depth").as_int()
    };
    let pop = |i: &mut anthill_core::eval::Interpreter, h: &Value| {
        i.call("test.wi364.stack.popOr", &[h.clone(), Value::Int(-1)]).expect("pop").as_int()
    };

    // fresh stack is empty; popping it yields the sentinel
    assert_eq!(depth(&mut interp, &s), Some(0), "a fresh stack is empty");
    assert_eq!(pop(&mut interp, &s), Some(-1), "pop on empty -> sentinel");

    // push 10, 20, 30 (30 ends on top)
    for x in [10, 20, 30] {
        interp.call("test.wi364.stack.pushN", &[s.clone(), Value::Int(x)]).expect("push");
    }
    assert_eq!(depth(&mut interp, &s), Some(3), "three pushes -> depth 3");

    // top peeks without removing
    let peek = interp.call("test.wi364.stack.peekOr", &[s.clone(), Value::Int(-1)]).expect("peek");
    assert_eq!(peek.as_int(), Some(30), "top is the last pushed (30)");
    assert_eq!(depth(&mut interp, &s), Some(3), "peek does not remove");

    // pop in LIFO order
    assert_eq!(pop(&mut interp, &s), Some(30), "pop -> 30 (LIFO)");
    assert_eq!(pop(&mut interp, &s), Some(20), "pop -> 20");
    assert_eq!(depth(&mut interp, &s), Some(1), "one element left");

    // clear empties the rest
    interp.call("test.wi364.stack.wipe", &[s.clone()]).expect("clear");
    assert_eq!(depth(&mut interp, &s), Some(0), "clear empties the same handle");
    assert_eq!(pop(&mut interp, &s), Some(-1), "pop on cleared -> sentinel");
}

/// The MutableCollection view, literally the proposal-002 Phase 4 acceptance
/// shape: new -> insert -> walk (size, via iterator) -> clear. `insert` returns
/// the "was new" witness (vacuously true for a stack/bag).
#[test]
fn mutable_stack_collection_view_insert_walk_clear() {
    let mut interp = interp_for(SRC);
    register_modify_handler(&mut interp);

    let s = interp.call("test.wi364.stack.fresh", &[]).expect("fresh");
    assert_eq!(
        interp.call("test.wi364.stack.depth", &[s.clone()]).unwrap().as_int(),
        Some(0),
        "a fresh stack is empty",
    );

    // insert via the MutableCollection op; the witness is true (stack/bag)
    let w1 = interp
        .call("test.wi364.stack.addColl", &[s.clone(), Value::Int(10)])
        .expect("insert 10");
    assert_eq!(w1.as_bool(), Some(true), "insert returns the 'was new' witness");
    interp
        .call("test.wi364.stack.addColl", &[s.clone(), Value::Int(20)])
        .expect("insert 20");

    // walk via iterator
    assert_eq!(
        interp.call("test.wi364.stack.depth", &[s.clone()]).unwrap().as_int(),
        Some(2),
        "two inserts -> size 2 (walked via iterator)",
    );

    // clear empties
    interp.call("test.wi364.stack.wipe", &[s.clone()]).expect("clear");
    assert_eq!(
        interp.call("test.wi364.stack.depth", &[s]).unwrap().as_int(),
        Some(0),
        "clear empties the same handle",
    );
}

/// Identity / non-aliasing: two `new()` allocations are distinct cells, so a
/// push to one is not observed by the other (the Cell opaque-handle scheme).
#[test]
fn mutable_stack_new_returns_distinct_handles() {
    let mut interp = interp_for(SRC);
    register_modify_handler(&mut interp);

    let a = interp.call("test.wi364.stack.fresh", &[]).expect("fresh a");
    let b = interp.call("test.wi364.stack.fresh", &[]).expect("fresh b");

    interp.call("test.wi364.stack.pushN", &[a.clone(), Value::Int(1)]).expect("push into a");

    let depth_a = interp.call("test.wi364.stack.depth", &[a]).expect("depth a");
    let depth_b = interp.call("test.wi364.stack.depth", &[b]).expect("depth b");
    assert_eq!(depth_a.as_int(), Some(1), "a got the push");
    assert_eq!(depth_b.as_int(), Some(0), "b is a distinct, untouched stack");
}
