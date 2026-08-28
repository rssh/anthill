//! WI-364 — first concrete MutableCollection carrier (proposal
//! docs/proposals/library/002-iteration-collection.md, Phase 4).
//!
//! `MutableStack` (stdlib/anthill/prelude/mutable_stack.anthill) is a nominal
//! `mutableStack(rep: Cell[V = List[T]])` wrapper (head of the list = top):
//! the handle is a Cell, so `Modify[s]` rides the existing Cell arena + Modify
//! handler. The provision bodies FIELD-PROJECT the backing cell (`Cell.set(s.rep,
//! …)`): the declared `Modify[s]` covers the incurred `Modify[s.rep]` (WI-506)
//! and the desugared `field_access` node round-trips a re-type-check (WI-509).
//!
//! These tests pin the full mutable lifecycle under effect tracking, threading
//! ONE handle across calls so the in-place mutations are observed:
//!   - the stack API: push -> top -> pop (LIFO, read+mutate) -> empty pop;
//!   - the collection view: size (walk via iterator) and clear.

use crate::common::{interp_for, register_modify_handler};
use anthill_core::eval::Value;

/// Helper ops wrapping the calls so the Rust side can thread a single handle.
/// `popOr`/`peekOr` collapse the `Option[T]` result to an `Int64` (with a
/// sentinel for empty) so the assertions stay simple; `depth` is
/// `FiniteCollection.size` (post-WI-589: MutableStack provides FiniteCollection,
/// `size` materializes the current contents via `collect`/`Cell.get`).
///
/// The MutableCollection interface is exercised through its ABSTRACT spec ops:
/// `new()` (WI-508 — carrier pinned by the `MutableStack[T = Int64]` return
/// type), `insert`/`clear` (WI-507 — carrier-only bare calls). All dispatch
/// end-to-end now; the element is concrete (`MutableStack[T = Int64]`) so the
/// carrier-only ops resolve `Element`.
const SRC: &str = r#"
namespace test.wi364.stack
  import anthill.prelude.{Int64, Bool, Unit, List, Iterable, Stream, MutableStack}
  import anthill.prelude.Option.{none, some}
  import anthill.prelude.MutableCollection.{new, insert, clear}
  import anthill.prelude.FiniteCollection.{size}
  import anthill.prelude.Stream.{takeN}

  operation fresh() -> MutableStack[T = Int64] effects Modify[result] = new()
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
  operation wipe(s: MutableStack[T = Int64]) -> Unit effects Modify[s] = clear(s)

  operation inc(x: Int64) -> Int64 = x + 1

  -- WI-590 REGRESSION GUARD. `Iterable.map` is applied, the SOURCE is then mutated,
  -- and only then is the result walked. `iterator`'s contract is a SNAPSHOT taken at
  -- `iterator` time, so the walk must not see the later push.
  operation map_then_push_then_count(s: MutableStack[T = Int64]) -> Int64
    effects Modify[s] =
    let m = Iterable.map(s, inc)
    let _ = MutableStack.push(s, 99)
    List.length(takeN(Iterable.iterator(m), 100))
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
        i.call("test.wi364.stack.depth", &[h.clone()])
            .expect("depth")
            .as_int()
    };
    let pop = |i: &mut anthill_core::eval::Interpreter, h: &Value| {
        i.call("test.wi364.stack.popOr", &[h.clone(), Value::Int(-1)])
            .expect("pop")
            .as_int()
    };

    // fresh stack is empty; popping it yields the sentinel
    assert_eq!(depth(&mut interp, &s), Some(0), "a fresh stack is empty");
    assert_eq!(pop(&mut interp, &s), Some(-1), "pop on empty -> sentinel");

    // push 10, 20, 30 (30 ends on top)
    for x in [10, 20, 30] {
        interp
            .call("test.wi364.stack.pushN", &[s.clone(), Value::Int(x)])
            .expect("push");
    }
    assert_eq!(depth(&mut interp, &s), Some(3), "three pushes -> depth 3");

    // top peeks without removing
    let peek = interp
        .call("test.wi364.stack.peekOr", &[s.clone(), Value::Int(-1)])
        .expect("peek");
    assert_eq!(peek.as_int(), Some(30), "top is the last pushed (30)");
    assert_eq!(depth(&mut interp, &s), Some(3), "peek does not remove");

    // pop in LIFO order
    assert_eq!(pop(&mut interp, &s), Some(30), "pop -> 30 (LIFO)");
    assert_eq!(pop(&mut interp, &s), Some(20), "pop -> 20");
    assert_eq!(depth(&mut interp, &s), Some(1), "one element left");

    // clear empties the rest
    interp
        .call("test.wi364.stack.wipe", &[s.clone()])
        .expect("clear");
    assert_eq!(
        depth(&mut interp, &s),
        Some(0),
        "clear empties the same handle"
    );
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
        interp
            .call("test.wi364.stack.depth", &[s.clone()])
            .unwrap()
            .as_int(),
        Some(0),
        "a fresh stack is empty",
    );

    // insert via the MutableCollection op; the witness is true (stack/bag)
    let w1 = interp
        .call("test.wi364.stack.addColl", &[s.clone(), Value::Int(10)])
        .expect("insert 10");
    assert_eq!(
        w1.as_bool(),
        Some(true),
        "insert returns the 'was new' witness"
    );
    interp
        .call("test.wi364.stack.addColl", &[s.clone(), Value::Int(20)])
        .expect("insert 20");

    // walk via iterator
    assert_eq!(
        interp
            .call("test.wi364.stack.depth", &[s.clone()])
            .unwrap()
            .as_int(),
        Some(2),
        "two inserts -> size 2 (walked via iterator)",
    );

    // clear empties
    interp
        .call("test.wi364.stack.wipe", &[s.clone()])
        .expect("clear");
    assert_eq!(
        interp
            .call("test.wi364.stack.depth", &[s])
            .unwrap()
            .as_int(),
        Some(0),
        "clear empties the same handle",
    );
}

/// Identity / non-aliasing: two `new()` allocations are distinct cells, so a
/// push to one is not observed by the other (the Cell opaque-handle scheme).
/// WI-590 — `Iterable.map` SNAPSHOTS its source, it does not capture it live.
///
/// `MutableStack.iterator`'s own doc is the contract this pins, in so many words:
/// "a later `push`/`pop` does not perturb an already-produced snapshot (it is the
/// List value captured at `iterator` time) — the 'snapshot, not live cursor' reading
/// in the proposal". `Iterable.map` inherits that by calling `iterator(c)` EAGERLY
/// and wrapping the result, rather than storing the carrier for the first peel to
/// walk.
///
/// FOUND BY `/code-review` ON WI-590, which had changed the body to `mapped(c, f)`
/// so the lazy carrier would keep the SOURCE SORT its finiteness witness reads. That
/// moved the snapshot to consume time, and nothing in the suite noticed — every
/// existing `map`/`filter` row runs over a `List`, whose `iterator` is the identity
/// and which cannot be mutated. The witness keeps its handle on the source sort
/// through `FiniteCollection.map`, whose `mapped(c, f)` stores the carrier exactly as
/// the pre-WI-590 `fmapped(c, f)` did; `Iterable.map` went back to `iterator(c)`.
///
/// MEASURED, both ways: push 1 and 2, map, push 99, walk. Snapshot semantics answer
/// 2. With `mapped(c, f)` restored in `Iterable.map` the same program answers 3 — so
/// this row fails when the eager `iterator(c)` is backed out, and it is the ONLY row
/// in the workspace that does.
#[test]
fn iterable_map_snapshots_the_source_it_does_not_capture_it_live() {
    let mut interp = interp_for(SRC);
    register_modify_handler(&mut interp);

    let s = interp.call("test.wi364.stack.fresh", &[]).expect("fresh");
    for v in [1i64, 2] {
        interp
            .call("test.wi364.stack.pushN", &[s.clone(), Value::Int(v)])
            .expect("push");
    }

    let counted = interp
        .call("test.wi364.stack.map_then_push_then_count", &[s])
        .expect("map, mutate, walk");
    assert_eq!(
        counted.as_int(),
        Some(2),
        "the walk must see the 2-element snapshot taken when `map` ran, not the \
         3 elements the source holds by the time it is walked"
    );
}

#[test]
fn mutable_stack_new_returns_distinct_handles() {
    let mut interp = interp_for(SRC);
    register_modify_handler(&mut interp);

    let a = interp.call("test.wi364.stack.fresh", &[]).expect("fresh a");
    let b = interp.call("test.wi364.stack.fresh", &[]).expect("fresh b");

    interp
        .call("test.wi364.stack.pushN", &[a.clone(), Value::Int(1)])
        .expect("push into a");

    let depth_a = interp
        .call("test.wi364.stack.depth", &[a])
        .expect("depth a");
    let depth_b = interp
        .call("test.wi364.stack.depth", &[b])
        .expect("depth b");
    assert_eq!(depth_a.as_int(), Some(1), "a got the push");
    assert_eq!(
        depth_b.as_int(),
        Some(0),
        "b is a distinct, untouched stack"
    );
}
