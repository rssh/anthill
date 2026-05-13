//! WI-205 — Cell sort + Modifiable marker. Verifies the Cell builtins
//! (new, get, set), the cell_arena lifecycle (refcount-driven slot
//! reclamation), and that the Modifiable facts for stdlib resources
//! resolve. Per `docs/design/cell-runtime.md`: each `Cell.new` returns
//! a fresh handle (opaque-handle identity), Cell.set is O(1), and
//! cycle prevention is the typer's job.

mod common;

use anthill_core::eval::Value;
use common::{interp_for, register_modify_handler};

#[test]
fn cell_new_then_get_round_trip() {
    let src = r#"
namespace test.wi205_round_trip
  import anthill.prelude.{Int, Cell}

  operation make_and_read(n: Int) -> Int =
    Cell.get(Cell.new(n))
end
"#;
    let mut interp = interp_for(src);
    register_modify_handler(&mut interp);

    let r = interp.call("test.wi205_round_trip.make_and_read", &[Value::Int(42)])
        .expect("make_and_read");
    assert_eq!(r.as_int(), Some(42));
}

#[test]
fn cell_set_overwrites_value() {
    let src = r#"
namespace test.wi205_overwrite
  import anthill.prelude.{Int, Cell, Unit}

  operation make(n: Int) -> Cell = Cell.new(n)
  operation overwrite(c: Cell, n: Int) -> Unit = Cell.set(c, n)
  operation read(c: Cell) -> Int = Cell.get(c)
end
"#;
    let mut interp = interp_for(src);
    register_modify_handler(&mut interp);

    let cell = interp.call("test.wi205_overwrite.make", &[Value::Int(1)]).expect("make");
    interp.call("test.wi205_overwrite.overwrite", &[cell.clone(), Value::Int(99)])
        .expect("overwrite");
    let r = interp.call("test.wi205_overwrite.read", &[cell]).expect("read");
    assert_eq!(r.as_int(), Some(99));
}

#[test]
fn cell_new_returns_distinct_handles() {
    // Two Cell.new calls with the same initial value must yield distinct
    // cells — opaque-handle identity, not value-keyed. Setting one must
    // not perturb the other.
    let src = r#"
namespace test.wi205_distinct
  import anthill.prelude.{Int, Cell, Unit}

  operation make(n: Int) -> Cell = Cell.new(n)
  operation set_value(c: Cell, n: Int) -> Unit = Cell.set(c, n)
  operation read(c: Cell) -> Int = Cell.get(c)
end
"#;
    let mut interp = interp_for(src);
    register_modify_handler(&mut interp);

    let a = interp.call("test.wi205_distinct.make", &[Value::Int(1)]).expect("make a");
    let b = interp.call("test.wi205_distinct.make", &[Value::Int(2)]).expect("make b");

    interp.call("test.wi205_distinct.set_value", &[a.clone(), Value::Int(100)])
        .expect("set a");

    let read_a = interp.call("test.wi205_distinct.read", &[a]).expect("read a");
    let read_b = interp.call("test.wi205_distinct.read", &[b]).expect("read b");
    assert_eq!(read_a.as_int(), Some(100), "a's update should land in a");
    assert_eq!(read_b.as_int(), Some(2), "b should be untouched");
}

#[test]
fn cell_handle_drop_reclaims_slot() {
    // Refcount lifecycle: drop the only handle, the arena's slot count
    // must drop. Mirrors the closure_arena / map_arena reclamation tests.
    let src = r#"
namespace test.wi205_refcount
  import anthill.prelude.{Int, Cell}
  operation make(n: Int) -> Cell = Cell.new(n)
end
"#;
    let mut interp = interp_for(src);
    register_modify_handler(&mut interp);

    let before = interp.cell_arena_live_count();
    let cell = interp.call("test.wi205_refcount.make", &[Value::Int(7)]).expect("make");
    assert_eq!(interp.cell_arena_live_count(), before + 1,
               "alloc should bump the live count");
    drop(cell);
    assert_eq!(interp.cell_arena_live_count(), before,
               "drop of last handle should reclaim the slot");
}

#[test]
fn cell_handle_clone_keeps_slot_alive() {
    // Cloning bumps refcount; both handles must keep the slot live;
    // both must drop before reclamation.
    let src = r#"
namespace test.wi205_clone
  import anthill.prelude.{Int, Cell}
  operation make(n: Int) -> Cell = Cell.new(n)
end
"#;
    let mut interp = interp_for(src);
    register_modify_handler(&mut interp);

    let before = interp.cell_arena_live_count();
    let h1 = interp.call("test.wi205_clone.make", &[Value::Int(0)]).expect("make");
    let h2 = h1.clone();
    drop(h1);
    assert_eq!(interp.cell_arena_live_count(), before + 1,
               "h2 still references the slot");
    drop(h2);
    assert_eq!(interp.cell_arena_live_count(), before,
               "no live handle remains; slot reclaimed");
}

#[test]
fn cell_recursive_allocation_no_aliasing() {
    // Each nested Cell.new call must see its own cell at unwind.
    let src = r#"
namespace test.wi205_recursive
  import anthill.prelude.{Int, Cell, Bool}

  -- Each frame contributes Cell.get(c) - n to the sum. If no
  -- aliasing, the contribution is 0 per frame and the total is 0.
  -- With aliasing, an inner call would have overwritten our cell to
  -- a smaller n, so Cell.get(c) - n would be negative on at least
  -- one frame and the total drifts away from 0.
  operation chain(n: Int) -> Int =
    if n < 1 then 0
    else
      let c = Cell.new(n)
      let rec = chain(n - 1)
      Cell.get(c) - n + rec
end
"#;
    let mut interp = interp_for(src);
    register_modify_handler(&mut interp);

    // Each frame contributes Cell.get(c) - n; if no aliasing, this is 0
    // for every frame, so the sum is 0. With aliasing, the inner call
    // overwrites our cell with a smaller n; Cell.get(c) - n becomes
    // negative on at least some frames and the sum is strictly < 0.
    let r = interp.call("test.wi205_recursive.chain", &[Value::Int(100)])
        .expect("chain");
    assert_eq!(r.as_int(), Some(0),
               "each recursion frame must read back its own cell value");
}

#[test]
fn modify_set_get_on_cell_routes_through_arena() {
    // WI-205 (a) per-resource Modify dispatch: calling Modify.set / .get
    // directly on a Value::Cell handle (not via Cell.set/get) routes to
    // the cell arena, identical to Cell.set/get. Distinct cells must
    // remain independent — confirms the arena, not the functor-keyed
    // fallback map, is what stores the value.
    let mut interp = interp_for("namespace test.wi205_modify_cell end\n");
    register_modify_handler(&mut interp);

    let cell_a = interp.alloc_cell(Value::Int(1));
    let cell_b = interp.alloc_cell(Value::Int(2));
    let cell_a_value = Value::Cell(cell_a);
    let cell_b_value = Value::Cell(cell_b);

    let set_sym = interp.kb_mut().intern("set");
    let get_sym = interp.kb_mut().intern("get");

    interp.invoke_effect_handler(
        "anthill.prelude.Modify",
        set_sym,
        &[cell_a_value.clone(), Value::Int(100)],
    ).expect("Modify.set on Cell A");

    let got_a = interp.invoke_effect_handler(
        "anthill.prelude.Modify", get_sym, &[cell_a_value],
    ).expect("Modify.get on Cell A");
    assert_eq!(got_a.as_int(), Some(100), "Cell A should hold the written value");

    let got_b = interp.invoke_effect_handler(
        "anthill.prelude.Modify", get_sym, &[cell_b_value],
    ).expect("Modify.get on Cell B");
    assert_eq!(got_b.as_int(), Some(2),
        "Cell B should remain untouched — functor-keyed aliasing must not happen");
}

#[test]
fn modifiable_facts_for_stdlib_resources_resolve() {
    // Confirm that `Modifiable` is registered as a sort and that
    // FileStore / IndexedFileStore / KB / Cell satisfy it via facts
    // emitted alongside their declarations.
    let interp = interp_for(r#"
namespace test.wi205_modifiable
  -- empty namespace just to drive the load.
end
"#);
    let kb = interp.kb();
    assert!(
        kb.try_resolve_symbol("anthill.prelude.Modifiable").is_some(),
        "Modifiable sort must be declared",
    );
    let modifiable_sym = kb.try_resolve_symbol("anthill.prelude.Modifiable").unwrap();
    let facts = kb.by_functor(modifiable_sym);
    assert!(
        !facts.is_empty(),
        "expected at least one Modifiable[T = ...] fact (Cell, FileStore, etc.)",
    );
}
