//! WI-205 — Cell sort + Modifiable marker. Verifies the Cell builtins
//! (new, get, set) round-trip via the Modify handler, and that the
//! Modifiable facts for stdlib resources resolve.

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
