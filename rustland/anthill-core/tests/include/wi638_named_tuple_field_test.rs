//! WI-638 — named-tuple component field access (`t.x`).
//!
//! A dot projection `t.x` where `t` types as a NAMED TUPLE (`(x: A, y: B)`,
//! `TypeExtractor::NamedTuple`) did not resolve: a named tuple's functor is
//! `named_tuple`, not a sort, so the receiver has no `recv_sort`, and both prior
//! dot-dispatch modes — the method fallback and the entity/sort field access —
//! are keyed on the receiver's sort. `t.x` therefore fell through to a loud
//! "no such member (dot dispatch)" error.
//!
//! The fix adds a THIRD dispatch mode in the `DotApply` typer frame: when the
//! receiver's type is a `NamedTuple`, resolve the zero-arg member against the
//! tuple's (component-name, type) list and reuse the same `field_access`
//! desugaring the entity path uses. The eval twin (`reflect_field_access`) reads
//! the component off the runtime `Value::Tuple` — a named component by short
//! name (from `named`), a positional `_N` component by index (from `pos`).

use anthill_core::eval::Value;
use crate::common::{interp_for, try_load_kb_with};

fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// THE acceptance shape: a named-tuple LITERAL projected by component name, a
/// PARAM typed as a named tuple projected by name, and a POSITIONAL tuple
/// projected by `_N` — all type-check and evaluate.
#[test]
fn named_tuple_component_access_types_and_evals() {
    let src = r#"
namespace test.wi638
  import anthill.prelude.{Int64}
  operation lit_x() -> Int64
    = (x: 10, y: 20).x
  operation lit_y() -> Int64
    = (x: 10, y: 20).y
  operation param_x(t: (x: Int64, y: Int64)) -> Int64
    = t.x
  operation param_y(t: (x: Int64, y: Int64)) -> Int64
    = t.y
  operation use_param() -> Int64
    = param_x((x: 7, y: 9))
  operation pos1() -> Int64
    = (100, 200)._1
  operation pos2() -> Int64
    = (100, 200)._2
end
"#;
    assert!(
        try_load_kb_with(src).is_ok(),
        "named-tuple component access must type-check; got: {:?}",
        try_load_kb_with(src).err(),
    );
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi638.lit_x"), 10, "(x:10,y:20).x");
    assert_eq!(run_int(&mut interp, "test.wi638.lit_y"), 20, "(x:10,y:20).y");
    assert_eq!(run_int(&mut interp, "test.wi638.use_param"), 7, "t.x on a named-tuple param");
    assert_eq!(run_int(&mut interp, "test.wi638.pos1"), 100, "(100,200)._1");
    assert_eq!(run_int(&mut interp, "test.wi638.pos2"), 200, "(100,200)._2");
}

/// Projection composes: a component that is ITSELF a tuple (or an entity)
/// projects again, and positional projection nests too.
#[test]
fn named_tuple_component_access_composes() {
    let src = r#"
namespace test.wi638c
  import anthill.prelude.{Int64}
  sort Box
    import anthill.prelude.{Int64}
    entity box(value: Int64)
  end
  operation nested() -> Int64
    = (a: (m: 5, n: 6), b: 7).a.n
  operation of_entity() -> Int64
    = (b: box(42), k: 1).b.value
  operation pos_nested() -> Int64
    = ((10, 20), 30)._1._2
end
"#;
    assert!(
        try_load_kb_with(src).is_ok(),
        "composed named-tuple projection must type-check; got: {:?}",
        try_load_kb_with(src).err(),
    );
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi638c.nested"), 6, "(a: (m,n), b).a.n");
    assert_eq!(run_int(&mut interp, "test.wi638c.of_entity"), 42, "(b: box(42), k).b.value");
    assert_eq!(run_int(&mut interp, "test.wi638c.pos_nested"), 20, "((10,20),30)._1._2");
}

/// Ordering-robustness (the concern behind `tuple_order_test.rs`): component
/// access is keyed by NAME, never by position within the value's `named`
/// vector, so it returns the right value even when a tuple's SOURCE order is the
/// opposite of its fields' symbol-interning order.
///
/// `zqalpha` first-occurs (is interned) in `seed`'s param — LOWER symbol index;
/// `zqzeta` first-occurs later — HIGHER index. The tuple is written
/// `(zqzeta: 1, zqalpha: 2)`: SOURCE order [zqzeta, zqalpha], the OPPOSITE of
/// index order. (`canonicalize_record_named_args` exempts a `TupleLiteral` via
/// `is_ordered_product_functor`, so source order is preserved — but even if it
/// reordered, name-keyed access would be immune.)
#[test]
fn named_tuple_component_access_is_order_independent() {
    let src = r#"
namespace test.wi638ord
  import anthill.prelude.{Int64}
  operation seed(zqalpha: Int64) -> Int64
    = zqalpha
  operation get_zeta() -> Int64
    = (zqzeta: 1, zqalpha: 2).zqzeta
  operation get_alpha() -> Int64
    = (zqzeta: 1, zqalpha: 2).zqalpha
end
"#;
    assert!(try_load_kb_with(src).is_ok(), "adversarial-order tuple must type-check");
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi638ord.get_zeta"), 1, ".zqzeta by name");
    assert_eq!(run_int(&mut interp, "test.wi638ord.get_alpha"), 2, ".zqalpha by name");
}

/// A component that the tuple does NOT declare stays a loud dot-dispatch error —
/// the new mode adds a resolution, it does not swallow genuine mismatches.
#[test]
fn absent_named_tuple_component_is_a_loud_error() {
    let src = r#"
namespace test.wi638neg
  import anthill.prelude.{Int64}
  operation bad(t: (x: Int64, y: Int64)) -> Int64
    = t.z
end
"#;
    let errs = match try_load_kb_with(src) {
        Ok(_) => panic!("projecting an absent tuple component `t.z` must NOT load"),
        Err(errs) => errs,
    };
    assert!(
        errs.iter().any(|e| e.contains("dot dispatch")),
        "absent component must surface a dot-dispatch error; got: {errs:?}",
    );
}
