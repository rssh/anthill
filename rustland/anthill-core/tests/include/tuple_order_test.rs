//! Named tuples are ordered products — the VALUE representation must preserve
//! source field order (sorting fields would collapse a tuple into a record).
//!
//! `finish_constructor` runs a constructor's named args through
//! `canonicalize_record_named_args`, which EXEMPTS ordered products: a
//! `TupleLiteral` is caught by `is_ordered_product_functor` and returned
//! untouched, so source order is preserved by an explicit contract. Today the
//! same order also survives the record path (a `TupleLiteral`'s EMPTY field
//! schema, `Some([])`, sends every field to `usize::MAX` under a STABLE
//! `sort_by_key`), so this test asserts the OUTCOME — source order — under
//! adverse symbol-interning order. The explicit exemption is what keeps that
//! outcome robust: were `TupleLiteral` to gain a non-empty schema (→ reorder by
//! declared order) or the fallback sort to become unstable, a tuple reaching the
//! record path would silently reorder; the exemption forecloses both.

use anthill_core::eval::{Interpreter, Value};
use crate::common::load_kb_with;

#[test]
fn named_tuple_value_preserves_source_field_order() {
    // Distinctive field names the prelude will not have pre-interned. `zqalpha`
    // first-occurs in `seed`'s parameter (interned FIRST); `zqzeta` first-occurs
    // in `pair` (interned SECOND) — so zqalpha.index() < zqzeta.index(). The
    // tuple is written `(zqzeta: x, zqalpha: 2)` — SOURCE order [zqzeta, zqalpha],
    // the OPPOSITE of index order. A parameter blocks load-time const folding, so
    // the tuple is built at runtime through `finish_constructor`.
    let src = r#"
namespace test.tuple_order
  import anthill.prelude.{Int64}
  operation seed(zqalpha: Int64) -> Int64
    = zqalpha
  operation pair(x: Int64) -> (zqzeta: Int64, zqalpha: Int64)
    = (zqzeta: x, zqalpha: 2)
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let v = interp
        .call("test.tuple_order.pair", &[Value::Int(1)])
        .expect("call pair");
    match v {
        Value::Tuple { named, .. } => {
            let shape: Vec<(&str, i64)> = named
                .iter()
                .map(|(s, val)| (interp.kb().resolve_sym(*s), val.as_int().expect("int field")))
                .collect();
            // source order is (zqzeta: 1, zqalpha: 2)
            assert_eq!(
                shape,
                vec![("zqzeta", 1), ("zqalpha", 2)],
                "tuple field order corrupted (reordered by symbol index?): got {shape:?}"
            );
        }
        other => panic!("expected Value::Tuple, got {other:?}"),
    }
}
