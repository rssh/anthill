//! WI-644 (final acceptance) — USE-SITE `requires Eq` enforcement: a parametric
//! sort with a `requires Eq[K]` clause (`Map`, `Set`) instantiated in an entity
//! field type over a carrier that provides `NonEq` (IEEE `Float`, or a
//! Float-containing composite via WI-664) is a LOAD ERROR — a raw `Float` key is
//! not lawful (`nan != nan`), so `Map[K = Float]` is rejected rather than silently
//! misdeciding. `Map[K = TotalFloat]` / `Map[K = Int64]` / a lawful composite key
//! load. This closes proposal 004's "`Map[K = Float]` is a load error, `Map[K =
//! TotalFloat]` loads" acceptance.

/// The field type in error must be reported with the `NonEq` lawful-key diagnostic.
fn assert_nonEq_key_error(errs: &[String], container: &str, carrier: &str) {
    assert!(
        errs.iter().any(|e| {
            e.contains("lawful") && e.contains("Eq") && e.contains(container) && e.contains(carrier)
        }),
        "expected a `{container}` requires-lawful-Eq error naming `{carrier}`; got:\n{}",
        errs.join("\n"),
    );
}

fn assert_loads_clean(src: &str) {
    if let Err(errs) = crate::common::try_load_kb_with(src) {
        panic!("expected a clean load; got errors:\n{}", errs.join("\n"));
    }
}

// ── The load errors: a Float (NonEq) key ────────────────────────────────────

#[test]
fn map_with_float_key_is_a_load_error() {
    let src = r#"
namespace test.wi644.mapfloat
  import anthill.prelude.{Map, Float, Int64}
  sort Holder
    entity holder(m: Map[K = Float, V = Int64])
  end
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert_nonEq_key_error(&errs, "Map", "Float");
}

#[test]
fn set_with_float_element_is_a_load_error() {
    let src = r#"
namespace test.wi644.setfloat
  import anthill.prelude.{Set, Float}
  sort Holder
    entity holder(s: Set[T = Float])
  end
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert_nonEq_key_error(&errs, "Set", "Float");
}

/// WI-664 integration: a Float-CONTAINING composite derives `NonEq`, so it is also
/// not a lawful key — `Map[K = <Float composite>]` is rejected too.
#[test]
fn map_with_float_composite_key_is_a_load_error() {
    let src = r#"
namespace test.wi644.mapcomposite
  import anthill.prelude.{Map, Float, Int64}
  sort Pt
    entity pt(x: Float, y: Float)
  end
  sort Holder
    entity holder(m: Map[K = Pt, V = Int64])
  end
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert_nonEq_key_error(&errs, "Map", "Pt");
}

// ── The clean loads: lawful keys ────────────────────────────────────────────

/// `Map[K = TotalFloat]` loads — TotalFloat provides lawful (structural) `Eq`. The
/// proposal's named escape hatch for "floats as keys".
#[test]
fn map_with_totalfloat_key_loads() {
    assert_loads_clean(r#"
namespace test.wi644.maptf
  import anthill.prelude.{Map, TotalFloat, Int64}
  sort Holder
    entity holder(m: Map[K = TotalFloat, V = Int64])
  end
end
"#);
}

/// A lawful primitive key loads.
#[test]
fn map_with_int_key_loads() {
    assert_loads_clean(r#"
namespace test.wi644.mapint
  import anthill.prelude.{Map, Int64, String}
  sort Holder
    entity holder(m: Map[K = Int64, V = String])
  end
end
"#);
}

/// An ALL-`Eq` composite key loads — it is lawfully `Eq` (WI-664 does not derive
/// `NonEq` for it), so the negative check does not fire (it would over-reject under
/// a positive "must provide Eq" check, since no `Eq` fact is derived for it).
#[test]
fn map_with_all_eq_composite_key_loads() {
    assert_loads_clean(r#"
namespace test.wi644.mapokcomposite
  import anthill.prelude.{Map, Int64}
  sort Q
    entity q(a: Int64, b: Int64)
  end
  sort Holder
    entity holder(m: Map[K = Q, V = Int64])
  end
end
"#);
}

/// An ABSTRACT key binding (a parametric holder whose own param is the map key)
/// loads — the binding is not a concrete carrier, so the check defers (it must not
/// fire on a type-param).
#[test]
fn map_over_abstract_param_key_loads() {
    assert_loads_clean(r#"
namespace test.wi644.mapabstract
  import anthill.prelude.{Map, Int64}
  sort Holder
    sort K = ?
    entity holder(m: Map[K = K, V = Int64])
  end
end
"#);
}
