//! WI-847: a `TypeMapping` written under a sort's QUALIFIED name overrides one
//! written under its SHORT name at the SAME key — the qualified-over-short
//! priority `resolve_type_mapping`'s doc promises. The WI-833 migration merged
//! every candidate spelling's hits into one list before the per-key selector,
//! which turned this working override into a loud ambiguity ERROR (two competing
//! host types at one key). This is the coverage the merge path never had: it is
//! reached ONLY from `marshal_for_type` (the sole two-spelling caller), so it
//! rides through carrier-dispatch body synthesis, not the single-spelling
//! `cpp_base_host_type` path every other WI-833 test uses.
//!
//! Two disciplines are pinned here:
//!   * a cross-spelling pair at ONE key is an OVERRIDE (qualified wins), and
//!   * the key ladder still DOMINATES the spelling order, so a binding overlay
//!     under EITHER spelling shadows a base under the other (binding > base must
//!     not invert just because the base is seen first under the qualified name).
//! A SAME-spelling pair at one key stays ambiguous — that WI-833 discipline is
//! pinned unchanged in `wi833_resolve_aggregation_test`.

use super::common;

use anthill_cpp_gen::emit_traits_struct;
use common::load_kb_with;

#[test]
fn qualified_type_mapping_overrides_short_at_the_same_key() {
    // `marshal_for_type` queries `[qualified, short]` = `["test.xspell.Vec3",
    // "Vec3"]` at binding `some("vendor")`. Two overlays sit at that ONE key:
    // one under the qualified name, one under the bare short name, with DISTINCT
    // host types and lift adapters. Pre-WI-847 the merged list held two competing
    // hits at key `some("vendor")` and selection aborted with an ambiguity error;
    // the qualified spelling must win instead (tried first, and the first spelling
    // that yields a selection is taken).
    let source = r#"
        namespace test.xspell
          import anthill.prelude.{Float, Modify}
          import anthill.realization.{Implementation, CarrierBinding, TypeMapping}

          entity Vec3(x: Float, y: Float, z: Float)

          sort Sensor
            operation get_values(self: Sensor) -> Vec3
          end

          fact Implementation(
            target:        "test.xspell.Sensor",
            artifact:      "sensor.hpp",
            language:      "cpp",
            profile:       some("cpp17-stl"),
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Sensor",
                                           host_type: "::vendor::Sensor *")],
            namespace_map: [],
            binding:       some("vendor")
          )

          -- The qualified-name overlay: the intended override.
          fact TypeMapping(
            anthill_type: "test.xspell.Vec3",
            host_type:    "const double *",
            lift:         some("QualifiedVec3::from_array"),
            lower:        none,
            lang:         some("cpp"),
            key:          some("vendor")
          )

          -- A short-name overlay at the SAME key, DISTINCT host type + adapter.
          -- Under the merge this collides with the qualified one and aborts;
          -- under qualified-over-short priority it is shadowed.
          fact TypeMapping(
            anthill_type: "Vec3",
            host_type:    "const float *",
            lift:         some("ShortVec3::from_array"),
            lower:        none,
            lang:         some("cpp"),
            key:          some("vendor")
          )
        end
    "#;
    let mut kb = load_kb_with(source);
    let traits = emit_traits_struct(&mut kb, "test.xspell.Sensor")
        .expect("qualified spelling overrides short — selection must not be ambiguous");

    // The body lifts via the QUALIFIED overlay's adapter, never the short one.
    assert!(
        traits.contains("return QualifiedVec3::from_array(self->getValues());"),
        "get_values must lift through the qualified-name overlay:\n{traits}"
    );
    assert!(
        !traits.contains("ShortVec3"),
        "the short-name overlay must be shadowed by the qualified one:\n{traits}"
    );
}

#[test]
fn binding_overlay_under_short_shadows_base_under_qualified() {
    // The key ladder must DOMINATE the spelling order. `marshal_for_type` queries
    // `[qualified, short]`, so the qualified spelling is seen FIRST — but a BASE
    // (key: none) under the qualified name must NOT preempt a BINDING overlay
    // (key: some("vendor")) under the short name: binding > base in the ladder.
    // Were selection spelling-major (first spelling with ANY hit wins), the
    // qualified base would win and the vendor overlay's adapter would be silently
    // dropped — here it lifts through the wrong host rep, and for a plain-rename
    // base marshalling would be skipped entirely (an un-adapted value that fails
    // to compile). This is the cross-KEY companion to the same-key override above.
    let source = r#"
        namespace test.xspell2
          import anthill.prelude.{Float, Modify}
          import anthill.realization.{Implementation, CarrierBinding, TypeMapping}

          entity Vec3(x: Float, y: Float, z: Float)

          sort Sensor
            operation get_values(self: Sensor) -> Vec3
          end

          fact Implementation(
            target:        "test.xspell2.Sensor",
            artifact:      "sensor.hpp",
            language:      "cpp",
            profile:       some("cpp17-stl"),
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Sensor",
                                           host_type: "::vendor::Sensor *")],
            namespace_map: [],
            binding:       some("vendor")
          )

          -- BASE mapping under the QUALIFIED name (key: none), seen first.
          fact TypeMapping(
            anthill_type: "test.xspell2.Vec3",
            host_type:    "const double *",
            lift:         some("QualifiedBase::from_array"),
            lower:        none,
            lang:         some("cpp"),
            key:          none
          )

          -- BINDING overlay under the SHORT name (key: some("vendor")).
          fact TypeMapping(
            anthill_type: "Vec3",
            host_type:    "const float *",
            lift:         some("ShortVendor::from_array"),
            lower:        none,
            lang:         some("cpp"),
            key:          some("vendor")
          )
        end
    "#;
    let mut kb = load_kb_with(source);
    let traits = emit_traits_struct(&mut kb, "test.xspell2.Sensor")
        .expect("the vendor overlay resolves — binding > base");

    // The vendor binding overlay wins over the base, regardless of spelling.
    assert!(
        traits.contains("return ShortVendor::from_array(self->getValues());"),
        "binding overlay (short) must shadow the base (qualified) — binding > base:\n{traits}"
    );
    assert!(
        !traits.contains("QualifiedBase"),
        "a base under the qualified name must not preempt the vendor overlay:\n{traits}"
    );
}
