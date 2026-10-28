//! WI-847 / K6WFS: a `TypeMapping` names its sort by the qualified name, and only so.
//!
//! WI-847 made a qualified-name entry override a short-name one at the same key,
//! because `marshal_for_type` looked a sort up under both spellings. K6WFS removed the
//! short spelling: an entry under `"Vec3"` answered for every sort of that name in
//! every namespace. What is pinned here is what replaced it, on the carrier-dispatch
//! path (`marshal_for_type`) the WI-847 tests rode:
//!   * an entry under a short name is REFUSED, naming it, rather than silently never
//!     matching once the lookup stopped trying that spelling; and
//!   * the key ladder still decides between two entries of the one spelling — a
//!     binding overlay shadows the base.

use super::common;

use anthill_cpp_gen::emit_traits_struct;
use common::load_kb_with;

#[test]
fn a_short_name_overlay_is_refused_not_ignored() {
    let source = r#"
        namespace test.xspell
          import anthill.prelude.{Float, Modify}
          import anthill.realization.{Implementation, CarrierBinding, TypeMapping}
          import anthill.prelude.Option.{none, some}

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
    let err = emit_traits_struct(&mut kb, "test.xspell.Sensor")
        .expect_err("a short-name entry is refused, not left unmatched");
    assert!(
        err.message.contains("TypeMapping of \"Vec3\"")
            && err.message.contains("names no sort by its qualified name"),
        "{}",
        err.message
    );
}

#[test]
fn binding_overlay_shadows_base_at_a_carrier_boundary() {
    // The key ladder decides between two entries for one sort: a BASE (key: none)
    // must not preempt a BINDING overlay (key: some("vendor")) at a dispatch into a
    // vendor-bound carrier. Were the base taken, the vendor overlay's adapter would be
    // silently dropped — here it lifts through the wrong host rep, and for a
    // plain-rename base marshalling would be skipped entirely (an un-adapted value
    // that fails to compile).
    let source = r#"
        namespace test.xspell2
          import anthill.prelude.{Float, Modify}
          import anthill.realization.{Implementation, CarrierBinding, TypeMapping}
          import anthill.prelude.Option.{none, some}

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

          -- BASE mapping (key: none).
          fact TypeMapping(
            anthill_type: "test.xspell2.Vec3",
            host_type:    "const double *",
            lift:         some("BaseVec3::from_array"),
            lower:        none,
            lang:         some("cpp"),
            key:          none
          )

          -- BINDING overlay (key: some("vendor")).
          fact TypeMapping(
            anthill_type: "test.xspell2.Vec3",
            host_type:    "const float *",
            lift:         some("VendorVec3::from_array"),
            lower:        none,
            lang:         some("cpp"),
            key:          some("vendor")
          )
        end
    "#;
    let mut kb = load_kb_with(source);
    let traits = emit_traits_struct(&mut kb, "test.xspell2.Sensor")
        .expect("the vendor overlay resolves — binding > base");

    // The vendor binding overlay wins over the base.
    assert!(
        traits.contains("return VendorVec3::from_array(self->getValues());"),
        "binding overlay must shadow the base — binding > base:\n{traits}"
    );
    assert!(
        !traits.contains("BaseVec3"),
        "the base must not preempt the vendor overlay:\n{traits}"
    );
}
