//! When a generated header references a carrier-bound type
//! (e.g. `webots::GPS *`), the cpp-gen also emits an
//! `#include <webots/GPS.hpp>` derived from the source
//! `Implementation.artifact` field. Without this, the generated
//! header is uncompilable as it stands.

use super::common::load_kb_with;

use anthill_cpp_gen::emit_namespace_header;

#[test]
fn carrier_artifact_becomes_include_directive() {
    let source = r#"
        namespace test.car_inc.dev
          import anthill.prelude.{List, Option, String}
          import anthill.realization.{Implementation, CarrierBinding}

          sort GPS end

          fact Implementation(
            target:        "test.car_inc.dev.GPS",
            artifact:      "vendor/GPS.hpp",
            language:      "cpp",
            profile:       none,
            description:   none,
            carrier:       [CarrierBinding(sort_name: "GPS",
                                           host_type: "vendor::GPS *")],
            namespace_map: []
          )
        end

        namespace test.car_inc
          import anthill.prelude.{Int64}
          import test.car_inc.dev.{GPS}
          sort Sensors
            operation read(g: GPS) -> Int64 = 0
          end
        end
    "#;
    let kb = load_kb_with(source);
    let header = emit_namespace_header(&kb, "test.car_inc")
        .expect("emit Sensors namespace");

    assert!(
        header.contains("vendor::GPS *"),
        "header should reference the carrier host type:\n{header}"
    );
    assert!(
        header.contains("#include <vendor/GPS.hpp>"),
        "header should include the artifact declared by Implementation \
         when emitting a reference to its carrier-bound type:\n{header}"
    );
}
