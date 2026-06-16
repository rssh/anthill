//! Tests for `ReturnTypeConversion`-driven body wrapping.
//!
//! When a `fact ReturnTypeConversion(target, operation, conversion)`
//! is asserted, body synthesis emits
//!   `return <conversion>(self->{cppMethod}(args));`
//! regardless of whether the return type would otherwise have been
//! body-emittable. The conversion is a hand-authored C++ function
//! shipped alongside the generated code.

use super::common;

use std::process::Command;

use anthill_cpp_gen::emit_traits_struct;
use common::{find_cxx, load_kb_with, scratch_dir};

#[test]
fn return_type_conversion_wraps_carrier_call() {
    // GPS-like sort: get_values returns a project-local Vec3, the
    // C++ side returns const double *. Without the conversion fact,
    // body would be skipped (Vec3 is project-local). With it, body
    // wraps the call in Vec3::from_array.
    let source = r#"
        namespace test.conv
          import anthill.prelude.{Float, Int64, Unit, Modify}
          import anthill.realization.{Implementation, CarrierBinding}
          import anthill.realization.cpp_std.{ReturnTypeConversion}

          entity Vec3(x: Float, y: Float, z: Float)

          sort Sensor
            operation get_values(self: Sensor) -> Vec3
            operation reset(self: Sensor) -> Unit
              effects Modify[self]
          end

          fact Implementation(
            target:        "test.conv.Sensor",
            artifact:      "sensor.hpp",
            language:      "cpp",
            profile:       some("cpp17-stl"),
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Sensor",
                                           host_type: "::vendor::Sensor *")],
            namespace_map: []
          )

          fact ReturnTypeConversion(
            target:     "test.conv.Sensor",
            operation:  "get_values",
            conversion: "Vec3::from_array"
          )
        end
    "#;
    let kb = load_kb_with(source);
    let traits = emit_traits_struct(&kb, "test.conv.Sensor")
        .expect("emit Sensor traits");

    // get_values: body wraps the carrier call in Vec3::from_array.
    assert!(
        traits.contains("static Vec3 get_values(::vendor::Sensor * self) {\n        return Vec3::from_array(self->getValues());\n    }"),
        "get_values body should use the conversion:\n{traits}"
    );

    // reset: no conversion fact; primitive (void) return → existing
    // direct-dispatch body.
    assert!(
        traits.contains("static void reset(::vendor::Sensor * self) {\n        self->reset();\n    }"),
        "reset body unchanged:\n{traits}"
    );
}

#[test]
fn no_conversion_fact_keeps_decl_only_for_entity_returns() {
    // Same shape minus the ReturnTypeConversion — Vec3 return stays
    // declaration-only (current behaviour).
    let source = r#"
        namespace test.no_conv
          import anthill.prelude.{Float, Modify}
          import anthill.realization.{Implementation, CarrierBinding}

          entity Vec3(x: Float, y: Float, z: Float)

          sort Sensor
            operation get_values(self: Sensor) -> Vec3
          end

          fact Implementation(
            target:        "test.no_conv.Sensor",
            artifact:      "sensor.hpp",
            language:      "cpp",
            profile:       some("cpp17-stl"),
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Sensor",
                                           host_type: "::vendor::Sensor *")],
            namespace_map: []
          )
        end
    "#;
    let kb = load_kb_with(source);
    let traits = emit_traits_struct(&kb, "test.no_conv.Sensor")
        .expect("emit Sensor traits");
    assert!(
        traits.contains("static Vec3 get_values(::vendor::Sensor * self);"),
        "without conversion fact, get_values should be decl-only:\n{traits}"
    );
}

#[test]
fn conversion_wrapped_body_compiles() {
    // End-to-end: emit a Sensor with a get_values that wraps
    // ::vendor::Sensor::getValues (returns const double *) into
    // a Vec3 via a hand-written Vec3::from_array.
    let source = r#"
        namespace test.conv_compile
          import anthill.prelude.{Float, Modify}
          import anthill.realization.{Implementation, CarrierBinding}
          import anthill.realization.cpp_std.{ReturnTypeConversion}

          entity Vec3(x: Float, y: Float, z: Float)

          sort Sensor
            operation get_values(self: Sensor) -> Vec3
          end

          fact Implementation(
            target:        "test.conv_compile.Sensor",
            artifact:      "sensor.hpp",
            language:      "cpp",
            profile:       some("cpp17-stl"),
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Sensor",
                                           host_type: "::vendor::Sensor *")],
            namespace_map: []
          )

          fact ReturnTypeConversion(
            target:     "test.conv_compile.Sensor",
            operation:  "get_values",
            conversion: "Vec3::from_array"
          )
        end
    "#;
    let kb = load_kb_with(source);
    let traits = emit_traits_struct(&kb, "test.conv_compile.Sensor")
        .expect("emit Sensor traits");

    let cxx = match find_cxx() {
        Some(c) => c,
        None => {
            eprintln!("no C++ compiler available — skipping conversion compile check");
            return;
        }
    };
    let dir = scratch_dir("conversion");
    let driver = format!(
        r#"namespace vendor {{
struct Sensor {{
    double buf[3] = {{1.0, 2.0, 3.0}};
    const double * getValues() {{ return buf; }}
}};
}}

namespace test::conv_compile {{

struct Vec3 {{
    double x, y, z;
    static Vec3 from_array(const double * raw) {{
        return Vec3{{raw[0], raw[1], raw[2]}};
    }}
}};

{traits}
}}

int main() {{
    ::vendor::Sensor s;
    auto v = test::conv_compile::Sensor::get_values(&s);
    (void)v;
    return 0;
}}
"#
    );
    let driver_path = dir.join("driver.cpp");
    std::fs::write(&driver_path, &driver).expect("write driver");

    let output = Command::new(cxx)
        .args(["-std=c++17", "-fsyntax-only", "-Wall", "-Wextra"])
        .arg(&driver_path)
        .output()
        .expect("invoke compiler");

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        panic!(
            "conversion-wrapped body failed to compile (compiler: {cxx})\n\
             ── traits ───────────\n{traits}\n\
             ── driver ───────────\n{driver}\n\
             ── stderr ───────────\n{stderr}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}
