//! Tests for marshalled-`TypeMapping`-driven body wrapping (WI-088 / WI-089(a)).
//!
//! A top-level `fact TypeMapping(anthill_type, host_type, lift, lower, lang,
//! key)` that carries an adapter declares that the host represents
//! `anthill_type` as `host_type`, with `lift` (foreign->anthill) and/or
//! `lower` (anthill->foreign) bridging the boundary. The overlay is keyed
//! `key: some("<binding>")` and selected only when dispatching onto a carrier
//! whose `Implementation` declares the matching `binding` (WI-089(a)): the
//! binding key is prepended to the active-key list at the boundary, so the
//! overlay shadows the language base there and stays invisible in declared-
//! signature position. At a carrier-dispatch site body synthesis derives the
//! host method's foreign signature by mapping the operation's anthill types
//! through these entries and emits:
//!   - `return <lift>(self->method(args));`  when the return is marshalled
//!   - `self->method(<lower>(arg))`          when an argument is marshalled
//! The adapters are hand-authored C++ shipped alongside the generated code.

use super::common;

use std::process::Command;

use anthill_cpp_gen::emit_traits_struct;
use common::{find_cxx, load_kb_with, scratch_dir};

#[test]
fn marshalled_lift_wraps_carrier_return() {
    // GPS-like sort: get_values returns a project-local Vec3, the C++
    // side returns const double *. The marshalled TypeMapping for Vec3
    // (lift = Vec3::from_array) makes body synthesis wrap the carrier
    // call. Without it, the Vec3 return would be decl-only.
    let source = r#"
        namespace test.conv
          import anthill.prelude.{Float, Int64, Unit, Modify}
          import anthill.realization.{Implementation, CarrierBinding, TypeMapping}

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
            namespace_map: [],
            binding:       some("vendor")
          )

          fact TypeMapping(
            anthill_type: "test.conv.Vec3",
            host_type:    "const double *",
            lift:         some("Vec3::from_array"),
            lower:        none,
            lang:         some("cpp"),
            key:          some("vendor")
          )
        end
    "#;
    let kb = load_kb_with(source);
    let traits = emit_traits_struct(&kb, "test.conv.Sensor")
        .expect("emit Sensor traits");

    // get_values: body lifts the carrier call via Vec3::from_array.
    assert!(
        traits.contains("static Vec3 get_values(::vendor::Sensor * self) {\n        return Vec3::from_array(self->getValues());\n    }"),
        "get_values body should lift the carrier return:\n{traits}"
    );

    // reset: no marshalled type involved; primitive (void) return →
    // existing direct-dispatch body, unchanged.
    assert!(
        traits.contains("static void reset(::vendor::Sensor * self) {\n        self->reset();\n    }"),
        "reset body unchanged:\n{traits}"
    );
}

#[test]
fn marshalled_lower_wraps_carrier_argument() {
    // The opposite direction: a setter takes a Vec3 the host wants as
    // `const double *`. The marshalled TypeMapping's `lower` adapter
    // (Vec3::to_array) wraps the argument before it is passed into the
    // carrier call. Exercises the input direction, which has no lf1
    // consumer yet but is the bidirectional half of the mechanism.
    let source = r#"
        namespace test.lower
          import anthill.prelude.{Float, Unit, Modify}
          import anthill.realization.{Implementation, CarrierBinding, TypeMapping}

          entity Vec3(x: Float, y: Float, z: Float)

          sort Actuator
            operation set_target(self: Actuator, target: Vec3) -> Unit
              effects Modify[self]
          end

          fact Implementation(
            target:        "test.lower.Actuator",
            artifact:      "actuator.hpp",
            language:      "cpp",
            profile:       some("cpp17-stl"),
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Actuator",
                                           host_type: "::vendor::Actuator *")],
            namespace_map: [],
            binding:       some("vendor")
          )

          fact TypeMapping(
            anthill_type: "test.lower.Vec3",
            host_type:    "const double *",
            lift:         some("Vec3::from_array"),
            lower:        some("Vec3::to_array"),
            lang:         some("cpp"),
            key:          some("vendor")
          )
        end
    "#;
    let kb = load_kb_with(source);
    let traits = emit_traits_struct(&kb, "test.lower.Actuator")
        .expect("emit Actuator traits");

    // set_target: the Vec3 argument is lowered via Vec3::to_array
    // before being handed to the carrier method.
    assert!(
        traits.contains("self->setTarget(Vec3::to_array(target));"),
        "set_target body should lower the Vec3 argument:\n{traits}"
    );
}

#[test]
fn marshalled_argument_without_lower_is_loud() {
    // A type that is marshalled (host wants the foreign rep) but whose
    // TypeMapping declares only `lift`, no `lower`, cannot be bridged on
    // the input direction. Passing such a value as an argument must
    // surface a loud TODO rather than silently emitting an un-lowered
    // argument that won't compile.
    let source = r#"
        namespace test.nolower
          import anthill.prelude.{Float, Unit, Modify}
          import anthill.realization.{Implementation, CarrierBinding, TypeMapping}

          entity Vec3(x: Float, y: Float, z: Float)

          sort Actuator
            operation set_orient(self: Actuator, e: Vec3) -> Unit
              effects Modify[self]
          end

          fact Implementation(
            target:        "test.nolower.Actuator",
            artifact:      "actuator.hpp",
            language:      "cpp",
            profile:       some("cpp17-stl"),
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Actuator",
                                           host_type: "::vendor::Actuator *")],
            namespace_map: [],
            binding:       some("vendor")
          )

          fact TypeMapping(
            anthill_type: "test.nolower.Vec3",
            host_type:    "const double *",
            lift:         some("Vec3::from_array"),
            lower:        none,
            lang:         some("cpp"),
            key:          some("vendor")
          )
        end
    "#;
    let kb = load_kb_with(source);
    let traits = emit_traits_struct(&kb, "test.nolower.Actuator")
        .expect("emit Actuator traits");

    // The body must carry the loud TODO naming the offending parameter,
    // and must NOT pass the bare `e` argument into the call.
    assert!(
        traits.contains("// TODO: WI-088: parameter 'e' has a marshalled type with no `lower` adapter"),
        "set_orient should surface a loud TODO for the unlowerable argument:\n{traits}"
    );
    assert!(
        !traits.contains("self->setOrient(e)"),
        "set_orient must not emit the un-lowered bare argument:\n{traits}"
    );
}

#[test]
fn no_marshal_fact_keeps_decl_only_for_entity_returns() {
    // Same shape minus the marshalled TypeMapping — the Vec3 return is
    // a project-local entity codegen can't bridge, so it stays
    // declaration-only.
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
        "without a marshalled TypeMapping, get_values should be decl-only:\n{traits}"
    );
}

#[test]
fn marshalled_lift_body_compiles() {
    // End-to-end: emit a Sensor with a get_values that lifts
    // ::vendor::Sensor::getValues (returns const double *) into a Vec3
    // via a hand-written Vec3::from_array.
    let source = r#"
        namespace test.conv_compile
          import anthill.prelude.{Float, Modify}
          import anthill.realization.{Implementation, CarrierBinding, TypeMapping}

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
            namespace_map: [],
            binding:       some("vendor")
          )

          fact TypeMapping(
            anthill_type: "test.conv_compile.Vec3",
            host_type:    "const double *",
            lift:         some("Vec3::from_array"),
            lower:        none,
            lang:         some("cpp"),
            key:          some("vendor")
          )
        end
    "#;
    let kb = load_kb_with(source);
    let traits = emit_traits_struct(&kb, "test.conv_compile.Sensor")
        .expect("emit Sensor traits");

    let cxx = match find_cxx() {
        Some(c) => c,
        None => {
            eprintln!("no C++ compiler available — skipping marshalled compile check");
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
            "marshalled-lift body failed to compile (compiler: {cxx})\n\
             ── traits ───────────\n{traits}\n\
             ── driver ───────────\n{driver}\n\
             ── stderr ───────────\n{stderr}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}
