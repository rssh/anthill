//! Tests for emit_traits_struct (sort-with-operations → C++ struct
//! with static method declarations).

mod common;

use std::process::Command;

use anthill_cpp_gen::emit_traits_struct;
use common::{collect_anthill_files, find_cxx, load_kb_with, load_kb_with_extras, rustland_root, scratch_dir};

#[test]
fn simple_sort_with_two_operations() {
    // Greeter with a carrier so self-types resolve.
    let source_with_carrier = r#"
        namespace test.simple
          import anthill.prelude.{Int, Unit, String, Modify, Option}
          import anthill.realization.{Implementation, CarrierBinding}
          export Greeter

          sort Greeter
            operation greet(self: Greeter, name: String) -> Unit
              effects Modify[self]
            operation count(self: Greeter) -> Int
          end

          fact Implementation(
            target:        "test.simple.Greeter",
            artifact:      "greeter.hpp",
            language:      "cpp",
            profile:       some("cpp17-stl"),
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Greeter",
                                           host_type: "::greet::Greeter")],
            namespace_map: []
          )
        end
    "#;

    let kb2 = load_kb_with(source_with_carrier);
    let cpp2 = emit_traits_struct(&kb2, "test.simple.Greeter")
        .expect("emit Greeter (carrier)");

    // Bodies are emitted because Greeter has a carrier AND every op
    // returns a primitive. Greeter is a value carrier (no `*`), so
    // dispatch uses `.` not `->`.
    let expected = "\
struct Greeter {
    static int64_t count(::greet::Greeter self) {
        return self.count();
    }
    static void greet(::greet::Greeter self, std::string name) {
        self.greet(name);
    }
};
";
    assert_eq!(cpp2, expected, "Greeter traits struct mismatch:\n{cpp2}");
}

#[test]
fn emitted_bodies_actually_compile() {
    // Build a tiny anthill spec with a sort + carrier, emit the
    // traits struct, write it next to a hand-written stub of the
    // carrier C++ class, and invoke the compiler. This is the proof
    // that body lowering produces valid C++ — beyond textual matching.
    let source = r#"
        namespace test.bodies
          import anthill.prelude.{Int, Unit, String, Modify, Option}
          import anthill.realization.{Implementation, CarrierBinding}
          export Counter

          sort Counter
            operation increment(self: Counter) -> Unit
              effects Modify[self]
            operation reset(self: Counter) -> Unit
              effects Modify[self]
            operation value(self: Counter) -> Int
            operation set_to(self: Counter, n: Int) -> Unit
              effects Modify[self]
          end

          fact Implementation(
            target:        "test.bodies.Counter",
            artifact:      "counter.hpp",
            language:      "cpp",
            profile:       some("cpp17-stl"),
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Counter",
                                           host_type: "::demo::Counter *")],
            namespace_map: []
          )
        end
    "#;

    let kb = load_kb_with(source);
    let traits = emit_traits_struct(&kb, "test.bodies.Counter")
        .expect("emit Counter traits");

    // Bodies for all four ops (Counter is a pointer carrier, all
    // primitives). Verify the dispatch + naming.
    assert!(
        traits.contains("self->increment();"),
        "unexpected increment body:\n{traits}"
    );
    assert!(
        traits.contains("self->reset();"),
        "unexpected reset body:\n{traits}"
    );
    assert!(
        traits.contains("return self->value();"),
        "unexpected value body:\n{traits}"
    );
    assert!(
        traits.contains("self->setTo(n);"),
        "unexpected set_to body (snake→camel: setTo):\n{traits}"
    );

    // Compile.
    let cxx = match find_cxx() {
        Some(c) => c,
        None => {
            eprintln!("no C++ compiler available — skipping body compile check");
            return;
        }
    };

    let dir = std::env::temp_dir().join(format!(
        "anthill-cpp-gen-bodies-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("scratch dir");

    // The traits header references `::demo::Counter`. Provide a stub
    // header that declares it, plus the traits struct, plus a driver
    // that invokes every method.
    let driver = format!(
        r#"#include <cstdint>

namespace demo {{
struct Counter {{
    int64_t v_ = 0;
    void increment() {{ ++v_; }}
    void reset() {{ v_ = 0; }}
    int64_t value() const {{ return v_; }}
    void setTo(int64_t n) {{ v_ = n; }}
}};
}}

namespace test::bodies {{

{traits}
}}

int main() {{
    ::demo::Counter c;
    test::bodies::Counter::increment(&c);
    test::bodies::Counter::set_to(&c, 42);     // anthill snake_case at the static-method level
    auto v = test::bodies::Counter::value(&c);
    test::bodies::Counter::reset(&c);
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
            "C++ compile of generated bodies failed (compiler: {cxx})\n\
             ── driver.cpp ───────\n{driver}\n\
             ── stderr ───────────\n{stderr}"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn sort_with_no_operations_errors() {
    // A sort declaring only fields (an entity) — no operations means
    // the traits-struct emitter has nothing to emit.
    let source = r#"
        namespace test.empty_ops
          import anthill.prelude.{Float}
          export Vec3
          entity Vec3(x: Float, y: Float, z: Float)
        end
    "#;
    let kb = load_kb_with(source);
    // Vec3 is an entity, not a sort-with-ops; the emitter should error.
    let result = emit_traits_struct(&kb, "Vec3");
    assert!(result.is_err(), "expected error for entity-only Vec3");
}

#[test]
fn lf1_gps_traits_struct_emits_correctly() {
    // The actual lf1 GPS sort: 6 operations, all using primitive +
    // carrier-bound types. This exercises the realization-fact path
    // end-to-end against real project sources.
    let lf1 = rustland_root().join("examples/webots-modelling/lf1/webots");
    let kb = load_kb_with_extras("namespace test.lf1_traits end", &collect_anthill_files(&lf1));

    let cpp = emit_traits_struct(&kb, "anthill.examples.lf1.webots.GPS")
        .expect("emit GPS traits struct");

    // Operations sorted alphabetically: disable, enable, get_sampling_period,
    // get_speed, get_speed_vector, get_values.
    // self → webots::GPS * (carrier); Int → int64_t; Float → double;
    // Vec3 → Vec3 short name (no carrier — a project-local entity);
    // Unit → void.
    assert!(cpp.contains("struct GPS {"), "missing struct header:\n{cpp}");

    // Pointer carrier → `->` dispatch; primitive-return ops get
    // bodies; Vec3-return ops stay as declarations (need WI-088
    // marshalling pattern for const double * → Vec3 conversion).
    assert!(
        cpp.contains("static void disable(webots::GPS * self) {\n        self->disable();\n    }"),
        "missing disable body:\n{cpp}"
    );
    assert!(
        cpp.contains("static void enable(webots::GPS * self, int64_t sampling_period) {\n        self->enable(sampling_period);\n    }"),
        "missing enable body:\n{cpp}"
    );
    assert!(
        cpp.contains("static int64_t get_sampling_period(webots::GPS * self) {\n        return self->getSamplingPeriod();\n    }"),
        "missing get_sampling_period body:\n{cpp}"
    );
    assert!(
        cpp.contains("static double get_speed(webots::GPS * self) {\n        return self->getSpeed();\n    }"),
        "missing get_speed body:\n{cpp}"
    );
    // Vec3-returning ops: declaration only.
    assert!(
        cpp.contains("static Vec3 get_speed_vector(webots::GPS * self);"),
        "missing get_speed_vector decl:\n{cpp}"
    );
    assert!(
        cpp.contains("static Vec3 get_values(webots::GPS * self);"),
        "missing get_values decl:\n{cpp}"
    );
}
