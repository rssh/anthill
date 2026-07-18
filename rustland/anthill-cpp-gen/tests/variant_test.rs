//! Tests for `std::variant` emission from sum-typed sorts.
//! Covers nullary constructors (`enum X { entity A; entity B }`),
//! constructor entities with fields, and the include-set wiring
//! that produces `#include <variant>` in the namespace header.

use super::common;

use std::process::Command;

use anthill_cpp_gen::{emit_namespace_header, emit_sum};
use common::{find_cxx, load_kb_with, scratch_dir};

#[test]
fn nullary_sum_emits_variant_alias() {
    // The lf1 StepResult shape: enum with two zero-field variants.
    let source = r#"
        namespace test.sum_nullary
          enum StepResult
            entity Running
            entity Quit
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_sum(&mut kb, "test.sum_nullary.StepResult")
        .expect("emit StepResult sum");

    let expected = "\
struct Quit {
};

struct Running {
};

using StepResult = std::variant<Quit, Running>;
";
    assert_eq!(cpp, expected, "StepResult sum mismatch:\n{cpp}");
}

#[test]
fn sum_with_field_carrying_constructors() {
    let source = r#"
        namespace test.sum_fielded
          import anthill.prelude.{Float}
          enum Shape
            entity Circle(radius: Float)
            entity Square(side: Float)
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_sum(&mut kb, "test.sum_fielded.Shape").expect("emit Shape sum");

    assert!(cpp.contains("struct Circle {\n    double radius;\n};"),
            "Circle struct missing or wrong:\n{cpp}");
    assert!(cpp.contains("struct Square {\n    double side;\n};"),
            "Square struct missing or wrong:\n{cpp}");
    assert!(cpp.contains("using Shape = std::variant<Circle, Square>;"),
            "variant alias missing:\n{cpp}");
}

#[test]
fn missing_sum_returns_error() {
    let source = r#"
        namespace test.no_sum
          import anthill.prelude.{Float}
          entity Plain(x: Float)
        end
    "#;
    let mut kb = load_kb_with(source);
    // Plain is an entity, not a sort with constructors — emit_sum
    // should error out.
    let result = emit_sum(&mut kb, "test.no_sum.Plain");
    assert!(result.is_err(), "expected error for non-sum sort");
}

#[test]
fn namespace_header_with_sums_compiles() {
    // End-to-end: a namespace mixing flat entities and sum sorts
    // emits a header that #includes <variant> and compiles via clang.
    let source = r#"
        namespace test.mixed
          import anthill.prelude.{Float}

          entity Vec2(x: Float, y: Float)

          enum Shape
            entity Circle(radius: Float)
            entity Square(side: Float)
          end

          enum Status
            entity Ok
            entity Err
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let header = emit_namespace_header(&mut kb, "test.mixed")
        .expect("emit test.mixed header");

    // Includes set
    assert!(header.contains("#include <variant>"),
            "<variant> missing:\n{header}");
    // Vec2 (flat entity) emitted
    assert!(header.contains("struct Vec2 {"), "Vec2 missing:\n{header}");
    // Shape sum emitted
    assert!(header.contains("struct Circle {"), "Circle missing:\n{header}");
    assert!(header.contains("struct Square {"), "Square missing:\n{header}");
    assert!(header.contains("using Shape = std::variant<Circle, Square>;"),
            "Shape variant alias missing:\n{header}");
    // Status sum (zero-field constructors) emitted
    assert!(header.contains("using Status = std::variant<Err, Ok>;"),
            "Status variant alias missing:\n{header}");

    // Compile.
    let cxx = match find_cxx() {
        Some(c) => c,
        None => {
            eprintln!("no C++ compiler available — skipping sum compile check");
            return;
        }
    };
    let dir = scratch_dir("variant_mixed");
    let header_path = dir.join("mixed.hpp");
    std::fs::write(&header_path, &header).expect("write header");

    let driver = format!(
        r#"#include "{}"

int main() {{
    test::mixed::Vec2 v{{1.0, 2.0}};
    test::mixed::Shape s = test::mixed::Circle{{3.0}};
    test::mixed::Status st = test::mixed::Ok{{}};
    (void)v; (void)s; (void)st;
    return 0;
}}
"#,
        header_path.display()
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
            "header with sums failed to compile (compiler: {cxx})\n\
             ── header ───────────\n{header}\n\
             ── driver ───────────\n{driver}\n\
             ── stderr ───────────\n{stderr}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}
