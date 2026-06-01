//! Tests for parameterized type lowering: `List[T = X]` →
//! `std::vector<X>`, `Option[T = X]` → `std::optional<X>`, etc.,
//! including nested parameterizations and the implied
//! `<vector>` / `<optional>` includes in emitted headers.

use super::common;

use std::process::Command;

use anthill_cpp_gen::{emit_entity_struct, emit_namespace_header};
use common::{find_cxx, load_kb_with, scratch_dir};

#[test]
fn entity_with_list_field() {
    let source = r#"
        namespace test.params
          import anthill.prelude.{Float, List}
          export Polyline
          entity Polyline(points: List[T = Float])
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_entity_struct(&kb, "test.params.Polyline").expect("emit Polyline");
    let expected = "\
struct Polyline {
    std::vector<double> points;
};
";
    assert_eq!(cpp, expected, "Polyline mismatch:\n{cpp}");
}

#[test]
fn entity_with_option_field() {
    let source = r#"
        namespace test.params
          import anthill.prelude.{Int, String, Option}
          export User
          entity User(name: String, age: Option[T = Int])
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_entity_struct(&kb, "test.params.User").expect("emit User");
    let expected = "\
struct User {
    std::string name;
    std::optional<int64_t> age;
};
";
    assert_eq!(cpp, expected, "User mismatch:\n{cpp}");
}

#[test]
fn two_param_field_lowers_in_declaration_order() {
    // WI-361 regression guard: term-backed parameterized bindings are stored in
    // canonical symbol-interning order, NOT declaration order, so cpp-gen must
    // emit C++ template args in the sort's DECLARED param order. A 2-param sort
    // `Pair { sort Z = ?; sort A = ? }` mapped to `std::pair` must lower
    // `Pair[Z = Int, A = String]` as `std::pair<int64_t, std::string>` (Z first),
    // regardless of how Z/A intern. Pre-fix this emitted the args swapped.
    let source = r#"
        namespace test.params
          import anthill.prelude.{Int, String}
          export Pair, Holder
          sort Pair
            sort Z = ?
            sort A = ?
          end
          entity Holder(p: Pair[Z = Int, A = String])
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_entity_struct(&kb, "test.params.Holder").expect("emit Holder");
    assert!(
        cpp.contains("std::pair<int64_t, std::string>"),
        "2-param type must lower in declaration order (Z=Int then A=String); got:\n{cpp}"
    );
}

#[test]
fn nested_parameterization() {
    // Option[T = List[T = Float]] → std::optional<std::vector<double>>
    let source = r#"
        namespace test.params
          import anthill.prelude.{Float, List, Option}
          export OptionalSamples
          entity OptionalSamples(samples: Option[T = List[T = Float]])
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_entity_struct(&kb, "test.params.OptionalSamples")
        .expect("emit OptionalSamples");
    assert!(
        cpp.contains("std::optional<std::vector<double>> samples"),
        "expected nested optional<vector<double>>:\n{cpp}"
    );
}

#[test]
fn namespace_header_with_parameterized_emits_includes() {
    // The header must add `<vector>` and `<optional>` to its include
    // block when the emitted entities use those types — and remain
    // compilable.
    let source = r#"
        namespace test.params
          import anthill.prelude.{Float, Int, String, List, Option}
          export Polyline, User

          entity Polyline(points: List[T = Float])
          entity User(name: String, age: Option[T = Int])
        end
    "#;
    let kb = load_kb_with(source);
    let header = emit_namespace_header(&kb, "test.params")
        .expect("emit test.params header");

    assert!(header.contains("#include <cstdint>"), "<cstdint> missing:\n{header}");
    assert!(header.contains("#include <string>"),  "<string> missing:\n{header}");
    assert!(header.contains("#include <vector>"),  "<vector> missing:\n{header}");
    assert!(header.contains("#include <optional>"),"<optional> missing:\n{header}");
    assert!(header.contains("namespace test::params {"), "namespace missing:\n{header}");

    // Compile if a compiler is available.
    let cxx = match find_cxx() {
        Some(c) => c,
        None => {
            eprintln!("no C++ compiler available — skipping parameterized compile check");
            return;
        }
    };
    let dir = scratch_dir("parameterized");
    let header_path = dir.join("params.hpp");
    std::fs::write(&header_path, &header).expect("write header");

    let driver = format!(
        r#"#include "{}"

int main() {{
    test::params::Polyline poly{{{{1.0, 2.0, 3.0}}}};
    test::params::User u{{"alice", 42}};
    (void)poly; (void)u;
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

    assert!(
        output.status.success(),
        "parameterized header failed to compile (compiler: {cxx})\n\
         ── header ───────────\n{header}\n\
         ── driver ───────────\n{driver}\n\
         ── stderr ───────────\n{}",
        String::from_utf8_lossy(&output.stderr),
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn carrier_overrides_parameterized_default() {
    // A CarrierBinding on List itself overrides the default
    // `std::vector` template choice.
    let source = r#"
        namespace test.params
          import anthill.prelude.{Float, List, Option}
          import anthill.realization.{Implementation, CarrierBinding}
          export Polyline

          entity Polyline(points: List[T = Float])

          fact Implementation(
            target:        "anthill.prelude.List",
            artifact:      "small_vec.hpp",
            language:      "cpp",
            profile:       some("cpp17-stl"),
            description:   none,
            carrier:       [CarrierBinding(sort_name: "List",
                                           host_type: "::small::Vec")],
            namespace_map: []
          )
        end
    "#;
    let kb = load_kb_with(source);
    let cpp = emit_entity_struct(&kb, "test.params.Polyline").expect("emit Polyline");
    assert!(
        cpp.contains("::small::Vec<double> points"),
        "carrier override should produce ::small::Vec<double>:\n{cpp}"
    );
}
