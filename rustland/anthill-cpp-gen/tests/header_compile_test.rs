//! End-to-end test: emit a complete .hpp file and verify it compiles
//! via `clang++ -std=c++17 -fsyntax-only`.
//!
//! Skips with a printed warning if no C++ compiler is available — the
//! test should not fail on machines that lack one. CI must therefore
//! ensure clang++ or g++ is installed if it wants real coverage.

use super::common;

use std::process::Command;

use anthill_cpp_gen::emit_namespace_header;
use common::{find_cxx, load_kb_with, scratch_dir};

#[test]
fn namespace_header_emits_compilable_cpp() {
    let source = r#"
        namespace test.geom
          import anthill.prelude.{Float, Int64, String}
          entity Vec3(x: Float, y: Float, z: Float)
          entity Account(id: Int64, name: String)
        end
    "#;

    let kb = load_kb_with(source);
    let header = emit_namespace_header(&kb, "test.geom")
        .expect("emit test.geom header");

    // Sanity-check the structure before invoking the compiler.
    assert!(header.contains("#pragma once"), "missing #pragma once:\n{header}");
    assert!(header.contains("#include <cstdint>"),
            "missing <cstdint> for int64_t:\n{header}");
    assert!(header.contains("#include <string>"),
            "missing <string> for std::string:\n{header}");
    assert!(header.contains("namespace test::geom {"),
            "missing namespace open:\n{header}");
    assert!(header.contains("}  // namespace test::geom"),
            "missing namespace close comment:\n{header}");
    assert!(header.contains("struct Vec3"), "missing Vec3:\n{header}");
    assert!(header.contains("struct Account"), "missing Account:\n{header}");

    // Now actually compile it.
    let cxx = match find_cxx() {
        Some(c) => c,
        None => {
            eprintln!("no C++ compiler available — skipping compile check");
            return;
        }
    };

    let dir = scratch_dir("namespace_header");
    let header_path = dir.join("test_geom.hpp");
    std::fs::write(&header_path, &header).expect("write header");

    // Driver source: include the header, instantiate one of each
    // emitted struct via designated initializers (C++20) — but we
    // target C++17, so use brace-init in declaration order. This
    // also exercises the field-order convention.
    let driver = format!(
        r#"#include "{}"

int main() {{
    test::geom::Vec3 v{{1.0, 2.0, 3.0}};
    test::geom::Account a{{42, std::string("alice")}};
    (void)v;
    (void)a;
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
        let stdout = String::from_utf8_lossy(&output.stdout);
        panic!(
            "C++ compile failed (compiler: {cxx})\n\
             ── header.hpp ───────────────────────\n{header}\n\
             ── driver.cpp ───────────────────────\n{driver}\n\
             ── stderr ───────────────────────────\n{stderr}\n\
             ── stdout ───────────────────────────\n{stdout}"
        );
    }

    // Best-effort cleanup; ignore errors.
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn missing_namespace_returns_error() {
    let kb = load_kb_with(r#"
        namespace test.empty
          import anthill.prelude.{Float}
        end
    "#);
    let result = emit_namespace_header(&kb, "test.empty");
    assert!(result.is_err(), "expected error for empty namespace");
}
