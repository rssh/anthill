//! `emit_runtime_header()` returns the static `anthill_runtime.hpp`
//! support file. This test compiles the header and verifies the
//! SFINAE traits return true for `std::vector<int>` (IndexedSeq) and
//! correctly reject types that don't satisfy a given spec.

use super::common;

use std::process::Command;

use anthill_cpp_gen::emit_runtime_header;
use common::{find_cxx, scratch_dir};

#[test]
fn runtime_header_is_non_empty_and_namespaced() {
    let header = emit_runtime_header();
    assert!(header.contains("namespace anthill::runtime {"),
            "header should declare the runtime namespace");
    assert!(header.contains("satisfies_indexed_seq_v"),
            "IndexedSeq trait missing");
    assert!(header.contains("satisfies_eq_v"), "Eq trait missing");
    assert!(header.contains("satisfies_ordered_v"), "Ordered trait missing");
    assert!(header.contains("satisfies_numeric_v"), "Numeric trait missing");
}

#[test]
fn runtime_header_compiles_and_traits_behave() {
    let cxx = match find_cxx() {
        Some(c) => c,
        None => {
            eprintln!("no C++ compiler — skipping runtime header compile check");
            return;
        }
    };

    let dir = scratch_dir("runtime_header");
    let header_path = dir.join("anthill_runtime.hpp");
    std::fs::write(&header_path, emit_runtime_header()).expect("write header");

    // Driver exercises every trait against types that should match
    // and types that should not. Each assertion is a static_assert
    // so a mismatch fails the compile, not a runtime check.
    let driver = r#"
#include <vector>
#include <array>
#include <string>
#include <set>
#include "anthill_runtime.hpp"

struct Plain {};

// Eq: vector and string compare; Plain doesn't.
static_assert( anthill::runtime::satisfies_eq_v<int>);
static_assert( anthill::runtime::satisfies_eq_v<std::string>);
static_assert(!anthill::runtime::satisfies_eq_v<Plain>);

// Ordered: int and string have <; Plain doesn't.
static_assert( anthill::runtime::satisfies_ordered_v<int>);
static_assert( anthill::runtime::satisfies_ordered_v<std::string>);
static_assert(!anthill::runtime::satisfies_ordered_v<Plain>);

// Numeric: int has +/-/*; string supports + only (concatenation),
// so it must NOT pass numeric (no `-`/`*`).
static_assert( anthill::runtime::satisfies_numeric_v<int>);
static_assert( anthill::runtime::satisfies_numeric_v<double>);
static_assert(!anthill::runtime::satisfies_numeric_v<std::string>);

// IndexedSeq: vector and array support .size() + [].
// std::set has size() but no operator[size_t], so it must NOT pass.
static_assert( anthill::runtime::satisfies_indexed_seq_v<std::vector<int>>);
static_assert( anthill::runtime::satisfies_indexed_seq_v<std::array<int, 4>>);
static_assert(!anthill::runtime::satisfies_indexed_seq_v<std::set<int>>);

int main() { return 0; }
"#;
    let driver_path = dir.join("driver.cpp");
    std::fs::write(&driver_path, driver).expect("write driver");

    let output = Command::new(cxx)
        .args(["-std=c++17", "-fsyntax-only", "-Wall", "-Wextra"])
        .arg(&driver_path)
        .output()
        .expect("invoke compiler");

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        panic!(
            "runtime header compile / static_assert failed (compiler: {cxx})\n\
             ── header ───────────\n{}\n\
             ── driver ───────────\n{driver}\n\
             ── stderr ───────────\n{stderr}",
            emit_runtime_header()
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}
