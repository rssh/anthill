//! Smoke test against the actual lf1 spec files.
//! Verifies the codegen handles real project sources, not just inline ones.

use super::common;

use std::process::Command;

use anthill_cpp_gen::{emit_entity_struct, emit_namespace_header};
use common::{collect_anthill_files, find_cxx, load_kb_with_extras, rustland_root, scratch_dir};

#[test]
fn lf1_vec3_and_euler_emit_correctly() {
    let lf1_webots = rustland_root().join("examples/webots-modelling/lf1/webots");
    let lf1_files = collect_anthill_files(&lf1_webots);
    assert!(!lf1_files.is_empty(), "expected lf1 webots sources");

    // Empty user source — lf1 binding files come in via extras.
    let kb = load_kb_with_extras("namespace test.lf1_smoke end", &lf1_files);

    let cpp = emit_entity_struct(&kb, "Vec3").expect("emit Vec3");
    let expected = "\
struct Vec3 {
    double x;
    double y;
    double z;
};
";
    assert_eq!(cpp, expected, "lf1 Vec3 mismatch:\n{cpp}");

    // EulerAngles exercises declaration-order emission: roll/pitch/yaw
    // is the C++ field order, distinct from alphabetical pitch/roll/yaw.
    let cpp_euler = emit_entity_struct(&kb, "EulerAngles").expect("emit EulerAngles");
    let expected_euler = "\
struct EulerAngles {
    double roll;
    double pitch;
    double yaw;
};
";
    assert_eq!(cpp_euler, expected_euler, "lf1 EulerAngles mismatch:\n{cpp_euler}");
}

#[test]
fn lf1_types_namespace_emits_compilable_header() {
    // Vec3 / EulerAngles now live in `anthill.geometry` (shared
    // stdlib). Emit the whole namespace as a single .hpp and compile
    // it — the lf1 webots binding files re-target their imports here
    // instead of carrying a project-local copy.
    let lf1_webots = rustland_root().join("examples/webots-modelling/lf1/webots");
    let lf1_files = collect_anthill_files(&lf1_webots);
    let kb = load_kb_with_extras("namespace test.lf1_smoke end", &lf1_files);

    let header = emit_namespace_header(&kb, "anthill.geometry")
        .expect("emit anthill.geometry header");

    assert!(header.contains("namespace anthill::geometry {"));
    assert!(header.contains("struct Vec3"));
    assert!(header.contains("struct EulerAngles"));

    let cxx = match find_cxx() {
        Some(c) => c,
        None => {
            eprintln!("no C++ compiler available — skipping lf1 compile check");
            return;
        }
    };

    let dir = scratch_dir("lf1_types");
    let header_path = dir.join("geometry.hpp");
    std::fs::write(&header_path, &header).expect("write header");

    let driver = format!(
        r#"#include "{}"

int main() {{
    anthill::geometry::Vec3 v{{1.0, 2.0, 3.0}};
    anthill::geometry::EulerAngles e{{0.0, 0.0, 0.0}};
    (void)v; (void)e;
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
        "anthill.geometry header failed to compile (compiler: {cxx})\n\
         ── header ───────────\n{header}\n\
         ── stderr ───────────\n{}",
        String::from_utf8_lossy(&output.stderr),
    );

    let _ = std::fs::remove_dir_all(&dir);
}
