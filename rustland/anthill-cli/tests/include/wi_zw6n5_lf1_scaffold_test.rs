//! WI-20260823-ZW6N5: lf1's CODEGEN track — `examples/webots-modelling/lf1/build.sh`
//! → `anthill codegen cpp-project` — must scaffold a tree that compiles.
//!
//! It sat broken from April to August with nothing noticing: the spec was split
//! into per-controller namespaces (`lf1.leader`, `lf1.follower_gps`, …), while
//! cpp-project still emitted ONE header, for the `--namespace` umbrella, which now
//! declared nothing. Only the proof track had a test. Each controller now gets the
//! header of the namespace declaring it plus every header that one includes
//! (`emit_namespace_header_closure`), under the names those `#include`s spell.
//!
//! The shims are compiled against STUB Webots headers written below, not a Webots
//! install: what can rot here is the agreement between the generated headers and
//! the hand-written shims, and that needs only the declarations `mavic_base.hpp`
//! uses. The real `make` against `libController` is the README's manual step.

use crate::common::{anthill, Output};
use std::path::{Path, PathBuf};
use std::process::Command;

fn lf1_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/webots-modelling/lf1")
}

fn scratch(test: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("anthill-zw6n5-{}-{test}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create scratch dir");
    dir
}

/// The `--namespace` build.sh passes, read from the script itself: the defect was
/// build.sh naming a namespace the spec had since emptied, so the test scaffolds
/// what build.sh scaffolds rather than a copy of it that can drift.
fn build_sh_namespace() -> String {
    let text = std::fs::read_to_string(lf1_dir().join("build.sh")).expect("read lf1/build.sh");
    let mut tokens = text.split_whitespace();
    while let Some(t) = tokens.next() {
        if t == "--namespace" {
            return tokens.next().expect("--namespace has a value").to_string();
        }
    }
    panic!("lf1/build.sh passes no --namespace");
}

fn file_names(dir: &Path) -> Vec<String> {
    let mut names: Vec<String> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
        .collect();
    names.sort();
    names
}

fn expect_ok(out: &Output, what: &str) {
    assert_eq!(
        out.code, 0,
        "{what} failed\n── stdout ──\n{}\n── stderr ──\n{}",
        out.stdout, out.stderr
    );
}

fn find_cxx() -> Option<&'static str> {
    ["clang++", "g++", "c++"].into_iter().find(|c| {
        Command::new(c)
            .arg("--version")
            .output()
            .is_ok_and(|o| o.status.success())
    })
}

/// Just enough of the Webots C++ API for `mavic_base.hpp`: `Robot` is a base
/// class (complete), the devices are held by pointer (declared).
const WEBOTS_STUBS: &[(&str, &str)] = &[
    (
        "Robot.hpp",
        "#pragma once\nnamespace webots { class Robot { public: virtual ~Robot() = default; }; }\n",
    ),
    ("GPS.hpp", "#pragma once\nnamespace webots { class GPS; }\n"),
    (
        "Gyro.hpp",
        "#pragma once\nnamespace webots { class Gyro; }\n",
    ),
    (
        "InertialUnit.hpp",
        "#pragma once\nnamespace webots { class InertialUnit; }\n",
    ),
    (
        "Motor.hpp",
        "#pragma once\nnamespace webots { class Motor; }\n",
    ),
];

/// Syntax-check `source` with the flags the generated Makefile builds with
/// (`-std=c++20 -Wall -Wextra`), warnings fatal.
fn syntax_check(cxx: &str, source: &Path, stub_include: &Path) {
    let out = Command::new(cxx)
        .args(["-std=c++20", "-fsyntax-only", "-Wall", "-Wextra", "-Werror"])
        .arg("-I")
        .arg(stub_include)
        .arg(source)
        .output()
        .expect("invoke compiler");
    assert!(
        out.status.success(),
        "{} does not compile (compiler: {cxx})\n{}",
        source.display(),
        String::from_utf8_lossy(&out.stderr)
    );
}

/// build.sh's scaffold: exit 0, each controller folder holding exactly its own
/// header closure (never the proof-only `lf1.safety_*` namespaces, never an
/// umbrella `lf1.hpp`), and every shim and every generated header compiling.
/// Before the fix cpp-project exited 1 with WI-761's "no entities … directly under
/// namespace 'anthill.examples.lf1'".
#[test]
fn lf1_scaffold_ships_each_controller_its_header_closure_and_compiles() {
    let lf1 = lf1_dir();
    let root = scratch("scaffold");
    let out_dir = root.join("build");
    let out = anthill(&[
        "codegen",
        "cpp-project",
        "--namespace",
        &build_sh_namespace(),
        "--cpp-sources",
        lf1.join("cpp").to_str().unwrap(),
        "--worlds-dir",
        lf1.join("worlds").to_str().unwrap(),
        "--output-dir",
        out_dir.to_str().unwrap(),
        lf1.to_str().unwrap(),
    ]);
    expect_ok(&out, "cpp-project over lf1");

    let controllers = out_dir.join("controllers");
    assert_eq!(
        file_names(&controllers),
        ["FollowerController", "LeaderController"]
    );
    let shared = [
        "Makefile",
        "anthill_examples_lf1_leader.hpp",
        "anthill_geometry.hpp",
        "anthill_runtime.hpp",
        "mavic_base.cpp",
        "mavic_base.hpp",
    ];
    let expected = |own: &[&str]| {
        let mut v: Vec<String> = shared.iter().chain(own).map(|s| s.to_string()).collect();
        v.sort();
        v
    };
    assert_eq!(
        file_names(&controllers.join("LeaderController")),
        expected(&["LeaderController_main.cpp"])
    );
    assert_eq!(
        file_names(&controllers.join("FollowerController")),
        expected(&[
            "FollowerController_main.cpp",
            "anthill_examples_lf1_follower_gps.hpp",
        ])
    );
    assert_eq!(
        file_names(&out_dir.join("worlds")),
        ["multirotor_leader_follower1.wbt"]
    );

    let Some(cxx) = find_cxx() else {
        eprintln!("no C++ compiler available — skipping the lf1 scaffold compile check");
        return;
    };
    let stubs = root.join("webots_stub");
    std::fs::create_dir_all(stubs.join("webots")).unwrap();
    for (name, text) in WEBOTS_STUBS {
        std::fs::write(stubs.join("webots").join(name), text).unwrap();
    }
    for ctor in ["LeaderController", "FollowerController"] {
        let dir = controllers.join(ctor);
        // The shim: generated API as the hand-written glue uses it.
        syntax_check(cxx, &dir.join(format!("{ctor}_main.cpp")), &stubs);
        // Each generated header on its OWN — so every include it needs was shipped.
        for name in file_names(&dir) {
            if name.starts_with("anthill_") && name.ends_with(".hpp") {
                let driver = root.join(format!("{ctor}__{name}.cpp"));
                std::fs::write(
                    &driver,
                    format!("#include \"{}\"\n", dir.join(&name).display()),
                )
                .unwrap();
                syntax_check(cxx, &driver, &stubs);
            }
        }
    }
    let _ = std::fs::remove_dir_all(&root);
}

const DEMO_SPEC: &str = r#"
namespace zw6n5.demo
  import anthill.prelude.{Float}
  import anthill.realization.{Generated}
  import anthill.prelude.Option.{some}

  sort Ctl
    operation step(x: Float) -> Float = x
  end

  fact Generated(
    source:      "zw6n5.demo.Ctl",
    artifact:    "controllers/Ctl",
    language:    "cpp",
    profile:     some("cpp20-stl"),
    kind:        "controller",
    description: some("entry-point refusal fixture")
  )
end
"#;

/// A declared controller with no source of its own would scaffold a folder with no
/// `main`, and `make` there fails at LINK (lf1's TransponderFollowerController
/// did). Refused before anything is written. CONTROL: the same fixture plus a
/// `Ctl_main.cpp` scaffolds — so the refusal is about the missing entry point, not
/// the fixture. Before the fix the first run exited 0.
#[test]
fn a_controller_without_an_entry_point_is_refused() {
    let root = scratch("entry_point");
    std::fs::write(root.join("demo.anthill"), DEMO_SPEC).unwrap();
    let cpp = root.join("cpp");
    std::fs::create_dir_all(&cpp).unwrap();
    // A shared helper is not the controller's own source.
    std::fs::write(cpp.join("helper.hpp"), "#pragma once\n").unwrap();
    let out_dir = root.join("build");
    let run = || {
        anthill(&[
            "codegen",
            "cpp-project",
            "--namespace",
            "zw6n5.demo",
            "--cpp-sources",
            cpp.to_str().unwrap(),
            "--output-dir",
            out_dir.to_str().unwrap(),
            root.join("demo.anthill").to_str().unwrap(),
        ])
    };

    let refused = run();
    assert_eq!(refused.code, 1, "stderr:\n{}", refused.stderr);
    assert!(
        refused.has_diagnostic(
            "error:",
            "controller 'Ctl' has no hand-authored entry point"
        ),
        "stderr:\n{}",
        refused.stderr
    );
    assert!(!out_dir.exists(), "a refused scaffold must write nothing");

    std::fs::write(cpp.join("Ctl_main.cpp"), "int main() { return 0; }\n").unwrap();
    expect_ok(&run(), "cpp-project with an entry point");
    assert_eq!(
        file_names(&out_dir.join("controllers").join("Ctl")),
        [
            "Ctl_main.cpp",
            "Makefile",
            "anthill_runtime.hpp",
            "helper.hpp",
            "zw6n5_demo.hpp",
        ]
    );
    let _ = std::fs::remove_dir_all(&root);
}

/// `codegen cpp` writes the same closure, under the names the includes spell.
/// Before the fix it wrote `follower_gps.hpp` (last segment) plus a hard-coded
/// `anthill_geometry.hpp`, and no leader header at all — so the
/// `#include "anthill_examples_lf1_leader.hpp"` inside it dangled.
#[test]
fn codegen_cpp_writes_the_closure_under_its_include_names() {
    let lf1 = lf1_dir();
    let root = scratch("codegen_cpp");
    let out = anthill(&[
        "codegen",
        "cpp",
        "--namespace",
        "anthill.examples.lf1.follower_gps",
        "--output-dir",
        root.to_str().unwrap(),
        lf1.to_str().unwrap(),
    ]);
    expect_ok(&out, "codegen cpp over lf1.follower_gps");
    assert_eq!(
        file_names(&root),
        [
            "anthill_examples_lf1_follower_gps.hpp",
            "anthill_examples_lf1_leader.hpp",
            "anthill_geometry.hpp",
            "anthill_runtime.hpp",
        ]
    );
    let _ = std::fs::remove_dir_all(&root);
}
