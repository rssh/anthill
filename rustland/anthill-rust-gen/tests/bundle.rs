//! Tests for `bundle::generate_bundle`. Runs the generator against a
//! hello-world fixture and asserts the emitted file structure plus a few
//! key contents. Does NOT invoke `cargo` on the emitted crate — that
//! costs a full target/ build per test invocation and is more
//! appropriate for a manual smoke or for the WI-009 anthill-todo port.

use std::path::PathBuf;

use anthill_rust_gen::{generate_bundle, BundleError, BundleOptions, CoreDep};
use tempfile::TempDir;

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn stdlib_dir() -> PathBuf {
    workspace_root().join("stdlib/anthill")
}

fn anthill_core_dir() -> PathBuf {
    workspace_root().join("rustland/anthill-core")
}

fn options() -> BundleOptions {
    BundleOptions {
        project_name: "hello-bundle".into(),
        description: Some("smoke test for anthill-rust-gen".into()),
        entry_qname: "demo.hello.main".into(),
        user_sources: vec![(
            "hello.anthill".into(),
            r#"
namespace demo.hello
  import anthill.prelude.{Int64, String, List}
  import anthill.prelude.Console.{console, println, ConsoleOutput}

  operation main(args: List[T = String]) -> Int64
    effects ConsoleOutput
  =
    let _ = println(console(), "hello bundle")
    0
end
"#.into(),
        )],
        stdlib_dir: stdlib_dir(),
        anthill_core_dep: CoreDep::Path(anthill_core_dir()),
    }
}

#[test]
fn bundle_emits_expected_file_layout() {
    let tmp = TempDir::new().unwrap();
    let opts = options();
    generate_bundle(&opts, tmp.path()).expect("generate");

    assert!(tmp.path().join("Cargo.toml").is_file(), "Cargo.toml emitted");
    assert!(tmp.path().join("src/main.rs").is_file(), "src/main.rs emitted");
    assert!(tmp.path().join("spec/user/hello.anthill").is_file(), "user source vendored");
    assert!(tmp.path().join("spec/stdlib/prelude/list.anthill").is_file(), "stdlib list vendored");
    assert!(tmp.path().join("spec/stdlib/prelude/console.anthill").is_file(), "stdlib console vendored");
    assert!(tmp.path().join("spec/stdlib/realization/rust_anthill.anthill").is_file(), "rust_anthill profile vendored");
}

#[test]
fn cargo_toml_names_crate_and_binary() {
    let tmp = TempDir::new().unwrap();
    let opts = options();
    generate_bundle(&opts, tmp.path()).expect("generate");
    let cargo = std::fs::read_to_string(tmp.path().join("Cargo.toml")).unwrap();
    assert!(cargo.contains("name = \"hello-bundle\""), "Cargo.toml carries crate name");
    assert!(cargo.contains("[[bin]]"), "Cargo.toml declares a [[bin]] target");
    assert!(cargo.contains("anthill-core = { path"), "Cargo.toml has anthill-core path dep");
}

#[test]
fn main_rs_dispatches_to_entry_qname() {
    let tmp = TempDir::new().unwrap();
    let opts = options();
    generate_bundle(&opts, tmp.path()).expect("generate");
    let main = std::fs::read_to_string(tmp.path().join("src/main.rs")).unwrap();
    assert!(main.contains("interp.call(\"demo.hello.main\""), "main calls the named entry op");
    assert!(main.contains("register_standard_builtins"), "main registers standard builtins");
    assert!(main.contains("register_standard_effect_handlers"), "main registers default effect handlers");
    assert!(main.contains("include_str!(\"../spec/user/hello.anthill\")"),
            "main embeds the user source via include_str!");
}

#[test]
fn description_omitted_when_none() {
    let tmp = TempDir::new().unwrap();
    let mut opts = options();
    opts.description = None;
    generate_bundle(&opts, tmp.path()).expect("generate");
    let cargo = std::fs::read_to_string(tmp.path().join("Cargo.toml")).unwrap();
    assert!(!cargo.contains("description ="),
            "no description = line when description is None; got:\n{cargo}");
}

/// End-to-end smoke: emit the bundle, then run `cargo check` on it.
/// Verifies the generated `main.rs` is valid Rust against the real
/// `anthill-core` API. Slow (~minutes on cold cache), so it lives behind
/// the `--ignored` flag — invoke explicitly with
/// `cargo test -p anthill-rust-gen -- --ignored`.
#[test]
#[ignore = "runs nested cargo check; opt in via --ignored"]
fn emitted_bundle_compiles() {
    let tmp = TempDir::new().unwrap();
    let opts = options();
    generate_bundle(&opts, tmp.path()).expect("generate");
    let status = std::process::Command::new(env!("CARGO"))
        .args(["check", "--quiet", "--manifest-path"])
        .arg(tmp.path().join("Cargo.toml"))
        .status()
        .expect("invoke cargo check");
    assert!(status.success(), "emitted bundle failed to cargo check");
}

#[test]
fn git_dep_renders_url_and_rev() {
    let tmp = TempDir::new().unwrap();
    let mut opts = options();
    opts.anthill_core_dep = CoreDep::Git {
        url: "https://github.com/example/anthill".into(),
        rev: "deadbeef".into(),
    };
    generate_bundle(&opts, tmp.path()).expect("generate");
    let cargo = std::fs::read_to_string(tmp.path().join("Cargo.toml")).unwrap();
    assert!(
        cargo.contains("anthill-core = { git = \"https://github.com/example/anthill\", rev = \"deadbeef\" }"),
        "Cargo.toml carries git+rev dep, got:\n{cargo}",
    );
    assert!(!cargo.contains("anthill-core = { path"),
            "git mode should not emit a path dep for anthill-core");
}

#[test]
fn errors_when_no_user_sources() {
    let tmp = TempDir::new().unwrap();
    let mut opts = options();
    opts.user_sources.clear();
    match generate_bundle(&opts, tmp.path()) {
        Err(BundleError::NoSources) => {}
        other => panic!("expected NoSources, got {other:?}"),
    }
}
