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
"#
            .into(),
        )],
        stdlib_dir: stdlib_dir(),
        // WI-880 — the host bindings, without which the bundle has no host
        // implementations at all. `emitted_bundle_compiles` is the only thing in the
        // tree that compiles what this ships, so if the emitted crate is ever RUN this
        // is what makes `x.f` work in it.
        bindings_dir: stdlib_dir()
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("rustland/anthill-stl/anthill"),
        anthill_core_dep: CoreDep::Path(anthill_core_dir()),
    }
}

#[test]
fn bundle_emits_expected_file_layout() {
    let tmp = TempDir::new().unwrap();
    let opts = options();
    generate_bundle(&opts, tmp.path()).expect("generate");

    assert!(
        tmp.path().join("Cargo.toml").is_file(),
        "Cargo.toml emitted"
    );
    assert!(
        tmp.path().join("src/main.rs").is_file(),
        "src/main.rs emitted"
    );
    assert!(
        tmp.path().join("spec/user/hello.anthill").is_file(),
        "user source vendored"
    );
    assert!(
        tmp.path()
            .join("spec/stdlib/prelude/list.anthill")
            .is_file(),
        "stdlib list vendored"
    );
    assert!(
        tmp.path()
            .join("spec/stdlib/prelude/console.anthill")
            .is_file(),
        "stdlib console vendored"
    );
    assert!(
        tmp.path()
            .join("spec/stdlib/realization/rust_anthill.anthill")
            .is_file(),
        "rust_anthill profile vendored"
    );
}

/// WI-20261009-AN6CQ — the emitted loader hands the standard library to the loader
/// FIRST, in a load of its own, and the program in a later one — as the CLI does.
///
/// READ OFF THE EMITTED TEXT, AND THAT IS ALL IT IS: the two tables hold what their
/// names say, each is parsed into the argument its name says, and the loader makes the
/// one call that takes them apart. `emitted_bundle_compiles` (opt-in, below) is what
/// says the call exists with that shape. Nothing in the tree RUNS an emitted bundle,
/// so that a bundle REFUSES what `anthill` and `anthill-todo` refuse is not driven
/// here: it rests on `load::load_program` being the one function all three call, whose
/// seal `anthill-core`'s `wi_an6cq_load_program_test` and the two binaries' rows drive.
///
/// FAILS when the template goes back to one table and one `load_all` (measured: with
/// the pre-ticket template, no `EMBEDDED_PROGRAM` is found).
#[test]
fn the_emitted_loader_loads_the_stdlib_before_the_program() {
    let dir = tempfile::tempdir().expect("tempdir");
    generate_bundle(&options(), dir.path()).expect("bundle");
    let main_rs = std::fs::read_to_string(dir.path().join("src/main.rs")).expect("main.rs");

    let table = |name: &str| -> &str {
        let start = main_rs
            .find(&format!("static {name}: &[(&str, &str)] = &["))
            .unwrap_or_else(|| panic!("the emitted loader has no `{name}` table:\n{main_rs}"));
        let end = main_rs[start..].find("];").expect("the table closes") + start;
        &main_rs[start..end]
    };
    let (stdlib, program) = (table("EMBEDDED_STDLIB"), table("EMBEDDED_PROGRAM"));
    assert!(
        stdlib.contains("(\"stdlib/") && !stdlib.contains("(\"user/"),
        "the stdlib's table holds the stdlib's files and no file of the program:\n{stdlib}"
    );
    assert!(
        program.contains("(\"user/") && !program.contains("(\"stdlib/"),
        "the program's table holds the program's files and none of the stdlib's:\n{program}"
    );
    for wiring in [
        "let stdlib = parse_embedded(EMBEDDED_STDLIB)?;",
        "let program = parse_embedded(EMBEDDED_PROGRAM)?;",
        "let library: Vec<_> = stdlib.iter().collect();",
        "let program: Vec<_> = program.iter().collect();",
        "load::load_program(&mut kb, &library, &program, &NullResolver)",
    ] {
        assert!(
            main_rs.contains(wiring),
            "the stdlib's table is the library and the program's the program, through \
             `load_program`; missing `{wiring}` in:\n{main_rs}"
        );
    }
    assert!(
        !main_rs.contains("load::load_all("),
        "and no `load_all` of everything at once is left beside it"
    );
}

/// WI-880 — THE HOST BINDINGS ARE VENDORED, and the emitted `EMBEDDED_STDLIB` names
/// them.
///
/// A bundle vendored `stdlib/anthill` and nothing else, which was invisible while every
/// host implementation was registered by hardcoded qualified name in `eval/builtins.rs`
/// — `register_standard_builtins` bound them regardless of what the bundle shipped. With
/// the surface keyed per operation, a bundle without the binding blocks has no
/// `Int64.add`, no `String.concat`, and none of the 26 `anthill.reflect` accessors, so
/// `x.f` in an operation body (which lowers to `field_access`) does not run.
///
/// Found by /code-review. NOT covered before by anything: `bundle_emits_expected_file_
/// layout` checks the layout, and `emitted_bundle_compiles` COMPILES the crate — neither
/// looks at which spec files went in, and a missing host implementation is a RUN-time
/// failure, so compiling proves nothing about it.
///
/// WHAT THIS STILL DOES NOT COVER, stated rather than implied: nothing in the tree RUNS
/// an emitted bundle. This asserts the sources are present and named; that they then
/// register is `register_operation_mappings`' contract, driven in anthill-core.
#[test]
fn bundle_vendors_the_rust_host_bindings() {
    let dir = tempfile::tempdir().expect("tempdir");
    generate_bundle(&options(), dir.path()).expect("bundle");

    let vendored = dir.path().join("spec/stdlib/host-rust/reflect.anthill");
    assert!(
        vendored.is_file(),
        "the rust binding tree must be vendored — without it the bundle has no host \
         implementations at all; looked for {}",
        vendored.display()
    );
    let mapped = std::fs::read_to_string(&vendored).expect("read vendored binding");
    assert!(
        mapped.contains("operation_map"),
        "the vendored file must be the binding block itself, not an empty placeholder"
    );

    let main_rs = std::fs::read_to_string(dir.path().join("src/main.rs")).expect("main.rs");
    assert!(
        main_rs.contains("stdlib/host-rust/reflect.anthill"),
        "…and `EMBEDDED_STDLIB` must NAME it: vendoring a file the generated loader \
         never lists would leave the bundle exactly as broken, and this is the half a \
         file-layout check cannot see:\n{main_rs}"
    );
    // ORDER: the bindings refine declarations the stdlib makes, so they must load AFTER
    // it — the same rule `anthill-stl/src/stdlib.rs`'s hand-ordered list follows.
    let stdlib_at = main_rs.find("stdlib/prelude/").expect("a prelude file is listed");
    let binding_at = main_rs.find("stdlib/host-rust/").expect("a binding is listed");
    assert!(
        stdlib_at < binding_at,
        "the host bindings must be listed after the stdlib they refine"
    );
}

#[test]
fn cargo_toml_names_crate_and_binary() {
    let tmp = TempDir::new().unwrap();
    let opts = options();
    generate_bundle(&opts, tmp.path()).expect("generate");
    let cargo = std::fs::read_to_string(tmp.path().join("Cargo.toml")).unwrap();
    assert!(
        cargo.contains("name = \"hello-bundle\""),
        "Cargo.toml carries crate name"
    );
    assert!(
        cargo.contains("[[bin]]"),
        "Cargo.toml declares a [[bin]] target"
    );
    assert!(
        cargo.contains("anthill-core = { path"),
        "Cargo.toml has anthill-core path dep"
    );
}

#[test]
fn main_rs_dispatches_to_entry_qname() {
    let tmp = TempDir::new().unwrap();
    let opts = options();
    generate_bundle(&opts, tmp.path()).expect("generate");
    let main = std::fs::read_to_string(tmp.path().join("src/main.rs")).unwrap();
    assert!(
        main.contains("interp.call(\"demo.hello.main\""),
        "main calls the named entry op"
    );
    assert!(
        main.contains("register_standard_builtins"),
        "main registers standard builtins"
    );
    assert!(
        main.contains("register_standard_effect_handlers"),
        "main registers default effect handlers"
    );
    assert!(
        main.contains("include_str!(\"../spec/user/hello.anthill\")"),
        "main embeds the user source via include_str!"
    );
}

#[test]
fn description_omitted_when_none() {
    let tmp = TempDir::new().unwrap();
    let mut opts = options();
    opts.description = None;
    generate_bundle(&opts, tmp.path()).expect("generate");
    let cargo = std::fs::read_to_string(tmp.path().join("Cargo.toml")).unwrap();
    assert!(
        !cargo.contains("description ="),
        "no description = line when description is None; got:\n{cargo}"
    );
}

/// End-to-end smoke: emit the bundle, then run `cargo check` on it.
/// Verifies the generated `main.rs` is valid Rust against the real
/// `anthill-core` API. Slow (~minutes on cold cache), so it lives behind
/// the `--ignored` flag — invoke explicitly with
/// `cargo test -p anthill-rust-gen -- --ignored`.
///
/// RUN IT WHENEVER `anthill-core`'s PUBLIC API MOVES, and treat that as a rule rather
/// than a courtesy. The bundle's `main.rs` lives inside a `format!` string literal, so
/// `cargo check --workspace --all-targets` cannot see it and neither can a
/// compiler-driven census of a removed method's call sites: the template is the one
/// consumer of the API that the compiler is blind to, and THIS test is the only thing
/// that reads it. WI-20260827-14EV6 deleted `Value::as_int`, which the template called;
/// the whole workspace stayed green and every emitted bundle would have failed to
/// compile at the user's machine. Measured — with that one line reverted this test
/// fails with `no method named `as_int` found for enum `Value``, in 22s on a warm cache.
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
        cargo.contains(
            "anthill-core = { git = \"https://github.com/example/anthill\", rev = \"deadbeef\" }"
        ),
        "Cargo.toml carries git+rev dep, got:\n{cargo}",
    );
    assert!(
        !cargo.contains("anthill-core = { path"),
        "git mode should not emit a path dep for anthill-core"
    );
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
