//! WI-748: `anthill-todo -d <dir> init` must scaffold under <dir>, not the cwd.
//!
//! Every other subcommand routes `-d` through `find_project_dir`; init alone
//! hardcoded the cwd, so `-d X init` from any other directory silently dropped
//! the project wherever the user stood — and the success message named a bare
//! `anthill-todo/` with no path, so nothing in the output revealed where it went.
//! The existing shim test (`cmd_shim_test::init_with_leading_dir_flag_scaffolds`)
//! set cwd == the -d dir, so it could not tell "honors -d" from "uses cwd". These
//! tests keep the two DISTINCT, which is what the bug needed to surface.

use std::process::Command;

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

#[test]
fn init_honors_dir_flag_from_a_different_cwd() {
    let cwd_dir = tempfile::tempdir().expect("cwd tempdir");
    let target = tempfile::tempdir().expect("target tempdir");
    assert_ne!(
        cwd_dir.path(),
        target.path(),
        "cwd and -d must differ for this test"
    );

    let out = Command::new(BIN)
        .current_dir(cwd_dir.path())
        .args(["-d", target.path().to_str().unwrap(), "init"])
        .output()
        .expect("run init");
    assert!(
        out.status.success(),
        "init failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    // The scaffold lands under -d …
    assert!(
        target
            .path()
            .join("anthill-todo/store_format.anthill")
            .exists(),
        "store_format.anthill missing under -d target"
    );
    assert!(
        target.path().join("anthill-todo/project.anthill").exists(),
        "project.anthill missing under -d target"
    );
    // … and NOTHING leaks into the cwd.
    assert!(
        !cwd_dir.path().join("anthill-todo").exists(),
        "init leaked an anthill-todo/ into the cwd"
    );

    // The success message names the ABSOLUTE path created — matching what the CLI
    // builds (canonicalize(base).join("anthill-todo")) so a wrong-place write is
    // visible even to someone reading the output.
    let stdout = String::from_utf8_lossy(&out.stdout);
    let expected = std::fs::canonicalize(target.path())
        .unwrap()
        .join("anthill-todo");
    assert!(
        stdout.contains(&*expected.to_string_lossy()),
        "success message must name the absolute created path {}; got: {stdout}",
        expected.display()
    );

    // `list` immediately after init must FIND the just-created project — the
    // write side and the discovery side agree on where the project lives.
    let list = Command::new(BIN)
        .args(["-d", target.path().to_str().unwrap(), "list"])
        .output()
        .expect("run list");
    assert!(
        list.status.success(),
        "list after init must find the project: stderr={}",
        String::from_utf8_lossy(&list.stderr)
    );
    let list_err = String::from_utf8_lossy(&list.stderr);
    assert!(
        !list_err.contains("no anthill-todo project found"),
        "list must not report a missing project right after init: {list_err}"
    );
}

#[test]
fn init_refuses_to_scaffold_over_an_existing_project() {
    let target = tempfile::tempdir().expect("target tempdir");

    let first = Command::new(BIN)
        .args(["-d", target.path().to_str().unwrap(), "init"])
        .output()
        .expect("run init");
    assert!(
        first.status.success(),
        "first init: {}",
        String::from_utf8_lossy(&first.stderr)
    );

    // A second init at the same -d must fail LOUDLY, not silently re-scaffold.
    let second = Command::new(BIN)
        .args(["-d", target.path().to_str().unwrap(), "init"])
        .output()
        .expect("run init again");
    assert!(
        !second.status.success(),
        "re-init over an existing project must exit non-zero"
    );
    let stderr = String::from_utf8_lossy(&second.stderr);
    assert!(
        stderr.contains("already exists"),
        "re-init error must name the collision: {stderr}"
    );
}

#[test]
fn init_with_nonexistent_dir_flag_errors() {
    let parent = tempfile::tempdir().expect("tempdir");
    let missing = parent.path().join("nope");

    let out = Command::new(BIN)
        .args(["-d", missing.to_str().unwrap(), "init"])
        .output()
        .expect("run init");
    assert!(
        !out.status.success(),
        "init -d <nonexistent> must error, not conjure a tree"
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("does not exist"),
        "error must name the missing directory: {stderr}"
    );
    assert!(
        !missing.exists(),
        "init must not have created the missing -d directory"
    );
}

#[test]
fn init_refuses_over_a_flat_layout_project() {
    // A project can live "flat": marker files directly in the base dir with no
    // `anthill-todo/` subdir (the layout `find_project_dir`'s arm 3 accepts). Its
    // refusal path is a SECOND guard, distinct from the re-init `dir.exists()`
    // one: init always scaffolds a nested `anthill-todo/`, so only a hand-planted
    // flat project reaches `is_project_dir(&abs_base)`. Without this test that
    // guard is unreachable and a regression (dropping it, or flipping it to
    // `!is_project_dir`) would silently nest a second project.
    let target = tempfile::tempdir().expect("target tempdir");
    std::fs::write(
        target.path().join("workitems.anthill"),
        "-- Work items\n\nfact StoreFormat(version: 1)\n",
    )
    .expect("plant flat-layout marker");

    let out = Command::new(BIN)
        .args(["-d", target.path().to_str().unwrap(), "init"])
        .output()
        .expect("run init");
    assert!(
        !out.status.success(),
        "init must refuse over a flat-layout project, not nest a second one"
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("already an anthill-todo project"),
        "flat-layout refusal must name the collision: {stderr}"
    );
    assert!(
        !target.path().join("anthill-todo").exists(),
        "init must not nest an anthill-todo/ inside a flat-layout project"
    );
}

#[test]
fn init_with_relative_dir_flag_scaffolds_absolute() {
    // The whole point of canonicalizing is an ABSOLUTE success message even when
    // -d is RELATIVE. The other tests pass absolute tempdir paths, for which
    // canonicalize only resolves symlinks — so on a non-symlinked /tmp its effect
    // is invisible and a dropped canonicalize would go uncaught. A relative -d
    // makes the absolute-ness observable everywhere.
    let parent = tempfile::tempdir().expect("parent tempdir");
    let subname = "relproj";
    let sub = parent.path().join(subname);
    std::fs::create_dir(&sub).expect("mkdir sub");

    let out = Command::new(BIN)
        .current_dir(parent.path())
        .args(["-d", subname, "init"]) // RELATIVE -d, resolved against the cwd
        .output()
        .expect("run init");
    assert!(
        out.status.success(),
        "relative -d init failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        sub.join("anthill-todo/store_format.anthill").exists(),
        "scaffold missing under the relative -d target"
    );

    // The printed `created <path> with:` line must carry an ABSOLUTE path even
    // though -d was relative — the platform-independent proof canonicalize ran.
    let stdout = String::from_utf8_lossy(&out.stdout);
    let created = stdout
        .lines()
        .find(|l| l.starts_with("created ") && l.ends_with(" with:"))
        .expect("init must print a 'created <path> with:' line");
    let path_str = created
        .strip_prefix("created ")
        .unwrap()
        .strip_suffix(" with:")
        .unwrap();
    assert!(
        std::path::Path::new(path_str).is_absolute(),
        "created path must be absolute even for a relative -d; got: {path_str}"
    );

    // The default project name derives from the -d dir's basename (not the cwd) —
    // the `cwd.file_name()` → `abs_base.file_name()` change this fix introduced.
    let project = std::fs::read_to_string(sub.join("anthill-todo/project.anthill"))
        .expect("read project.anthill");
    assert!(
        project.contains(&format!("name: \"{subname}\"")),
        "default project name must derive from the -d dir basename; got: {project}"
    );
}

// ─── init's NAME argument, and what a dash-led token in it means ─────────────
//
// `init` is host-served — it runs before any KB exists — so the bundle's
// spec-driven argument reporter never sees its argv, and the name is POSITIONAL.
// Together that meant every mistyped flag read as a project name: `init --help`
// scaffolded a project literally CALLED `--help` and exited 0 (found censusing
// WI-1124, 2026-09-06).
//
// CONTROL. Restore the two-arm `match` these replace —
//     let name = match bundle_argv.get(1).map(|s| s.as_str()) {
//         Some("--name") => bundle_argv.get(2).map(|s| s.as_str()),
//         other => other,
//     };
// — and all four tests below fail: each one's dash-led token becomes the name and
// the command exits 0 having scaffolded. `init_names_the_project_from_a_bare_
// argument` passes either way BY DESIGN; it is the witness that the refusals did
// not cost `init` the argument it is actually for. The four are one per argv
// shape because the arms differ: `--help` PRINTS and succeeds, a stray flag and a
// flag-valued `--name` REFUSE, and a value-less `--name` used to fall through to
// the directory-derived default rather than to any flag at all.

/// Returns the `TempDir` itself, not its path: the caller has to hold the guard
/// while it asserts on what was (or was not) written, and a `PathBuf` would let
/// the directory be cleaned up first, making every `scaffolded()` answer false.
fn init_in_a_fresh_dir(args: &[&str]) -> (i32, String, String, tempfile::TempDir) {
    let dir = tempfile::tempdir().expect("tempdir");
    let mut argv = vec!["-d", dir.path().to_str().unwrap(), "init"];
    argv.extend_from_slice(args);
    let out = Command::new(BIN).args(&argv).output().expect("run init");
    (
        out.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
        dir,
    )
}

fn scaffolded(dir: &tempfile::TempDir) -> bool {
    dir.path().join("anthill-todo/project.anthill").exists()
}

#[test]
fn init_help_prints_usage_and_scaffolds_nothing() {
    let (code, stdout, _, dir) = init_in_a_fresh_dir(&["--help"]);
    assert_eq!(code, 0, "`init --help` is a help request, not a failure");
    assert!(
        stdout.contains("usage: anthill-todo [-d <DIR>] init [<name>]"),
        "expected init's own usage, got stdout:\n{stdout}"
    );
    assert!(
        !scaffolded(&dir),
        "a help request must not create a project; {} exists",
        dir.path().join("anthill-todo").display()
    );
}

#[test]
fn init_refuses_a_stray_flag_as_a_project_name() {
    let (code, _, stderr, dir) = init_in_a_fresh_dir(&["--nosuch"]);
    assert_eq!(code, 2, "a mistyped flag is a usage error");
    assert!(
        stderr.contains("`init` takes a project name, not the flag `--nosuch`"),
        "the refusal must name the offending token, got stderr:\n{stderr}"
    );
    assert!(!scaffolded(&dir), "a refused init must create nothing");
}

#[test]
fn init_name_refuses_a_flag_as_its_value() {
    let (code, _, stderr, dir) = init_in_a_fresh_dir(&["--name", "--help"]);
    assert_eq!(code, 2, "a flag where a name belongs is a usage error");
    assert!(
        stderr.contains("`init --name` expects a project name, got the flag `--help`"),
        "the refusal must name the offending token, got stderr:\n{stderr}"
    );
    assert!(!scaffolded(&dir), "a refused init must create nothing");
}

#[test]
fn init_name_with_no_value_is_refused_rather_than_defaulted() {
    // This one never involved a flag: `--name` with nothing after it fell through
    // to the directory-derived default, so a malformed flag scaffolded a project
    // under a name the caller never chose.
    let (code, _, stderr, dir) = init_in_a_fresh_dir(&["--name"]);
    assert_eq!(code, 2, "a value-less --name is a usage error");
    assert!(
        stderr.contains("`init --name` expects a project name, and none was given"),
        "the refusal must say what was missing, got stderr:\n{stderr}"
    );
    assert!(!scaffolded(&dir), "a refused init must create nothing");
}

#[test]
fn init_names_the_project_from_a_bare_argument() {
    // Passes with and without the refusals, BY DESIGN: the control that they did
    // not cost `init` the positional argument they guard.
    let (code, _, stderr, dir) = init_in_a_fresh_dir(&["my-thing"]);
    assert_eq!(
        code, 0,
        "a plain name must still scaffold; stderr:\n{stderr}"
    );
    let project = std::fs::read_to_string(dir.path().join("anthill-todo/project.anthill"))
        .expect("project.anthill written");
    assert!(
        project.contains("name: \"my-thing\""),
        "the given name must reach the project file, got:\n{project}"
    );
}

#[test]
fn init_refuses_a_token_after_the_project_name() {
    // /code-review, 2026-09-06: guarding argv[1] alone left the same swallow one
    // position over — `init myproj --help` scaffolded `myproj` and discarded
    // `--help` in silence. CONTROL: drop the `consumed`/`extra` check and this
    // fails alone; `init_names_the_project_from_a_bare_argument` stays green,
    // which is what says the guard did not eat the name itself.
    let (code, _, stderr, dir) = init_in_a_fresh_dir(&["myproj", "--help"]);
    assert_eq!(code, 2, "an unconsumed trailing token is a usage error");
    assert!(
        stderr.contains("`init` takes one project name; `--help` is unexpected"),
        "the refusal must name the dropped token, got stderr:\n{stderr}"
    );
    assert!(!scaffolded(&dir), "a refused init must create nothing");
}
