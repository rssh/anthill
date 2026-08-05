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
    assert_ne!(cwd_dir.path(), target.path(), "cwd and -d must differ for this test");

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
        target.path().join("anthill-todo/workitems.anthill").exists(),
        "workitems.anthill missing under -d target"
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
    let expected = std::fs::canonicalize(target.path()).unwrap().join("anthill-todo");
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
    assert!(first.status.success(), "first init: {}", String::from_utf8_lossy(&first.stderr));

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
    assert!(!missing.exists(), "init must not have created the missing -d directory");
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
        sub.join("anthill-todo/workitems.anthill").exists(),
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
    let project =
        std::fs::read_to_string(sub.join("anthill-todo/project.anthill")).expect("read project.anthill");
    assert!(
        project.contains(&format!("name: \"{subname}\"")),
        "default project name must derive from the -d dir basename; got: {project}"
    );
}
