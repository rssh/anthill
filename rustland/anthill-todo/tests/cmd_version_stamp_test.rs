//! WI-434: per-project data-format versioning, done anthill-native.
//!
//! `init` scaffolds a new project stamped with `fact StoreFormat(version: N)`.
//! The bundle's `main` runs a version check (a query over the loaded
//! StoreFormat facts — NOT a host prescan) that warns on stderr when a project
//! has no stamp (pre-versioning) or a stamp whose version differs from the
//! binary. `migrate` stamps a pre-versioning project by asserting the fact
//! THROUGH the store, so the write lands in workitems.anthill. The entity is
//! defined in the binary bundle, so a stamp resolves regardless of how old the
//! project's own domain.anthill is.

mod common;

use std::path::Path;
use std::process::Command;

use common::setup_project;

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

fn run_in(dir: &Path, args: &[&str]) -> std::process::Output {
    Command::new(BIN).current_dir(dir).args(args).output().expect("run anthill-todo")
}

fn run(proj: &Path, args: &[&str]) -> std::process::Output {
    let mut full = vec!["-d", proj.to_str().unwrap()];
    full.extend_from_slice(args);
    Command::new(BIN).args(&full).output().expect("run anthill-todo")
}

fn stderr(out: &std::process::Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}
fn stdout(out: &std::process::Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

// A pre-versioning project: work items but no `StoreFormat` stamp.
const NO_STAMP: &str = r#"
fact WorkItem(
  id: "WI-001",
  description: "base item",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)
"#;

const STAMPED_CURRENT: &str = r#"
fact StoreFormat(version: 1)

fact WorkItem(
  id: "WI-001",
  description: "base item",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)
"#;

// A stamp at a version the binary does not understand — stands in for a project
// left behind by a future format bump.
const STAMPED_STALE: &str = r#"
fact StoreFormat(version: 99)

fact WorkItem(
  id: "WI-001",
  description: "base item",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)
"#;

/// `init` scaffolds a stamped project, so a following command must not warn
/// about versioning. This also guards the host `CURRENT_STORE_FORMAT_VERSION`
/// ↔ bundle `current_store_format` pairing: if the two integers diverge, a
/// freshly-initialised project reads as stale and this test fails.
#[test]
fn fresh_init_project_loads_clean() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let init = run_in(tmp.path(), &["init", "demo"]);
    assert!(init.status.success(), "init failed: {}", stderr(&init));

    let out = run(tmp.path(), &["status"]);
    let e = stderr(&out);
    assert!(!e.contains("pre-versioning"), "fresh init is pre-versioning: {e}");
    assert!(!e.contains("store format has version"), "fresh init reads stale: {e}");
}

/// A project with no stamp at all — the entity is defined (in the bundle) but
/// no fact asserts it — is reported as pre-versioning.
#[test]
fn pre_versioning_project_warns() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, NO_STAMP);
    let e = stderr(&run(&proj, &["status"]));
    assert!(e.contains("pre-versioning"), "expected pre-versioning warning, got: {e}");
}

/// A stamp whose version differs from the binary warns loudly, naming both the
/// found and the expected version.
#[test]
fn stale_stamp_warns_with_versions() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, STAMPED_STALE);
    let e = stderr(&run(&proj, &["status"]));
    assert!(e.contains("store format has version 99"), "got: {e}");
    assert!(e.contains("expects version 1"), "got: {e}");
}

/// A current stamp is silent — no pre-versioning, no stale warning.
#[test]
fn current_stamp_is_silent() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, STAMPED_CURRENT);
    let e = stderr(&run(&proj, &["status"]));
    assert!(!e.contains("pre-versioning"), "got: {e}");
    assert!(!e.contains("store format has version"), "got: {e}");
}

/// `migrate` stamps a pre-versioning project by persisting the fact through the
/// store (it lands in workitems.anthill), and a reload is then clean.
#[test]
fn migrate_stamps_pre_versioning_project() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, NO_STAMP);

    let out = run(&proj, &["migrate"]);
    assert!(out.status.success(), "migrate failed: {}", stderr(&out));
    assert!(stdout(&out).contains("migrated"), "migrate did not report: {}", stdout(&out));

    let wi = std::fs::read_to_string(proj.join("anthill-todo/workitems.anthill"))
        .expect("read workitems");
    assert!(wi.contains("StoreFormat"), "StoreFormat not persisted through store: {wi}");

    let e = stderr(&run(&proj, &["status"]));
    assert!(!e.contains("pre-versioning"), "still pre-versioning after migrate: {e}");
}

/// `migrate` on an already-current project is a no-op that says so.
#[test]
fn migrate_is_idempotent() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, STAMPED_CURRENT);
    let out = run(&proj, &["migrate"]);
    assert!(stdout(&out).contains("already up to date"),
        "expected up-to-date, got: {}", stdout(&out));
}

/// `migrate` does NOT silently re-stamp a version it has no data migrator for —
/// it reports and fails rather than mislabel the data's format.
#[test]
fn migrate_refuses_unmigratable_version() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, STAMPED_STALE);
    let out = run(&proj, &["migrate"]);
    assert!(!out.status.success(), "migrate should fail on an un-migratable version");
    assert!(stderr(&out).contains("cannot be migrated"), "expected refusal, got: {}", stderr(&out));
}
