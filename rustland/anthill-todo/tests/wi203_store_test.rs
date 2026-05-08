//! WI-203 — WorkItemStore spec + FileBasedWorkitemStore impl.
//!
//! Phase 2 (per proposal 036): the project-side `store.anthill` declares
//! the spec (over `Cell[V = State]`) and the file-backed impl
//! (`enum WIS { entity wis(...) }` + `fact WorkItemStore[State = WIS]`).
//! Bundle command bodies aren't yet rewritten to use it (phase 3); this
//! test verifies the declarations load alongside domain.anthill /
//! rules.anthill and the fact is asserted.

mod common;

use std::fs;
use std::process::Command;

use common::{setup_project, workspace_root};

const ANTHILL_TODO_BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

/// Variant of setup_project that also copies store.anthill into the
/// project's anthill-todo/ — verifying the bundle's BulkStore::pull
/// path picks it up alongside the existing domain/rules.
fn setup_project_with_store(tmp: &tempfile::TempDir, workitems: &str) -> std::path::PathBuf {
    let proj = setup_project(tmp, workitems);
    let inner = proj.join("anthill-todo");
    let src_root = workspace_root().join("anthill-todo");
    fs::copy(src_root.join("store.anthill"), inner.join("store.anthill"))
        .expect("copy store.anthill");
    proj
}

#[test]
fn store_anthill_loads_alongside_domain() {
    // Smoke test: just running `list` against a project that has
    // store.anthill in its anthill-todo/ directory exercises the load
    // path. If the spec / impl had a parse or resolution error, the
    // bundle would print warnings to stderr.
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project_with_store(&tmp, "\
fact WorkItem(
  id: \"WI-001\",
  description: \"first\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Open)
");
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(), "list"])
        .output().expect("run");
    let stderr = String::from_utf8_lossy(&out.stderr);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success(),
        "bundle list failed: stdout={stdout}\nstderr={stderr}",
    );
    // Surface any unresolved imports / sorts / facts surfaced during
    // load — they print to stderr as `warning: …`.
    assert!(
        !stderr.contains("unresolved"),
        "store.anthill load produced unresolved-* warnings: {stderr}",
    );
    assert!(
        !stderr.contains("error:"),
        "store.anthill load produced an error: {stderr}",
    );
    // The stage0 WorkItem is still discoverable; the store.anthill load
    // didn't break the existing list-by-functor query.
    assert!(stdout.contains("WI-001"), "expected WI-001 in list: {stdout}");
}
