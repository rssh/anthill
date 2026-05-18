//! WI-203 — WorkItemStore spec + FileBasedWorkitemStore impl.
//!
//! Phase 2 (per proposal 036): `store.anthill` declares the spec
//! (over `Cell[V = State]`) and the file-backed impl
//! (`enum WIS { entity wis(...) }` + `fact WorkItemStore[State = WIS]`)
//! plus the operation bodies (next_id / lookup / by_status_of / commit /
//! commit_feedback / forget). This file is embedded in the bundle binary
//! alongside main.anthill — no per-project copy needed. This test
//! verifies the whole file loads + type-checks under the bundle path:
//! parse, resolution, and typing all succeed.

mod common;

use std::process::Command;

use common::setup_project;

const ANTHILL_TODO_BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

#[test]
fn store_anthill_loads_alongside_domain() {
    // Smoke test: just running `list` against a fresh project exercises
    // the bundle's embedded store.anthill load path. If the spec / impl
    // had a parse or resolution error, the bundle would print warnings
    // to stderr.
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "\
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
