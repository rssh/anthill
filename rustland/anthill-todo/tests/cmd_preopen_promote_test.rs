//! `preopen <id>` / `promote <id>`: the Open↔PreOpened transition pair.
//! `preopen` demotes an Open item to PreOpened (backlog, not claimable);
//! `promote` lifts a PreOpened item back into the active Open queue. Each is
//! valid only from its source status (loud error otherwise) and routes
//! through the same atomic buffered-replace path as claim/unclaim.

mod common;

use std::process::Command;

use common::{read_combined, setup_project};

const ANTHILL_TODO_BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

const SINGLE_OPEN_WI: &str = "\
fact WorkItem(
  id: \"WI-001\",
  description: \"open item\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Open)
";

const SINGLE_PREOPENED_WI: &str = "\
fact WorkItem(
  id: \"WI-001\",
  description: \"backlog item\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: PreOpened)
";

const SINGLE_CLAIMED_WI: &str = "\
fact WorkItem(
  id: \"WI-001\",
  description: \"claimed item\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Claimed(agent: \"alice\", since: \"2026-05-01T00:00:00Z\"))
";

#[test]
fn preopen_demotes_open_to_preopened() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, SINGLE_OPEN_WI);
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "--agent", "bob", "preopen", "WI-001"])
        .output().unwrap();
    assert!(out.status.success(),
        "preopen failed: {}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("preopened: WI-001 by bob"), "stdout: {stdout}");

    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(combined.contains("status: PreOpened"),
        "PreOpened replacement not present: {combined}");
}

#[test]
fn promote_lifts_preopened_to_open() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, SINGLE_PREOPENED_WI);
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "--agent", "bob", "promote", "WI-001"])
        .output().unwrap();
    assert!(out.status.success(),
        "promote failed: {}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("promoted: WI-001 by bob"), "stdout: {stdout}");

    // The workitems file must no longer carry the PreOpened status for WI-001.
    let workitems = std::fs::read_to_string(
        proj.join("anthill-todo").join("workitems.anthill")).unwrap();
    assert!(workitems.contains("status: Open"),
        "should be Open now: {workitems}");
    assert!(!workitems.contains("PreOpened"),
        "no PreOpened should remain in workitems: {workitems}");
}

#[test]
fn preopen_on_non_open_errors() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, SINGLE_CLAIMED_WI);
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "preopen", "WI-001"])
        .output().unwrap();
    assert_eq!(out.status.code(), Some(1),
        "expected exit 1 on a non-Open item; stderr={}",
        String::from_utf8_lossy(&out.stderr));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("WI-001") && stderr.contains("is not Open"),
        "expected a clear 'is not Open' diagnostic, got: {stderr}");
    assert!(stderr.contains("Claimed"),
        "diagnostic should name the current status: {stderr}");
}

#[test]
fn promote_on_non_preopened_errors() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, SINGLE_OPEN_WI);
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "promote", "WI-001"])
        .output().unwrap();
    assert_eq!(out.status.code(), Some(1),
        "expected exit 1 on a non-PreOpened item; stderr={}",
        String::from_utf8_lossy(&out.stderr));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("WI-001") && stderr.contains("is not PreOpened"),
        "expected a clear 'is not PreOpened' diagnostic, got: {stderr}");
}

/// Round-trip: an Open item demoted then promoted returns to a claimable Open
/// state (the whole point of the inverse pair).
#[test]
fn preopen_then_promote_round_trips_to_open() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, SINGLE_OPEN_WI);

    let demote = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "--agent", "alice", "preopen", "WI-001"])
        .output().unwrap();
    assert!(demote.status.success(),
        "preopen failed: {}", String::from_utf8_lossy(&demote.stderr));

    let promote = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "--agent", "alice", "promote", "WI-001"])
        .output().unwrap();
    assert!(promote.status.success(),
        "promote failed: {}", String::from_utf8_lossy(&promote.stderr));

    let workitems = std::fs::read_to_string(
        proj.join("anthill-todo").join("workitems.anthill")).unwrap();
    assert!(workitems.contains("status: Open"),
        "should be back to Open: {workitems}");
    assert!(!workitems.contains("PreOpened"),
        "no PreOpened block should remain after promote: {workitems}");
}

#[test]
fn preopen_unknown_id_errors() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, "");
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "preopen", "WI-999"])
        .output().unwrap();
    assert_eq!(out.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("WI-999") && stderr.contains("not found"),
        "expected diagnostic, got: {stderr}");
}
