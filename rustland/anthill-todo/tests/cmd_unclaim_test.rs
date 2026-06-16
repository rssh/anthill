//! WI-310 `unclaim <id>`: Claimed → Open, the inverse of `claim`. Same
//! retract+assert atomic-replace path as cmd_claim (the Claimed block is
//! dropped and an Open replacement lands in the SAME workitems.anthill).
//! Only valid from Claimed — any other status errors clearly (exit 1) and
//! writes nothing.

mod common;

use std::process::Command;

use common::{read_combined, setup_project};

const ANTHILL_TODO_BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

const SINGLE_CLAIMED_WI: &str = "\
fact WorkItem(
  id: \"WI-001\",
  description: \"claimed item\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Claimed(agent: \"alice\", since: \"2026-05-01T00:00:00Z\"))
";

const SINGLE_OPEN_WI: &str = "\
fact WorkItem(
  id: \"WI-001\",
  description: \"open item\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Open)
";

#[test]
fn unclaim_replaces_claimed_with_open() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, SINGLE_CLAIMED_WI);
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "--agent", "bob", "unclaim", "WI-001"])
        .output().unwrap();
    assert!(out.status.success(),
        "unclaim failed: {}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("unclaimed: WI-001 by bob"),
        "stdout: {stdout}");

    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(combined.contains("\"WI-001\""), "WI-001 lost: {combined}");
    assert!(combined.contains("status: Open"),
        "Open replacement not present: {combined}");
    // The old Claimed block's unique since-timestamp must be gone (atomic
    // replace dropped it, not left a stale duplicate).
    assert!(!combined.contains("2026-05-01T00:00:00Z"),
        "old Claimed block lingered: {combined}");
}

#[test]
fn unclaim_on_open_item_errors_and_writes_nothing() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, SINGLE_OPEN_WI);
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "unclaim", "WI-001"])
        .output().unwrap();
    assert_eq!(out.status.code(), Some(1),
        "expected exit 1 on a non-Claimed item; stderr={}",
        String::from_utf8_lossy(&out.stderr));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("WI-001") && stderr.contains("not claimed"),
        "expected a clear 'not claimed' diagnostic, got: {stderr}");
    // It must mention the actual status so the user knows why.
    assert!(stderr.contains("Open"),
        "diagnostic should name the current status: {stderr}");
}

#[test]
fn unclaim_unknown_id_errors() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, "");
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "unclaim", "WI-999"])
        .output().unwrap();
    assert_eq!(out.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("WI-999") && stderr.contains("not found"),
        "expected diagnostic, got: {stderr}");
}

/// Round-trip: claim then unclaim returns the item to a claimable Open
/// state (the whole point — releasing a claim back to the queue).
#[test]
fn claim_then_unclaim_round_trips_to_open() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, SINGLE_OPEN_WI);

    let claim = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "--agent", "alice", "claim", "WI-001"])
        .output().unwrap();
    assert!(claim.status.success(),
        "claim failed: {}", String::from_utf8_lossy(&claim.stderr));

    let unclaim = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "--agent", "alice", "unclaim", "WI-001"])
        .output().unwrap();
    assert!(unclaim.status.success(),
        "unclaim failed: {}", String::from_utf8_lossy(&unclaim.stderr));

    // Check workitems.anthill specifically (not read_combined, which also
    // pulls in rules.anthill — that file mentions `Claimed` in its rule
    // patterns and would defeat a blanket "no Claimed" assertion).
    let workitems = std::fs::read_to_string(
        proj.join("anthill-todo").join("workitems.anthill")).unwrap();
    assert!(workitems.contains("status: Open"),
        "should be back to Open: {workitems}");
    assert!(!workitems.contains("Claimed"),
        "no Claimed block should remain in workitems after unclaim: {workitems}");
}
