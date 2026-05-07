//! WI-009 phase 3 status transitions: cmd_deliver, cmd_verify, cmd_delete.
//! Same retract+assert pattern as cmd_claim, parameterised on the new
//! status entity (or no replacement, for delete).

mod common;

use std::fs;
use std::process::Command;

use common::setup_project;

const ANTHILL_TODO_BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

const SINGLE_CLAIMED_WI: &str = "\
fact WorkItem(
  id: \"WI-001\",
  description: \"to deliver\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Claimed(agent: \"alice\", since: \"2026-05-01T00:00:00Z\"))
";

const SINGLE_DELIVERED_WI: &str = "\
fact WorkItem(
  id: \"WI-001\",
  description: \"to verify\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Delivered(agent: \"alice\", at: \"2026-05-02T00:00:00Z\"))
";

const SINGLE_OPEN_WI: &str = "\
fact WorkItem(
  id: \"WI-001\",
  description: \"to delete\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Open)
";

fn read_combined(inner: &std::path::Path) -> String {
    let mut combined = String::new();
    for entry in fs::read_dir(inner).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().and_then(|s| s.to_str()) == Some("anthill") {
            combined.push_str(&fs::read_to_string(&path).unwrap());
        }
    }
    combined
}

#[test]
fn deliver_replaces_claimed_with_delivered() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, SINGLE_CLAIMED_WI);
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "--agent", "bob", "deliver", "WI-001"])
        .output().unwrap();
    assert!(out.status.success(),
        "deliver failed: {}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("delivered: WI-001 by bob"),
        "stdout: {stdout}");

    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(combined.contains("\"WI-001\""), "WI-001 lost: {combined}");
    assert!(combined.contains("agent: \"bob\""),
        "Delivered fact with bob not present: {combined}");
    // Old Claimed block's unique since-timestamp must be gone.
    assert!(!combined.contains("2026-05-01T00:00:00Z"),
        "old Claimed block lingered: {combined}");
}

#[test]
fn verify_replaces_delivered_with_verified() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, SINGLE_DELIVERED_WI);
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "verify", "WI-001"])
        .output().unwrap();
    assert!(out.status.success(),
        "verify failed: {}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("verified: WI-001"),
        "stdout: {stdout}");

    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(combined.contains("Verified"), "Verified missing: {combined}");
    // The retract-target's Delivered timestamp is unique enough to
    // disambiguate from rule-pattern occurrences in domain/rules.
    assert!(!combined.contains("2026-05-02T00:00:00Z"),
        "old Delivered fact lingered: {combined}");
}

#[test]
fn delete_drops_workitem_from_disk() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, SINGLE_OPEN_WI);
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "delete", "WI-001"])
        .output().unwrap();
    assert!(out.status.success(),
        "delete failed: {}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("deleted: WI-001"),
        "stdout: {stdout}");

    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(!combined.contains("\"WI-001\""),
        "WI-001 still present after delete: {combined}");
}

#[test]
fn deliver_unknown_id_errors() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, "");
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "deliver", "WI-999"])
        .output().unwrap();
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("WI-999") && stderr.contains("not found"),
        "expected diagnostic, got: {stderr}");
}

#[test]
fn verify_unknown_id_errors() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, "");
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "verify", "WI-999"])
        .output().unwrap();
    assert!(!out.status.success());
}

#[test]
fn delete_unknown_id_errors() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, "");
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "delete", "WI-999"])
        .output().unwrap();
    assert!(!out.status.success());
}
