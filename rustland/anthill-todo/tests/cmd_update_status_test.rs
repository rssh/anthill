//! WI-395 `update --status <Status>`: the general status-correction
//! route. Unlike the targeted claim/unclaim/deliver/verify/preopen/promote
//! commands (each valid only from one source status), `update --status`
//! sets ANY lifecycle status directly — reverting a mistaken Delivered,
//! un-verifying, or marking Rejected/Stale. Agent + timestamp are stamped
//! exactly as claim/deliver/verify do; id/depends_on are preserved; an
//! unknown status or a reason-carrying status without --reason fails
//! loudly and writes nothing.

mod common;

use std::process::Command;

use common::{read_combined, setup_project, workitem_block_contains};

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

const DELIVERED_WI: &str = "\
fact WorkItem(
  id: \"WI-001\",
  description: \"delivered by mistake\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [\"WI-000\"],
  status: Delivered(agent: \"alice\", at: \"2026-05-02T00:00:00Z\"))
";

const CLAIMED_WI: &str = "\
fact WorkItem(
  id: \"WI-001\",
  description: \"claimed item\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Claimed(agent: \"alice\", since: \"2026-05-01T00:00:00Z\"))
";

const OPEN_WI: &str = "\
fact WorkItem(
  id: \"WI-001\",
  description: \"open item\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Open)
";

/// The motivating case: an item delivered by mistake reverted to Claimed.
/// The new Claimed carries the --agent and a fresh timestamp; the old
/// Delivered block (with its unique timestamp) is gone; depends_on stays.
#[test]
fn status_reverts_delivered_to_claimed() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, DELIVERED_WI);
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "--agent", "bob", "update", "WI-001", "--status", "Claimed"])
        .output().unwrap();
    assert!(out.status.success(),
        "update failed: {}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("updated WI-001: status"), "stdout: {stdout}");

    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(combined.contains("Claimed(agent: \"bob\""),
        "Claimed-by-bob not persisted: {combined}");
    assert!(!combined.contains("2026-05-02T00:00:00Z"),
        "old Delivered timestamp lingered: {combined}");
    // id + depends_on preserved through the rebuild.
    assert!(workitem_block_contains(&combined, "WI-001", "WI-000"),
        "depends_on WI-000 lost: {combined}");
}

/// `--status Open` from Claimed clears the claimant — the same end state
/// as `unclaim`, reached via the general route.
#[test]
fn status_open_clears_claimant() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, CLAIMED_WI);
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "update", "WI-001", "--status", "Open"])
        .output().unwrap();
    assert!(out.status.success(),
        "update failed: {}", String::from_utf8_lossy(&out.stderr));

    // Inspect workitems.anthill specifically — rules.anthill mentions
    // Claimed in rule patterns and would defeat a blanket assertion.
    let workitems = std::fs::read_to_string(
        proj.join("anthill-todo").join("workitems.anthill")).unwrap();
    assert!(workitems.contains("status: Open"),
        "should be Open now: {workitems}");
    assert!(!workitems.contains("Claimed"),
        "no Claimed block should remain: {workitems}");
}

/// `--status Verified` stamps a timestamp but no agent (mirrors `verify`).
#[test]
fn status_verified_stamps_timestamp_only() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, DELIVERED_WI);
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "--agent", "bob", "update", "WI-001", "--status", "Verified"])
        .output().unwrap();
    assert!(out.status.success(),
        "update failed: {}", String::from_utf8_lossy(&out.stderr));
    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(combined.contains("status: Verified(at:"),
        "Verified not persisted: {combined}");
    // Verified carries no agent field, so bob must not appear in the status.
    assert!(!combined.contains("Verified(at: \"") || !combined.contains("bob"),
        "Verified should not record an agent: {combined}");
}

/// Status names are case-insensitive.
#[test]
fn status_name_is_case_insensitive() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, CLAIMED_WI);
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "update", "WI-001", "--status", "open"])
        .output().unwrap();
    assert!(out.status.success(),
        "lowercase status name rejected: {}", String::from_utf8_lossy(&out.stderr));
    let workitems = std::fs::read_to_string(
        proj.join("anthill-todo").join("workitems.anthill")).unwrap();
    assert!(workitems.contains("status: Open"), "not Open: {workitems}");
}

/// A reason-carrying status with --reason persists the reason + timestamp.
#[test]
fn status_rejected_with_reason_persists() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, OPEN_WI);
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "update", "WI-001", "--status", "Rejected",
               "--reason", "superseded by WI-002"])
        .output().unwrap();
    assert!(out.status.success(),
        "update failed: {}", String::from_utf8_lossy(&out.stderr));
    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(combined.contains("Rejected(reason: \"superseded by WI-002\""),
        "Rejected reason not persisted: {combined}");
}

/// A reason-carrying status WITHOUT --reason fails loudly (exit 2) and
/// leaves the item untouched — no empty-reason rejection slips through.
#[test]
fn status_rejected_without_reason_errors_and_writes_nothing() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, OPEN_WI);
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "update", "WI-001", "--status", "Rejected"])
        .output().unwrap();
    assert_eq!(out.status.code(), Some(2),
        "expected exit 2; stderr={}", String::from_utf8_lossy(&out.stderr));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("--reason"),
        "diagnostic should mention --reason: {stderr}");
    // Inspect workitems.anthill specifically — domain.anthill *defines*
    // `entity Rejected(...)`, so read_combined would always see "Rejected".
    let workitems = std::fs::read_to_string(
        proj.join("anthill-todo").join("workitems.anthill")).unwrap();
    assert!(workitems.contains("status: Open"),
        "item should be untouched (still Open): {workitems}");
    assert!(!workitems.contains("Rejected"),
        "no Rejected should have been written: {workitems}");
}

/// An unknown status name fails loudly (exit 2), names the valid options,
/// and writes nothing.
#[test]
fn status_unknown_name_errors_and_writes_nothing() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, OPEN_WI);
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "update", "WI-001", "--status", "Frobnicate"])
        .output().unwrap();
    assert_eq!(out.status.code(), Some(2),
        "expected exit 2; stderr={}", String::from_utf8_lossy(&out.stderr));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("unknown status") && stderr.contains("Frobnicate"),
        "expected unknown-status diagnostic, got: {stderr}");
    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(combined.contains("status: Open"),
        "item should be untouched: {combined}");
}

/// `--description` and `--status` combine in one atomic replace; the
/// summary line lists both changed fields.
#[test]
fn description_and_status_combine() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, CLAIMED_WI);
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "update", "WI-001", "--description", "reworded", "--status", "Open"])
        .output().unwrap();
    assert!(out.status.success(),
        "update failed: {}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("updated WI-001: description, status"),
        "summary should list both fields: {stdout}");
    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(combined.contains("some(value: \"reworded\")"),
        "new description not persisted: {combined}");
    let workitems = std::fs::read_to_string(
        proj.join("anthill-todo").join("workitems.anthill")).unwrap();
    assert!(workitems.contains("status: Open") && !workitems.contains("Claimed"),
        "status should be Open: {workitems}");
}

/// A stray `--reason` on a non-reason status fails loudly (exit 2) rather
/// than being silently dropped — the item is left untouched.
#[test]
fn status_reason_on_non_reason_status_errors() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, CLAIMED_WI);
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "update", "WI-001", "--status", "Open", "--reason", "oops"])
        .output().unwrap();
    assert_eq!(out.status.code(), Some(2),
        "expected exit 2; stderr={}", String::from_utf8_lossy(&out.stderr));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("--reason"),
        "diagnostic should mention --reason: {stderr}");
    // Untouched: still Claimed, no Open written.
    let workitems = std::fs::read_to_string(
        proj.join("anthill-todo").join("workitems.anthill")).unwrap();
    assert!(workitems.contains("Claimed"),
        "item should be untouched (still Claimed): {workitems}");
}

/// A `--reason` with no `--status` at all fails loudly (exit 2) rather than
/// silently ignoring the flag.
#[test]
fn status_reason_without_status_errors() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, OPEN_WI);
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "update", "WI-001", "--description", "x", "--reason", "oops"])
        .output().unwrap();
    assert_eq!(out.status.code(), Some(2),
        "expected exit 2; stderr={}", String::from_utf8_lossy(&out.stderr));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("--reason"),
        "diagnostic should mention --reason: {stderr}");
}

/// `update --status` on a missing id errors (exit 1).
#[test]
fn status_unknown_id_errors() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, "");
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "update", "WI-999", "--status", "Open"])
        .output().unwrap();
    assert_eq!(out.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("WI-999") && stderr.contains("not found"),
        "expected diagnostic, got: {stderr}");
}
