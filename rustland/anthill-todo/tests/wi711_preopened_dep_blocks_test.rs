//! WI-711: the `list` view derives its blocked/ready split from the KB
//! `dep_satisfied` rule (single source), not a hand-rolled status check.
//! These pin the load-bearing invariant: an Open item depending on a
//! PreOpened item is BLOCKED consistently across `list`, `next`, and
//! `--unblocked` — a PreOpened dependency is not Delivered/Verified, so it
//! never satisfies. A dep that IS Delivered leaves the dependent ready
//! (the control), and the blocked/ready split is status-agnostic, so a
//! PreOpened item with an unmet dep shows blocked under its OWN group.

mod common;

use std::process::Command;

use common::setup_project;

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

/// WI-001 is a PreOpened backlog premise with no deps (itself ready).
/// WI-002 (Open) depends on it → blocked (a PreOpened dep never satisfies).
/// WI-003 (Open) depends on the Delivered WI-004 → ready (the control).
/// WI-005 (PreOpened) depends on the still-Open WI-002 → blocked within the
/// PreOpened group (status-agnostic split).
const FIXTURE: &str = r#"
fact WorkItem(
  id: "WI-001",
  description: "preopened premise",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: PreOpened)

fact WorkItem(
  id: "WI-002",
  description: "depends on preopened premise",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: ["WI-001"],
  status: Open)

fact WorkItem(
  id: "WI-003",
  description: "dep already delivered",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: ["WI-004"],
  status: Open)

fact WorkItem(
  id: "WI-004",
  description: "delivered dep",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Delivered(agent: "claude", at: "2026-01-01T00:00:00Z"))

fact WorkItem(
  id: "WI-005",
  description: "preopened, depends on still-open WI-002",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: ["WI-002"],
  status: PreOpened)
"#;

fn run(proj: &std::path::Path, args: &[&str]) -> String {
    let mut full = vec!["-d", proj.to_str().unwrap()];
    full.extend_from_slice(args);
    let out = Command::new(BIN).args(&full).output().expect("run anthill-todo");
    assert!(out.status.success(),
        "command failed: stderr={}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// In `list`, the item depending on a PreOpened premise lands in the Open
/// group's `-- blocked --` section, while the item whose dep is Delivered
/// stays ready (above the blocked marker).
#[test]
fn preopened_dep_blocks_dependent_in_list() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, FIXTURE);

    let stdout = run(&proj, &["list"]);

    let open_hdr = stdout.find("Open:").expect("Open group header");
    // The blocked marker inside the Open group (the first one after "Open:").
    let blocked_idx = stdout[open_hdr..].find("-- blocked --")
        .map(|i| open_hdr + i)
        .expect("Open group has a blocked section");
    let wi002 = stdout.find("WI-002").expect("WI-002 shown");
    let wi003 = stdout.find("WI-003").expect("WI-003 shown");

    assert!(wi003 < blocked_idx,
        "WI-003 (dep Delivered) must be ready, above the blocked marker: {stdout}");
    assert!(wi002 > blocked_idx,
        "WI-002 (dep PreOpened) must be in the blocked section: {stdout}");
    assert!(stdout.contains("WI-001 [PreOpened]"),
        "the PreOpened premise still lists: {stdout}");
}

/// `next` offers the ready item and never the one blocked by a PreOpened dep.
#[test]
fn preopened_dep_excludes_dependent_from_next() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, FIXTURE);

    let stdout = run(&proj, &["next", "--all"]);
    assert!(stdout.contains("WI-003"),
        "the ready item (dep Delivered) is claimable: {stdout}");
    assert!(!stdout.contains("WI-002"),
        "the PreOpened-blocked item must not be offered: {stdout}");
    assert!(!stdout.contains("WI-001"),
        "a PreOpened item is not itself claimable: {stdout}");
}

/// `list --unblocked` drops the PreOpened-blocked item, keeps the ready one.
#[test]
fn preopened_dep_hidden_under_unblocked() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, FIXTURE);

    let stdout = run(&proj, &["list", "--unblocked"]);
    assert!(!stdout.contains("WI-002"),
        "blocked-by-PreOpened item is dropped: {stdout}");
    assert!(stdout.contains("WI-003 [Open]"),
        "the ready item (dep Delivered) is kept: {stdout}");
}

/// The blocked/ready split is status-agnostic: a PreOpened item with an
/// unmet dependency shows blocked within the PreOpened group, and there are
/// two blocked sections (one per group), while the depless PreOpened premise
/// stays ready. Locks the every-group behavior the KB rule now matches.
#[test]
fn blocked_split_is_status_agnostic_across_groups() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, FIXTURE);

    let stdout = run(&proj, &["list"]);
    assert_eq!(stdout.matches("-- blocked --").count(), 2,
        "one blocked section in the Open group and one in the PreOpened group: {stdout}");
    let preopen_hdr = stdout.find("PreOpened:").expect("PreOpened group header");
    let tail = &stdout[preopen_hdr..];
    let blocked_idx = tail.find("-- blocked --").expect("PreOpened group blocked section");
    let wi001 = tail.find("WI-001").expect("WI-001 in PreOpened group");
    let wi005 = tail.find("WI-005").expect("WI-005 in PreOpened group");
    assert!(wi001 < blocked_idx,
        "the depless PreOpened premise WI-001 is ready: {stdout}");
    assert!(wi005 > blocked_idx,
        "WI-005 (unmet dep) is blocked within the PreOpened group: {stdout}");
}
