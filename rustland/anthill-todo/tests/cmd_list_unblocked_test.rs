//! `list --unblocked`: narrow the listing to items whose dependencies are all
//! satisfied (Delivered/Verified). Covers the plain grouped view and the
//! `--tag` sequence view, plus the interaction with `--status`/`--all`.

mod common;

use std::process::Command;

use common::setup_project;

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

/// WI-002 is blocked on the still-Open WI-001; WI-003 is independent; WI-004
/// depends on WI-005 which is already Delivered, so WI-004 is unblocked. The
/// `seq` tag covers WI-001..WI-003 and points at a missing WI-999.
const FIXTURE: &str = r#"
fact WorkItem(
  id: "WI-001",
  description: "base item",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)

fact WorkItem(
  id: "WI-002",
  description: "blocked on WI-001",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: ["WI-001"],
  status: Open)

fact WorkItem(
  id: "WI-003",
  description: "independent open",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)

fact WorkItem(
  id: "WI-004",
  description: "dep already delivered",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: ["WI-005"],
  status: Open)

fact WorkItem(
  id: "WI-005",
  description: "delivered dep",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Delivered)

fact Tag(workitem: "WI-001", name: "seq")
fact Tag(workitem: "WI-002", name: "seq")
fact Tag(workitem: "WI-003", name: "seq")
fact Tag(workitem: "WI-999", name: "seq")
"#;

fn run(proj: &std::path::Path, args: &[&str]) -> String {
    let mut full = vec!["-d", proj.to_str().unwrap()];
    full.extend_from_slice(args);
    let out = Command::new(BIN).args(&full).output().expect("run anthill-todo");
    assert!(out.status.success(),
        "command failed: stderr={}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8_lossy(&out.stdout).into_owned()
}

#[test]
fn plain_unblocked_drops_blocked_rows_keeps_deps_met() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, FIXTURE);

    let stdout = run(&proj, &["list", "--unblocked"]);
    // WI-002 (dep WI-001 still Open) is dropped; WI-004 (dep WI-005 Delivered)
    // stays. No `-- blocked --` section is emitted.
    assert!(stdout.contains("WI-001 [Open]"), "stdout: {stdout}");
    assert!(stdout.contains("WI-003 [Open]"), "stdout: {stdout}");
    assert!(stdout.contains("WI-004 [Open]"), "stdout: {stdout}");
    assert!(!stdout.contains("WI-002"), "blocked WI-002 must be hidden: {stdout}");
    assert!(!stdout.contains("-- blocked --"),
        "no blocked section under --unblocked: {stdout}");
    assert!(stdout.ends_with("3 item(s)\n"), "stdout: {stdout}");
}

#[test]
fn plain_unblocked_reports_none_when_all_blocked() {
    let tmp = tempfile::tempdir().expect("tempdir");
    // A mutual/dangling block: nothing is ever unblocked.
    let proj = setup_project(&tmp, r#"
fact WorkItem(
  id: "WI-010",
  description: "blocked on undelivered dep",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: ["WI-011"],
  status: Open)

fact WorkItem(
  id: "WI-011",
  description: "also open",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: ["WI-010"],
  status: Open)
"#);

    let stdout = run(&proj, &["list", "--unblocked"]);
    assert_eq!(stdout, "No work items found.\n");
}

#[test]
fn tagged_unblocked_narrows_sequence_and_drops_missing() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, FIXTURE);

    let stdout = run(&proj, &["list", "--tag", "seq", "--unblocked"]);
    // Blocked WI-002 and the dangling WI-999 are both dropped; header and
    // footer counts agree on the narrowed set.
    let expected = "tag 'seq' (2 item(s), sequence order):\n\
                    \x20 WI-001 [Open] base item  <- next\n\
                    \x20 WI-003 [Open] independent open\n\
                    2 item(s)\n";
    assert_eq!(stdout, expected);
}

#[test]
fn unblocked_composes_with_all_flag() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, FIXTURE);

    // --all surfaces the Delivered WI-005 (no deps → unblocked); the blocked
    // WI-002 stays hidden.
    let stdout = run(&proj, &["list", "--unblocked", "--all"]);
    assert!(stdout.contains("WI-005 [Delivered]"), "stdout: {stdout}");
    assert!(!stdout.contains("WI-002"), "stdout: {stdout}");
    assert!(stdout.ends_with("4 item(s)\n"), "stdout: {stdout}");
}
