//! WI-009 (bundle catalogue): `list --tag` through the `--anthill` bundle —
//! the named-list sequence view (topo order, `(blocked: …)`, `<- next`,
//! `[missing]` rows), mirroring the native run_list_tagged byte for byte.

mod common;

use std::process::Command;

use common::setup_project;

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

/// WI-002 depends on WI-001; WI-003 depends on WI-002 THROUGH an untagged
/// view (WI-003 itself tagged, dep direct); WI-004 untagged. A Tag fact
/// also points at a missing id (data error — must stay visible).
const FIXTURE: &str = r#"
fact WorkItem(
  id: "WI-001",
  description: "base item",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)

fact WorkItem(
  id: "WI-002",
  description: "mid item",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: ["WI-001"],
  status: Open)

fact WorkItem(
  id: "WI-003",
  description: "top item",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: ["WI-002"],
  status: Open)

fact WorkItem(
  id: "WI-004",
  description: "untagged item",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)

fact Tag(workitem: "WI-003", name: "seq")
fact Tag(workitem: "WI-001", name: "seq")
fact Tag(workitem: "WI-002", name: "seq")
fact Tag(workitem: "WI-999", name: "seq")
"#;

fn run_bundle(proj: &std::path::Path, args: &[&str]) -> String {
    let mut full = vec!["-d", proj.to_str().unwrap(), "--anthill"];
    full.extend_from_slice(args);
    let out = Command::new(BIN).args(&full).output().expect("run anthill-todo");
    assert!(out.status.success(),
        "command failed: stderr={}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn run_native(proj: &std::path::Path, args: &[&str]) -> String {
    let mut full = vec!["-d", proj.to_str().unwrap()];
    full.extend_from_slice(args);
    let out = Command::new(BIN).args(&full).output().expect("run anthill-todo");
    assert!(out.status.success(),
        "command failed: stderr={}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8_lossy(&out.stdout).into_owned()
}

#[test]
fn tagged_view_orders_marks_next_and_blocked() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, FIXTURE);

    let stdout = run_bundle(&proj, &["list", "--tag", "seq"]);
    let expected = "tag 'seq' (4 item(s), sequence order):\n\
                    \x20 WI-001 [Open] base item  <- next\n\
                    \x20 WI-002 [Open] mid item (blocked: WI-001)\n\
                    \x20 WI-003 [Open] top item (blocked: WI-002)\n\
                    \x20 WI-999 [missing] (no such work item)\n\
                    4 item(s)\n";
    assert_eq!(stdout, expected);
}

/// The bundle output must equal the native path byte for byte — the
/// WI-009 parity bar for this subcommand.
#[test]
fn tagged_view_matches_native_byte_for_byte() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, FIXTURE);

    for args in [
        vec!["list", "--tag", "seq"],
        vec!["list", "--tag", "seq", "--status", "open"],
        vec!["list", "--tag", "seq", "--status", "OPEN"],
        vec!["list", "--tag", "absent"],
    ] {
        let bundle = run_bundle(&proj, &args);
        let native = run_native(&proj, &args);
        assert_eq!(bundle, native, "diverged for {args:?}");
    }
}

#[test]
fn tagged_view_status_filter_is_case_insensitive() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, FIXTURE);

    let stdout = run_bundle(&proj, &["list", "--tag", "seq", "--status", "OPEN"]);
    assert!(stdout.contains("WI-001 [Open]"), "stdout: {stdout}");
    // [missing] rows print regardless of the filter; 3 Open + 1 missing.
    assert!(stdout.ends_with("4 item(s)\n"), "stdout: {stdout}");
}

#[test]
fn empty_tag_reports_no_items() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, FIXTURE);

    let stdout = run_bundle(&proj, &["list", "--tag", "absent"]);
    assert_eq!(stdout, "No work items tagged 'absent'.\n");
}
