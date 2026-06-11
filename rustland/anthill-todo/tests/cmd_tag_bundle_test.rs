//! WI-009 (bundle catalogue): `tag` / `untag` through the `--anthill` bundle
//! path — the WI-388 named-list primitives previously implemented only in the
//! native (clap) CLI. Mirrors `cmd_tag_test`'s native cases and adds
//! CROSS-PATH interop: both paths now target workitems.anthill (the
//! bundle store's SingleFile convention; native appends directly), and
//! both read every project .anthill file, so each must see and remove
//! the other's Tag facts.

mod common;

use std::process::Command;

use common::{read_combined, setup_project};

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

const TWO_ITEMS: &str = r#"
fact WorkItem(
  id: "WI-001",
  description: "base item",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)

fact WorkItem(
  id: "WI-002",
  description: "second item",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)
"#;

fn run_bundle(proj: &std::path::Path, args: &[&str]) -> std::process::Output {
    let mut full = vec!["-d", proj.to_str().unwrap(), "--anthill"];
    full.extend_from_slice(args);
    Command::new(BIN).args(&full).output().expect("run anthill-todo")
}

fn run_native(proj: &std::path::Path, args: &[&str]) -> std::process::Output {
    let mut full = vec!["-d", proj.to_str().unwrap()];
    full.extend_from_slice(args);
    Command::new(BIN).args(&full).output().expect("run anthill-todo")
}

fn ok(out: &std::process::Output) -> String {
    assert!(
        out.status.success(),
        "command failed: stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn err(out: &std::process::Output) -> String {
    assert!(!out.status.success(), "command unexpectedly succeeded");
    String::from_utf8_lossy(&out.stderr).into_owned()
}

#[test]
fn bundle_tag_persists_and_reports() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, TWO_ITEMS);

    let stdout = ok(&run_bundle(&proj, &["tag", "WI-001", "typing"]));
    assert!(stdout.contains("tagged: WI-001 +typing"), "stdout: {stdout}");

    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(combined.contains("fact Tag("), "no Tag fact written: {combined}");
    assert!(combined.contains("workitem: \"WI-001\""));
    assert!(combined.contains("name: \"typing\""));

    // The SingleFile convention targets the legacy layout: the persisted
    // fact must land in workitems.anthill itself, not a side facts.anthill.
    let workitems = std::fs::read_to_string(proj.join("anthill-todo/workitems.anthill"))
        .expect("read workitems.anthill");
    assert!(
        workitems.contains("fact Tag("),
        "Tag fact not in workitems.anthill: {workitems}"
    );
    assert!(
        !proj.join("anthill-todo/facts.anthill").exists(),
        "facts.anthill should not be created"
    );
}

#[test]
fn bundle_duplicate_tag_errors() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, TWO_ITEMS);

    ok(&run_bundle(&proj, &["tag", "WI-001", "typing"]));
    let stderr = err(&run_bundle(&proj, &["tag", "WI-001", "typing"]));
    assert!(
        stderr.contains("error: 'WI-001' is already tagged 'typing'"),
        "stderr: {stderr}"
    );
}

#[test]
fn bundle_tag_unknown_item_errors() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, TWO_ITEMS);

    let stderr = err(&run_bundle(&proj, &["tag", "WI-999", "typing"]));
    assert!(
        stderr.contains("error: work item 'WI-999' not found"),
        "stderr: {stderr}"
    );
}

#[test]
fn bundle_untag_removes_the_fact() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, TWO_ITEMS);

    ok(&run_bundle(&proj, &["tag", "WI-001", "typing"]));
    let stdout = ok(&run_bundle(&proj, &["untag", "WI-001", "typing"]));
    assert!(stdout.contains("untagged: WI-001 -typing"), "stdout: {stdout}");

    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(!combined.contains("fact Tag("), "Tag fact survived: {combined}");
}

#[test]
fn bundle_untag_without_tag_errors() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, TWO_ITEMS);

    let stderr = err(&run_bundle(&proj, &["untag", "WI-001", "typing"]));
    assert!(
        stderr.contains("error: 'WI-001' is not tagged 'typing'"),
        "stderr: {stderr}"
    );
}

/// Native-written tag (workitems.anthill, `name` field first) must be
/// visible to and removable by the bundle path.
#[test]
fn native_tag_bundle_untag_interop() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, TWO_ITEMS);

    ok(&run_native(&proj, &["tag", "WI-001", "typing"]));
    let stdout = ok(&run_bundle(&proj, &["untag", "WI-001", "typing"]));
    assert!(stdout.contains("untagged: WI-001 -typing"), "stdout: {stdout}");

    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(!combined.contains("fact Tag("), "Tag fact survived: {combined}");
}

/// Bundle-written tag must be visible to and removable by the native path.
#[test]
fn bundle_tag_native_untag_interop() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, TWO_ITEMS);

    ok(&run_bundle(&proj, &["tag", "WI-001", "typing"]));
    let stdout = ok(&run_native(&proj, &["untag", "WI-001", "typing"]));
    assert!(stdout.contains("untagged: WI-001 -typing"), "stdout: {stdout}");

    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(!combined.contains("fact Tag("), "Tag fact survived: {combined}");
}
