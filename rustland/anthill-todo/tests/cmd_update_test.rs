//! WI-267 Phase B4: cmd_update / cmd_add_dependency / cmd_remove_dependency
//! integration tests against the bundle.

mod common;

use std::process::Command;

use common::{read_combined, setup_project, workitem_block_contains};

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

const TWO_OPEN_WIS: &str = "\
fact WorkItem(
  id: \"WI-001\",
  description: \"first\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Open)

fact WorkItem(
  id: \"WI-002\",
  description: \"second\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Open)
";

#[test]
fn update_description_rewrites_workitem() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, TWO_OPEN_WIS);
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "update", "WI-001", "--description", "rewritten"])
        .output().unwrap();
    assert!(out.status.success(),
        "update failed: {}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("updated WI-001: description"), "stdout: {stdout}");

    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(combined.contains("description: some(value: \"rewritten\")"),
        "new description not persisted: {combined}");
    assert!(!combined.contains("some(value: \"first\")"),
        "old description lingered: {combined}");
}

#[test]
fn update_acceptance_replaces_list() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, TWO_OPEN_WIS);
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "update", "WI-001", "--acceptance", "rustfmt"])
        .output().unwrap();
    assert!(out.status.success(),
        "update failed: {}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("updated WI-001: acceptance"), "stdout: {stdout}");

    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(combined.contains("ToolPasses(tool: \"rustfmt\""),
        "new acceptance not persisted: {combined}");
}

#[test]
fn update_no_flags_errors() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, TWO_OPEN_WIS);
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "update", "WI-001"])
        .output().unwrap();
    assert!(!out.status.success(), "expected failure for no-flags update");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("nothing to change"),
        "unexpected stderr: {stderr}");
}

#[test]
fn update_unknown_id_errors() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, TWO_OPEN_WIS);
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "update", "WI-999", "--description", "ignored"])
        .output().unwrap();
    assert!(!out.status.success(), "expected failure for missing id");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("WI-999"), "unexpected stderr: {stderr}");
}

#[test]
fn add_dependency_appends_to_depends_on() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, TWO_OPEN_WIS);
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "add-dependency", "WI-002", "WI-001"])
        .output().unwrap();
    assert!(out.status.success(),
        "add-dependency failed: {}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("added dependency: WI-002 -> WI-001"),
        "stdout: {stdout}");

    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(combined.contains("\"WI-001\""), "WI-001 ref missing: {combined}");
    assert!(workitem_block_contains(&combined, "WI-002", "WI-001"),
        "WI-002.depends_on missing WI-001 ref: {combined}");
}

#[test]
fn add_dependency_self_loop_errors() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, TWO_OPEN_WIS);
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "add-dependency", "WI-001", "WI-001"])
        .output().unwrap();
    assert!(!out.status.success(), "expected failure for self-loop");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("cannot depend on itself"),
        "unexpected stderr: {stderr}");
}

#[test]
fn add_dependency_unknown_target_errors() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, TWO_OPEN_WIS);
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "add-dependency", "WI-001", "WI-999"])
        .output().unwrap();
    assert!(!out.status.success(), "expected failure for missing target");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("WI-999"), "unexpected stderr: {stderr}");
}

#[test]
fn remove_dependency_filters_out_dep() {
    // Start with WI-002 depending on WI-001, then remove the link.
    let project_text = "\
fact WorkItem(
  id: \"WI-001\",
  description: \"first\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Open)

fact WorkItem(
  id: \"WI-002\",
  description: \"second\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [\"WI-001\"],
  status: Open)
";
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, project_text);
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "remove-dependency", "WI-002", "WI-001"])
        .output().unwrap();
    assert!(out.status.success(),
        "remove-dependency failed: {}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("removed dependency: WI-002 -> WI-001"),
        "stdout: {stdout}");

    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(!workitem_block_contains(&combined, "WI-002", "WI-001"),
        "WI-002 still depends on WI-001 after remove: {combined}");
}

#[test]
fn remove_dependency_not_present_errors() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_project(&tmp, TWO_OPEN_WIS);
    let out = Command::new(BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "remove-dependency", "WI-001", "WI-002"])
        .output().unwrap();
    assert!(!out.status.success(), "expected failure for missing dep link");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("does not depend on"),
        "unexpected stderr: {stderr}");
}

