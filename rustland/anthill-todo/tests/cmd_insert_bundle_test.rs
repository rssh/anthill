//! WI-009 (bundle catalogue): `add --tag` and `insert` through the
//! `--anthill` bundle path — the remaining WI-388 mutating primitives.
//! `insert <desc> --before <id>` creates the item, tags it, and makes
//! the --before target depend on it; a --depends that is (or reaches)
//! the target is a cycle and rejected loudly, BEFORE anything persists.

mod common;

use std::process::Command;

use common::{read_combined, setup_project};

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

const THREE_ITEMS: &str = r#"
fact WorkItem(
  id: "WI-001",
  description: "base item",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)

fact WorkItem(
  id: "WI-002",
  description: "depends on 001",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: ["WI-001"],
  status: Open)

fact WorkItem(
  id: "WI-003",
  description: "independent",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)
"#;

fn run_bundle(proj: &std::path::Path, args: &[&str]) -> std::process::Output {
    let mut full = vec!["-d", proj.to_str().unwrap(), "--anthill"];
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
fn add_with_tags_persists_tag_facts_and_notes_them() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);

    let stdout = ok(&run_bundle(
        &proj,
        &["add", "tagged item", "--tag", "typing", "--tag", "infra"],
    ));
    assert!(
        stdout.contains("added: WI-004 — tagged item [tags: typing, infra]"),
        "stdout: {stdout}"
    );

    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(combined.contains("workitem: \"WI-004\""), "{combined}");
    assert!(combined.contains("name: \"typing\""), "{combined}");
    assert!(combined.contains("name: \"infra\""), "{combined}");
}

#[test]
fn insert_creates_tags_and_rewires_the_before_target() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);

    let stdout = ok(&run_bundle(
        &proj,
        &["insert", "prereq work", "--before", "WI-002", "--tag", "typing"],
    ));
    assert!(
        stdout.contains(
            "inserted: WI-004 before WI-002 [tags: typing] (WI-002 now depends on WI-004)"
        ),
        "stdout: {stdout}"
    );

    let combined = read_combined(&proj.join("anthill-todo"));
    // The new item exists, is tagged, and WI-002's deps now include it
    // (alongside the original WI-001).
    assert!(combined.contains("prereq work"), "{combined}");
    assert!(combined.contains("workitem: \"WI-004\""), "{combined}");
    let wi002 = combined
        .split("fact WorkItem(")
        .find(|b| b.contains("\"WI-002\""))
        .expect("WI-002 block");
    assert!(wi002.contains("WI-001") && wi002.contains("WI-004"),
        "WI-002 deps should hold both: {wi002}");
}

#[test]
fn insert_with_before_equal_dep_rejects_cycle() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);

    let stderr = err(&run_bundle(
        &proj,
        &["insert", "bad", "--before", "WI-001", "--depends", "WI-001"],
    ));
    assert!(
        stderr.contains(
            "error: inserting before WI-001 with dependency WI-001 would create a cycle"
        ),
        "stderr: {stderr}"
    );
    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(!combined.contains("\"bad\""), "nothing should persist: {combined}");
}

/// WI-002 depends on WI-001, so inserting before WI-001 with a dependency
/// on WI-002 closes a transitive cycle.
#[test]
fn insert_with_transitive_cycle_rejects() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);

    let stderr = err(&run_bundle(
        &proj,
        &["insert", "bad", "--before", "WI-001", "--depends", "WI-002"],
    ));
    assert!(
        stderr.contains(
            "error: inserting before WI-001 with dependency WI-002 would create a cycle"
        ),
        "stderr: {stderr}"
    );
}

#[test]
fn insert_unknown_before_errors() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);

    let stderr = err(&run_bundle(&proj, &["insert", "x", "--before", "WI-999"]));
    assert!(
        stderr.contains("error: --before target 'WI-999' not found"),
        "stderr: {stderr}"
    );
}
