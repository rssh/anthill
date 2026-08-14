//! A work item id is the key every command reads by, so two records sharing
//! one is a broken store — and it used to break SILENTLY: `chrono_topo`'s
//! id-keyed emit walk dropped the second record from every listing while the
//! footer still counted it, and `show <id>` answered whichever record sorted
//! first. This repo carried exactly that for months (`WI-169` named two
//! unrelated items, both Delivered, so both landed in one status group; the
//! listing printed 1088 rows under a `1089 item(s)` footer). `main` now
//! refuses ahead of dispatch.
//!
//! CONTROL. `duplicate_id_refuses_before_any_command` and
//! `the_refusal_names_the_offending_id` fail with the gate backed out —
//! without it these commands exit 0 and quietly serve one of the two records.
//! `a_clean_store_passes_the_gate` and `the_gate_reads_ids_not_descriptions`
//! pass EITHER WAY by design: they pin that the gate does not false-positive,
//! which is the failure mode a too-eager check would introduce.

use std::process::Command;

use crate::common::setup_project;

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

/// Two unrelated records under one id — the WI-169 shape, reduced. Both are
/// Delivered on purpose: a shared STATUS is what makes the drop silent, since
/// the two rows then land in the same status group where the emit walk keys on
/// id alone.
const DUPLICATE: &str = r#"
fact WorkItem(
  id: "WI-001",
  description: "first record under this id",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Delivered(agent: "alice", at: "2026-01-01T00:00:00Z"))

fact WorkItem(
  id: "WI-001",
  description: "a wholly different item, same id",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Delivered(agent: "bob", at: "2026-02-02T00:00:00Z"))

fact WorkItem(
  id: "WI-002",
  description: "bystander",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)
"#;

/// Two separate collisions, one of them three records deep — the shape a
/// parallel-branch merge produces.
const MANY_DUPLICATES: &str = r#"
fact WorkItem(
  id: "WI-001",
  description: "first record under this id",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Delivered(agent: "alice", at: "2026-01-01T00:00:00Z"))

fact WorkItem(
  id: "WI-001",
  description: "second record, same id",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)

fact WorkItem(
  id: "WI-001",
  description: "third record, same id again",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)

fact WorkItem(
  id: "WI-002",
  description: "an unrelated second collision",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)

fact WorkItem(
  id: "WI-002",
  description: "its twin",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)
"#;

/// The same store with the collision resolved. Descriptions still MENTION a
/// repeated id in prose, which the gate must not mistake for a record.
const CLEAN: &str = r#"
fact WorkItem(
  id: "WI-001",
  description: "first record; supersedes the note in WI-001 above",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Delivered(agent: "alice", at: "2026-01-01T00:00:00Z"))

fact WorkItem(
  id: "WI-003",
  description: "renumbered away from WI-001, per the collision fix",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Delivered(agent: "bob", at: "2026-02-02T00:00:00Z"))

fact WorkItem(
  id: "WI-002",
  description: "bystander",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)
"#;

/// (exit code, stdout, stderr) — this suite is about the FAILURE path, so it
/// cannot use a helper that asserts success.
fn run(proj: &std::path::Path, args: &[&str]) -> (i32, String, String) {
    let mut full = vec!["-d", proj.to_str().unwrap()];
    full.extend_from_slice(args);
    let out = Command::new(BIN)
        .args(&full)
        .output()
        .expect("run anthill-todo");
    (
        out.status.code().expect("exit code"),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

/// Every id-keyed reader is broken by the collision, so the gate sits ahead of
/// dispatch rather than in any one command. Reads and writes alike.
#[test]
fn duplicate_id_refuses_before_any_command() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, DUPLICATE);

    for args in [
        vec!["list"],
        vec!["list", "--all"],
        vec!["show", "WI-001"],
        vec!["status"],
        vec!["next"],
        vec!["claim", "WI-002"],
    ] {
        let (code, stdout, _) = run(&proj, &args);
        assert_eq!(code, 2, "expected refusal for {args:?}, got stdout={stdout}");
        assert!(
            !stdout.contains("WI-002"),
            "the command must not run at all for {args:?}: {stdout}"
        );
    }
}

/// A refusal that does not say WHICH id collided leaves the reader to diff a
/// four-figure store by hand.
#[test]
fn the_refusal_names_the_offending_id() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, DUPLICATE);

    let (code, _, stderr) = run(&proj, &["list"]);

    assert_eq!(code, 2, "stderr={stderr}");
    assert!(
        stderr.contains("duplicate work item id") && stderr.contains("WI-001"),
        "the diagnostic names the id: {stderr}"
    );
    assert!(
        stderr.contains("workitems.anthill"),
        "the diagnostic says where to fix it: {stderr}"
    );
}

/// A merge between parallel branches lands SEVERAL collisions at once, which
/// is the cause the gate exists for. Reporting one per run would charge a
/// refuse / hand-edit / re-run cycle each, so one run names them all — and an
/// id carrying three records names itself once, not twice.
#[test]
fn every_collision_is_reported_in_one_run() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, MANY_DUPLICATES);

    let (code, _, stderr) = run(&proj, &["list"]);

    assert_eq!(code, 2, "stderr={stderr}");
    assert!(
        stderr.contains("WI-001") && stderr.contains("WI-002"),
        "both collisions in one run: {stderr}"
    );
    assert_eq!(
        stderr.matches("WI-001").count(),
        1,
        "the thrice-repeated id is named once: {stderr}"
    );
}

#[test]
fn a_clean_store_passes_the_gate() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, CLEAN);

    let (code, stdout, stderr) = run(&proj, &["list", "--all"]);

    assert_eq!(code, 0, "stderr={stderr}");
    assert!(stdout.contains("WI-003"), "renumbered record shows: {stdout}");
}

/// The count the listing reports and the rows it prints must agree — that
/// disagreement is the symptom the collision produced, and the gate exists to
/// make it unreachable.
#[test]
fn the_gate_reads_ids_not_descriptions() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, CLEAN);

    let (code, stdout, stderr) = run(&proj, &["list", "--all"]);
    assert_eq!(code, 0, "a repeated id in PROSE is not a duplicate: {stderr}");

    let rows = stdout
        .lines()
        .filter(|l| l.starts_with("  WI-"))
        .count();
    assert!(
        stdout.contains(&format!("{rows} item(s)")),
        "footer must count the rows actually printed: {stdout}"
    );
}
