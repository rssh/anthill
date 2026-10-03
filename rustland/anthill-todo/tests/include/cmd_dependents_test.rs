//! WI-20260904-WX613 — `dependents <id>` shows every item that depends on a work item,
//! directly or transitively, as `graph`'s tree rooted at that item.
//!
//! CONTROL — MEASURED, two back-outs:
//! - with the `dependents` arm removed from `dispatch` (the command then answers "not yet
//!   ported"), every row FAILS except `a_missing_id_is_a_usage_error`, which passes BY
//!   DESIGN: the usage error comes from the command's `spec_with_id` entry, which the
//!   argument parser checks before `dispatch` runs, so it pins the spec, not the body;
//! - with the `print_tree` call removed from `cmd_dependents`, every row FAILS except the
//!   two error rows (`an_unknown_id_is_an_error`, `a_missing_id_is_a_usage_error`), which
//!   never reach the walk.
//!
//! The walk itself is `graph`'s, whose cycle and diamond behaviour `graph_cycle_guard_test`
//! pins; `a_cycle_is_marked_not_looped` re-asks it from this entry point because a
//! different root is a different walk.

use std::process::{Command, Output};

use crate::common::setup_project;

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

fn item(id: &str, deps: &[&str]) -> String {
    let deps = deps
        .iter()
        .map(|d| format!("\"{d}\""))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        r#"
fact WorkItem(
  id: "{id}",
  created: "2026-01-01T00:00:00Z",
  description: "{id}",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [{deps}],
  last_status_change: StatusChange(status: Open()))
"#
    )
}

fn run(fixture: &str, args: &[&str]) -> Output {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, fixture);
    let mut argv = vec!["-d", proj.to_str().unwrap(), "dependents"];
    argv.extend_from_slice(args);
    Command::new(BIN).args(&argv).output().expect("run anthill-todo dependents")
}

fn stdout_ok(out: &Output) -> String {
    assert!(
        out.status.success(),
        "dependents failed: stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// WI-001 ← WI-002 ← WI-003 (a chain), WI-001 ← WI-004, and WI-005 unrelated.
fn store() -> String {
    format!(
        "{}{}{}{}{}",
        item("WI-001", &[]),
        item("WI-002", &["WI-001"]),
        item("WI-003", &["WI-002"]),
        item("WI-004", &["WI-001"]),
        item("WI-005", &[]),
    )
}

/// The tree is rooted at the item asked about and reaches TRANSITIVE dependents:
/// WI-003 depends on WI-001 only through WI-002, and is shown beneath it.
#[test]
fn shows_direct_and_transitive_dependents_as_a_tree() {
    let stdout = stdout_ok(&run(&store(), &["WI-001"]));
    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines[0], "WI-001 [Open]", "the root is the item asked about: {stdout}");
    for id in ["WI-002", "WI-003", "WI-004"] {
        assert!(stdout.contains(id), "{id} depends on WI-001 and must be shown: {stdout}");
    }
    assert!(!stdout.contains("WI-005"), "WI-005 depends on nothing here: {stdout}");
    let pos = |id: &str| stdout.find(id).unwrap();
    assert!(
        pos("WI-002") < pos("WI-003"),
        "WI-003 is reached through WI-002 and renders beneath it: {stdout}"
    );
    assert!(
        !stdout.contains("No work items depend"),
        "an item with dependents must not say it has none: {stdout}"
    );
}

/// Asked about a middle item, only ITS dependents are shown — not its dependencies.
#[test]
fn shows_only_the_subtree_below_the_item() {
    let stdout = stdout_ok(&run(&store(), &["WI-002"]));
    assert!(stdout.contains("WI-003"), "WI-003 depends on WI-002: {stdout}");
    assert!(
        !stdout.contains("WI-001") && !stdout.contains("WI-004"),
        "WI-001 is a dependency of WI-002, not a dependent, and WI-004 is a sibling: {stdout}"
    );
}

/// An item nothing depends on says so, rather than printing nothing a reader could
/// mistake for a failed lookup.
#[test]
fn an_item_nothing_depends_on_says_so() {
    let stdout = stdout_ok(&run(&store(), &["WI-005"]));
    assert_eq!(
        stdout.trim_end(),
        "WI-005 [Open]\nNo work items depend on WI-005",
        "got: {stdout}"
    );
}

/// The id is resolved like every other command's: a minted id's digest is enough.
#[test]
fn an_id_fragment_resolves() {
    let fixture = format!(
        "{}{}",
        item("WI-20260101-AB12C-root-item", &[]),
        item("WI-20260101-ZZ99Y-child-item", &["WI-20260101-AB12C-root-item"]),
    );
    let stdout = stdout_ok(&run(&fixture, &["AB12C"]));
    assert!(stdout.starts_with("WI-20260101-AB12C-root-item [Open]"), "got: {stdout}");
    assert!(stdout.contains("WI-20260101-ZZ99Y-child-item"), "got: {stdout}");
}

/// A corrupt cyclic store must not hang the walk from this root either.
#[test]
fn a_cycle_is_marked_not_looped() {
    let fixture = format!(
        "{}{}{}",
        item("WI-001", &[]),
        item("WI-002", &["WI-001", "WI-003"]),
        item("WI-003", &["WI-002"]),
    );
    let stdout = stdout_ok(&run(&fixture, &["WI-001"]));
    assert!(stdout.lines().count() < 20, "did not terminate compactly: {stdout}");
    assert!(stdout.contains("(cycle)"), "the cycle is marked: {stdout}");
}

#[test]
fn an_unknown_id_is_an_error() {
    let out = run(&store(), &["WI-999"]);
    assert_eq!(out.status.code(), Some(1), "stderr={}", String::from_utf8_lossy(&out.stderr));
}

#[test]
fn a_missing_id_is_a_usage_error() {
    let out = run(&store(), &[]);
    assert_eq!(out.status.code(), Some(2), "stderr={}", String::from_utf8_lossy(&out.stderr));
}
