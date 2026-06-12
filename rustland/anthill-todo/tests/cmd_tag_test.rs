//! WI-388: named ticket lists (tags) + ordered insert + dep-edit — the
//! build-loop primitives. All exercise the default (clap) CLI path, NOT the
//! `--anthill` bundle: the tag/insert/list-ordering features live there
//! (the build-loop skill and `docs/design/typing-build-loop.md` use that path).

mod common;

use std::process::Command;

use common::{read_combined, setup_project, workitem_block_contains};

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

/// A 3-item project: WI-002 depends on WI-001; WI-003 is independent.
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

fn run(proj: &std::path::Path, args: &[&str]) -> std::process::Output {
    let mut full = vec!["-d", proj.to_str().unwrap()];
    full.extend_from_slice(args);
    Command::new(BIN).args(&full).output().expect("run anthill-todo")
}

fn ok(out: &std::process::Output) -> String {
    assert!(out.status.success(),
        "command failed: stderr={}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8_lossy(&out.stdout).into_owned()
}

// ── tag / untag ─────────────────────────────────────────────────

#[test]
fn tag_persists_a_tag_fact_and_show_reports_it() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);

    let stdout = ok(&run(&proj, &["tag", "WI-001", "typing"]));
    assert!(stdout.contains("tagged: WI-001 +typing"), "stdout: {stdout}");

    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(combined.contains("fact Tag("), "no Tag fact persisted:\n{combined}");
    assert!(combined.contains("workitem: \"WI-001\"") && combined.contains("name: \"typing\""),
        "tag fact missing markers:\n{combined}");

    // show surfaces the tag
    let shown = ok(&run(&proj, &["show", "WI-001"]));
    assert!(shown.contains("Tags:") && shown.contains("typing"),
        "show did not report tag:\n{shown}");
}

#[test]
fn tag_is_idempotent_and_errors_on_duplicate() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);

    ok(&run(&proj, &["tag", "WI-001", "typing"]));
    let out = run(&proj, &["tag", "WI-001", "typing"]);
    assert!(!out.status.success(), "duplicate tag should error");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("already tagged"), "stderr: {stderr}");
}

#[test]
fn tag_unknown_item_errors() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);

    let out = run(&proj, &["tag", "WI-999", "typing"]);
    assert!(!out.status.success(), "tagging a missing item should error");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("not found"), "stderr: {stderr}");
}

#[test]
fn untag_removes_the_fact_then_errors_when_absent() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);

    ok(&run(&proj, &["tag", "WI-003", "typing"]));
    let stdout = ok(&run(&proj, &["untag", "WI-003", "typing"]));
    assert!(stdout.contains("untagged: WI-003 -typing"), "stdout: {stdout}");

    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(!combined.contains("workitem: \"WI-003\""),
        "Tag fact for WI-003 not removed:\n{combined}");

    // second untag is a loud no-op
    let out = run(&proj, &["untag", "WI-003", "typing"]);
    assert!(!out.status.success(), "untagging an absent tag should error");
}

#[test]
fn untag_keeps_one_of_multiple_tags() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);

    ok(&run(&proj, &["tag", "WI-001", "typing"]));
    ok(&run(&proj, &["tag", "WI-001", "review"]));
    ok(&run(&proj, &["untag", "WI-001", "typing"]));

    let shown = ok(&run(&proj, &["show", "WI-001"]));
    assert!(shown.contains("review"), "review tag should survive:\n{shown}");
    assert!(!shown.contains("typing"), "typing tag should be gone:\n{shown}");
}

// ── list --tag (ordered sequence view) ──────────────────────────

#[test]
fn list_tag_shows_items_in_dependency_order() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);

    // Tag in a deliberately non-sequence order; the view must reorder.
    ok(&run(&proj, &["tag", "WI-002", "typing"]));
    ok(&run(&proj, &["tag", "WI-001", "typing"]));

    let stdout = ok(&run(&proj, &["list", "--tag", "typing"]));
    let pos1 = stdout.find("WI-001").expect("WI-001 listed");
    let pos2 = stdout.find("WI-002").expect("WI-002 listed");
    assert!(pos1 < pos2,
        "dependency WI-001 must precede dependent WI-002:\n{stdout}");

    // WI-001 (Open, no unmet deps) is the build-loop's pick.
    assert!(stdout.contains("<- next"), "expected a `<- next` marker:\n{stdout}");
    // WI-002 is blocked by its unsatisfied dependency.
    assert!(stdout.contains("blocked: WI-001"),
        "WI-002 should show its unmet dependency:\n{stdout}");
}

#[test]
fn list_tag_marks_next_after_dependency_delivered() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);
    ok(&run(&proj, &["tag", "WI-001", "typing"]));
    ok(&run(&proj, &["tag", "WI-002", "typing"]));

    // Deliver WI-001; now WI-002's deps are satisfied and it is `<- next`.
    ok(&run(&proj, &["--agent", "claude", "claim", "WI-001"]));
    ok(&run(&proj, &["--agent", "claude", "deliver", "WI-001"]));

    let stdout = ok(&run(&proj, &["list", "--tag", "typing"]));
    // The `<- next` marker should now sit on the WI-002 line, not WI-001.
    let next_line = stdout.lines().find(|l| l.contains("<- next")).unwrap_or("");
    assert!(next_line.contains("WI-002"),
        "next marker should move to WI-002 once WI-001 delivered:\n{stdout}");
}

#[test]
fn list_tag_empty_reports_no_items() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);
    let stdout = ok(&run(&proj, &["list", "--tag", "nonexistent"]));
    assert!(stdout.contains("No work items tagged"), "stdout: {stdout}");
}

// ── add --tag ───────────────────────────────────────────────────

#[test]
fn add_with_tag_writes_workitem_and_tag() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);

    let stdout = ok(&run(&proj, &["add", "tagged item", "--tag", "typing"]));
    assert!(stdout.contains("added: WI-004"), "stdout: {stdout}");
    assert!(stdout.contains("typing"), "tag note absent: {stdout}");

    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(combined.contains("id: \"WI-004\""), "WI-004 not persisted");
    assert!(combined.contains("workitem: \"WI-004\"") && combined.contains("name: \"typing\""),
        "tag fact for WI-004 not persisted:\n{combined}");
}

// ── insert --before ─────────────────────────────────────────────

#[test]
fn insert_before_creates_tags_and_adds_dependency() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);

    let stdout = ok(&run(&proj, &["insert", "prerequisite", "--before", "WI-002", "--tag", "typing"]));
    assert!(stdout.contains("inserted: WI-004 before WI-002"), "stdout: {stdout}");

    let combined = read_combined(&proj.join("anthill-todo"));
    // The new item exists and is tagged.
    assert!(combined.contains("id: \"WI-004\""), "WI-004 not created:\n{combined}");
    assert!(combined.contains("workitem: \"WI-004\""), "WI-004 not tagged:\n{combined}");
    // WI-002 now depends on the freshly-inserted WI-004.
    assert!(workitem_block_contains(&combined, "WI-002", "WI-004"),
        "WI-002 should depend on WI-004:\n{combined}");
}

#[test]
fn insert_orders_new_item_before_target_in_tag_view() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);
    ok(&run(&proj, &["tag", "WI-002", "typing"]));

    ok(&run(&proj, &["insert", "prerequisite", "--before", "WI-002", "--tag", "typing"]));

    let stdout = ok(&run(&proj, &["list", "--tag", "typing"]));
    let pos_new = stdout.find("WI-004").expect("WI-004 listed");
    let pos_002 = stdout.find("WI-002").expect("WI-002 listed");
    assert!(pos_new < pos_002,
        "inserted WI-004 must precede WI-002 in the sequence:\n{stdout}");
}

#[test]
fn insert_unknown_before_errors_and_creates_nothing() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);

    let out = run(&proj, &["insert", "x", "--before", "WI-999", "--tag", "typing"]);
    assert!(!out.status.success(), "insert before a missing item should error");
    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(!combined.contains("id: \"WI-004\""),
        "no item should be created when --before is missing:\n{combined}");
}

#[test]
fn insert_before_non_bracket_depends_succeeds() {
    // `before`'s depends_on is `nil()` (not a `[...]` literal). The legacy
    // text surgery could not edit that form and had to fail-without-orphan;
    // the bundle's replace path rewrites the whole block, so the insert now
    // simply WORKS — the orphan hazard the old test guarded is structurally
    // gone (WI-009 cutover).
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, r#"
fact WorkItem(
  id: "WI-001",
  description: "nil deps",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: nil(),
  status: Open)
"#);

    let out = run(&proj, &["insert", "prereq", "--before", "WI-001", "--tag", "typing"]);
    assert!(out.status.success(),
        "insert must rewrite a non-bracket depends_on: stderr={}",
        String::from_utf8_lossy(&out.stderr));
    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(combined.contains("description: some(\"prereq\")"),
        "the new item should be persisted:\n{combined}");
    assert!(workitem_block_contains(&combined, "WI-001", "WI-002"),
        "WI-001 should now depend on the inserted WI-002:\n{combined}");
}

// ── escaping: a tag name with special characters round-trips ─────

#[test]
fn untag_finds_escaped_tag_name() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);

    // A tag name containing a quote is persisted escaped; untag must build the
    // same escaped marker to find and remove it.
    let weird = r#"a"b"#;
    ok(&run(&proj, &["tag", "WI-001", weird]));
    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(combined.contains(r#"name: "a\"b""#), "escaped tag not persisted:\n{combined}");

    ok(&run(&proj, &["untag", "WI-001", weird]));
    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(!combined.contains(r#"name: "a\"b""#), "escaped tag not removed:\n{combined}");
}

// ── dep-edit (add-dependency / remove-dependency) ───────────────

#[test]
fn add_and_remove_dependency_roundtrip() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);

    ok(&run(&proj, &["add-dependency", "WI-003", "WI-001"]));
    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(workitem_block_contains(&combined, "WI-003", "WI-001"),
        "WI-003 should depend on WI-001:\n{combined}");

    ok(&run(&proj, &["remove-dependency", "WI-003", "WI-001"]));
    let combined = read_combined(&proj.join("anthill-todo"));
    assert!(!workitem_block_contains(&combined, "WI-003", "WI-001"),
        "WI-003 dependency on WI-001 should be removed:\n{combined}");
}

#[test]
fn add_dependency_rejects_cycle() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, THREE_ITEMS);

    // WI-002 already depends on WI-001; WI-001 -> WI-002 would close a cycle.
    let out = run(&proj, &["add-dependency", "WI-001", "WI-002"]);
    assert!(!out.status.success(), "cyclic dependency should be rejected");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("cycle"), "stderr: {stderr}");
}
