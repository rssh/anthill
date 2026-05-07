//! `anthill-todo --anthill add <description> [--depends ...]* [--acceptance ...]*`
//! integration test. Phase 2 of WI-009: cmd_add is the second mutating
//! command on the bundle, exercising the same persist+flush path as
//! cmd_feedback plus a freshly-derived id (max-WI-NNN + 1) and
//! repeatable-flag collection.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

const ANTHILL_TODO_BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent().unwrap()
        .parent().unwrap()
        .to_path_buf()
}

fn setup_project(tmp: &tempfile::TempDir, workitems: &str) -> PathBuf {
    let proj = tmp.path().to_path_buf();
    let inner = proj.join("anthill-todo");
    fs::create_dir(&inner).expect("mkdir anthill-todo");

    let src_root = workspace_root().join("anthill-todo");
    for f in ["domain.anthill", "rules.anthill"] {
        fs::copy(src_root.join(f), inner.join(f)).expect("copy stdlib");
    }
    fs::write(inner.join("workitems.anthill"), workitems).expect("write workitems");
    proj
}

fn read_all_anthill(inner: &std::path::Path) -> String {
    let mut combined = String::new();
    for entry in fs::read_dir(inner).expect("read_dir") {
        let path = entry.expect("entry").path();
        if path.extension().and_then(|s| s.to_str()) == Some("anthill") {
            combined.push_str(&fs::read_to_string(&path).expect("read"));
        }
    }
    combined
}

#[test]
fn add_assigns_next_id_after_max() {
    let tmp = tempfile::tempdir().expect("tempdir");
    // WI-001 + WI-005 → next id should be WI-006.
    let proj = setup_project(&tmp, "\
fact WorkItem(
  id: \"WI-001\",
  description: \"first\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Open)

fact WorkItem(
  id: \"WI-005\",
  description: \"fifth\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Open)
");
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "add", "next item"])
        .output().expect("run");
    assert!(out.status.success(),
        "add failed: stderr={}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("added: WI-006 — next item"),
        "unexpected stdout: {stdout}");

    let combined = read_all_anthill(&proj.join("anthill-todo"));
    assert!(combined.contains("id: \"WI-006\""),
        "WI-006 not persisted: {combined}");
    assert!(combined.contains("description: \"next item\""));
    assert!(combined.contains("status: Open"));
}

#[test]
fn add_empty_project_starts_at_wi_001() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "add", "first ever"])
        .output().expect("run");
    assert!(out.status.success(),
        "add failed: stderr={}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("added: WI-001 — first ever"),
        "expected WI-001, got: {stdout}");
}

#[test]
fn add_repeatable_depends_in_caller_order() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "add", "with deps",
               "--depends", "WI-A",
               "--depends", "WI-B",
               "--depends", "WI-C"])
        .output().expect("run");
    assert!(out.status.success(),
        "stderr={}", String::from_utf8_lossy(&out.stderr));

    let combined = read_all_anthill(&proj.join("anthill-todo"));
    // WI-A precedes WI-B precedes WI-C in the persisted depends_on
    // list — confirms the repeatable-flag collection preserves the
    // order the user typed them.
    let a_pos = combined.find("\"WI-A\"").expect("WI-A in output");
    let b_pos = combined.find("\"WI-B\"").expect("WI-B in output");
    let c_pos = combined.find("\"WI-C\"").expect("WI-C in output");
    assert!(a_pos < b_pos && b_pos < c_pos,
        "depends order wrong: {combined}");
}

#[test]
fn add_default_acceptance_is_cargo_test() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "add", "default-accept"])
        .output().expect("run");
    assert!(out.status.success(),
        "stderr={}", String::from_utf8_lossy(&out.stderr));

    let combined = read_all_anthill(&proj.join("anthill-todo"));
    assert!(combined.contains("ToolPasses(tool: \"cargo-test\")"),
        "expected default cargo-test acceptance, got: {combined}");
}

#[test]
fn add_custom_acceptance_overrides_default() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(),
               "add", "custom-accept",
               "--acceptance", "my-tool"])
        .output().expect("run");
    assert!(out.status.success(),
        "stderr={}", String::from_utf8_lossy(&out.stderr));

    let combined = read_all_anthill(&proj.join("anthill-todo"));
    assert!(combined.contains("ToolPasses(tool: \"my-tool\")"));
    // The default cargo-test must not appear when the user supplied
    // an explicit acceptance — it would mean the default-fallback
    // branch fired even though the user opted out.
    let added_block_start = combined.find("WI-001").expect("WI-001 lives");
    let added_block = &combined[added_block_start..];
    let block_end = added_block.find("status: Open")
        .map(|i| added_block_start + i).unwrap_or(combined.len());
    let added_block = &combined[added_block_start..block_end];
    assert!(!added_block.contains("\"cargo-test\""),
        "cargo-test default leaked into custom-acceptance block: {added_block}");
}

#[test]
fn add_missing_description_errors() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(), "add"])
        .output().expect("run");
    assert!(!out.status.success(), "expected failure");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("argument error") || stderr.contains("missing"),
        "expected diagnostic, got stderr: {stderr}");
}
