//! `anthill-todo --anthill feedback <id> <text>` integration test.
//!
//! Phase 2 of WI-009: cmd_feedback is the first mutating command on the
//! anthill-side bundle. This test sets up a tempdir project with the
//! same domain.anthill / rules.anthill the real project uses, runs the
//! binary against it, and asserts a Feedback fact lands in the project
//! directory through the FileStore persist+flush path.
//!
//! The bundle's store uses FileConvention::SingleFile("workitems.anthill"),
//! so runtime-persisted facts land in the same workitems.anthill the
//! legacy text-append shim used. (No real project ever carried a
//! facts.anthill: the bundle path was always behind the hidden
//! --anthill flag, so the earlier Flat convention only ever wrote to
//! throwaway test dirs.)

mod common;

use std::fs;
use std::process::Command;

use common::setup_project;

const ANTHILL_TODO_BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

const SINGLE_OPEN_WI: &str = "\
fact WorkItem(
  id: \"WI-001\",
  description: \"test item\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Open)
";

#[test]
fn feedback_persists_fact_to_project_dir() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, SINGLE_OPEN_WI);

    let out = Command::new(ANTHILL_TODO_BIN)
        .args([
            "--anthill",
            "-d", proj.to_str().unwrap(),
            "--agent", "claude",
            "feedback", "WI-001", "ported from anthill bundle",
        ])
        .output()
        .expect("run anthill-todo");

    assert!(out.status.success(),
        "feedback failed: stderr={}",
        String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("feedback on WI-001: ported from anthill bundle"),
        "unexpected stdout: {stdout}");

    // The fact lands in some `.anthill` file under anthill-todo/ (the
    // SingleFile convention targets workitems.anthill); the test is
    // tolerant of any landing site so a future routing change doesn't
    // require a fixture rewrite.
    let inner = proj.join("anthill-todo");
    let mut found = false;
    for entry in fs::read_dir(&inner).expect("read_dir") {
        let path = entry.expect("entry").path();
        if path.extension().and_then(|s| s.to_str()) == Some("anthill") {
            let content = fs::read_to_string(&path).expect("read");
            if content.contains("fact Feedback")
                && content.contains("workitem: \"WI-001\"")
                && content.contains("author: \"claude\"")
                && content.contains("content: \"ported from anthill bundle\"")
            {
                found = true;
                break;
            }
        }
    }
    assert!(found,
        "Feedback fact not found in any .anthill file under {}",
        inner.display());
}

#[test]
fn feedback_on_missing_item_errors_and_writes_nothing() {
    // WI-432(a,b): the legacy `feedback` committed the Feedback fact without
    // checking the target existed, so `feedback WI-999 ...` landed an orphan
    // fact AND exited 0 (silently succeeding a mistargeted write). It must now
    // fail loudly and persist nothing.
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, SINGLE_OPEN_WI); // only WI-001 exists

    let out = Command::new(ANTHILL_TODO_BIN)
        .args([
            "-d", proj.to_str().unwrap(),
            "--agent", "claude",
            "feedback", "WI-999", "feedback for a ghost",
        ])
        .output()
        .expect("run anthill-todo");

    assert!(!out.status.success(),
        "feedback on a missing item must exit nonzero; stderr={}",
        String::from_utf8_lossy(&out.stderr));
    let stderr = String::from_utf8_lossy(&out.stderr);
    // Pin the exact diagnostic (not two independent substrings) so a nonzero
    // exit for an *unrelated* reason can't masquerade as the not-found path.
    assert!(stderr.contains("work item 'WI-999' not found"),
        "expected the not-found diagnostic, got stderr: {stderr}");

    // Prove the store was left untouched — not merely that the literal
    // "WI-999" is absent (a truncating rewrite would pass that). The pre-
    // existing WI-001 must survive and NO Feedback fact may have landed.
    // Neither domain.anthill nor rules.anthill mentions "WI-001" or
    // "fact Feedback", so both checks are attributable to the store write.
    let combined = common::read_combined(&proj.join("anthill-todo"));
    assert!(!combined.contains("WI-999"),
        "no orphan fact for a nonexistent item should be persisted; store:\n{combined}");
    assert!(!combined.contains("fact Feedback"),
        "no Feedback fact should have been written at all; store:\n{combined}");
    assert!(combined.contains("WI-001"),
        "the existing work item must remain intact; store:\n{combined}");
}

#[test]
fn feedback_missing_text_errors_cleanly() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, SINGLE_OPEN_WI);

    let out = Command::new(ANTHILL_TODO_BIN)
        .args([
            "--anthill",
            "-d", proj.to_str().unwrap(),
            "feedback", "WI-001",  // text positional missing
        ])
        .output()
        .expect("run anthill-todo");

    assert!(!out.status.success(), "expected failure for missing text");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("argument error") || stderr.contains("missing text"),
        "expected diagnostic about missing positional, got stderr: {stderr}",
    );
}
