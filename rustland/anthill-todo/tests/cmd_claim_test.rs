//! `anthill-todo --anthill claim <id>` — first retract+assert command
//! on the bundle, exercising IndexedFileStore's span-based retract
//! path (WI-187). The Open WorkItem block is dropped from the source
//! file by byte range; the Claimed replacement lands in the persist
//! file. Untargeted facts are untouched.

mod common;

use std::fs;
use std::process::Command;

use common::setup_project;

const ANTHILL_TODO_BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

#[test]
fn claim_drops_open_block_and_writes_claimed() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "\
fact WorkItem(
  id: \"WI-001\",
  description: \"test item\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Open)

fact WorkItem(
  id: \"WI-002\",
  description: \"second\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Open)
");

    let out = Command::new(ANTHILL_TODO_BIN)
        .args([
            "--anthill", "-d", proj.to_str().unwrap(),
            "--agent", "claude",
            "claim", "WI-001",
        ])
        .output().expect("run");
    assert!(out.status.success(),
        "claim failed: stderr={}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("claimed: WI-001 by claude"),
        "unexpected stdout: {stdout}");

    let inner = proj.join("anthill-todo");
    let workitems = fs::read_to_string(inner.join("workitems.anthill")).unwrap();
    // WI-001's Open block must be gone from workitems.anthill.
    assert!(!workitems.contains("\"WI-001\""),
        "WI-001 Open block should have been retracted: {workitems}");
    // WI-002 untouched.
    assert!(workitems.contains("\"WI-002\""),
        "WI-002 should be intact: {workitems}");

    // The Claimed replacement landed in some .anthill file — the
    // persist-side facts.anthill — and includes the agent and a Z-
    // suffixed timestamp.
    let mut found_claimed = false;
    for entry in fs::read_dir(&inner).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().and_then(|s| s.to_str()) == Some("anthill") {
            let content = fs::read_to_string(&path).unwrap();
            if content.contains("\"WI-001\"")
                && content.contains("Claimed")
                && content.contains("agent: \"claude\"")
            {
                found_claimed = true;
                break;
            }
        }
    }
    assert!(found_claimed,
        "Claimed WI-001 fact not found in any .anthill file under {}",
        inner.display());
}

#[test]
fn claim_unknown_id_errors() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    let out = Command::new(ANTHILL_TODO_BIN)
        .args([
            "--anthill", "-d", proj.to_str().unwrap(),
            "claim", "WI-999",
        ])
        .output().expect("run");
    assert!(!out.status.success(), "expected failure for unknown id");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("WI-999") && stderr.contains("not found"),
        "expected diagnostic, got stderr: {stderr}");
}
