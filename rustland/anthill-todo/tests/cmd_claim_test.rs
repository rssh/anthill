//! `anthill-todo --anthill claim <id>` — first retract+assert command
//! on the bundle, exercising IndexedFileStore's span-based retract
//! path (WI-187). The Open WorkItem block is dropped from the source
//! file by byte range; the Claimed replacement lands in the SAME
//! workitems.anthill (the store's SingleFile convention — one flush
//! applies a retract and a write to one file). Untargeted facts are
//! untouched.

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
    // WI-001's Open block must be gone, and its Claimed replacement must be
    // in the SAME workitems.anthill (SingleFile convention) — so exactly one
    // `status: Open)` remains (WI-002's) and WI-001 reads Claimed.
    assert_eq!(workitems.matches("status: Open)").count(), 1,
        "only WI-002 should still be Open: {workitems}");
    assert!(workitems.contains("status: Claimed(agent: \"claude\""),
        "WI-001 Claimed replacement should be in workitems.anthill: {workitems}");
    // WI-002 untouched.
    assert!(workitems.contains("\"WI-002\""),
        "WI-002 should be intact: {workitems}");

    // The Claimed replacement landed in some .anthill file — the
    // SingleFile convention targets workitems.anthill — and includes
    // the agent and a Z-suffixed timestamp.
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

#[cfg(unix)]
#[test]
fn claim_on_readonly_dir_raises_clean_error_not_panic() {
    // WI-195: a store I/O failure (here: a read-only project dir so the
    // FileStore can't create/rewrite files) must surface through the Error
    // effect as a clean `error: ... failed: ...` line + EXIT_RUNTIME — NOT a
    // Rust panic/backtrace, and NOT a leaked `internal evaluator error:`
    // fault. Persist/flush/retract declare `effects Error`, so the host-side
    // failure rides the Error channel.
    use std::os::unix::fs::PermissionsExt;

    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "\
fact WorkItem(
  id: \"WI-001\",
  description: \"test item\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Open)
");
    let inner = proj.join("anthill-todo");
    // Read-only dir: reads still work (bundle loads), but the store cannot
    // create/rename files, so persist/flush fails.
    fs::set_permissions(&inner, fs::Permissions::from_mode(0o555)).expect("chmod ro");

    let out = Command::new(ANTHILL_TODO_BIN)
        .args([
            "--anthill", "-d", proj.to_str().unwrap(),
            "--agent", "claude",
            "claim", "WI-001",
        ])
        .output().expect("run");

    // Restore write so the tempdir can be cleaned up.
    fs::set_permissions(&inner, fs::Permissions::from_mode(0o755)).expect("chmod rw");

    let stderr = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(1),
        "expected EXIT_RUNTIME (1); stderr={stderr}");
    assert!(stderr.contains("error:") && stderr.contains("failed"),
        "expected a clean 'error: ... failed' line, got stderr: {stderr}");
    // The failure rode the Error effect — not a leaked Internal fault / panic.
    assert!(!stderr.contains("internal evaluator error"),
        "store I/O failure should be a Raised Error, not Internal: {stderr}");
    assert!(!stderr.to_lowercase().contains("panic"),
        "must not panic: {stderr}");
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
