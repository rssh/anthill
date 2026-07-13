//! Regression: `claim` hung indefinitely when any WorkItem's string
//! field (e.g. `description`) contained an unbalanced parenthesis.
//! The bug was in `fact_block_end`: paren counting did not skip
//! string literals, so an unbalanced `(` left depth above zero and
//! the outer search re-entered the same offset forever.
//!
//! No `--anthill` on purpose — the IndexedFileStore retract path
//! used by `--anthill` is span-based and not affected by this bug.

mod common;

use std::fs;
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

const WORKITEMS_WITH_UNBALANCED_PAREN: &str = r#"
fact WorkItem(
  id: "WI-001",
  description: "this description has an unbalanced ( open paren",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)
"#;

#[test]
fn claim_completes_when_description_has_unbalanced_paren() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = common::setup_project(&tmp, WORKITEMS_WITH_UNBALANCED_PAREN);

    // Guards a real regression: `find_fact_block` once looped forever on an
    // unbalanced `(` in a string field, so `claim` never returned. The guard is
    // about *termination*, not speed — we assert the process COMPLETES (and
    // succeeds); any finite exit means the parser loop is bounded and the guard
    // holds. The deadline is only a backstop so a genuine non-terminating
    // regression fails instead of hanging the suite forever — not a performance
    // budget. The claim runs in ~2.7s idle and up to ~10-20s under heavy
    // parallel load (WI-715), so a 20s backstop sits just above the observed
    // range; if it flakes again under heavier load, raise it — the only hard
    // requirement is that it stay finite so a real hang still fails.
    let hang_backstop = Duration::from_secs(20);
    let start = Instant::now();

    let mut child = Command::new(BIN)
        .args(["-d", proj.to_str().unwrap(), "--agent", "claude", "claim", "WI-001"])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn anthill-todo");

    loop {
        if let Some(status) = child.try_wait().expect("try_wait") {
            assert!(status.success(),
                "claim WI-001 exited {:?} after {:?}", status.code(), start.elapsed());
            break;
        }
        if start.elapsed() > hang_backstop {
            let _ = child.kill();
            let _ = child.wait();
            panic!(
                "claim WI-001 still had not terminated after {:?} — treating \
                 as a find_fact_block non-terminating-loop regression (an \
                 unbalanced `(` in a description must not hang the parser). If \
                 this fires under heavy parallel test load rather than a real \
                 hang, raise the backstop in this test.",
                hang_backstop
            );
        }
        thread::sleep(Duration::from_millis(50));
    }

    // Verify the source was actually updated — the bug previously
    // would have hung before reaching this write step.
    let inner = proj.join("anthill-todo");
    let mut found_claimed = false;
    for entry in fs::read_dir(&inner).expect("read project") {
        let path = entry.expect("dir entry").path();
        if path.extension().and_then(|e| e.to_str()) != Some("anthill") { continue; }
        let content = fs::read_to_string(&path).expect("read file");
        if content.contains("\"WI-001\"")
            && content.contains("Claimed")
            && content.contains("agent: \"claude\"")
        {
            found_claimed = true;
            break;
        }
    }
    assert!(found_claimed,
        "Claimed WI-001 fact not found in any .anthill file under {}",
        inner.display());
}
