//! WI-009 cutover parity: the DEFAULT path (no flag — the anthill bundle)
//! replays a full CLI session and must reproduce the golden transcript byte
//! for byte. The golden was captured at cutover time and equals the legacy
//! native output except four DOCUMENTED divergences (recorded on WI-009):
//!   1. `show`'s Acceptance items print the loader-canonical named form
//!      (`ToolPasses(tool: "cargo-test", …)`, legacy printed the positional
//!      spelling);
//!   2. `next` with several claimable items picks resolver order (the
//!      scenario keeps exactly one claimable so the transcript is
//!      deterministic — multi-claimable order is unpinned);
//!   3. `delete` prints `deleted: <id>` without the file path (the store
//!      abstraction doesn't leak file names);
//!   4. unknown subcommands get the bundle's one-line error, not clap's
//!      usage dump; `--help` is the spec-driven catalogue;
//!   5. exit codes are LOUD: `show`/`delete` on an unknown id exit 1
//!      (legacy printed the error but exited 0 — the "exit-0-with-stderr"
//!      display-command convention is retired with the native dispatch).
//! Everything else — every message, marker, ordering, and exit code — is
//! the legacy behavior.

use std::process::Command;

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");
const GOLDEN: &str = include_str!("golden/cli_transcript.golden");

/// The scenario: each entry is one CLI invocation (argv after the binary).
const SCENARIO: &[&[&str]] = &[
    &["add", "base work", "--acceptance", "cargo-test"],
    &["add", "second work", "--depends", "WI-001", "--tag", "seq"],
    &["add", "third work", "--depends", "WI-002", "--tag", "seq"],
    &["insert", "prereq for third", "--before", "WI-003", "--depends", "WI-001", "--tag", "seq"],
    &["tag", "WI-001", "seq"],
    &["status"],
    &["list"],
    &["list", "--all"],
    &["list", "--status", "open"],
    &["list", "--tag", "seq"],
    &["show", "WI-001"],
    &["next"],
    &["graph"],
    &["--agent", "claude", "claim", "WI-001"],
    &["--agent", "claude", "deliver", "WI-001"],
    &["verify", "WI-001"],
    &["--agent", "claude", "feedback", "WI-002", "some feedback text"],
    &["show", "WI-002"],
    &["update", "WI-002", "--description", "second work updated"],
    &["add-dependency", "WI-003", "WI-001"],
    &["add-dependency", "WI-001", "WI-002"],
    &["remove-dependency", "WI-003", "WI-001"],
    &["untag", "WI-004", "seq"],
    &["list", "--tag", "seq"],
    &["delete", "WI-004"],
    &["list", "--all"],
    &["show", "WI-999"],
    &["nonexistent-subcommand"],
];

#[test]
fn default_path_reproduces_the_golden_transcript() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = tmp.path();

    let init = Command::new(BIN)
        .current_dir(proj)
        .arg("init")
        .output()
        .expect("run init");
    assert!(init.status.success(), "init failed: {}", String::from_utf8_lossy(&init.stderr));

    let mut transcript = String::new();
    for args in SCENARIO {
        transcript.push_str("$ anthill-todo ");
        transcript.push_str(&args.join(" "));
        transcript.push('\n');

        let mut full: Vec<&str> = vec!["-d", proj.to_str().unwrap()];
        full.extend_from_slice(args);
        let out = Command::new(BIN).args(&full).output().expect("run anthill-todo");

        // Mirror the capture script: trailing newlines trimmed, stdout
        // before stderr, each section emitted only when non-empty.
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stdout = stdout.trim_end_matches('\n');
        if !stdout.is_empty() {
            transcript.push_str(stdout);
            transcript.push('\n');
        }
        let stderr = String::from_utf8_lossy(&out.stderr);
        let stderr = stderr.trim_end_matches('\n');
        if !stderr.is_empty() {
            transcript.push_str(stderr);
            transcript.push('\n');
        }
        let code = out.status.code().unwrap_or(-1);
        transcript.push_str(&format!("[exit={code}]\n"));
    }

    if transcript != GOLDEN {
        // Locate the first diverging line for a readable failure.
        let mut g = GOLDEN.lines();
        for (i, a) in transcript.lines().enumerate() {
            match g.next() {
                Some(e) if e == a => continue,
                Some(e) => panic!(
                    "transcript diverges at line {}:\n  expected: {e}\n  actual:   {a}",
                    i + 1
                ),
                None => panic!("transcript longer than golden at line {}: {a}", i + 1),
            }
        }
        panic!("transcript shorter than golden");
    }
}
