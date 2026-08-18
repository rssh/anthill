//! WI-009 cutover parity: the DEFAULT path (no flag — the anthill bundle)
//! replays a full CLI session and must reproduce the golden transcript byte
//! for byte. The golden was captured at cutover time and equals the legacy
//! native output except four DOCUMENTED divergences (recorded on WI-009):
//!   1. `show`'s Acceptance items print the loader-canonical named form
//!      (`ToolPasses(tool: "cargo-test", params: none)`, legacy printed the
//!      positional spelling). WI-716: an omitted optional field renders as
//!      `none`, not the loader's synthetic fill var `?params` — a ground fact
//!      stores `none()` for an absent optional, not an unbound var;
//!   2. `next` with several claimable items picks resolver order (the
//!      scenario keeps exactly one claimable so the transcript is
//!      deterministic — multi-claimable order is unpinned);
//!   3. `delete` prints `deleted: <id>` without the file path (the store
//!      abstraction doesn't leak file names);
//!   4. unknown subcommands get the bundle's one-line error, not clap's
//!      usage dump; `--help` is the spec-driven catalogue;
//!   5. exit codes are LOUD: `show`/`delete` on an unknown id exit 1
//!      (legacy printed the error but exited 0 — the "exit-0-with-stderr"
//!      display-command convention is retired with the native dispatch);
//! THE THREE `add` STEPS CARRY `--created` (WI-1121), and that is load-bearing
//! rather than decoration: `list` orders by `created` with the id as tie-break,
//! and a MINTED id's tie-break order is its digest's — deterministic for a given
//! tracker, but different every run, since the id is derived from the timestamp.
//! Four items added inside one second therefore tied and listed in an order that
//! varied run to run. Fixed stamps pin both the ids and the order. `insert` has
//! no such flag by design (§6.7: it is a positional gesture, not a back-dated
//! filing), and needs none — `now()` sorts after every fixed stamp here.
//!
//!   6. an unknown id is refused by the reference LADDER (WI-1121) before it
//!      reaches `lookup`, so the message is `no work item matches '<given>'` —
//!      one refusal for "matches nothing" and for "matches several", where the
//!      old one could only say the first;
//!   7. `delete WI-004` warns that WI-003 still depends on it (WI-1123).
//!      THIS SCENARIO IS THE CASE THE WARNING EXISTS FOR, and the golden
//!      shows why on the very next line: `list --all` renders WI-003 as
//!      `(depends: WI-002, WI-004)`, an edge to an item that no longer
//!      exists. A dep naming no work item counts as unmet, so WI-003 is
//!      unclaimable from here on and nothing used to say so.
//! Everything else — every message, marker, ordering, and exit code — is
//! the legacy behavior.

use std::process::Command;

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");
const GOLDEN: &str = include_str!("../golden/cli_transcript.golden");

/// The scenario: each entry is one CLI invocation (argv after the binary).
const SCENARIO: &[&[&str]] = &[
    &["add", "base work", "--acceptance", "cargo-test", "--created", "2026-08-01T00:00:01Z"],
    &["add", "second work", "--depends", "WI-001", "--tag", "seq", "--created", "2026-08-01T00:00:02Z"],
    &["add", "third work", "--depends", "WI-002", "--tag", "seq", "--created", "2026-08-01T00:00:03Z"],
    &[
        "insert",
        "prereq for third",
        "--before",
        "WI-003",
        "--depends",
        "WI-001",
        "--tag",
        "seq",
    ],
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
    &[
        "--agent",
        "claude",
        "feedback",
        "WI-002",
        "some feedback text",
    ],
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
    assert!(
        init.status.success(),
        "init failed: {}",
        String::from_utf8_lossy(&init.stderr)
    );

    // WI-1121: THE SCENARIO'S `WI-00N` ARE PLACEHOLDERS, NOT IDS. An id is minted
    // from the item — author, `created`, description — so it is not knowable in
    // advance, and a transcript full of them would be a different file on every
    // run. Each `add`/`insert` registers the id it minted against the next
    // placeholder; a placeholder in an ARGUMENT is expanded to that id on the way
    // in, and the id in the OUTPUT is folded back to its placeholder on the way
    // out. The golden therefore stays exactly the file it was, and still measures
    // every message, marker, ordering and exit code it always did.
    //
    // `WI-999` is not registered by anything and so passes through untouched —
    // which is the point of the two scenario steps that use it.
    let mut minted: Vec<(String, String)> = Vec::new();

    let mut transcript = String::new();
    for args in SCENARIO {
        transcript.push_str("$ anthill-todo ");
        transcript.push_str(&args.join(" "));
        transcript.push('\n');

        let expand = |arg: &str| -> String {
            minted
                .iter()
                .find(|(_, placeholder)| placeholder == arg)
                .map(|(id, _)| id.clone())
                .unwrap_or_else(|| arg.to_string())
        };
        let expanded: Vec<String> = args.iter().map(|a| expand(a)).collect();
        let mut full: Vec<&str> = vec!["-d", proj.to_str().unwrap()];
        full.extend(expanded.iter().map(|s| s.as_str()));
        let out = Command::new(BIN)
            .args(&full)
            .output()
            .expect("run anthill-todo");

        // Mirror the capture script: trailing newlines trimmed, stdout
        // before stderr, each section emitted only when non-empty.
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stdout = stdout.trim_end_matches('\n');
        // Registered BEFORE folding, since the line that announces an id is the
        // only place it is ever seen.
        if matches!(args.first(), Some(&"add") | Some(&"insert")) {
            let id = stdout
                .split_whitespace()
                .nth(1)
                .expect("`added:`/`inserted:` names the id")
                .to_string();
            let placeholder = format!("WI-{:03}", minted.len() + 1);
            minted.push((id, placeholder));
        }
        let fold = |text: &str| -> String {
            let mut out = text.to_string();
            for (id, placeholder) in &minted {
                out = out.replace(id.as_str(), placeholder.as_str());
            }
            out
        };
        let stdout = fold(stdout);
        if !stdout.is_empty() {
            transcript.push_str(&stdout);
            transcript.push('\n');
        }
        let stderr = String::from_utf8_lossy(&out.stderr);
        let stderr = fold(stderr.trim_end_matches('\n'));
        if !stderr.is_empty() {
            transcript.push_str(&stderr);
            transcript.push('\n');
        }
        let code = out.status.code().unwrap_or(-1);
        transcript.push_str(&format!("[exit={code}]\n"));
    }

    if transcript != GOLDEN {
        // The whole actual transcript, so a divergence can be REVIEWED as a diff
        // rather than re-derived one panic line at a time. Written beside the
        // build, never into the source tree — accepting it is a deliberate copy.
        let dump = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../target/cli_transcript.actual");
        let _ = std::fs::write(&dump, &transcript);
        eprintln!("actual transcript written to {}", dump.display());
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
