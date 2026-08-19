//! WI-1097: `list` prints the SHORT row by default — the description's first
//! line, clipped to 100 chars, with `…` iff anything was dropped — and `--long`
//! opts back into the full stored text. Before this, the two views disagreed:
//! `--tag` truncated, the plain (default) listing did not, so the view one
//! reaches for by default was the unreadable one.
//!
//! CONTROL, per the repo's testing rule. Backing WI-1097 out fails
//! `plain_list_truncates_long_description_by_default`,
//! `plain_list_short_row_is_a_single_line`,
//! `a_leading_blank_line_does_not_swallow_the_row`,
//! `a_trailing_newline_alone_earns_no_ellipsis`,
//! `long_flag_restores_the_full_text` and `tagged_view_honors_long_flag`
//! (the first four because the plain view printed the raw description, the
//! last two because `--long` was not a known flag and the parser exits 2).
//! The two whitespace tests are also what fails if `short_desc` drops its
//! `trim` and cuts at the first newline unconditionally: the row becomes a
//! bare `…` and an ellipsis appears over an empty tail.
//! `tagged_view_still_truncates_without_the_flag` and
//! `a_short_description_is_identical_in_both_modes` pass EITHER WAY by
//! design: the first pins that the tagged view kept its truncation, the
//! second that shaping leaves an already-short row untouched.

use std::process::Command;

use crate::common::setup_project;

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

/// The 100-char head that survives truncation, and the tail that must not.
const HEAD_CHAR: char = 'H';
const TAIL_WORD: &str = "TAILWORD";
/// WI-002's first line, and the body word that lives past the first newline.
const SUMMARY_LINE: &str = "short summary line";
const BODY_WORD: &str = "BODYWORD";
/// WI-003: under 100 chars and single-line, so nothing is dropped.
const SHORT_DESC: &str = "plain short row";
/// WI-004 opens with a newline — `add "$(cat notes.md)"` produces exactly this
/// — so its FIRST line is empty and a naive first-line cut renders the item as
/// a bare ellipsis.
const BURIED_TITLE: &str = "buried title";
/// WI-005 ends with a newline and has nothing behind it.
const TRAILING_NEWLINE_DESC: &str = "row with a trailing newline";

fn head() -> String {
    std::iter::repeat(HEAD_CHAR).take(100).collect()
}

/// WI-001 is one long line (exercises the 100-char clip), WI-002 is a short
/// first line over a body (exercises the first-line cut — the case a bare
/// 100-char clip would spill across two terminal lines), WI-003 is already
/// short (the no-op control). All three carry the `seq` tag so the same three
/// shapes drive the `--tag` view.
fn fixture() -> String {
    format!(
        r#"
fact WorkItem(
  id: "WI-001",
  created: "2026-01-01T00:00:00Z",
  description: "{head}{TAIL_WORD}",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  last_status_change: StatusChange(status: Open()))

fact WorkItem(
  id: "WI-002",
  created: "2026-01-01T00:00:00Z",
  description: "{SUMMARY_LINE}\n\n{BODY_WORD} second paragraph",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  last_status_change: StatusChange(status: Open()))

fact WorkItem(
  id: "WI-003",
  created: "2026-01-01T00:00:00Z",
  description: "{SHORT_DESC}",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  last_status_change: StatusChange(status: Open()))

fact WorkItem(
  id: "WI-004",
  created: "2026-01-01T00:00:00Z",
  description: "\n{BURIED_TITLE}\n\n{BODY_WORD} again",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  last_status_change: StatusChange(status: Open()))

fact WorkItem(
  id: "WI-005",
  created: "2026-01-01T00:00:00Z",
  description: "{TRAILING_NEWLINE_DESC}\n",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  last_status_change: StatusChange(status: Open()))

fact Tag(workitem: "WI-001", name: "seq")
fact Tag(workitem: "WI-002", name: "seq")
fact Tag(workitem: "WI-003", name: "seq")
"#,
        head = head()
    )
}

fn run(proj: &std::path::Path, args: &[&str]) -> String {
    let mut full = vec!["-d", proj.to_str().unwrap()];
    full.extend_from_slice(args);
    let out = Command::new(BIN)
        .args(&full)
        .output()
        .expect("run anthill-todo");
    assert!(
        out.status.success(),
        "command failed ({:?}): stderr={}",
        args,
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// The one output line carrying `id`. Panics rather than returning an Option:
/// a missing row means the listing changed shape, which is a test failure and
/// not a case to branch on.
fn row_for<'a>(stdout: &'a str, id: &str) -> &'a str {
    stdout
        .lines()
        .find(|l| l.contains(&format!("{id} [")))
        .unwrap_or_else(|| panic!("no row for {id} in:\n{stdout}"))
}

#[test]
fn plain_list_truncates_long_description_by_default() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, &fixture());

    let stdout = run(&proj, &["list", "--status", "Open"]);

    assert_eq!(
        row_for(&stdout, "WI-001"),
        format!("  WI-001 [Open] {}…", head()),
        "the default row is the 100-char head plus an ellipsis: {stdout}"
    );
    assert!(
        !stdout.contains(TAIL_WORD),
        "the 101st char onward must not print without --long: {stdout}"
    );
}

/// The first-line cut, not just the 100-char clip: WI-002's summary is 18
/// chars, so a length-only truncation would carry the body's newlines into the
/// row and print three lines for one item.
#[test]
fn plain_list_short_row_is_a_single_line() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, &fixture());

    let stdout = run(&proj, &["list", "--status", "Open"]);

    assert_eq!(
        row_for(&stdout, "WI-002"),
        format!("  WI-002 [Open] {SUMMARY_LINE}…"),
        "the first line, with an ellipsis announcing the dropped body: {stdout}"
    );
    assert!(
        !stdout.contains(BODY_WORD),
        "nothing past the first line prints without --long: {stdout}"
    );
    // One row per item: five items, five rows, plus the `Open:` header and
    // the `N item(s)` footer.
    assert_eq!(
        stdout.lines().count(),
        7,
        "one line per item plus header and footer: {stdout}"
    );
}

/// A description that OPENS with a newline has an empty first line. Cutting
/// there would print `WI-004 [Open] …` — the row's every word gone, silently,
/// in the view that is now the default. The summary has to survive.
#[test]
fn a_leading_blank_line_does_not_swallow_the_row() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, &fixture());

    let stdout = run(&proj, &["list", "--status", "Open"]);

    assert_eq!(
        row_for(&stdout, "WI-004"),
        format!("  WI-004 [Open] {BURIED_TITLE}…"),
        "the first NON-EMPTY line is the row: {stdout}"
    );
}

/// The ellipsis is a promise that `--long` has more to show. A description
/// whose only dropped character is its final newline has nothing more, so it
/// must not carry one.
#[test]
fn a_trailing_newline_alone_earns_no_ellipsis() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, &fixture());

    let stdout = run(&proj, &["list", "--status", "Open"]);

    assert_eq!(
        row_for(&stdout, "WI-005"),
        format!("  WI-005 [Open] {TRAILING_NEWLINE_DESC}"),
        "no ellipsis over an empty tail: {stdout}"
    );
}

#[test]
fn long_flag_restores_the_full_text() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, &fixture());

    let stdout = run(&proj, &["list", "--status", "Open", "--long"]);

    assert!(
        stdout.contains(TAIL_WORD),
        "--long prints past the 100th char: {stdout}"
    );
    assert!(
        stdout.contains(BODY_WORD),
        "--long prints past the first line: {stdout}"
    );
    assert!(
        !stdout.contains('…'),
        "nothing is elided under --long: {stdout}"
    );
}

/// The tagged view truncated before WI-1097 and still does — this passes with
/// the change backed out, and is here to pin that the default-side fix did not
/// regress the view that was already right.
#[test]
fn tagged_view_still_truncates_without_the_flag() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, &fixture());

    let stdout = run(&proj, &["list", "--tag", "seq"]);

    assert!(
        stdout.contains(&format!("WI-001 [Open] {}…", head())),
        "the tagged row is still clipped at 100 chars: {stdout}"
    );
    assert!(
        !stdout.contains(TAIL_WORD),
        "the tagged view drops the tail: {stdout}"
    );
}

/// One flag, one meaning: `--long` widens the tagged sequence exactly as it
/// widens the plain listing.
#[test]
fn tagged_view_honors_long_flag() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, &fixture());

    let stdout = run(&proj, &["list", "--tag", "seq", "--long"]);

    assert!(
        stdout.contains(TAIL_WORD),
        "--long reaches the tagged view too: {stdout}"
    );
    assert!(
        stdout.contains(BODY_WORD),
        "--long prints the tagged item's body: {stdout}"
    );
}

/// A description that is single-line and under the clip is dropped-from by
/// nothing, so it must render identically in both modes — no stray ellipsis,
/// no lost character. Passes either way by design; it guards the shaping pass
/// against mangling the rows it has no work to do on.
#[test]
fn a_short_description_is_identical_in_both_modes() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, &fixture());

    let short = run(&proj, &["list", "--status", "Open"]);
    let long = run(&proj, &["list", "--status", "Open", "--long"]);

    let expected = format!("  WI-003 [Open] {SHORT_DESC}");
    assert_eq!(row_for(&short, "WI-003"), expected);
    assert_eq!(row_for(&long, "WI-003"), expected);
}
