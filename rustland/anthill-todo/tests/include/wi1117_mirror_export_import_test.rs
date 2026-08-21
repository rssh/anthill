//! WI-1117 — `export` publishes the tracker, `import` reads its comments back.
//!
//! Design: `docs/design/backend-github-coordination.md` §3.2, §7 (amended
//! 2026-08-17), §8.3. This drives the CLI end to end against the `FakeForge`,
//! which is the whole reason the fake is a first-class carrier rather than a
//! test helper: `gh` needs a network and an account, and nothing here has either.
//!
//! WHAT FAILS WITHOUT THE CHANGE: every test in this file. Before it there is no
//! `export`/`import` subcommand, no `Mirror` fact, no `MirrorEntry`, and no
//! `Forge` carrier — a project declaring one does not load.
//!
//! WHAT EACH TEST WOULD CATCH, since "it published something" is far too weak a
//! claim for a command whose entire contract is what the SECOND run does:
//!   * `export_publishes_...` — the entry reaches the target AND the link is
//!     written into the item's own file (both halves: an export that published
//!     without linking is not idempotent, and a link without an entry is a lie);
//!   * `a_second_export_...` — IDEMPOTENCE, the property the ticket is about:
//!     the same two items, no third entry, and the body updated in place;
//!   * `export_adopts_...` — an entry already there under the `<id>: ` title
//!     prefix is LINKED, not duplicated, which is what makes a fresh clone or a
//!     lost link recoverable;
//!   * `import_ingests_...` / `a_second_import_...` — the return channel and its
//!     dedup on `(workitem, author, at)`;
//!   * `import_skips_...` — the mirror does not echo its own comments back in;
//!   * `deleting_an_item_...` — the link is a satellite and goes with its item,
//!     the WI-1123 orphan-row failure applied to the row this ticket adds;
//!   * the access ladder — `--offline`, `ANTHILL_TODO_MIRROR`, an unconfigured
//!     project, and the precedence between the two overrides.
//!
//! WHAT PASSES EITHER WAY BY DESIGN: `a_project_with_no_mirror_still_works` —
//! the tracker must keep working with no mirror at all, so that test is a
//! regression guard rather than evidence for this ticket.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::common::setup_project;

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

fn run_in(proj: &Path, args: &[&str]) -> std::process::Output {
    let mut full = vec!["-d", proj.to_str().unwrap()];
    full.extend_from_slice(args);
    Command::new(BIN)
        .args(&full)
        .output()
        .expect("run anthill-todo")
}

fn ok(proj: &Path, args: &[&str]) -> String {
    let out = run_in(proj, args);
    assert!(
        out.status.success(),
        "{args:?} failed\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// A project on the item-per-file layout, publishing to a fake target in
/// `anthill-todo/mirror`. `MirrorEntry` is in `covers:` because the link is a
/// durable row like any other — a functor missing there keeps no durable home.
const MIRRORED_PROJECT: &str = r#"fact Project(
  name: "mirrored",
  language: "rust",
  build: "cargo",
  tools: ["cargo-test"])

fact anthill.persistence.ExtentBinding(
  store: anthill.persistence.filesystem.ItemPerFileStore(
    root: ".",
    status_field: "last_status_change.status",
    id_field: "id",
    ref_field: "workitem"),
  role: anthill.persistence.ExtentRole.mirror(),
  covers: [WorkItem, Feedback, Tag, MirrorEntry, StoreFormat])

fact Mirror(
  target: FakeForge(dir: "mirror"),
  access: MirrorAccess.enabled())
"#;

fn mirrored_project(tmp: &tempfile::TempDir) -> PathBuf {
    project_with(tmp, MIRRORED_PROJECT)
}

fn project_with(tmp: &tempfile::TempDir, config: &str) -> PathBuf {
    let proj = setup_project(tmp, "");
    fs::write(proj.join("anthill-todo/project.anthill"), config).expect("write project config");
    fs::remove_file(proj.join("anthill-todo/workitems.anthill")).expect("no shared file");
    proj
}

/// The id `add` minted, off its own output — WI-1121 removed the counter, so a
/// test cannot name an id in advance.
fn add(proj: &Path, description: &str) -> String {
    ok(proj, &["add", description])
        .split_whitespace()
        .nth(1)
        .expect("`added: <id> — …`")
        .to_string()
}

fn item_file(proj: &Path, state: &str, id: &str) -> PathBuf {
    proj.join("anthill-todo")
        .join(state)
        .join(format!("{id}.anthill.md"))
}

fn mirror_dir(proj: &Path) -> PathBuf {
    proj.join("anthill-todo/mirror")
}

/// Every entry handle the fake target holds, sorted, so a count and a set are
/// both readable off one answer.
fn entries(proj: &Path) -> Vec<String> {
    let dir = mirror_dir(proj);
    if !dir.exists() {
        return Vec::new();
    }
    let mut out: Vec<String> = fs::read_dir(&dir)
        .expect("read mirror dir")
        .filter_map(|e| {
            let path = e.expect("entry").path();
            (path.extension().and_then(|x| x.to_str()) == Some("entry"))
                .then(|| path.file_stem().unwrap().to_str().unwrap().to_string())
        })
        .collect();
    out.sort();
    out
}

fn entry_text(proj: &Path, entry: &str) -> String {
    fs::read_to_string(mirror_dir(proj).join(format!("{entry}.entry"))).expect("read entry")
}

/// The `- mirrors:` line of an item's file, or `None` when it carries no link.
fn link_line(proj: &Path, state: &str, id: &str) -> Option<String> {
    fs::read_to_string(item_file(proj, state, id))
        .expect("read item file")
        .lines()
        .find(|l| l.starts_with("- mirrors:"))
        .map(|l| l.to_string())
}

// ── export ───────────────────────────────────────────────────────

/// THE ACCEPTANCE, and it asserts BOTH halves. An export that wrote entries but
/// no links would pass a target-only check and then duplicate everything on its
/// next run; a link with no entry would pass an item-file-only check and fail at
/// the first update.
#[test]
fn export_publishes_an_entry_and_writes_the_link_into_the_item() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = mirrored_project(&tmp);
    let id = add(&proj, "a thing worth publishing");

    let out = ok(&proj, &["export"]);
    assert!(
        out.contains("1 item(s) written to fake:mirror"),
        "reports what it did: {out}"
    );

    assert_eq!(entries(&proj), vec!["1".to_string()], "one entry, handle `1`");
    let text = entry_text(&proj, "1");
    assert!(
        text.contains(&format!("title: {id}: a thing worth publishing")),
        "the title is `<id>: <summary>` (§7.1): {text}"
    );
    assert!(
        text.contains("Status: Open"),
        "the body carries the item's state: {text}"
    );
    assert!(
        text.contains("a thing worth publishing"),
        "and its description: {text}"
    );

    assert_eq!(
        link_line(&proj, "open", &id).as_deref(),
        Some("- mirrors: fake:mirror=1"),
        "the link is written into the item's own file, keyed by TARGET and entry"
    );
}

/// IDEMPOTENCE — the property this ticket is about. The second run must find the
/// link and UPDATE, so the target holds the same one entry and its content
/// tracks the tree.
///
/// The control is the description edit: an export that skipped already-linked
/// items would also leave one entry, and only the refreshed body tells the two
/// apart.
#[test]
fn a_second_export_updates_in_place_rather_than_publishing_again() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = mirrored_project(&tmp);
    let id = add(&proj, "before the edit");
    ok(&proj, &["export"]);

    ok(&proj, &["update", &id, "--description", "after the edit"]);
    let out = ok(&proj, &["export"]);

    assert_eq!(entries(&proj), vec!["1".to_string()], "still ONE entry");
    assert!(
        out.contains("(0 newly linked)"),
        "and nothing was newly linked: {out}"
    );
    let text = entry_text(&proj, "1");
    assert!(
        text.contains("after the edit"),
        "the entry was overwritten from the tree — tracker-wins: {text}"
    );
    assert!(
        !text.contains("before the edit"),
        "and the old content is gone, not appended to: {text}"
    );
}

/// ADOPTION: an entry already on the target under this item's title prefix is
/// LINKED rather than duplicated. That is what makes a fresh clone, a bad merge,
/// or a project whose `covers:` omitted `MirrorEntry` recoverable instead of a
/// second entry for every item.
///
/// The link is removed from the item file by hand, which is exactly the state
/// each of those produces: the target remembers, the tree does not.
#[test]
fn export_adopts_an_entry_whose_link_the_tree_has_lost() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = mirrored_project(&tmp);
    let id = add(&proj, "published once already");
    ok(&proj, &["export"]);

    let path = item_file(&proj, "open", &id);
    let text = fs::read_to_string(&path).expect("read item");
    fs::write(
        &path,
        text.lines()
            .filter(|l| !l.starts_with("- mirrors:"))
            .collect::<Vec<_>>()
            .join("\n"),
    )
    .expect("drop the link");
    assert_eq!(link_line(&proj, "open", &id), None, "the tree has forgotten");

    let out = ok(&proj, &["export"]);
    assert!(out.contains("adopted existing entry 1"), "says so: {out}");
    assert_eq!(
        entries(&proj),
        vec!["1".to_string()],
        "no second entry beside the one already there"
    );
    assert_eq!(
        link_line(&proj, "open", &id).as_deref(),
        Some("- mirrors: fake:mirror=1"),
        "and the link is back"
    );
}

// ── import ───────────────────────────────────────────────────────

/// Write the comments a target would have. Nothing in the tree generates one —
/// that is what makes ingestion sound (§7.3) — so a test authors them directly.
fn put_comments(proj: &Path, entry: &str, records: &str) {
    fs::write(mirror_dir(proj).join(format!("{entry}.comments")), records)
        .expect("write comments");
}

/// The return channel: a comment becomes a `Feedback` fact in the item's own
/// file, attributed to the identity that wrote it on the target.
#[test]
fn import_ingests_a_comment_as_feedback_on_the_item() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = mirrored_project(&tmp);
    let id = add(&proj, "will be commented on");
    ok(&proj, &["export"]);
    put_comments(
        &proj,
        "1",
        "author: octocat\nat: 2026-08-20T10:00:00Z\n--\nthis needs a test\n",
    );

    let out = ok(&proj, &["import"]);
    assert!(out.contains("1 new comment(s)"), "reports the count: {out}");

    let text = fs::read_to_string(item_file(&proj, "open", &id)).expect("read item");
    assert!(
        text.contains("this needs a test"),
        "the comment's text landed in the item: {text}"
    );
    assert!(
        text.contains("fake:mirror:octocat"),
        "attributed to <target>:<login>, so it cannot collide with a local agent \
         name and says WHICH target it came from: {text}"
    );
    assert!(
        text.contains("2026-08-20T10:00:00Z"),
        "at the time it was written on the target, not the time it was read: {text}"
    );
}

/// DEDUP ON `(workitem, author, at)` — the reason `import` is safe to re-run.
/// Without it every run would re-file every comment.
#[test]
fn a_second_import_adds_nothing() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = mirrored_project(&tmp);
    let id = add(&proj, "commented once");
    ok(&proj, &["export"]);
    put_comments(
        &proj,
        "1",
        "author: octocat\nat: 2026-08-20T10:00:00Z\n--\nsaid once\n",
    );
    ok(&proj, &["import"]);

    let out = ok(&proj, &["import"]);
    assert!(out.contains("0 new comment(s)"), "nothing new: {out}");

    let text = fs::read_to_string(item_file(&proj, "open", &id)).expect("read item");
    assert_eq!(
        text.matches("said once").count(),
        1,
        "and the comment is recorded exactly once: {text}"
    );
}

/// THE MIRROR MUST NOT ECHO INTO THE TRACKER IT MIRRORS. A comment opening with
/// this tool's own marker is not read back — otherwise a future `sync` that
/// explains itself in a comment would ingest its own explanation as feedback.
///
/// The control is the second record: both are in one file, and only the marked
/// one is skipped, so a reader that ingested nothing at all would fail here.
#[test]
fn import_skips_a_comment_this_tool_wrote() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = mirrored_project(&tmp);
    let id = add(&proj, "two comments, one skipped");
    ok(&proj, &["export"]);
    put_comments(
        &proj,
        "1",
        "author: hubot\nat: 2026-08-20T09:00:00Z\n--\n[anthill-todo] a note this tool wrote\n\
         ====\nauthor: octocat\nat: 2026-08-20T10:00:00Z\n--\na note a person wrote\n",
    );

    let out = ok(&proj, &["import"]);
    assert!(out.contains("1 new comment(s)"), "exactly one of two: {out}");

    let text = fs::read_to_string(item_file(&proj, "open", &id)).expect("read item");
    assert!(text.contains("a note a person wrote"), "the person's: {text}");
    assert!(
        !text.contains("a note this tool wrote"),
        "and not this tool's own: {text}"
    );
}

// ── the link is a satellite ──────────────────────────────────────

/// A link is dropped WITH the item it names — the same cascade `Feedback` and
/// `Tag` ride (WI-1123). A link left behind is a row describing an id nothing
/// holds: an `OrphanRow` fault at every later startup.
///
/// The control is the OTHER item's link, which must survive: a cascade that
/// retracted every `MirrorEntry` row would also pass a "the deleted one is gone"
/// check.
#[test]
fn deleting_an_item_takes_its_link_with_it() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = mirrored_project(&tmp);
    let doomed = add(&proj, "this one goes");
    let kept = add(&proj, "this one stays");
    ok(&proj, &["export"]);
    assert!(link_line(&proj, "open", &doomed).is_some());

    ok(&proj, &["delete", &doomed]);

    assert!(
        !item_file(&proj, "open", &doomed).exists(),
        "the item's file is gone, so its link cannot have been left in it"
    );
    assert!(
        link_line(&proj, "open", &kept).is_some(),
        "and the other item's link is untouched"
    );
    // The tracker must still LOAD: an orphaned row is a startup fault, so a
    // cascade that missed the link would surface as this command failing.
    ok(&proj, &["status"]);
}

// ── the access ladder (§3.2) ─────────────────────────────────────

/// `--offline` publishes nothing and SUCCEEDS. A configured-off run is a
/// configured state, not a failure — it is what a CI test job and an air-gapped
/// checkout do — and failing there would break builds behaving as configured.
#[test]
fn offline_publishes_nothing_and_succeeds() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = mirrored_project(&tmp);
    add(&proj, "not going anywhere");

    let out = ok(&proj, &["export", "--offline"]);
    assert!(out.contains("nothing published"), "says so: {out}");
    assert!(entries(&proj).is_empty(), "and nothing reached the target");
}

/// `ANTHILL_TODO_MIRROR=off` is the same override arriving from the environment,
/// which is where a PER-CHECKOUT answer lives — the project's own file cannot
/// know it is being read on a fork with no write access.
#[test]
fn the_environment_can_turn_the_mirror_off() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = mirrored_project(&tmp);
    add(&proj, "not going anywhere either");

    let out = Command::new(BIN)
        .args(["-d", proj.to_str().unwrap(), "export"])
        .env("ANTHILL_TODO_MIRROR", "off")
        .output()
        .expect("run anthill-todo");
    assert!(out.status.success(), "a configured-off run succeeds");
    assert!(
        String::from_utf8_lossy(&out.stdout).contains("nothing published"),
        "stdout: {}",
        String::from_utf8_lossy(&out.stdout)
    );
    assert!(entries(&proj).is_empty(), "and nothing reached the target");
}

/// THE CONTROL for both overrides: with neither, the same project publishes. A
/// build where `export` never published would pass the two tests above.
#[test]
fn the_control_without_an_override_the_same_project_publishes() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = mirrored_project(&tmp);
    add(&proj, "going somewhere");

    ok(&proj, &["export"]);
    assert_eq!(entries(&proj).len(), 1);
}

/// A `Mirror` fact saying `disabled` is the PROJECT-WIDE default, and
/// `ANTHILL_TODO_MIRROR=on` is what overrides it for one checkout. Without this,
/// the environment variable would be a one-way switch.
#[test]
fn the_environment_can_turn_a_disabled_mirror_on() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = project_with(&tmp, &MIRRORED_PROJECT.replace("enabled()", "disabled()"));
    add(&proj, "off by default");

    assert!(
        ok(&proj, &["export"]).contains("nothing published"),
        "the project's own default is off"
    );

    let out = Command::new(BIN)
        .args(["-d", proj.to_str().unwrap(), "export"])
        .env("ANTHILL_TODO_MIRROR", "on")
        .output()
        .expect("run anthill-todo");
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    assert_eq!(entries(&proj).len(), 1, "this checkout published anyway");
}

/// AN EXPLICIT FLAG WINS OVER THE ENVIRONMENT. Someone who typed `--offline` has
/// answered for this run, and a second answer arriving invisibly from the
/// environment would overrule the one they can see.
#[test]
fn an_explicit_flag_beats_the_environment() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = mirrored_project(&tmp);
    add(&proj, "the flag decides");

    let out = Command::new(BIN)
        .args(["-d", proj.to_str().unwrap(), "export", "--offline"])
        .env("ANTHILL_TODO_MIRROR", "on")
        .output()
        .expect("run anthill-todo");
    assert!(out.status.success());
    assert!(entries(&proj).is_empty(), "`--offline` won");
}

/// A project that declares no mirror is REFUSED rather than quietly doing
/// nothing: "export" on a tracker with nowhere to publish is a configuration
/// mistake, and the message names the fact to write.
#[test]
fn export_without_a_mirror_fact_is_refused() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = project_with(
        &tmp,
        &MIRRORED_PROJECT[..MIRRORED_PROJECT.find("fact Mirror(").expect("split")],
    );
    add(&proj, "nowhere to go");

    let out = run_in(&proj, &["export"]);
    assert!(!out.status.success(), "a usage error, not a silent no-op");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("declares no mirror"), "{err}");
    assert!(err.contains("fact Mirror"), "names what to write: {err}");
}

/// A TARGET NAME CARRYING THE ELEMENT SEPARATOR IS REFUSED **BEFORE ANYTHING IS
/// PUBLISHED**. A link is written as `<target>=<entry>` on one attributes line
/// and the reader splits at the first `=`, so such a name has no spelling there.
///
/// THE ORDERING IS THE ASSERTION. The document layer refuses this too, but only
/// at the persist step — which is after `create_entry` has already run, so the
/// entry exists on the target and the command then fails. On a forge that is a
/// real issue nobody asked for, once per item. The test therefore checks the
/// mirror directory is EMPTY, not merely that the command failed.
///
/// Driven through the carrier, which is where a target name actually comes from:
/// `FakeForge(dir: "a=b")` names itself `fake:a=b`.
#[test]
fn a_target_name_carrying_the_element_separator_is_refused_before_publishing() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = project_with(&tmp, &MIRRORED_PROJECT.replace(r#"dir: "mirror""#, r#"dir: "a=b""#));
    add(&proj, "will not be linkable");

    let out = run_in(&proj, &["export"]);
    assert!(!out.status.success(), "refused");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("fake:a=b"), "names the target: {err}");
    assert!(err.contains("nothing was published"), "{err}");
    assert!(
        !proj.join("anthill-todo/a=b").exists(),
        "and NOTHING reached the target — the refusal is before `create_entry`, \
         not after it"
    );
}

/// WHITESPACE IS THE QUIET ONE, and the reason the naming check exists rather
/// than being left to the document layer's separator refusal: a trailing space
/// SURVIVES the write and is TRIMMED on read, so the link reads back as a
/// different target, matches nothing, and every export publishes a fresh entry
/// for every item — with no error at any point.
///
/// The assertion is on the refusal AND on the empty target, because the failure
/// this prevents is silent success.
#[test]
fn a_target_name_with_trailing_whitespace_is_refused() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = project_with(&tmp, &MIRRORED_PROJECT.replace(r#"dir: "mirror""#, r#"dir: "mirror ""#));
    add(&proj, "would be re-published forever");

    let out = run_in(&proj, &["export"]);
    assert!(!out.status.success(), "refused");
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("whitespace"),
        "says which half of the name is wrong: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(entries(&proj).is_empty(), "nothing published");
}

/// `import` gets the SAME check, and it earns it differently: import only
/// COMPARES the target name against the links in the tree, so an unusable one
/// matches nothing and the command would report "0 new comment(s)" — a silent
/// all-clear on a return channel that is not working at all.
#[test]
fn import_refuses_an_unusable_target_name_rather_than_reporting_nothing_new() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = project_with(&tmp, &MIRRORED_PROJECT.replace(r#"dir: "mirror""#, r#"dir: "a=b""#));
    add(&proj, "unreadable channel");

    let out = run_in(&proj, &["import"]);
    assert!(!out.status.success(), "refused rather than reported clean");
    assert!(
        !String::from_utf8_lossy(&out.stdout).contains("0 new comment(s)"),
        "and it does NOT answer with an all-clear: {}",
        String::from_utf8_lossy(&out.stdout)
    );
}

/// AN ENTRY HANDLE REACHES A FILE PATH AND A COMMAND LINE, so it is checked
/// before it gets there. The handle arrives from a `- mirrors:` line — data
/// anyone can hand-edit and a merge can mangle — and `../../evil` would make the
/// fake write outside its own directory.
#[test]
fn a_hand_edited_entry_handle_that_escapes_the_target_is_refused() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = mirrored_project(&tmp);
    let id = add(&proj, "its link will be tampered with");
    ok(&proj, &["export"]);

    let path = item_file(&proj, "open", &id);
    let text = fs::read_to_string(&path).expect("read item");
    fs::write(
        &path,
        text.replace("- mirrors: fake:mirror=1", "- mirrors: fake:mirror=../../evil"),
    )
    .expect("tamper");

    let out = run_in(&proj, &["export"]);
    assert!(!out.status.success(), "refused");
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("usable entry handle"),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        !tmp.path().join("evil.entry").exists() && !proj.join("evil.entry").exists(),
        "and nothing was written outside the target's own directory"
    );
}

/// `ANTHILL_TODO_MIRROR=` (set, empty) is ABSENT, not an illegal value. That is
/// how a CI system writes a variable it has no value for, and injecting
/// `--mirror ""` would hard-fail both commands on a job that configured nothing.
#[test]
fn an_empty_environment_override_is_treated_as_unset() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = mirrored_project(&tmp);
    add(&proj, "published anyway");

    let out = Command::new(BIN)
        .args(["-d", proj.to_str().unwrap(), "export"])
        .env("ANTHILL_TODO_MIRROR", "")
        .output()
        .expect("run anthill-todo");
    assert!(
        out.status.success(),
        "an empty override must not fail the command: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(entries(&proj).len(), 1, "and the project's own default applies");
}

/// THE CONTROL for the empty case: a value that is set and NOT recognised is
/// still refused, naming the flag. Without it, "treat empty as absent" could
/// have been implemented as "ignore the variable".
#[test]
fn the_control_a_nonsense_environment_override_is_still_refused() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = mirrored_project(&tmp);
    add(&proj, "not published");

    let out = Command::new(BIN)
        .args(["-d", proj.to_str().unwrap(), "export"])
        .env("ANTHILL_TODO_MIRROR", "maybe")
        .output()
        .expect("run anthill-todo");
    assert!(!out.status.success());
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("--mirror"),
        "names the flag the value became: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(entries(&proj).is_empty());
}

// ── coverage of the link row ─────────────────────────────────────

/// A project WITH a mirror must declare `MirrorEntry` in its `covers:`. The
/// link is retracted with its item, and a retract needs the row's reference to
/// belong to the store being asked — an uncovered functor drops the in-memory row
/// and leaves the line on disk.
///
/// This is the test that DRIVES the mirrored-project detection: without it, a
/// `project_is_mirrored` that always answered `false` would pass every other
/// test in this file, because the fixture they share covers the row anyway.
#[test]
fn a_mirrored_project_must_cover_the_link() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = project_with(&tmp, &MIRRORED_PROJECT.replace(", MirrorEntry,", ","));

    let out = run_in(&proj, &["status"]);
    assert!(!out.status.success(), "refused at startup, before any command");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("MirrorEntry"), "names what is missing: {err}");
    assert!(err.contains("covers:"), "and where to add it: {err}");
}

/// THE CONTROL, and the reason the requirement is CONDITIONAL: a project with no
/// mirror cannot hold a link, so it is not asked to declare one. An unconditional
/// requirement would refuse, at startup, every existing tracker that has no
/// mirror and cannot reach the failure the requirement exists to prevent.
#[test]
fn the_control_an_unmirrored_project_need_not_cover_the_link() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let without_mirror = &MIRRORED_PROJECT[..MIRRORED_PROJECT.find("fact Mirror(").expect("split")];
    let proj = project_with(&tmp, &without_mirror.replace(", MirrorEntry,", ","));

    let id = add(&proj, "no mirror, no link");
    ok(&proj, &["delete", &id]);
}

/// PASSES BOTH WITH AND WITHOUT THE CHANGE, BY DESIGN. The tracker must keep
/// working with no mirror at all — no network, no target, nothing configured —
/// which is the constraint every other command in the tool is held to.
#[test]
fn a_project_with_no_mirror_still_works() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = project_with(
        &tmp,
        &MIRRORED_PROJECT[..MIRRORED_PROJECT.find("fact Mirror(").expect("split")],
    );

    let id = add(&proj, "purely local");
    ok(&proj, &["claim", &id, "--agent", "claude"]);
    ok(&proj, &["feedback", &id, "a local note"]);
    assert!(ok(&proj, &["show", &id]).contains("purely local"));
}
