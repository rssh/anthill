//! WI-1121 — an id is MINTED FROM THE ITEM, and any fragment of one resolves.
//!
//! Design: `rustland/anthill-todo/docs/design/backend-github-coordination.md`
//! §6.5 (the policy), §6.6 (two unsynced writers), §12. Allocation is a policy
//! now, and this is the local one: `WI-<YYYYMMDD>-<5 Crockford base32>-<slug>`
//! derived from the filing agent, the moment, and the description. No network,
//! no registry, no retry loop, no losing racer.
//!
//! WHAT FAILS WITHOUT THE CHANGE: every test here. Before it `add` drew from a
//! counter the host seeded off the highest `WI-NNN` on disk, so the shape
//! assertions fail, `mint_id` does not exist, and no fragment resolves.
//!
//! WHAT PASSES EITHER WAY BY DESIGN: nothing here — `an_exact_legacy_id_wins`
//! looks like it might, since `show WI-112` worked before the ladder existed,
//! but it is the ONE test that pins the ladder's single precedence rule, and it
//! fails the moment that rule is removed (the fragment then matches four items
//! and is reported as ambiguous).

use std::fs;
use std::path::Path;
use std::process::Command;

use crate::common::setup_project;

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

fn run_in(proj: &Path, args: &[&str]) -> std::process::Output {
    let mut full = vec!["-d", proj.to_str().unwrap()];
    full.extend_from_slice(args);
    Command::new(BIN).args(&full).output().expect("run anthill-todo")
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

fn fails(proj: &Path, args: &[&str]) -> String {
    let out = run_in(proj, args);
    assert!(
        !out.status.success(),
        "{args:?} unexpectedly succeeded: {}",
        String::from_utf8_lossy(&out.stdout)
    );
    String::from_utf8_lossy(&out.stderr).into_owned()
}

/// The id on the `added:` line.
fn added_id(stdout: &str) -> String {
    stdout
        .split_whitespace()
        .nth(1)
        .expect("`added: <id> — …`")
        .to_string()
}

/// `WI-` + eight digits + `-` + five uppercase Crockford characters, and
/// optionally `-` + a lowercase slug.
fn assert_minted_shape(id: &str) {
    let body = id.strip_prefix("WI-").unwrap_or_else(|| panic!("{id} keeps the reference marker"));
    let (day, rest) = body.split_at(8);
    assert!(
        day.chars().all(|c| c.is_ascii_digit()),
        "{id} starts with a YYYYMMDD partition"
    );
    let rest = rest.strip_prefix('-').unwrap_or_else(|| panic!("{id} separates day from digest"));
    let digest: String = rest.chars().take(5).collect();
    assert!(
        digest
            .chars()
            .all(|c| "0123456789ABCDEFGHJKMNPQRSTVWXYZ".contains(c)),
        "{id}: `{digest}` is not five Crockford base32 characters"
    );
}

const TWO_LEGACY_ITEMS: &str = "\
fact WorkItem(
  id: \"WI-001\",
  created: \"2026-01-01T00:00:00Z\",
  description: \"first\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  last_status_change: StatusChange(status: Open()))

fact WorkItem(
  id: \"WI-005\",
  created: \"2026-01-01T00:00:00Z\",
  description: \"fifth\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  last_status_change: StatusChange(status: Open()))
";

/// THE POLICY, in one assertion: the id does not continue the sequence on disk.
/// A counter would have answered `WI-006` here, and the point of §6.5 is that
/// there is no counter to continue — two checkouts that have not synced cannot
/// both draw the same next number, because neither draws.
#[test]
fn an_id_is_minted_from_the_item_not_from_the_highest_on_disk() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, TWO_LEGACY_ITEMS);

    let id = added_id(&ok(
        &proj,
        &["add", "item per file store", "--created", "2026-08-17T10:22:03Z"],
    ));

    assert_ne!(id, "WI-006", "the counter is gone, not merely reseeded");
    assert_minted_shape(&id);
    assert!(
        id.starts_with("WI-20260817-"),
        "{id} carries the day it was filed, so a plain sort reads chronologically"
    );
    assert!(
        id.ends_with("-item-per-file-store"),
        "{id} carries a slug, which is what makes `ls open/` a table of contents"
    );
}

/// IDEMPOTENCE — the one thing hashing gives over plain entropy (§6.5). A
/// retried `add` re-derives the same id, finds its own half-written item and
/// heals, where a random token would file a second one.
///
/// `--created` is what makes this observable at all: without a settable stamp
/// the property only holds when both runs land in the same second.
#[test]
fn the_same_add_twice_re_derives_one_id_and_files_one_item() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");

    let first = ok(&proj, &["add", "retried", "--created", "2026-08-17T10:22:03Z"]);
    let second = ok(&proj, &["add", "retried", "--created", "2026-08-17T10:22:03Z"]);

    let id = added_id(&first);
    assert!(
        second.starts_with("already filed:"),
        "the retry recognised its own work: {second}"
    );
    assert!(second.contains(&id), "and named the same id: {second}");
    assert!(
        ok(&proj, &["status"]).contains("1 work item(s)"),
        "one item, not two"
    );
}

/// A DIFFERENT item in the same partition is a different id — the attempt
/// counter advances only for a genuine collision, and here there is not even
/// one, because the descriptions differ.
#[test]
fn two_different_items_in_one_second_get_different_ids() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");

    let a = added_id(&ok(&proj, &["add", "alpha thing", "--created", "2026-08-17T10:22:03Z"]));
    let b = added_id(&ok(&proj, &["add", "beta thing", "--created", "2026-08-17T10:22:03Z"]));

    assert_ne!(a, b);
    assert!(ok(&proj, &["status"]).contains("2 work item(s)"));
}

/// AN EMPTY SLUG IS LEGAL AND THEN OMITTED. A description in a non-Latin script
/// keeps nothing, and the id must still be well-formed — which is why §6.5 says
/// the slug can never be load-bearing.
#[test]
fn a_non_latin_description_still_yields_an_id_with_no_slug() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");

    let id = added_id(&ok(
        &proj,
        &["add", "Перевірка типів", "--created", "2026-08-17T10:22:03Z"],
    ));

    assert_minted_shape(&id);
    assert_eq!(id.len(), "WI-20260817-K7M2Q".len(), "{id} is day-digest alone");
    assert!(ok(&proj, &["show", &id]).contains("Перевірка типів"));
}

/// THE LADDER (§6.5): every part of an id is separately addressable, and the
/// reading is not chosen by precedence — it is whichever one matches uniquely.
#[test]
fn a_reference_resolves_by_digest_by_day_digest_or_by_slug() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    let id = added_id(&ok(
        &proj,
        &["add", "the resolution ladder", "--created", "2026-08-17T10:22:03Z"],
    ));
    let digest: String = id.chars().skip("WI-20260817-".len()).take(5).collect();

    for fragment in [
        format!("WI-{digest}"),                    // digest
        format!("WI-{}", &digest[..3]),            // a prefix of one
        format!("WI-20260817-{digest}"),           // the day-digest handle
        "WI-the-resolution".to_string(),           // a slug prefix
        id.clone(),                                // the whole thing
    ] {
        assert!(
            ok(&proj, &["show", &fragment]).contains(&id),
            "`{fragment}` did not resolve to {id}"
        );
    }
}

/// AMBIGUITY IS REPORTED WITH THE CANDIDATES, never resolved by precedence — the
/// way git reports an ambiguous object name. A repeated slug is not a defect
/// (§6.5: it groups a family), so the candidate list is itself the answer.
#[test]
fn an_ambiguous_fragment_names_its_candidates_and_writes_nothing() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    let a = added_id(&ok(&proj, &["add", "flaky test one", "--created", "2026-08-17T10:22:03Z"]));
    let b = added_id(&ok(&proj, &["add", "flaky test two", "--created", "2026-08-17T10:22:04Z"]));

    let err = fails(&proj, &["claim", "WI-flaky-test", "--agent", "claude"]);
    assert!(err.contains("ambiguous"), "{err}");
    assert!(err.contains(&a) && err.contains(&b), "both candidates named: {err}");
    assert!(
        ok(&proj, &["status"]).contains("Open: 2"),
        "and neither was claimed"
    );
}

/// THE LADDER'S ONE PRECEDENCE RULE, and the reason it has to exist: legacy ids
/// are GRANDFATHERED and dense, so `WI-112` is a whole id AND a prefix of
/// `WI-1120`. Without the exact-match rule the ladder would refuse a reference
/// that names one item unambiguously — for a hundred ids this tracker has
/// already published.
#[test]
fn an_exact_legacy_id_wins_over_being_a_prefix_of_another() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(
        &tmp,
        "fact WorkItem(id: \"WI-112\", created: \"2026-01-01T00:00:00Z\", \
         description: \"the short one\", acceptance: [], last_status_change: StatusChange(status: Open()))\n\
         fact WorkItem(id: \"WI-1120\", created: \"2026-01-02T00:00:00Z\", \
         description: \"the long one\", acceptance: [], last_status_change: StatusChange(status: Open()))\n",
    );

    let shown = ok(&proj, &["show", "WI-112"]);
    assert!(shown.contains("the short one"), "{shown}");
    assert!(!shown.contains("the long one"), "{shown}");
    // …and a fragment that is nobody's whole id still reports both.
    let err = fails(&proj, &["show", "WI-11"]);
    assert!(err.contains("ambiguous") && err.contains("WI-1120"), "{err}");
}

/// `--depends` NAMES AN ITEM TOO, and `depends_on` stores whole ids: a fragment
/// written there would be a dangling edge that reads like a real one.
#[test]
fn a_depends_fragment_is_expanded_to_the_whole_id() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    let target = added_id(&ok(&proj, &["add", "the prerequisite", "--created", "2026-08-17T10:22:03Z"]));
    let digest: String = target.chars().skip("WI-20260817-".len()).take(5).collect();

    ok(
        &proj,
        &["add", "the dependent", "--created", "2026-08-17T10:22:04Z", "--depends", &format!("WI-{digest}")],
    );

    let written = fs::read_to_string(proj.join("anthill-todo/workitems.anthill")).expect("read");
    assert!(
        written.contains(&format!("[\"{target}\"]")),
        "the fragment was stored as written: {written}"
    );
}

/// THE `created` GATE. The field feeds the mint and the listing's order, and a
/// missing one reaches both as a fresh var — so it is refused at startup, before
/// any command reads it, and the message names the conversion that fills it in.
#[test]
fn an_item_with_no_created_stamp_blocks_every_command() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(
        &tmp,
        "fact WorkItem(id: \"WI-900\", description: \"undated\", acceptance: [], last_status_change: StatusChange(status: Open()))\n",
    );

    let err = fails(&proj, &["list"]);
    assert!(err.contains("WI-900"), "the offending item is named: {err}");
    assert!(err.contains("`created`"), "{err}");
    // A remedy that EXISTS for the layout this project is on. `fsck --fix` dates
    // each item from its own file; the migration's table is the other route.
    assert!(err.contains("fsck --fix"), "the remedy is named: {err}");
    assert!(err.contains("--created-from"), "and the other one: {err}");
}

/// THE ORDER IS `created`, NOT THE ID — the change that had to come with the
/// mint, because a content-derived id carries the day and then a digest, so
/// within one day id order is digest order.
///
/// THE CONTROL is that the two disagree here: `WI-900` sorts before `WI-901`
/// numerically and after it chronologically, so a listing still keyed on the id
/// prints them the other way round.
#[test]
fn the_listing_orders_by_created_not_by_id() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(
        &tmp,
        "fact WorkItem(id: \"WI-900\", created: \"2026-02-02T00:00:00Z\", \
         description: \"filed second\", acceptance: [], last_status_change: StatusChange(status: Open()))\n\
         fact WorkItem(id: \"WI-901\", created: \"2026-01-01T00:00:00Z\", \
         description: \"filed first\", acceptance: [], last_status_change: StatusChange(status: Open()))\n",
    );

    let listed = ok(&proj, &["list"]);
    let first = listed.find("WI-901").expect("WI-901 listed");
    let second = listed.find("WI-900").expect("WI-900 listed");
    assert!(
        first < second,
        "the older item comes first even though its number is higher:\n{listed}"
    );
}

// ── The repair for a hand-added file ───────────────────────────

const ITEM_PER_FILE_BINDING: &str = r#"fact Project(
  name: "hand-written",
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
  covers: [WorkItem, Feedback, Tag, StoreFormat])
"#;

/// A WORK ITEM SOMEBODY WROTE BY HAND, with no `created` — which is not an exotic
/// case, it is what happens whenever a person edits the tree instead of running
/// `add`. The field is required, so the loader fills the omission with a fresh
/// VAR, and the gate refuses because a var can be neither sorted nor hashed.
///
/// REFUSING IS RIGHT; REFUSING WITH NO WAY FORWARD IS NOT. The filesystem knows
/// when that file was made, and under a file-per-item layout that time IS the
/// item's — so `fsck --fix` dates it and writes the row back.
///
/// THE CHAPTER IS THE CONTROL. The fill is a HEAD-only change, so the prose
/// beside it must come through byte-identical; a repair that re-rendered the
/// whole file would pass every other assertion here and quietly reflow a
/// description.
#[test]
fn fsck_fix_dates_a_hand_written_item_from_its_file() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    fs::write(proj.join("anthill-todo/project.anthill"), ITEM_PER_FILE_BINDING)
        .expect("write project config");
    fs::remove_file(proj.join("anthill-todo/workitems.anthill")).expect("no shared file");
    let dir = proj.join("anthill-todo/open");
    fs::create_dir_all(&dir).expect("mkdir");
    let path = dir.join("WI-hand-written.anthill.md");
    let prose = "somebody wrote this by hand\n\n#### and added a note\n\nkeep me.";
    fs::write(
        &path,
        format!(
            "## Attributes\n\n- id: WI-hand-written\n\n- status: Open\n\n## Description\n\n{prose}\n"
        ),
    )
    .expect("write");

    // It blocks, and the message names the repair that works on THIS layout.
    let err = fails(&proj, &["list"]);
    assert!(err.contains("WI-hand-written"), "{err}");
    assert!(err.contains("fsck --fix"), "the remedy is named: {err}");

    let fixed = ok(&proj, &["fsck", "--fix"]);
    assert!(fixed.contains("dated WI-hand-written from its file"), "{fixed}");

    let text = fs::read_to_string(&path).expect("read");
    assert!(text.contains("- created: 20"), "the stamp was written: {text}");
    assert!(!text.contains("?created"), "and it is a value, not a var: {text}");
    let chapter = text.split_once("## Description\n\n").expect("the chapter").1;
    assert_eq!(chapter.trim_end(), prose, "the prose is untouched");

    // …and the tracker reads.
    assert!(ok(&proj, &["list"]).contains("WI-hand-written"));
}
