//! WI-1123 — `delete <id>` takes the item's satellite rows with it, and names the
//! `depends_on` edges it deliberately leaves standing.
//!
//! THE MEASURED BUG: `WorkItemStore.forget` retracted only the `WorkItem` row, so
//! every `Feedback` and `Tag` row keyed `workitem: <id>` outlived the item it
//! described. Found during WI-1118's migration rehearsal on this repo's own
//! tracker — two `Feedback` rows naming a `WI-237` whose item had been deleted
//! months earlier, invisible because every row shared one file.
//!
//! WHAT THE FIX IS: `Feedback` is now `non_monotone` (store.anthill §0 carries the
//! argument — the append-only rule was about not rewriting a LIVE item's history,
//! and proposal 053's per-functor vocabulary cannot say "retractable only with its
//! item"), and `forget` buffers the satellites with the item and flushes once.
//!
//! CONTROLS, MEASURED by backing each half out and re-running, not asserted from
//! reading. Drop `forget_satellites_buffer` from `forget` and FOUR fail —
//! `delete_takes_the_items_feedback_and_tags_with_it`,
//! `the_deleted_rows_do_not_come_back_on_the_next_load`,
//! `delete_removes_the_items_file_and_fsck_stays_clean` and
//! `deleting_one_item_leaves_another_items_satellites_alone`. Drop the
//! `warn_dangling_deps` call from `cmd_delete` and exactly ONE fails,
//! `delete_names_the_items_that_still_depend_on_it`. Drop the
//! `check_covers_every_retracted_functor` call and one more fails,
//! `a_binding_that_omits_feedback_is_refused_with_the_fix`. Drop the status filter
//! from `blocked_dependents_of` and `a_finished_dependent_is_not_named_but_an_open_one_is`
//! fails.
//! `delete_with_no_dependents_adds_no_warning` passes either way BY DESIGN, and so
//! do the BYSTANDER halves of
//! `deleting_one_item_leaves_another_items_satellites_alone`: those two pin that
//! the cascade and the warning are SCOPED, which is the half a too-eager fix
//! breaks and which no other test here would catch.

use std::fs;
use std::path::Path;
use std::process::Command;

use crate::common::{read_combined, setup_project};

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

/// The per-file layout's binding, copied from `wi1114_item_per_file_backend_test`:
/// the one thing a project changes to move layouts is the store term.
const ITEM_PER_FILE_BINDING: &str = r#"fact Project(
  name: "per-file",
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

fn per_file_project(tmp: &tempfile::TempDir) -> std::path::PathBuf {
    let proj = setup_project(tmp, "");
    fs::write(
        proj.join("anthill-todo/project.anthill"),
        ITEM_PER_FILE_BINDING,
    )
    .expect("write project config");
    fs::remove_file(proj.join("anthill-todo/workitems.anthill")).expect("no shared file");
    proj
}

/// The id `add` minted, off its own output — WI-1121 removed the counter, so a
/// test cannot name `WI-001` in advance.
fn add(proj: &Path, description: &str) -> String {
    ok(proj, &["add", description])
        .split_whitespace()
        .nth(1)
        .expect("`added: <id> — …`")
        .to_string()
}

// ── The cascade (a): the item's satellite rows ─────────────────

/// THE TICKET'S ACCEPTANCE, driven: add an item, attach feedback and a tag, delete,
/// and assert on the store's ACTUAL ROWS. "delete exited 0" is what the old,
/// leaking `delete` also did.
///
/// FAILS WITHOUT THE CHANGE — every `Feedback`/`Tag` assertion below is exactly
/// what used to be left behind.
#[test]
fn delete_takes_the_items_feedback_and_tags_with_it() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    let inner = proj.join("anthill-todo");

    let id = add(&proj, "doomed");
    ok(&proj, &["feedback", &id, "first note"]);
    ok(&proj, &["feedback", &id, "second note"]);
    ok(&proj, &["tag", &id, "cascade"]);

    let before = read_combined(&inner);
    assert!(before.contains("first note") && before.contains("second note"));
    assert!(before.contains(&format!("Tag(workitem: \"{id}\", name: \"cascade\")")));

    assert!(ok(&proj, &["delete", &id]).contains(&format!("deleted: {id}")));

    let after = read_combined(&inner);
    assert!(
        !after.contains(id.as_str()),
        "no row naming the deleted item is left anywhere: {after}"
    );
    assert!(!after.contains("first note"), "feedback row 1 left: {after}");
    assert!(!after.contains("second note"), "feedback row 2 left: {after}");
    assert!(!after.contains("cascade"), "the tag row left: {after}");
}

/// The rows the delete dropped are gone for the NEXT process too. Without this the
/// assertions above are about bytes nobody has parsed back — and a retract that
/// dropped the in-memory rule while leaving the block would pass them all.
///
/// FAILS WITHOUT THE CHANGE: `show` renders the stranded feedback under the
/// re-created item, and it is a `Feedback` row on disk either way.
#[test]
fn the_deleted_rows_do_not_come_back_on_the_next_load() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");

    // WI-1121 CHANGED HOW THE ID COMES BACK, not whether it can. A counter freed
    // the number and the next `add` happened to reuse it; a derived id is
    // re-derived by filing the same content again — same agent, same `created`,
    // same description — which is a SHARPER version of the same hazard, because
    // it is reproducible rather than incidental.
    let stamp = "2026-08-17T10:22:03Z";
    let id = ok(&proj, &["--agent", "claude", "add", "doomed", "--created", stamp]);
    let id = id.split_whitespace().nth(1).expect("an id").to_string();
    ok(&proj, &["feedback", &id, "a note about the doomed one"]);
    ok(&proj, &["delete", &id]);

    let again = ok(&proj, &["--agent", "claude", "add", "doomed", "--created", stamp]);
    assert!(
        again.contains(&id),
        "the same content re-derives the same id: {again}"
    );
    let shown = ok(&proj, &["show", &id]);
    assert!(shown.contains("doomed"), "{shown}");
    assert!(
        !shown.contains("a note about the doomed one"),
        "the deleted item's feedback resurfaced on its successor: {shown}"
    );
}

/// Two-sided, and deliberately: the cascade is keyed on the `workitem` FIELD, so
/// it must take the deleted item's satellites and leave a neighbour's alone.
///
/// THE `goes away` ASSERTION FAILS WITHOUT THE CHANGE. The three BYSTANDER
/// assertions pass either way by design, and they are the control no other test
/// here supplies: a sweep that dropped every `Feedback`/`Tag` row, or one that
/// matched on functor rather than key, satisfies every assertion in the tests
/// above and fails only here.
#[test]
fn deleting_one_item_leaves_another_items_satellites_alone() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    let inner = proj.join("anthill-todo");

    let id = add(&proj, "doomed");
    let bystander = add(&proj, "bystander");
    ok(&proj, &["feedback", &id, "goes away"]);
    ok(&proj, &["feedback", &bystander, "stays put"]);
    ok(&proj, &["tag", &bystander, "keepme"]);

    ok(&proj, &["delete", &id]);

    let after = read_combined(&inner);
    assert!(!after.contains("goes away"), "{after}");
    assert!(after.contains("stays put"), "the bystander's feedback: {after}");
    assert!(
        after.contains(&format!("Tag(workitem: \"{bystander}\", name: \"keepme\")")),
        "the bystander's tag: {after}"
    );
    assert!(ok(&proj, &["show", &bystander]).contains("stays put"));
}

// ── The per-file layout: the item's FILE ───────────────────────

/// The ticket's extra acceptance under `ItemPerFileStore`: the item's file is GONE,
/// not left holding stranded rows. This is the layout in which the old behaviour
/// was loud — a file named after an item that no longer exists, reported as
/// `LayoutFault::OrphanRow` at every startup.
///
/// THE `fsck` ASSERTION IS THE CONTROL FOR THE FILE ASSERTION. Removing the file
/// and leaving the rows unretracted somewhere else would satisfy the first check
/// alone; a clean `fsck` says no row anywhere names an item no file holds.
///
/// FAILS WITHOUT THE CHANGE: the file survives holding two orphaned rows, and
/// `fsck` names them.
#[test]
fn delete_removes_the_items_file_and_fsck_stays_clean() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);

    let id = add(&proj, "doomed");
    ok(&proj, &["feedback", &id, "a note in the item's own file"]);
    ok(&proj, &["tag", &id, "cascade"]);
    // WI-1120: an item file is a DOCUMENT, `WI-….anthill.md`.
    let item_file = proj.join(format!("anthill-todo/open/{id}.anthill.md"));
    let text = fs::read_to_string(&item_file).expect("the item has a file");
    assert!(
        text.contains("a note in the item's own file") && text.contains("name: \"cascade\""),
        "the satellites are filed in the item's file: {text}"
    );

    ok(&proj, &["delete", &id]);

    assert!(
        !item_file.exists(),
        "the file went with its last row, rather than standing with stranded ones"
    );
    assert!(
        ok(&proj, &["fsck"]).contains("layout ok"),
        "and nothing anywhere names an item no file holds"
    );
}

// ── (b): the depends_on edges, named and NOT deleted ───────────

/// Deleting an item other items depend on is not a cascade over the ITEM graph —
/// in the case that prompted this, `WI-237` would have taken three items with it.
/// But it is not silent either: a dep naming no work item counts as UNMET, so each
/// dependent quietly stops being claimable.
///
/// FAILS WITHOUT THE `cmd_delete` WARNING (and passes with the store cascade backed
/// out): the delete succeeds and prints nothing about the edges.
#[test]
fn delete_names_the_items_that_still_depend_on_it() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");

    let id = add(&proj, "the prerequisite");
    let one = ok(&proj, &["add", "waits on it", "--depends", &id]);
    let one = one.split_whitespace().nth(1).expect("an id").to_string();
    let two = ok(&proj, &["add", "also waits on it", "--depends", &id]);
    let two = two.split_whitespace().nth(1).expect("an id").to_string();

    let out = run_in(&proj, &["delete", &id]);
    assert!(out.status.success(), "the delete still succeeds: {out:?}");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        err.contains(&one) && err.contains(&two),
        "every dependent is named: {err}"
    );
    assert!(
        err.contains("remove-dependency"),
        "and the command that clears one: {err}"
    );

    // NOT deleted — the dependents and their edges are exactly as they were.
    let listed = ok(&proj, &["list"]);
    assert!(
        listed.contains(&one) && listed.contains(&two),
        "the dependents are still there: {listed}"
    );
    assert!(
        crate::common::workitem_block_contains(
            &read_combined(&proj.join("anthill-todo")),
            &one,
            &id
        ),
        "and their edges are untouched — clearing them is the user's call"
    );
}

// ── The binding the cascade now depends on ─────────────────────

/// A binding that does not name `Feedback` in its `covers:` is refused AT STARTUP,
/// by name, with the fix.
///
/// MEASURED, and the reason this guard exists: with `covers: [WorkItem, Tag,
/// StoreFormat]` the tool used to work until the first `delete`, which then died
/// with `retract: FactRef does not belong to the supplied store` — true and loud
/// and diagnosing nothing, since the reader is looking at `delete` and the fault is
/// four lines of `project.anthill`. The old `delete` never touched `Feedback`, so
/// the omission cost nothing and stayed invisible; making the cascade real is what
/// turned it into a failure, and it should fail where it can be read.
///
/// FAILS WITHOUT THE GUARD: `list` succeeds on a binding that will not survive its
/// first delete.
#[test]
fn a_binding_that_omits_feedback_is_refused_with_the_fix() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    fs::write(
        proj.join("anthill-todo/project.anthill"),
        ITEM_PER_FILE_BINDING.replace("[WorkItem, Feedback, Tag, StoreFormat]", "[WorkItem, Tag]"),
    )
    .expect("write project config");

    let out = run_in(&proj, &["list"]);
    assert!(!out.status.success(), "an incomplete binding refuses: {out:?}");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        err.contains("Feedback"),
        "the missing functor is named: {err}"
    );
    assert!(
        err.contains("covers") && err.contains("project.anthill"),
        "and where to put it: {err}"
    );
    assert!(
        err.contains("delete"),
        "and what would otherwise have broken: {err}"
    );
    // THE REMEDY MUST BE THE SPELLING THAT WORKS (found in review). The guard
    // compares QUALIFIED names — that is what a resolved symbol gives back — but a
    // `covers:` list is read where `Feedback` resolves and `anthill.stage0.Feedback`
    // does not, so a message naming the qualified form sends the reader to a
    // spelling that is refused again, identically: an unrecoverable loop.
    assert!(
        !err.contains("anthill.stage0."),
        "no qualified name is offered as the fix: {err}"
    );

    // Driven, not read: doing what the message says makes the project work.
    fs::write(
        proj.join("anthill-todo/project.anthill"),
        ITEM_PER_FILE_BINDING.replace("[WorkItem, Feedback, Tag, StoreFormat]", "[WorkItem, Feedback, Tag]"),
    )
    .expect("write project config");
    assert!(
        run_in(&proj, &["list"]).status.success(),
        "adding the named functor in the named spelling clears it"
    );
}

/// A FINISHED dependent is not named. An unmet dep gates CLAIMING and nothing
/// else, so a `Delivered`/`Verified` item's stale edge costs nothing — and on this
/// repo's own tracker the most-referenced ids carry up to nine dependents, nearly
/// all delivered, which would bury the one item that is genuinely stuck.
///
/// THE OPEN DEPENDENT IS THE CONTROL: it must still be named in the same run, so
/// this cannot pass by the warning going quiet altogether. Found in review.
#[test]
fn a_finished_dependent_is_not_named_but_an_open_one_is() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");

    let id = add(&proj, "the prerequisite");
    let finished = ok(&proj, &["add", "finished long ago", "--depends", &id]);
    let finished = finished.split_whitespace().nth(1).expect("an id").to_string();
    let waiting = ok(&proj, &["add", "still waiting", "--depends", &id]);
    let waiting = waiting.split_whitespace().nth(1).expect("an id").to_string();
    ok(&proj, &["--agent", "claude", "claim", &finished]);
    ok(&proj, &["--agent", "claude", "deliver", &finished]);
    ok(&proj, &["verify", &finished]);

    let out = run_in(&proj, &["delete", &id]);
    assert!(out.status.success(), "{out:?}");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        err.contains(&waiting),
        "the open dependent is still named: {err}"
    );
    assert!(
        !err.contains(&finished),
        "the verified one is not — its stale edge costs nothing: {err}"
    );
}

/// PASSES EITHER WAY BY DESIGN: the warning is CONDITIONAL. An unconditional note
/// on every delete would be noise, and would stop distinguishing the state that
/// needs attention from the ordinary one.
#[test]
fn delete_with_no_dependents_adds_no_warning() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    let id = add(&proj, "depended on by nobody");

    let out = run_in(&proj, &["delete", &id]);
    assert!(out.status.success());
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        !err.contains("depends_on") && !err.contains("remove-dependency"),
        "nothing to warn about, so nothing is said: {err}"
    );
}
