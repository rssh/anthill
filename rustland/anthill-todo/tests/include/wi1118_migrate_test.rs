//! WI-1118 — `migrate --to item-per-file`: THE LAYOUT MOVE.
//!
//! Design: `docs/design/backend-github-coordination.md` §11 (migration), §4 (the
//! layout it produces), §3.1 (the binding that names it).
//!
//! WHAT THIS SHIPS is increment 6 of WI-437 reduced to what it turned out to be: a
//! purely local rewrite. Creating one mirror entry per item was step 2 for as long
//! as the forge ALLOCATED ids; with ids minted locally that is `export`, run
//! separately. So there is no network here and nothing to resume across an API —
//! which is also why these tests need no forge stub.
//!
//! WHAT DRIVES WHAT. `a_migrated_project_is_a_working_tracker` is the load-bearing
//! one: it migrates and then RUNS the CLI against the result, claiming an item and
//! watching its file move with its feedback aboard. Every other test here would
//! pass against a migrator that wrote a correct-looking tree the CLI could not
//! then use.
//!
//! WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT: all of them — `migrate --to`
//! does not exist before this change, so each one gets "unknown option" or an
//! unmigrated tree. The ones that would pass against a NAIVE migrator and so carry
//! the real weight are called out at their sites:
//!   * `a_migrated_project_is_a_working_tracker` — a migrator that wrote the files
//!     but left the binding naming the old layout passes every "the file exists"
//!     assertion here and produces a tracker that reads nothing.
//!   * `the_binding_rewrite_keeps_the_prose_around_it` — regenerating
//!     `project.anthill` wholesale yields a CORRECT binding and silently drops the
//!     comments explaining it.
//!   * `an_orphan_satellite_is_carried_across_and_reported` — the store refuses an
//!     unplaceable row at `persist`, so a migrator that just fed everything
//!     through it dies mid-flush naming one row. Orphans are not a defect to clean
//!     up first: `Feedback` is `monotone`, so `delete` always leaves some behind.
//!   * `the_data_format_stamp_is_not_bumped` — §11 step 4 as drafted said to stamp
//!     version 2. This asserts the opposite, so it fails the moment someone
//!     implements the step as written; the reasoning is in §11 and `MIGRATE_USAGE`.
//!   * `a_file_holding_a_rule_beside_its_rows_is_refused` — migration DELETES the
//!     files it consumes, and the first cut decided "is this a store file?" by
//!     counting facts, which is blind to every other kind of item. It deleted a
//!     rule.
//!   * `re_migrating_a_finished_tree_changes_nothing` — compares the WHOLE tree, so
//!     it fails against anything that rewrites a finished tree, not just against
//!     one that visibly damages it.
//!   * `a_project_declaring_the_backend_before_migrating_is_told_what_to_do` —
//!     answering that state from the BINDING made it a dead end, and the ordinary
//!     path never reaches it (it writes the binding itself, last).

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::common::{setup_domainless_project, setup_project};

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

fn run_in(proj: &Path, args: &[&str]) -> std::process::Output {
    let mut full = vec!["-d", proj.to_str().unwrap()];
    full.extend_from_slice(args);
    Command::new(BIN).args(&full).output().expect("run anthill-todo")
}

fn migrate(proj: &Path) -> std::process::Output {
    run_in(proj, &["migrate", "--to", "item-per-file"])
}

fn stderr(out: &std::process::Output) -> String {
    String::from_utf8_lossy(&out.stderr).to_string()
}

fn stdout(out: &std::process::Output) -> String {
    String::from_utf8_lossy(&out.stdout).to_string()
}

/// Two items in different states, one of them carrying both kinds of satellite, plus
/// the store-level stamp. Enough to exercise all three of the store's routes.
const ITEMS: &str = r#"fact StoreFormat(version: 1)

fact WorkItem(
  id: "WI-001",
  description: "the open one",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Open)

fact Feedback(workitem: "WI-001", author: "user", content: "a note", at: "2026-01-01T00:00:00Z")

fact Tag(workitem: "WI-001", name: "probe")

fact WorkItem(
  id: "WI-002",
  description: "the delivered one",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  status: Delivered(agent: "claude", at: "2026-01-02T00:00:00Z"))
"#;

fn read(proj: &Path, rel: &str) -> String {
    let path = proj.join("anthill-todo").join(rel);
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

fn store_dir(proj: &Path) -> PathBuf {
    proj.join("anthill-todo")
}

/// §4: a directory per state, a file per item, and every fact about an item in its
/// own file. The satellites are the point — a migrator that filed only the primary
/// rows would leave the feedback and the tag with no home at all.
#[test]
fn migrate_explodes_the_store_into_one_file_per_item() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, ITEMS);

    let out = migrate(&proj);
    assert!(out.status.success(), "migrate failed: {}", stderr(&out));

    let one = read(&proj, "open/WI-001.anthill");
    assert!(one.contains(r#"id: "WI-001""#), "the item's own row:\n{one}");
    assert!(one.contains("a note"), "its feedback rides along:\n{one}");
    assert!(one.contains(r#"name: "probe""#), "its tag rides along:\n{one}");

    let two = read(&proj, "delivered/WI-002.anthill");
    assert!(two.contains(r#"id: "WI-002""#), "filed by its own status:\n{two}");

    // The store-level row — neither a primary nor a satellite — is filed under its
    // own functor at the root (§8.3's third route).
    assert!(
        read(&proj, "store_format.anthill").contains("StoreFormat"),
        "the format stamp keeps a durable home"
    );

    // And the file it all came out of is gone: a tracker with both would answer
    // every read twice.
    assert!(
        !store_dir(&proj).join("workitems.anthill").exists(),
        "the migrated file is removed"
    );
}

/// THE LOAD-BEARING TEST. Migrating is only worth anything if the result is a
/// tracker, so this runs the real CLI against it and drives a state change: the
/// item's file must MOVE, carrying its satellites (§5).
///
/// A migrator that wrote a perfect tree and left the binding naming the old layout
/// passes every other test in this file and fails this one at the first command.
#[test]
fn a_migrated_project_is_a_working_tracker() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, ITEMS);
    assert!(migrate(&proj).status.success());

    let out = run_in(&proj, &["status"]);
    assert!(out.status.success(), "status failed: {}", stderr(&out));
    assert!(stdout(&out).contains("2 work item(s)"), "{}", stdout(&out));

    let out = run_in(&proj, &["--agent", "claude", "claim", "WI-001"]);
    assert!(out.status.success(), "claim failed: {}", stderr(&out));

    assert!(
        !store_dir(&proj).join("open/WI-001.anthill").exists(),
        "the item left the directory its old status named"
    );
    let moved = read(&proj, "claimed/WI-001.anthill");
    assert!(moved.contains("Claimed"), "the status fact is rewritten:\n{moved}");
    assert!(moved.contains("a note"), "the feedback moved with it:\n{moved}");
    assert!(moved.contains(r#"name: "probe""#), "the tag moved with it:\n{moved}");

    // A write through the migrated store lands in the item's own file.
    let out = run_in(&proj, &["feedback", "WI-001", "after the move"]);
    assert!(out.status.success(), "feedback failed: {}", stderr(&out));
    assert!(read(&proj, "claimed/WI-001.anthill").contains("after the move"));
}

/// The binding is spliced over the fact's own span, not regenerated. `project.anthill`
/// is hand-written and its comments explain the binding they sit above.
///
/// CONTROL: rewriting the whole file passes the two `contains` assertions on the
/// binding and fails the one on the prose.
#[test]
fn the_binding_rewrite_keeps_the_prose_around_it() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, ITEMS);
    let config = store_dir(&proj).join("project.anthill");
    let original = fs::read_to_string(&config).expect("read config");
    fs::write(
        &config,
        format!(
            "{original}\n-- WHY THIS BINDING READS THE WAY IT DOES.\n{}\n",
            r#"fact anthill.persistence.ExtentBinding(
  store: anthill.persistence.filesystem.IndexedFileStore(
    root: ".",
    convention: anthill.persistence.filesystem.FileConvention.single_file(
      file: "workitems.anthill")),
  role: anthill.persistence.ExtentRole.mirror(),
  covers: [WorkItem, Feedback, Tag, StoreFormat])"#
        ),
    )
    .expect("write config");

    assert!(migrate(&proj).status.success());

    let after = fs::read_to_string(&config).expect("read config");
    assert!(after.contains("ItemPerFileStore("), "the binding names the new layout:\n{after}");
    assert!(!after.contains("IndexedFileStore("), "and not the old one:\n{after}");
    assert!(
        after.contains("-- WHY THIS BINDING READS THE WAY IT DOES."),
        "the comment above the binding survives:\n{after}"
    );
    assert!(
        after.contains(r#"name: "test-project""#),
        "and so does every other fact in the file:\n{after}"
    );
    // `covers` is carried across rather than re-derived — migration changes where
    // rows live, not which ones the store holds.
    assert!(after.contains("covers: [WorkItem, Feedback, Tag, StoreFormat]"), "{after}");
}

/// A project running on the DEFAULT binding has no text to splice, so one is
/// written. That shape is supported (a directory holding nothing but
/// `workitems.anthill`), so it gets a binding rather than a refusal.
#[test]
fn a_project_with_no_written_binding_gets_one() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_domainless_project(&tmp, ITEMS);

    let out = migrate(&proj);
    assert!(out.status.success(), "migrate failed: {}", stderr(&out));

    let config = read(&proj, "project.anthill");
    assert!(config.contains("ItemPerFileStore("), "a binding was written:\n{config}");

    // Driven, not merely written: the CLI reads it back on the next run.
    let out = run_in(&proj, &["status"]);
    assert!(out.status.success(), "status failed: {}", stderr(&out));
    assert!(stdout(&out).contains("2 work item(s)"), "{}", stdout(&out));
}

/// A satellite whose item has no row is CARRIED ACROSS, not refused and not
/// dropped. Found in the live tracker, and it is not a defect: `Feedback` is
/// `monotone` (proposal 053) so it cannot be retracted, which means `delete`
/// leaves an item's feedback behind BY DESIGN. Refusing to migrate over one would
/// lock out every tracker that has ever deleted an item that had feedback.
///
/// CONTROL, and it is the whole reason this is not left to the store: the store
/// REFUSES an orphan at `persist` (`a_satellite_naming_no_item_is_refused_at_flush`
/// pins that), because creating one is a bug. Backed out, migration dies mid-flush
/// naming one row. What this asserts is the other half of that line — inheriting
/// one is not a bug, and §10 already calls the result non-blocking.
#[test]
fn an_orphan_satellite_is_carried_across_and_reported() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let orphaned = format!(
        "{ITEMS}\nfact Feedback(workitem: \"WI-404\", author: \"user\", content: \"outlived it\", at: \"2026-01-01T00:00:00Z\")\n\
         fact Tag(workitem: \"WI-405\", name: \"also-orphaned\")\n"
    );
    let proj = setup_project(&tmp, &orphaned);

    let out = migrate(&proj);
    assert!(out.status.success(), "migration proceeds: {}", stderr(&out));
    let said = stdout(&out);
    assert!(said.contains("WI-404"), "both orphans are named, not just the first:\n{said}");
    assert!(said.contains("WI-405"), "both orphans are named, not just the first:\n{said}");

    // The rows themselves survive — this is real feedback about a real item.
    let kept = read(&proj, "orphaned.anthill");
    assert!(kept.contains("outlived it"), "the content is preserved:\n{kept}");
    assert!(kept.contains("also-orphaned"), "every orphan kind, not just feedback:\n{kept}");

    // And the items that DO exist migrated normally alongside them.
    assert!(read(&proj, "open/WI-001.anthill").contains("a note"));

    // §10: an orphan is reported and does NOT block. Both halves matter — a
    // migration that produced a blocking fault would leave the tracker unusable.
    let out = run_in(&proj, &["fsck"]);
    assert!(out.status.success(), "fsck does not block: {}", stderr(&out));
    assert!(stderr(&out).contains("WI-404"), "but it does report:\n{}", stderr(&out));
    let out = run_in(&proj, &["status"]);
    assert!(out.status.success(), "and the tracker runs: {}", stderr(&out));
}

/// Migration moves a whole file or none of it. Splitting one means rewriting a
/// hand-written file around the rows removed from it, and what should survive is
/// not something to guess at on a one-way rewrite.
#[test]
fn a_file_holding_both_covered_and_uncovered_rows_is_refused() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, ITEMS);
    // A work item in `project.anthill`, next to `Project` — which the binding does
    // not cover.
    let config = store_dir(&proj).join("project.anthill");
    let original = fs::read_to_string(&config).expect("read config");
    fs::write(
        &config,
        format!(
            "{original}\nfact WorkItem(\n  id: \"WI-003\",\n  description: \"misfiled\",\n  \
             acceptance: [ToolPasses(\"cargo-test\")],\n  depends_on: [],\n  status: Open)\n"
        ),
    )
    .expect("write config");

    let out = migrate(&proj);
    assert!(!out.status.success(), "a mixed file is refused");
    let err = stderr(&out);
    assert!(err.contains("project.anthill"), "the file is named:\n{err}");
    assert!(
        store_dir(&proj).join("workitems.anthill").exists(),
        "and nothing was written"
    );
}

/// THE ONE THAT DELETED DATA. Migration removes the files it consumes, so the
/// "whole file or none" question is whether the file holds anything ELSE — and the
/// first cut asked it of `fact_rule_ids`, which counts facts and nothing else. A
/// file whose rows were all covered but which also held a `rule` passed as a store
/// file, had its rows re-emitted, and was then deleted with the rule inside it.
///
/// CONTROL: count facts instead of items and this test fails while every other one
/// here still passes — none of the others puts a non-fact item in a covered file.
#[test]
fn a_file_holding_a_rule_beside_its_rows_is_refused() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, ITEMS);
    let extra = store_dir(&proj).join("extra.anthill");
    fs::write(
        &extra,
        "-- a rule this project wrote, in a file that also holds a row\n\
         rule my_urgent(?x)\n  \
           :- WorkItem(id: ?x, status: Open)\n\n\
         fact WorkItem(\n  id: \"WI-003\",\n  description: \"beside a rule\",\n  \
         acceptance: [ToolPasses(\"cargo-test\")],\n  depends_on: [],\n  status: Open)\n",
    )
    .expect("write extra");

    let out = migrate(&proj);
    assert!(!out.status.success(), "a file holding more than rows is refused");
    assert!(stderr(&out).contains("extra.anthill"), "{}", stderr(&out));

    // The whole point: the file — and the rule in it — is still there.
    let kept = fs::read_to_string(&extra).expect("the file survives");
    assert!(kept.contains("rule my_urgent"), "the rule was not deleted:\n{kept}");
    assert!(store_dir(&proj).join("workitems.anthill").exists());
}

/// `migrate --help` reaches the usage text for BOTH forms. It did not: the
/// dispatch keyed on `--to`, so the one command with options was the one whose
/// usage was unreachable (found in review).
#[test]
fn migrate_help_reaches_the_usage() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, ITEMS);

    let out = run_in(&proj, &["migrate", "--help"]);
    assert!(out.status.success(), "{}", stderr(&out));
    let said = stdout(&out);
    assert!(said.contains("--to item-per-file"), "the layout move:\n{said}");
    assert!(said.contains("pre-versioning"), "and the schema stamp:\n{said}");
    // It printed help and did nothing.
    assert!(store_dir(&proj).join("workitems.anthill").exists());
    assert!(!store_dir(&proj).join("open").exists());
}

/// Re-running a finished migration is not an error, and — the part that matters —
/// it does not TOUCH the tree.
///
/// Idempotence is answered from the STORE — a finished tree reports no `SharedFile`
/// fault, so there is nothing to split — and the run must then touch nothing at all.
/// This compares the whole tree byte for byte rather than spot-checking one file: a
/// spot check passes against a migrator that rewrote every file identically and
/// removed the ones it did not re-add.
#[test]
fn re_migrating_a_finished_tree_changes_nothing() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, ITEMS);
    assert!(migrate(&proj).status.success());

    let before = tree_snapshot(&store_dir(&proj));
    assert!(before.len() >= 4, "a migrated tree to compare against: {before:?}");

    let out = migrate(&proj);
    assert!(out.status.success(), "a second run succeeds: {}", stderr(&out));
    assert!(
        stdout(&out).contains("already one file per item"),
        "and says why it did nothing: {}",
        stdout(&out)
    );
    assert_eq!(before, tree_snapshot(&store_dir(&proj)), "the tree is untouched");
}

/// A project whose BINDING was switched to the new backend while its rows still sit
/// in one shared file is told what to do, rather than told "already migrated".
///
/// It USED to be answered from the binding — "this project already declares
/// ItemPerFileStore" — which was a dead end: every other command blocks on the
/// layout fault, `fsck` says splitting is `migrate`'s job, and `migrate` declined.
/// The answer now comes from the STORE, which reports `SharedFile` for exactly this.
///
/// AND IT REFUSES RATHER THAN MIGRATING FROM HERE, deliberately. Doing the move in
/// this state means deciding per file which are already the target shape — the
/// store's routing rule, re-derived outside it — and a first cut that did so was
/// wrong four ways (a satellite-only file silently dropped, satellites of skipped
/// files misfiled as orphans, the orphan file truncated over saved rows, and a
/// flush-failure note advising deletion of the only copy of the data). One loud
/// sentence naming the remedy beats four silent ways to lose rows.
///
/// CONTROL: answer from the binding instead and the assertion on the remedy fails —
/// the ordinary path never reaches this state, because it writes the binding itself
/// and does so last.
#[test]
fn a_project_declaring_the_backend_before_migrating_is_told_what_to_do() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, ITEMS);
    fs::write(
        store_dir(&proj).join("project.anthill"),
        "fact Project(name: \"switched-early\", language: \"rust\", build: \"cargo\", \
         tools: [\"cargo-test\"])\n\n\
         fact anthill.persistence.ExtentBinding(\n  \
           store: anthill.persistence.filesystem.ItemPerFileStore(\n    \
             root: \".\",\n    status_field: \"status\",\n    id_field: \"id\",\n    \
             ref_field: \"workitem\"),\n  \
           role: anthill.persistence.ExtentRole.mirror(),\n  \
           covers: [WorkItem, Feedback, Tag, StoreFormat])\n",
    )
    .expect("write config");

    let out = migrate(&proj);
    assert!(!out.status.success(), "refused, not silently declined");
    let err = stderr(&out);
    assert!(err.contains("workitems.anthill"), "it names the file:\n{err}");
    assert!(err.contains("IndexedFileStore"), "and the remedy:\n{err}");
    // Nothing was written on the way to that refusal.
    assert!(!store_dir(&proj).join("open").exists());
    assert!(store_dir(&proj).join("workitems.anthill").exists());
}

/// Every `.anthill` file under `root`, as (relative path, contents).
fn tree_snapshot(root: &Path) -> Vec<(String, String)> {
    fn walk(dir: &Path, root: &Path, out: &mut Vec<(String, String)>) {
        for entry in fs::read_dir(dir).expect("read_dir").flatten() {
            let path = entry.path();
            if path.is_dir() {
                walk(&path, root, out);
            } else if path.extension().is_some_and(|e| e == "anthill") {
                out.push((
                    path.strip_prefix(root).expect("under root").display().to_string(),
                    fs::read_to_string(&path).expect("read"),
                ));
            }
        }
    }
    let mut out = Vec::new();
    walk(root, root, &mut out);
    out.sort();
    out
}

/// §11's step 4 as drafted said to stamp `StoreFormat(version: 2)`. It is not done,
/// and this is the control that says so rather than leaving it to be re-derived.
///
/// `StoreFormat` versions the SCHEMA a row is written in; this changes no schema —
/// the same entities with the same fields, redistributed across files. Bumping the
/// binary's current version would make every project on the single-file layout —
/// supported, not deprecated — warn that it is out of date and point at a command
/// that would refuse the bump.
#[test]
fn the_data_format_stamp_is_not_bumped() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, ITEMS);
    assert!(migrate(&proj).status.success());

    assert!(
        read(&proj, "store_format.anthill").contains("version: 1"),
        "the stamp moved, unchanged"
    );
    // The bundle's own `migrate` — the WI-434 schema stamp — still agrees with it,
    // which is the observable that a bump would break.
    let out = run_in(&proj, &["migrate"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(stdout(&out).contains("already up to date"), "{}", stdout(&out));
    // And no command emits a stale-format warning.
    let out = run_in(&proj, &["status"]);
    assert!(!stderr(&out).contains("store format"), "{}", stderr(&out));
}

/// The ticket and §11 were drafted when this move also created ~1110 GitHub issues.
/// It no longer touches a forge, so the old spelling is refused with the reason —
/// accepting it as an alias would answer a different question than the one asked.
#[test]
fn the_forge_spelling_is_refused_with_its_reason() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, ITEMS);

    let out = run_in(&proj, &["migrate", "--to", "github-coordinated"]);
    assert!(!out.status.success(), "refused");
    let err = stderr(&out);
    assert!(err.contains("item-per-file"), "it names what to run instead:\n{err}");
    assert!(err.contains("export"), "and where the mirror went:\n{err}");
    assert!(
        store_dir(&proj).join("workitems.anthill").exists(),
        "nothing happened"
    );
}

/// A bare `migrate` is still the bundle's schema stamp (WI-434). The two commands
/// share a name and do not overlap: that one versions the schema a row is written
/// in, this one moves which file it lives in.
#[test]
fn a_bare_migrate_is_still_the_schema_stamp() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "fact WorkItem(\n  id: \"WI-001\",\n  description: \"unstamped\",\n  acceptance: [ToolPasses(\"cargo-test\")],\n  depends_on: [],\n  status: Open)\n");

    let out = run_in(&proj, &["migrate"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(stdout(&out).contains("store format version"), "{}", stdout(&out));
    // It stamped, and did NOT move anything.
    assert!(store_dir(&proj).join("workitems.anthill").exists());
    assert!(!store_dir(&proj).join("open").exists());
}
