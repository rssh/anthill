//! WI-1114 — the tracker runs on `ItemPerFileStore`, declared and not compiled in.
//!
//! Design: `rustland/anthill-todo/docs/design/backend-github-coordination.md` §4, §5,
//! §5.1, §8.3, §10. `anthill-core`'s own `wi1114_item_per_file_store_test` drives the
//! store directly; THIS one drives the CLI, and so measures the parts that live only
//! here — the per-backend host arm, the field names arriving from the project's own
//! binding, `fsck`, and the fact that a swap of the store TERM is the entire change a
//! project makes.
//!
//! WHAT FAILS WITHOUT THE CHANGE: every test here. Before it, `ItemPerFileStore` is a
//! name no build provides, so `resolve_backend` refuses the binding and each of these
//! dies at startup.
//!
//! WHAT PASSES EITHER WAY BY DESIGN: `the_single_file_backend_is_untouched` — the
//! existing layout must behave exactly as before, which is what lets this repo's own
//! tracker stay on it while this is built (§14.1).

use std::fs;
use std::path::Path;
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

/// The ONE thing a project changes to move layouts: the store term inside its
/// `ExtentBinding`. Everything else — role, coverage, the rest of the CLI — is
/// untouched, which is what "the binding names a backend to build" buys.
const ITEM_PER_FILE_BINDING: &str = r#"fact Project(
  name: "per-file",
  language: "rust",
  build: "cargo",
  tools: ["cargo-test"])

fact anthill.persistence.ExtentBinding(
  store: anthill.persistence.filesystem.ItemPerFileStore(
    root: ".",
    status_field: "status",
    id_field: "id",
    ref_field: "workitem"),
  role: anthill.persistence.ExtentRole.mirror(),
  covers: [WorkItem, Feedback, Tag, StoreFormat])
"#;

/// A project on the new layout, with no `workitems.anthill` at all — the rows live in
/// the per-state directories, and there is nothing else for them to live in.
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

/// `add` files a new item under the directory its status names, in a file of its own.
/// Two adds are two files, which is the whole conflict story (§9).
#[test]
fn add_files_each_item_in_its_own_file_under_its_status() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);

    ok(&proj, &["add", "the first one"]);
    ok(&proj, &["add", "the second one"]);

    let first = proj.join("anthill-todo/open/WI-001.anthill");
    let second = proj.join("anthill-todo/open/WI-002.anthill");
    assert!(first.exists(), "WI-001 got its own file");
    assert!(second.exists(), "WI-002 got its own — a different file");
    assert!(
        fs::read_to_string(&first).unwrap().contains("the first one"),
        "and its own row is in it"
    );
    assert!(
        !proj.join("anthill-todo/workitems.anthill").exists(),
        "nothing fell back to the shared file"
    );
}

/// THE INCREMENT'S REASON TO EXIST, end to end: a state change is a file move, and the
/// item's feedback and tags travel with it.
///
/// THE CONTROL IS THE FEEDBACK AND THE TAG. "The item moved" would pass for a store
/// that wrote the new row and deleted the old file; those two rows are named by nothing
/// in `claim`, and must arrive at the destination anyway.
#[test]
fn a_claim_moves_the_file_and_carries_feedback_and_tags() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);

    ok(&proj, &["add", "movable"]);
    ok(&proj, &["feedback", "WI-001", "a note that must travel"]);
    ok(&proj, &["tag", "WI-001", "wi1114"]);
    assert!(proj.join("anthill-todo/open/WI-001.anthill").exists());

    ok(&proj, &["claim", "WI-001", "--agent", "claude"]);

    assert!(
        !proj.join("anthill-todo/open/WI-001.anthill").exists(),
        "the source file is gone"
    );
    let moved = fs::read_to_string(proj.join("anthill-todo/claimed/WI-001.anthill"))
        .expect("the item moved to claimed/");
    assert!(moved.contains("Claimed(agent: \"claude\""), "{moved}");
    assert!(
        moved.contains("a note that must travel"),
        "the feedback rode along: {moved}"
    );
    assert!(
        moved.contains("Tag(workitem: \"WI-001\", name: \"wi1114\")"),
        "the tag rode along: {moved}"
    );
}

/// The rows the move wrote are read back by the NEXT process. Without this the layout
/// is write-only — every assertion above is about bytes nobody has parsed.
#[test]
fn the_moved_rows_are_read_back_by_the_next_invocation() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);

    ok(&proj, &["add", "round trip"]);
    ok(&proj, &["feedback", "WI-001", "survives a reload"]);
    ok(&proj, &["claim", "WI-001", "--agent", "claude"]);

    let shown = ok(&proj, &["show", "WI-001"]);
    assert!(shown.contains("round trip"), "{shown}");
    assert!(shown.contains("survives a reload"), "{shown}");
    assert!(shown.contains("Claimed"), "{shown}");

    let listed = ok(&proj, &["list"]);
    assert!(listed.contains("WI-001"), "{listed}");
}

/// A second state change moves the file again, from wherever it currently is — the
/// destination is computed from the fact, not from a remembered origin.
#[test]
fn a_second_state_change_moves_it_again() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);

    ok(&proj, &["add", "two hops"]);
    ok(&proj, &["claim", "WI-001", "--agent", "claude"]);
    ok(&proj, &["deliver", "WI-001", "--agent", "claude"]);

    assert!(!proj.join("anthill-todo/claimed/WI-001.anthill").exists());
    assert!(proj.join("anthill-todo/delivered/WI-001.anthill").exists());
}

/// `feedback` on an item that has already moved lands in the file the item is in NOW.
/// A satellite routed when its persist was buffered — or against a stale index — would
/// write it under the item's old status.
#[test]
fn feedback_after_a_move_lands_in_the_current_file() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);

    ok(&proj, &["add", "moved first"]);
    ok(&proj, &["claim", "WI-001", "--agent", "claude"]);
    ok(&proj, &["feedback", "WI-001", "written after the move"]);

    let claimed = fs::read_to_string(proj.join("anthill-todo/claimed/WI-001.anthill")).unwrap();
    assert!(claimed.contains("written after the move"), "{claimed}");
    assert!(
        !proj.join("anthill-todo/open/WI-001.anthill").exists(),
        "nothing re-created the old file"
    );
}

/// A row carrying neither an id nor an item reference — the format stamp `migrate`
/// writes (§11 step 4) — gets a store-level home at the root, and the next load
/// reads it back. Without a home it would be unroutable, and `migrate` is not
/// optional: every project is asked to run it.
#[test]
fn migrate_stamps_the_format_at_the_root_and_it_is_read_back() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    ok(&proj, &["add", "needs a stamp"]);

    let before = run_in(&proj, &["list"]);
    assert!(
        String::from_utf8_lossy(&before.stderr).contains("pre-versioning"),
        "the un-stamped project warns"
    );

    ok(&proj, &["migrate"]);
    let stamp = fs::read_to_string(proj.join("anthill-todo/store_format.anthill"))
        .expect("the keyless row got a store-level home");
    assert!(stamp.contains("StoreFormat(version:"), "{stamp}");

    let after = run_in(&proj, &["list"]);
    assert!(
        !String::from_utf8_lossy(&after.stderr).contains("pre-versioning"),
        "and the next load reads the stamp back: {}",
        String::from_utf8_lossy(&after.stderr)
    );
}

// ── fsck (§10) ─────────────────────────────────────────────────

/// The state a crash between the move's two filesystem steps leaves: a file whose
/// directory denies its own fact. It BLOCKS every command — the store's routing would
/// otherwise have to guess — and `fsck --fix` repairs it in the one direction §4
/// settles: the fact wins.
#[test]
fn a_misplaced_file_blocks_and_fsck_fix_repairs_it() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    ok(&proj, &["add", "displaced"]);

    // Move the file by hand, the way an interrupted `claim` or a careless `git mv`
    // would: the bytes say `Open`, the directory says `claimed`.
    let inner = proj.join("anthill-todo");
    fs::create_dir_all(inner.join("claimed")).unwrap();
    fs::rename(
        inner.join("open/WI-001.anthill"),
        inner.join("claimed/WI-001.anthill"),
    )
    .unwrap();

    let blocked = run_in(&proj, &["list"]);
    assert!(
        !blocked.status.success(),
        "a disagreeing layout is not quietly worked around"
    );
    let err = String::from_utf8_lossy(&blocked.stderr);
    assert!(err.contains("WI-001"), "the fault names the item: {err}");
    assert!(err.contains("fsck --fix"), "and the remedy: {err}");

    let out = run_in(&proj, &["fsck", "--fix"]);
    assert!(out.status.success(), "fsck --fix: {out:?}");
    assert!(inner.join("open/WI-001.anthill").exists(), "the fact won");
    assert!(!inner.join("claimed/WI-001.anthill").exists());

    // And the tracker is usable again.
    assert!(ok(&proj, &["list"]).contains("WI-001"));
}

/// A clean tree passes `fsck` with nothing to say, and says so — a checker that prints
/// nothing is indistinguishable from a checker that did not run.
#[test]
fn fsck_reports_a_clean_layout() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    ok(&proj, &["add", "tidy"]);
    assert!(ok(&proj, &["fsck"]).contains("layout ok"));
}

/// `fsck` under the shared-file backend refuses rather than reporting a clean bill of
/// health it did not check. There is no directory-per-state layout there to check.
///
/// BOTH FORMS REFUSE, and that pair is the assertion. Bare `fsck` used to print
/// `layout ok` while `--fix` on the same project refused — the two arms disagreeing
/// about whether the question was even answerable, with the read-only one giving the
/// silent-skip answer the repo's principles forbid (found in review).
#[test]
fn fsck_under_the_shared_file_backend_refuses() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    for form in [vec!["fsck"], vec!["fsck", "--fix"]] {
        let out = run_in(&proj, &form);
        assert!(!out.status.success(), "{form:?} must refuse");
        let err = String::from_utf8_lossy(&out.stderr);
        assert!(err.contains("IndexedFileStore"), "{form:?}: {err}");
    }
}

/// `fsck --help` prints its usage. It is in the bundle's registry precisely so
/// `--help` finds it, so asking it for its own help is a likely first move — and it
/// used to exit non-zero with "unknown fsck option `--help`" (found in review).
#[test]
fn fsck_help_prints_usage() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let out = run_in(&proj, &["fsck", "--help"]);
    assert!(out.status.success(), "{out:?}");
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(text.contains("--fix"), "{text}");
}

/// A project that declares this backend before migrating into it still has one
/// shared `workitems.anthill`. Every command blocks — correctly — and the remedy it
/// is told to run must not make things worse: `fsck --fix` names the shape and
/// refuses, pointing at `migrate`. It used to rename the whole shared file to the
/// first item's path (found in review).
#[test]
fn a_project_declaring_the_backend_before_migrating_is_told_to_migrate() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(
        &tmp,
        "fact WorkItem(id: \"WI-001\", acceptance: [], status: Open)\n\
         fact WorkItem(id: \"WI-002\", acceptance: [], status: Open)\n",
    );
    fs::write(
        proj.join("anthill-todo/project.anthill"),
        ITEM_PER_FILE_BINDING,
    )
    .unwrap();

    let blocked = run_in(&proj, &["list"]);
    assert!(!blocked.status.success(), "the un-migrated layout blocks");

    let out = run_in(&proj, &["fsck", "--fix"]);
    assert!(!out.status.success(), "and the repair refuses: {out:?}");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("migrate"), "naming what would help: {err}");

    let items = fs::read_to_string(proj.join("anthill-todo/workitems.anthill")).unwrap();
    assert!(
        items.contains("WI-001") && items.contains("WI-002"),
        "and every row is still where it was: {items}"
    );
    assert!(
        !proj.join("anthill-todo/open/WI-001.anthill").exists(),
        "nothing was renamed to one item's path"
    );
}

// ── The other backend, unchanged (§14.1) ───────────────────────

/// PASSES EITHER WAY BY DESIGN, and that is the assertion: this repo's own tracker
/// stays on the shared-file store while the new one is built, so the default binding
/// and the default layout must be exactly what they were.
#[test]
fn the_single_file_backend_is_untouched() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    ok(&proj, &["add", "still shared"]);
    let items = fs::read_to_string(proj.join("anthill-todo/workitems.anthill")).unwrap();
    assert!(items.contains("still shared"), "{items}");
    assert!(
        !proj.join("anthill-todo/open").exists(),
        "no per-state directories appeared"
    );
}

/// A store this build does not provide is a hard refusal naming both backends it does —
/// never a fall back to a local file store, which would write a project's rows somewhere
/// it did not ask for.
#[test]
fn an_unprovided_backend_is_refused_and_the_message_lists_both() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    fs::write(
        proj.join("anthill-todo/project.anthill"),
        ITEM_PER_FILE_BINDING.replace("ItemPerFileStore", "GitHubBackedStore"),
    )
    .unwrap();
    let out = run_in(&proj, &["list"]);
    assert!(!out.status.success());
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        err.contains("IndexedFileStore") && err.contains("ItemPerFileStore"),
        "the refusal names what this build DOES provide: {err}"
    );
}
