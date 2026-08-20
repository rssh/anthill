//! WI-1120 — a work item is a DOCUMENT: structured fields, then markdown prose.
//!
//! WI-K63ZV replaced the ENCODING these tests were written against — the fields
//! moved from a fenced `anthill` head into an `## Attributes` chapter — but not
//! the invariants, which are WI-1120's contribution and still hold: prose leaves
//! the structured region and comes back, a hand-added sub-section survives a
//! rewrite, and a heading the mapping does not name is a LOAD ERROR rather than
//! a note. Specification: `docs/design/document-mapping.md`.
//!
//! `anthill-core`'s `persistence::document` unit tests drive the reader and the
//! writer; THIS one drives the CLI, so it measures what only exists end to end —
//! the declared mapping reaching the store, and the opacity invariant.
//!
//! WHAT FAILS WITHOUT THE CHANGE: every test here. Before it an item is a block
//! of `fact` declarations in `WI-NNN.anthill`, so the file these look for does
//! not exist.
//!
//! WHAT PASSES EITHER WAY BY DESIGN: none of them. The nearest candidate is
//! `a_state_change_leaves_the_chapters_byte_identical`, which reads like a
//! restatement of WI-1114's "a claim moves the file" — but its assertion is on
//! the BYTES of prose the attributes do not mention, and it fails the day the
//! store starts re-serialising a whole file from facts, which is the one failure
//! mode that would quietly eat a user's notes.

use std::fs;
use std::path::{Path, PathBuf};
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

const ITEM_PER_FILE_BINDING: &str = r#"fact Project(
  name: "documents",
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

fn per_file_project(tmp: &tempfile::TempDir) -> PathBuf {
    let proj = setup_project(tmp, "");
    fs::write(proj.join("anthill-todo/project.anthill"), ITEM_PER_FILE_BINDING)
        .expect("write project config");
    fs::remove_file(proj.join("anthill-todo/workitems.anthill")).expect("no shared file");
    proj
}

fn added_id(stdout: &str) -> String {
    stdout.split_whitespace().nth(1).expect("`added: <id> — …`").to_string()
}

/// The single item document under `<state>/`.
fn the_document(proj: &Path, state: &str) -> PathBuf {
    let dir = proj.join("anthill-todo").join(state);
    let mut found: Vec<PathBuf> = fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .map(|e| e.expect("entry").path())
        .filter(|p| p.to_string_lossy().ends_with(".anthill.md"))
        .collect();
    assert_eq!(found.len(), 1, "one document under {state}/: {found:?}");
    found.pop().expect("checked")
}

/// THE SHAPE (§2): one item file is an `## Attributes` chapter of data followed
/// by prose chapters, and the prose is NOT among the attributes.
#[test]
fn an_added_item_is_an_attributes_chapter_plus_a_description() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);

    let id = added_id(&ok(&proj, &["add", "prose that leaves the head", "--created", "2026-08-17T10:22:03Z"]));

    let path = the_document(&proj, "open");
    assert!(
        path.to_string_lossy().ends_with(&format!("{id}.anthill.md")),
        "the file is named for its id, with the document suffix: {}",
        path.display()
    );
    let text = fs::read_to_string(&path).expect("read");
    assert!(text.starts_with("## Attributes\n\n"), "{text}");
    let (attributes, body) = text.split_once("\n## Description\n").expect("a description");
    assert!(attributes.contains(&format!("- id: {id}\n")), "{attributes}");
    assert!(
        !attributes.contains("prose that leaves the head"),
        "the description is NOT an attribute: {attributes}"
    );
    assert!(body.starts_with("\nprose that leaves the head"), "{body}");
    // …and it comes back as the description it was.
    assert!(ok(&proj, &["show", &id]).contains("prose that leaves the head"));
}

/// FEEDBACK IS A CONTAINER PLUS ENTRIES (§5.3), not a run of top-level chapters
/// named by timestamps: a repeated fact is not a field of the item.
#[test]
fn feedback_becomes_entries_under_one_container() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let id = added_id(&ok(&proj, &["add", "with notes", "--created", "2026-08-17T10:22:03Z"]));

    ok(&proj, &["feedback", &id, "the first note", "--agent", "user"]);
    ok(&proj, &["feedback", &id, "the second note", "--agent", "claude"]);

    let text = fs::read_to_string(the_document(&proj, "open")).expect("read");
    assert_eq!(text.matches("\n## Changes\n").count(), 1, "one container: {text}");
    assert_eq!(text.matches("\n### ").count(), 2, "two entries: {text}");
    // The heading IS the fact's structured half — `at`, the KIND, then the
    // author — so there is no second copy of it anywhere to disagree with.
    assert!(text.contains(" — feedback — user\n"), "{text}");
    assert!(text.contains(" — feedback — claude\n"), "{text}");
    assert!(text.contains("the first note"), "{text}");
    let attributes = text.split("\n## ").next().expect("attributes");
    assert!(!attributes.contains("the first note"), "{attributes}");
    assert!(!attributes.contains("workitem"), "a satellite's key is not written: {attributes}");
    // And both come back.
    let shown = ok(&proj, &["show", &id]);
    assert!(shown.contains("the first note") && shown.contains("the second note"), "{shown}");
}

/// THE OPACITY INVARIANT (§5.3, row four), and it holds only as a TESTED one:
/// hand-add a sub-section inside a description, run a command that rewrites the
/// head AND renames the file, and assert the sub-section survives byte-identical.
///
/// This is the test that fails the day the store starts re-serialising a whole
/// file from facts — the one failure mode that would quietly eat a user's notes.
#[test]
fn a_state_change_leaves_the_chapters_byte_identical() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let id = added_id(&ok(&proj, &["add", "carries notes", "--created", "2026-08-17T10:22:03Z"]));
    ok(&proj, &["feedback", &id, "a note", "--agent", "user"]);

    let path = the_document(&proj, "open");
    let text = fs::read_to_string(&path).expect("read");
    let hand_added = "\n#### a hand-added sub-section\n\nkeep me exactly as I am.\n";
    let edited = text.replace("carries notes\n", &format!("carries notes\n{hand_added}"));
    assert_ne!(edited, text, "the edit landed");
    fs::write(&path, &edited).expect("write");
    let chapters_before = edited.split_once("\n## Description\n").expect("a description").1.to_string();

    ok(&proj, &["claim", &id, "--agent", "claude"]);

    let moved = fs::read_to_string(the_document(&proj, "claimed")).expect("the item moved");
    assert!(
        moved.contains("- status: Claimed\n- status_agent: claude\n"),
        "the attributes WERE rewritten: {moved}"
    );
    let chapters_after = moved.split_once("\n## Description\n").expect("a description").1;
    assert_eq!(
        chapters_after, chapters_before,
        "every chapter came through the move unchanged, sub-section included"
    );
}

/// THE PRECISE CLAIM of §5.3: the only prose the store ever rewrites is one
/// `description` chapter, via `update`. The feedback entries beside it are not
/// touched — which is a correctness property, not a volume one.
#[test]
fn an_update_rewrites_the_description_chapter_and_no_other() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let id = added_id(&ok(&proj, &["add", "the first wording", "--created", "2026-08-17T10:22:03Z"]));
    ok(&proj, &["feedback", &id, "a note that must not move", "--agent", "user"]);

    ok(&proj, &["update", &id, "--description", "a second wording"]);

    let text = fs::read_to_string(the_document(&proj, "open")).expect("read");
    assert!(text.contains("## Description\n\na second wording"), "{text}");
    assert!(!text.contains("the first wording"), "{text}");
    assert!(text.contains("a note that must not move"), "{text}");
}

/// PROSE WITH ITS OWN HEADINGS IS DEMOTED, NOT REFUSED (§4.1) — WI-K63ZV\'s
/// change, and the reason is that text written somewhere else arrives with a
/// hierarchy starting at `#` or `##`, which collides with the levels this format
/// reserves. The whole hierarchy shifts down by the MINIMUM that clears them, so
/// the relative structure is preserved exactly.
///
/// IT IS IDEMPOTENT, which is what makes it safe on every write: stored prose has
/// no collision left, so writing it back shifts nothing.
#[test]
fn prose_carrying_a_reserved_heading_is_demoted_rather_than_refused() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let id = added_id(&ok(&proj, &["add", "intact", "--created", "2026-08-17T10:22:03Z"]));

    ok(&proj, &["update", &id, "--description", "intro\n\n## a section\n\n### under it\n\ntail"]);

    let text = fs::read_to_string(the_document(&proj, "open")).expect("read");
    assert!(text.contains("\n### a section\n"), "shifted below the reserved level: {text}");
    assert!(text.contains("\n#### under it\n"), "and its child kept its place under it: {text}");
    // `## Attributes` opens the file, so it has no newline before it — count the
    // chapter headings at line starts rather than by a leading newline.
    assert_eq!(
        text.lines().filter(|l| l.starts_with("## ")).count(),
        2,
        "still two chapters: {text}"
    );
    // The whole description comes back, sub-sections included.
    let shown = ok(&proj, &["show", &id]);
    assert!(shown.contains("### a section") && shown.contains("tail"), "{shown}");

    // …and writing the SAME text back shifts nothing. That is what makes the
    // demotion safe to apply on every write: stored prose has no collision left,
    // so a round trip is identity from the second write onward. Driven by
    // rewriting the description rather than by some other command, because it is
    // the description's own path through demote-and-render that must be idempotent.
    let again = fs::read_to_string(the_document(&proj, "open")).expect("read");
    ok(
        &proj,
        &["update", &id, "--description", "intro\n\n### a section\n\n#### under it\n\ntail"],
    );
    assert_eq!(
        fs::read_to_string(the_document(&proj, "open")).expect("read"),
        again,
        "a second write shifted the prose again"
    );
}

/// THE TRUNCATION CASE (§5.3's third row), and it must not look like a note: a
/// heading at the reserved level that the mapping does not name is a LOAD ERROR.
#[test]
fn a_heading_the_mapping_does_not_name_is_a_load_error() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    ok(&proj, &["add", "about to be edited", "--created", "2026-08-17T10:22:03Z"]);

    let path = the_document(&proj, "open");
    let text = fs::read_to_string(&path).expect("read");
    fs::write(&path, format!("{text}\n## Notes\n\nhand-added at the wrong level\n")).expect("write");

    let err = fails(&proj, &["list"]);
    assert!(err.contains("Notes"), "the heading is named: {err}");
    assert!(err.contains("reserved"), "{err}");
}

/// AN ENTRY HEADING IS THE DATA, NOT A PROJECTION OF IT (WI-K63ZV, §4.3), and
/// that is a whole fault class gone rather than a check dropped.
///
/// Under the previous encoding the heading was REGENERATED from a field of the
/// head, so the two could disagree: a hand-edited heading was a diagnostic, and
/// a REORDERED container was a blocking fault whose repair had to move prose
/// rather than relabel it, because entries bound to facts by POSITION. Now `at`
/// and `author` are read out of the heading itself. There is nothing left for it
/// to disagree with, and order is not data.
///
/// SO THIS TEST IS THE OPPOSITE OF THE ONE IT REPLACES: a reordered container is
/// neither an error nor a diagnostic, and each note is still attached to the
/// author it was written by.
#[test]
fn a_reordered_container_is_neither_an_error_nor_a_diagnostic() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let id = added_id(&ok(&proj, &["add", "two notes", "--created", "2026-08-17T10:22:03Z"]));
    ok(&proj, &["feedback", &id, "the first note", "--agent", "user"]);
    ok(&proj, &["feedback", &id, "the second note", "--agent", "claude"]);

    // Swap the two entries, the way a union merge or a hand-edit would.
    let path = the_document(&proj, "open");
    let text = fs::read_to_string(&path).expect("read");
    let (head, body) = text.split_once("## Changes\n").expect("a container");
    let entries: Vec<&str> = body.split("### ").filter(|e| !e.trim().is_empty()).collect();
    assert_eq!(entries.len(), 2, "two entries: {body}");
    fs::write(&path, format!("{head}## Changes\n### {}### {}", entries[1], entries[0]))
        .expect("write");

    // Nothing to report: the same entries in any order denote the same facts.
    assert!(ok(&proj, &["fsck"]).contains("layout ok"));

    // And each note is still its own author's — which is the property the old
    // positional binding needed a blocking fault to protect.
    let shown = ok(&proj, &["show", &id]);
    let user_at = shown.find("user").expect("the user entry");
    let first = shown.find("the first note").expect("the first note");
    let claude_at = shown.find("claude").expect("the claude entry");
    let second = shown.find("the second note").expect("the second note");
    assert!(user_at < first && claude_at < second, "notes kept their authors: {shown}");
}

/// FILENAME-VS-ID, the check this increment's acceptance surface asks for. It is
/// WI-1114's whole-PATH comparison doing its job — the suffix is now part of the
/// path it compares, so a file whose name denies its id is the same fault it
/// always was, and `--fix` moves it.
#[test]
fn a_filename_that_denies_its_id_blocks_and_fsck_fix_repairs_it() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let id = added_id(&ok(&proj, &["add", "renamed by hand", "--created", "2026-08-17T10:22:03Z"]));

    let path = the_document(&proj, "open");
    let wrong = path.with_file_name("WI-not-this-id.anthill.md");
    fs::rename(&path, &wrong).expect("rename");

    let err = fails(&proj, &["list"]);
    assert!(err.contains("WI-not-this-id"), "{err}");
    assert!(err.contains(&id), "the fact's own path is named: {err}");

    ok(&proj, &["fsck", "--fix"]);
    assert!(!wrong.exists(), "the misnamed file is gone");
    assert!(ok(&proj, &["show", &id]).contains("renamed by hand"));
}

/// THE SECOND FULL-TREE PASS (§11): a tracker already exploded into plain
/// `WI-NNN.anthill` files is converted in place, and `created` is back-dated
/// from a table rather than stamped with the migration date — which would put
/// every legacy item in ONE day partition.
#[test]
fn migrate_to_document_converts_a_plain_tree_and_backdates_created() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let dir = proj.join("anthill-todo/open");
    fs::create_dir_all(&dir).expect("mkdir");
    fs::write(
        dir.join("WI-042.anthill"),
        "fact WorkItem(id: \"WI-042\", description: \"a legacy item\", \
         acceptance: [], last_status_change: StatusChange(status: Open()))\n\n\
         fact Feedback(workitem: \"WI-042\", author: \"user\", content: \"a legacy note\", \
         at: \"2026-04-04T04:04:04Z\")\n",
    )
    .expect("write");
    let table = tmp.path().join("created.tsv");
    fs::write(&table, "WI-042\t2026-04-04T04:04:04Z\n").expect("write table");

    let out = ok(
        &proj,
        &["migrate", "--to", "document", "--created-from", table.to_str().unwrap()],
    );
    assert!(out.contains("1 file(s)"), "{out}");
    assert!(out.contains("back-dated `created` on 1 item(s)"), "{out}");

    assert!(!dir.join("WI-042.anthill").exists(), "the plain file is gone");
    let text = fs::read_to_string(dir.join("WI-042.anthill.md")).expect("the document");
    assert!(text.contains("- created: 2026-04-04T04:04:04Z\n"), "{text}");
    assert!(text.contains("## Description\n\na legacy item"), "{text}");
    assert!(text.contains("a legacy note"), "{text}");
    // The rows are the rows they were — a reformat, not a data change.
    let shown = ok(&proj, &["show", "WI-042"]);
    assert!(shown.contains("a legacy item") && shown.contains("a legacy note"), "{shown}");
}

/// THE CONVERSION BRINGS THE BINDING WITH IT, and without this the migration
/// succeeds and leaves a tracker nothing can read.
///
/// The store routes a row by the `status_field` its `ExtentBinding` names.
/// WI-K63ZV moved stage0's status inside `last_status_change`, so a binding left
/// naming `"status"` points at a field the converted rows do not have, and every
/// later command fails with "carries `id` … but no `status` field" — on data
/// that converted perfectly. The conversion does not notice, because it builds
/// its own target store from this CLI's constants rather than from the
/// declaration.
///
/// MEASURED THE WAY A USER MEETS IT: convert a project whose binding is
/// untouched, then run an ordinary command. The `status` assertion is the one
/// that fails when the rewrite is backed out.
#[test]
fn converting_a_tree_repoints_its_binding_at_the_moved_status_field() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let config = proj.join("anthill-todo/project.anthill");
    // The binding as a project written before the flattening carries it.
    let before = fs::read_to_string(&config).expect("read");
    fs::write(
        &config,
        before.replace(
            "status_field: \"last_status_change.status\"",
            "status_field: \"status\"",
        ),
    )
    .expect("write");

    let open = proj.join("anthill-todo/open");
    fs::create_dir_all(&open).expect("mkdir");
    fs::write(
        open.join("WI-910.anthill.md"),
        "```anthill\nfact WorkItem(id: \"WI-910\", created: \"2026-01-01T00:00:00Z\", \
         acceptance: [], status: Open)\n```\n\n## description\n\nbinding probe\n",
    )
    .expect("write");

    let out = ok(&proj, &["migrate", "--to", "document"]);
    assert!(out.contains("updated the store binding"), "it says so: {out}");
    assert!(
        fs::read_to_string(&config)
            .expect("read")
            .contains("status_field: \"last_status_change.status\""),
        "the binding names the field the status actually lives in"
    );

    // …and the tracker WORKS afterwards, which is the property that matters.
    assert!(ok(&proj, &["status"]).contains("1 work item"));
    assert!(ok(&proj, &["show", "WI-910"]).contains("binding probe"));
}

/// A CONVERTED ITEM WHOSE DIRECTORY DENIED ITS STATUS MUST NOT END UP IN TWO
/// FILES, and this is the one case where "a legacy document is rewritten at its
/// own path" is false.
///
/// The directory IS the status, so a source tree that already disagreed —
/// a `Claimed` item sitting under `open/`, which `fsck` reports as a
/// `PathDisagreement` — converts to a DIFFERENT path. Removing only the plain
/// sources left the legacy file behind, and the item then existed twice: a
/// `DuplicateId`, which BLOCKS every later command, produced by the very
/// command that was supposed to fix the tree.
///
/// THE CONTROL is every other conversion test here, where source and
/// destination agree and there is correctly nothing to remove — so this cannot
/// be satisfied by deleting the source unconditionally either.
#[test]
fn converting_a_misfiled_legacy_document_leaves_exactly_one_file() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let open = proj.join("anthill-todo/open");
    fs::create_dir_all(&open).expect("mkdir");
    // Claimed, but filed under `open/`.
    fs::write(
        open.join("WI-905.anthill.md"),
        "```anthill\nfact WorkItem(id: \"WI-905\", created: \"2026-01-01T00:00:00Z\", \
         acceptance: [], status: Claimed(agent: \"alice\", since: \"2026-02-02T00:00:00Z\"))\n\
         ```\n\n## description\n\nmisfiled and legacy\n",
    )
    .expect("write");

    ok(&proj, &["migrate", "--to", "document"]);

    assert!(!open.join("WI-905.anthill.md").exists(), "the source was removed");
    let moved = proj.join("anthill-todo/claimed/WI-905.anthill.md");
    assert!(moved.exists(), "the item landed where its status says");
    let text = fs::read_to_string(&moved).expect("read");
    assert!(text.contains("- status: Claimed\n- status_agent: alice\n"), "{text}");

    // ONE file, so nothing is a duplicate and every command still works.
    assert!(ok(&proj, &["fsck"]).contains("layout ok"));
    assert!(ok(&proj, &["show", "WI-905"]).contains("misfiled and legacy"));
}

/// AN UNDATED ITEM IS DATED FROM ITS OWN FILE rather than refused. `created`
/// cannot be INVENTED — it feeds the id mint and the listing's order — but it
/// does not have to be: the filesystem knows when that file was made, and under
/// a file-per-item layout that time IS the item's.
///
/// A migration that refused over a field it could derive would be a barrier, not
/// a check; this is the difference between a project being able to adopt the
/// format and having to reconstruct history first.
///
/// WHICH SOURCE WAS USED IS REPORTED, and that is the half that keeps it honest:
/// a file time is a WEAKER answer than a table (a shared file dates every item
/// in it alike, landing the whole tracker in one day partition), so the run says
/// so and names the better route.
#[test]
fn a_conversion_dates_an_undated_item_from_its_file() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let dir = proj.join("anthill-todo/open");
    fs::create_dir_all(&dir).expect("mkdir");
    fs::write(
        dir.join("WI-043.anthill"),
        "fact WorkItem(id: \"WI-043\", description: \"undated\", acceptance: [], last_status_change: StatusChange(status: Open()))\n",
    )
    .expect("write");

    let out = ok(&proj, &["migrate", "--to", "document"]);
    assert!(
        out.contains("from their file's creation time"),
        "the weaker source is named: {out}"
    );
    assert!(out.contains("--created-from"), "and the better one: {out}");

    let text = fs::read_to_string(dir.join("WI-043.anthill.md")).expect("the document");
    assert!(text.contains("- created: 20"), "a real stamp was written: {text}");
    assert!(!text.contains("?created"), "not the loader's fill var: {text}");
    assert!(ok(&proj, &["show", "WI-043"]).contains("undated"));
}

/// THE TABLE WINS OVER THE FILE TIME, which is the precedence that makes the
/// fallback safe to have: a project that reconstructed real creation dates gets
/// them, and only what the table does not name falls back.
///
/// THE CONTROL is the file time itself — it is today's, and the table's is not,
/// so a run that ignored the table would be visible in the stamp.
#[test]
fn the_supplied_table_is_preferred_over_the_file_time() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let dir = proj.join("anthill-todo/open");
    fs::create_dir_all(&dir).expect("mkdir");
    fs::write(
        dir.join("WI-044.anthill"),
        "fact WorkItem(id: \"WI-044\", description: \"dated by the table\", \
         acceptance: [], last_status_change: StatusChange(status: Open()))\n",
    )
    .expect("write");
    let table = tmp.path().join("created.tsv");
    fs::write(&table, "WI-044\t2026-04-04T04:04:04Z\n").expect("write table");

    let out = ok(
        &proj,
        &["migrate", "--to", "document", "--created-from", table.to_str().unwrap()],
    );
    assert!(out.contains("from the supplied table"), "{out}");
    assert!(
        !out.contains("from their file's creation time"),
        "nothing fell back: {out}"
    );

    let text = fs::read_to_string(dir.join("WI-044.anthill.md")).expect("the document");
    assert!(text.contains("- created: 2026-04-04T04:04:04Z\n"), "{text}");
}

/// `--to item-per-file` WRITES DOCUMENTS TOO, so it needs the same `created`
/// plan — and without it a tracker predating the field became UNUSABLE, not
/// merely unconverted.
///
/// The dead end this pins shut: the migration wrote `created: ?created` (the
/// loader's fill for an omitted required field, an unbound variable) into every
/// document, the startup gate then refused every command — including the
/// `migrate` its own message named — and `--to document` answered "already a
/// document" and exited 0 without stamping. Nothing could fill the field in.
///
/// Both migrations now share one plan, so a shared-file tracker that predates
/// the field converts in one step and is READABLE afterwards. That last clause
/// is the assertion that matters: the old failure produced a tree that loaded
/// and then refused every command.
#[test]
fn migrating_a_pre_created_tracker_dates_it_and_leaves_it_readable() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(
        &tmp,
        "fact WorkItem(id: \"WI-001\", description: \"a pre-created item\", \
         acceptance: [], depends_on: [], last_status_change: StatusChange(status: Open()))\n\
         fact WorkItem(id: \"WI-002\", description: \"another\", \
         acceptance: [], depends_on: [], last_status_change: StatusChange(status: Open()))\n",
    );

    let out = ok(&proj, &["migrate", "--to", "item-per-file"]);
    assert!(out.contains("from their file's creation time"), "{out}");

    let text = fs::read_to_string(proj.join("anthill-todo/open/WI-001.anthill.md"))
        .expect("the document");
    assert!(text.contains("- created: 20"), "{text}");
    assert!(!text.contains("?created"), "no unbound stamp reached disk: {text}");

    let listed = ok(&proj, &["list"]);
    assert!(
        listed.contains("a pre-created item") && listed.contains("another"),
        "and the tracker reads afterwards: {listed}"
    );
}

/// §5.3's FIRST malformed-editing row, end to end: a chapter the mapping names
/// but the file does not carry leaves an `Option` field `none()`.
///
/// It needs no rule of its own, and that is the point: the chapter is spliced
/// into the fact before the loader sees it, so an ABSENT chapter simply leaves
/// the field off, and the loader's existing omitted-optional handling answers.
/// The document is written by hand here because no command produces one — `add`
/// always has a description.
#[test]
fn a_document_with_no_description_chapter_loads_with_none() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let dir = proj.join("anthill-todo/open");
    fs::create_dir_all(&dir).expect("mkdir");
    fs::write(
        dir.join("WI-20260101-AAAAA-no-chapter.anthill.md"),
        "## Attributes\n\n- id: WI-20260101-AAAAA-no-chapter\n\
         - created: 2026-01-01T00:00:00Z\n\n- status: Open\n",
    )
    .expect("write");

    let shown = ok(&proj, &["show", "WI-AAAAA"]);
    assert!(shown.contains("WI-20260101-AAAAA-no-chapter"), "{shown}");
    assert!(shown.contains("Status:"), "the item loads: {shown}");
    assert!(
        !shown.contains("Description:"),
        "an absent chapter is an absent description, not an empty one: {shown}"
    );
}

/// §7's "a key naming neither a field of the functor nor a declared attributes
/// field" row: the attributes chapter is the machine's region, and a key the
/// schema does not declare BLOCKS — because writing the file back would drop it.
///
/// The fault is SCOPED to that field (§7): the rest of the item still loads, and
/// what makes reading it partially safe is precisely that writes are refused.
#[test]
fn an_unknown_attributes_key_is_a_load_error_naming_the_file() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let dir = proj.join("anthill-todo/open");
    fs::create_dir_all(&dir).expect("mkdir");
    fs::write(
        dir.join("WI-20260101-BBBBB-bad-key.anthill.md"),
        "## Attributes\n\n- id: WI-20260101-BBBBB-bad-key\n\
         - created: 2026-01-01T00:00:00Z\n\n- status: Open\n\n- nonesuch: x\n",
    )
    .expect("write");

    let err = fails(&proj, &["list"]);
    assert!(err.contains("nonesuch"), "the offending key is named: {err}");
    assert!(err.contains("bad-key.anthill.md"), "and the file: {err}");
}
