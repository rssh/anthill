//! WI-1120 — a work item is a DOCUMENT: an anthill head plus markdown chapters.
//!
//! Design: `rustland/anthill-todo/docs/design/backend-github-coordination.md`
//! §5.3 (the rules) and §5.4 (the mapping and a worked example). `anthill-core`'s
//! own `persistence::document` unit tests drive the scanner; THIS one drives the
//! CLI, so it measures the parts that only exist end to end — the declared
//! mapping reaching the store, prose leaving the head and coming back, and the
//! invariant that keeps a user's hand-added notes alive.
//!
//! WHAT FAILS WITHOUT THE CHANGE: every test here. Before it an item is a block
//! of `fact` declarations in `WI-NNN.anthill`, so the file these look for does
//! not exist.
//!
//! WHAT PASSES EITHER WAY BY DESIGN: none of them. The nearest candidate is
//! `a_state_change_leaves_the_chapters_byte_identical`, which reads like a
//! restatement of WI-1114's "a claim moves the file" — but its assertion is on
//! the BYTES of prose the head does not mention, and it fails the day the store
//! starts re-serialising a whole file from facts, which is the one failure mode
//! that would quietly eat a user's notes.

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
    status_field: "status",
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

/// THE SHAPE (§5.4): one item file is a fenced `anthill` head followed by
/// markdown chapters, and the prose is NOT in the head.
#[test]
fn an_added_item_is_a_fenced_head_plus_a_description_chapter() {
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
    assert!(text.starts_with("```anthill\n"), "{text}");
    let (head, body) = text.split_once("\n```\n").expect("a closed head fence");
    assert!(head.contains("fact WorkItem(id: \""), "{head}");
    assert!(
        !head.contains("prose that leaves the head"),
        "the description is NOT in the head: {head}"
    );
    assert!(body.contains("## description\n\nprose that leaves the head"), "{body}");
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
    assert_eq!(text.matches("\n## Feedback\n").count(), 1, "one container: {text}");
    assert_eq!(text.matches("\n### ").count(), 2, "two entries: {text}");
    assert!(text.contains(" — user\n"), "the author decorates its heading: {text}");
    assert!(text.contains(" — claude\n"), "{text}");
    assert!(text.contains("the first note"), "{text}");
    // The head keeps the structured half of each row and none of the prose.
    let head = text.split("\n```\n").next().expect("head");
    assert_eq!(head.matches("fact Feedback(").count(), 2, "{head}");
    assert!(!head.contains("the first note"), "{head}");
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
    let chapters_before = edited.split_once("\n```\n").expect("head fence").1.to_string();

    ok(&proj, &["claim", &id, "--agent", "claude"]);

    let moved = fs::read_to_string(the_document(&proj, "claimed")).expect("the item moved");
    assert!(moved.contains("Claimed(agent: \"claude\""), "the head WAS rewritten: {moved}");
    let chapters_after = moved.split_once("\n```\n").expect("head fence").1;
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
    assert!(text.contains("## description\n\na second wording"), "{text}");
    assert!(!text.contains("the first wording"), "{text}");
    assert!(text.contains("a note that must not move"), "{text}");
}

/// THE WRITER'S REFUSAL. Prose carrying a heading at the reserved level would
/// END its own chapter when read back, and the tail would reappear as a stray
/// chapter — so it is caught BEFORE the file is written, where the command can
/// still fail with nothing on disk.
#[test]
fn prose_carrying_a_reserved_heading_is_refused_and_nothing_is_written() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let id = added_id(&ok(&proj, &["add", "intact", "--created", "2026-08-17T10:22:03Z"]));
    let before = fs::read_to_string(the_document(&proj, "open")).expect("read");

    let err = fails(&proj, &["update", &id, "--description", "intro\n## a chapter\ntail"]);
    assert!(err.contains("ends this chapter"), "{err}");

    let after = fs::read_to_string(the_document(&proj, "open")).expect("read");
    assert_eq!(after, before, "the file is untouched");
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

/// AN ENTRY HEADING IS A PROJECTION and is CHECKED, which is the only thing that
/// makes positional binding safe: without it a reordered or hand-edited entry
/// would silently rebind prose onto the wrong row.
#[test]
fn a_stale_entry_heading_is_reported_and_fsck_fix_rewrites_it() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let id = added_id(&ok(&proj, &["add", "with a note", "--created", "2026-08-17T10:22:03Z"]));
    ok(&proj, &["feedback", &id, "a note", "--agent", "user"]);

    let path = the_document(&proj, "open");
    let text = fs::read_to_string(&path).expect("read");
    fs::write(&path, text.replace(" — user\n", " — somebody-else\n")).expect("write");

    let reported = String::from_utf8_lossy(&run_in(&proj, &["fsck"]).stderr).into_owned();
    assert!(reported.contains("somebody-else"), "{reported}");
    assert!(reported.contains("regenerated from the head"), "{reported}");

    let repaired = ok(&proj, &["fsck", "--fix"]);
    assert!(repaired.contains("rewrote"), "{repaired}");
    assert!(
        fs::read_to_string(&path).expect("read").contains(" — user\n"),
        "the heading agrees with its fact again"
    );
}

/// REORDERED ENTRIES ARE NOT A HEADING PROBLEM, and the distinction is the whole
/// reason positional binding is safe. Entries bind to facts BY POSITION, so a
/// file whose entries were swapped has already handed each fact the wrong prose
/// — and "repairing" it by rewriting the headings to match would make the file
/// self-consistent while permanently reattributing every note to the wrong
/// author. The repair moves the PROSE.
///
/// THE CONTROL IS THE TEST ABOVE: a hand-edited heading, where the headings are
/// NOT a permutation of the facts, still gets rewritten. One uniform rule cannot
/// serve both, and picking the wrong one silently corrupts an audit trail.
#[test]
fn swapped_entries_are_moved_back_rather_than_relabelled() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let id = added_id(&ok(&proj, &["add", "two notes", "--created", "2026-08-17T10:22:03Z"]));
    ok(&proj, &["feedback", &id, "the first note", "--agent", "user"]);
    ok(&proj, &["feedback", &id, "the second note", "--agent", "claude"]);

    // Swap the two entries, the way a careless merge or hand-edit would.
    let path = the_document(&proj, "open");
    let text = fs::read_to_string(&path).expect("read");
    let (head, body) = text.split_once("## Feedback\n").expect("a container");
    let entries: Vec<&str> = body
        .split("### ")
        .filter(|e| !e.trim().is_empty())
        .collect();
    assert_eq!(entries.len(), 2, "two entries: {body}");
    let swapped = format!("{head}## Feedback\n### {}### {}", entries[1], entries[0]);
    fs::write(&path, &swapped).expect("write");

    // It BLOCKS — every read of this file is currently wrong, not just its
    // headings — and says which way the repair goes.
    let err = fails(&proj, &["list"]);
    assert!(err.contains("wrong order"), "{err}");
    assert!(err.contains("will not relabel"), "{err}");

    let repaired = ok(&proj, &["fsck", "--fix"]);
    assert!(repaired.contains("back in the head's order"), "{repaired}");

    // Each note is under its OWN heading again.
    let fixed = fs::read_to_string(&path).expect("read");
    let user_at = fixed.find("— user").expect("the user entry");
    let first = fixed.find("the first note").expect("the first note");
    let claude_at = fixed.find("— claude").expect("the claude entry");
    let second = fixed.find("the second note").expect("the second note");
    assert!(user_at < first && first < claude_at, "notes reattached: {fixed}");
    assert!(claude_at < second, "notes reattached: {fixed}");
    assert!(ok(&proj, &["fsck"]).contains("layout ok"));
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
         acceptance: [], status: Open)\n\n\
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
    assert!(text.contains("created: \"2026-04-04T04:04:04Z\""), "{text}");
    assert!(text.contains("## description\n\na legacy item"), "{text}");
    assert!(text.contains("a legacy note"), "{text}");
    // The rows are the rows they were — a reformat, not a data change.
    let shown = ok(&proj, &["show", "WI-042"]);
    assert!(shown.contains("a legacy item") && shown.contains("a legacy note"), "{shown}");
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
        "fact WorkItem(id: \"WI-043\", description: \"undated\", acceptance: [], status: Open)\n",
    )
    .expect("write");

    let out = ok(&proj, &["migrate", "--to", "document"]);
    assert!(
        out.contains("from their file's creation time"),
        "the weaker source is named: {out}"
    );
    assert!(out.contains("--created-from"), "and the better one: {out}");

    let text = fs::read_to_string(dir.join("WI-043.anthill.md")).expect("the document");
    assert!(text.contains("created: \""), "a real stamp was written: {text}");
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
         acceptance: [], status: Open)\n",
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
    assert!(text.contains("created: \"2026-04-04T04:04:04Z\""), "{text}");
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
         acceptance: [], depends_on: [], status: Open)\n\
         fact WorkItem(id: \"WI-002\", description: \"another\", \
         acceptance: [], depends_on: [], status: Open)\n",
    );

    let out = ok(&proj, &["migrate", "--to", "item-per-file"]);
    assert!(out.contains("from their file's creation time"), "{out}");

    let text = fs::read_to_string(proj.join("anthill-todo/open/WI-001.anthill.md"))
        .expect("the document");
    assert!(text.contains("created: \""), "{text}");
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
        "```anthill\nfact WorkItem(id: \"WI-20260101-AAAAA-no-chapter\", \
         created: \"2026-01-01T00:00:00Z\", acceptance: [], status: Open)\n```\n",
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

/// §5.3's "unknown key in the head" row: the head is the machine's region, and a
/// field the schema does not declare is a LOAD ERROR naming the file.
///
/// PASSES EITHER WAY BY DESIGN — this is the loader's existing check, not one
/// this increment adds. It is pinned here because the acceptance surface lists
/// it, and because what it proves is specific to the encoding: the head really
/// is parsed as anthill against the declared domain, rather than scanned for
/// what the store happens to want.
#[test]
fn an_unknown_key_in_the_head_is_a_load_error_naming_the_file() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let dir = proj.join("anthill-todo/open");
    fs::create_dir_all(&dir).expect("mkdir");
    fs::write(
        dir.join("WI-20260101-BBBBB-bad-key.anthill.md"),
        "```anthill\nfact WorkItem(id: \"WI-20260101-BBBBB-bad-key\", \
         created: \"2026-01-01T00:00:00Z\", acceptance: [], status: Open, nonesuch: \"x\")\n```\n",
    )
    .expect("write");

    let err = fails(&proj, &["list"]);
    assert!(err.contains("nonesuch"), "the offending key is named: {err}");
    assert!(err.contains("bad-key.anthill.md"), "and the file: {err}");
}
