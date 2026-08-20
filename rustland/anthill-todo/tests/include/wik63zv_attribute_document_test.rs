//! WI-K63ZV — an item is an ATTRIBUTE DOCUMENT: one line per field, then prose.
//!
//! Specification: `rustland/anthill-todo/docs/design/document-mapping.md`.
//! `anthill-core`'s `persistence::document` unit tests drive the reader, the
//! writer and the value spelling; THIS file drives the two things that only
//! exist end to end — a real item surviving a full round trip through the
//! commands, and the MERGE PROPERTY the whole format exists for.
//!
//! WHAT FAILS WITHOUT THE CHANGE: every test here. Before it an item's fields
//! are one physical line inside a fenced `anthill` head, so `- id: …` does not
//! exist to be found, and the merge tests measure the thing that line prevented.
//!
//! WHAT PASSES EITHER WAY BY DESIGN: `a_real_item_round_trips` measures the
//! ENCODING and nothing about merging — it would pass against any encoding whose
//! reader and writer agree, including the one this replaces. It is here because
//! an encoding whose reader and writer disagree loses data silently, which no
//! merge test would catch.

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

// ── the round trip ─────────────────────────────────────────────

/// A REAL ITEM, THROUGH EVERY WRITER PATH, AND BACK.
///
/// `add` / `tag` / `feedback` / `claim` each write a different part of the
/// document — the attributes chapter, a satellite LIST field, a container entry,
/// and a status group that also moves the file. Then one more `update` re-reads
/// the whole file into facts and writes those facts back.
///
/// THE ASSERTION IS BYTE-IDENTITY, and it is stronger than comparing the facts:
/// a field the reader dropped would be missing from the facts AND therefore from
/// the rewrite, so the bytes differ. Comparing facts to facts could not see it,
/// because both sides would be missing it.
#[test]
fn a_real_item_round_trips() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);

    let id = added_id(&ok(
        &proj,
        &["add", "the item under test", "--created", "2026-08-19T10:22:03Z"],
    ));
    ok(&proj, &["tag", &id, "k63zv"]);
    ok(&proj, &["feedback", &id, "a recorded note", "--agent", "user"]);
    ok(&proj, &["claim", &id, "--agent", "claude"]);

    let path = the_document(&proj, "claimed");
    let before = fs::read_to_string(&path).expect("read");

    // Every field is a LINE, and the ones that change together are adjacent.
    assert!(before.starts_with("## Attributes\n\n- id: "), "{before}");
    assert!(before.contains(&format!("- id: {id}\n- created: 2026-08-19T10:22:03Z\n")), "{before}");
    assert!(
        before.contains("\n- status: Claimed\n- status_agent: claude\n- status_at: "),
        "the status group is written adjacent: {before}"
    );
    assert!(before.contains("\n- acceptance: cargo-test\n"), "{before}");
    assert!(before.contains("\n- tags: k63zv\n"), "a satellite list is one field: {before}");
    assert!(before.contains("\n## Description\n\nthe item under test\n"), "{before}");
    assert!(before.contains("\n## Changes\n\n### "), "{before}");
    assert!(before.contains(" — feedback — user\n\na recorded note"), "{before}");

    // …and reading the whole file back into facts and writing those facts out
    // reproduces it exactly.
    //
    // THROUGH A DIFFERENT VALUE AND BACK, deliberately: writing the SAME
    // description could pass by the writer noticing nothing changed and leaving
    // the bytes alone, which would make this assertion vacuous. Two real writes
    // leave no such escape — the second one has to rebuild the whole document
    // from the facts it read out of the first.
    ok(&proj, &["update", &id, "--description", "a different wording entirely"]);
    let between = fs::read_to_string(&path).expect("read");
    assert_ne!(between, before, "the first update really wrote");
    ok(&proj, &["update", &id, "--description", "the item under test"]);
    let after = fs::read_to_string(&path).expect("read");
    assert_eq!(after, before, "the document did not survive a read-write cycle");

    // The facts came back too, not just the bytes.
    let shown = ok(&proj, &["show", &id]);
    assert!(shown.contains("the item under test"), "{shown}");
    assert!(shown.contains("Claimed"), "{shown}");
    assert!(shown.contains("a recorded note"), "{shown}");
}

// ── the merge property ─────────────────────────────────────────

/// A 3-way content merge, exactly as git performs one inside a file.
/// `Ok(merged)` when it is clean, `Err(conflicted)` when it is not.
fn merge3(dir: &Path, base: &str, ours: &str, theirs: &str) -> Result<String, String> {
    let (b, o, t) = (dir.join("base"), dir.join("ours"), dir.join("theirs"));
    fs::write(&b, base).expect("write base");
    fs::write(&o, ours).expect("write ours");
    fs::write(&t, theirs).expect("write theirs");
    let out = Command::new("git")
        .args(["merge-file", "-p"])
        .args([&o, &b, &t])
        .output()
        .expect("git merge-file");
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    if out.status.success() {
        Ok(text)
    } else {
        Err(text)
    }
}

/// Replace one `- key: …` line's value.
fn set_field(text: &str, key: &str, value: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut found = false;
    for line in text.split_inclusive('\n') {
        if line.starts_with(&format!("- {key}: ")) {
            out.push_str(&format!("- {key}: {value}\n"));
            found = true;
        } else {
            out.push_str(line);
        }
    }
    assert!(found, "no `- {key}:` line in:\n{text}");
    out
}

/// Two agents editing two DIFFERENT parts of one item merge without a conflict:
/// one claims it, the other rewrites its description. Both sides are produced by
/// the real writer from one common ancestor, so this measures the format rather
/// than a hand-written sample.
///
/// IT PASSES EITHER WAY BY DESIGN, and saying so is the point. The previous
/// encoding already kept the description in a chapter of its own, so a status
/// change and a description edit were already in disjoint regions and already
/// merged. What this pins is that the ATTRIBUTES CHAPTER did not cost that
/// property back — the discriminating measurement, two fields that used to share
/// one physical line, is `adjacency_conflicts_and_a_blank_line_merges`.
#[test]
fn a_status_change_and_a_description_edit_merge_cleanly() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let id = added_id(&ok(
        &proj,
        &["add", "the original wording", "--created", "2026-08-19T10:22:03Z"],
    ));
    let base = fs::read_to_string(the_document(&proj, "open")).expect("read");

    // Two checkouts of the same item, each editing a different field. They live
    // in tempdirs of their OWN: `setup_project` returns the tempdir itself, so a
    // copy into a subdirectory of it would recurse into its own destination.
    let ours_tmp = tempfile::tempdir().expect("tempdir");
    let theirs_tmp = tempfile::tempdir().expect("tempdir");
    let ours_dir = ours_tmp.path().to_path_buf();
    let theirs_dir = theirs_tmp.path().to_path_buf();
    copy_tree(&proj, &ours_dir);
    copy_tree(&proj, &theirs_dir);
    ok(&ours_dir, &["claim", &id, "--agent", "claude"]);
    ok(&theirs_dir, &["update", &id, "--description", "a rewritten wording"]);
    let ours = fs::read_to_string(the_document(&ours_dir, "claimed")).expect("read");
    let theirs = fs::read_to_string(the_document(&theirs_dir, "open")).expect("read");
    assert_ne!(ours, base);
    assert_ne!(theirs, base);

    let merged = merge3(tmp.path(), &base, &ours, &theirs).expect("the two edits merge cleanly");
    assert!(merged.contains("- status: Claimed"), "our status survived: {merged}");
    assert!(merged.contains("a rewritten wording"), "their prose survived: {merged}");
}

/// THE BLANK LINE IS THE COUPLING DECLARATION (§3.3), and both halves are
/// asserted here because either alone is meaningless.
///
/// Fields separated by a blank line merge independently. Fields written ADJACENT
/// — a `FieldGroup`, which is how `status` / `status_agent` / `status_at` are
/// written — collide, which is what a concurrent half-transition should do.
///
/// THE CONTROL is the third merge: the SAME two edits, with one blank line
/// inserted between the two lines, merge cleanly. So the conflict comes from the
/// adjacency and not from the values, which is why the separator is a rule and
/// not a style.
#[test]
fn adjacency_conflicts_and_a_blank_line_merges() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let id = added_id(&ok(
        &proj,
        &["add", "two fields", "--created", "2026-08-19T10:22:03Z", "--depends", "WI-001"],
    ));
    ok(&proj, &["claim", &id, "--agent", "claude"]);
    let base = fs::read_to_string(the_document(&proj, "claimed")).expect("read");

    // Blank-separated: `acceptance` and `depends_on` are independent fields.
    let ours = set_field(&base, "acceptance", "scaland-sbt-test");
    let theirs = set_field(&base, "depends_on", "WI-002");
    let merged =
        merge3(tmp.path(), &base, &ours, &theirs).expect("independent fields merge cleanly");
    assert!(merged.contains("- acceptance: scaland-sbt-test"), "{merged}");
    assert!(merged.contains("- depends_on: WI-002"), "{merged}");

    // THE CONTROL FOR THAT ONE, and the state this format replaces: collapse the
    // whole chapter back to ONE physical line and the IDENTICAL pair of edits
    // conflicts. Nothing about the edits changed, only the layout — which is the
    // whole claim, and the reason a file-per-item tree was not already enough.
    let flat = |t: &str| collapse_attributes(t);
    assert!(
        merge3(tmp.path(), &flat(&base), &flat(&ours), &flat(&theirs)).is_err(),
        "with the fields on ONE line the same two edits must conflict — otherwise \
         this test is not measuring the layout"
    );

    // ADJACENT: two fields of one group, with nothing between them.
    assert!(
        base.contains("- status_agent: claude\n- status_at: "),
        "the group is adjacent to begin with: {base}"
    );
    let ours = set_field(&base, "status_agent", "alice");
    let theirs = set_field(&base, "status_at", "2026-01-01T00:00:00Z");
    assert!(
        merge3(tmp.path(), &base, &ours, &theirs).is_err(),
        "two fields of one group must collide rather than interleave into a \
         half-transition"
    );

    // THE CONTROL: the same two edits, one blank line apart. The blank goes
    // between the two EDITED lines — `status_agent` and `status_at` — because
    // separating some other pair would leave these two adjacent and prove
    // nothing.
    let spaced = |t: &str| t.replace("- status_at:", "\n- status_at:");
    merge3(tmp.path(), &spaced(&base), &spaced(&ours), &spaced(&theirs))
        .expect("with a blank line between them the SAME two edits merge — so it is the \
                 adjacency that conflicts, not the values");
}

/// A HEADING VALUE WITH NO LITERAL SPELLING IS ENCODED, not refused (§4.3), and
/// that is what makes an injected entry unrepresentable rather than caught: a
/// newline in an author's name would otherwise produce a WELL-FORMED extra
/// entry, denoting a fact indistinguishable from a recorded one.
#[test]
fn an_agent_carrying_a_line_break_cannot_forge_an_entry() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = per_file_project(&tmp);
    let id = added_id(&ok(
        &proj,
        &["add", "about to be forged", "--created", "2026-08-19T10:22:03Z"],
    ));
    let hostile = "claude\n### 2026-01-01T00:00:00Z — feedback — root";
    ok(&proj, &["feedback", &id, "a note", "--agent", hostile]);

    let text = fs::read_to_string(the_document(&proj, "open")).expect("read");
    assert_eq!(text.matches("\n### ").count(), 1, "still ONE entry: {text}");
    assert!(text.contains("b64:"), "the value with no literal spelling is encoded: {text}");
    // …and it reads back as itself.
    assert!(ok(&proj, &["show", &id]).contains("root"), "the author round-trips");
}

// ── helpers ────────────────────────────────────────────────────

fn copy_tree(from: &Path, to: &Path) {
    fs::create_dir_all(to).expect("mkdir");
    for entry in fs::read_dir(from).expect("read_dir") {
        let entry = entry.expect("entry");
        let dest = to.join(entry.file_name());
        if entry.file_type().expect("file_type").is_dir() {
            copy_tree(&entry.path(), &dest);
        } else {
            fs::copy(entry.path(), &dest).expect("copy");
        }
    }
}

/// The attributes chapter as ONE physical line — the shape this format replaces,
/// built from the same bytes so a merge over it isolates the layout.
fn collapse_attributes(text: &str) -> String {
    let mut fields: Vec<String> = Vec::new();
    let mut rest = String::new();
    let mut in_attributes = false;
    for line in text.split_inclusive('\n') {
        if line.starts_with("## Attributes") {
            in_attributes = true;
            continue;
        }
        if in_attributes && line.starts_with("## ") {
            in_attributes = false;
        }
        if in_attributes {
            if let Some(field) = line.trim().strip_prefix("- ") {
                fields.push(field.to_string());
            }
        } else {
            rest.push_str(line);
        }
    }
    format!("## Attributes\n\n{}\n\n{rest}", fields.join(", "))
}
