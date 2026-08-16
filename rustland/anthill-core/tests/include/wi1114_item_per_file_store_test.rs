//! WI-1114 — `ItemPerFileStore`: one file per primary row, one directory per
//! state, and a state change that is a FILE MOVE.
//!
//! Design: `rustland/anthill-todo/docs/design/backend-github-coordination.md`
//! §4 (layout), §5 / §5.1 (the move and the relocation rule), §5.2 (why this is
//! a sibling `Store` and not a `FileConvention`), §8.3 (routing), §10 (the loud
//! failures).
//!
//! WHAT DRIVES WHAT. Every test here runs the real seam — `record_file` to seed,
//! then `Store::persist` / `retract` / `update` / `flush` — and then READS THE
//! DISK. "It compiled" is not evidence a store stores.
//!
//! WHICH TESTS FAIL WITHOUT THE CHANGE: all of them; `ItemPerFileStore` is new
//! in this change and there is no other store with content-driven routing. The
//! ones that would pass against a naive implementation and so carry the real
//! weight are called out at their sites:
//!   * `a_state_change_moves_the_file_and_carries_its_satellites` — a store that
//!     wrote the new row and dropped the old would pass a "the new file exists"
//!     assertion; the control is the satellite, which must arrive at the new
//!     path having never been mentioned by the mutation.
//!   * `inter_row_text_survives_a_move` — a block model that kept only rows
//!     passes every routing test and silently eats the file's comments.
//!   * `a_satellite_persisted_after_a_move_lands_at_the_new_path` — routing a
//!     satellite at BUFFER time instead of at flush passes until a move happens
//!     first in the same flush.

use std::path::PathBuf;

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::{ClauseKind, KnowledgeBase, RuleId};
use anthill_core::parse;
use anthill_core::persistence::item_per_file_store::{ItemFields, ItemPerFileStore, LayoutFault};
use anthill_core::persistence::Store;
use smallvec::SmallVec;

/// A domain-neutral stand-in for stage0: a primary row keyed on `id` and filed
/// by `status`, a satellite naming its item through `workitem`, and a row that
/// carries neither key. The store never learns these names — they arrive as its
/// `ItemFields` configuration, which is the whole point of §8.3's
/// parameterization.
const DOMAIN: &str = r#"
namespace test.wi1114
  import anthill.prelude.{String, Int64}

  entity Item(id: String, note: String, status: State)

  enum State
    entity Open
    entity Claimed(agent: String)
    entity ProposalRejected(reason: String)
  end

  entity Note(workitem: String, text: String)

  entity Stamp(version: Int64)

  -- A primary row whose `status` is a STRING rather than a variant: what a
  -- careless hand-edit of an item file produces. It loads (the declaration says
  -- String), and the store cannot place it, because a string names no functor
  -- and so names no directory.
  entity HandEdited(id: String, status: String)
end
"#;

const WI1: &str = "namespace test.wi1114\n\
                   \x20 -- the first item, with a comment nobody should lose\n\
                   \x20 fact Item(id: \"WI-1\", note: \"first\", status: Open)\n\
                   \n\
                   \x20 fact Note(workitem: \"WI-1\", text: \"a note\")\n\
                   end\n";

const WI2: &str = "namespace test.wi1114\n\
                   \x20 fact Item(id: \"WI-2\", note: \"second\", status: Open)\n\
                   end\n";

/// A seeded store over a fresh temp tree, plus the KB the rows live in.
struct Fixture {
    _dir: tempfile::TempDir,
    root: PathBuf,
    kb: KnowledgeBase,
    store: ItemPerFileStore,
    /// The `RuleId`s of each seeded file's facts, in source order, keyed by the
    /// file's path relative to the root.
    rows: Vec<(String, Vec<RuleId>)>,
}

impl Fixture {
    /// `files` is `(path relative to the root, source)`. Each is written to
    /// disk, parsed, loaded, and then handed to the store the way
    /// `anthill-todo`'s host arm hands it over.
    fn new(files: &[(&str, &str)]) -> Fixture {
        let dir = tempfile::tempdir().expect("temp dir");
        let root = dir.path().to_path_buf();

        let stdlib = crate::common::collect_anthill_files(&crate::common::stdlib_dir());
        let mut sources: Vec<String> = stdlib
            .iter()
            .map(|p| std::fs::read_to_string(p).expect("read stdlib file"))
            .collect();
        sources.push(DOMAIN.to_string());
        for (rel, src) in files {
            let path = root.join(rel);
            std::fs::create_dir_all(path.parent().expect("has a parent")).expect("mkdir");
            std::fs::write(&path, src).expect("write fixture file");
            sources.push((*src).to_string());
        }

        let parsed: Vec<_> = sources
            .iter()
            .map(|s| parse::parse(s).expect("fixture parses"))
            .collect();
        let refs: Vec<_> = parsed.iter().collect();
        let mut kb = KnowledgeBase::new();
        let (_, per_file) = crate::common::expect_loaded(load::load_all_per_file(
            &mut kb,
            &refs,
            &NullResolver,
        ));

        let mut store = ItemPerFileStore::new(root.clone(), ItemFields::new("status", "id", "workitem"));
        let offset = stdlib.len() + 1;
        let mut rows = Vec::new();
        for (i, (rel, src)) in files.iter().enumerate() {
            let spans = parsed[offset + i].fact_spans();
            let ids = per_file[offset + i].fact_rule_ids.clone();
            assert_eq!(ids.len(), spans.len(), "{rel}: one RuleId per fact span");
            let pairs: Vec<_> = ids.iter().copied().zip(spans).collect();
            store
                .record_file(&kb, root.join(rel), src, &pairs)
                .expect("seeding a loaded file");
            rows.push(((*rel).to_string(), ids));
        }

        Fixture {
            _dir: dir,
            root,
            kb,
            store,
            rows,
        }
    }

    fn rule(&self, rel: &str, nth: usize) -> RuleId {
        let (_, ids) = self
            .rows
            .iter()
            .find(|(p, _)| p == rel)
            .unwrap_or_else(|| panic!("no seeded file {rel}"));
        ids[nth]
    }

    fn read(&self, rel: &str) -> String {
        std::fs::read_to_string(self.root.join(rel))
            .unwrap_or_else(|e| panic!("read {rel}: {e}"))
    }

    fn exists(&self, rel: &str) -> bool {
        self.root.join(rel).exists()
    }

    /// `Item(id:, note:, status:)` built through the entity funnel, so its named
    /// args carry the declared field order the printer and the discrim tree both
    /// expect.
    fn item(&mut self, id: &str, note: &str, status: TermId) -> TermId {
        let functor = sym(&self.kb, "test.wi1114.Item");
        let id_f = self.kb.intern("id");
        let note_f = self.kb.intern("note");
        let status_f = self.kb.intern("status");
        let id_t = self.kb.alloc(Term::Const(Literal::String(id.into())));
        let note_t = self.kb.alloc(Term::Const(Literal::String(note.into())));
        let named: SmallVec<[(_, _); 2]> =
            SmallVec::from_slice(&[(id_f, id_t), (note_f, note_t), (status_f, status)]);
        self.kb.make_entity_term(functor, SmallVec::new(), named)
    }

    /// The nullary `Open` status, built off the RESOLVED symbol. `make_name_term`
    /// would intern the dotted string as a fresh unresolved symbol, whose
    /// `local_name` is the whole qualified name — and the store now refuses that
    /// rather than filing the row under a directory with dots in its name.
    fn open(&mut self) -> TermId {
        let functor = sym(&self.kb, "test.wi1114.State.Open");
        self.kb.make_name_term_from_sym(functor)
    }

    fn claimed(&mut self, agent: &str) -> TermId {
        let functor = sym(&self.kb, "test.wi1114.State.Claimed");
        let agent_f = self.kb.intern("agent");
        let agent_t = self.kb.alloc(Term::Const(Literal::String(agent.into())));
        self.kb
            .make_entity_term(functor, SmallVec::new(), SmallVec::from_slice(&[(agent_f, agent_t)]))
    }

    fn note(&mut self, item: &str, text: &str) -> TermId {
        let functor = sym(&self.kb, "test.wi1114.Note");
        let wi_f = self.kb.intern("workitem");
        let text_f = self.kb.intern("text");
        let wi_t = self.kb.alloc(Term::Const(Literal::String(item.into())));
        let text_t = self.kb.alloc(Term::Const(Literal::String(text.into())));
        self.kb.make_entity_term(
            functor,
            SmallVec::new(),
            SmallVec::from_slice(&[(wi_f, wi_t), (text_f, text_t)]),
        )
    }

    fn stamp(&mut self, version: i64) -> TermId {
        let functor = sym(&self.kb, "test.wi1114.Stamp");
        let v_f = self.kb.intern("version");
        let v_t = self.kb.alloc(Term::Const(Literal::Int(version)));
        self.kb
            .make_entity_term(functor, SmallVec::new(), SmallVec::from_slice(&[(v_f, v_t)]))
    }

    /// Buffer a persist through the store the way the persist builtin does.
    fn persist(&mut self, fact: TermId) -> Result<(), String> {
        let kind = ClauseKind::Fact;
        let domain = self.kb.intern("test.wi1114");
        self.store
            .persist(&self.kb, fact, kind, domain, None)
            .map_err(|e| e.to_string())
    }

    fn update(&mut self, rule: RuleId, new: TermId) -> Result<bool, String> {
        let kind = self.kb.rule_clause_kind(rule);
        let domain = self.kb.rule_domain(rule);
        self.store
            .update(&self.kb, rule, new, kind, domain, None)
            .map_err(|e| e.to_string())
    }

    fn flush(&mut self) {
        self.store.flush(&self.kb).expect("flush");
    }
}

fn sym(kb: &KnowledgeBase, name: &str) -> anthill_core::intern::Symbol {
    kb.try_resolve_symbol(name)
        .unwrap_or_else(|| panic!("`{name}` must resolve in the fixture domain"))
}

// ── The layout ─────────────────────────────────────────────────

/// A clean tree has nothing to report, and the routing index is built from the
/// FACTS rather than from the directory listing.
#[test]
fn a_clean_tree_reports_no_faults() {
    let f = Fixture::new(&[("open/WI-1.anthill", WI1), ("open/WI-2.anthill", WI2)]);
    assert_eq!(f.store.layout_faults(), Vec::new());
}

// ── The move (§5, §5.1) ────────────────────────────────────────

/// THE INCREMENT'S REASON TO EXIST. `claim WI-1` is one `update` — a retract and
/// a persist of the same key, buffered and flushed once — and the store executes
/// it as a file move.
///
/// THE CONTROL IS THE SATELLITE. A store that merely wrote the new row at the
/// new path and deleted the old file would satisfy "the file moved"; the `Note`
/// is what distinguishes a move from a rewrite, because nothing in the mutation
/// mentions it and it must nonetheless arrive at the destination. §5.1: "the
/// unit of relocation is the FILE, not the fact."
#[test]
fn a_state_change_moves_the_file_and_carries_its_satellites() {
    let mut f = Fixture::new(&[("open/WI-1.anthill", WI1), ("open/WI-2.anthill", WI2)]);
    let item = f.rule("open/WI-1.anthill", 0);

    let claimed = f.claimed("claude");
    let new = f.item("WI-1", "first", claimed);
    assert!(f.update(item, new).expect("update buffers"));
    f.flush();

    assert!(!f.exists("open/WI-1.anthill"), "the source file is gone");
    assert!(f.exists("claimed/WI-1.anthill"), "the item moved to its status");
    let moved = f.read("claimed/WI-1.anthill");
    assert!(
        moved.contains("Claimed(agent: \"claude\")"),
        "the item's own block was rewritten: {moved}"
    );
    assert!(
        moved.contains("fact Note(workitem: \"WI-1\", text: \"a note\")"),
        "the satellite rode along untouched: {moved}"
    );
    assert!(
        f.exists("open/WI-2.anthill"),
        "a different item's file is not touched — that is the whole conflict story"
    );
}

/// A block model that kept only the rows would pass every routing assertion above
/// and quietly eat the file's comments on the first move. This is the control for
/// that: the comment is inter-row text, named by nothing, and must survive.
#[test]
fn inter_row_text_survives_a_move() {
    let mut f = Fixture::new(&[("open/WI-1.anthill", WI1)]);
    let item = f.rule("open/WI-1.anthill", 0);
    let claimed = f.claimed("claude");
    let new = f.item("WI-1", "first", claimed);
    f.update(item, new).expect("update");
    f.flush();

    let moved = f.read("claimed/WI-1.anthill");
    assert!(
        moved.contains("-- the first item, with a comment nobody should lose"),
        "the comment survived: {moved}"
    );
    assert!(
        moved.starts_with("namespace test.wi1114"),
        "and so did the namespace wrapper: {moved}"
    );
    assert!(moved.trim_end().ends_with("end"), "…including its `end`: {moved}");
}

/// An edit that does NOT change the status is the same code path with the same
/// destination: the block is rewritten where it sits and no file is created or
/// removed.
#[test]
fn an_edit_that_keeps_the_status_rewrites_in_place() {
    let mut f = Fixture::new(&[("open/WI-1.anthill", WI1)]);
    let item = f.rule("open/WI-1.anthill", 0);
    let open = f.open();
    let new = f.item("WI-1", "edited", open);
    f.update(item, new).expect("update");
    f.flush();

    assert!(f.exists("open/WI-1.anthill"));
    let text = f.read("open/WI-1.anthill");
    assert!(text.contains("note: \"edited\""), "{text}");
    assert!(!text.contains("note: \"first\""), "the old row is gone: {text}");
    assert!(text.contains("fact Note("), "the satellite stayed: {text}");
}

// ── Routing (§8.3) ─────────────────────────────────────────────

/// A satellite is routed to the file that holds its item AT FLUSH TIME. Routing
/// it when the persist is buffered passes until something moves the item first
/// in the same flush — which is exactly what a `claim` followed by a `feedback`
/// in one process does.
#[test]
fn a_satellite_persisted_after_a_move_lands_at_the_new_path() {
    let mut f = Fixture::new(&[("open/WI-1.anthill", WI1)]);
    let item = f.rule("open/WI-1.anthill", 0);
    let claimed = f.claimed("claude");
    let new = f.item("WI-1", "first", claimed);
    f.update(item, new).expect("update");
    let note = f.note("WI-1", "written while it was moving");
    f.persist(note).expect("persist buffers");
    f.flush();

    assert!(!f.exists("open/WI-1.anthill"));
    let moved = f.read("claimed/WI-1.anthill");
    assert!(
        moved.contains("written while it was moving"),
        "the satellite followed the item: {moved}"
    );
}

/// A row carrying neither key is filed under its own functor at the root — the
/// store-level home a format stamp needs (§11 step 4). It is NOT an error and it
/// is NOT an item.
#[test]
fn a_keyless_row_is_filed_under_its_functor() {
    let mut f = Fixture::new(&[("open/WI-1.anthill", WI1)]);
    let stamp = f.stamp(2);
    f.persist(stamp).expect("persist");
    f.flush();
    assert!(f.exists("stamp.anthill"), "the store-level row got a home");
    assert!(f.read("stamp.anthill").contains("Stamp(version: 2)"));
}

/// A brand-new item creates its file under the directory its status names, with
/// the directory created on demand.
#[test]
fn a_new_item_creates_its_own_file_in_its_status_directory() {
    let mut f = Fixture::new(&[("open/WI-1.anthill", WI1)]);
    let rejected = {
        let functor = sym(&f.kb, "test.wi1114.State.ProposalRejected");
        let reason_f = f.kb.intern("reason");
        let reason_t = f.kb.alloc(Term::Const(Literal::String("no".into())));
        f.kb.make_entity_term(
            functor,
            SmallVec::new(),
            SmallVec::from_slice(&[(reason_f, reason_t)]),
        )
    };
    let new = f.item("WI-9", "fresh", rejected);
    f.persist(new).expect("persist");
    f.flush();
    assert!(
        f.exists("proposal_rejected/WI-9.anthill"),
        "the directory is the snake_case of the status functor, derived and not listed"
    );
}

// ── Retract ────────────────────────────────────────────────────

/// Retracting a satellite drops that block and leaves the file — the file is the
/// ITEM's, not the row's.
#[test]
fn retracting_a_satellite_leaves_the_item_file_standing() {
    let mut f = Fixture::new(&[("open/WI-1.anthill", WI1)]);
    let note = f.rule("open/WI-1.anthill", 1);
    assert!(f.store.retract(&f.kb, note).expect("retract buffers"));
    f.flush();

    let text = f.read("open/WI-1.anthill");
    assert!(text.contains("fact Item(id: \"WI-1\""), "the item stayed: {text}");
    assert!(!text.contains("a note"), "the satellite's block left: {text}");
}

/// Retracting the last row removes the file outright. A directory holding an
/// empty file would read as an item that exists.
#[test]
fn retracting_the_last_row_removes_the_file() {
    let mut f = Fixture::new(&[("open/WI-2.anthill", WI2)]);
    let item = f.rule("open/WI-2.anthill", 0);
    assert!(f.store.retract(&f.kb, item).expect("retract"));
    f.flush();
    assert!(!f.exists("open/WI-2.anthill"));
}

/// Deleting an item whose feedback is append-only leaves the file standing with
/// the stranded rows, and SAYS SO. Dropping them would lose facts the KB still
/// holds and no one asked to delete; silently keeping them would leave a file
/// named after an item that no longer exists.
#[test]
fn deleting_an_item_strands_its_satellites_loudly() {
    let mut f = Fixture::new(&[("open/WI-1.anthill", WI1)]);
    let item = f.rule("open/WI-1.anthill", 0);
    f.store.retract(&f.kb, item).expect("retract");
    f.flush();

    assert!(f.exists("open/WI-1.anthill"), "the satellite's bytes are still there");
    let faults = f.store.layout_faults();
    assert!(
        faults
            .iter()
            .any(|x| matches!(x, LayoutFault::OrphanRow { item, .. } if item == "WI-1")),
        "the stranded row is reported: {faults:?}"
    );
    assert!(
        faults.iter().all(|x| !x.blocking()),
        "…and reporting it does not stand between the user and every later command"
    );
}

// ── Loud failures (§10, and the repo's own principle) ──────────

/// The directory is an index and the fact is the truth. A file in the wrong
/// directory is a half-finished move, and it BLOCKS — the next write would have
/// to guess which of the two the store believes.
#[test]
fn a_file_in_the_wrong_directory_is_a_blocking_fault_that_fsck_repairs() {
    let mut f = Fixture::new(&[("claimed/WI-1.anthill", WI1)]);
    let faults = f.store.layout_faults();
    assert!(
        matches!(
            faults.as_slice(),
            [LayoutFault::PathDisagreement { id, .. }] if id == "WI-1"
        ),
        "the disagreement is named: {faults:?}"
    );
    assert!(faults[0].blocking());

    let moves = f.store.repair_paths().expect("repair");
    assert_eq!(moves.len(), 1);
    assert!(f.exists("open/WI-1.anthill"), "the fact won");
    assert!(!f.exists("claimed/WI-1.anthill"));
    assert_eq!(f.store.layout_faults(), Vec::new());
}

/// The same id in two files: the state a crash between the move's two filesystem
/// steps leaves behind. It blocks, and `fsck --fix` does NOT pick a winner — the
/// misplaced copy's destination IS the other copy, so "repair" would overwrite it.
/// Only whoever interrupted the move knows which file is the item.
#[test]
fn the_same_id_in_two_files_blocks_and_is_not_auto_repaired() {
    let mut f = Fixture::new(&[("open/WI-1.anthill", WI1), ("claimed/WI-1.anthill", WI1)]);
    let faults = f.store.layout_faults();
    assert!(
        faults
            .iter()
            .any(|x| matches!(x, LayoutFault::DuplicateId { id, .. } if id == "WI-1")),
        "{faults:?}"
    );
    assert!(faults.iter().any(|x| x.blocking()));

    let err = f
        .store
        .repair_paths()
        .expect_err("a repair that would overwrite the other copy is refused");
    assert!(err.to_string().contains("WI-1"), "{err}");
    assert!(
        f.exists("open/WI-1.anthill") && f.exists("claimed/WI-1.anthill"),
        "and both files are still there"
    );
}

/// A file holding SEVERAL items — the shared-file layout, which is exactly what a
/// project declaring this backend before migrating into it presents.
///
/// FOUND IN REVIEW, and it was destructive. Read as N misplaced items it produced
/// N `PathDisagreement`s naming ONE file, and `--fix` renamed that whole file to
/// the FIRST item's path and then failed on the second with "no model for
/// <a path that no longer exists>" — every other item's rows lost, the moves
/// already made unreported, and this on the one command offered as the remedy for
/// the state that blocks every other command. It is now its own fault, and the
/// repair refuses.
#[test]
fn one_file_holding_several_items_is_named_as_such_and_never_repaired() {
    let shared = "namespace test.wi1114\n\
                  \x20 fact Item(id: \"WI-1\", note: \"one\", status: Open)\n\
                  \n\
                  \x20 fact Item(id: \"WI-2\", note: \"two\", status: Open)\n\
                  \n\
                  \x20 fact Item(id: \"WI-3\", note: \"three\", status: Open)\n\
                  end\n";
    let mut f = Fixture::new(&[("workitems.anthill", shared)]);

    let faults = f.store.layout_faults();
    assert!(
        matches!(
            faults.as_slice(),
            [LayoutFault::SharedFile { ids, .. }] if ids.len() == 3
        ),
        "ONE fault naming the file's shape, not one per row: {faults:?}"
    );
    assert!(faults[0].blocking());

    let err = f.store.repair_paths().expect_err("splitting a file is not a repair");
    assert!(err.to_string().contains("migrate"), "{err}");
    assert!(
        f.read("workitems.anthill").contains("WI-3"),
        "and every row is still there"
    );
    assert!(
        !f.exists("open/WI-1.anthill"),
        "nothing was moved to one item's path"
    );
}

/// The same id twice in ONE file. The duplicate check used to compare PATHS, so a
/// repeat within a file read as the same row seen again and no fault fired — and
/// then a further persist appended a third copy rather than refusing. (Found in
/// review.)
#[test]
fn the_same_id_twice_in_one_file_is_a_duplicate_too() {
    let twice = "namespace test.wi1114\n\
                 \x20 fact Item(id: \"WI-1\", note: \"one\", status: Open)\n\
                 \n\
                 \x20 fact Item(id: \"WI-1\", note: \"again\", status: Open)\n\
                 end\n";
    let f = Fixture::new(&[("open/WI-1.anthill", twice)]);
    let faults = f.store.layout_faults();
    let dup = faults
        .iter()
        .find(|x| matches!(x, LayoutFault::DuplicateId { id, .. } if id == "WI-1"))
        .unwrap_or_else(|| panic!("the repeat is a duplicate: {faults:?}"));
    assert!(
        format!("{dup}").contains("twice in this one file"),
        "and it says which kind of duplicate it is: {dup}"
    );
    // NOT a shared file: `SharedFile` counts DISTINCT items, and one key repeated
    // is a duplicate key with a different remedy.
    assert!(
        !faults
            .iter()
            .any(|x| matches!(x, LayoutFault::SharedFile { .. })),
        "{faults:?}"
    );
}

/// A satellite retracted in the SAME flush that moves its item. The retract
/// captured the item's OLD path when it was buffered, and by the time the flush
/// reaches it the file lives somewhere else — so the retract has to follow the
/// move, and the emptied-file check has to see that the rewritten item block is
/// still a row. Getting either wrong deletes the item that was mid-move.
#[test]
fn a_satellite_retracted_during_a_move_follows_the_file() {
    let mut f = Fixture::new(&[("open/WI-1.anthill", WI1)]);
    let item = f.rule("open/WI-1.anthill", 0);
    let note = f.rule("open/WI-1.anthill", 1);

    let claimed = f.claimed("claude");
    let new = f.item("WI-1", "first", claimed);
    f.update(item, new).expect("update buffers");
    f.store.retract(&f.kb, note).expect("retract buffers");
    f.flush();

    assert!(!f.exists("open/WI-1.anthill"));
    let moved = f.read("claimed/WI-1.anthill");
    assert!(
        moved.contains("Claimed(agent: \"claude\")"),
        "the item survived the move: {moved}"
    );
    assert!(!moved.contains("a note"), "and the satellite left: {moved}");
}

/// A LOADED row this store cannot place is reported, not raised. `fsck` needs the
/// store built before it can say anything, so raising at seeding would kill the
/// one command written to diagnose the problem — and the user would be left with
/// a tracker that refuses every command, including the one that explains why.
///
/// THE CONTROL is that the store still builds: without the report-don't-raise
/// split, `record_file` returns `Err` and there is no store to ask.
#[test]
fn a_row_this_store_cannot_place_is_reported_rather_than_raised() {
    let malformed = "namespace test.wi1114\n\
                     \x20 fact HandEdited(id: \"WI-7\", status: \"Open\")\n\
                     end\n";
    let f = Fixture::new(&[("open/WI-7.anthill", malformed)]);
    let faults = f.store.layout_faults();
    assert!(
        faults
            .iter()
            .any(|x| matches!(x, LayoutFault::UnroutableRow { .. })),
        "the unplaceable row is named: {faults:?}"
    );
    assert!(
        faults.iter().any(|x| x.blocking()),
        "and it blocks — nothing may write through a store that cannot place a row"
    );
}

/// A primary row with no readable status has no directory to live in. Filing it
/// under a default would put it somewhere the next load disagrees with.
#[test]
fn a_primary_row_without_a_status_is_refused() {
    let mut f = Fixture::new(&[("open/WI-1.anthill", WI1)]);
    let functor = sym(&f.kb, "test.wi1114.Item");
    let id_f = f.kb.intern("id");
    let id_t = f.kb.alloc(Term::Const(Literal::String("WI-3".into())));
    let headless = f
        .kb
        .make_entity_term(functor, SmallVec::new(), SmallVec::from_slice(&[(id_f, id_t)]));
    let err = f.persist(headless).expect_err("a statusless item is refused");
    assert!(err.contains("status"), "the message names the missing field: {err}");
}

/// Both halves of a row's path are read out of the row, so both are checked at
/// the store's edge. An id carrying a separator would file the row outside the
/// tree — with `..`, outside the ROOT — and the next load would not find it
/// there. This is the one input to this store that is user text.
#[test]
fn an_id_that_is_not_a_file_name_is_refused() {
    let mut f = Fixture::new(&[("open/WI-1.anthill", WI1)]);
    let open = f.open();
    let escaping = f.item("../../escaped", "outside the root", open);
    let err = f.persist(escaping).expect_err("a traversing id is refused");
    assert!(err.contains("escaped"), "the message shows the value: {err}");
}

/// A retract of a row this store never saw is an error, not a no-op. The
/// content-keyed fallback the shared-file store falls back to here would compare
/// a loader-normalized canonical against source text and silently match nothing
/// (WI-187) — a write that reports success and changes no bytes.
#[test]
fn retracting_a_row_the_store_never_saw_is_loud() {
    let mut f = Fixture::new(&[("open/WI-1.anthill", WI1)]);
    let open = f.open();
    let orphan = f.item("WI-77", "never seeded", open);
    let domain = f.kb.intern("test.wi1114");
    let rule = f.kb.assert_fact(orphan, ClauseKind::Fact, domain, None);
    let err = f
        .store
        .retract(&f.kb, rule)
        .expect_err("an unaddressable row is refused");
    assert!(
        err.to_string().contains("holds no file"),
        "the message says why: {err}"
    );
}

/// Persisting a second row under an id the store already holds is a refusal, not
/// an overwrite: `add` allocating a duplicate id is the bug §6 exists to remove,
/// and it must not be absorbed here.
#[test]
fn persisting_a_second_row_under_a_live_id_is_refused() {
    let mut f = Fixture::new(&[("open/WI-1.anthill", WI1)]);
    let claimed = f.claimed("someone");
    let dup = f.item("WI-1", "a second WI-1", claimed);
    f.persist(dup).expect("persist buffers — the clash is a flush-time question");
    let err = f.store.flush(&f.kb).expect_err("the clash is refused");
    assert!(err.to_string().contains("WI-1"), "{err}");
}

/// A file on disk the store never read is not written over. The loader WARNS and
/// SKIPS a project file it cannot parse — under a shared-file store that only
/// hides rows, but here the skipped file is an item, so its id is invisible, the
/// allocator can hand it out again, and the write would land on top of it. The
/// rows are recoverable while the file is still there.
#[test]
fn a_file_the_store_never_read_is_not_written_over() {
    let mut f = Fixture::new(&[("open/WI-1.anthill", WI1)]);
    // Stand in for the unparseable file the loader skipped: bytes at a path the
    // store has no model for.
    let squatter = f.root.join("open/WI-5.anthill");
    std::fs::write(&squatter, "fact Item(id: \"WI-5\"  -- unbalanced\n").unwrap();

    let open = f.open();
    let colliding = f.item("WI-5", "would clobber", open);
    f.persist(colliding).expect("persist buffers");
    let err = f.store.flush(&f.kb).expect_err("the write is refused");
    assert!(err.to_string().contains("WI-5"), "{err}");
    assert!(
        std::fs::read_to_string(&squatter).unwrap().contains("unbalanced"),
        "and the bytes are still there to recover"
    );
}

/// A re-add landing on a path this same flush just emptied is the flush finishing
/// its own work, not a stranger's file. The removals run LAST (so a crash leaves a
/// duplicate rather than a hole), which means the old bytes are still on disk when
/// the re-add is routed — and the occupant check used to refuse it with a message
/// about an unparseable file, which is actively wrong. (Found in review.)
#[test]
fn a_re_add_onto_a_path_this_flush_emptied_is_allowed() {
    let mut f = Fixture::new(&[("open/WI-2.anthill", WI2)]);
    let item = f.rule("open/WI-2.anthill", 0);
    f.store.retract(&f.kb, item).expect("retract buffers");
    let open = f.open();
    let reborn = f.item("WI-2", "same id, new row", open);
    f.persist(reborn).expect("persist buffers");
    f.flush();

    let text = f.read("open/WI-2.anthill");
    assert!(text.contains("same id, new row"), "{text}");
    assert!(!text.contains("second"), "the old row is gone: {text}");
}

/// A satellite naming an item no file holds cannot be routed. Writing it to a
/// guessed path would put a row where the next load will not look for it.
#[test]
fn a_satellite_naming_no_item_is_refused_at_flush() {
    let mut f = Fixture::new(&[("open/WI-1.anthill", WI1)]);
    let note = f.note("WI-404", "about nothing");
    f.persist(note).expect("persist buffers");
    let err = f.store.flush(&f.kb).expect_err("an unroutable satellite is refused");
    assert!(err.to_string().contains("WI-404"), "{err}");
}

/// Repeated writes do not make the file taller. Each append and each in-place
/// rewrite has to leave exactly one blank line between blocks — a row block that
/// carried its own trailing newline while the block it replaced did not grows the
/// gap by one line on every state change, which nothing else here would notice.
#[test]
fn repeated_writes_keep_the_file_shape_stable() {
    let mut f = Fixture::new(&[("open/WI-2.anthill", WI2)]);
    for i in 0..3 {
        let note = f.note("WI-2", &format!("note {i}"));
        f.persist(note).expect("persist");
        f.flush();
    }
    let claimed = f.claimed("claude");
    let new = f.item("WI-2", "second", claimed);
    f.update(f.rule("open/WI-2.anthill", 0), new).expect("update");
    f.flush();

    let text = f.read("claimed/WI-2.anthill");
    assert!(
        !text.contains("\n\n\n"),
        "no run of blank lines accumulated:\n{text:?}"
    );
    assert_eq!(
        text.matches("fact ").count(),
        4,
        "the item plus three notes: {text}"
    );
}

// ── The seam this store deliberately does not have ─────────────

/// `retrieve` is not implemented: this store keeps no query index, and answering
/// a pattern from the block model would be a scan pretending to be an index. The
/// default `NotQueryable` is the honest answer, and the anthill side matches it
/// by declaring no `QueryableStore` fact for this backend.
#[test]
fn this_store_does_not_claim_to_be_queryable() {
    let mut f = Fixture::new(&[("open/WI-1.anthill", WI1)]);
    let open = f.open();
    let pattern = f.item("WI-1", "first", open);
    let err = f.store.retrieve(&f.kb, pattern).expect_err("not queryable");
    assert!(err.to_string().contains("retrieve"), "{err}");
}

/// The store writes files a fresh loader can read back. Without this the whole
/// layout is write-only: the CLI's next invocation parses these files.
#[test]
fn what_the_store_writes_parses_back() {
    let mut f = Fixture::new(&[("open/WI-1.anthill", WI1)]);
    let claimed = f.claimed("claude");
    let new = f.item("WI-1", "first", claimed);
    f.update(f.rule("open/WI-1.anthill", 0), new).expect("update");
    let extra = f.note("WI-1", "and one more");
    f.persist(extra).expect("persist");
    f.flush();

    let text = f.read("claimed/WI-1.anthill");
    let reparsed = parse::parse(&text).unwrap_or_else(|e| panic!("re-parse {text}: {e:?}"));
    assert_eq!(
        reparsed.fact_spans().len(),
        3,
        "the item, its original note and the new one: {text}"
    );
}
