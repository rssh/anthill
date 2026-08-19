//! `ItemPerFileStore` — one file per primary row, one directory per state.
//!
//! The second filesystem backend, and a SIBLING of [`IndexedFileStore`], not a
//! convention inside it (WI-1114; design
//! `rustland/anthill-todo/docs/design/backend-github-coordination.md` §5.2).
//! The two models are opposites:
//!
//! | | `IndexedFileStore` | `ItemPerFileStore` |
//! | --- | --- | --- |
//! | a file holds | many unrelated rows | one item and its satellites |
//! | a row is addressed by | its byte range | the file it lives in |
//! | routing is | content-BLIND (`fact_path` reads only the domain) | content-DRIVEN (the status field picks the directory) |
//! | a state change is | an edit | a **file move** (§5.1) |
//!
//! None of the span machinery carries over, so this store implements the six
//! [`Store`] methods and NOT [`super::IndexedStore`] — there is no byte range to
//! hand out. What it holds instead is a **block model** of each file it was
//! seeded with: the ordered list of text blocks the file is made of, each either
//! one resident row or the inter-row text (comments, blank lines) around it.
//!
//! WHY BLOCKS RATHER THAN OFFSETS, given the host could hand over spans just as
//! easily: a relocation REWRITES the whole file at a new path, which shifts or
//! invalidates every offset in it. An offset map would be stale the moment the
//! feature this store exists for runs, and stale offsets do not fail — they drop
//! the wrong bytes. The seeding call consumes the host's spans to CUT the file
//! into blocks and keeps none of them, so a rewrite leaves nothing behind to go
//! stale. `render`ing a file is then a concatenation, and a move is a `BTreeMap`
//! re-key.
//!
//! ## Routing (§8.3)
//!
//! A row is routed by what it carries, against three configured field names so
//! that `anthill-core` stays domain-neutral and stage0's spelling
//! (`status` / `id` / `workitem`) lives in the todo CLI's configuration of it:
//!
//! * carries `id_field` → a PRIMARY row: `<root>/<status_dir>/<id>.anthill`,
//!   where `status_dir` is the snake_case short name of its `status_field`'s
//!   functor. A primary row whose status is missing or is not functor-headed is
//!   a loud refusal — the directory IS its status, so there is no file to pick.
//! * carries `ref_field` → a SATELLITE row (feedback, a tag, a mirror link): the
//!   file of the item it names. Resolved at FLUSH, not at buffer time, so an
//!   item and its first satellite may be persisted in one flush.
//! * neither → a STORE-LEVEL row (a format stamp): `<root>/<functor>.anthill`.
//!
//! ## The relocation rule (§5.1)
//!
//! One flush holding a retract and a persist of the SAME primary key at
//! differing paths executes as a **file move**: the item's block is rewritten
//! where it sits and the whole file is written at the new path, so every other
//! block in it — its feedback, its tags — rides along untouched. That is what
//! makes "moving a work item moves its feedback" fall out of the existing
//! single-flush atomicity of `update` rather than needing a new spec operation.
//!
//! The flush is two filesystem steps however it is ordered (write the new file,
//! remove the old), so a crash between them leaves the item in two files. That
//! is the state [`LayoutFault::DuplicateId`] names, loudly, on the next load.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs;
use std::path::{Path, PathBuf};

use crate::intern::Symbol;
use crate::kb::term::{Literal, Term, TermId};
use crate::kb::typing::get_named_arg;
use crate::kb::{ClauseKind, KnowledgeBase, RuleId};
use crate::span::Span;

use super::document::{
    self, AttrField, Document, DocumentMapping, SegmentKind,
};
use super::print;
use super::{PersistenceError, Store};

/// The suffix of an item file under the plain-`fact` layout (WI-1118).
pub const ITEM_PLAIN_SUFFIX: &str = ".anthill";
/// …and under the document encoding (WI-1120). See [`ItemPerFileStore::item_suffix`].
pub const ITEM_DOCUMENT_SUFFIX: &str = ".anthill.md";

// ── Configuration ──────────────────────────────────────────────

/// The three field names this store routes on. Named rather than positional:
/// three `String`s in a row is three chances to swap two of them, and the
/// symptom of a swap is rows filed under a directory named after an id.
#[derive(Clone, Debug)]
pub struct ItemFields {
    /// The field whose functor names the directory.
    ///
    /// A DOTTED PATH, because the field need not be a direct one:
    /// `last_status_change.status` reaches the state through the record that
    /// carries it. The store follows the path and knows nothing else about the
    /// shape — which is what keeps `anthill-core` out of stage0's schema while
    /// stage0 is free to model a status change as a record.
    pub status: String,
    /// The field carrying a primary row's key (`id`).
    pub id: String,
    /// The field by which a satellite row names its item (`workitem`).
    pub reference: String,
}

impl ItemFields {
    pub fn new(
        status: impl Into<String>,
        id: impl Into<String>,
        reference: impl Into<String>,
    ) -> Self {
        Self {
            status: status.into(),
            id: id.into(),
            reference: reference.into(),
        }
    }
}

// ── Layout faults (§10) ────────────────────────────────────────

/// A disagreement between the layout (an index) and the facts (the truth).
///
/// The directory is a coarse, greppable projection of the `status` field, and
/// the file name of the `id` field. That redundancy is CHECKED here rather than
/// assumed: §5.1's move is two filesystem steps, and a crash between them leaves
/// exactly these states behind.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LayoutFault {
    /// A primary row sits at a path its own fields do not name — a half-finished
    /// move, or a hand-edit of the status field without the rename. The FACT
    /// wins: `fsck --fix` moves the file to `expected`.
    PathDisagreement {
        found: PathBuf,
        expected: PathBuf,
        id: String,
    },
    /// The same primary key in two files. Under a coordinated allocator this is
    /// unreachable; reached, it means either the allocator is broken or a move
    /// died between its two filesystem steps.
    DuplicateId {
        id: String,
        first: PathBuf,
        second: PathBuf,
    },
    /// A satellite row naming an item no file holds. Not blocking: a tracker can
    /// arrive in this state through a hand-edit, a partial merge, or a `delete`
    /// run by a build predating WI-1123 (which flipped `Feedback` to
    /// `non_monotone` so that deleting an item takes its satellites with it —
    /// before that, every delete minted one of these by construction). A store
    /// refuses to CREATE an orphan (`path_of`) and tolerates INHERITING one, so
    /// this is a state to REPORT, not one to refuse every later command over.
    OrphanRow {
        path: PathBuf,
        functor: String,
        item: String,
    },
    /// A satellite row in a file other than its item's. Its item would not carry
    /// it through a move. Not blocking, for the same reason as `OrphanRow`.
    MisfiledRow {
        found: PathBuf,
        expected: PathBuf,
        functor: String,
        item: String,
    },
    /// A loaded row this store cannot place — a hand-edited status that is a
    /// string rather than a variant, say. Blocking, and reported rather than
    /// raised, so that `fsck` (which needs the store BUILT to say anything at
    /// all) still runs and can name every such row at once. Raising it from
    /// seeding would kill the one command written to diagnose it.
    UnroutableRow { path: PathBuf, reason: String },
    /// One file holding SEVERAL primary rows — the shared-file layout, read by a
    /// store that expects one item per file. Almost always a project that
    /// declared this backend before migrating into it.
    ///
    /// It is its own fault kind because the alternative reading is actively
    /// destructive: taken as N misplaced items, the "repair" renames the whole
    /// shared file to ONE item's path and drops the rest. And it would drown the
    /// report — this repo's own tracker would produce 1110 of them. Blocking,
    /// and not repairable by a file move: exploding a shared file into one file
    /// per item is `migrate`'s job, not `fsck`'s.
    SharedFile { path: PathBuf, ids: Vec<String> },
    /// An item held in a PLAIN `.anthill` file by a project whose items are
    /// documents (WI-1120) — a tracker that has not run `migrate --to document`.
    ///
    /// ITS OWN FAULT RATHER THAN A `PathDisagreement`, and the difference is what
    /// the remedy would do: `fsck --fix` moves a file to the path its fact names,
    /// and moving `WI-1.anthill` to `WI-1.anthill.md` would produce a file with
    /// the document's NAME and the plain layout's CONTENTS — unreadable on the
    /// next load, and a repair that made things worse. Converting the encoding is
    /// `migrate`'s job, exactly as splitting a shared file is.
    PlainItemFile { path: PathBuf, id: String },
    /// TWO REAL ITEMS whose minted ids share an identity prefix (WI-1121, §6.6).
    ///
    /// A DIFFERENT FAULT FROM `DuplicateId`, WITH THE OPPOSITE REMEDY, which is
    /// why they are separate: a duplicate id is one item in two files and the
    /// repair is to delete one, while this is two items whose digests collided
    /// and the repair is to RENUMBER the loser.
    ///
    /// COMPARED ON THE `<time>-<hash>` PREFIX, NEVER THE WHOLE ID, and that is
    /// the thing a naive implementation gets wrong silently: two items whose
    /// digests collide have different descriptions, hence different slugs, hence
    /// different FILENAMES — so a whole-string comparison misses every case, and
    /// git merges the two files perfectly cleanly because at the VCS level
    /// nothing is wrong. The tracker is the only possible detector.
    ///
    /// The whole-id comparison is also what tells the two faults apart, for the
    /// same reason: under `ContentHash` a shared prefix AND a shared slug means a
    /// shared description, which means one item.
    IdCollision {
        prefix: String,
        first: PathBuf,
        second: PathBuf,
    },
    /// A fault the document READER found in one file (WI-K63ZV, §7): an
    /// attributes line that is not `- key: value`, a key naming no field, a
    /// value with no spelling for its declared type.
    ///
    /// CARRIED THROUGH RATHER THAN RAISED, and that is the design §7 states as
    /// one thing rather than two: the reader reads as much as can be read, and
    /// what makes a partial read safe rather than data loss is that a blocking
    /// fault refuses WRITES. Written back, a document the reader had to drop a
    /// field from would lose that field silently — the reader drops what it could
    /// not parse, the writer re-renders from what it holds, and the difference is
    /// gone.
    DocumentFault {
        path: PathBuf,
        blocking: bool,
        message: String,
    },
}

impl LayoutFault {
    /// Whether this fault must stop a normal command.
    ///
    /// The split is §10's: a fault that makes the store's own ROUTING ambiguous
    /// blocks (two files claiming one key; a file whose path denies its fact),
    /// because the next write would have to guess. A fault that merely leaves a
    /// row stranded is reported by `fsck` and does not stand between the user
    /// and the tracker.
    pub fn blocking(&self) -> bool {
        match self {
            LayoutFault::PathDisagreement { .. }
            | LayoutFault::DuplicateId { .. }
            | LayoutFault::IdCollision { .. }
            | LayoutFault::PlainItemFile { .. }
            | LayoutFault::UnroutableRow { .. }
            | LayoutFault::SharedFile { .. } => true,
            LayoutFault::OrphanRow { .. } | LayoutFault::MisfiledRow { .. } => false,
            LayoutFault::DocumentFault { blocking, .. } => *blocking,
        }
    }
}

impl std::fmt::Display for LayoutFault {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LayoutFault::PathDisagreement {
                found,
                expected,
                id,
            } => write!(
                f,
                "{}: `{id}` says it belongs at {} — the directory is an index and the \
                 fact is the truth; `fsck --fix` moves it",
                found.display(),
                expected.display()
            ),
            LayoutFault::DuplicateId { id, first, second } if same_path(first, second) => write!(
                f,
                "{}: `{id}` is declared twice in this one file; a primary key names one row",
                first.display()
            ),
            LayoutFault::DuplicateId { id, first, second } => write!(
                f,
                "`{id}` is held by two files, {} and {}; one of them is debris from an \
                 interrupted move and only you can say which",
                first.display(),
                second.display()
            ),
            LayoutFault::OrphanRow {
                path,
                functor,
                item,
            } => write!(
                f,
                "{}: a `{functor}` row names `{item}`, which no file holds",
                path.display()
            ),
            LayoutFault::MisfiledRow {
                found,
                expected,
                functor,
                item,
            } => write!(
                f,
                "{}: a `{functor}` row names `{item}`, whose file is {} — it will not \
                 travel with its item",
                found.display(),
                expected.display()
            ),
            LayoutFault::UnroutableRow { path, reason } => {
                write!(f, "{}: {reason}", path.display())
            }
            LayoutFault::PlainItemFile { path, id } => write!(
                f,
                "{}: `{id}` is still a plain `fact` file, and this project's items are \
                 documents — run `anthill-todo migrate --to document` to convert the tree. \
                 `fsck --fix` will not do it: renaming the file would leave its name and its \
                 contents disagreeing",
                path.display()
            ),
            LayoutFault::IdCollision {
                prefix,
                first,
                second,
            } => write!(
                f,
                "`{prefix}` names two DIFFERENT items, {} and {} — their content-derived ids \
                 collided, which git cannot see because the two files have different names. \
                 One of them has to be renumbered",
                first.display(),
                second.display()
            ),
            LayoutFault::DocumentFault { path, message, .. } => {
                write!(f, "{}: {message}", path.display())
            }
            LayoutFault::SharedFile { path, ids } => write!(
                f,
                "{} holds {} items ({}, …) — this store gives each item a file of its own, \
                 and splitting a shared file is `migrate`'s job, not a repair",
                path.display(),
                ids.len(),
                ids.iter().take(3).cloned().collect::<Vec<_>>().join(", "),
            ),
        }
    }
}

// ── The block model ────────────────────────────────────────────

/// What a stretch of a file IS. Being a row and being addressable are two
/// different things, and conflating them cost a file: after a relocation the
/// item's block is rewritten and its old `RuleId` is dead, so the block is a row
/// with no name — and a single `Option<RuleId>` made it indistinguishable from a
/// blank line, which is what "the file has no rows left, delete it" reads next.
enum Kind {
    /// A fact declaration. `Some` when this store can still address it; `None`
    /// for a row appended at runtime or rewritten in place — [`Store::persist`]
    /// is handed the fact, never the `RuleId` the KB is about to mint for it, so
    /// such a row has no name until the next load gives it one.
    Row(Option<RuleId>),
    /// The text around a row: comments, blank lines, a namespace wrapper.
    Text,
}

/// One stretch of a file.
struct Block {
    kind: Kind,
    text: String,
}

impl Block {
    fn rule(&self) -> Option<RuleId> {
        match self.kind {
            Kind::Row(rule) => rule,
            Kind::Text => None,
        }
    }

    fn is_text(&self) -> bool {
        matches!(self.kind, Kind::Text)
    }
}

/// One markdown chapter of a document file, as text this store may replace
/// wholesale but never reads into.
///
/// IDENTIFIED BY A MINTED `id`, NOT BY ITS POSITION, and that is not tidiness: a
/// retract removes a segment from the middle, and index-keyed bindings would then
/// all name the chapter after the one they meant — silently, and only for the
/// rows that happened to sit later in the file.
struct DocSegment {
    id: u32,
    kind: SegmentKind,
    text: String,
}

/// One element of a satellite list — a `Tag`, written as one comma-separated
/// item of an attributes field rather than as a row of its own (§3.1).
struct ListElement {
    id: u32,
    /// The attributes field it is written under.
    named: String,
    /// Its value, already spelled.
    value: String,
}

/// A document file's model: the item's own fields, its satellite lists, and the
/// prose chapters below them.
///
/// THE ATTRIBUTES CHAPTER IS NOT KEPT AS TEXT, and that is the difference from
/// the fenced-head encoding this replaces. It is DATA, wholly derived from the
/// facts, so it is RE-RENDERED on every write; nothing about the bytes on disk
/// is authoritative. Prose is the opposite — a description's text is the fact's
/// value and is carried verbatim — which is why the two live in different fields
/// here rather than in one list of chapters.
#[derive(Default)]
struct DocModel {
    /// The item's own fact, as the attributes lines it renders to.
    item: Option<Vec<AttrField>>,
    lists: Vec<ListElement>,
    body: Vec<DocSegment>,
    next_segment: u32,
}

#[derive(Default)]
struct FileModel {
    blocks: Vec<Block>,
    /// `Some` for an item document; `None` for a plain `.anthill` file, which is
    /// every file under a project that declares no mapping and, in every
    /// project, the store-level rows.
    doc: Option<DocModel>,
}

impl FileModel {
    fn render(&self, mapping: Option<&DocumentMapping>) -> String {
        let Some(doc) = &self.doc else {
            let mut out = String::new();
            for b in &self.blocks {
                out.push_str(&b.text);
            }
            return out;
        };
        let mut out = String::new();
        if let Some(mapping) = mapping {
            let mut fields = doc.item.clone().unwrap_or_default();
            let mut by_named: HashMap<String, Vec<String>> = HashMap::new();
            for e in &doc.lists {
                by_named.entry(e.named.clone()).or_default().push(e.value.clone());
            }
            fields.extend(document::list_fields(mapping, &by_named));
            out.push_str(&document::render_attributes(
                mapping.level,
                &mapping.attributes,
                &fields,
            ));
        }
        for seg in &doc.body {
            out.push_str(&seg.text);
        }
        out
    }

    fn doc_mut(&mut self) -> &mut DocModel {
        self.doc.get_or_insert_with(DocModel::default)
    }

    fn position_of(&self, rule: RuleId) -> Option<usize> {
        self.blocks.iter().position(|b| b.rule() == Some(rule))
    }

    /// Whether this file still declares anything. Asked of ROWS, not of
    /// addressable rows: a file whose only row was just rewritten in place still
    /// holds that row, and deleting it because the store no longer has a name for
    /// it would delete the item the rewrite was moving.
    fn holds_rows(&self) -> bool {
        match &self.doc {
            Some(doc) => doc.item.is_some() || !doc.lists.is_empty() || !doc.body.is_empty(),
            None => self.blocks.iter().any(|b| !b.is_text()),
        }
    }

    /// Drop the block at `at`, and with it a purely-blank run of text that
    /// followed it — otherwise each retract cycle leaves the file one blank
    /// line taller. Mirrors [`super::extend_drop_end`], which does the same
    /// thing to a byte range.
    fn drop_block(&mut self, at: usize) {
        if at + 1 < self.blocks.len()
            && self.blocks[at + 1].is_text()
            && self.blocks[at + 1].text.trim().is_empty()
        {
            self.blocks.remove(at + 1);
        }
        self.blocks.remove(at);
    }

    /// Append a row, separated from what is already there by exactly one blank
    /// line. Reads the LAST block rather than the rendered file, which it can
    /// because [`Self::push_free`] keeps text blocks maximal: a trailing `Text`
    /// block IS the file's whole trailing run of inter-row text.
    fn append_row(&mut self, text: String) {
        let separator = match self.blocks.last() {
            None => "",
            Some(last) if !last.is_text() => "\n\n",
            Some(last) if last.text.ends_with("\n\n") => "",
            Some(last) if last.text.ends_with('\n') => "\n",
            Some(_) => "\n\n",
        };
        self.push_free(separator);
        self.blocks.push(Block {
            kind: Kind::Row(None),
            text: row_text(&text),
        });
        self.push_free("\n");
    }

    /// Append inter-row text, MERGING into a trailing text block rather than
    /// pushing a second one beside it. The invariant this maintains — **text
    /// blocks are maximal**, never two in a row — is load-bearing twice:
    /// [`Self::drop_block`] takes the blank run following a row and can only take
    /// one block, and [`Self::append_row`] reads the file's trailing text off the
    /// last block alone.
    fn push_free(&mut self, text: &str) {
        if text.is_empty() {
            return;
        }
        match self.blocks.last_mut() {
            Some(last) if last.is_text() => last.text.push_str(text),
            _ => self.blocks.push(Block {
                kind: Kind::Text,
                text: text.to_string(),
            }),
        }
    }
}

impl DocModel {
    fn mint(&mut self) -> u32 {
        self.next_segment += 1;
        self.next_segment
    }

    fn segment(&mut self, id: u32) -> Option<&mut DocSegment> {
        self.body.iter_mut().find(|s| s.id == id)
    }

    /// Where a new chapter goes: at its rank in the writer's canonical order,
    /// not on the end. A file that gains a `## Reason` gets it above `## Changes`
    /// rather than below, which is what keeps two files with the same fields
    /// byte-identical however they were reached.
    fn insert_at(&self, kind: &SegmentKind, mapping: &DocumentMapping) -> usize {
        let rank = mapping.rank_of(kind);
        match &kind {
            // An entry goes after the last entry of its own container, so that
            // appending keeps a container's entries in one run.
            SegmentKind::Entry { container, fields, .. } => {
                let first = fields.first().cloned().unwrap_or_default();
                let mut at = None;
                for (i, s) in self.body.iter().enumerate() {
                    match &s.kind {
                        SegmentKind::Container { name } if name == container => at = Some(i + 1),
                        // Ascending by the entry's first heading field (§4.3),
                        // so an entry that arrives out of order still lands in
                        // the right place.
                        SegmentKind::Entry {
                            container: c,
                            fields: f,
                            ..
                        } if c == container => {
                            if f.first().is_some_and(|other| *other <= first) {
                                at = Some(i + 1);
                            }
                        }
                        _ => {}
                    }
                }
                at.unwrap_or(self.body.len())
            }
            _ => self
                .body
                .iter()
                .position(|s| mapping.rank_of(&s.kind) > rank)
                .unwrap_or(self.body.len()),
        }
    }
}

/// A row block's text never carries its own trailing newline: the separators
/// between blocks live in the free blocks around them, so that a row REPLACED in
/// place (the §5.1 move) occupies exactly the shape the one it replaced did.
/// Fact spans already exclude the newline; `print_fact` includes one.
fn row_text(printed: &str) -> String {
    printed.trim_end_matches('\n').to_string()
}

// ── Routing ────────────────────────────────────────────────────

/// Where a row belongs, decided by what the row carries.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Route {
    /// A primary row: its own file, in the directory its status names.
    Item { id: String, dir: String },
    /// A satellite row: the file of the item it names.
    Satellite { item: String, functor: String },
    /// Neither key: a store-level row, filed under its own functor.
    StoreLevel { functor: String },
}

/// Where a row's bytes live in the file that holds it.
///
/// FOUR SHAPES, NOT ONE, because under the document encoding a row is no longer
/// a stretch of text: an item's fact is the attributes chapter plus its prose
/// chapters, a `Tag` is one comma-separated element of an attributes field, and
/// a `Feedback` is one entry. Only a plain `.anthill` file still holds a row as a
/// block of source.
#[derive(Clone, Debug, Default)]
enum Slot {
    /// A fact declaration in a plain `.anthill` file.
    #[default]
    Block,
    /// The document's own item fact: the attributes chapter, plus the segment
    /// id of each prose chapter it fills.
    Item { chapters: Vec<u32> },
    /// One element of a satellite list.
    ListElement { id: u32 },
    /// One entry of a container.
    Entry { id: u32 },
}

struct RowInfo {
    path: PathBuf,
    route: Route,
    slot: Slot,
}

struct PendingRetract {
    rule: RuleId,
    path: PathBuf,
    route: Route,
    slot: Slot,
}

/// A row about to be written, in the shape its file holds it in.
enum PendingRow {
    /// Printed `.anthill` source, for a plain file.
    Plain(String),
    /// The item's own fact: its attributes lines, and the prose of each chapter
    /// the mapping gives it — absent chapters simply missing.
    Item {
        fields: Vec<AttrField>,
        chapters: Vec<(String, String)>,
    },
    ListElement {
        named: String,
        value: String,
    },
    Entry {
        kind: SegmentKind,
        body: String,
    },
}

struct PendingWrite {
    route: Route,
    row: PendingRow,
}

// ── The store ──────────────────────────────────────────────────

pub struct ItemPerFileStore {
    root: PathBuf,
    fields: ItemFields,
    /// The declared fact↔markdown mapping (WI-1120). `None` is the plain-`fact`
    /// layout WI-1118 migrated into; `Some` makes every ITEM file a document,
    /// `WI-NNN.anthill.md`. Store-level rows stay plain either way — they carry
    /// no prose, so there is nothing for a chapter to hold.
    mapping: Option<DocumentMapping>,
    /// The block model of every file this store was seeded with, plus every file
    /// it has since written. `BTreeMap` so a flush writes in a deterministic
    /// order and a test can read the layout back without sorting.
    files: BTreeMap<PathBuf, FileModel>,
    /// Where each addressable row lives, and what it routes as.
    rows: HashMap<RuleId, RowInfo>,
    /// The routing index for satellites, and the source of a relocation.
    by_item: HashMap<String, PathBuf>,
    /// The file each minted id's `<time>-<hash>` IDENTITY PREFIX was seen in
    /// (WI-1121 §6.6). Separate from `by_item` because it is keyed on a PREFIX:
    /// the slug after it is a rendering, and two colliding items differ in
    /// exactly that.
    by_identity: HashMap<String, PathBuf>,
    faults: Vec<LayoutFault>,
    pending_retracts: Vec<PendingRetract>,
    pending_writes: Vec<PendingWrite>,
}

impl ItemPerFileStore {
    pub fn new(root: PathBuf, fields: ItemFields) -> Self {
        Self {
            root,
            fields,
            mapping: None,
            files: BTreeMap::new(),
            rows: HashMap::new(),
            by_item: HashMap::new(),
            by_identity: HashMap::new(),
            faults: Vec::new(),
            pending_retracts: Vec::new(),
            pending_writes: Vec::new(),
        }
    }

    /// Read and write item files as DOCUMENTS under this mapping (WI-1120).
    ///
    /// The mapping arrives from the KB, declared in anthill beside the domain it
    /// describes, so this store never learns which fields a work item has — only
    /// the one concept "this field's text is the chapter named N".
    pub fn with_document_mapping(mut self, mapping: DocumentMapping) -> Self {
        self.mapping = Some(mapping);
        self
    }

    /// Whether item files are documents.
    pub fn writes_documents(&self) -> bool {
        self.mapping.is_some()
    }

    /// Claim these paths as files this store may overwrite, holding no rows.
    ///
    /// FOR A CONVERSION AND NOTHING ELSE. [`Self::refuse_unknown_occupant`]
    /// refuses to write a file this store never read, because the loader's one
    /// reason for withholding a file is that it could not parse it — and here
    /// that would be an item whose id is invisible while the allocator can hand
    /// it out again. A migration DID read these files; it just read them through
    /// another store, and it is rewriting them in place. This is where it says
    /// so, rather than the refusal being weakened for everyone.
    pub fn adopt(&mut self, paths: impl IntoIterator<Item = PathBuf>) {
        for path in paths {
            self.files.entry(path).or_default();
        }
    }

    /// The file-name suffix an ITEM file carries. `.anthill.md` under a document
    /// mapping: the trailing `.md` is what makes editors and GitHub render it,
    /// and the `.anthill` before it makes the file self-identifying, so a
    /// `README.md` in the same tree is not mistaken for one.
    ///
    /// A SUFFIX, NOT AN EXTENSION — `Path::extension()` answers `md` for
    /// `WI-690.anthill.md`, so every reader of these files tests `ends_with`.
    pub fn item_suffix(&self) -> &'static str {
        match self.mapping {
            Some(_) => ITEM_DOCUMENT_SUFFIX,
            None => ITEM_PLAIN_SUFFIX,
        }
    }

    /// Seed one already-loaded file: the host has read, parsed and loaded it, and
    /// hands over its text plus the `(RuleId, byte range)` of each fact in it.
    ///
    /// The ranges are consumed HERE, to cut the text into blocks; none is kept.
    /// This is the only way rows become addressable — there is no store-side bulk
    /// read, on the same rule as `IndexedFileStore::record_source` (WI-932).
    pub fn record_file(
        &mut self,
        kb: &KnowledgeBase,
        path: PathBuf,
        source: &str,
        rows: &[(RuleId, Span)],
    ) -> Result<(), PersistenceError> {
        let mut ordered: Vec<(RuleId, Span)> = rows.to_vec();
        ordered.sort_by_key(|(_, s)| s.start);

        let mut model = FileModel::default();
        let mut cursor = 0usize;
        for (rule, span) in &ordered {
            let (start, end) = (span.start as usize, span.end as usize);
            if start < cursor {
                return Err(PersistenceError::Io(format!(
                    "{}: fact ranges overlap at byte {start}",
                    path.display()
                )));
            }
            let free = slice(source, cursor, start, &path)?;
            model.push_free(free);
            model.blocks.push(Block {
                kind: Kind::Row(Some(*rule)),
                text: slice(source, start, end, &path)?.to_string(),
            });
            cursor = end;
        }
        model.push_free(slice(source, cursor, source.len(), &path)?);

        // Route every row first, so the file's own SHAPE is known before any fault
        // about it is recorded. A file holding several primary rows is not several
        // misplaced items — it is the shared-file layout, and reading it the other
        // way is what makes a "repair" rename the whole file to one item's path.
        let mut routed: Vec<(RuleId, Route)> = Vec::with_capacity(ordered.len());
        for (rule, _) in &ordered {
            // A row this store cannot place is REPORTED, not raised: `fsck` needs
            // the store built before it can say anything, so raising here would
            // take down the one command written to diagnose the problem. It is a
            // blocking fault, so nothing writes through the store meanwhile.
            match self.route_of(kb, kb.rule_head(*rule)) {
                Ok(route) => routed.push((*rule, route)),
                Err(e) => self.faults.push(LayoutFault::UnroutableRow {
                    path: path.clone(),
                    reason: e.to_string(),
                }),
            }
        }
        // DISTINCT ids: one file holding `WI-1` twice is a duplicate key, which is
        // a different fault with a different remedy. Only several DIFFERENT items
        // in one file is the shared-file layout.
        let mut primaries: Vec<String> = Vec::new();
        for (_, route) in &routed {
            if let Route::Item { id, .. } = route {
                if !primaries.contains(id) {
                    primaries.push(id.clone());
                }
            }
        }
        let shared = primaries.len() > 1;
        if shared {
            self.faults.push(LayoutFault::SharedFile {
                path: path.clone(),
                ids: primaries,
            });
        }

        for (rule, route) in routed {
            if let Route::Item { id, dir } = &route {
                // Suppressed under `SharedFile`: every row in a shared file
                // disagrees with its path, and reporting 1110 of them would bury
                // the one fault that says what is actually wrong.
                let expected = self.item_path(id, dir);
                if !shared && !same_path(&path, &expected) {
                    // An UNCONVERTED file — right directory, right id, plain
                    // encoding — is a different fault with a different remedy.
                    let unconverted = self.mapping.is_some()
                        && same_path(&path, &self.root.join(dir).join(format!("{id}{ITEM_PLAIN_SUFFIX}")));
                    self.faults.push(if unconverted {
                        LayoutFault::PlainItemFile {
                            path: path.clone(),
                            id: id.clone(),
                        }
                    } else {
                        LayoutFault::PathDisagreement {
                            found: path.clone(),
                            expected,
                            id: id.clone(),
                        }
                    });
                }
                // Any repeat of a key is a duplicate — including twice in ONE
                // file, which a path comparison alone reads as the same row seen
                // again. `Display` tells the two apart.
                match self.by_item.get(id) {
                    Some(first) => {
                        self.faults.push(LayoutFault::DuplicateId {
                            id: id.clone(),
                            first: first.clone(),
                            second: path.clone(),
                        });
                    }
                    None => {
                        // §6.6, and the check has to be HERE rather than in a
                        // merge driver or a git hook: two unsynced writers who
                        // mint the same digest produce different FILENAMES, so
                        // git merges them cleanly and the case that matters never
                        // reaches a hook at all. The tracker is the only detector.
                        if let Some(prefix) = identity_prefix(id) {
                            match self.by_identity.get(&prefix) {
                                Some(first) => self.faults.push(LayoutFault::IdCollision {
                                    prefix,
                                    first: first.clone(),
                                    second: path.clone(),
                                }),
                                None => {
                                    self.by_identity.insert(prefix, path.clone());
                                }
                            }
                        }
                        self.by_item.insert(id.clone(), path.clone());
                    }
                }
            }
            self.rows.insert(
                rule,
                RowInfo {
                    path: path.clone(),
                    route,
                    slot: Slot::Block,
                },
            );
        }

        self.files.insert(path, model);
        Ok(())
    }

    /// Seed one already-loaded DOCUMENT.
    ///
    /// `rows` are the file's facts in the order [`document::document_facts`]
    /// emitted them — the item, then its satellite-list elements, then its
    /// entries — which is the order they appear in the file. That order is the
    /// binding: a field chapter is found by NAME, but a container's entries are
    /// ORDERED SIBLINGS, because their heading fields are not injective (this
    /// tracker holds two `Feedback` rows with identical `at` AND `author`).
    ///
    /// NOTHING IS CHECKED AGAINST A PROJECTION HERE, and that is a fault class
    /// gone rather than an omission. Under the fenced-head encoding an entry
    /// heading was regenerated from a field of the head, so the two could
    /// disagree and a reordered file silently rebound prose onto the wrong row.
    /// The heading IS the data now — `at` and `author` are read out of it — so
    /// there is nothing left for it to disagree with.
    pub fn record_document(
        &mut self,
        kb: &KnowledgeBase,
        path: PathBuf,
        source: &str,
        rows: &[RuleId],
        doc: &Document,
    ) -> Result<(), PersistenceError> {
        let Some(mapping) = self.mapping.clone() else {
            return Err(PersistenceError::Io(format!(
                "{}: this store was not given a chapter mapping, so it cannot read a document",
                path.display()
            )));
        };

        let mut model = FileModel {
            blocks: Vec::new(),
            doc: Some(DocModel::default()),
        };
        let docmodel = model.doc.as_mut().expect("just built");
        // Every chapter and entry becomes a segment, in file order. The
        // ATTRIBUTES chapter deliberately does not: it is data, re-rendered from
        // the facts on every write, so keeping its bytes would be keeping a
        // second copy of what the KB already holds.
        let mut segment_of: Vec<Option<u32>> = Vec::with_capacity(doc.segments.len());
        for seg in &doc.segments {
            if matches!(seg.kind, SegmentKind::Attributes) {
                segment_of.push(None);
                continue;
            }
            let id = docmodel.mint();
            docmodel.body.push(DocSegment {
                id,
                kind: seg.kind.clone(),
                text: source[seg.span.clone()].to_string(),
            });
            segment_of.push(Some(id));
        }
        self.files.insert(path.clone(), model);

        for fault in &doc.faults {
            self.faults.push(LayoutFault::DocumentFault {
                path: path.clone(),
                blocking: fault.blocking,
                message: fault.message.clone(),
            });
        }

        // Which entry the next row binds to, keyed on (container, KIND) — the
        // same pair the segment filter below matches on. Keyed on the container
        // alone, two groups sharing one container (which the format exists to
        // make additive) would advance one cursor over two disjoint segment
        // sequences and bind prose to the wrong row.
        let mut entry_cursor: HashMap<(String, String), usize> = HashMap::new();
        for &rule in rows {
            let head = kb.rule_head(rule);
            let route = match self.route_of(kb, head) {
                Ok(route) => route,
                Err(e) => {
                    self.faults.push(LayoutFault::UnroutableRow {
                        path: path.clone(),
                        reason: e.to_string(),
                    });
                    continue;
                }
            };
            let Some(functor) = functor_short(kb, head) else {
                continue;
            };
            let slot = if let Some(spec) = mapping.list_for(&functor) {
                let id = self.model_for(&path).doc_mut().mint();
                let value = list_element_value(kb, head, spec, &mapping)?;
                self.model_for(&path).doc_mut().lists.push(ListElement {
                    id,
                    named: spec.named.clone(),
                    value,
                });
                Slot::ListElement { id }
            } else if let Some(group) = mapping.group_for(&functor) {
                let nth = entry_cursor
                    .entry((group.container.clone(), group.kind.clone()))
                    .or_insert(0);
                let found = doc
                    .segments
                    .iter()
                    .enumerate()
                    .filter(|(_, s)| {
                        matches!(&s.kind, SegmentKind::Entry { container, kind, .. }
                                 if *container == group.container && *kind == group.kind)
                    })
                    .nth(*nth)
                    .and_then(|(i, _)| segment_of[i]);
                *nth += 1;
                match found {
                    Some(id) => Slot::Entry { id },
                    None => {
                        return Err(PersistenceError::Io(format!(
                            "{}: more `{functor}` rows than `{}` entries of that kind — each \
                             row's prose is the entry at its own position",
                            path.display(),
                            group.container
                        )))
                    }
                }
            } else {
                // The item's own fact. Its attributes are re-derived, and each
                // prose chapter the mapping gives it binds BY NAME.
                let chapters: Vec<u32> = mapping
                    .chapters
                    .iter()
                    .filter(|c| c.functor == functor)
                    .filter_map(|c| {
                        doc.segments
                            .iter()
                            .enumerate()
                            .find(|(_, s)| {
                                matches!(&s.kind, SegmentKind::Field { name } if *name == c.named)
                            })
                            .and_then(|(i, _)| segment_of[i])
                    })
                    .collect();
                let fields = document::attribute_fields(kb, head, &functor, &mapping);
                self.model_for(&path).doc_mut().item = Some(fields);
                Slot::Item { chapters }
            };

            if let Route::Item { id, dir } = &route {
                let expected = self.item_path(id, dir);
                if !same_path(&path, &expected) {
                    self.faults.push(LayoutFault::PathDisagreement {
                        found: path.clone(),
                        expected,
                        id: id.clone(),
                    });
                }
                match self.by_item.get(id) {
                    Some(first) => self.faults.push(LayoutFault::DuplicateId {
                        id: id.clone(),
                        first: first.clone(),
                        second: path.clone(),
                    }),
                    None => {
                        if let Some(prefix) = identity_prefix(id) {
                            match self.by_identity.get(&prefix) {
                                Some(first) => self.faults.push(LayoutFault::IdCollision {
                                    prefix,
                                    first: first.clone(),
                                    second: path.clone(),
                                }),
                                None => {
                                    self.by_identity.insert(prefix, path.clone());
                                }
                            }
                        }
                        self.by_item.insert(id.clone(), path.clone());
                    }
                }
            }
            self.rows.insert(
                rule,
                RowInfo {
                    path: path.clone(),
                    route,
                    slot,
                },
            );
        }
        Ok(())
    }

    /// Every PRIMARY row, with the file it lives in — for a repair that has to
    /// rewrite a fact rather than move a file (WI-1121's `created` fill).
    ///
    /// The store hands out `(RuleId, path)` and nothing more: what is wrong with
    /// the row, and what to write instead, are the caller's business — this one
    /// does not know stage0's schema and must not start.
    pub fn primary_rows(&self) -> Vec<(RuleId, PathBuf)> {
        let mut out: Vec<(RuleId, PathBuf)> = self
            .rows
            .iter()
            .filter(|(_, info)| matches!(info.route, Route::Item { .. }))
            .map(|(rule, info)| (*rule, info.path.clone()))
            .collect();
        // Deterministic: a repair that walks these writes files, and a HashMap's
        // order would make its output differ run to run.
        out.sort_by(|a, b| a.1.cmp(&b.1));
        out
    }

    /// Every layout fault this store can see: the ones recorded per file while
    /// seeding, plus the cross-file satellite pass, which can only run once every
    /// file has been recorded (a satellite may be read before its item).
    pub fn layout_faults(&self) -> Vec<LayoutFault> {
        let mut out = self.faults.clone();
        for info in self.rows.values() {
            let Route::Satellite { item, functor } = &info.route else {
                continue;
            };
            match self.by_item.get(item) {
                None => out.push(LayoutFault::OrphanRow {
                    path: info.path.clone(),
                    functor: functor.clone(),
                    item: item.clone(),
                }),
                Some(home) if !same_path(home, &info.path) => {
                    out.push(LayoutFault::MisfiledRow {
                        found: info.path.clone(),
                        expected: home.clone(),
                        functor: functor.clone(),
                        item: item.clone(),
                    })
                }
                Some(_) => {}
            }
        }
        out.sort_by_key(|f| format!("{f}"));
        out
    }

    /// Move each misplaced file to the path its own fact names (`fsck --fix`).
    /// The FACT wins, per §4: the status field carries a payload no directory
    /// name can hold, so it is the truth and the directory is the projection.
    ///
    /// Returns the moves performed. Faults that are not a `PathDisagreement` are
    /// left alone and stay reported — a duplicate id is a genuine disagreement
    /// about which file is real, and this cannot know.
    pub fn repair_paths(&mut self) -> Result<Vec<(PathBuf, PathBuf)>, PersistenceError> {
        let faults = self.layout_faults();
        // THE WHOLE PLAN IS VALIDATED BEFORE ANY BYTE MOVES. This repair renames
        // files, so a refusal discovered halfway through leaves a half-repaired
        // tree that the error message describes badly and the user did not ask
        // for. Every reason to refuse is therefore checked up front.
        //
        // A duplicate id is a disagreement about WHICH file is the item, and a
        // misplaced file's destination may be the other copy. An unroutable row
        // means this store does not know where that file's item belongs at all.
        // A shared file is not misplaced items, it is a different layout.
        if let Some(blocker) = faults.iter().find(|f| {
            matches!(
                f,
                LayoutFault::DuplicateId { .. }
                    | LayoutFault::IdCollision { .. }
                    | LayoutFault::PlainItemFile { .. }
                    | LayoutFault::UnroutableRow { .. }
                    | LayoutFault::SharedFile { .. }
            )
        }) {
            return Err(PersistenceError::Io(format!(
                "{blocker}. Resolve that first: this repair moves whole files, and it will \
                 not move one onto another, split one, or guess where an unreadable row \
                 belongs"
            )));
        }

        let plan: Vec<(PathBuf, PathBuf)> = faults
            .into_iter()
            .filter_map(|f| match f {
                LayoutFault::PathDisagreement {
                    found, expected, ..
                } => Some((found, expected)),
                _ => None,
            })
            .collect();
        // A `found` twice would rename one file to two destinations; an `expected`
        // twice would land two files on one. Both are unreachable given the
        // refusals above — one file holds one primary row, and two rows keyed
        // alike are a `DuplicateId` — so this is a backstop, and it says so by
        // refusing rather than by picking an order.
        for (i, (found, expected)) in plan.iter().enumerate() {
            if let Some((other, _)) = plan[..i]
                .iter()
                .find(|(f, e)| same_path(f, found) || same_path(e, expected))
            {
                return Err(PersistenceError::Io(format!(
                    "the repair of {} collides with the repair of {}; refusing rather than \
                     choosing an order",
                    found.display(),
                    other.display()
                )));
            }
            if expected.exists() {
                return Err(PersistenceError::Io(format!(
                    "{} belongs at {}, which already exists; moving it would overwrite \
                     that file",
                    found.display(),
                    expected.display()
                )));
            }
        }

        let mut moves = Vec::new();
        for (found, expected) in plan {
            self.relocate(&found, &expected)?;
            write_file(&expected, &self.files[&expected].render(self.mapping.as_ref()))?;
            remove_file(&found)?;
            moves.push((found, expected));
        }
        self.faults
            .retain(|f| !matches!(f, LayoutFault::PathDisagreement { .. }));
        Ok(moves)
    }

    /// Re-render the LAYOUT of every document the reader reported a diagnostic
    /// about (`fsck --fix`).
    ///
    /// The two diagnostics §7 lists are both about a rendering rather than a
    /// value — a `FieldGroup` written apart (or two independent fields written
    /// together), and a heading value encoded when it did not have to be — so
    /// the repair is to write the canonical rendering of what is already held.
    /// The attributes chapter is derived from the facts, and an entry's heading
    /// is derived from its decoded fields, so this is a re-render and never a
    /// re-interpretation: prose bodies are carried through untouched.
    ///
    /// A BLOCKING fault stops it PER FILE, for the reason §7 gives: a file the
    /// reader had to drop something from must not be written back, because the
    /// rewrite would make the loss permanent. Per file and not per tree — one
    /// unreadable item must not silently cancel the repair of the other 1128,
    /// which is a fault report that reads as a repair.
    pub fn repair_layout(&mut self) -> Result<Vec<PathBuf>, PersistenceError> {
        let Some(mapping) = self.mapping.clone() else {
            return Ok(Vec::new());
        };
        let mut blocked: Vec<PathBuf> = Vec::new();
        let mut targets: Vec<PathBuf> = Vec::new();
        for fault in &self.faults {
            let LayoutFault::DocumentFault { path, blocking, .. } = fault else {
                continue;
            };
            let list = if *blocking { &mut blocked } else { &mut targets };
            if !list.contains(path) {
                list.push(path.clone());
            }
        }
        let mut repaired = Vec::new();
        for path in targets {
            if blocked.contains(&path) {
                continue;
            }
            let Some(model) = self.files.get_mut(&path) else {
                continue;
            };
            let Some(doc) = model.doc.as_mut() else {
                continue;
            };
            for seg in doc.body.iter_mut() {
                let SegmentKind::Entry { kind, fields, .. } = &seg.kind else {
                    continue;
                };
                let heading = document::entry_heading(kind, fields);
                let body = seg
                    .text
                    .split_once('\n')
                    .map(|(_, rest)| rest.trim().to_string())
                    .unwrap_or_default();
                seg.text = document::render_chapter(mapping.level + 1, &heading, &body);
            }
            let rendered = self.files[&path].render(Some(&mapping));
            write_file(&path, &rendered)?;
            repaired.push(path);
        }
        // Only the faults of files actually rewritten are cleared. Clearing them
        // all would make `fsck` answer "layout ok" for a file it skipped.
        self.faults.retain(|f| match f {
            LayoutFault::DocumentFault {
                path,
                blocking: false,
                ..
            } => !repaired.contains(path),
            _ => true,
        });
        Ok(repaired)
    }

    /// The directory a row with this status belongs in. DERIVED from the status
    /// functor's own short name, never looked up in a list: a new status variant
    /// cannot drift out of sync with the layout because there is nothing for it
    /// to drift from. `Open` → `open`, `ProposalRejected` → `proposal_rejected`.
    fn item_path(&self, id: &str, dir: &str) -> PathBuf {
        self.root
            .join(dir)
            .join(format!("{id}{}", self.item_suffix()))
    }

    fn route_of(&self, kb: &KnowledgeBase, term: TermId) -> Result<Route, PersistenceError> {
        let (functor, named) = match kb.get_term(term) {
            Term::Fn {
                functor,
                named_args,
                ..
            } => (*functor, Some(named_args)),
            Term::Ref(s) | Term::Ident(s) => (*s, None),
            other => {
                return Err(PersistenceError::Io(format!(
                    "this store routes a row by its fields, and {other:?} has none"
                )))
            }
        };
        let functor_name = kb.local_name_of(functor).to_string();
        if let Some(named) = named {
            if let Some(id) =
                get_named_arg(kb, named, &self.fields.id).and_then(|t| string_of(kb, t))
            {
                let path: Vec<String> =
                    self.fields.status.split('.').map(|s| s.to_string()).collect();
                let status = document::value_at(kb, term, &path).ok_or_else(|| {
                    PersistenceError::Io(format!(
                        "`{functor_name}` carries `{}` = \"{id}\" but no `{}` field, and the \
                         directory a row lives in IS its status",
                        self.fields.id, self.fields.status
                    ))
                })?;
                let dir = functor_short(kb, status).ok_or_else(|| {
                    PersistenceError::Io(format!(
                        "`{functor_name}(\"{id}\")` has a `{}` field that names no functor, so \
                         there is no directory to file it under",
                        self.fields.status
                    ))
                })?;
                // Both halves of the path come from the ROW, so both are checked
                // before they reach the filesystem. An id is user text, and a
                // status read off an UNRESOLVED symbol is a dotted qualified
                // name; either one carrying a separator would file the row
                // outside the tree — or outside the root — and the next load
                // would not find it there.
                check_segment(&id, &format!("the `{}` field", self.fields.id))?;
                let dir = snake_case(&dir);
                check_segment(&dir, &format!("the `{}` field's functor", self.fields.status))?;
                return Ok(Route::Item { id, dir });
            }

            if let Some(item) =
                get_named_arg(kb, named, &self.fields.reference).and_then(|t| string_of(kb, t))
            {
                return Ok(Route::Satellite {
                    item,
                    functor: functor_name,
                });
            }
        }

        // Neither key — or no fields at all: a store-level row, filed under its
        // own functor at the root.
        let functor = snake_case(&functor_name);
        check_segment(&functor, "this row's functor")?;
        Ok(Route::StoreLevel { functor })
    }

    /// The file a route names. Item and store-level routes are pure functions of
    /// the row; a satellite's answer is whatever file currently holds its item,
    /// which is why this is asked at FLUSH — after any relocation in the same
    /// flush has already moved it.
    fn path_of(&self, route: &Route) -> Result<PathBuf, PersistenceError> {
        match route {
            Route::Item { id, dir } => Ok(self.item_path(id, dir)),
            Route::Satellite { item, functor } => self.by_item.get(item).cloned().ok_or_else(|| {
                PersistenceError::Io(format!(
                    "a `{functor}` row names `{item}`, which this store holds no file for"
                ))
            }),
            Route::StoreLevel { functor } => Ok(self.root.join(format!("{functor}.anthill"))),
        }
    }

    /// Turn a row into the shape its file holds it in.
    ///
    /// A row under the document encoding is not a stretch of text: the item's
    /// fact becomes the attributes chapter plus its prose chapters, a
    /// satellite-list fact becomes one element of an attributes field, and a
    /// container's fact becomes one entry. `PendingRow::Plain` is every row in a
    /// project with no mapping, and the store-level format stamp in every project.
    ///
    /// THE PROSE IS DEMOTED HERE, not refused (§4.1). Text written somewhere else
    /// arrives with a hierarchy of its own; the whole hierarchy shifts down by the
    /// minimum that clears the levels this chapter reserves. It is idempotent, so
    /// a round trip is identity from the second write onward.
    fn render_row(
        &self,
        kb: &KnowledgeBase,
        fact: TermId,
        meta: Option<TermId>,
    ) -> Result<PendingRow, PersistenceError> {
        let Some(mapping) = &self.mapping else {
            return Ok(PendingRow::Plain(print::print_fact(kb, fact, meta)));
        };
        let Some(functor) = functor_short(kb, fact) else {
            return Ok(PendingRow::Plain(print::print_fact(kb, fact, meta)));
        };
        if let Some(spec) = mapping.list_for(&functor) {
            return Ok(PendingRow::ListElement {
                named: spec.named.clone(),
                value: list_element_value(kb, fact, spec, mapping)?,
            });
        }
        if let Some(group) = mapping.group_for(&functor) {
            let mut fields = Vec::with_capacity(group.heading.len());
            for name in &group.heading {
                fields.push(named_field(kb, fact, name).ok_or_else(|| {
                    PersistenceError::Io(format!(
                        "a `{functor}` row carries no string `{name}`, and that field is written \
                         in its entry's heading"
                    ))
                })?);
            }
            let kind = SegmentKind::Entry {
                container: group.container.clone(),
                kind: group.kind.clone(),
                fields,
            };
            let body = prose_field(kb, fact, &group.field)?.unwrap_or_default();
            let body = document::demote_prose(
                &body,
                document::deepest_reserved_for(&kind, mapping.level),
            )
            .map_err(|e| {
                PersistenceError::Io(format!("this row's `{}` cannot be written: {e}", group.field))
            })?;
            return Ok(PendingRow::Entry { kind, body });
        }
        if mapping.item_functor() != Some(functor.as_str()) {
            return Ok(PendingRow::Plain(print::print_fact(kb, fact, meta)));
        }

        let fields = document::attribute_fields(kb, fact, &functor, mapping);
        let mut chapters = Vec::new();
        for spec in mapping.chapters.iter().filter(|c| c.functor == functor) {
            // A chapter field may live inside a FLATTENED record, so it is
            // reached through its slot's path rather than as a named argument.
            let Some(slot) = mapping.slot_of(&functor, &spec.field) else {
                continue;
            };
            let held = document::value_at(kb, fact, &slot.path);
            // An ABSENT optional field writes no chapter at all — which is
            // exactly what the reader turns back into `none`, by leaving the
            // field off the fact it hands the loader (§3.5).
            let Some(value) = held.map(|v| prose_text(kb, v, &spec.field)).transpose()?.flatten()
            else {
                continue;
            };
            let kind = SegmentKind::Field {
                name: spec.named.clone(),
            };
            let value = document::demote_prose(
                &value,
                document::deepest_reserved_for(&kind, mapping.level),
            )
            .map_err(|e| {
                PersistenceError::Io(format!("this row's `{}` cannot be written: {e}", spec.field))
            })?;
            chapters.push((spec.named.clone(), value));
        }
        Ok(PendingRow::Item { fields, chapters })
    }

    /// Write one prose chapter into `path`'s document, replacing the segment
    /// `existing` names if its text differs and inserting a new one otherwise.
    ///
    /// RETURNS THE SEGMENT'S id, so the caller can re-bind the row. And it
    /// compares before it writes: a chapter whose text is unchanged is left
    /// exactly as its bytes were, which is what makes `claim` — a status change,
    /// nothing else — leave a 20,000-character description untouched.
    fn write_segment(
        &mut self,
        path: &Path,
        existing: Option<u32>,
        kind: &SegmentKind,
        body: &str,
    ) -> Result<u32, PersistenceError> {
        let mapping = self
            .mapping
            .clone()
            .ok_or_else(|| PersistenceError::Io("no chapter mapping".to_string()))?;
        let (level, heading) = match kind {
            SegmentKind::Field { name } => (mapping.level, name.clone()),
            SegmentKind::Entry {
                kind: word, fields, ..
            } => (
                mapping.level + 1,
                document::entry_heading(word, fields),
            ),
            other => {
                return Err(PersistenceError::Io(format!(
                    "{}: {other:?} is not a chapter this store writes",
                    path.display()
                )))
            }
        };
        let text = document::render_chapter(level, &heading, body);
        let model = self.model_for(path).doc_mut();
        if let Some(id) = existing {
            if let Some(seg) = model.segment(id) {
                seg.text = text;
                seg.kind = kind.clone();
                return Ok(id);
            }
        }
        // A new ENTRY creates its container heading if this is the first one, so
        // a document gains its `## Changes` section the moment it gains a change
        // and never before.
        let id = model.mint();
        if let SegmentKind::Entry { container, .. } = kind {
            let has_container = model
                .body
                .iter()
                .any(|s| matches!(&s.kind, SegmentKind::Container { name } if name == container));
            if !has_container {
                let cid = model.mint();
                let ckind = SegmentKind::Container {
                    name: container.clone(),
                };
                let at = model.insert_at(&ckind, &mapping);
                model.body.insert(
                    at,
                    DocSegment {
                        id: cid,
                        text: document::render_chapter(mapping.level, container, ""),
                        kind: ckind,
                    },
                );
            }
        }
        let at = model.insert_at(kind, &mapping);
        model.body.insert(
            at,
            DocSegment {
                id,
                kind: kind.clone(),
                text,
            },
        );
        Ok(id)
    }

    /// The model for `path`.
    fn model_for(&mut self, path: &Path) -> &mut FileModel {
        let documented = self.mapping.is_some()
            && path
                .file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.ends_with(ITEM_DOCUMENT_SUFFIX));
        let model = self.files.entry(path.to_path_buf()).or_default();
        if documented && model.doc.is_none() {
            model.doc = Some(DocModel::default());
        }
        model
    }

    /// Write a document row into its file, reusing the segments the row already
    /// owned so that unchanged prose comes through byte-identical.
    fn place_document_row(
        &mut self,
        path: &Path,
        previous: Option<&Slot>,
        row: &PendingRow,
    ) -> Result<Slot, PersistenceError> {
        match row {
            PendingRow::Item { fields, chapters } => {
                self.model_for(path).doc_mut().item = Some(fields.clone());
                let existing = match previous {
                    Some(Slot::Item { chapters }) => chapters.clone(),
                    _ => Vec::new(),
                };
                let mut ids = Vec::with_capacity(chapters.len());
                for (named, body) in chapters {
                    let kind = SegmentKind::Field {
                        name: named.clone(),
                    };
                    let at = existing.iter().copied().find(|id| {
                        self.files
                            .get(path)
                            .and_then(|m| m.doc.as_ref())
                            .and_then(|d| d.body.iter().find(|s| s.id == *id))
                            .is_some_and(|s| {
                                matches!(&s.kind, SegmentKind::Field { name } if name == named)
                            })
                    });
                    ids.push(self.write_segment(path, at, &kind, body)?);
                }
                // A chapter that is no longer written goes with the field it
                // held: an `update` that cleared a reason leaves no `## Reason`
                // behind, rather than prose bound to nothing.
                for id in existing {
                    if !ids.contains(&id) {
                        self.drop_segment(path, id);
                    }
                }
                Ok(Slot::Item { chapters: ids })
            }
            PendingRow::ListElement { named, value } => {
                let model = self.model_for(path).doc_mut();
                if let Some(Slot::ListElement { id }) = previous {
                    if let Some(e) = model.lists.iter_mut().find(|e| e.id == *id) {
                        e.named = named.clone();
                        e.value = value.clone();
                        return Ok(Slot::ListElement { id: *id });
                    }
                }
                let id = model.mint();
                model.lists.push(ListElement {
                    id,
                    named: named.clone(),
                    value: value.clone(),
                });
                Ok(Slot::ListElement { id })
            }
            PendingRow::Entry { kind, body } => {
                let existing = match previous {
                    Some(Slot::Entry { id }) => Some(*id),
                    _ => None,
                };
                Ok(Slot::Entry {
                    id: self.write_segment(path, existing, kind, body)?,
                })
            }
            PendingRow::Plain(_) => Err(PersistenceError::Io(format!(
                "{}: a plain fact row has no place in a document",
                path.display()
            ))),
        }
    }

    /// Drop everything a retracted row owned.
    fn drop_slot(&mut self, path: &Path, slot: &Slot) {
        match slot {
            Slot::Item { chapters } => {
                if let Some(doc) = self.files.get_mut(path).and_then(|m| m.doc.as_mut()) {
                    doc.item = None;
                }
                for id in chapters.clone() {
                    self.drop_segment(path, id);
                }
            }
            Slot::Entry { id } => self.drop_segment(path, *id),
            Slot::ListElement { id } => {
                if let Some(doc) = self.files.get_mut(path).and_then(|m| m.doc.as_mut()) {
                    doc.lists.retain(|e| e.id != *id);
                }
            }
            Slot::Block => {}
        }
    }

    /// Drop one prose segment. A `Container` left with no entries goes with the
    /// last of them: an empty `## Changes` heading is a section that describes
    /// nothing, and the reader would carry it forever.
    fn drop_segment(&mut self, path: &Path, id: u32) {
        let Some(model) = self.files.get_mut(path).and_then(|m| m.doc.as_mut()) else {
            return;
        };
        let Some(at) = model.body.iter().position(|s| s.id == id) else {
            return;
        };
        let container = match &model.body[at].kind {
            SegmentKind::Entry { container, .. } => Some(container.clone()),
            _ => None,
        };
        model.body.remove(at);
        if let Some(container) = container {
            let remaining = model.body.iter().any(
                |s| matches!(&s.kind, SegmentKind::Entry { container: c, .. } if *c == container),
            );
            if !remaining {
                model.body.retain(
                    |s| !matches!(&s.kind, SegmentKind::Container { name } if *name == container),
                );
            }
        }
    }

    /// Refuse to write a path that exists on disk but that this store never
    /// loaded.
    ///
    /// Everything this store writes it first read, so a file it has no model for
    /// is one the loader did not hand over — and the loader's one reason for
    /// that is a file it could not parse, which it WARNS about and skips. Under
    /// a shared-file store that skip only hides rows; here the skipped file is an
    /// item, so the id it holds is invisible, the allocator can hand it out
    /// again, and the write would land on top of it. The rows are recoverable
    /// while the file is still there, so this refuses while that is still true.
    ///
    /// `dropped` are the paths THIS flush has already emptied. Their bytes are
    /// still on disk — the removals run last, so that a crash leaves a duplicate
    /// rather than a hole — and a re-add landing on one of them is the flush
    /// finishing its own work, not a stranger's file.
    fn refuse_unknown_occupant(
        &self,
        path: &Path,
        dropped: &BTreeSet<PathBuf>,
    ) -> Result<(), PersistenceError> {
        if self.files.contains_key(path) || dropped.contains(path) || !path.exists() {
            return Ok(());
        }
        Err(PersistenceError::Io(format!(
            "{} already exists and this store never read it — most likely it did not \
             parse, and was warned about and skipped at startup. Writing here would \
             overwrite it; fix or move that file first",
            path.display()
        )))
    }

    /// Re-key one file's whole model, carrying every row in it — the item, its
    /// feedback, its tags, its mirror link. The unit of relocation is the FILE,
    /// not the row, and this is the line that says so.
    fn relocate(&mut self, from: &Path, to: &Path) -> Result<(), PersistenceError> {
        let model = self.files.remove(from).ok_or_else(|| {
            PersistenceError::Io(format!("no model for {} to relocate", from.display()))
        })?;
        self.files.insert(to.to_path_buf(), model);
        for info in self.rows.values_mut() {
            if same_path(&info.path, from) {
                info.path = to.to_path_buf();
            }
        }
        for home in self.by_item.values_mut() {
            if same_path(home, from) {
                *home = to.to_path_buf();
            }
        }
        // The identity index too (WI-1121): it is read only while seeding, so a
        // stale path here is unobservable today — which is exactly why it is
        // worth keeping true rather than leaving as a fact about the current
        // call order.
        for home in self.by_identity.values_mut() {
            if same_path(home, from) {
                *home = to.to_path_buf();
            }
        }
        Ok(())
    }
}

impl Store for ItemPerFileStore {
    fn persist(
        &mut self,
        kb: &KnowledgeBase,
        fact: TermId,
        _clause_kind: ClauseKind,
        _domain: Symbol,
        meta: Option<TermId>,
    ) -> Result<(), PersistenceError> {
        let route = self.route_of(kb, fact)?;
        let row = self.render_row(kb, fact, meta)?;
        self.pending_writes.push(PendingWrite { route, row });
        Ok(())
    }

    fn retract(&mut self, kb: &KnowledgeBase, id: RuleId) -> Result<bool, PersistenceError> {
        if !kb.is_rule_alive(id) {
            return Ok(false);
        }
        // Read the row's identity NOW: the caller retracts it from the KB
        // immediately after, and this store's flush runs later.
        let info = self.rows.get(&id).ok_or_else(|| {
            PersistenceError::Io(format!(
                "retract: this store holds no file for {}; only a row it loaded or wrote \
                 in an earlier flush can be addressed",
                print::TermPrinter::new(kb).print_term(kb.rule_head(id))
            ))
        })?;
        self.pending_retracts.push(PendingRetract {
            rule: id,
            path: info.path.clone(),
            route: info.route.clone(),
            slot: info.slot.clone(),
        });
        Ok(true)
    }

    fn update(
        &mut self,
        kb: &KnowledgeBase,
        id: RuleId,
        new: TermId,
        clause_kind: ClauseKind,
        domain: Symbol,
        meta: Option<TermId>,
    ) -> Result<bool, PersistenceError> {
        if !self.retract(kb, id)? {
            return Ok(false);
        }
        // Buffered, both of them: it is the single flush below that recognizes
        // the pair as one move (§5.1), so composing them here is the mechanism,
        // not a caller-visible retract-then-persist.
        self.persist(kb, new, clause_kind, domain, meta)?;
        Ok(true)
    }

    fn flush(&mut self, _kb: &KnowledgeBase) -> Result<(), PersistenceError> {
        let retracts = std::mem::take(&mut self.pending_retracts);
        let writes = std::mem::take(&mut self.pending_writes);
        if retracts.is_empty() && writes.is_empty() {
            return Ok(());
        }

        let mut dirty: BTreeSet<PathBuf> = BTreeSet::new();
        let mut deleted: BTreeSet<PathBuf> = BTreeSet::new();
        // Where each file relocated to during THIS flush. A retract captures its
        // row's path when it is buffered, so a satellite retracted in the same
        // flush that moves its item still names the old path — and would find no
        // model there.
        let mut moved: HashMap<PathBuf, PathBuf> = HashMap::new();

        // A retract is pairable by the primary key it carries. Only a primary
        // row has one — a satellite retract is never a move, it is a row leaving
        // a file that stays where it is.
        let mut pairable: HashMap<String, usize> = HashMap::new();
        for (i, r) in retracts.iter().enumerate() {
            if let Route::Item { id, .. } = &r.route {
                pairable.insert(id.clone(), i);
            }
        }
        let mut paired = vec![false; retracts.len()];

        // Pass 1 — the relocation rule. A persist whose primary key a retract in
        // this same flush also names is that row MOVING: rewrite its block where
        // it sits, then carry the whole file to the new path.
        let mut unpaired_writes: Vec<PendingWrite> = Vec::new();
        for write in writes {
            let Route::Item { id, .. } = &write.route else {
                unpaired_writes.push(write);
                continue;
            };
            let Some(&i) = pairable.get(id) else {
                unpaired_writes.push(write);
                continue;
            };
            if paired[i] {
                return Err(PersistenceError::Io(format!(
                    "two rows keyed `{id}` were persisted against one retract in a single \
                     flush; a primary key names one row"
                )));
            }
            paired[i] = true;

            let old_path = retracts[i].path.clone();
            let new_path = self.path_of(&write.route)?;
            // THE ROW IS REWRITTEN BEFORE THE FILE MOVES, while the model is
            // still keyed at the old path. Its chapters are rewritten only where
            // the text actually changed: `claim` rewrites the attributes and
            // renames the file, and the description must come through
            // byte-identical — that is the invariant that keeps hand-added prose
            // alive.
            match &write.row {
                PendingRow::Plain(text) => {
                    let model = self.files.get_mut(&old_path).ok_or_else(|| {
                        PersistenceError::Io(format!("no model for {}", old_path.display()))
                    })?;
                    let at = model.position_of(retracts[i].rule).ok_or_else(|| {
                        PersistenceError::Io(format!(
                            "{}: the row for `{id}` is not in this file's model",
                            old_path.display()
                        ))
                    })?;
                    model.blocks[at] = Block {
                        kind: Kind::Row(None),
                        text: row_text(text),
                    };
                }
                row => {
                    self.place_document_row(&old_path, Some(&retracts[i].slot), row)?;
                }
            }
            self.rows.remove(&retracts[i].rule);
            if !same_path(&old_path, &new_path) {
                self.refuse_unknown_occupant(&new_path, &deleted)?;
                self.relocate(&old_path, &new_path)?;
                moved.insert(old_path.clone(), new_path.clone());
                deleted.insert(old_path.clone());
                dirty.remove(&old_path);
            }
            self.by_item.insert(id.clone(), new_path.clone());
            dirty.insert(new_path);
        }

        // Pass 2 — retracts with no partner: the row simply leaves. A file with
        // no rows left is removed; one with satellites left standing is KEPT and
        // reported by `layout_faults`, because those rows are still live facts
        // and dropping them here would lose data no one asked to lose.
        for (i, r) in retracts.iter().enumerate() {
            if paired[i] {
                continue;
            }
            let path = moved.get(&r.path).unwrap_or(&r.path).clone();
            let missing =
                || PersistenceError::Io(format!("no model for {}", path.display()));
            let model = self.files.get_mut(&path).ok_or_else(missing)?;
            if let Some(at) = model.position_of(r.rule) {
                model.drop_block(at);
            }
            // The row's prose leaves with it — an orphan chapter would be text
            // bound to no fact, and the next rewrite would carry it forever.
            self.drop_slot(&path, &r.slot);
            self.rows.remove(&r.rule);
            if let Route::Item { id, .. } = &r.route {
                self.by_item.remove(id);
            }
            if self.files.get(&path).ok_or_else(missing)?.holds_rows() {
                dirty.insert(path);
            } else {
                deleted.insert(path.clone());
                dirty.remove(&path);
                self.files.remove(&path);
            }
        }

        // Pass 3 — plain appends. Satellites resolve here, so an item persisted
        // in this same flush is already at its final path.
        //
        // PRIMARIES ARE PLACED BEFORE ANY SATELLITE IS ASKED WHERE IT GOES. A
        // satellite's path is whatever file holds its item, so without this the
        // answer depends on the order the caller happened to buffer in: a
        // `Feedback` persisted ahead of its own `WorkItem` in one flush failed
        // with "this store holds no file for X" — a property of the sequence,
        // not of the rows. A migration (WI-1118) replays a whole tracker in one
        // flush and has no business sorting its input by a routing rule that
        // lives in here.
        //
        // A STABLE PARTITION, not a sort: within each group the caller's order
        // is the order rows land in their file, so an item file reads
        // item-then-satellites (§4) and two feedback rows keep their sequence.
        // `Route::StoreLevel` rides with the satellites — its path depends on
        // nothing this flush does.
        let (primaries, rest): (Vec<PendingWrite>, Vec<PendingWrite>) = unpaired_writes
            .into_iter()
            .partition(|w| matches!(w.route, Route::Item { .. }));
        for write in primaries.into_iter().chain(rest) {
            if let Route::Item { id, dir } = &write.route {
                let path = self.item_path(id, dir);
                match self.by_item.get(id) {
                    Some(home) if !same_path(home, &path) => {
                        return Err(PersistenceError::Io(format!(
                            "persist of `{id}` at {} — this store already holds it at {}; a \
                             primary key has one file",
                            path.display(),
                            home.display()
                        )));
                    }
                    _ => {}
                }
                self.by_item.insert(id.clone(), path);
            }
            let path = self.path_of(&write.route)?;
            self.refuse_unknown_occupant(&path, &deleted)?;
            match &write.row {
                PendingRow::Plain(text) => self.model_for(&path).append_row(text.clone()),
                row => {
                    self.place_document_row(&path, None, row)?;
                }
            }
            deleted.remove(&path);
            dirty.insert(path);
        }

        for path in &dirty {
            let model = self
                .files
                .get(path)
                .ok_or_else(|| PersistenceError::Io(format!("no model for {}", path.display())))?;
            write_file(path, &model.render(self.mapping.as_ref()))?;
        }
        // Removals last: a crash before this point leaves the row in two files,
        // which the next load names as a `DuplicateId` — loud, and repairable.
        // The other order loses the row outright.
        for path in &deleted {
            remove_file(path)?;
        }
        Ok(())
    }
}

// ── Helpers ────────────────────────────────────────────────────

fn slice<'a>(
    source: &'a str,
    start: usize,
    end: usize,
    path: &Path,
) -> Result<&'a str, PersistenceError> {
    source.get(start..end).ok_or_else(|| {
        PersistenceError::Io(format!(
            "{}: byte range {start}..{end} is not a character boundary of this file",
            path.display()
        ))
    })
}

fn string_of(kb: &KnowledgeBase, t: TermId) -> Option<String> {
    match kb.get_term(t) {
        Term::Const(Literal::String(s)) => Some(s.clone()),
        _ => None,
    }
}

/// A term's string-valued named argument (WI-1120): what names an entry chapter,
/// and what its decoration is regenerated from.
fn named_field(kb: &KnowledgeBase, term: TermId, field: &str) -> Option<String> {
    let Term::Fn { named_args, .. } = kb.get_term(term) else {
        return None;
    };
    get_named_arg(kb, named_args, field).and_then(|t| string_of(kb, t))
}

/// The prose a chapter carries, peeled out of the field it left the head from.
///
/// BOTH SPELLINGS, and both are legal here: `Feedback.content` is a bare
/// `String` while `WorkItem.description` is `Option[T = String]`, so a rule
/// admitting only bare strings would exclude the very field this encoding exists
/// for. `None` is the ABSENT case — an `Option` written `none()`, or a field the
/// row does not carry — and it writes no chapter at all.
///
/// Anything else is a REFUSAL rather than a skip: a chapter-bearing field
/// holding a term this cannot render as text would be silently dropped from the
/// head by the split and then written nowhere.
fn prose_field(
    kb: &KnowledgeBase,
    term: TermId,
    field: &str,
) -> Result<Option<String>, PersistenceError> {
    let Term::Fn { named_args, .. } = kb.get_term(term) else {
        return Ok(None);
    };
    let Some(value) = get_named_arg(kb, named_args, field) else {
        return Ok(None);
    };
    prose_text(kb, value, field)
}

/// The same, given the value already reached — a chapter field inside a
/// flattened record is found by PATH, not as a named argument of the fact.
fn prose_text(
    kb: &KnowledgeBase,
    value: TermId,
    field: &str,
) -> Result<Option<String>, PersistenceError> {
    if let Some(s) = string_of(kb, value) {
        return Ok(Some(s));
    }
    match kb.get_term(value) {
        Term::Ref(s) | Term::Ident(s) if kb.local_name_of(*s) == "none" => Ok(None),
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } if kb.local_name_of(*functor) == "none"
            && pos_args.is_empty()
            && named_args.is_empty() =>
        {
            Ok(None)
        }
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } if kb.local_name_of(*functor) == "some" => {
            let inner = get_named_arg(kb, named_args, "value")
                .or_else(|| pos_args.first().copied())
                .ok_or_else(|| {
                    PersistenceError::Io(format!("`{field}` is a `some(…)` carrying no value"))
                })?;
            string_of(kb, inner).map(Some).ok_or_else(|| {
                PersistenceError::Io(format!(
                    "`{field}` is a chapter field, so it holds text — this `some(…)` holds {}",
                    print::TermPrinter::new(kb).print_term(inner)
                ))
            })
        }
        _ => Err(PersistenceError::Io(format!(
            "`{field}` is a chapter field, so it holds text — this row holds {}",
            print::TermPrinter::new(kb).print_term(value)
        ))),
    }
}

/// The value one satellite-list element is written as: its `field`, spelled by
/// the declared type, or the backticked term when it has no data spelling.
///
/// A value carrying `, ` would be indistinguishable from two elements, so it has
/// no data spelling either and takes the term form — which is exactly what
/// [`document::spell_write`] answers `None` for.
fn list_element_value(
    kb: &KnowledgeBase,
    fact: TermId,
    spec: &document::SatelliteListSpec,
    mapping: &DocumentMapping,
) -> Result<String, PersistenceError> {
    let Term::Fn { named_args, .. } = kb.get_term(fact) else {
        return Err(PersistenceError::Io(format!(
            "a `{}` row has no fields, so it cannot be written as a list element",
            spec.functor
        )));
    };
    let value = get_named_arg(kb, named_args, &spec.field).ok_or_else(|| {
        PersistenceError::Io(format!(
            "a `{}` row carries no `{}`, and that field IS its written value",
            spec.functor, spec.field
        ))
    })?;
    let ty = mapping
        .schema
        .field_type(&spec.functor, &spec.field)
        .ok_or_else(|| {
            PersistenceError::Io(format!(
                "`{}.{}` is not declared, so its value has no spelling",
                spec.functor, spec.field
            ))
        })?;
    // BOTH SPELLINGS MUST BE COMMA-FREE, and the fallback is the one that is
    // easy to forget. A satellite list is written as ONE attributes field with
    // its elements separated by `, `, so an element carrying that separator has
    // no spelling at all here — not even the backticked term, which the reader
    // splits before it ever looks for a backtick. Guarding only the data
    // spelling produced a file this store's own reader refuses.
    //
    // REFUSED, rather than encoded: §3.2's "the writer never has to refuse a
    // value" is about a field of the item's own fact, where the term spelling is
    // total. This position has no total escape, so the honest answer is to fail
    // before anything is written.
    let text = document::spell_write(kb, value, &ty, mapping)
        .unwrap_or_else(|| document::term_value(kb, value));
    if text.contains(", ") {
        return Err(PersistenceError::Io(format!(
            "a `{}` row's `{}` is {text}, which carries the `, ` that separates the elements \
             of `{}` — one element would read back as two",
            spec.functor, spec.field, spec.named
        )));
    }
    Ok(text)
}

/// The `WI-<YYYYMMDD>-<digest>` part of a MINTED id — everything up to the slug,
/// which is the only part that carries identity (§6.5).
///
/// `None` for a grandfathered `WI-NNN` or anything hand-written: those cannot
/// collide by this mechanism, because nothing derives them.
fn identity_prefix(id: &str) -> Option<String> {
    let body = id.strip_prefix("WI-")?;
    let mut parts = body.splitn(3, '-');
    let day = parts.next()?;
    if day.len() != 8 || !day.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    let digest = parts.next()?;
    if digest.is_empty() {
        return None;
    }
    Some(format!("WI-{day}-{digest}"))
}

fn functor_short(kb: &KnowledgeBase, t: TermId) -> Option<String> {
    match kb.get_term(t) {
        Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => {
            Some(kb.local_name_of(*functor).to_string())
        }
        _ => None,
    }
}

/// Refuse a value that is about to become ONE path segment but is not one.
///
/// Every part of a row's path is read out of the row: the id is user text, and
/// the directory is a functor's name, which is the fully-qualified dotted string
/// when the symbol did not resolve. A separator in either would file the row
/// somewhere the next load does not look — or, with `..`, outside the root
/// entirely. This is the store's edge, so it refuses here rather than trusting
/// what it was handed.
fn check_segment(value: &str, what: &str) -> Result<(), PersistenceError> {
    let bad = value.is_empty()
        || value == "."
        || value == ".."
        || value
            .chars()
            .any(|c| c == '/' || c == '\\' || c == std::path::MAIN_SEPARATOR || c == '\0');
    if bad {
        return Err(PersistenceError::Io(format!(
            "{what} is {value:?}, and it names one directory or one file in this store's \
             tree — which is not a name either of those can have"
        )));
    }
    Ok(())
}

/// Compare two paths by their components, so a `./x` the host built and an `x`
/// this store computed are the same file. Neither side canonicalizes — the
/// expected path names a file that need not exist yet.
fn same_path(a: &Path, b: &Path) -> bool {
    a.components().eq(b.components())
}

/// The directory-name policy of THIS store: a functor's short name, lowercased
/// with word breaks marked. Deliberately its own function rather than a shared
/// one with `codegen::rust`'s identically-named helper — that one answers "what
/// is this called in Rust", which is free to change with Rust's conventions,
/// while this one names a directory on a user's disk and must not.
fn snake_case(name: &str) -> String {
    let mut out = String::with_capacity(name.len() + 4);
    let mut prev_lower_or_digit = false;
    for c in name.chars() {
        if c == '-' || c == '_' {
            if !out.is_empty() && !out.ends_with('_') {
                out.push('_');
            }
            prev_lower_or_digit = false;
            continue;
        }
        if c.is_uppercase() {
            if prev_lower_or_digit {
                out.push('_');
            }
            out.extend(c.to_lowercase());
            prev_lower_or_digit = false;
        } else {
            out.push(c);
            prev_lower_or_digit = true;
        }
    }
    out
}

fn write_file(path: &Path, content: &str) -> Result<(), PersistenceError> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| {
            PersistenceError::Io(format!(
                "failed to create directory {}: {e}",
                parent.display()
            ))
        })?;
    }
    // APPENDED, not `with_extension` (WI-1120): an item document is
    // `WI-N.anthill.md`, whose `extension()` is `md`, so replacing the extension
    // produced `WI-N.anthill.anthill.tmp` — a name that says nothing true about
    // the file it is a draft of. Appending keeps the temp beside its target and
    // out of every reader's suffix test.
    let temp_path = path.with_file_name(format!(
        "{}.tmp",
        path.file_name().and_then(|n| n.to_str()).unwrap_or("row")
    ));
    fs::write(&temp_path, content).map_err(|e| {
        PersistenceError::Io(format!(
            "failed to write temp file {}: {e}",
            temp_path.display()
        ))
    })?;
    fs::rename(&temp_path, path).map_err(|e| {
        PersistenceError::Io(format!(
            "failed to rename {} → {}: {e}",
            temp_path.display(),
            path.display()
        ))
    })
}

fn remove_file(path: &Path) -> Result<(), PersistenceError> {
    match fs::remove_file(path) {
        Ok(()) => Ok(()),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(PersistenceError::Io(format!(
            "failed to remove {}: {e}",
            path.display()
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn snake_case_marks_word_breaks_without_a_list_of_statuses() {
        assert_eq!(snake_case("Open"), "open");
        assert_eq!(snake_case("PreOpened"), "pre_opened");
        assert_eq!(snake_case("ProposalRejected"), "proposal_rejected");
        assert_eq!(snake_case("Claimed"), "claimed");
    }
}
