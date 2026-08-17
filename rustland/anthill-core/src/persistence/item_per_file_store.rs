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

use super::print;
use super::{PersistenceError, Store};

// ── Configuration ──────────────────────────────────────────────

/// The three field names this store routes on. Named rather than positional:
/// three `String`s in a row is three chances to swap two of them, and the
/// symptom of a swap is rows filed under a directory named after an id.
#[derive(Clone, Debug)]
pub struct ItemFields {
    /// The field whose functor names the directory (`status`).
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
    /// A satellite row naming an item no file holds. Not blocking — deleting an
    /// item leaves its append-only feedback behind by design (feedback is
    /// `monotone`, so it cannot be retracted), and that is a state to REPORT,
    /// not one to refuse every later command over.
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
            | LayoutFault::UnroutableRow { .. }
            | LayoutFault::SharedFile { .. } => true,
            LayoutFault::OrphanRow { .. } | LayoutFault::MisfiledRow { .. } => false,
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

#[derive(Default)]
struct FileModel {
    blocks: Vec<Block>,
}

impl FileModel {
    fn render(&self) -> String {
        let mut out = String::new();
        for b in &self.blocks {
            out.push_str(&b.text);
        }
        out
    }

    fn position_of(&self, rule: RuleId) -> Option<usize> {
        self.blocks.iter().position(|b| b.rule() == Some(rule))
    }

    /// Whether this file still declares anything. Asked of ROWS, not of
    /// addressable rows: a file whose only row was just rewritten in place still
    /// holds that row, and deleting it because the store no longer has a name for
    /// it would delete the item the rewrite was moving.
    fn holds_rows(&self) -> bool {
        self.blocks.iter().any(|b| !b.is_text())
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

struct RowInfo {
    path: PathBuf,
    route: Route,
}

struct PendingRetract {
    rule: RuleId,
    path: PathBuf,
    route: Route,
}

struct PendingWrite {
    route: Route,
    text: String,
}

// ── The store ──────────────────────────────────────────────────

pub struct ItemPerFileStore {
    root: PathBuf,
    fields: ItemFields,
    /// The block model of every file this store was seeded with, plus every file
    /// it has since written. `BTreeMap` so a flush writes in a deterministic
    /// order and a test can read the layout back without sorting.
    files: BTreeMap<PathBuf, FileModel>,
    /// Where each addressable row lives, and what it routes as.
    rows: HashMap<RuleId, RowInfo>,
    /// The routing index for satellites, and the source of a relocation.
    by_item: HashMap<String, PathBuf>,
    faults: Vec<LayoutFault>,
    pending_retracts: Vec<PendingRetract>,
    pending_writes: Vec<PendingWrite>,
}

impl ItemPerFileStore {
    pub fn new(root: PathBuf, fields: ItemFields) -> Self {
        Self {
            root,
            fields,
            files: BTreeMap::new(),
            rows: HashMap::new(),
            by_item: HashMap::new(),
            faults: Vec::new(),
            pending_retracts: Vec::new(),
            pending_writes: Vec::new(),
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
                    self.faults.push(LayoutFault::PathDisagreement {
                        found: path.clone(),
                        expected,
                        id: id.clone(),
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
                        self.by_item.insert(id.clone(), path.clone());
                    }
                }
            }
            self.rows.insert(
                rule,
                RowInfo {
                    path: path.clone(),
                    route,
                },
            );
        }

        self.files.insert(path, model);
        Ok(())
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
            write_file(&expected, &self.files[&expected].render())?;
            remove_file(&found)?;
            moves.push((found, expected));
        }
        self.faults
            .retain(|f| !matches!(f, LayoutFault::PathDisagreement { .. }));
        Ok(moves)
    }

    /// The directory a row with this status belongs in. DERIVED from the status
    /// functor's own short name, never looked up in a list: a new status variant
    /// cannot drift out of sync with the layout because there is nothing for it
    /// to drift from. `Open` → `open`, `ProposalRejected` → `proposal_rejected`.
    fn item_path(&self, id: &str, dir: &str) -> PathBuf {
        self.root.join(dir).join(format!("{id}.anthill"))
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
                let status = get_named_arg(kb, named, &self.fields.status).ok_or_else(|| {
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
        self.pending_writes.push(PendingWrite {
            route,
            text: print::print_fact(kb, fact, meta),
        });
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
                text: row_text(&write.text),
            };
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
            let model = self
                .files
                .get_mut(&path)
                .ok_or_else(|| PersistenceError::Io(format!("no model for {}", path.display())))?;
            if let Some(at) = model.position_of(r.rule) {
                model.drop_block(at);
            }
            self.rows.remove(&r.rule);
            if let Route::Item { id, .. } = &r.route {
                self.by_item.remove(id);
            }
            if model.holds_rows() {
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
            self.files
                .entry(path.clone())
                .or_default()
                .append_row(write.text);
            deleted.remove(&path);
            dirty.insert(path);
        }

        for path in &dirty {
            let model = self
                .files
                .get(path)
                .ok_or_else(|| PersistenceError::Io(format!("no model for {}", path.display())))?;
            write_file(path, &model.render())?;
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
    let temp_path = path.with_extension("anthill.tmp");
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
