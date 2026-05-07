//! IndexedFileStore — `FileStore` augmented with a per-rule source map
//! so retract can drop the exact byte range a fact occupies on disk
//! without reconstructing it from a content fingerprint.
//!
//! The underlying `FileStore` keeps doing the actual file I/O — pull,
//! persist's append-to-pending, and flush's atomic rewrite all stay in
//! the inner store. `IndexedFileStore` adds:
//!
//! - `pull_with_source(&mut KnowledgeBase)` — load each `.anthill` file
//!   in the root, record `(rule_id → (path, span))` for every fact;
//! - `Store::retract` — consult the source map; if the rule was loaded
//!   from a file, buffer a span-based retract; otherwise fall back to
//!   the inner store's content-keyed retract for runtime-asserted
//!   facts.
//! - `flush` — apply span retracts (drop byte ranges directly), then
//!   delegate the rest to the inner store.
//!
//! Rationale: the legacy content-keyed retract path produces a
//! loader-normalized canonical (logical vars in unspecified named-args,
//! list-literal desugaring, constructor-arg expansion) that never
//! string-equals the parse-side print of the same fact in source. For
//! any entity with optional named-args (e.g. `WorkItem`) the retract
//! silently no-ops on disk. Span-based retract sidesteps the canonical
//! comparison entirely. (WI-187.)

use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;

use crate::kb::{KnowledgeBase, RuleId};
use crate::kb::term::TermId;
use crate::span::Span;

use super::file_store::{FileConvention, FileStore};
use super::{BulkStore, IndexedStore, PersistenceError, Store};

pub struct IndexedFileStore {
    inner: FileStore,
    /// Per-rule source location: which file the rule was loaded from
    /// and the byte range its `fact …(…)` block occupies. Populated by
    /// `pull_with_source`; consulted by `retract`.
    source_map: HashMap<RuleId, (PathBuf, Span)>,
    /// Span retracts queued for the next flush. `(file, byte_range)`
    /// tuples — flush drops the range from the file.
    pending_span_retracts: Vec<(PathBuf, Span)>,
}

impl IndexedFileStore {
    pub fn new(root: PathBuf, convention: FileConvention) -> Self {
        Self {
            inner: FileStore::new(root, convention),
            source_map: HashMap::new(),
            pending_span_retracts: Vec::new(),
        }
    }

    /// Record source location for a single fact. Callers that drove
    /// their own load path (e.g. the bundle's main.rs which loads
    /// stdlib + bundle + project together via `load_all_per_file`)
    /// populate the source map fact-by-fact without re-parsing.
    pub fn record_source(&mut self, rule_id: RuleId, path: PathBuf, span: Span) {
        self.source_map.insert(rule_id, (path, span));
    }
}

impl IndexedStore for IndexedFileStore {
    type Location = (PathBuf, Span);

    fn location_of(&self, id: RuleId) -> Option<Self::Location> {
        self.source_map.get(&id).cloned()
    }
}

impl Store for IndexedFileStore {
    fn persist(
        &mut self,
        kb: &KnowledgeBase,
        fact: TermId,
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> Result<(), PersistenceError> {
        self.inner.persist(kb, fact, sort, domain, meta)
    }

    fn retract(&mut self, kb: &KnowledgeBase, id: RuleId) -> Result<bool, PersistenceError> {
        if !kb.is_rule_alive(id) {
            return Ok(false);
        }
        match self.source_map.remove(&id) {
            Some((path, span)) => {
                self.pending_span_retracts.push((path, span));
                Ok(true)
            }
            // Runtime-asserted fact (no source). Fall through to the
            // inner store's content-keyed path so existing behaviour
            // is preserved for non-source-loaded retracts.
            None => self.inner.retract(kb, id),
        }
    }

    fn flush(&mut self, kb: &KnowledgeBase) -> Result<(), PersistenceError> {
        // Span retracts first: drop byte ranges from each file.
        // Group by path so we can apply all retracts to a file in one
        // rewrite, then sort within each file by descending start so
        // earlier drops don't shift the offsets of later ones.
        if !self.pending_span_retracts.is_empty() {
            let mut by_path: HashMap<PathBuf, Vec<Span>> = HashMap::new();
            for (path, span) in self.pending_span_retracts.drain(..) {
                by_path.entry(path).or_default().push(span);
            }
            for (path, mut spans) in by_path {
                let source = fs::read_to_string(&path).map_err(|e| {
                    PersistenceError::Io(format!("read {}: {e}", path.display()))
                })?;
                spans.sort_by(|a, b| b.start.cmp(&a.start));
                let mut content = source;
                for span in spans {
                    drop_range(&mut content, span.start as usize, span.end as usize);
                }
                let temp_path = path.with_extension("anthill.tmp");
                fs::write(&temp_path, &content).map_err(|e| {
                    PersistenceError::Io(format!(
                        "write {}: {e}", temp_path.display()
                    ))
                })?;
                fs::rename(&temp_path, &path).map_err(|e| {
                    PersistenceError::Io(format!(
                        "rename {} → {}: {e}",
                        temp_path.display(), path.display(),
                    ))
                })?;
            }
        }
        // Inner flush handles persisted writes and any content-keyed
        // retracts that fell through (runtime-asserted facts).
        self.inner.flush(kb)
    }
}

impl BulkStore for IndexedFileStore {
    fn pull(&self) -> Result<Vec<crate::parse::ir::ParsedFile>, PersistenceError> {
        self.inner.pull()
    }
}

fn drop_range(content: &mut String, start: usize, end: usize) {
    let drop_end = super::extend_drop_end(content.as_bytes(), end);
    content.replace_range(start..drop_end, "");
}
