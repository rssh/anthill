/// Persistence — traits and backends for storing/loading KB facts.
///
/// The `Store` trait provides persist/retract/flush for individual facts.
/// `BulkStore` extends it with `pull()` to load entire file sets.
///
/// `FileStore` is the filesystem backend: reads/writes `.anthill` files.

pub mod print;
pub mod file_store;
pub mod indexed_file_store;
pub mod term_ser;

use crate::kb::{RuleId, KnowledgeBase};
use crate::kb::term::TermId;
use crate::parse::error::ParseError;
use crate::parse::ir::ParsedFile;

// ── Error ──────────────────────────────────────────────────────

#[derive(Debug)]
pub enum PersistenceError {
    Io(String),
    Parse(Vec<ParseError>),
}

impl std::fmt::Display for PersistenceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PersistenceError::Io(msg) => write!(f, "persistence I/O error: {msg}"),
            PersistenceError::Parse(errs) => {
                write!(f, "persistence parse errors:")?;
                for e in errs {
                    write!(f, "\n  {e}")?;
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for PersistenceError {}

impl From<std::io::Error> for PersistenceError {
    fn from(e: std::io::Error) -> Self {
        PersistenceError::Io(e.to_string())
    }
}

// ── Traits ─────────────────────────────────────────────────────

/// Basic persistence: persist facts, retract, flush buffered writes.
pub trait Store {
    /// Buffer a fact for writing. The KB is needed to dereference TermIds
    /// for serialization.
    fn persist(
        &mut self,
        kb: &KnowledgeBase,
        fact: TermId,
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> Result<(), PersistenceError>;

    /// Buffer a retraction. The KB is needed to canonicalize the rule's
    /// head before the caller actually retracts it from the KB. Must be
    /// called *before* `kb.retract(id)` — afterwards the rule's TermIds
    /// may be invalid.
    /// Returns true if the rule was alive at call time.
    fn retract(&mut self, kb: &KnowledgeBase, id: RuleId) -> Result<bool, PersistenceError>;

    /// Flush all buffered writes to storage.
    fn flush(&mut self, kb: &KnowledgeBase) -> Result<(), PersistenceError>;
}

/// Bulk loading: read all persisted facts back as parsed files.
pub trait BulkStore: Store {
    /// Load all persisted `.anthill` files and return them as parsed IR.
    /// The caller loads them into a KB via `kb::load::load()`.
    fn pull(&self) -> Result<Vec<ParsedFile>, PersistenceError>;
}

/// Stores that index each persisted fact by a backend-specific location
/// (file path + byte range, SQL row id, content-addressed blob hash, ...)
/// so retract can drop a specific fact in place without reconstructing
/// it from a content fingerprint. The persist + pull side of each
/// implementation populates the index; the trait surfaces the lookup so
/// retract code can be backend-generic.
///
/// Stores that don't track per-fact location (the bare `FileStore`,
/// in-memory backends, etc.) do not implement `IndexedStore` — callers
/// that need source-precise retract dispatch on the indexed variant.
pub trait IndexedStore: Store {
    /// Backend-specific identifier of where a rule lives in storage.
    /// `(PathBuf, Span)` for `IndexedFileStore`; `RowId` for a future
    /// `IndexedSqlStore`; `(BlobHash, Path)` for a content-addressed
    /// `IndexedGitStore`. Cloneable so the lookup result can be moved
    /// into the retract buffer without holding a borrow on the store.
    type Location: Clone;

    /// Look up the storage location of a previously-persisted fact.
    /// Returns `None` for runtime-asserted facts that never went through
    /// the store (e.g. asserted directly into the KB by tests).
    fn location_of(&self, id: RuleId) -> Option<Self::Location>;
}
