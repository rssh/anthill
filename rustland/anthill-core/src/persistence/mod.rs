/// Persistence — traits and backends for storing/loading KB facts.
///
/// The `Store` trait provides persist/retract/flush for individual facts.
/// `BulkStore` extends it with `pull()` to load entire file sets.
///
/// `FileStore` is the filesystem backend: reads/writes `.anthill` files.

pub mod print;
pub mod file_store;

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

    /// Mark a fact for retraction. Returns true if the fact was known.
    fn retract(&mut self, id: RuleId) -> Result<bool, PersistenceError>;

    /// Flush all buffered writes to storage.
    fn flush(&mut self, kb: &KnowledgeBase) -> Result<(), PersistenceError>;
}

/// Bulk loading: read all persisted facts back as parsed files.
pub trait BulkStore: Store {
    /// Load all persisted `.anthill` files and return them as parsed IR.
    /// The caller loads them into a KB via `kb::load::load()`.
    fn pull(&self) -> Result<Vec<ParsedFile>, PersistenceError>;
}
