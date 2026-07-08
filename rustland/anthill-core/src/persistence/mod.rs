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
    NotQueryable,
    NotMutable,
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
            PersistenceError::NotQueryable => write!(
                f, "persistence: store does not implement pattern-based retrieve"
            ),
            PersistenceError::NotMutable => write!(
                f, "persistence: store is append-only (does not provide NonMonotonicStore) — cannot retract"
            ),
        }
    }
}

/// The three per-functor write policies (proposal 053), mirroring the anthill
/// `enum Monotonicity` in `anthill.reflect`. Lives here (not in `eval`) because
/// write policy is a storage property (007 §2): a `Store` reports it via
/// [`Store::owned_monotonicity`], and the eval-side guard reads the same enum.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Monotonicity {
    /// neither asserted nor retracted at runtime (frozen)
    Constant,
    /// asserted, never retracted (append-only) — the DEFAULT
    Monotone,
    /// asserted and retracted (retract / update)
    NonMonotone,
}

impl Monotonicity {
    /// The qualified name of this policy's `anthill.reflect.Monotonicity`
    /// variant — the single source of the enum↔anthill-name correspondence,
    /// used both to decode a reduced `fact_monotonicity` head and to encode a
    /// `Store.monotonicity` answer.
    pub fn reflect_variant_qname(self) -> &'static str {
        match self {
            Monotonicity::Constant => "anthill.reflect.Monotonicity.constant",
            Monotonicity::Monotone => "anthill.reflect.Monotonicity.monotone",
            Monotonicity::NonMonotone => "anthill.reflect.Monotonicity.non_monotone",
        }
    }
}

impl std::error::Error for PersistenceError {}

impl From<std::io::Error> for PersistenceError {
    fn from(e: std::io::Error) -> Self {
        PersistenceError::Io(e.to_string())
    }
}

/// Extend a fact-block byte range to swallow one trailing newline plus
/// one following blank line, so removing a block separated from its
/// successor by a blank line doesn't leave two blanks in a row. Shared
/// between `FileStore::apply_retracts` and `IndexedFileStore::flush`.
pub(crate) fn extend_drop_end(bytes: &[u8], end: usize) -> usize {
    let mut drop_end = end;
    if drop_end < bytes.len() && bytes[drop_end] == b'\n' {
        drop_end += 1;
    }
    if drop_end < bytes.len() && bytes[drop_end] == b'\n' {
        drop_end += 1;
    }
    drop_end
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
    ///
    /// `retract` is the mutation capability (proposal 053 / 007 §2): at the
    /// anthill level it lives on `NonMonotonicStore`, so only a backend that
    /// declares `fact NonMonotonicStore[X]` is ever asked to retract. This
    /// default is the Rust-side gate — an append-only backend that does not
    /// override it fails loudly (surfaced through the `Error` effect at the
    /// write, never a silent no-op), mirroring how `retrieve` defaults to
    /// `NotQueryable`.
    fn retract(&mut self, _kb: &KnowledgeBase, _id: RuleId) -> Result<bool, PersistenceError> {
        Err(PersistenceError::NotMutable)
    }

    /// Flush all buffered writes to storage.
    fn flush(&mut self, kb: &KnowledgeBase) -> Result<(), PersistenceError>;

    /// The store's intrinsic per-functor write policy (proposal 053 / 007 §2),
    /// as `(qualified functor name, policy)` pairs. This is how a store
    /// *provides* monotonicity — the store is the single authority (007 §2).
    ///
    /// Materialized into the reflect `fact_monotonicity` facade at
    /// registration (`Interpreter::register_store`): for a functor with no
    /// in-memory reflect rule, the guard falls back to the owning store's
    /// answer here rather than the in-memory `monotone` default.
    ///
    /// The filesystem backends return `[]`: their per-functor policy is the
    /// project's own reflect rules (`rule fact_monotonicity(WorkItem) =
    /// non_monotone()`), not intrinsic to the file store. A policy-bearing
    /// backend (a SQL store reading its schema, a read-only materialized view)
    /// overrides this with schema-derived values.
    fn owned_monotonicity(&self) -> Vec<(String, Monotonicity)> {
        Vec::new()
    }

    /// Pattern-based retrieval. The contract — declared formally on the
    /// anthill side via `fact QueryableStore[X]` — is that a store
    /// satisfying `QueryableStore` returns every persisted fact unifying
    /// with `pattern`. The default implementation returns `NotQueryable`;
    /// stores that satisfy `QueryableStore` override.
    ///
    /// Returns the matching fact `TermId`s in arbitrary order. The caller
    /// (the `retrieve` builtin) wraps the result as a `Stream[Term, Error]`.
    fn retrieve(
        &self,
        _kb: &KnowledgeBase,
        _pattern: TermId,
    ) -> Result<Vec<TermId>, PersistenceError> {
        Err(PersistenceError::NotQueryable)
    }
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
