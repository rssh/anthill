/// OccurrenceStore — positional identity for source expressions.
///
/// Each occurrence links a hash-consed TermId to a source position (SourceSpan)
/// and its owning declaration (operation, rule, fact, constraint).
/// Occurrences are NOT hash-consed — each source position gets a unique id.
///
/// Tree navigation is handled by the Expr entity structure (named fields like
/// cond, then_branch, etc.), not by parent-child links here.
///
/// See: docs/proposals/022-typing-as-facts.md

use std::collections::HashMap;

use super::term::TermId;
use crate::intern::Symbol;
use crate::span::SourceSpan;

// ── Handles ─────────────────────────────────────────────────────

/// Handle to an occurrence in the OccurrenceStore. Sequential, not hash-consed.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct OccurrenceId(u32);

impl OccurrenceId {
    pub fn index(self) -> usize {
        self.0 as usize
    }

    pub fn from_raw(raw: u32) -> Self {
        OccurrenceId(raw)
    }

    pub fn raw(self) -> u32 {
        self.0
    }
}

/// Handle to an expression occurrence. Newtype wrapper for type safety —
/// you can't pass a non-expression occurrence where an expression is expected.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ExprOccurrenceId(OccurrenceId);

impl ExprOccurrenceId {
    pub fn occurrence(self) -> OccurrenceId {
        self.0
    }

    pub fn raw(self) -> u32 {
        self.0.raw()
    }
}

// ── Store ───────────────────────────────────────────────────────

struct OccurrenceEntry {
    term: TermId,
    span: SourceSpan,
    /// Symbol of the containing declaration (operation, rule label, entity, etc.).
    /// None for top-level or unknown context.
    owner: Option<Symbol>,
    is_expr: bool,
    /// WI-231 — call-site classification the typer (`check_apply`)
    /// attached to this occurrence, consumed by `kb::req_insertion::run`.
    /// Boxed: `CallClass::ConcreteApplyWithin` is large and most
    /// occurrences carry no classification.
    classification: Option<Box<crate::kb::typing::CallClass>>,
}

/// Sequential store for positioned term occurrences.
pub struct OccurrenceStore {
    entries: Vec<OccurrenceEntry>,
    /// Index: TermId → list of occurrences sharing that structural term.
    by_term: HashMap<TermId, Vec<OccurrenceId>>,
    /// Index: functor Symbol → list of occurrences with that head functor.
    /// Used by the resolver to route Expr-typed queries to the OccurrenceStore.
    by_functor: HashMap<Symbol, Vec<OccurrenceId>>,
}

impl OccurrenceStore {
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
            by_term: HashMap::new(),
            by_functor: HashMap::new(),
        }
    }

    /// Create an occurrence, returning its id.
    pub fn alloc(
        &mut self,
        term: TermId,
        span: SourceSpan,
        owner: Option<Symbol>,
        is_expr: bool,
    ) -> OccurrenceId {
        let id = OccurrenceId(self.entries.len() as u32);
        self.entries.push(OccurrenceEntry {
            term,
            span,
            owner,
            is_expr,
            classification: None,
        });
        self.by_term.entry(term).or_default().push(id);
        id
    }

    /// Create an expression occurrence (convenience method).
    pub fn alloc_expr(
        &mut self,
        term: TermId,
        span: SourceSpan,
        owner: Option<Symbol>,
    ) -> ExprOccurrenceId {
        let id = self.alloc(term, span, owner, true);
        ExprOccurrenceId(id)
    }

    // ── Accessors ───────────────────────────────────────────────

    pub fn term(&self, id: OccurrenceId) -> TermId {
        self.entries[id.index()].term
    }

    pub fn span(&self, id: OccurrenceId) -> SourceSpan {
        self.entries[id.index()].span
    }

    pub fn owner(&self, id: OccurrenceId) -> Option<Symbol> {
        self.entries[id.index()].owner
    }

    pub fn is_expr(&self, id: OccurrenceId) -> bool {
        self.entries[id.index()].is_expr
    }

    // ── Classifications (WI-231) ────────────────────────────────

    /// Attach the typer's call-site classification to an occurrence.
    /// Called from `check_apply`; read back by `kb::req_insertion::run`.
    pub fn set_classification(&mut self, id: OccurrenceId, class: crate::kb::typing::CallClass) {
        self.entries[id.index()].classification = Some(Box::new(class));
    }

    /// Iterate `(OccurrenceId, &CallClass)` for every classified
    /// occurrence — the requirement-insertion pass's input.
    pub fn classifications_iter(
        &self,
    ) -> impl Iterator<Item = (OccurrenceId, &crate::kb::typing::CallClass)> {
        self.entries.iter().enumerate().filter_map(|(i, e)| {
            e.classification.as_deref().map(|c| (OccurrenceId(i as u32), c))
        })
    }

    // ── Indexing ──────────────────────────────────────────────────

    /// Register an occurrence under a functor symbol for query routing.
    pub fn index_by_functor(&mut self, id: OccurrenceId, functor: Symbol) {
        self.by_functor.entry(functor).or_default().push(id);
    }

    // ── Index queries ───────────────────────────────────────────

    /// All occurrences that share the given structural term.
    pub fn by_term(&self, term: TermId) -> &[OccurrenceId] {
        self.by_term.get(&term).map_or(&[], |v| v.as_slice())
    }

    /// All occurrences with the given head functor.
    pub fn by_functor(&self, functor: Symbol) -> &[OccurrenceId] {
        self.by_functor.get(&functor).map_or(&[], |v| v.as_slice())
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

// ── Tests ───────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::span::{SourceId, SourceSpan};

    fn make_span(source: u32, start: u32, end: u32) -> SourceSpan {
        SourceSpan::new(SourceId::from_raw(source), start, end)
    }

    #[test]
    fn alloc_and_retrieve() {
        let mut store = OccurrenceStore::new();
        let term = TermId::from_raw(10);
        let span = make_span(0, 5, 15);

        let occ = store.alloc(term, span, None, true);

        assert_eq!(store.term(occ), term);
        assert_eq!(store.span(occ), span);
        assert_eq!(store.owner(occ), None);
        assert!(store.is_expr(occ));
        assert_eq!(store.len(), 1);
    }

    #[test]
    fn alloc_expr_returns_typed_id() {
        let mut store = OccurrenceStore::new();
        let term = TermId::from_raw(20);
        let span = make_span(0, 10, 20);

        let expr_occ = store.alloc_expr(term, span, None);

        assert_eq!(store.term(expr_occ.occurrence()), term);
        assert!(store.is_expr(expr_occ.occurrence()));
    }

    #[test]
    fn by_term_index() {
        let mut store = OccurrenceStore::new();
        let term = TermId::from_raw(42);

        let occ1 = store.alloc(term, make_span(0, 10, 15), None, true);
        let occ2 = store.alloc(term, make_span(0, 30, 35), None, true);
        let _other = store.alloc(TermId::from_raw(99), make_span(0, 50, 55), None, true);

        assert_eq!(store.by_term(term), &[occ1, occ2]);
        assert_eq!(store.by_term(TermId::from_raw(999)), &[] as &[OccurrenceId]);
    }

    #[test]
    fn owner_symbol() {
        use crate::intern::SymbolTable;

        let mut store = OccurrenceStore::new();
        let mut symbols = SymbolTable::new();
        let term = TermId::from_raw(1);
        let span = make_span(0, 0, 10);

        let sym = symbols.intern("foo");

        let occ1 = store.alloc(term, span, Some(sym), true);
        let occ2 = store.alloc(term, span, None, true);

        assert_eq!(store.owner(occ1), Some(sym));
        assert_eq!(store.owner(occ2), None);
    }
}
