/// Hash-consed term store with reference counting.
///
/// Terms are immutable. Structurally identical terms share the same `TermId`.
/// Reference counting cascades to subterms on release.
///
/// See: docs/stage0/rust-term-store-design.md §3.3, §4

use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use ordered_float::OrderedFloat;
use smallvec::SmallVec;

use crate::intern::Symbol;

// ── Handles ─────────────────────────────────────────────────────

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct TermId(u32);

impl TermId {
    pub fn index(self) -> usize {
        self.0 as usize
    }

    pub(crate) fn from_raw(raw: u32) -> Self {
        TermId(raw)
    }

    pub fn raw(self) -> u32 {
        self.0
    }
}

/// Unique identity of a logic variable.
///
/// Within a single rule, all occurrences of `?x` share one `VarId`.
/// Across rules (or rule instantiations during deduction), `?x` gets a
/// fresh `VarId` each time — this is the standard "standardize apart" step.
///
/// The human-readable `name` is carried for debug/display purposes only;
/// `Eq` and `Hash` compare only the `id`, so two VarIds with the same
/// index but different names are considered equal (which can't happen in
/// practice since ids are unique).
#[derive(Clone, Copy, Debug)]
pub struct VarId {
    id: u32,
    name: Symbol,
}

impl VarId {
    pub fn new(id: u32, name: Symbol) -> Self {
        VarId { id, name }
    }

    pub fn raw(self) -> u32 {
        self.id
    }

    pub fn name(self) -> Symbol {
        self.name
    }
}

impl PartialEq for VarId {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for VarId {}

impl Hash for VarId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

/// Variable representation: a de Bruijn index (stored terms),
/// a global id (during resolution), or a rigid id (introduced when
/// opening a `forall_impl` binder).
#[derive(Clone, Copy, Debug)]
pub enum Var {
    /// De Bruijn index — canonical representation in stored terms.
    /// Index 0 = bound by innermost enclosing binder.
    DeBruijn(u32),
    /// Global variable id — used during resolution after opening binders.
    /// "Flex" in λProlog terminology: freely unifiable with any term.
    Global(VarId),
    /// Rigid variable — introduced as a fresh witness when discharging
    /// a `forall_impl` body goal (proposal 025 §Auto-generated induction
    /// rules; WI-108). Unifies only with another `Rigid` carrying the same
    /// `VarId`; never with a flex or a concrete term. Equivalent to
    /// "Skolem constant" (resolution literature) or "eigenvariable"
    /// (sequent calculus).
    Rigid(VarId),
}

impl Var {
    pub fn is_debruijn(&self) -> bool {
        matches!(self, Var::DeBruijn(_))
    }

    pub fn is_global(&self) -> bool {
        matches!(self, Var::Global(_))
    }

    pub fn is_rigid(&self) -> bool {
        matches!(self, Var::Rigid(_))
    }

    pub fn as_global(&self) -> Option<VarId> {
        match self {
            Var::Global(vid) => Some(*vid),
            _ => None,
        }
    }

    pub fn as_rigid(&self) -> Option<VarId> {
        match self {
            Var::Rigid(vid) => Some(*vid),
            _ => None,
        }
    }

    pub fn debruijn_index(&self) -> Option<u32> {
        match self {
            Var::DeBruijn(n) => Some(*n),
            _ => None,
        }
    }

    /// Get a VarId for use in substitutions.
    /// For Global / Rigid: returns the VarId directly.
    /// For DeBruijn(n): returns a synthetic VarId with id = u32::MAX - n
    /// (reserved range, won't conflict with fresh vars that count up from 0).
    /// The name is only for display — VarId equality uses id only.
    pub fn as_vid(&self) -> VarId {
        match self {
            Var::Global(vid) => *vid,
            Var::Rigid(vid) => *vid,
            Var::DeBruijn(n) => VarId::new(u32::MAX - n, Symbol::from_raw(0)),
        }
    }
}

impl PartialEq for Var {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Var::DeBruijn(a), Var::DeBruijn(b)) => a == b,
            (Var::Global(a), Var::Global(b)) => a == b,
            (Var::Rigid(a), Var::Rigid(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for Var {}

impl Hash for Var {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Var::DeBruijn(n) => {
                0u8.hash(state);
                n.hash(state);
            }
            Var::Global(vid) => {
                1u8.hash(state);
                vid.hash(state);
            }
            Var::Rigid(vid) => {
                2u8.hash(state);
                vid.hash(state);
            }
        }
    }
}

// ── Term ────────────────────────────────────────────────────────

/// A term in the knowledge base. Implements `Eq + Hash` for hash-consing.
///
/// Functor names are a single interned `Symbol` carrying the fully-qualified
/// name (e.g. `"banking.deposit"`).  Two domains that each define `+` produce
/// distinct symbols (`"x.+"` vs `"y.+"`), so domain-scoped identity is
/// resolved before terms enter the store.  Spans live in the parse IR, not here.
///
/// There is no `Infix` variant — infix syntax (`a + b`, `x = y`) is desugared
/// to `Fn` calls (`add(a, b)`, `eq(x, y)`) eagerly in the parser's CST→IR
/// converter, so every downstream consumer sees only `Fn`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    /// Literal constant: string, int, float, bool
    Const(Literal),
    /// Logic variable: `?x`. Uses `Var` representation — either a de Bruijn
    /// index (canonical in stored terms) or a global `VarId` (during resolution).
    Var(Var),
    /// Function application: `f(arg1, arg2, key: arg3)`.
    /// `functor` is the fully-qualified interned name of the function symbol.
    /// Positional args are stored in `pos_args`, named args in `named_args`
    /// (pre-sorted by `Symbol::index()` at construction time).
    Fn {
        functor: Symbol,
        pos_args: SmallVec<[TermId; 4]>,
        named_args: SmallVec<[(Symbol, TermId); 2]>,
    },
    /// Reference term: `Ref(name)`
    Ref(Symbol),
    /// Bottom: `⊥`
    Bottom,
    /// Bare identifier — resolves to Ref or Var later
    Ident(Symbol),
    /// WI-271 — parse-only: carries a tagged parse-IR payload
    /// (`ParseAux`) so the let_expr / apply Term::Fn can hold the
    /// annotation / type-args as a child `TermId` rather than via a
    /// side HashMap. Allocated only by the parse pass; the loader
    /// reads and lowers it before any KB-side allocation, so this
    /// variant **never** appears in the KB's hash-consed `TermStore`.
    /// KB-side consumers can `unreachable!()` on encounter.
    ParseAux(Box<crate::parse::ir::ParseAux>),
}

impl Term {
    /// Immediate child `TermId`s of this term.
    pub fn subterms(&self) -> SmallVec<[TermId; 4]> {
        match self {
            Term::Fn { pos_args, named_args, .. } => {
                let mut out: SmallVec<[TermId; 4]> = pos_args.iter().copied().collect();
                out.extend(named_args.iter().map(|&(_, id)| id));
                out
            }
            Term::Const(_) | Term::Var(_) | Term::Ref(_)
            | Term::Bottom | Term::Ident(_) => SmallVec::new(),
            // Parse-only; never reachable in the KB-side hash-consed
            // store (the loader strips ParseAux before allocation).
            Term::ParseAux(_) => SmallVec::new(),
        }
    }

    /// Total arity (positional + named args). Only meaningful for `Fn` terms.
    pub fn arity(&self) -> usize {
        match self {
            Term::Fn { pos_args, named_args, .. } => pos_args.len() + named_args.len(),
            _ => 0,
        }
    }
}

// ── Literal ─────────────────────────────────────────────────────

/// Kind of opaque handle stored as a literal value. WI-251: the
/// `Occurrence` variant is gone — expression occurrences live as
/// `Rc<NodeOccurrence>` trees keyed in `kb.op_bodies`, no longer as
/// arena-backed handles in term literals.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HandleKind {
    /// FactId/RuleId — identity of an asserted fact.
    Fact,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Literal {
    String(String),
    Int(i64),
    BigInt(num_bigint::BigInt),
    Float(OrderedFloat<f64>),
    Bool(bool),
    /// Opaque handle (OccurrenceId, FactId, etc.) representable as a term value.
    Handle(HandleKind, u32),
}

// ── TermStore (hash-consed, refcounted) ─────────────────────────

pub struct TermStore {
    terms: Vec<Option<Term>>,
    hash_index: HashMap<Term, TermId>,
    refcounts: Vec<u32>,
    free_list: Vec<TermId>,
}

impl TermStore {
    pub fn new() -> Self {
        Self {
            terms: Vec::new(),
            hash_index: HashMap::new(),
            refcounts: Vec::new(),
            free_list: Vec::new(),
        }
    }

    /// Allocate a term, deduplicating via hash-consing.
    /// If an identical term exists, increments its refcount and returns it.
    pub fn alloc(&mut self, term: Term) -> TermId {
        if let Some(&existing) = self.hash_index.get(&term) {
            self.refcounts[existing.index()] += 1;
            return existing;
        }
        // Increment refcounts on subterms
        for sub in term.subterms() {
            self.incref(sub);
        }
        let id = self.alloc_slot(term.clone());
        self.hash_index.insert(term, id);
        id
    }

    fn alloc_slot(&mut self, term: Term) -> TermId {
        if let Some(id) = self.free_list.pop() {
            self.terms[id.index()] = Some(term);
            self.refcounts[id.index()] = 1;
            id
        } else {
            let id = TermId(self.terms.len() as u32);
            self.terms.push(Some(term));
            self.refcounts.push(1);
            id
        }
    }

    /// Increment the reference count for an existing term.
    pub fn incref(&mut self, id: TermId) {
        self.refcounts[id.index()] += 1;
    }

    /// Decrement refcount. If zero, free the slot and cascade to subterms.
    pub fn release(&mut self, id: TermId) {
        let rc = &mut self.refcounts[id.index()];
        *rc = rc.saturating_sub(1);
        if *rc == 0 {
            if let Some(term) = self.terms[id.index()].take() {
                self.hash_index.remove(&term);
                self.free_list.push(id);
                for sub in term.subterms() {
                    self.release(sub);
                }
            }
        }
    }

    /// Get a reference to the term at the given id.
    pub fn get(&self, id: TermId) -> &Term {
        self.terms[id.index()]
            .as_ref()
            .expect("TermStore::get called on freed slot")
    }

    pub fn len(&self) -> usize {
        self.terms.len() - self.free_list.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn refcount(&self, id: TermId) -> u32 {
        self.refcounts[id.index()]
    }
}

impl Default for TermStore {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intern::Symbol;

    fn sym(n: u32) -> Symbol {
        // For testing only — bypass interner
        unsafe { std::mem::transmute(n) }
    }

    #[test]
    fn hash_consing_dedup() {
        let mut store = TermStore::new();
        let a = store.alloc(Term::Const(Literal::Int(42)));
        let b = store.alloc(Term::Const(Literal::Int(42)));
        assert_eq!(a, b);
        assert_eq!(store.refcount(a), 2);
    }

    #[test]
    fn release_cascades() {
        let mut store = TermStore::new();
        let inner = store.alloc(Term::Const(Literal::Int(1)));
        let outer = store.alloc(Term::Fn {
            functor: sym(0),
            pos_args: SmallVec::from_elem(inner, 1),
            named_args: SmallVec::new(),
        });
        // inner has refcount 2 (1 from alloc + 1 from being a subterm of outer)
        assert_eq!(store.refcount(inner), 2);
        store.release(outer);
        // outer freed, inner refcount decremented to 1
        assert_eq!(store.refcount(inner), 1);
    }

    #[test]
    fn infix_desugared_to_fn() {
        let mut store = TermStore::new();
        let a = store.alloc(Term::Const(Literal::Int(1)));
        let b = store.alloc(Term::Const(Literal::Int(2)));
        // a + b is represented as add(a, b)
        let sum = store.alloc(Term::Fn {
            functor: sym(0), // would be intern("add") in real use
            pos_args: SmallVec::from_slice(&[a, b]),
            named_args: SmallVec::new(),
        });
        let subs = store.get(sum).subterms();
        assert_eq!(subs.as_slice(), &[a, b]);
    }
}

// ── TermSource trait ────────────────────────────────────────────

/// Read-only view over a term graph plus the symbol table that names its
/// functors. Implemented by `KnowledgeBase` (hash-consed) and by
/// `ParsedFile` (parse-IR + parse-time symbol table). Lets `TermPrinter`
/// render either without duplicating the printing logic.
///
/// Distinct from `kb::term_view::TermView`, which abstracts unification
/// over `TermId` vs runtime `Value`. This trait is for *rendering*; that
/// one is for *matching*.
pub trait TermSource {
    fn term(&self, id: TermId) -> &Term;
    fn sym_name(&self, sym: Symbol) -> &str;
    /// Fully-qualified name of a symbol — for collision-free functor matching
    /// (WI-173: distinguishing the type functor
    /// `anthill.prelude.TypeExtractor.Arrow` / `…EffectExpression.merge` from a
    /// user sort/entity that happens to share the short name `Arrow`/`merge`).
    /// Defaults to the short name for views with no qualified-name table
    /// (e.g. parse-side `ParsedFile`), which simply keeps the generic Fn form.
    fn qualified_name(&self, sym: Symbol) -> &str {
        self.sym_name(sym)
    }
}
