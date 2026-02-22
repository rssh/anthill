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
    /// Logic variable: `?x`. Identity is the `VarId` index;
    /// the human-readable name is carried inside `VarId` for display only.
    Var(VarId),
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
    /// Unspecified term: `<"description">` with optional hints
    Unspecified {
        text: String,
        hints: SmallVec<[TermId; 2]>,
    },
    /// Bottom: `⊥`
    Bottom,
    /// Bare identifier — resolves to Ref or Var later
    Ident(Symbol),
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
            Term::Unspecified { hints, .. } => {
                hints.iter().copied().collect()
            }
            Term::Const(_) | Term::Var(_) | Term::Ref(_)
            | Term::Bottom | Term::Ident(_) => SmallVec::new(),
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Literal {
    String(String),
    Int(i64),
    Float(OrderedFloat<f64>),
    Bool(bool),
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
