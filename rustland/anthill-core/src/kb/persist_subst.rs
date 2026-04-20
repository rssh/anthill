/// Persistent substitution for discrimination tree traversal.
///
/// Bindings are accumulated during tree navigation. Each entry's right-hand
/// side is a `BindValue`: either an already-resolved `TermId` or a deferred
/// `VarPath` that is resolved at the leaf from the fact term.
///
/// Two implementations:
/// - `SmallSubst` — SmallVec-based, clone = memcpy (~128 bytes for ≤ 8 bindings)
/// - `SharedSubst` — Arc cons-list, clone = O(1) refcount bump

use std::sync::Arc;

use smallvec::SmallVec;

use crate::eval::value::Value;
use crate::intern::Symbol;
use super::subst::Substitution;
use super::term::{Term, TermId, TermStore, VarId};

// ── VarPath — position of a variable binding in a term ──────────

/// Describes where in a fact term to extract a variable's binding value.
#[derive(Clone, Debug)]
pub(crate) enum VarPath {
    /// The entire fact term (bare variable query)
    Root,
    /// An argument value of the top-level Fn
    Arg(ArgPos),
}

/// Identifies an argument within a Fn term.
#[derive(Clone, Debug)]
pub(crate) enum ArgPos {
    /// N-th positional argument (0-based)
    Positional(usize),
    /// Named argument with this key symbol
    Named(Symbol),
}

// ── BindValue — right-hand side of a persistent substitution entry

/// A binding value: a TermId (KB-resident), a deferred path into the fact
/// term, or a runtime `Value` (external-sourced, per 026.1 Q2 — used when
/// the query side is a `Value::Entity` etc. that can't be promoted to a
/// TermId without violating the lineage-preservation invariant).
#[derive(Clone, Debug)]
pub(crate) enum BindValue {
    /// Resolved immediately (e.g., tree var_edge bound to query's known TermId)
    Term(TermId),
    /// Deferred: extract from fact term at leaf using this path
    Path(VarPath),
    /// Non-TermId runtime value from an external-source query side.
    Value(Value),
}

// ── Path extraction ─────────────────────────────────────────────

/// Extract a subterm TermId from a fact term following a VarPath.
pub(crate) fn extract_at_path(terms: &TermStore, fact_term: TermId, path: &VarPath) -> TermId {
    match path {
        VarPath::Root => fact_term,
        VarPath::Arg(arg_pos) => {
            if let Term::Fn { pos_args, named_args, .. } = terms.get(fact_term) {
                match arg_pos {
                    ArgPos::Positional(n) => {
                        if let Some(&id) = pos_args.get(*n) {
                            return id;
                        }
                    }
                    ArgPos::Named(sym) => {
                        for &(s, id) in named_args.iter() {
                            if s == *sym { return id; }
                        }
                    }
                }
            }
            // Fallback: return fact_term itself (shouldn't happen with valid paths)
            fact_term
        }
    }
}

// ── PersistSubst trait ──────────────────────────────────────────

/// Persistent substitution for tree traversal.
///
/// `clone()` forks at branch points (SmallVec: memcpy, Chain: Arc bump).
/// `with_binding()` consumes self, returns extended substitution.
/// `resolve_leaf()` materializes deferred paths against the fact term.
pub(crate) trait PersistSubst: Clone {
    fn new() -> Self;
    fn with_binding(self, var: VarId, value: BindValue) -> Self;
    fn resolve_leaf(self, terms: &TermStore, fact_term: TermId) -> Substitution;
}

// ── SmallSubst — SmallVec-based (clone = memcpy) ────────────────

#[derive(Clone)]
pub(crate) struct SmallSubst {
    bindings: SmallVec<[(VarId, BindValue); 8]>,
}

impl PersistSubst for SmallSubst {
    fn new() -> Self {
        SmallSubst { bindings: SmallVec::new() }
    }

    fn with_binding(mut self, var: VarId, value: BindValue) -> Self {
        self.bindings.push((var, value));
        self
    }

    fn resolve_leaf(self, terms: &TermStore, fact_term: TermId) -> Substitution {
        let mut s = Substitution::new();
        for (vid, val) in self.bindings {
            match val {
                BindValue::Term(tid) => s.bind_term(vid, tid),
                BindValue::Path(path) => s.bind_term(vid, extract_at_path(terms, fact_term, &path)),
                BindValue::Value(v) => s.bind_value(vid, v),
            }
        }
        s
    }
}

// ── SharedSubst — Arc cons-list (clone = O(1)) ─────────────────

struct SubstCell {
    var: VarId,
    value: BindValue,
    tail: Option<Arc<SubstCell>>,
}

#[derive(Clone)]
#[allow(dead_code)]
pub(crate) struct SharedSubst {
    head: Option<Arc<SubstCell>>,
}

#[allow(dead_code)]
impl PersistSubst for SharedSubst {
    fn new() -> Self {
        SharedSubst { head: None }
    }

    fn with_binding(self, var: VarId, value: BindValue) -> Self {
        SharedSubst {
            head: Some(Arc::new(SubstCell {
                var, value, tail: self.head,
            })),
        }
    }

    fn resolve_leaf(self, terms: &TermStore, fact_term: TermId) -> Substitution {
        let mut s = Substitution::new();
        let mut cur = &self.head;
        while let Some(cell) = cur {
            match &cell.value {
                BindValue::Term(tid) => s.bind_term(cell.var, *tid),
                BindValue::Path(path) => s.bind_term(cell.var, extract_at_path(terms, fact_term, path)),
                BindValue::Value(v) => s.bind_value(cell.var, v.clone()),
            }
            cur = &cell.tail;
        }
        s
    }
}

// ── Tests ───────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intern::Interner;
    use super::super::term::{Literal, Term, TermId};

    struct TestEnv {
        terms: TermStore,
        interner: Interner,
        next_var: u32,
    }

    impl TestEnv {
        fn new() -> Self {
            TestEnv { terms: TermStore::new(), interner: Interner::new(), next_var: 0 }
        }
        fn intern(&mut self, s: &str) -> Symbol { self.interner.intern(s) }
        fn alloc(&mut self, term: Term) -> TermId { self.terms.alloc(term) }
        fn fresh_var(&mut self, name: &str) -> VarId {
            let sym = self.interner.intern(name);
            let id = self.next_var;
            self.next_var += 1;
            VarId::new(id, sym)
        }
    }

    // ── PersistSubst tests ──────────────────────────────────────

    #[test]
    fn small_subst_resolve_leaf_term() {
        let mut env = TestEnv::new();
        let vid = env.fresh_var("x");
        let tid = env.alloc(Term::Const(Literal::Int(42)));

        let s = SmallSubst::new()
            .with_binding(vid, BindValue::Term(tid));
        let sub = s.resolve_leaf(&env.terms, TermId::from_raw(0));
        assert_eq!(sub.resolve(vid), Some(tid));
    }

    #[test]
    fn small_subst_resolve_leaf_path() {
        let mut env = TestEnv::new();
        let vid = env.fresh_var("x");
        let f_sym = env.intern("f");
        let val = env.alloc(Term::Const(Literal::Int(42)));
        let fact_term = env.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });

        let s = SmallSubst::new()
            .with_binding(vid, BindValue::Path(VarPath::Arg(ArgPos::Positional(0))));
        let sub = s.resolve_leaf(&env.terms, fact_term);
        assert_eq!(sub.resolve(vid), Some(val));
    }

    #[test]
    fn small_subst_clone_independence() {
        let mut env = TestEnv::new();
        let vid1 = env.fresh_var("x");
        let vid2 = env.fresh_var("y");
        let tid = env.alloc(Term::Const(Literal::Int(1)));

        let s1 = SmallSubst::new()
            .with_binding(vid1, BindValue::Term(tid));
        let s2 = s1.clone()
            .with_binding(vid2, BindValue::Term(tid));

        let sub1 = s1.resolve_leaf(&env.terms, TermId::from_raw(0));
        assert_eq!(sub1.resolve(vid1), Some(tid));
        assert_eq!(sub1.resolve(vid2), None);

        let sub2 = s2.resolve_leaf(&env.terms, TermId::from_raw(0));
        assert_eq!(sub2.resolve(vid1), Some(tid));
        assert_eq!(sub2.resolve(vid2), Some(tid));
    }

    #[test]
    fn shared_subst_resolve_leaf() {
        let mut env = TestEnv::new();
        let vid = env.fresh_var("x");
        let tid = env.alloc(Term::Const(Literal::Int(42)));

        let s = SharedSubst::new()
            .with_binding(vid, BindValue::Term(tid));
        let sub = s.resolve_leaf(&env.terms, TermId::from_raw(0));
        assert_eq!(sub.resolve(vid), Some(tid));
    }

    #[test]
    fn shared_subst_clone_independence() {
        let mut env = TestEnv::new();
        let vid1 = env.fresh_var("x");
        let vid2 = env.fresh_var("y");
        let tid = env.alloc(Term::Const(Literal::Int(1)));

        let s1 = SharedSubst::new()
            .with_binding(vid1, BindValue::Term(tid));
        let s2 = s1.clone()
            .with_binding(vid2, BindValue::Term(tid));

        let sub1 = s1.resolve_leaf(&env.terms, TermId::from_raw(0));
        assert_eq!(sub1.resolve(vid2), None);

        let sub2 = s2.resolve_leaf(&env.terms, TermId::from_raw(0));
        assert_eq!(sub2.resolve(vid1), Some(tid));
        assert_eq!(sub2.resolve(vid2), Some(tid));
    }

    // ── Path extraction tests ───────────────────────────────────

    #[test]
    fn extract_at_path_root() {
        let mut env = TestEnv::new();
        let tid = env.alloc(Term::Const(Literal::Int(42)));
        assert_eq!(extract_at_path(&env.terms, tid, &VarPath::Root), tid);
    }

    #[test]
    fn extract_at_path_positional() {
        let mut env = TestEnv::new();
        let f_sym = env.intern("f");
        let val0 = env.alloc(Term::Const(Literal::Int(1)));
        let val1 = env.alloc(Term::Const(Literal::Int(2)));
        let term = env.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_slice(&[val0, val1]),
            named_args: SmallVec::new(),
        });
        assert_eq!(extract_at_path(&env.terms, term, &VarPath::Arg(ArgPos::Positional(0))), val0);
        assert_eq!(extract_at_path(&env.terms, term, &VarPath::Arg(ArgPos::Positional(1))), val1);
    }

    #[test]
    fn extract_at_path_named() {
        let mut env = TestEnv::new();
        let f_sym = env.intern("f");
        let k_sym = env.intern("key");
        let val = env.alloc(Term::Const(Literal::String("v".into())));
        let term = env.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(k_sym, val)]),
        });
        assert_eq!(extract_at_path(&env.terms, term, &VarPath::Arg(ArgPos::Named(k_sym))), val);
    }
}
