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
use crate::kb::term_view::{TermView, ViewItem};
use crate::kb::KnowledgeBase;

// ── VarPath — position of a variable binding in a term ──────────

/// Describes where in a fact term to extract a variable's binding value: a
/// chain of [`ArgPos`] steps descending from the head, root-to-leaf. The empty
/// chain is the root (a bare-variable query binds the whole head). A single
/// step addresses a top-level argument; multiple steps address a variable
/// nested inside a compound argument (`f(g(?y))` records `?y` at
/// `[Positional(0), Positional(0)]`). The discrimination-tree query records the
/// chain as it descends the query structure (WI-373 gap 3 — nested binding
/// extraction); `extract_at_path` / `extract_value_at_path` replay it against
/// the matched fact head.
#[derive(Clone, Debug, Default)]
pub struct VarPath(SmallVec<[ArgPos; 4]>);

impl VarPath {
    /// The root path (empty chain) — addresses the whole head.
    pub(crate) fn root() -> Self {
        VarPath(SmallVec::new())
    }

    /// A new path with `step` appended (descend one level). Cheap for the
    /// common shallow case (≤ 4 steps stay inline in the `SmallVec`).
    pub(crate) fn appended(&self, step: ArgPos) -> Self {
        let mut steps = self.0.clone();
        steps.push(step);
        VarPath(steps)
    }

    /// The steps, root-to-leaf.
    pub(crate) fn steps(&self) -> &[ArgPos] {
        &self.0
    }
}

/// Identifies an argument within a Fn term.
#[derive(Clone, Copy, Debug)]
pub enum ArgPos {
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
pub enum BindValue {
    /// Resolved immediately (e.g., tree var_edge bound to query's known TermId)
    Term(TermId),
    /// Deferred: extract from fact term at leaf using this path
    Path(VarPath),
    /// Non-TermId runtime value from an external-source query side.
    Value(Value),
}

// ── Path extraction ─────────────────────────────────────────────

/// Extract a subterm TermId from a fact term following a VarPath, descending
/// one [`ArgPos`] step at a time. The root path returns the whole term; a
/// multi-step path walks into nested `Fn` args (WI-373 gap 3).
pub(crate) fn extract_at_path(terms: &TermStore, fact_term: TermId, path: &VarPath) -> TermId {
    let mut cur = fact_term;
    for step in path.steps() {
        let Term::Fn { pos_args, named_args, .. } = terms.get(cur) else {
            // A recorded path must descend a term that matched the query
            // structure; a non-Fn here is a discrim/path desync — surface it
            // loudly in debug, fall back to the whole term in release.
            debug_assert!(false, "extract_at_path: path step {step:?} into a non-Fn term");
            return fact_term;
        };
        let next = match step {
            ArgPos::Positional(n) => pos_args.get(*n).copied(),
            ArgPos::Named(sym) => named_args.iter().find(|(s, _)| s == sym).map(|(_, id)| *id),
        };
        match next {
            Some(id) => cur = id,
            None => {
                debug_assert!(false, "extract_at_path: no arg at {step:?} (path/fact desync)");
                return fact_term;
            }
        }
    }
    cur
}

/// Carrier-faithful peer of [`extract_at_path`] (WI-348 Phase B): extract a
/// subterm of a `Value` fact head following a `VarPath`, returning a `Value` so
/// a `Value::Node` child keeps its occurrence identity in the answer. Walks the
/// head through `TermView` — the SAME surface the discrimination tree indexed it
/// by — so a named-arg position reads the child the path was recorded against
/// (the term-store walk would read a sorted-by-name skeleton; see the design
/// doc's named-order finding).
pub(crate) fn extract_value_at_path(kb: &KnowledgeBase, head: &Value, path: &VarPath) -> Value {
    let mut cur = head.clone();
    for step in path.steps() {
        // Read the child through `TermView` at each level — the SAME surface
        // the tree indexed by — so a `Value::Node` child keeps its occurrence
        // identity as we descend (WI-373 gap 3 nested path-descent).
        let item = match step {
            ArgPos::Positional(n) => cur.pos_arg(kb, *n),
            ArgPos::Named(sym) => cur.named_arg(kb, *sym),
        };
        cur = match item {
            Some(ViewItem::Term(t)) => Value::term(t),
            Some(ViewItem::Value(v)) => v.clone(),
            Some(ViewItem::Node(occ)) => Value::Node(occ),
            // Mirror extract_at_path: a recorded path must descend a matching
            // head; a missing child is a path/head desync — loud in debug,
            // whole-head fallback in release.
            None => {
                debug_assert!(false, "extract_value_at_path: no child at {step:?} (path/head desync)");
                return head.clone();
            }
        };
    }
    cur
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
    fn resolve_leaf(self, kb: &KnowledgeBase, fact_term: TermId) -> Substitution;

    /// Carrier-faithful peer of [`resolve_leaf`] (WI-348 Phase B): resolve
    /// deferred paths against a `Value` fact head instead of a hash-consed
    /// `TermId`, so a value fact's bindings keep `Value::Node` identity and read
    /// the carrier the discrimination tree actually indexed.
    fn resolve_leaf_view(self, kb: &KnowledgeBase, fact_head: &Value) -> Substitution;
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

    fn resolve_leaf(self, kb: &KnowledgeBase, fact_term: TermId) -> Substitution {
        let mut s = Substitution::new();
        for (vid, val) in self.bindings {
            match val {
                BindValue::Term(tid) => s.bind_term(kb, vid, tid),
                BindValue::Path(path) => {
                    s.bind_term(kb, vid, extract_at_path(&kb.terms, fact_term, &path))
                }
                BindValue::Value(v) => s.bind_value(kb, vid, v),
            }
        }
        s
    }

    fn resolve_leaf_view(self, kb: &KnowledgeBase, fact_head: &Value) -> Substitution {
        let mut s = Substitution::new();
        for (vid, val) in self.bindings {
            match val {
                BindValue::Term(tid) => s.bind_term(kb, vid, tid),
                BindValue::Path(path) => {
                    s.bind_value(kb, vid, extract_value_at_path(kb, fact_head, &path))
                }
                BindValue::Value(v) => s.bind_value(kb, vid, v),
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

    fn resolve_leaf(self, kb: &KnowledgeBase, fact_term: TermId) -> Substitution {
        let mut s = Substitution::new();
        let mut cur = &self.head;
        while let Some(cell) = cur {
            match &cell.value {
                BindValue::Term(tid) => s.bind_term(kb, cell.var, *tid),
                BindValue::Path(path) => {
                    s.bind_term(kb, cell.var, extract_at_path(&kb.terms, fact_term, path))
                }
                BindValue::Value(v) => s.bind_value(kb, cell.var, v.clone()),
            }
            cur = &cell.tail;
        }
        s
    }

    fn resolve_leaf_view(self, kb: &KnowledgeBase, fact_head: &Value) -> Substitution {
        let mut s = Substitution::new();
        let mut cur = &self.head;
        while let Some(cell) = cur {
            match &cell.value {
                BindValue::Term(tid) => s.bind_term(kb, cell.var, *tid),
                BindValue::Path(path) => {
                    s.bind_value(kb, cell.var, extract_value_at_path(kb, fact_head, path))
                }
                BindValue::Value(v) => s.bind_value(kb, cell.var, v.clone()),
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
    use super::super::term::{Literal, Term, TermId};

    // WI-486: `resolve_leaf` now takes `&KnowledgeBase` (its bind/path-extract
    // need the carrier-aware comparator + the kb's term store), so the fixture
    // wraps a real KB rather than a bare `TermStore`.
    struct TestEnv {
        kb: KnowledgeBase,
        next_var: u32,
    }

    impl TestEnv {
        fn new() -> Self {
            TestEnv { kb: KnowledgeBase::new(), next_var: 0 }
        }
        fn intern(&mut self, s: &str) -> Symbol { self.kb.intern(s) }
        fn alloc(&mut self, term: Term) -> TermId { self.kb.alloc(term) }
        fn fresh_var(&mut self, name: &str) -> VarId {
            let sym = self.kb.intern(name);
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
        let sub = s.resolve_leaf(&env.kb, TermId::from_raw(0));
        assert_eq!(sub.resolve_as_value(vid).map(|v| v.expect_term()), Some(tid));
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
            .with_binding(vid, BindValue::Path(VarPath::root().appended(ArgPos::Positional(0))));
        let sub = s.resolve_leaf(&env.kb, fact_term);
        assert_eq!(sub.resolve_as_value(vid).map(|v| v.expect_term()), Some(val));
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

        let sub1 = s1.resolve_leaf(&env.kb, TermId::from_raw(0));
        assert_eq!(sub1.resolve_as_value(vid1).map(|v| v.expect_term()), Some(tid));
        assert!(sub1.resolve_as_value(vid2).is_none());

        let sub2 = s2.resolve_leaf(&env.kb, TermId::from_raw(0));
        assert_eq!(sub2.resolve_as_value(vid1).map(|v| v.expect_term()), Some(tid));
        assert_eq!(sub2.resolve_as_value(vid2).map(|v| v.expect_term()), Some(tid));
    }

    #[test]
    fn shared_subst_resolve_leaf() {
        let mut env = TestEnv::new();
        let vid = env.fresh_var("x");
        let tid = env.alloc(Term::Const(Literal::Int(42)));

        let s = SharedSubst::new()
            .with_binding(vid, BindValue::Term(tid));
        let sub = s.resolve_leaf(&env.kb, TermId::from_raw(0));
        assert_eq!(sub.resolve_as_value(vid).map(|v| v.expect_term()), Some(tid));
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

        let sub1 = s1.resolve_leaf(&env.kb, TermId::from_raw(0));
        assert!(sub1.resolve_as_value(vid2).is_none());

        let sub2 = s2.resolve_leaf(&env.kb, TermId::from_raw(0));
        assert_eq!(sub2.resolve_as_value(vid1).map(|v| v.expect_term()), Some(tid));
        assert_eq!(sub2.resolve_as_value(vid2).map(|v| v.expect_term()), Some(tid));
    }

    // ── Path extraction tests ───────────────────────────────────

    #[test]
    fn extract_at_path_root() {
        let mut env = TestEnv::new();
        let tid = env.alloc(Term::Const(Literal::Int(42)));
        assert_eq!(extract_at_path(&env.kb.terms, tid, &VarPath::root()), tid);
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
        assert_eq!(extract_at_path(&env.kb.terms, term, &VarPath::root().appended(ArgPos::Positional(0))), val0);
        assert_eq!(extract_at_path(&env.kb.terms, term, &VarPath::root().appended(ArgPos::Positional(1))), val1);
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
        assert_eq!(extract_at_path(&env.kb.terms, term, &VarPath::root().appended(ArgPos::Named(k_sym))), val);
    }

    #[test]
    fn extract_at_path_nested() {
        // f(g(inner)) — a two-step path [Positional(0), Positional(0)]
        // descends into the nested compound to reach `inner` (WI-373 gap 3).
        let mut env = TestEnv::new();
        let f_sym = env.intern("f");
        let g_sym = env.intern("g");
        let inner = env.alloc(Term::Const(Literal::Int(7)));
        let g = env.alloc(Term::Fn {
            functor: g_sym, pos_args: SmallVec::from_elem(inner, 1), named_args: SmallVec::new(),
        });
        let f = env.alloc(Term::Fn {
            functor: f_sym, pos_args: SmallVec::from_elem(g, 1), named_args: SmallVec::new(),
        });
        let path = VarPath::root()
            .appended(ArgPos::Positional(0))
            .appended(ArgPos::Positional(0));
        assert_eq!(extract_at_path(&env.kb.terms, f, &path), inner);
        // One step short reaches the intermediate g(inner).
        assert_eq!(extract_at_path(&env.kb.terms, f, &VarPath::root().appended(ArgPos::Positional(0))), g);
    }
}
