/// Unified KnowledgeBase — hash-consed terms, facts, indexes, sort lattice.
///
/// One struct maintains everything. Sort relations are facts; subsort
/// indexes are materialized alongside other indexes.
///
/// See: docs/stage0/rust-term-store-design.md §7, §9 (Layer 0)

pub mod term;
pub mod subst;
pub mod load;

use std::collections::HashMap;

use crate::intern::{Interner, Symbol};
use term::{Term, TermId, TermStore, VarId};

// ── Fact handle ─────────────────────────────────────────────────

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct FactId(u32);

impl FactId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

// ── Fact entry ──────────────────────────────────────────────────

struct FactEntry {
    term: TermId,
    sort: TermId,
    domain: TermId,
    meta: Option<TermId>,
    retracted: bool,
}

// ── Sort kind ───────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SortKind {
    Abstract,
    Defined,
    Constructor,
}

// ── KnowledgeBase ───────────────────────────────────────────────

pub struct KnowledgeBase {
    // Term storage (hash-consed, refcounted)
    pub(crate) terms: TermStore,
    pub(crate) interner: Interner,

    // Facts
    facts: Vec<FactEntry>,

    // Indexes — all maintained atomically by assert/retract
    by_sort: HashMap<TermId, Vec<FactId>>,
    by_functor: HashMap<Symbol, Vec<FactId>>,

    // Sort indexes (subsort relations are facts; these are materialized indexes)
    subsort_children: HashMap<TermId, Vec<TermId>>,
    subsort_parents: HashMap<TermId, Vec<TermId>>,
    sort_info: HashMap<TermId, SortKind>,

    // Variable counter for fresh VarId allocation
    next_var: u32,

    // Well-known sort terms (cached for future layers)
    #[allow(dead_code)]
    sort_sort: Option<TermId>,
    #[allow(dead_code)]
    subsort_sort: Option<TermId>,
}

impl KnowledgeBase {
    pub fn new() -> Self {
        Self {
            terms: TermStore::new(),
            interner: Interner::new(),
            facts: Vec::new(),
            by_sort: HashMap::new(),
            by_functor: HashMap::new(),
            subsort_children: HashMap::new(),
            subsort_parents: HashMap::new(),
            sort_info: HashMap::new(),
            next_var: 0,
            sort_sort: None,
            subsort_sort: None,
        }
    }

    // ── Term allocation ─────────────────────────────────────────

    /// Allocate a term (hash-consed, refcounted).
    pub fn alloc(&mut self, term: Term) -> TermId {
        self.terms.alloc(term)
    }

    /// Intern a string, returning a Symbol.
    pub fn intern(&mut self, s: &str) -> Symbol {
        self.interner.intern(s)
    }

    /// Allocate a fresh logic variable id, carrying the display name.
    pub fn fresh_var(&mut self, name: Symbol) -> VarId {
        let id = self.next_var;
        self.next_var += 1;
        VarId::new(id, name)
    }

    /// Resolve a Symbol back to a string.
    pub fn resolve_sym(&self, sym: Symbol) -> &str {
        self.interner.resolve(sym)
    }

    /// Get the Term for a TermId.
    pub fn get_term(&self, id: TermId) -> &Term {
        self.terms.get(id)
    }

    // ── Fact assertion / retraction ─────────────────────────────

    /// Assert a fact into the KB. Updates all indexes.
    pub fn assert_fact(
        &mut self,
        term: TermId,
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> FactId {
        let fact_id = FactId(self.facts.len() as u32);

        // Incref on all referenced terms
        self.terms.incref(term);
        self.terms.incref(sort);
        self.terms.incref(domain);
        if let Some(m) = meta {
            self.terms.incref(m);
        }

        self.facts.push(FactEntry {
            term,
            sort,
            domain,
            meta,
            retracted: false,
        });

        // Update indexes
        self.by_sort.entry(sort).or_default().push(fact_id);

        // Index by top-level functor
        if let Term::Fn { functor, .. } = *self.terms.get(term) {
            self.by_functor.entry(functor).or_default().push(fact_id);
        }

        fact_id
    }

    /// Mark a fact as retracted. Removes from active indexes, decrements refcounts.
    pub fn retract(&mut self, fact_id: FactId) {
        let entry = &mut self.facts[fact_id.index()];
        if entry.retracted {
            return;
        }
        entry.retracted = true;

        let term = entry.term;
        let sort = entry.sort;
        let domain = entry.domain;
        let meta = entry.meta;

        // Remove from indexes
        if let Some(v) = self.by_sort.get_mut(&sort) {
            v.retain(|&id| id != fact_id);
        }
        if let Term::Fn { functor, .. } = *self.terms.get(term) {
            if let Some(v) = self.by_functor.get_mut(&functor) {
                v.retain(|&id| id != fact_id);
            }
        }

        // Release refcounts
        self.terms.release(term);
        self.terms.release(sort);
        self.terms.release(domain);
        if let Some(m) = meta {
            self.terms.release(m);
        }
    }

    // ── Sort management ─────────────────────────────────────────

    /// Register a sort term with its kind.
    pub fn register_sort(&mut self, sort_term: TermId, kind: SortKind) {
        self.sort_info.insert(sort_term, kind);
    }

    /// Register a subsort relationship: child < parent.
    /// Also asserts a Subsort fact in the KB.
    pub fn register_subsort(&mut self, child: TermId, parent: TermId) {
        self.subsort_children
            .entry(parent)
            .or_default()
            .push(child);
        self.subsort_parents
            .entry(child)
            .or_default()
            .push(parent);
    }

    /// Check if `sub` is a subtype of `sup` (transitive).
    pub fn is_subtype(&self, sub: TermId, sup: TermId) -> bool {
        if sub == sup {
            return true;
        }
        // BFS/DFS up the parent chain from sub
        let mut visited = Vec::new();
        let mut stack = vec![sub];
        while let Some(current) = stack.pop() {
            if current == sup {
                return true;
            }
            if visited.contains(&current) {
                continue;
            }
            visited.push(current);
            if let Some(parents) = self.subsort_parents.get(&current) {
                stack.extend(parents.iter().copied());
            }
        }
        false
    }

    // ── Query ───────────────────────────────────────────────────

    /// All active facts of a given sort (including subsorts).
    pub fn by_sort(&self, sort: TermId) -> Vec<FactId> {
        let mut result = Vec::new();

        // Direct facts of this sort
        if let Some(facts) = self.by_sort.get(&sort) {
            for &fid in facts {
                if !self.facts[fid.index()].retracted {
                    result.push(fid);
                }
            }
        }

        // Facts of subsorts
        let mut stack: Vec<TermId> = Vec::new();
        if let Some(children) = self.subsort_children.get(&sort) {
            stack.extend(children.iter().copied());
        }
        while let Some(child) = stack.pop() {
            if let Some(facts) = self.by_sort.get(&child) {
                for &fid in facts {
                    if !self.facts[fid.index()].retracted {
                        result.push(fid);
                    }
                }
            }
            if let Some(grandchildren) = self.subsort_children.get(&child) {
                stack.extend(grandchildren.iter().copied());
            }
        }

        result
    }

    /// All active facts with a given top-level functor symbol.
    pub fn by_functor(&self, sym: Symbol) -> Vec<FactId> {
        self.by_functor
            .get(&sym)
            .map(|v| {
                v.iter()
                    .copied()
                    .filter(|fid| !self.facts[fid.index()].retracted)
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Get the term of a fact.
    pub fn fact_term(&self, fact_id: FactId) -> TermId {
        self.facts[fact_id.index()].term
    }

    /// Get the sort of a fact.
    pub fn fact_sort(&self, fact_id: FactId) -> TermId {
        self.facts[fact_id.index()].sort
    }

    /// Get the domain of a fact.
    pub fn fact_domain(&self, fact_id: FactId) -> TermId {
        self.facts[fact_id.index()].domain
    }

    /// Get sort kind info.
    pub fn sort_kind(&self, sort_term: TermId) -> Option<SortKind> {
        self.sort_info.get(&sort_term).copied()
    }

    /// Get immediate children sorts.
    pub fn sort_children(&self, sort_term: TermId) -> &[TermId] {
        self.subsort_children
            .get(&sort_term)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Number of active (non-retracted) facts.
    pub fn fact_count(&self) -> usize {
        self.facts.iter().filter(|f| !f.retracted).count()
    }

    // ── Pattern matching ─────────────────────────────────────────

    /// One-way unification: match `pattern` against `target`.
    ///
    /// Variables in the pattern bind to subterms of the target.
    /// Variables in the target are treated as opaque (not unified).
    /// Returns `Some(subst)` on success, `None` on failure.
    pub fn match_term(&self, pattern: TermId, target: TermId) -> Option<subst::Substitution> {
        let mut s = subst::Substitution::new();
        if self.match_term_rec(pattern, target, &mut s) {
            Some(s)
        } else {
            None
        }
    }

    fn match_term_rec(
        &self,
        pattern: TermId,
        target: TermId,
        subst: &mut subst::Substitution,
    ) -> bool {
        // If same TermId (hash-consed), they're structurally equal
        if pattern == target {
            return true;
        }

        match self.terms.get(pattern) {
            Term::Var(vid) => {
                // Variable in pattern: bind or check consistency
                if let Some(bound) = subst.resolve(*vid) {
                    // Already bound — must match the same target
                    bound == target
                } else {
                    subst.bind(*vid, target);
                    true
                }
            }
            Term::Const(lit_p) => {
                // Constants must be equal
                match self.terms.get(target) {
                    Term::Const(lit_t) => lit_p == lit_t,
                    _ => false,
                }
            }
            Term::Fn { functor: f_p, args: args_p } => {
                match self.terms.get(target) {
                    Term::Fn { functor: f_t, args: args_t } => {
                        if f_p != f_t || args_p.len() != args_t.len() {
                            return false;
                        }
                        for (ap, at) in args_p.iter().zip(args_t.iter()) {
                            let (pid, tid) = match (ap, at) {
                                (term::FnArg::Positional(p), term::FnArg::Positional(t)) => (*p, *t),
                                (term::FnArg::Named(kp, p), term::FnArg::Named(kt, t)) => {
                                    if kp != kt {
                                        return false;
                                    }
                                    (*p, *t)
                                }
                                _ => return false, // positional vs named mismatch
                            };
                            if !self.match_term_rec(pid, tid, subst) {
                                return false;
                            }
                        }
                        true
                    }
                    _ => false,
                }
            }
            Term::Ident(sym_p) => {
                match self.terms.get(target) {
                    Term::Ident(sym_t) => sym_p == sym_t,
                    _ => false,
                }
            }
            Term::Ref(sym_p) => {
                match self.terms.get(target) {
                    Term::Ref(sym_t) => sym_p == sym_t,
                    _ => false,
                }
            }
            Term::Bottom => matches!(self.terms.get(target), Term::Bottom),
            Term::Unspecified { .. } => {
                // Unspecified terms don't participate in matching
                false
            }
        }
    }

    /// Find all active facts whose term matches the given pattern.
    ///
    /// Uses the functor index to narrow candidates when the pattern
    /// has a top-level `Fn` functor. Returns matching facts with
    /// their substitutions.
    pub fn query(&self, pattern: TermId) -> Vec<(FactId, subst::Substitution)> {
        // Determine candidate facts via index
        let candidates: Vec<FactId> = match self.terms.get(pattern) {
            Term::Fn { functor, .. } => {
                // Use functor index for efficiency
                self.by_functor
                    .get(functor)
                    .map(|v| {
                        v.iter()
                            .copied()
                            .filter(|fid| !self.facts[fid.index()].retracted)
                            .collect()
                    })
                    .unwrap_or_default()
            }
            Term::Var(_) => {
                // Variable pattern matches everything — scan all facts
                self.facts
                    .iter()
                    .enumerate()
                    .filter(|(_, f)| !f.retracted)
                    .map(|(i, _)| FactId(i as u32))
                    .collect()
            }
            _ => {
                // For other patterns, scan all facts
                self.facts
                    .iter()
                    .enumerate()
                    .filter(|(_, f)| !f.retracted)
                    .map(|(i, _)| FactId(i as u32))
                    .collect()
            }
        };

        let mut results = Vec::new();
        for fid in candidates {
            let fact_term = self.facts[fid.index()].term;
            if let Some(s) = self.match_term(pattern, fact_term) {
                results.push((fid, s));
            }
        }
        results
    }

    // ── Helpers ─────────────────────────────────────────────────

    /// Convenience: allocate a nullary functor term (name with no args).
    pub fn make_name_term(&mut self, name: &str) -> TermId {
        let sym = self.interner.intern(name);
        self.terms.alloc(Term::Fn {
            functor: sym,
            args: smallvec::SmallVec::new(),
        })
    }
}

impl Default for KnowledgeBase {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use term::{FnArg, Literal};
    use smallvec::SmallVec;

    #[test]
    fn assert_and_query_by_sort() {
        let mut kb = KnowledgeBase::new();
        let sort_account = kb.make_name_term("Account");
        let domain = kb.make_name_term("banking");

        let acct1 = {
            let id_sym = kb.intern("account");
            let arg = kb.alloc(Term::Const(Literal::String("A001".into())));
            kb.alloc(Term::Fn {
                functor: id_sym,
                args: SmallVec::from_elem(FnArg::Positional(arg), 1),
            })
        };

        let fid = kb.assert_fact(acct1, sort_account, domain, None);
        let results = kb.by_sort(sort_account);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], fid);
    }

    #[test]
    fn subsort_query_includes_children() {
        let mut kb = KnowledgeBase::new();
        let nat = kb.make_name_term("Nat");
        let zero = kb.make_name_term("zero");
        let domain = kb.make_name_term("test");

        kb.register_sort(nat, SortKind::Defined);
        kb.register_sort(zero, SortKind::Constructor);
        kb.register_subsort(zero, nat);

        // Assert a fact of sort `zero`
        let zero_val = kb.make_name_term("zero");
        let fid = kb.assert_fact(zero_val, zero, domain, None);

        // Query by_sort(Nat) should include the zero fact
        let results = kb.by_sort(nat);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], fid);

        // is_subtype
        assert!(kb.is_subtype(zero, nat));
        assert!(!kb.is_subtype(nat, zero));
    }

    #[test]
    fn retract_removes_from_index() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("T");
        let domain = kb.make_name_term("d");
        let term = kb.alloc(Term::Const(Literal::Int(42)));

        let fid = kb.assert_fact(term, sort, domain, None);
        assert_eq!(kb.by_sort(sort).len(), 1);

        kb.retract(fid);
        assert_eq!(kb.by_sort(sort).len(), 0);
    }

    #[test]
    fn match_term_const() {
        let mut kb = KnowledgeBase::new();
        let a = kb.alloc(Term::Const(Literal::Int(42)));
        let b = kb.alloc(Term::Const(Literal::Int(42)));
        let c = kb.alloc(Term::Const(Literal::Int(99)));

        assert!(kb.match_term(a, b).is_some());
        assert!(kb.match_term(a, c).is_none());
    }

    #[test]
    fn match_term_var_binds() {
        let mut kb = KnowledgeBase::new();
        let x_sym = kb.intern("x");
        let vid = kb.fresh_var(x_sym);
        let var_term = kb.alloc(Term::Var(vid));
        let target = kb.alloc(Term::Const(Literal::Int(42)));

        let s = kb.match_term(var_term, target).expect("should match");
        assert_eq!(s.resolve(vid), Some(target));
    }

    #[test]
    fn match_term_var_consistency() {
        // ?x matches first arg, then must match same value in second arg
        let mut kb = KnowledgeBase::new();
        let x_sym = kb.intern("x");
        let vid = kb.fresh_var(x_sym);
        let var_term = kb.alloc(Term::Var(vid));

        let f_sym = kb.intern("f");
        let val = kb.alloc(Term::Const(Literal::Int(1)));

        // Pattern: f(?x, ?x)
        let pattern = kb.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_slice(&[
                FnArg::Positional(var_term),
                FnArg::Positional(var_term),
            ]),
        });

        // Target: f(1, 1) — should match
        let target_ok = kb.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_slice(&[
                FnArg::Positional(val),
                FnArg::Positional(val),
            ]),
        });
        assert!(kb.match_term(pattern, target_ok).is_some());

        // Target: f(1, 2) — should fail (inconsistent binding for ?x)
        let val2 = kb.alloc(Term::Const(Literal::Int(2)));
        let target_bad = kb.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_slice(&[
                FnArg::Positional(val),
                FnArg::Positional(val2),
            ]),
        });
        assert!(kb.match_term(pattern, target_bad).is_none());
    }

    #[test]
    fn match_term_fn_structure() {
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("f");
        let g = kb.intern("g");
        let val = kb.alloc(Term::Const(Literal::Int(1)));

        let term_f = kb.alloc(Term::Fn {
            functor: f,
            args: SmallVec::from_elem(FnArg::Positional(val), 1),
        });
        let term_g = kb.alloc(Term::Fn {
            functor: g,
            args: SmallVec::from_elem(FnArg::Positional(val), 1),
        });

        // Same functor + args → matches
        assert!(kb.match_term(term_f, term_f).is_some());
        // Different functor → fails
        assert!(kb.match_term(term_f, term_g).is_none());
    }

    #[test]
    fn query_by_pattern() {
        let mut kb = KnowledgeBase::new();
        let fact_sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let parent_sym = kb.intern("parent");

        // Assert parent("alice", "bob") and parent("bob", "charlie")
        let alice = kb.alloc(Term::Const(Literal::String("alice".into())));
        let bob = kb.alloc(Term::Const(Literal::String("bob".into())));
        let charlie = kb.alloc(Term::Const(Literal::String("charlie".into())));

        let fact1 = kb.alloc(Term::Fn {
            functor: parent_sym,
            args: SmallVec::from_slice(&[
                FnArg::Positional(alice),
                FnArg::Positional(bob),
            ]),
        });
        let fact2 = kb.alloc(Term::Fn {
            functor: parent_sym,
            args: SmallVec::from_slice(&[
                FnArg::Positional(bob),
                FnArg::Positional(charlie),
            ]),
        });

        kb.assert_fact(fact1, fact_sort, domain, None);
        kb.assert_fact(fact2, fact_sort, domain, None);

        // Query: parent(?x, "bob") — should find only fact1
        let x_sym = kb.intern("x");
        let vid = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(vid));
        let pattern = kb.alloc(Term::Fn {
            functor: parent_sym,
            args: SmallVec::from_slice(&[
                FnArg::Positional(var_x),
                FnArg::Positional(bob),
            ]),
        });

        let results = kb.query(pattern);
        assert_eq!(results.len(), 1);
        let (_, ref s) = results[0];
        assert_eq!(s.resolve(vid), Some(alice));
    }
}
