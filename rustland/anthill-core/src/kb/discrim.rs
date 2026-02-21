/// Substitution Tree — discrimination tree with variable binding.
///
/// A multi-level index over terms that collects variable bindings during
/// traversal. At each leaf, the stored data is immediately usable with the
/// accumulated substitution.
///
/// Two edge types at each node:
/// - **Concrete edges** (`HashMap<DiscrimKey, Node>`): dispatch on specific value
/// - **Variable edges** (`Vec<(VarId, Node)>`): match anything, bind VarId
///
/// See: docs/stage0/rust-term-store-design.md §7.6

use std::collections::HashMap;
use std::sync::Arc;

use smallvec::SmallVec;

use crate::intern::Symbol;
use super::subst::Substitution;
use super::term::{FnArg, Literal, Term, TermId, TermStore, VarId};

// ── DiscrimKey — concrete edge labels ───────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum DiscrimKey {
    /// Top-level functor of a Fn term
    Functor(Symbol),
    /// Argument count
    Arity(u16),
    /// Named argument label (emitted before the value key)
    NamedKey(Symbol),
    /// Positional argument marker (emitted before the value key)
    Positional,
    /// Literal constant value
    Lit(Literal),
    /// Ident(sym) term
    Ident(Symbol),
    /// Ref(sym) term
    Ref(Symbol),
    /// Nested Fn — one level deep (functor + arity, not recursive)
    FnRef { functor: Symbol, arity: u16 },
    /// Bottom term
    Bottom,
}

// ── PatternKey — used during pattern insertion ──────────────────

enum PatternKey {
    Concrete(DiscrimKey),
    Bind(VarId),
}

// ── QueryKey — used during query traversal ──────────────────────

enum QueryKey {
    Concrete(DiscrimKey),
    /// Query position is a variable — follow all edges, bind this VarId
    Var(VarId),
}

// ── PersistSubst — persistent substitution trait ────────────────

/// Persistent substitution for tree traversal.
///
/// `clone()` forks the substitution at branch points.
/// `with_binding()` consumes self and returns a new value with the binding added.
/// For SmallVec: push and return self. For Chain: prepend new Arc cell.
pub(crate) trait PersistSubst: Clone {
    fn new() -> Self;
    /// Add a binding, consuming self and returning the extended substitution.
    fn with_binding(self, var: VarId, term: TermId) -> Self;
    fn resolve(&self, var: VarId) -> Option<TermId>;
    fn into_substitution(self) -> Substitution;
}

// ── SmallSubst — SmallVec-based (clone = memcpy) ────────────────

#[derive(Clone)]
pub(crate) struct SmallSubst {
    bindings: SmallVec<[(VarId, TermId); 8]>,
}

impl PersistSubst for SmallSubst {
    fn new() -> Self {
        SmallSubst {
            bindings: SmallVec::new(),
        }
    }

    fn with_binding(mut self, var: VarId, term: TermId) -> Self {
        self.bindings.push((var, term));
        self
    }

    fn resolve(&self, var: VarId) -> Option<TermId> {
        self.bindings.iter().rev().find(|(v, _)| *v == var).map(|(_, t)| *t)
    }

    fn into_substitution(self) -> Substitution {
        let mut s = Substitution::new();
        for (v, t) in self.bindings {
            s.bind(v, t);
        }
        s
    }
}

// ── SharedSubst — Arc cons-list (clone = refcount bump, O(1)) ──

struct SubstCell {
    var: VarId,
    term: TermId,
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

    fn with_binding(self, var: VarId, term: TermId) -> Self {
        SharedSubst {
            head: Some(Arc::new(SubstCell {
                var,
                term,
                tail: self.head,
            })),
        }
    }

    fn resolve(&self, var: VarId) -> Option<TermId> {
        let mut cur = &self.head;
        while let Some(cell) = cur {
            if cell.var == var {
                return Some(cell.term);
            }
            cur = &cell.tail;
        }
        None
    }

    fn into_substitution(self) -> Substitution {
        let mut s = Substitution::new();
        let mut cur = &self.head;
        // Walk the list and collect bindings (earliest binding wins for HashMap)
        let mut pairs = SmallVec::<[(VarId, TermId); 8]>::new();
        while let Some(cell) = cur {
            pairs.push((cell.var, cell.term));
            cur = &cell.tail;
        }
        // Insert in reverse so earliest (outermost) binding is overwritten by latest
        for (v, t) in pairs {
            s.bind(v, t);
        }
        s
    }
}

// ── DiscrimNode — tree node ─────────────────────────────────────

struct DiscrimNode<L> {
    /// Concrete dispatch edges
    concrete: HashMap<DiscrimKey, DiscrimNode<L>>,
    /// Variable-binding edges: when traversed, VarId is bound to query value
    var_edges: Vec<(VarId, DiscrimNode<L>)>,
    /// Leaf data at end of a complete key path
    leaves: Vec<L>,
}

impl<L> DiscrimNode<L> {
    fn new() -> Self {
        DiscrimNode {
            concrete: HashMap::new(),
            var_edges: Vec::new(),
            leaves: Vec::new(),
        }
    }

    fn is_empty(&self) -> bool {
        self.concrete.is_empty() && self.var_edges.is_empty() && self.leaves.is_empty()
    }
}

// ── SubstTree — top-level structure ─────────────────────────────

pub(crate) struct SubstTree<L> {
    root: DiscrimNode<L>,
}

impl<L> SubstTree<L> {
    pub(crate) fn new() -> Self {
        SubstTree {
            root: DiscrimNode::new(),
        }
    }
}

// ── Key extraction ──────────────────────────────────────────────

/// Extract concrete keys from a ground term (for fact indexing).
fn extract_keys(terms: &TermStore, term_id: TermId) -> Vec<DiscrimKey> {
    let mut keys = Vec::new();
    extract_keys_into(terms, term_id, &mut keys);
    keys
}

fn extract_keys_into(terms: &TermStore, term_id: TermId, keys: &mut Vec<DiscrimKey>) {
    match terms.get(term_id) {
        Term::Fn { functor, args } => {
            keys.push(DiscrimKey::Functor(*functor));
            keys.push(DiscrimKey::Arity(args.len() as u16));

            // Separate positional and named args; named sorted by symbol index
            let mut positional = Vec::new();
            let mut named = Vec::new();
            for arg in args.iter() {
                match arg {
                    FnArg::Positional(id) => positional.push(*id),
                    FnArg::Named(sym, id) => named.push((*sym, *id)),
                }
            }
            named.sort_by_key(|(sym, _)| sym.index());

            // Emit positional args first
            for id in positional {
                keys.push(DiscrimKey::Positional);
                extract_arg_value_key(terms, id, keys);
            }
            // Then named args
            for (sym, id) in named {
                keys.push(DiscrimKey::NamedKey(sym));
                extract_arg_value_key(terms, id, keys);
            }
        }
        Term::Const(lit) => {
            keys.push(DiscrimKey::Lit(lit.clone()));
        }
        Term::Ident(sym) => {
            keys.push(DiscrimKey::Ident(*sym));
        }
        Term::Ref(sym) => {
            keys.push(DiscrimKey::Ref(*sym));
        }
        Term::Bottom => {
            keys.push(DiscrimKey::Bottom);
        }
        Term::Var(_) => {
            // Ground extraction should not encounter variables,
            // but be defensive — emit nothing (will not match concrete edges)
        }
        Term::Unspecified { .. } => {
            // Unspecified terms don't participate in indexing
        }
    }
}

/// Extract the key for an argument value (one level deep).
fn extract_arg_value_key(terms: &TermStore, term_id: TermId, keys: &mut Vec<DiscrimKey>) {
    match terms.get(term_id) {
        Term::Const(lit) => {
            keys.push(DiscrimKey::Lit(lit.clone()));
        }
        Term::Ident(sym) => {
            keys.push(DiscrimKey::Ident(*sym));
        }
        Term::Ref(sym) => {
            keys.push(DiscrimKey::Ref(*sym));
        }
        Term::Fn { functor, args } => {
            // One level deep — emit FnRef, not recursive
            keys.push(DiscrimKey::FnRef {
                functor: *functor,
                arity: args.len() as u16,
            });
        }
        Term::Bottom => {
            keys.push(DiscrimKey::Bottom);
        }
        Term::Var(_) => {
            // Should not happen in ground terms
        }
        Term::Unspecified { .. } => {}
    }
}

/// Extract pattern keys (for rule insertion — may contain variable positions).
fn extract_pattern_keys(terms: &TermStore, term_id: TermId) -> Vec<PatternKey> {
    let mut keys = Vec::new();
    extract_pattern_keys_into(terms, term_id, &mut keys);
    keys
}

fn extract_pattern_keys_into(terms: &TermStore, term_id: TermId, keys: &mut Vec<PatternKey>) {
    match terms.get(term_id) {
        Term::Var(vid) => {
            keys.push(PatternKey::Bind(*vid));
        }
        Term::Fn { functor, args } => {
            keys.push(PatternKey::Concrete(DiscrimKey::Functor(*functor)));
            keys.push(PatternKey::Concrete(DiscrimKey::Arity(args.len() as u16)));

            let mut positional = Vec::new();
            let mut named = Vec::new();
            for arg in args.iter() {
                match arg {
                    FnArg::Positional(id) => positional.push(*id),
                    FnArg::Named(sym, id) => named.push((*sym, *id)),
                }
            }
            named.sort_by_key(|(sym, _)| sym.index());

            for id in positional {
                keys.push(PatternKey::Concrete(DiscrimKey::Positional));
                extract_pattern_arg_value(terms, id, keys);
            }
            for (sym, id) in named {
                keys.push(PatternKey::Concrete(DiscrimKey::NamedKey(sym)));
                extract_pattern_arg_value(terms, id, keys);
            }
        }
        Term::Const(lit) => {
            keys.push(PatternKey::Concrete(DiscrimKey::Lit(lit.clone())));
        }
        Term::Ident(sym) => {
            keys.push(PatternKey::Concrete(DiscrimKey::Ident(*sym)));
        }
        Term::Ref(sym) => {
            keys.push(PatternKey::Concrete(DiscrimKey::Ref(*sym)));
        }
        Term::Bottom => {
            keys.push(PatternKey::Concrete(DiscrimKey::Bottom));
        }
        Term::Unspecified { .. } => {}
    }
}

fn extract_pattern_arg_value(terms: &TermStore, term_id: TermId, keys: &mut Vec<PatternKey>) {
    match terms.get(term_id) {
        Term::Var(vid) => {
            keys.push(PatternKey::Bind(*vid));
        }
        Term::Const(lit) => {
            keys.push(PatternKey::Concrete(DiscrimKey::Lit(lit.clone())));
        }
        Term::Ident(sym) => {
            keys.push(PatternKey::Concrete(DiscrimKey::Ident(*sym)));
        }
        Term::Ref(sym) => {
            keys.push(PatternKey::Concrete(DiscrimKey::Ref(*sym)));
        }
        Term::Fn { functor, args } => {
            keys.push(PatternKey::Concrete(DiscrimKey::FnRef {
                functor: *functor,
                arity: args.len() as u16,
            }));
        }
        Term::Bottom => {
            keys.push(PatternKey::Concrete(DiscrimKey::Bottom));
        }
        Term::Unspecified { .. } => {}
    }
}

/// Extract query keys from a query term (may contain variables).
fn extract_query_keys(terms: &TermStore, term_id: TermId) -> Vec<QueryKey> {
    let mut keys = Vec::new();
    extract_query_keys_into(terms, term_id, &mut keys);
    keys
}

fn extract_query_keys_into(terms: &TermStore, term_id: TermId, keys: &mut Vec<QueryKey>) {
    match terms.get(term_id) {
        Term::Var(vid) => {
            keys.push(QueryKey::Var(*vid));
        }
        Term::Fn { functor, args } => {
            keys.push(QueryKey::Concrete(DiscrimKey::Functor(*functor)));
            keys.push(QueryKey::Concrete(DiscrimKey::Arity(args.len() as u16)));

            let mut positional = Vec::new();
            let mut named = Vec::new();
            for arg in args.iter() {
                match arg {
                    FnArg::Positional(id) => positional.push(*id),
                    FnArg::Named(sym, id) => named.push((*sym, *id)),
                }
            }
            named.sort_by_key(|(sym, _)| sym.index());

            for id in positional {
                keys.push(QueryKey::Concrete(DiscrimKey::Positional));
                extract_query_arg_value(terms, id, keys);
            }
            for (sym, id) in named {
                keys.push(QueryKey::Concrete(DiscrimKey::NamedKey(sym)));
                extract_query_arg_value(terms, id, keys);
            }
        }
        Term::Const(lit) => {
            keys.push(QueryKey::Concrete(DiscrimKey::Lit(lit.clone())));
        }
        Term::Ident(sym) => {
            keys.push(QueryKey::Concrete(DiscrimKey::Ident(*sym)));
        }
        Term::Ref(sym) => {
            keys.push(QueryKey::Concrete(DiscrimKey::Ref(*sym)));
        }
        Term::Bottom => {
            keys.push(QueryKey::Concrete(DiscrimKey::Bottom));
        }
        Term::Unspecified { .. } => {}
    }
}

fn extract_query_arg_value(terms: &TermStore, term_id: TermId, keys: &mut Vec<QueryKey>) {
    match terms.get(term_id) {
        Term::Var(vid) => {
            keys.push(QueryKey::Var(*vid));
        }
        Term::Const(lit) => {
            keys.push(QueryKey::Concrete(DiscrimKey::Lit(lit.clone())));
        }
        Term::Ident(sym) => {
            keys.push(QueryKey::Concrete(DiscrimKey::Ident(*sym)));
        }
        Term::Ref(sym) => {
            keys.push(QueryKey::Concrete(DiscrimKey::Ref(*sym)));
        }
        Term::Fn { functor, args } => {
            keys.push(QueryKey::Concrete(DiscrimKey::FnRef {
                functor: *functor,
                arity: args.len() as u16,
            }));
        }
        Term::Bottom => {
            keys.push(QueryKey::Concrete(DiscrimKey::Bottom));
        }
        Term::Unspecified { .. } => {}
    }
}

// ── SubstTree operations ────────────────────────────────────────

impl<L> SubstTree<L> {
    /// Insert a ground term (only concrete edges).
    pub(crate) fn insert_ground(&mut self, terms: &TermStore, term_id: TermId, leaf: L) {
        let keys = extract_keys(terms, term_id);
        let mut node = &mut self.root;
        for key in keys {
            node = node.concrete.entry(key).or_insert_with(DiscrimNode::new);
        }
        node.leaves.push(leaf);
    }

    /// Insert a pattern term (may create variable edges).
    #[allow(dead_code)]
    pub(crate) fn insert_pattern(&mut self, terms: &TermStore, pattern_id: TermId, leaf: L) {
        let keys = extract_pattern_keys(terms, pattern_id);
        let mut node = &mut self.root;
        for key in keys {
            match key {
                PatternKey::Concrete(dk) => {
                    node = node.concrete.entry(dk).or_insert_with(DiscrimNode::new);
                }
                PatternKey::Bind(vid) => {
                    // Find or create var_edge for this VarId
                    let pos = node.var_edges.iter().position(|(v, _)| *v == vid);
                    if let Some(idx) = pos {
                        node = &mut node.var_edges[idx].1;
                    } else {
                        node.var_edges.push((vid, DiscrimNode::new()));
                        let last = node.var_edges.len() - 1;
                        node = &mut node.var_edges[last].1;
                    }
                }
            }
        }
        node.leaves.push(leaf);
    }

    /// Remove a ground term's leaf from the tree.
    pub(crate) fn remove_ground(&mut self, terms: &TermStore, term_id: TermId, leaf: &L)
    where
        L: PartialEq,
    {
        let keys = extract_keys(terms, term_id);
        Self::remove_rec(&mut self.root, &keys, 0, leaf);
    }

    /// Recursive removal with upward pruning of empty nodes.
    /// Returns true if the node is now empty and can be pruned.
    fn remove_rec(node: &mut DiscrimNode<L>, keys: &[DiscrimKey], depth: usize, leaf: &L) -> bool
    where
        L: PartialEq,
    {
        if depth == keys.len() {
            // At leaf position: remove the matching leaf
            if let Some(pos) = node.leaves.iter().position(|l| l == leaf) {
                node.leaves.swap_remove(pos);
            }
            return node.is_empty();
        }

        let key = &keys[depth];
        if let Some(child) = node.concrete.get_mut(key) {
            let child_empty = Self::remove_rec(child, keys, depth + 1, leaf);
            if child_empty {
                node.concrete.remove(key);
            }
        }

        node.is_empty()
    }
}

impl<L: Clone> SubstTree<L> {
    /// Query the tree with a term, collecting substitutions along the way.
    ///
    /// Returns all (leaf, substitution) pairs reachable from the query.
    pub(crate) fn query(&self, terms: &TermStore, query_term: TermId) -> Vec<(L, Substitution)> {
        // Bare variable query: matches everything in the tree
        if matches!(terms.get(query_term), Term::Var(_)) {
            let mut results = Vec::new();
            let subst = SmallSubst::new();
            Self::collect_all(&self.root, subst, &mut results);
            return results;
        }

        let query_keys = extract_query_keys(terms, query_term);
        let mut results = Vec::new();
        let subst = SmallSubst::new();
        Self::collect(&self.root, &query_keys, 0, subst, &mut results);
        results
    }

    /// Collect all leaves in the entire subtree (for bare-variable queries).
    fn collect_all<S: PersistSubst>(
        node: &DiscrimNode<L>,
        subst: S,
        results: &mut Vec<(L, Substitution)>,
    ) {
        for leaf in &node.leaves {
            results.push((leaf.clone(), subst.clone().into_substitution()));
        }
        for (_, child) in &node.concrete {
            Self::collect_all(child, subst.clone(), results);
        }
        for (_, child) in &node.var_edges {
            Self::collect_all(child, subst.clone(), results);
        }
    }

    /// Recursive traversal collecting results.
    fn collect<S: PersistSubst>(
        node: &DiscrimNode<L>,
        query_keys: &[QueryKey],
        depth: usize,
        subst: S,
        results: &mut Vec<(L, Substitution)>,
    ) {
        if depth == query_keys.len() {
            // Reached end of query keys — collect leaves
            for leaf in &node.leaves {
                results.push((leaf.clone(), subst.clone().into_substitution()));
            }
            return;
        }

        match &query_keys[depth] {
            QueryKey::Concrete(qk) => {
                // 1. Follow matching concrete edge (no binding)
                if let Some(child) = node.concrete.get(qk) {
                    Self::collect(child, query_keys, depth + 1, subst.clone(), results);
                }

                // 2. Follow ALL var_edges (bind tree's VarId to query value)
                //    The "query value" for a concrete key is the TermId that the
                //    key represents. For structural keys (Functor, Arity, Positional,
                //    NamedKey), var edges don't apply — they only apply at value
                //    positions. We handle this by only following var_edges at
                //    value positions (where the key represents an actual term value).
                if is_value_key(qk) {
                    for (vid, child) in &node.var_edges {
                        // We don't have the original TermId easily here for
                        // binding. For Layer 0, var_edges are only used with
                        // insert_pattern and queries go through match_term
                        // verification. We still follow var_edges but bind
                        // to a placeholder — the real binding comes from
                        // match_term verification.
                        let branch = subst.clone().with_binding(*vid, TermId::from_raw(0));
                        Self::collect(child, query_keys, depth + 1, branch, results);
                    }
                }
            }
            QueryKey::Var(query_vid) => {
                // Query position is a variable — follow ALL concrete edges,
                // binding query's VarId to each.
                // For structural keys this doesn't make sense — only at value positions.
                // But a Var query key means the entire term at this position is a variable,
                // which replaces the whole key sequence for this position.
                // For now, follow ALL concrete edges at this level.
                for (_dk, child) in &node.concrete {
                    // Bind query variable — we don't have the TermId for the
                    // concrete edge here, so bind to placeholder for now.
                    // match_term verification will produce correct bindings.
                    let branch = subst.clone().with_binding(*query_vid, TermId::from_raw(0));
                    Self::collect(child, query_keys, depth + 1, branch, results);
                }

                // Also follow var_edges (bind both)
                for (tree_vid, child) in &node.var_edges {
                    let branch = subst
                        .clone()
                        .with_binding(*query_vid, TermId::from_raw(0))
                        .with_binding(*tree_vid, TermId::from_raw(0));
                    Self::collect(child, query_keys, depth + 1, branch, results);
                }
            }
        }
    }
}

/// Returns true if a DiscrimKey is a "value" key (represents a term value,
/// not a structural marker like Functor/Arity/Positional/NamedKey).
fn is_value_key(key: &DiscrimKey) -> bool {
    matches!(
        key,
        DiscrimKey::Lit(_)
            | DiscrimKey::Ident(_)
            | DiscrimKey::Ref(_)
            | DiscrimKey::FnRef { .. }
            | DiscrimKey::Bottom
    )
}

// ── Tests ───────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intern::Interner;

    /// Helper to build a test KB-like environment.
    struct TestEnv {
        terms: TermStore,
        interner: Interner,
        next_var: u32,
    }

    impl TestEnv {
        fn new() -> Self {
            TestEnv {
                terms: TermStore::new(),
                interner: Interner::new(),
                next_var: 0,
            }
        }

        fn intern(&mut self, s: &str) -> Symbol {
            self.interner.intern(s)
        }

        fn alloc(&mut self, term: Term) -> TermId {
            self.terms.alloc(term)
        }

        fn make_name(&mut self, name: &str) -> TermId {
            let sym = self.interner.intern(name);
            self.terms.alloc(Term::Fn {
                functor: sym,
                args: SmallVec::new(),
            })
        }

        fn fresh_var(&mut self, name: &str) -> VarId {
            let sym = self.interner.intern(name);
            let id = self.next_var;
            self.next_var += 1;
            VarId::new(id, sym)
        }
    }

    // ── Key extraction tests ────────────────────────────────────

    #[test]
    fn extract_keys_nullary_fn() {
        let mut env = TestEnv::new();
        let t = env.make_name("Account");
        let keys = extract_keys(&env.terms, t);
        let account_sym = env.intern("Account");
        assert_eq!(keys, vec![DiscrimKey::Functor(account_sym), DiscrimKey::Arity(0)]);
    }

    #[test]
    fn extract_keys_positional_args() {
        let mut env = TestEnv::new();
        let f_sym = env.intern("f");
        let val1 = env.alloc(Term::Const(Literal::Int(42)));
        let val2 = env.alloc(Term::Const(Literal::String("hello".into())));
        let term = env.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_slice(&[
                FnArg::Positional(val1),
                FnArg::Positional(val2),
            ]),
        });

        let keys = extract_keys(&env.terms, term);
        assert_eq!(
            keys,
            vec![
                DiscrimKey::Functor(f_sym),
                DiscrimKey::Arity(2),
                DiscrimKey::Positional,
                DiscrimKey::Lit(Literal::Int(42)),
                DiscrimKey::Positional,
                DiscrimKey::Lit(Literal::String("hello".into())),
            ]
        );
    }

    #[test]
    fn extract_keys_named_args_canonical_order() {
        let mut env = TestEnv::new();
        let f_sym = env.intern("f");
        // Intern in order so that "name" might get a lower index than "id"
        // or vice versa — the point is they're sorted by symbol index.
        let name_sym = env.intern("name");
        let id_sym = env.intern("id");
        let val_a = env.alloc(Term::Const(Literal::String("A".into())));
        let val_b = env.alloc(Term::Const(Literal::String("B".into())));

        let term = env.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_slice(&[
                FnArg::Named(name_sym, val_a),
                FnArg::Named(id_sym, val_b),
            ]),
        });

        let keys = extract_keys(&env.terms, term);
        // Named args sorted by symbol index
        // name_sym was interned first (index 1), id_sym second (index 2)
        // (f_sym is index 0)
        assert_eq!(keys[0], DiscrimKey::Functor(f_sym));
        assert_eq!(keys[1], DiscrimKey::Arity(2));
        // Should be sorted by sym.index(): name(1) before id(2)
        assert_eq!(keys[2], DiscrimKey::NamedKey(name_sym));
        assert_eq!(keys[3], DiscrimKey::Lit(Literal::String("A".into())));
        assert_eq!(keys[4], DiscrimKey::NamedKey(id_sym));
        assert_eq!(keys[5], DiscrimKey::Lit(Literal::String("B".into())));
    }

    #[test]
    fn extract_keys_nested_fn_ref() {
        let mut env = TestEnv::new();
        let outer_sym = env.intern("outer");
        let inner_sym = env.intern("inner");
        let val = env.alloc(Term::Const(Literal::Int(1)));
        let inner = env.alloc(Term::Fn {
            functor: inner_sym,
            args: SmallVec::from_elem(FnArg::Positional(val), 1),
        });
        let outer = env.alloc(Term::Fn {
            functor: outer_sym,
            args: SmallVec::from_elem(FnArg::Positional(inner), 1),
        });

        let keys = extract_keys(&env.terms, outer);
        assert_eq!(
            keys,
            vec![
                DiscrimKey::Functor(outer_sym),
                DiscrimKey::Arity(1),
                DiscrimKey::Positional,
                DiscrimKey::FnRef {
                    functor: inner_sym,
                    arity: 1,
                },
            ]
        );
    }

    #[test]
    fn extract_keys_non_fn_terms() {
        let mut env = TestEnv::new();

        let lit = env.alloc(Term::Const(Literal::Bool(true)));
        assert_eq!(extract_keys(&env.terms, lit), vec![DiscrimKey::Lit(Literal::Bool(true))]);

        let sym = env.intern("foo");
        let ident = env.alloc(Term::Ident(sym));
        assert_eq!(extract_keys(&env.terms, ident), vec![DiscrimKey::Ident(sym)]);

        let r = env.alloc(Term::Ref(sym));
        assert_eq!(extract_keys(&env.terms, r), vec![DiscrimKey::Ref(sym)]);

        let b = env.alloc(Term::Bottom);
        assert_eq!(extract_keys(&env.terms, b), vec![DiscrimKey::Bottom]);
    }

    // ── Insert ground + query tests ─────────────────────────────

    #[test]
    fn insert_ground_and_exact_query() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();

        let f_sym = env.intern("account");
        let val = env.alloc(Term::Const(Literal::String("A001".into())));
        let term = env.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_elem(FnArg::Positional(val), 1),
        });

        tree.insert_ground(&env.terms, term, 1);

        // Exact same term → should find leaf
        let results = tree.query(&env.terms, term);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, 1);
    }

    #[test]
    fn query_different_arg_finds_nothing() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();

        let f_sym = env.intern("f");
        let val1 = env.alloc(Term::Const(Literal::Int(1)));
        let val2 = env.alloc(Term::Const(Literal::Int(2)));

        let term1 = env.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_elem(FnArg::Positional(val1), 1),
        });
        let term2 = env.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_elem(FnArg::Positional(val2), 1),
        });

        tree.insert_ground(&env.terms, term1, 1);

        let results = tree.query(&env.terms, term2);
        assert!(results.is_empty());
    }

    #[test]
    fn multiple_facts_same_functor() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();

        let f_sym = env.intern("parent");
        let alice = env.alloc(Term::Const(Literal::String("alice".into())));
        let bob = env.alloc(Term::Const(Literal::String("bob".into())));
        let charlie = env.alloc(Term::Const(Literal::String("charlie".into())));

        let fact1 = env.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_slice(&[
                FnArg::Positional(alice),
                FnArg::Positional(bob),
            ]),
        });
        let fact2 = env.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_slice(&[
                FnArg::Positional(bob),
                FnArg::Positional(charlie),
            ]),
        });

        tree.insert_ground(&env.terms, fact1, 1);
        tree.insert_ground(&env.terms, fact2, 2);

        // Query with exact match for fact1
        let results = tree.query(&env.terms, fact1);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, 1);

        // Query with exact match for fact2
        let results = tree.query(&env.terms, fact2);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, 2);
    }

    #[test]
    fn query_with_variable_matches_all() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();

        let f_sym = env.intern("f");
        let val1 = env.alloc(Term::Const(Literal::Int(1)));
        let val2 = env.alloc(Term::Const(Literal::Int(2)));

        let term1 = env.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_elem(FnArg::Positional(val1), 1),
        });
        let term2 = env.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_elem(FnArg::Positional(val2), 1),
        });

        tree.insert_ground(&env.terms, term1, 1);
        tree.insert_ground(&env.terms, term2, 2);

        // Query with variable arg: f(?x)
        let vid = env.fresh_var("x");
        let var_term = env.alloc(Term::Var(vid));
        let pattern = env.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_elem(FnArg::Positional(var_term), 1),
        });

        let results = tree.query(&env.terms, pattern);
        // Variable at arg value position → follows all concrete edges
        assert_eq!(results.len(), 2);
        let leaf_ids: Vec<u32> = results.iter().map(|(l, _)| *l).collect();
        assert!(leaf_ids.contains(&1));
        assert!(leaf_ids.contains(&2));
    }

    #[test]
    fn query_all_variable_matches_everything() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();

        let f_sym = env.intern("f");
        let g_sym = env.intern("g");
        let val = env.alloc(Term::Const(Literal::Int(1)));

        let term_f = env.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_elem(FnArg::Positional(val), 1),
        });
        let term_g = env.alloc(Term::Fn {
            functor: g_sym,
            args: SmallVec::new(),
        });

        tree.insert_ground(&env.terms, term_f, 1);
        tree.insert_ground(&env.terms, term_g, 2);

        // Query with bare variable — should match all
        let vid = env.fresh_var("x");
        let var_query = env.alloc(Term::Var(vid));

        let results = tree.query(&env.terms, var_query);
        assert_eq!(results.len(), 2);
    }

    // ── Remove + pruning tests ──────────────────────────────────

    #[test]
    fn remove_ground_and_prune() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();

        let f_sym = env.intern("f");
        let val = env.alloc(Term::Const(Literal::Int(42)));
        let term = env.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_elem(FnArg::Positional(val), 1),
        });

        tree.insert_ground(&env.terms, term, 1);
        assert_eq!(tree.query(&env.terms, term).len(), 1);

        tree.remove_ground(&env.terms, term, &1);
        assert!(tree.query(&env.terms, term).is_empty());
        // Root should be pruned clean
        assert!(tree.root.is_empty());
    }

    #[test]
    fn remove_one_of_two_leaves() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();

        let f_sym = env.intern("f");
        let val = env.alloc(Term::Const(Literal::Int(1)));
        let term = env.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_elem(FnArg::Positional(val), 1),
        });

        // Two different leaves at same path
        tree.insert_ground(&env.terms, term, 1);
        tree.insert_ground(&env.terms, term, 2);
        assert_eq!(tree.query(&env.terms, term).len(), 2);

        tree.remove_ground(&env.terms, term, &1);
        let results = tree.query(&env.terms, term);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, 2);
    }

    // ── Variable edge (pattern insertion) tests ─────────────────

    #[test]
    fn insert_pattern_with_var_and_query_ground() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();

        let f_sym = env.intern("f");
        let vid = env.fresh_var("x");
        let var_term = env.alloc(Term::Var(vid));

        // Pattern: f(?x) — variable at arg position
        let pattern = env.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_elem(FnArg::Positional(var_term), 1),
        });
        tree.insert_pattern(&env.terms, pattern, 100);

        // Query with ground: f(42)
        let val = env.alloc(Term::Const(Literal::Int(42)));
        let ground = env.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_elem(FnArg::Positional(val), 1),
        });

        let results = tree.query(&env.terms, ground);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, 100);
    }

    #[test]
    fn mixed_concrete_and_var_edges() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();

        let f_sym = env.intern("f");
        let val42 = env.alloc(Term::Const(Literal::Int(42)));

        // Insert ground: f(42) → leaf 1
        let ground = env.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_elem(FnArg::Positional(val42), 1),
        });
        tree.insert_ground(&env.terms, ground, 1);

        // Insert pattern: f(?x) → leaf 2
        let vid = env.fresh_var("x");
        let var_term = env.alloc(Term::Var(vid));
        let pattern = env.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_elem(FnArg::Positional(var_term), 1),
        });
        tree.insert_pattern(&env.terms, pattern, 2);

        // Query with f(42) → should find both (concrete match + var match)
        let results = tree.query(&env.terms, ground);
        assert_eq!(results.len(), 2);
        let leaf_ids: Vec<u32> = results.iter().map(|(l, _)| *l).collect();
        assert!(leaf_ids.contains(&1));
        assert!(leaf_ids.contains(&2));

        // Query with f(99) → should find only the pattern (var edge)
        let val99 = env.alloc(Term::Const(Literal::Int(99)));
        let query99 = env.alloc(Term::Fn {
            functor: f_sym,
            args: SmallVec::from_elem(FnArg::Positional(val99), 1),
        });
        let results = tree.query(&env.terms, query99);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, 2);
    }

    // ── PersistSubst implementation tests ───────────────────────

    #[test]
    fn small_subst_basic() {
        let mut env = TestEnv::new();
        let vid = env.fresh_var("x");
        let tid = env.alloc(Term::Const(Literal::Int(42)));

        let s = SmallSubst::new().with_binding(vid, tid);
        assert_eq!(s.resolve(vid), Some(tid));

        let vid2 = env.fresh_var("y");
        assert_eq!(s.resolve(vid2), None);
    }

    #[test]
    fn small_subst_clone_independence() {
        let mut env = TestEnv::new();
        let vid = env.fresh_var("x");
        let tid1 = env.alloc(Term::Const(Literal::Int(1)));
        let tid2 = env.alloc(Term::Const(Literal::Int(2)));

        let s1 = SmallSubst::new().with_binding(vid, tid1);
        let s2 = s1.clone();
        // s1 is unchanged by s2 operations
        let vid2 = env.fresh_var("y");
        let s2 = s2.with_binding(vid2, tid2);

        assert_eq!(s1.resolve(vid2), None);
        assert_eq!(s2.resolve(vid2), Some(tid2));
    }

    #[test]
    fn shared_subst_basic() {
        let mut env = TestEnv::new();
        let vid = env.fresh_var("x");
        let tid = env.alloc(Term::Const(Literal::Int(42)));

        let s = SharedSubst::new().with_binding(vid, tid);
        assert_eq!(s.resolve(vid), Some(tid));
    }

    #[test]
    fn shared_subst_clone_independence() {
        let mut env = TestEnv::new();
        let vid = env.fresh_var("x");
        let vid2 = env.fresh_var("y");
        let tid1 = env.alloc(Term::Const(Literal::Int(1)));
        let tid2 = env.alloc(Term::Const(Literal::Int(2)));

        let s1 = SharedSubst::new().with_binding(vid, tid1);
        let s2 = s1.clone().with_binding(vid2, tid2);

        // s1 doesn't see vid2
        assert_eq!(s1.resolve(vid2), None);
        // s2 sees both
        assert_eq!(s2.resolve(vid), Some(tid1));
        assert_eq!(s2.resolve(vid2), Some(tid2));
    }

    #[test]
    fn small_subst_into_substitution() {
        let mut env = TestEnv::new();
        let vid = env.fresh_var("x");
        let tid = env.alloc(Term::Const(Literal::Int(42)));

        let s = SmallSubst::new().with_binding(vid, tid);
        let sub = s.into_substitution();
        assert_eq!(sub.resolve(vid), Some(tid));
    }

    #[test]
    fn shared_subst_into_substitution() {
        let mut env = TestEnv::new();
        let vid = env.fresh_var("x");
        let tid = env.alloc(Term::Const(Literal::Int(42)));

        let s = SharedSubst::new().with_binding(vid, tid);
        let sub = s.into_substitution();
        assert_eq!(sub.resolve(vid), Some(tid));
    }
}
