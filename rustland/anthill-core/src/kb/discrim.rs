/// Substitution Tree — discrimination tree with variable binding.
///
/// A multi-level index over terms. Query traversal is driven directly by the
/// query term's structure (no intermediate key extraction). At variable
/// positions, all subtrees are explored; bindings are recorded as `VarPath`
/// and resolved at the leaf from the fact term.
///
/// Two edge types at each node:
/// - **Concrete edges** (`HashMap<DiscrimKey, Node>`): dispatch on specific value
/// - **Variable edges** (`Vec<(VarId, Node)>`): match anything, bind VarId
///
/// See: docs/stage0/rust-term-store-design.md §7.6

use std::collections::HashMap;

use crate::intern::Symbol;
use super::persist_subst::{ArgPos, BindValue, PersistSubst, SmallSubst, VarPath};
use super::subst::Substitution;
use super::term::{Literal, Term, TermId, TermStore, Var, VarId};

// ── DiscrimKey — concrete edge labels ───────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum DiscrimKey {
    Functor(Symbol),
    Arity(u16),
    NamedKey(Symbol),
    Positional,
    Lit(Literal),
    Ident(Symbol),
    Ref(Symbol),
    Bottom,
}

// ── DiscrimNode — tree node ─────────────────────────────────────

struct DiscrimNode<L> {
    concrete: HashMap<DiscrimKey, DiscrimNode<L>>,
    var_edges: Vec<(VarId, DiscrimNode<L>)>,
    leaves: Vec<L>,
}

impl<L> DiscrimNode<L> {
    fn new() -> Self {
        DiscrimNode { concrete: HashMap::new(), var_edges: Vec::new(), leaves: Vec::new() }
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
        SubstTree { root: DiscrimNode::new() }
    }
}

// ── Term-driven insert ──────────────────────────────────────────

impl<L> SubstTree<L> {
    #[allow(dead_code)]
    pub(crate) fn insert_ground(&mut self, terms: &TermStore, term_id: TermId, leaf: L) {
        let node = Self::insert_walk(&mut self.root, terms, term_id);
        node.leaves.push(leaf);
    }

    /// Walk the term structure, creating concrete edges. Returns the final node.
    fn insert_walk<'a>(
        node: &'a mut DiscrimNode<L>,
        terms: &TermStore,
        term_id: TermId,
    ) -> &'a mut DiscrimNode<L> {
        match terms.get(term_id) {
            Term::Fn { functor, pos_args, named_args } => {
                let functor = *functor;
                let pos_args = pos_args.clone();
                let named_args = named_args.clone();
                let arity = pos_args.len() + named_args.len();
                let n = node.concrete.entry(DiscrimKey::Functor(functor))
                    .or_insert_with(DiscrimNode::new);
                let n = n.concrete.entry(DiscrimKey::Arity(arity as u16))
                    .or_insert_with(DiscrimNode::new);
                Self::insert_walk_args(n, terms, &pos_args, &named_args)
            }
            Term::Const(lit) => {
                node.concrete.entry(DiscrimKey::Lit(lit.clone()))
                    .or_insert_with(DiscrimNode::new)
            }
            Term::Ident(sym) => {
                node.concrete.entry(DiscrimKey::Ident(*sym))
                    .or_insert_with(DiscrimNode::new)
            }
            Term::Ref(sym) => {
                node.concrete.entry(DiscrimKey::Ref(*sym))
                    .or_insert_with(DiscrimNode::new)
            }
            Term::Bottom => {
                node.concrete.entry(DiscrimKey::Bottom)
                    .or_insert_with(DiscrimNode::new)
            }
            Term::Var(_) => node,
        }
    }

    fn insert_walk_args<'a>(
        node: &'a mut DiscrimNode<L>,
        terms: &TermStore,
        positional: &[TermId],
        named: &[(Symbol, TermId)],
    ) -> &'a mut DiscrimNode<L> {
        let mut cur = node;
        for &id in positional {
            cur = cur.concrete.entry(DiscrimKey::Positional)
                .or_insert_with(DiscrimNode::new);
            cur = Self::insert_walk(cur, terms, id);
        }
        for &(sym, id) in named {
            cur = cur.concrete.entry(DiscrimKey::NamedKey(sym))
                .or_insert_with(DiscrimNode::new);
            cur = Self::insert_walk(cur, terms, id);
        }
        cur
    }

    pub(crate) fn insert_pattern(&mut self, terms: &TermStore, pattern_id: TermId, leaf: L) {
        let node = Self::insert_pattern_walk(&mut self.root, terms, pattern_id);
        node.leaves.push(leaf);
    }

    fn insert_pattern_walk<'a>(
        node: &'a mut DiscrimNode<L>,
        terms: &TermStore,
        term_id: TermId,
    ) -> &'a mut DiscrimNode<L> {
        match terms.get(term_id) {
            Term::Var(Var::Global(vid)) => {
                let vid = *vid;
                let pos = node.var_edges.iter().position(|(v, _)| *v == vid);
                if let Some(idx) = pos {
                    &mut node.var_edges[idx].1
                } else {
                    node.var_edges.push((vid, DiscrimNode::new()));
                    let last = node.var_edges.len() - 1;
                    &mut node.var_edges[last].1
                }
            }
            Term::Var(Var::DeBruijn(_)) => node,
            Term::Fn { functor, pos_args, named_args } => {
                let functor = *functor;
                let pos_args = pos_args.clone();
                let named_args = named_args.clone();
                let arity = pos_args.len() + named_args.len();
                let n = node.concrete.entry(DiscrimKey::Functor(functor))
                    .or_insert_with(DiscrimNode::new);
                let n = n.concrete.entry(DiscrimKey::Arity(arity as u16))
                    .or_insert_with(DiscrimNode::new);
                Self::insert_pattern_walk_args(n, terms, &pos_args, &named_args)
            }
            Term::Const(lit) => {
                node.concrete.entry(DiscrimKey::Lit(lit.clone()))
                    .or_insert_with(DiscrimNode::new)
            }
            Term::Ident(sym) => {
                node.concrete.entry(DiscrimKey::Ident(*sym))
                    .or_insert_with(DiscrimNode::new)
            }
            Term::Ref(sym) => {
                node.concrete.entry(DiscrimKey::Ref(*sym))
                    .or_insert_with(DiscrimNode::new)
            }
            Term::Bottom => {
                node.concrete.entry(DiscrimKey::Bottom)
                    .or_insert_with(DiscrimNode::new)
            }
        }
    }

    fn insert_pattern_walk_args<'a>(
        node: &'a mut DiscrimNode<L>,
        terms: &TermStore,
        positional: &[TermId],
        named: &[(Symbol, TermId)],
    ) -> &'a mut DiscrimNode<L> {
        let mut cur = node;
        for &id in positional {
            cur = cur.concrete.entry(DiscrimKey::Positional)
                .or_insert_with(DiscrimNode::new);
            cur = Self::insert_pattern_walk(cur, terms, id);
        }
        for &(sym, id) in named {
            cur = cur.concrete.entry(DiscrimKey::NamedKey(sym))
                .or_insert_with(DiscrimNode::new);
            cur = Self::insert_pattern_walk(cur, terms, id);
        }
        cur
    }

    // ── Term-driven remove ──────────────────────────────────────

    pub(crate) fn remove_ground(&mut self, terms: &TermStore, term_id: TermId, leaf: &L)
    where L: PartialEq,
    {
        Self::remove_walk_term(&mut self.root, terms, term_id, leaf);
    }

    /// Walk the term structure to find and remove a leaf, pruning empty nodes.
    fn remove_walk_term(
        node: &mut DiscrimNode<L>,
        terms: &TermStore,
        term_id: TermId,
        leaf: &L,
    ) -> bool
    where L: PartialEq,
    {
        match terms.get(term_id) {
            Term::Fn { functor, pos_args, named_args } => {
                let functor = *functor;
                let pos_args = pos_args.clone();
                let named_args = named_args.clone();
                let arity = pos_args.len() + named_args.len();
                let fk = DiscrimKey::Functor(functor);
                let prune_fn = if let Some(fn_child) = node.concrete.get_mut(&fk) {
                    let ak = DiscrimKey::Arity(arity as u16);
                    let prune_ar = if let Some(ar_child) = fn_child.concrete.get_mut(&ak) {
                        let mut arg_seq: Vec<(DiscrimKey, TermId)> = Vec::new();
                        for &id in &pos_args {
                            arg_seq.push((DiscrimKey::Positional, id));
                        }
                        for &(sym, id) in &named_args {
                            arg_seq.push((DiscrimKey::NamedKey(sym), id));
                        }
                        Self::remove_walk_args(ar_child, terms, &arg_seq, 0, leaf)
                    } else { false };
                    if prune_ar { fn_child.concrete.remove(&ak); }
                    fn_child.is_empty()
                } else { false };
                if prune_fn { node.concrete.remove(&fk); }
                node.is_empty()
            }
            Term::Const(lit) => Self::remove_at_leaf_key(node, DiscrimKey::Lit(lit.clone()), leaf),
            Term::Ident(sym) => Self::remove_at_leaf_key(node, DiscrimKey::Ident(*sym), leaf),
            Term::Ref(sym) => Self::remove_at_leaf_key(node, DiscrimKey::Ref(*sym), leaf),
            Term::Bottom => Self::remove_at_leaf_key(node, DiscrimKey::Bottom, leaf),
            Term::Var(_) => node.is_empty(),
        }
    }

    /// Remove leaf at a terminal key, prune if empty.
    fn remove_at_leaf_key(
        node: &mut DiscrimNode<L>,
        key: DiscrimKey,
        leaf: &L,
    ) -> bool
    where L: PartialEq,
    {
        if let Some(child) = node.concrete.get_mut(&key) {
            if let Some(pos) = child.leaves.iter().position(|l| l == leaf) {
                child.leaves.swap_remove(pos);
            }
            if child.is_empty() {
                node.concrete.remove(&key);
            }
        }
        node.is_empty()
    }

    /// Walk through arg sequence, one arg at a time, pruning on the way back.
    fn remove_walk_args(
        node: &mut DiscrimNode<L>,
        terms: &TermStore,
        arg_seq: &[(DiscrimKey, TermId)],
        idx: usize,
        leaf: &L,
    ) -> bool
    where L: PartialEq,
    {
        if idx == arg_seq.len() {
            if let Some(pos) = node.leaves.iter().position(|l| l == leaf) {
                node.leaves.swap_remove(pos);
            }
            return node.is_empty();
        }

        let marker = arg_seq[idx].0.clone();
        let arg_term_id = arg_seq[idx].1;
        let prune = if let Some(marker_child) = node.concrete.get_mut(&marker) {
            Self::remove_walk_arg_value(marker_child, terms, arg_term_id, arg_seq, idx, leaf)
        } else { false };
        if prune { node.concrete.remove(&marker); }
        node.is_empty()
    }

    /// Walk a single arg's value, then continue with remaining args.
    fn remove_walk_arg_value(
        node: &mut DiscrimNode<L>,
        terms: &TermStore,
        arg_term_id: TermId,
        arg_seq: &[(DiscrimKey, TermId)],
        idx: usize,
        leaf: &L,
    ) -> bool
    where L: PartialEq,
    {
        match terms.get(arg_term_id) {
            Term::Fn { functor, pos_args, named_args } => {
                let functor = *functor;
                let inner_pos = pos_args.clone();
                let inner_named = named_args.clone();
                let arity = inner_pos.len() + inner_named.len();
                let fk = DiscrimKey::Functor(functor);
                let prune_fn = if let Some(fn_child) = node.concrete.get_mut(&fk) {
                    let ak = DiscrimKey::Arity(arity as u16);
                    let prune_ar = if let Some(ar_child) = fn_child.concrete.get_mut(&ak) {
                        let mut combined: Vec<(DiscrimKey, TermId)> = Vec::new();
                        for &id in &inner_pos {
                            combined.push((DiscrimKey::Positional, id));
                        }
                        for &(sym, id) in &inner_named {
                            combined.push((DiscrimKey::NamedKey(sym), id));
                        }
                        combined.extend_from_slice(&arg_seq[idx + 1..]);
                        Self::remove_walk_args(ar_child, terms, &combined, 0, leaf)
                    } else { false };
                    if prune_ar { fn_child.concrete.remove(&ak); }
                    fn_child.is_empty()
                } else { false };
                if prune_fn { node.concrete.remove(&fk); }
                node.is_empty()
            }
            Term::Const(lit) => {
                Self::remove_value_then_continue(node, DiscrimKey::Lit(lit.clone()), terms, arg_seq, idx, leaf)
            }
            Term::Ident(sym) => {
                Self::remove_value_then_continue(node, DiscrimKey::Ident(*sym), terms, arg_seq, idx, leaf)
            }
            Term::Ref(sym) => {
                Self::remove_value_then_continue(node, DiscrimKey::Ref(*sym), terms, arg_seq, idx, leaf)
            }
            Term::Bottom => {
                Self::remove_value_then_continue(node, DiscrimKey::Bottom, terms, arg_seq, idx, leaf)
            }
            Term::Var(_) => node.is_empty(),
        }
    }

    /// Follow a value key, continue with remaining args, prune if empty.
    fn remove_value_then_continue(
        node: &mut DiscrimNode<L>,
        key: DiscrimKey,
        terms: &TermStore,
        arg_seq: &[(DiscrimKey, TermId)],
        idx: usize,
        leaf: &L,
    ) -> bool
    where L: PartialEq,
    {
        let prune = if let Some(child) = node.concrete.get_mut(&key) {
            Self::remove_walk_args(child, terms, arg_seq, idx + 1, leaf)
        } else { false };
        if prune { node.concrete.remove(&key); }
        node.is_empty()
    }
}

// ── Term-driven query traversal ─────────────────────────────────
//
// Arg processing uses continuation-passing: `on_done` is called when all args
// at one level are matched. For nested Fn in arg position, a closure captures
// the remaining outer args and original `on_done`, chaining naturally for
// arbitrary nesting depth — no temporary Vec allocation needed.

impl<L: Clone> SubstTree<L> {
    pub(crate) fn query_raw(
        &self,
        terms: &TermStore,
        query_term: TermId,
    ) -> Vec<(L, SmallSubst)> {
        let mut results = Vec::new();
        Self::query_node(&self.root, terms, query_term, VarPath::Root, SmallSubst::new(), &mut results);
        results
    }

    pub(crate) fn query_resolved<F>(
        &self,
        terms: &TermStore,
        query_term: TermId,
        resolve_term: F,
    ) -> Vec<(L, Substitution)>
    where
        F: Fn(&L) -> TermId,
    {
        self.query_raw(terms, query_term).into_iter()
            .map(|(leaf, subst)| {
                let fact_term = resolve_term(&leaf);
                let s = subst.resolve_leaf(terms, fact_term);
                (leaf, s)
            })
            .collect()
    }

    fn query_node(
        node: &DiscrimNode<L>,
        terms: &TermStore,
        query_term: TermId,
        path: VarPath,
        subst: SmallSubst,
        results: &mut Vec<(L, SmallSubst)>,
    ) {
        match terms.get(query_term) {
            Term::Var(Var::Global(vid)) => {
                let s = subst.with_binding(*vid, BindValue::Path(path));
                Self::collect_all_leaves(node, s, results);
            }
            Term::Var(Var::DeBruijn(_)) => {
                // DeBruijn vars don't participate in substitution tree queries
            }

            Term::Fn { functor, pos_args, named_args } => {
                let functor = *functor;
                let pos_args = pos_args.clone();
                let named_args = named_args.clone();
                let arity = pos_args.len() + named_args.len();
                if let Some(n1) = node.concrete.get(&DiscrimKey::Functor(functor)) {
                    if let Some(n2) = n1.concrete.get(&DiscrimKey::Arity(arity as u16)) {
                        let collect_leaves = |node: &DiscrimNode<L>, subst: SmallSubst, results: &mut Vec<(L, SmallSubst)>| {
                            for leaf in &node.leaves {
                                results.push((leaf.clone(), subst.clone()));
                            }
                        };
                        Self::query_args(n2, terms, &pos_args, &named_args, 0, true,
                            subst.clone(), results, &collect_leaves);
                    }
                }

                for (tree_vid, child) in &node.var_edges {
                    let branch = subst.clone()
                        .with_binding(*tree_vid, BindValue::Term(query_term));
                    Self::collect_all_leaves(child, branch, results);
                }
            }

            Term::Const(lit) => {
                Self::query_leaf_key(node, &DiscrimKey::Lit(lit.clone()), query_term, subst, results);
            }
            Term::Ident(sym) => {
                Self::query_leaf_key(node, &DiscrimKey::Ident(*sym), query_term, subst, results);
            }
            Term::Ref(sym) => {
                Self::query_leaf_key(node, &DiscrimKey::Ref(*sym), query_term, subst, results);
            }
            Term::Bottom => {
                Self::query_leaf_key(node, &DiscrimKey::Bottom, query_term, subst, results);
            }
        }
    }

    fn query_leaf_key(
        node: &DiscrimNode<L>,
        key: &DiscrimKey,
        query_term: TermId,
        subst: SmallSubst,
        results: &mut Vec<(L, SmallSubst)>,
    ) {
        if let Some(child) = node.concrete.get(key) {
            for leaf in &child.leaves {
                results.push((leaf.clone(), subst.clone()));
            }
        }
        for (tree_vid, child) in &node.var_edges {
            let branch = subst.clone()
                .with_binding(*tree_vid, BindValue::Term(query_term));
            Self::collect_all_leaves(child, branch, results);
        }
    }

    /// Process args in canonical order. `on_done` is called when all args match.
    /// `bind_paths`: true at top-level args (VarPath valid), false at nested
    /// positions (VarPath only supports one level of extraction).
    fn query_args(
        node: &DiscrimNode<L>,
        terms: &TermStore,
        positional: &[TermId],
        named: &[(Symbol, TermId)],
        pos_offset: usize,
        bind_paths: bool,
        subst: SmallSubst,
        results: &mut Vec<(L, SmallSubst)>,
        on_done: &dyn Fn(&DiscrimNode<L>, SmallSubst, &mut Vec<(L, SmallSubst)>),
    ) {
        if positional.is_empty() && named.is_empty() {
            on_done(node, subst, results);
            return;
        }

        if !positional.is_empty() {
            let path = if bind_paths {
                Some(VarPath::Arg(ArgPos::Positional(pos_offset)))
            } else { None };
            if let Some(mc) = node.concrete.get(&DiscrimKey::Positional) {
                Self::query_arg_value(
                    mc, terms, positional[0], path,
                    &positional[1..], named, pos_offset + 1, bind_paths,
                    subst, results, on_done,
                );
            }
        } else {
            let (sym, id) = named[0];
            let path = if bind_paths {
                Some(VarPath::Arg(ArgPos::Named(sym)))
            } else { None };
            if let Some(mc) = node.concrete.get(&DiscrimKey::NamedKey(sym)) {
                Self::query_arg_value(
                    mc, terms, id, path,
                    positional, &named[1..], pos_offset, bind_paths,
                    subst, results, on_done,
                );
            }
        }
    }

    /// Process one arg value, then continue with remaining args.
    fn query_arg_value(
        node: &DiscrimNode<L>,
        terms: &TermStore,
        arg_term_id: TermId,
        arg_path: Option<VarPath>,
        remaining_pos: &[TermId],
        remaining_named: &[(Symbol, TermId)],
        pos_offset: usize,
        bind_paths: bool,
        subst: SmallSubst,
        results: &mut Vec<(L, SmallSubst)>,
        on_done: &dyn Fn(&DiscrimNode<L>, SmallSubst, &mut Vec<(L, SmallSubst)>),
    ) {
        match terms.get(arg_term_id) {
            Term::Var(Var::Global(vid)) => {
                let s = match arg_path {
                    Some(path) => subst.with_binding(*vid, BindValue::Path(path)),
                    None => subst,
                };
                Self::skip_subtree_then_continue(
                    node, terms, remaining_pos, remaining_named, pos_offset,
                    bind_paths, s, results, on_done,
                );
            }
            Term::Var(Var::DeBruijn(_)) => {
                // DeBruijn vars: skip subtree like a wildcard, no binding
                Self::skip_subtree_then_continue(
                    node, terms, remaining_pos, remaining_named, pos_offset,
                    bind_paths, subst, results, on_done,
                );
            }

            Term::Fn { functor, pos_args, named_args } => {
                let functor = *functor;
                let inner_pos = pos_args.clone();
                let inner_named = named_args.clone();
                let arity = inner_pos.len() + inner_named.len();
                if let Some(n1) = node.concrete.get(&DiscrimKey::Functor(functor)) {
                    if let Some(n2) = n1.concrete.get(&DiscrimKey::Arity(arity as u16)) {
                        // After inner args, continue with remaining outer args
                        let nested_cont = |node: &DiscrimNode<L>, subst: SmallSubst, results: &mut Vec<(L, SmallSubst)>| {
                            Self::query_args(
                                node, terms, remaining_pos, remaining_named, pos_offset,
                                bind_paths, subst, results, on_done,
                            );
                        };
                        Self::query_args(
                            n2, terms, &inner_pos, &inner_named, 0, false,
                            subst.clone(), results, &nested_cont,
                        );
                    }
                }
                // var_edges: tree variable matches this nested Fn
                for (tree_vid, child) in &node.var_edges {
                    let branch = subst.clone()
                        .with_binding(*tree_vid, BindValue::Term(arg_term_id));
                    Self::query_args(
                        child, terms, remaining_pos, remaining_named, pos_offset,
                        bind_paths, branch, results, on_done,
                    );
                }
            }

            Term::Const(lit) => {
                Self::follow_key_then_continue(
                    node, &DiscrimKey::Lit(lit.clone()), arg_term_id, terms,
                    remaining_pos, remaining_named, pos_offset, bind_paths,
                    subst, results, on_done,
                );
            }
            Term::Ident(sym) => {
                Self::follow_key_then_continue(
                    node, &DiscrimKey::Ident(*sym), arg_term_id, terms,
                    remaining_pos, remaining_named, pos_offset, bind_paths,
                    subst, results, on_done,
                );
            }
            Term::Ref(sym) => {
                Self::follow_key_then_continue(
                    node, &DiscrimKey::Ref(*sym), arg_term_id, terms,
                    remaining_pos, remaining_named, pos_offset, bind_paths,
                    subst, results, on_done,
                );
            }
            Term::Bottom => {
                Self::follow_key_then_continue(
                    node, &DiscrimKey::Bottom, arg_term_id, terms,
                    remaining_pos, remaining_named, pos_offset, bind_paths,
                    subst, results, on_done,
                );
            }
        }
    }

    /// Follow a concrete key, then continue with remaining args.
    fn follow_key_then_continue(
        node: &DiscrimNode<L>,
        key: &DiscrimKey,
        query_term: TermId,
        terms: &TermStore,
        remaining_pos: &[TermId],
        remaining_named: &[(Symbol, TermId)],
        pos_offset: usize,
        bind_paths: bool,
        subst: SmallSubst,
        results: &mut Vec<(L, SmallSubst)>,
        on_done: &dyn Fn(&DiscrimNode<L>, SmallSubst, &mut Vec<(L, SmallSubst)>),
    ) {
        if let Some(child) = node.concrete.get(key) {
            Self::query_args(child, terms, remaining_pos, remaining_named, pos_offset,
                bind_paths, subst.clone(), results, on_done);
        }
        for (tree_vid, child) in &node.var_edges {
            let branch = subst.clone()
                .with_binding(*tree_vid, BindValue::Term(query_term));
            Self::query_args(child, terms, remaining_pos, remaining_named, pos_offset,
                bind_paths, branch, results, on_done);
        }
    }

    /// Skip an entire subtree (query Var at arg position), then continue.
    fn skip_subtree_then_continue(
        node: &DiscrimNode<L>,
        terms: &TermStore,
        remaining_pos: &[TermId],
        remaining_named: &[(Symbol, TermId)],
        pos_offset: usize,
        bind_paths: bool,
        subst: SmallSubst,
        results: &mut Vec<(L, SmallSubst)>,
        on_done: &dyn Fn(&DiscrimNode<L>, SmallSubst, &mut Vec<(L, SmallSubst)>),
    ) {
        // This node might be the end of the skipped subtree
        Self::query_args(node, terms, remaining_pos, remaining_named, pos_offset,
            bind_paths, subst.clone(), results, on_done);
        // Or it might have deeper structure
        for (_, child) in &node.concrete {
            Self::skip_subtree_then_continue(child, terms, remaining_pos, remaining_named,
                pos_offset, bind_paths, subst.clone(), results, on_done);
        }
        for (_, child) in &node.var_edges {
            Self::skip_subtree_then_continue(child, terms, remaining_pos, remaining_named,
                pos_offset, bind_paths, subst.clone(), results, on_done);
        }
    }

    /// Collect all leaves in the entire subtree.
    fn collect_all_leaves(
        node: &DiscrimNode<L>,
        subst: SmallSubst,
        results: &mut Vec<(L, SmallSubst)>,
    ) {
        for leaf in &node.leaves {
            results.push((leaf.clone(), subst.clone()));
        }
        for (_, child) in &node.concrete {
            Self::collect_all_leaves(child, subst.clone(), results);
        }
        for (_, child) in &node.var_edges {
            Self::collect_all_leaves(child, subst.clone(), results);
        }
    }
}

// ── Tests ───────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use smallvec::SmallVec;
    use crate::intern::Interner;

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

    fn make_resolver(mapping: Vec<(u32, TermId)>) -> impl Fn(&u32) -> TermId {
        move |leaf: &u32| mapping.iter().find(|(k, _)| k == leaf).unwrap().1
    }

    // ── Insert ground + query tests ─────────────────────────────

    #[test]
    fn insert_ground_and_exact_query() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();
        let f = env.intern("account");
        let val = env.alloc(Term::Const(Literal::String("A001".into())));
        let term = env.alloc(Term::Fn {
            functor: f, pos_args: SmallVec::from_elem(val, 1), named_args: SmallVec::new(),
        });
        tree.insert_ground(&env.terms, term, 1);
        let results = tree.query_resolved(&env.terms, term, |_| term);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, 1);
    }

    #[test]
    fn query_different_arg_finds_nothing() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();
        let f = env.intern("f");
        let v1 = env.alloc(Term::Const(Literal::Int(1)));
        let v2 = env.alloc(Term::Const(Literal::Int(2)));
        let t1 = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(v1, 1), named_args: SmallVec::new() });
        let t2 = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(v2, 1), named_args: SmallVec::new() });
        tree.insert_ground(&env.terms, t1, 1);
        assert!(tree.query_raw(&env.terms, t2).is_empty());
    }

    #[test]
    fn multiple_facts_same_functor() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();
        let f = env.intern("parent");
        let a = env.alloc(Term::Const(Literal::String("alice".into())));
        let b = env.alloc(Term::Const(Literal::String("bob".into())));
        let c = env.alloc(Term::Const(Literal::String("charlie".into())));
        let f1 = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_slice(&[a, b]), named_args: SmallVec::new() });
        let f2 = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_slice(&[b, c]), named_args: SmallVec::new() });
        tree.insert_ground(&env.terms, f1, 1);
        tree.insert_ground(&env.terms, f2, 2);
        let res = make_resolver(vec![(1, f1), (2, f2)]);
        assert_eq!(tree.query_resolved(&env.terms, f1, &res).len(), 1);
        assert_eq!(tree.query_resolved(&env.terms, f2, &res).len(), 1);
    }

    #[test]
    fn query_with_variable_matches_all_and_binds() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();
        let f = env.intern("f");
        let v1 = env.alloc(Term::Const(Literal::Int(1)));
        let v2 = env.alloc(Term::Const(Literal::Int(2)));
        let t1 = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(v1, 1), named_args: SmallVec::new() });
        let t2 = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(v2, 1), named_args: SmallVec::new() });
        tree.insert_ground(&env.terms, t1, 1);
        tree.insert_ground(&env.terms, t2, 2);

        let vid = env.fresh_var("x");
        let var = env.alloc(Term::Var(Var::Global(vid)));
        let pat = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(var, 1), named_args: SmallVec::new() });
        let res = make_resolver(vec![(1, t1), (2, t2)]);
        let results = tree.query_resolved(&env.terms, pat, &res);
        assert_eq!(results.len(), 2);
        for (leaf, subst) in &results {
            let bound = subst.resolve(vid).expect("bound");
            match leaf { 1 => assert_eq!(bound, v1), 2 => assert_eq!(bound, v2), _ => panic!() }
        }
    }

    #[test]
    fn query_named_arg_variable_binds_correctly() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();
        let f = env.intern("Account");
        let id_s = env.intern("id");
        let name_s = env.intern("name");
        let vid = env.alloc(Term::Const(Literal::String("A001".into())));
        let vname = env.alloc(Term::Const(Literal::String("Savings".into())));
        let fact = env.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(id_s, vid), (name_s, vname)]),
        });
        tree.insert_ground(&env.terms, fact, 1);

        let xv = env.fresh_var("x");
        let var_x = env.alloc(Term::Var(Var::Global(xv)));
        let pat = env.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(id_s, var_x), (name_s, vname)]),
        });
        let results = tree.query_resolved(&env.terms, pat, |_| fact);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].1.resolve(xv).unwrap(), vid);
    }

    #[test]
    fn query_all_variable_matches_everything() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();
        let f = env.intern("f");
        let g = env.intern("g");
        let val = env.alloc(Term::Const(Literal::Int(1)));
        let tf = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(val, 1), named_args: SmallVec::new() });
        let tg = env.alloc(Term::Fn { functor: g, pos_args: SmallVec::new(), named_args: SmallVec::new() });
        tree.insert_ground(&env.terms, tf, 1);
        tree.insert_ground(&env.terms, tg, 2);

        let vid = env.fresh_var("x");
        let var_q = env.alloc(Term::Var(Var::Global(vid)));
        let res = make_resolver(vec![(1, tf), (2, tg)]);
        let results = tree.query_resolved(&env.terms, var_q, &res);
        assert_eq!(results.len(), 2);
        for (leaf, subst) in &results {
            let bound = subst.resolve(vid).unwrap();
            match leaf { 1 => assert_eq!(bound, tf), 2 => assert_eq!(bound, tg), _ => panic!() }
        }
    }

    #[test]
    fn nested_fn_exact_discrimination() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();
        let f = env.intern("f");
        let g = env.intern("g");
        let v1 = env.alloc(Term::Const(Literal::Int(1)));
        let v2 = env.alloc(Term::Const(Literal::Int(2)));
        let g1 = env.alloc(Term::Fn { functor: g, pos_args: SmallVec::from_elem(v1, 1), named_args: SmallVec::new() });
        let g2 = env.alloc(Term::Fn { functor: g, pos_args: SmallVec::from_elem(v2, 1), named_args: SmallVec::new() });
        let fg1 = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(g1, 1), named_args: SmallVec::new() });
        let fg2 = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(g2, 1), named_args: SmallVec::new() });
        tree.insert_ground(&env.terms, fg1, 1);
        tree.insert_ground(&env.terms, fg2, 2);

        let res = make_resolver(vec![(1, fg1), (2, fg2)]);
        let r1 = tree.query_resolved(&env.terms, fg1, &res);
        assert_eq!(r1.len(), 1);
        assert_eq!(r1[0].0, 1);
        let r2 = tree.query_resolved(&env.terms, fg2, &res);
        assert_eq!(r2.len(), 1);
        assert_eq!(r2[0].0, 2);
    }

    // ── Remove + pruning tests ──────────────────────────────────

    #[test]
    fn remove_ground_and_prune() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();
        let f = env.intern("f");
        let val = env.alloc(Term::Const(Literal::Int(42)));
        let term = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(val, 1), named_args: SmallVec::new() });
        tree.insert_ground(&env.terms, term, 1);
        assert_eq!(tree.query_raw(&env.terms, term).len(), 1);
        tree.remove_ground(&env.terms, term, &1);
        assert!(tree.query_raw(&env.terms, term).is_empty());
        assert!(tree.root.is_empty());
    }

    #[test]
    fn remove_one_of_two_leaves() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();
        let f = env.intern("f");
        let val = env.alloc(Term::Const(Literal::Int(1)));
        let term = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(val, 1), named_args: SmallVec::new() });
        tree.insert_ground(&env.terms, term, 1);
        tree.insert_ground(&env.terms, term, 2);
        tree.remove_ground(&env.terms, term, &1);
        let results = tree.query_raw(&env.terms, term);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, 2);
    }

    // ── Variable edge (pattern insertion) tests ─────────────────

    #[test]
    fn insert_pattern_with_var_and_query_ground() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();
        let f = env.intern("f");
        let vid = env.fresh_var("x");
        let var_term = env.alloc(Term::Var(Var::Global(vid)));
        let pat = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(var_term, 1), named_args: SmallVec::new() });
        tree.insert_pattern(&env.terms, pat, 100);
        let val = env.alloc(Term::Const(Literal::Int(42)));
        let ground = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(val, 1), named_args: SmallVec::new() });
        let results = tree.query_raw(&env.terms, ground);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, 100);
    }

    #[test]
    fn mixed_concrete_and_var_edges() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();
        let f = env.intern("f");
        let v42 = env.alloc(Term::Const(Literal::Int(42)));
        let ground = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(v42, 1), named_args: SmallVec::new() });
        tree.insert_ground(&env.terms, ground, 1);

        let vid = env.fresh_var("x");
        let var_term = env.alloc(Term::Var(Var::Global(vid)));
        let pat = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(var_term, 1), named_args: SmallVec::new() });
        tree.insert_pattern(&env.terms, pat, 2);

        assert_eq!(tree.query_raw(&env.terms, ground).len(), 2);
        let v99 = env.alloc(Term::Const(Literal::Int(99)));
        let q99 = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(v99, 1), named_args: SmallVec::new() });
        let r = tree.query_raw(&env.terms, q99);
        assert_eq!(r.len(), 1);
        assert_eq!(r[0].0, 2);
    }
}
