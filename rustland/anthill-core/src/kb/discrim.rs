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
use std::rc::Rc;

use crate::eval::value::Value;
use crate::intern::Symbol;
use super::node_occurrence::NodeOccurrence;
use super::persist_subst::{ArgPos, BindValue, PersistSubst, SmallSubst, VarPath};
use super::subst::Substitution;
use super::term::{Literal, TermId, Var};
use super::term_view::{TermView, ViewHead, ViewItem};
use super::KnowledgeBase;
#[cfg(test)]
use super::term::{Term, VarId};

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
    var_edges: Vec<(Var, DiscrimNode<L>)>,
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

/// Iterative `Drop` for `DiscrimNode`. The default Drop walks every
/// nested `DiscrimNode` value recursively (one host stack frame per
/// tree depth) — fine for shallow indexes but blows the default 2 MiB
/// debug-build stack when the discrimination tree gets deep (e.g. the
/// 624-line typing_pass_spec.anthill builds a deeply-branched index).
/// Drain children into an explicit work stack and decrement
/// iteratively so each `DiscrimNode`'s natural Drop finds emptied
/// fields and adds no further frames.
impl<L> Drop for DiscrimNode<L> {
    fn drop(&mut self) {
        let mut stack: Vec<DiscrimNode<L>> = Vec::new();
        steal_discrim_children(self, &mut stack);
        while let Some(mut node) = stack.pop() {
            steal_discrim_children(&mut node, &mut stack);
            // `node` drops here; its `concrete` and `var_edges` have
            // been emptied so the recursive Drop call into this impl
            // finds nothing to drain.
        }
    }
}

fn steal_discrim_children<L>(node: &mut DiscrimNode<L>, stack: &mut Vec<DiscrimNode<L>>) {
    for (_, child) in std::mem::take(&mut node.concrete) {
        stack.push(child);
    }
    for (_, child) in std::mem::take(&mut node.var_edges) {
        stack.push(child);
    }
    // `leaves` are owned `L` values (RuleId-shaped in practice) — no
    // recursive Drop concern.
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

// ── OwnedView — a lifetime-free child descriptor ────────────────
//
// The remove walk flattens a nested compound's args together with the
// remaining outer args into one sequence (the pruning back-walk needs them
// contiguous). A borrowed [`ViewItem`] can't survive that splice — its
// `Value` arm borrows its parent, whose borrow ends each recursion level.
// `OwnedView` owns its payload (an `Rc`/`Value` clone — cheap; remove is the
// cold retract path), so flattened sequences carry no borrow. It re-exposes a
// [`ViewItem`] on demand via [`OwnedView::view`]. The insert walk keeps the
// borrowed `ViewItem` — it never stores a child across recursion levels.

#[derive(Clone)]
enum OwnedView {
    Term(TermId),
    Value(Value),
    Node(Rc<NodeOccurrence>),
}

impl OwnedView {
    fn from_item(item: &ViewItem<'_>) -> Self {
        match item {
            ViewItem::Term(t) => OwnedView::Term(*t),
            ViewItem::Value(v) => OwnedView::Value((*v).clone()),
            ViewItem::Node(occ) => OwnedView::Node(Rc::clone(occ)),
        }
    }

    fn view(&self) -> ViewItem<'_> {
        match self {
            OwnedView::Term(t) => ViewItem::Term(*t),
            OwnedView::Value(v) => ViewItem::Value(v),
            OwnedView::Node(occ) => ViewItem::Node(Rc::clone(occ)),
        }
    }
}

// ── View-driven insert ──────────────────────────────────────────

impl<L> SubstTree<L> {
    /// Insert a ground term. Ground heads carry no variables, so the pattern
    /// walk indexes them identically — its var-edge arm is simply never
    /// reached. Test-only today; the live ground path is `assert_fact` →
    /// `insert_pattern`.
    #[allow(dead_code)]
    pub(crate) fn insert_ground<V: TermView>(&mut self, kb: &KnowledgeBase, term: &V, leaf: L) {
        self.insert_pattern(kb, term, leaf)
    }

    /// Insert a stored pattern (a rule / fact head), creating concrete edges
    /// for structure and var-edges for variables. Driven by [`TermView`]
    /// (WI-348): a `TermId` head and a `Value::Node`-carrying value fact
    /// decompose into the *same* structural [`DiscrimKey`]s, so both index
    /// identically.
    pub(crate) fn insert_pattern<V: TermView>(&mut self, kb: &KnowledgeBase, pattern: &V, leaf: L) {
        let node = Self::insert_walk(&mut self.root, kb, pattern);
        node.leaves.push(leaf);
    }

    /// Walk the view's structure, creating edges. Returns the final node.
    /// The "recurse into this child" pointer is a [`ViewItem`] (itself a
    /// `TermView`), not a `TermId` — so a Node child is walked in place.
    fn insert_walk<'a, V: TermView>(
        node: &'a mut DiscrimNode<L>,
        kb: &KnowledgeBase,
        view: &V,
    ) -> &'a mut DiscrimNode<L> {
        // A stored-pattern variable of any kind (Global / Rigid / DeBruijn)
        // keys a var-edge — see [`TermView::index_var`].
        if let Some(var) = view.index_var(kb) {
            let pos = node.var_edges.iter().position(|(v, _)| *v == var);
            return if let Some(idx) = pos {
                &mut node.var_edges[idx].1
            } else {
                node.var_edges.push((var, DiscrimNode::new()));
                let last = node.var_edges.len() - 1;
                &mut node.var_edges[last].1
            };
        }
        match view.head(kb) {
            ViewHead::Functor { functor: Some(functor), pos_arity, named_arity } => {
                let arity = pos_arity + named_arity;
                let n = node.concrete.entry(DiscrimKey::Functor(functor))
                    .or_insert_with(DiscrimNode::new);
                let n = n.concrete.entry(DiscrimKey::Arity(arity as u16))
                    .or_insert_with(DiscrimNode::new);
                Self::insert_walk_args(n, kb, view, pos_arity)
            }
            ViewHead::Const(lit) => node.concrete.entry(DiscrimKey::Lit(lit))
                .or_insert_with(DiscrimNode::new),
            ViewHead::Ident(sym) => node.concrete.entry(DiscrimKey::Ident(sym))
                .or_insert_with(DiscrimNode::new),
            ViewHead::Ref(sym) => node.concrete.entry(DiscrimKey::Ref(sym))
                .or_insert_with(DiscrimNode::new),
            ViewHead::Bottom => node.concrete.entry(DiscrimKey::Bottom)
                .or_insert_with(DiscrimNode::new),
            // Functor-less aggregates (tuple / unit) and Opaque heads
            // (closures, streams, post-elaboration forms …) carry no concrete
            // discrimination key. A leaf attached at the current node would be
            // unreachable by exact query — the query walk follows only var-edges
            // for these heads — and would collide with every other such head in
            // one undiscriminated bucket. Stored-pattern *variables* of any kind
            // (Global / Rigid / DeBruijn) do NOT reach here — `index_var` routes
            // them to a var-edge above, for every carrier including occurrence
            // value heads (WI-373). No fact/rule form in use today produces a
            // functor-less / opaque stored head; fail loudly rather than silently
            // mis-index (Phase A review guard #1/#2).
            ViewHead::Functor { functor: None, .. } | ViewHead::Opaque => panic!(
                "discrim insert: functor-less / opaque head carries no \
                 discrimination key — value-fact keying is unimplemented \
                 (WI-348 Phase B/C)"
            ),
            // Variables of every kind (Global / Rigid / DeBruijn) were routed
            // to a var-edge by `index_var` above, so a bare `Var` head is
            // unreachable here.
            ViewHead::Var(_) => unreachable!("Var head handled by index_var"),
        }
    }

    /// Walk a compound's args in canonical order — positionals first, then
    /// named in [`TermView::named_keys`] order — the same order the query
    /// walk uses, so insert and lookup descend the tree in lockstep.
    fn insert_walk_args<'a, V: TermView>(
        node: &'a mut DiscrimNode<L>,
        kb: &KnowledgeBase,
        view: &V,
        pos_arity: usize,
    ) -> &'a mut DiscrimNode<L> {
        let mut cur = node;
        for i in 0..pos_arity {
            let arg = view.pos_arg(kb, i).expect("pos_arg in range during insert");
            cur = cur.concrete.entry(DiscrimKey::Positional)
                .or_insert_with(DiscrimNode::new);
            cur = Self::insert_walk(cur, kb, &arg);
        }
        for sym in view.named_keys(kb) {
            let arg = view.named_arg(kb, sym).expect("named_arg present during insert");
            cur = cur.concrete.entry(DiscrimKey::NamedKey(sym))
                .or_insert_with(DiscrimNode::new);
            cur = Self::insert_walk(cur, kb, &arg);
        }
        cur
    }

    // ── View-driven remove ──────────────────────────────────────

    pub(crate) fn remove_ground<V: TermView>(&mut self, kb: &KnowledgeBase, view: &V, leaf: &L)
    where L: PartialEq,
    {
        Self::remove_walk(&mut self.root, kb, view, leaf);
    }

    /// Walk the view's structure to find and remove a leaf, pruning empty
    /// nodes on the way back. The structural mirror of [`insert_walk`]
    /// (WI-348).
    fn remove_walk<V: TermView>(
        node: &mut DiscrimNode<L>,
        kb: &KnowledgeBase,
        view: &V,
        leaf: &L,
    ) -> bool
    where L: PartialEq,
    {
        // Removing a var-headed pattern by structure is never requested — the
        // callers retract stored ground/`TermId` heads. Mirror the old
        // `Term::Var(_)` no-op.
        if view.index_var(kb).is_some() {
            return node.is_empty();
        }
        match view.head(kb) {
            ViewHead::Functor { functor: Some(functor), pos_arity, named_arity } => {
                let arity = pos_arity + named_arity;
                let fk = DiscrimKey::Functor(functor);
                let prune_fn = if let Some(fn_child) = node.concrete.get_mut(&fk) {
                    let ak = DiscrimKey::Arity(arity as u16);
                    let prune_ar = if let Some(ar_child) = fn_child.concrete.get_mut(&ak) {
                        let arg_seq = Self::owned_arg_seq(kb, view, pos_arity);
                        Self::remove_walk_args(ar_child, kb, &arg_seq, 0, leaf)
                    } else { false };
                    if prune_ar { fn_child.concrete.remove(&ak); }
                    fn_child.is_empty()
                } else { false };
                if prune_fn { node.concrete.remove(&fk); }
                node.is_empty()
            }
            ViewHead::Const(lit) => Self::remove_at_leaf_key(node, DiscrimKey::Lit(lit), leaf),
            ViewHead::Ident(sym) => Self::remove_at_leaf_key(node, DiscrimKey::Ident(sym), leaf),
            ViewHead::Ref(sym) => Self::remove_at_leaf_key(node, DiscrimKey::Ref(sym), leaf),
            ViewHead::Bottom => Self::remove_at_leaf_key(node, DiscrimKey::Bottom, leaf),
            // Mirror of `insert_walk`'s guard: such a head can never have been
            // inserted (insert panics on it), so retracting one is a logic
            // error (Phase A review guard #1/#2).
            ViewHead::Functor { functor: None, .. } | ViewHead::Opaque => panic!(
                "discrim remove: functor-less / opaque head carries no \
                 discrimination key — value-fact keying is unimplemented \
                 (WI-348 Phase B/C)"
            ),
            // Variables were routed by `index_var` above (handled at the top
            // of this fn for the structural-var no-op case).
            ViewHead::Var(_) => unreachable!("Var head handled by index_var"),
        }
    }

    /// The canonical arg sequence (positionals then named, in
    /// [`TermView::named_keys`] order) as owned, borrow-free [`OwnedView`]
    /// descriptors, so a nested compound's args can be flattened with the
    /// remaining outer args.
    fn owned_arg_seq<V: TermView>(
        kb: &KnowledgeBase,
        view: &V,
        pos_arity: usize,
    ) -> Vec<(DiscrimKey, OwnedView)> {
        let mut seq = Vec::new();
        for i in 0..pos_arity {
            let item = view.pos_arg(kb, i).expect("pos_arg in range during remove");
            seq.push((DiscrimKey::Positional, OwnedView::from_item(&item)));
        }
        for sym in view.named_keys(kb) {
            let item = view.named_arg(kb, sym).expect("named_arg present during remove");
            seq.push((DiscrimKey::NamedKey(sym), OwnedView::from_item(&item)));
        }
        seq
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
        kb: &KnowledgeBase,
        arg_seq: &[(DiscrimKey, OwnedView)],
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
        let prune = if let Some(marker_child) = node.concrete.get_mut(&marker) {
            Self::remove_walk_arg_value(marker_child, kb, &arg_seq[idx].1, arg_seq, idx, leaf)
        } else { false };
        if prune { node.concrete.remove(&marker); }
        node.is_empty()
    }

    /// Walk a single arg's value, then continue with remaining args.
    fn remove_walk_arg_value(
        node: &mut DiscrimNode<L>,
        kb: &KnowledgeBase,
        arg: &OwnedView,
        arg_seq: &[(DiscrimKey, OwnedView)],
        idx: usize,
        leaf: &L,
    ) -> bool
    where L: PartialEq,
    {
        let view = arg.view();
        if view.index_var(kb).is_some() {
            return node.is_empty();
        }
        match view.head(kb) {
            ViewHead::Functor { functor: Some(functor), pos_arity, named_arity } => {
                let arity = pos_arity + named_arity;
                let fk = DiscrimKey::Functor(functor);
                let prune_fn = if let Some(fn_child) = node.concrete.get_mut(&fk) {
                    let ak = DiscrimKey::Arity(arity as u16);
                    let prune_ar = if let Some(ar_child) = fn_child.concrete.get_mut(&ak) {
                        let mut combined = Self::owned_arg_seq(kb, &view, pos_arity);
                        combined.extend(arg_seq[idx + 1..].iter().cloned());
                        Self::remove_walk_args(ar_child, kb, &combined, 0, leaf)
                    } else { false };
                    if prune_ar { fn_child.concrete.remove(&ak); }
                    fn_child.is_empty()
                } else { false };
                if prune_fn { node.concrete.remove(&fk); }
                node.is_empty()
            }
            ViewHead::Const(lit) => {
                Self::remove_value_then_continue(node, DiscrimKey::Lit(lit), kb, arg_seq, idx, leaf)
            }
            ViewHead::Ident(sym) => {
                Self::remove_value_then_continue(node, DiscrimKey::Ident(sym), kb, arg_seq, idx, leaf)
            }
            ViewHead::Ref(sym) => {
                Self::remove_value_then_continue(node, DiscrimKey::Ref(sym), kb, arg_seq, idx, leaf)
            }
            ViewHead::Bottom => {
                Self::remove_value_then_continue(node, DiscrimKey::Bottom, kb, arg_seq, idx, leaf)
            }
            // Mirror of `insert_walk_args`' guard: such an arg can never have
            // been inserted, so encountering one on remove is a logic error
            // (Phase A review guard #1/#2).
            ViewHead::Functor { functor: None, .. } | ViewHead::Opaque => panic!(
                "discrim remove: functor-less / opaque arg carries no \
                 discrimination key — value-fact keying is unimplemented \
                 (WI-348 Phase B/C)"
            ),
            // Variables were handled by the `index_var` check above.
            ViewHead::Var(_) => unreachable!("Var arg handled by index_var"),
        }
    }

    /// Follow a value key, continue with remaining args, prune if empty.
    fn remove_value_then_continue(
        node: &mut DiscrimNode<L>,
        key: DiscrimKey,
        kb: &KnowledgeBase,
        arg_seq: &[(DiscrimKey, OwnedView)],
        idx: usize,
        leaf: &L,
    ) -> bool
    where L: PartialEq,
    {
        let prune = if let Some(child) = node.concrete.get_mut(&key) {
            Self::remove_walk_args(child, kb, arg_seq, idx + 1, leaf)
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
    pub(crate) fn query_raw<V: TermView>(
        &self,
        kb: &KnowledgeBase,
        query: &V,
    ) -> Vec<(L, SmallSubst)> {
        let mut results = Vec::new();
        Self::query_node(&self.root, kb, query, VarPath::Root, SmallSubst::new(), &mut results);
        results
    }

    pub(crate) fn query_resolved<V: TermView, F>(
        &self,
        kb: &KnowledgeBase,
        query: &V,
        resolve_term: F,
    ) -> Vec<(L, Substitution)>
    where
        F: Fn(&L) -> TermId,
    {
        self.query_raw(kb, query).into_iter()
            .map(|(leaf, subst)| {
                let fact_term = resolve_term(&leaf);
                let s = subst.resolve_leaf(&kb.terms, fact_term);
                (leaf, s)
            })
            .collect()
    }

    /// Carrier-faithful peer of [`query_resolved`] (WI-348 Phase B). The fact
    /// head is resolved as a `Value`: a `Value::Term` head takes the fast term
    /// path ([`PersistSubst::resolve_leaf`], unchanged); any other carrier (a
    /// value fact with a `Value::Node` subterm) resolves deferred paths against
    /// the head's own `TermView` ([`PersistSubst::resolve_leaf_view`]), so
    /// named-arg positions read the same carrier the tree indexed (the
    /// term-store path would read a sorted-by-name skeleton — the named-order
    /// finding).
    pub(crate) fn query_resolved_value<V: TermView, F>(
        &self,
        kb: &KnowledgeBase,
        query: &V,
        resolve_head: F,
    ) -> Vec<(L, Substitution)>
    where
        F: Fn(&L) -> Value,
    {
        self.query_raw(kb, query).into_iter()
            .map(|(leaf, subst)| {
                let head = resolve_head(&leaf);
                let s = match &head {
                    Value::Term(t) => subst.resolve_leaf(&kb.terms, *t),
                    _ => subst.resolve_leaf_view(kb, &head),
                };
                (leaf, s)
            })
            .collect()
    }

    fn query_node<V: TermView>(
        node: &DiscrimNode<L>,
        kb: &KnowledgeBase,
        query: &V,
        path: VarPath,
        subst: SmallSubst,
        results: &mut Vec<(L, SmallSubst)>,
    ) {
        match query.head(kb) {
            ViewHead::Var(vid) => {
                let s = subst.with_binding(vid, BindValue::Path(path));
                Self::collect_all_leaves(node, s, results);
            }
            ViewHead::Functor { functor, pos_arity, named_arity } => {
                let arity = pos_arity + named_arity;
                if let Some(fsym) = functor {
                    if let Some(n1) = node.concrete.get(&DiscrimKey::Functor(fsym)) {
                        if let Some(n2) = n1.concrete.get(&DiscrimKey::Arity(arity as u16)) {
                            let named_keys = query.named_keys(kb);
                            let collect_leaves = |node: &DiscrimNode<L>, subst: SmallSubst, results: &mut Vec<(L, SmallSubst)>| {
                                for leaf in &node.leaves {
                                    results.push((leaf.clone(), subst.clone()));
                                }
                            };
                            Self::query_args(
                                n2, kb, query, 0, pos_arity, &named_keys, 0,
                                0, true, subst.clone(), results, &collect_leaves,
                            );
                        }
                    }
                }
                for (tree_var, child) in &node.var_edges {
                    let branch = subst.clone().with_binding(tree_var.as_vid(), query.as_bind_value());
                    Self::collect_all_leaves(child, branch, results);
                }
            }
            ViewHead::Const(lit) => {
                Self::query_leaf_key(node, &DiscrimKey::Lit(lit), query, subst, results);
            }
            ViewHead::Ident(sym) => {
                Self::query_leaf_key(node, &DiscrimKey::Ident(sym), query, subst, results);
            }
            ViewHead::Ref(sym) => {
                Self::query_leaf_key(node, &DiscrimKey::Ref(sym), query, subst, results);
            }
            ViewHead::Bottom => {
                Self::query_leaf_key(node, &DiscrimKey::Bottom, query, subst, results);
            }
            ViewHead::Opaque => {
                // Closures, streams, lazies, DeBruijn — no concrete match.
                // Still honor var_edges so an opaque value can bind a tree var.
                for (tree_var, child) in &node.var_edges {
                    let branch = subst.clone().with_binding(tree_var.as_vid(), query.as_bind_value());
                    Self::collect_all_leaves(child, branch, results);
                }
            }
        }
    }

    fn query_leaf_key<V: TermView>(
        node: &DiscrimNode<L>,
        key: &DiscrimKey,
        query: &V,
        subst: SmallSubst,
        results: &mut Vec<(L, SmallSubst)>,
    ) {
        if let Some(child) = node.concrete.get(key) {
            for leaf in &child.leaves {
                results.push((leaf.clone(), subst.clone()));
            }
        }
        for (tree_var, child) in &node.var_edges {
            let branch = subst.clone().with_binding(tree_var.as_vid(), query.as_bind_value());
            Self::collect_all_leaves(child, branch, results);
        }
    }

    /// Process args in canonical order: positionals 0..pos_total first,
    /// then named in `named_keys` starting at `named_idx`. `on_done` fires
    /// when both cursors reach their ends.
    #[allow(clippy::too_many_arguments)]
    fn query_args<V: TermView>(
        node: &DiscrimNode<L>,
        kb: &KnowledgeBase,
        query: &V,
        pos_idx: usize,
        pos_total: usize,
        named_keys: &[Symbol],
        named_idx: usize,
        pos_offset: usize,
        bind_paths: bool,
        subst: SmallSubst,
        results: &mut Vec<(L, SmallSubst)>,
        on_done: &dyn Fn(&DiscrimNode<L>, SmallSubst, &mut Vec<(L, SmallSubst)>),
    ) {
        if pos_idx >= pos_total && named_idx >= named_keys.len() {
            on_done(node, subst, results);
            return;
        }

        if pos_idx < pos_total {
            let path = if bind_paths {
                Some(VarPath::Arg(ArgPos::Positional(pos_offset)))
            } else { None };
            if let Some(mc) = node.concrete.get(&DiscrimKey::Positional) {
                if let Some(arg) = query.pos_arg(kb, pos_idx) {
                    Self::query_arg_value(
                        mc, kb, arg, path, query,
                        pos_idx + 1, pos_total, named_keys, named_idx,
                        pos_offset + 1, bind_paths, subst, results, on_done,
                    );
                }
            }
        } else {
            let sym = named_keys[named_idx];
            let path = if bind_paths {
                Some(VarPath::Arg(ArgPos::Named(sym)))
            } else { None };
            if let Some(mc) = node.concrete.get(&DiscrimKey::NamedKey(sym)) {
                if let Some(arg) = query.named_arg(kb, sym) {
                    Self::query_arg_value(
                        mc, kb, arg, path, query,
                        pos_idx, pos_total, named_keys, named_idx + 1,
                        pos_offset, bind_paths, subst, results, on_done,
                    );
                }
            }
        }
    }

    /// Process one arg value, then continue with the remaining args of the
    /// outer query via `query_args`.
    #[allow(clippy::too_many_arguments)]
    fn query_arg_value<V: TermView>(
        node: &DiscrimNode<L>,
        kb: &KnowledgeBase,
        arg: ViewItem<'_>,
        arg_path: Option<VarPath>,
        outer: &V,
        pos_idx: usize,
        pos_total: usize,
        named_keys: &[Symbol],
        named_idx: usize,
        pos_offset: usize,
        bind_paths: bool,
        subst: SmallSubst,
        results: &mut Vec<(L, SmallSubst)>,
        on_done: &dyn Fn(&DiscrimNode<L>, SmallSubst, &mut Vec<(L, SmallSubst)>),
    ) {
        match arg.head(kb) {
            ViewHead::Var(vid) => {
                let s = match arg_path {
                    Some(path) => subst.with_binding(vid, BindValue::Path(path)),
                    None => subst,
                };
                Self::skip_subtree_then_continue(
                    node, kb, outer, pos_idx, pos_total, named_keys, named_idx,
                    pos_offset, bind_paths, s, results, on_done,
                );
            }
            ViewHead::Functor { functor, pos_arity, named_arity } => {
                let arity = pos_arity + named_arity;
                if let Some(fsym) = functor {
                    if let Some(n1) = node.concrete.get(&DiscrimKey::Functor(fsym)) {
                        if let Some(n2) = n1.concrete.get(&DiscrimKey::Arity(arity as u16)) {
                            let inner_named_keys = arg.named_keys(kb);
                            let nested_cont = |node: &DiscrimNode<L>, subst: SmallSubst, results: &mut Vec<(L, SmallSubst)>| {
                                Self::query_args(
                                    node, kb, outer, pos_idx, pos_total, named_keys, named_idx,
                                    pos_offset, bind_paths, subst, results, on_done,
                                );
                            };
                            Self::query_args(
                                n2, kb, &arg, 0, pos_arity, &inner_named_keys, 0,
                                0, false, subst.clone(), results, &nested_cont,
                            );
                        }
                    }
                }
                for (tree_var, child) in &node.var_edges {
                    let branch = subst.clone().with_binding(tree_var.as_vid(), arg.as_bind_value());
                    Self::query_args(
                        child, kb, outer, pos_idx, pos_total, named_keys, named_idx,
                        pos_offset, bind_paths, branch, results, on_done,
                    );
                }
            }
            ViewHead::Const(lit) => {
                Self::follow_key_then_continue(
                    node, &DiscrimKey::Lit(lit), arg, kb, outer,
                    pos_idx, pos_total, named_keys, named_idx, pos_offset, bind_paths,
                    subst, results, on_done,
                );
            }
            ViewHead::Ident(sym) => {
                Self::follow_key_then_continue(
                    node, &DiscrimKey::Ident(sym), arg, kb, outer,
                    pos_idx, pos_total, named_keys, named_idx, pos_offset, bind_paths,
                    subst, results, on_done,
                );
            }
            ViewHead::Ref(sym) => {
                Self::follow_key_then_continue(
                    node, &DiscrimKey::Ref(sym), arg, kb, outer,
                    pos_idx, pos_total, named_keys, named_idx, pos_offset, bind_paths,
                    subst, results, on_done,
                );
            }
            ViewHead::Bottom => {
                Self::follow_key_then_continue(
                    node, &DiscrimKey::Bottom, arg, kb, outer,
                    pos_idx, pos_total, named_keys, named_idx, pos_offset, bind_paths,
                    subst, results, on_done,
                );
            }
            ViewHead::Opaque => {
                for (tree_var, child) in &node.var_edges {
                    let branch = subst.clone().with_binding(tree_var.as_vid(), arg.as_bind_value());
                    Self::query_args(
                        child, kb, outer, pos_idx, pos_total, named_keys, named_idx,
                        pos_offset, bind_paths, branch, results, on_done,
                    );
                }
            }
        }
    }

    /// Follow a concrete key, then continue with remaining outer args.
    #[allow(clippy::too_many_arguments)]
    fn follow_key_then_continue<V: TermView>(
        node: &DiscrimNode<L>,
        key: &DiscrimKey,
        arg: ViewItem<'_>,
        kb: &KnowledgeBase,
        outer: &V,
        pos_idx: usize,
        pos_total: usize,
        named_keys: &[Symbol],
        named_idx: usize,
        pos_offset: usize,
        bind_paths: bool,
        subst: SmallSubst,
        results: &mut Vec<(L, SmallSubst)>,
        on_done: &dyn Fn(&DiscrimNode<L>, SmallSubst, &mut Vec<(L, SmallSubst)>),
    ) {
        if let Some(child) = node.concrete.get(key) {
            Self::query_args(
                child, kb, outer, pos_idx, pos_total, named_keys, named_idx,
                pos_offset, bind_paths, subst.clone(), results, on_done,
            );
        }
        for (tree_var, child) in &node.var_edges {
            let branch = subst.clone().with_binding(tree_var.as_vid(), arg.as_bind_value());
            Self::query_args(
                child, kb, outer, pos_idx, pos_total, named_keys, named_idx,
                pos_offset, bind_paths, branch, results, on_done,
            );
        }
    }

    /// Skip an entire subtree (query Var at arg position), then continue.
    #[allow(clippy::too_many_arguments)]
    fn skip_subtree_then_continue<V: TermView>(
        node: &DiscrimNode<L>,
        kb: &KnowledgeBase,
        outer: &V,
        pos_idx: usize,
        pos_total: usize,
        named_keys: &[Symbol],
        named_idx: usize,
        pos_offset: usize,
        bind_paths: bool,
        subst: SmallSubst,
        results: &mut Vec<(L, SmallSubst)>,
        on_done: &dyn Fn(&DiscrimNode<L>, SmallSubst, &mut Vec<(L, SmallSubst)>),
    ) {
        Self::query_args(
            node, kb, outer, pos_idx, pos_total, named_keys, named_idx,
            pos_offset, bind_paths, subst.clone(), results, on_done,
        );
        for (_, child) in &node.concrete {
            Self::skip_subtree_then_continue(
                child, kb, outer, pos_idx, pos_total, named_keys, named_idx,
                pos_offset, bind_paths, subst.clone(), results, on_done,
            );
        }
        for (_, child) in &node.var_edges {
            Self::skip_subtree_then_continue(
                child, kb, outer, pos_idx, pos_total, named_keys, named_idx,
                pos_offset, bind_paths, subst.clone(), results, on_done,
            );
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

    /// Holds a real `KnowledgeBase` so tests can call the generic
    /// `query_resolved`/`query_raw` APIs that need `&KB`. `env.terms`,
    /// `env.intern`, `env.alloc` delegate to the inner KB.
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

    /// Shorthand for `&TermIdView(tid)` that the query APIs want.
    fn view(tid: TermId) -> super::super::term_view::TermIdView {
        super::super::term_view::TermIdView(tid)
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
        tree.insert_ground(&env.kb, &view(term), 1);
        let results = tree.query_resolved(&env.kb, &view(term), |_| term);
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
        tree.insert_ground(&env.kb, &view(t1), 1);
        assert!(tree.query_raw(&env.kb, &view(t2)).is_empty());
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
        tree.insert_ground(&env.kb, &view(f1), 1);
        tree.insert_ground(&env.kb, &view(f2), 2);
        let res = make_resolver(vec![(1, f1), (2, f2)]);
        assert_eq!(tree.query_resolved(&env.kb, &view(f1), &res).len(), 1);
        assert_eq!(tree.query_resolved(&env.kb, &view(f2), &res).len(), 1);
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
        tree.insert_ground(&env.kb, &view(t1), 1);
        tree.insert_ground(&env.kb, &view(t2), 2);

        let vid = env.fresh_var("x");
        let var = env.alloc(Term::Var(Var::Global(vid)));
        let pat = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(var, 1), named_args: SmallVec::new() });
        let res = make_resolver(vec![(1, t1), (2, t2)]);
        let results = tree.query_resolved(&env.kb, &view(pat), &res);
        assert_eq!(results.len(), 2);
        for (leaf, subst) in &results {
            let bound = subst.resolve_as_value(vid).and_then(|v| v.as_term()).expect("bound");
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
        tree.insert_ground(&env.kb, &view(fact), 1);

        let xv = env.fresh_var("x");
        let var_x = env.alloc(Term::Var(Var::Global(xv)));
        let pat = env.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(id_s, var_x), (name_s, vname)]),
        });
        let results = tree.query_resolved(&env.kb, &view(pat), |_| fact);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].1.resolve_as_value(xv).and_then(|v| v.as_term()).unwrap(), vid);
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
        tree.insert_ground(&env.kb, &view(tf), 1);
        tree.insert_ground(&env.kb, &view(tg), 2);

        let vid = env.fresh_var("x");
        let var_q = env.alloc(Term::Var(Var::Global(vid)));
        let res = make_resolver(vec![(1, tf), (2, tg)]);
        let results = tree.query_resolved(&env.kb, &view(var_q), &res);
        assert_eq!(results.len(), 2);
        for (leaf, subst) in &results {
            let bound = subst.resolve_as_value(vid).and_then(|v| v.as_term()).unwrap();
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
        tree.insert_ground(&env.kb, &view(fg1), 1);
        tree.insert_ground(&env.kb, &view(fg2), 2);

        let res = make_resolver(vec![(1, fg1), (2, fg2)]);
        let r1 = tree.query_resolved(&env.kb, &view(fg1), &res);
        assert_eq!(r1.len(), 1);
        assert_eq!(r1[0].0, 1);
        let r2 = tree.query_resolved(&env.kb, &view(fg2), &res);
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
        tree.insert_ground(&env.kb, &view(term), 1);
        assert_eq!(tree.query_raw(&env.kb, &view(term)).len(), 1);
        tree.remove_ground(&env.kb, &view(term), &1);
        assert!(tree.query_raw(&env.kb, &view(term)).is_empty());
        assert!(tree.root.is_empty());
    }

    #[test]
    fn remove_one_of_two_leaves() {
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();
        let f = env.intern("f");
        let val = env.alloc(Term::Const(Literal::Int(1)));
        let term = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(val, 1), named_args: SmallVec::new() });
        tree.insert_ground(&env.kb, &view(term), 1);
        tree.insert_ground(&env.kb, &view(term), 2);
        tree.remove_ground(&env.kb, &view(term), &1);
        let results = tree.query_raw(&env.kb, &view(term));
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
        tree.insert_pattern(&env.kb, &view(pat), 100);
        let val = env.alloc(Term::Const(Literal::Int(42)));
        let ground = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(val, 1), named_args: SmallVec::new() });
        let results = tree.query_raw(&env.kb, &view(ground));
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
        tree.insert_ground(&env.kb, &view(ground), 1);

        let vid = env.fresh_var("x");
        let var_term = env.alloc(Term::Var(Var::Global(vid)));
        let pat = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(var_term, 1), named_args: SmallVec::new() });
        tree.insert_pattern(&env.kb, &view(pat), 2);

        assert_eq!(tree.query_raw(&env.kb, &view(ground)).len(), 2);
        let v99 = env.alloc(Term::Const(Literal::Int(99)));
        let q99 = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(v99, 1), named_args: SmallVec::new() });
        let r = tree.query_raw(&env.kb, &view(q99));
        assert_eq!(r.len(), 1);
        assert_eq!(r[0].0, 2);
    }
}
