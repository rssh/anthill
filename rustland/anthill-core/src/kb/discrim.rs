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
use super::term::{Literal, TermId, Var, VarId};
use super::term_view::{TermView, ViewHead, ViewItem};
use super::KnowledgeBase;
#[cfg(test)]
use super::term::Term;

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
    /// A `Rigid` (skolem / eigenvariable) var, keyed by its `VarId` *identity*.
    /// Unlike a wildcard var-edge (which matches any subterm), this concrete
    /// edge matches only the SAME rigid — a skolem is a constant, not a
    /// pattern var, so it belongs with the other constant keys (`Lit`/`Ref`/…),
    /// not in `var_edges`. This is what keeps two distinct skolems apart and
    /// stops a rigid goal var from over-matching a concrete fact.
    RigidVar(VarId),
    Bottom,
}

// ── DiscrimNode — tree node ─────────────────────────────────────

/// Children are `Rc<DiscrimNode>`, making the tree a PERSISTENT (path-copying)
/// structure: `Clone` is O(1) — a shallow copy of this node's edge maps as
/// `Rc` bumps, sharing every subtree. Mutation goes through `Rc::make_mut`, so
/// `insert` clones only the nodes along the touched path and leaves the rest
/// shared (proposal-050 / WI-537: a `FlowEnv`'s Γ overlay forks at every
/// control-flow split, and each fork must be O(path), not O(tree) — see
/// [`SubstTree::insert_walk`]).
///
/// One representation serves BOTH consumers: the Γ overlay (snapshots shared,
/// refcount > 1 → `make_mut` path-copies) and the main KB fact index (uniquely
/// owned during its mutable build, refcount == 1 → `make_mut` is a no-op
/// clone-wise, so index build cost is unchanged). `Drop` recurses only into
/// uniquely-owned children (see below), so a shared subtree is never freed
/// twice and a deep unique chain never overflows the host stack.
#[derive(Clone)]
struct DiscrimNode<L> {
    concrete: HashMap<DiscrimKey, Rc<DiscrimNode<L>>>,
    var_edges: Vec<(Var, Rc<DiscrimNode<L>>)>,
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
    // Children are `Rc`-shared: descend only into one we solely own
    // (`into_inner` is `Some` iff refcount was 1, consuming it). A child still
    // shared by another snapshot is left to its other owners — its `Rc` here
    // just decrements: no recursion, no double free.
    for (_, child) in std::mem::take(&mut node.concrete) {
        if let Some(inner) = Rc::into_inner(child) { stack.push(inner); }
    }
    for (_, child) in std::mem::take(&mut node.var_edges) {
        if let Some(inner) = Rc::into_inner(child) { stack.push(inner); }
    }
    // `leaves` are owned `L` values (RuleId-shaped in practice) — no
    // recursive Drop concern.
}

/// Descend into the child under `key` (creating it if absent), forking it for
/// writing via `Rc::make_mut`. The single home of the persistent-tree write
/// invariant on the concrete-edge insert path: a node shared with another
/// snapshot (a Γ overlay's COW fork) is path-copied here, while a uniquely-owned
/// node (the main index during its build, refcount 1) is edited in place.
fn make_mut_child<L: Clone>(
    map: &mut HashMap<DiscrimKey, Rc<DiscrimNode<L>>>,
    key: DiscrimKey,
) -> &mut DiscrimNode<L> {
    Rc::make_mut(map.entry(key).or_insert_with(|| Rc::new(DiscrimNode::new())))
}

/// As [`make_mut_child`] but for the remove path: fork an *existing* child for
/// writing, or `None` if absent. Same `make_mut` discipline — only the main
/// (unshared) index ever removes, so this never actually clones in practice.
fn get_mut_child<'a, L: Clone>(
    map: &'a mut HashMap<DiscrimKey, Rc<DiscrimNode<L>>>,
    key: &DiscrimKey,
) -> Option<&'a mut DiscrimNode<L>> {
    map.get_mut(key).map(Rc::make_mut)
}

// ── SubstTree — top-level structure ─────────────────────────────

#[derive(Clone)]
pub(crate) struct SubstTree<L> {
    root: DiscrimNode<L>,
}

impl<L> SubstTree<L> {
    pub(crate) fn new() -> Self {
        SubstTree { root: DiscrimNode::new() }
    }

    /// No stored pattern. The proposal-050 Γ overlay uses this to read whether
    /// the local context is the empty seed (Γ₀) vs a narrowed branch env.
    pub(crate) fn is_empty(&self) -> bool {
        self.root.is_empty()
    }
}

/// Whether [`SubstTree::insert_pattern`] can index `view` without tripping its
/// functor-less / `Opaque` panic — i.e. every head along the whole structure is
/// a concrete key (`Functor{Some}` / `Const` / `Ident` / `Ref` / `Bottom`) or a
/// variable (which routes to a var-edge). Mirrors the [`SubstTree::insert_walk`]
/// recursion, so it is the authoritative pre-check.
///
/// The proposal-050 (WI-537) Γ overlay uses this to SKIP a non-indexable fact —
/// a raw `if`-condition occurrence carrying an elaborated / `Opaque` (or
/// functor-less tuple/unit) sub-part. Such a fact could never unify with a
/// clean goal-shaped membership query, so excluding it is lossless; and it
/// spares the strict rule-head invariant `insert_pattern` rightly enforces
/// (loud panic) rather than weakening that invariant for the overlay's sake.
pub(crate) fn view_is_indexable<V: TermView>(kb: &KnowledgeBase, view: &V) -> bool {
    // A variable of any kind routes to a var-edge — always indexable.
    if view.index_var(kb).is_some() {
        return true;
    }
    match view.head(kb) {
        ViewHead::Functor { functor: Some(_), pos_arity, .. } => {
            (0..pos_arity).all(|i| {
                view.pos_arg(kb, i).map_or(false, |a| view_is_indexable(kb, &a))
            }) && view.named_keys(kb).into_iter().all(|s| {
                view.named_arg(kb, s).map_or(false, |a| view_is_indexable(kb, &a))
            })
        }
        ViewHead::Const(_) | ViewHead::Ident(_) | ViewHead::Ref(_) | ViewHead::Bottom => true,
        ViewHead::Functor { functor: None, .. } | ViewHead::Opaque => false,
        // Routed to a var-edge by `index_var` above; unreachable, treated as ok.
        ViewHead::Var(_) => true,
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

// `L: Clone` because `insert` / `remove` descend through `Rc::make_mut`, which
// clones a node when it is shared (a Γ snapshot). The main index is uniquely
// owned, so `make_mut` there never actually clones.
impl<L: Clone> SubstTree<L> {
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
        // A stored-pattern variable routes by kind (see [`TermView::index_var`]):
        // a flex `Global` / bound `DeBruijn` is a WILDCARD pattern var → a
        // var-edge (matches any subterm); a `Rigid` skolem is a CONSTANT → a
        // `RigidVar` concrete edge (matches only the same rigid).
        if let Some(var) = view.index_var(kb) {
            if let Var::Rigid(vid) = var {
                return make_mut_child(&mut node.concrete, DiscrimKey::RigidVar(vid));
            }
            let pos = node.var_edges.iter().position(|(v, _)| *v == var);
            return if let Some(idx) = pos {
                Rc::make_mut(&mut node.var_edges[idx].1)
            } else {
                node.var_edges.push((var, Rc::new(DiscrimNode::new())));
                let last = node.var_edges.len() - 1;
                Rc::make_mut(&mut node.var_edges[last].1)
            };
        }
        match view.head(kb) {
            ViewHead::Functor { functor: Some(functor), pos_arity, named_arity } => {
                let arity = pos_arity + named_arity;
                let n = make_mut_child(&mut node.concrete, DiscrimKey::Functor(functor));
                let n = make_mut_child(&mut n.concrete, DiscrimKey::Arity(arity as u16));
                Self::insert_walk_args(n, kb, view, pos_arity)
            }
            ViewHead::Const(lit) => make_mut_child(&mut node.concrete, DiscrimKey::Lit(lit)),
            ViewHead::Ident(sym) => make_mut_child(&mut node.concrete, DiscrimKey::Ident(sym)),
            ViewHead::Ref(sym) => make_mut_child(&mut node.concrete, DiscrimKey::Ref(sym)),
            ViewHead::Bottom => make_mut_child(&mut node.concrete, DiscrimKey::Bottom),
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
            cur = make_mut_child(&mut cur.concrete, DiscrimKey::Positional);
            cur = Self::insert_walk(cur, kb, &arg);
        }
        for sym in view.named_keys(kb) {
            let arg = view.named_arg(kb, sym).expect("named_arg present during insert");
            cur = make_mut_child(&mut cur.concrete, DiscrimKey::NamedKey(sym));
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
                let prune_fn = if let Some(fn_child) = get_mut_child(&mut node.concrete, &fk) {
                    let ak = DiscrimKey::Arity(arity as u16);
                    let prune_ar = if let Some(ar_child) = get_mut_child(&mut fn_child.concrete, &ak) {
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
        let prune = if let Some(child) = get_mut_child(&mut node.concrete, &key) {
            if let Some(pos) = child.leaves.iter().position(|l| l == leaf) {
                child.leaves.swap_remove(pos);
            }
            child.is_empty()
        } else { false };
        if prune {
            node.concrete.remove(&key);
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
        let prune = if let Some(marker_child) = get_mut_child(&mut node.concrete, &marker) {
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
                let prune_fn = if let Some(fn_child) = get_mut_child(&mut node.concrete, &fk) {
                    let ak = DiscrimKey::Arity(arity as u16);
                    let prune_ar = if let Some(ar_child) = get_mut_child(&mut fn_child.concrete, &ak) {
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
        let prune = if let Some(child) = get_mut_child(&mut node.concrete, &key) {
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
        self.query_raw_mode(kb, query, false)
    }

    /// Like [`query_raw`], but `match_mode` selects one-directional MATCHING:
    /// a flex-`Global` var in the *query* (target) is treated as an inert
    /// subterm — it matches only a stored PATTERN var (a var-edge), never a
    /// concrete stored structure, and is NOT itself bound. Resolution
    /// (`match_mode = false`) keeps the wildcard semantics (a query var binds to
    /// any stored structure). Only `query_resolved` (the matcher behind
    /// `match_view`) passes `true`; every resolution path passes `false`. The
    /// distinction is inert for a concrete/rigid target (no flex-`Global` head),
    /// so it changes nothing for existing `match_view` callers.
    pub(crate) fn query_raw_mode<V: TermView>(
        &self,
        kb: &KnowledgeBase,
        query: &V,
        match_mode: bool,
    ) -> Vec<(L, SmallSubst)> {
        let mut results = Vec::new();
        Self::query_node(&self.root, kb, query, VarPath::root(), SmallSubst::new(), match_mode, &mut results);
        results
    }

    /// [`query_resolved_mode`] with `match_mode = false` — the resolution
    /// (wildcard) leaf-resolve with `unify_rebind = false` (WI-633). Used by
    /// `match_view` (whose target may be a live goal whose flex-`Global` query
    /// vars SHOULD bind — assumed-fact discharge, reflect matching). The
    /// simp-rewriter's one-directional matcher uses `query_resolved_mode(.., true)`
    /// via `match_view_oneway`; SLD head-selection uses [`query_resolved_value`].
    pub(crate) fn query_resolved<V: TermView, F>(
        &self,
        kb: &KnowledgeBase,
        query: &V,
        resolve_term: F,
    ) -> Vec<(L, Substitution)>
    where
        F: Fn(&L) -> TermId,
    {
        self.query_resolved_mode(kb, query, false, resolve_term)
    }

    /// [`query_resolved`] with an explicit `match_mode`. `match_view` passes
    /// `true` (one-directional matching: a flex-`Global` target var is inert —
    /// matches only a stored pattern var, never a concrete fact, and is not
    /// bound). Everything else keeps the wildcard query-var semantics via
    /// [`query_resolved`] (`false`).
    pub(crate) fn query_resolved_mode<V: TermView, F>(
        &self,
        kb: &KnowledgeBase,
        query: &V,
        match_mode: bool,
        resolve_term: F,
    ) -> Vec<(L, Substitution)>
    where
        F: Fn(&L) -> TermId,
    {
        self.query_raw_mode(kb, query, match_mode).into_iter()
            .map(|(leaf, subst)| {
                let fact_term = resolve_term(&leaf);
                let s = subst.resolve_leaf(kb, fact_term, false);
                (leaf, s)
            })
            .collect()
    }

    /// Carrier-faithful peer of [`query_resolved`] (WI-348 Phase B). The fact
    /// head is resolved as a `Value`: a `Value::Term` head takes the fast term
    /// path ([`PersistSubst::resolve_leaf`]); any other carrier (a value fact
    /// with a `Value::Node` subterm) resolves deferred paths against the head's
    /// own `TermView` ([`PersistSubst::resolve_leaf_view`]), so named-arg
    /// positions read the same carrier the tree indexed (the term-store path
    /// would read a sorted-by-name skeleton — the named-order finding).
    ///
    /// This is the RESOLUTION path (SLD head selection via `query_view`, and the
    /// Γ overlay's `query_resolved_value` + `views_structurally_equal` filter),
    /// so a nonlinear pattern var UNIFIES its matched subterms (`unify_rebind =
    /// true`, WI-633) — the binding becomes part of the answer. `match_view`'s
    /// one-directional matching uses [`query_resolved`] instead.
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
                    Value::Term { id: t, .. } => subst.resolve_leaf(kb, *t, true),
                    _ => subst.resolve_leaf_view(kb, &head, true),
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
        match_mode: bool,
        results: &mut Vec<(L, SmallSubst)>,
    ) {
        match query.head(kb) {
            // Flex `Global`: in RESOLUTION a WILDCARD query var — binds this
            // position and matches every stored structure here. In MATCH mode
            // (`match_view`) a target var is INERT — it matches only a stored
            // PATTERN var (a var-edge, one-way `pattern-var ↦ target-var`), never
            // concrete stored structure, and is not itself bound (exactly the
            // `DeBruijn`/`Opaque` branch below).
            ViewHead::Var(Var::Global(vid)) if !match_mode => {
                let s = subst.with_binding(vid, BindValue::Path(path));
                Self::collect_all_leaves(node, s, results);
            }
            // `Rigid` skolem: a CONSTANT — matches only the same-id `RigidVar`
            // edge (plus universal var-edges, which a stored pattern var binds
            // to it), never a concrete fact or a different skolem.
            ViewHead::Var(Var::Rigid(vid)) => {
                Self::query_leaf_key(node, &DiscrimKey::RigidVar(vid), query, subst, results);
            }
            // MATCH mode's flex `Global` (the `!match_mode` arm above did not
            // fire) joins `DeBruijn`/`Opaque`: an INERT target var — bind a
            // stored pattern var to it, match no concrete fact, never self-bind.
            // `DeBruijn` never reaches a resolution goal head (binders open to
            // `Global`), and `Opaque` (closures, streams, lazies) has no concrete
            // key — all three route to universal var-edges only.
            ViewHead::Var(Var::Global(_) | Var::DeBruijn(_)) | ViewHead::Opaque => {
                for (tree_var, child) in &node.var_edges {
                    let branch = subst.clone().with_binding(tree_var.as_vid(), query.as_bind_value());
                    Self::collect_all_leaves(child, branch, results);
                }
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
                            // `path` is the prefix to this head's args — root at
                            // the top level; the args' own paths extend it.
                            Self::query_args(
                                n2, kb, query, 0, pos_arity, &named_keys, 0,
                                &path, subst.clone(), match_mode, results, &collect_leaves,
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
    /// when both cursors reach their ends. `prefix` is the [`VarPath`] to this
    /// container; each arg's own path extends it by one step, recorded so a
    /// query var — at any depth — binds to the matched fact's subterm (WI-373
    /// gap 3: nested binding extraction).
    #[allow(clippy::too_many_arguments)]
    fn query_args<V: TermView>(
        node: &DiscrimNode<L>,
        kb: &KnowledgeBase,
        query: &V,
        pos_idx: usize,
        pos_total: usize,
        named_keys: &[Symbol],
        named_idx: usize,
        prefix: &VarPath,
        subst: SmallSubst,
        match_mode: bool,
        results: &mut Vec<(L, SmallSubst)>,
        on_done: &dyn Fn(&DiscrimNode<L>, SmallSubst, &mut Vec<(L, SmallSubst)>),
    ) {
        if pos_idx >= pos_total && named_idx >= named_keys.len() {
            on_done(node, subst, results);
            return;
        }

        if pos_idx < pos_total {
            let arg_path = prefix.appended(ArgPos::Positional(pos_idx));
            if let Some(mc) = node.concrete.get(&DiscrimKey::Positional) {
                if let Some(arg) = query.pos_arg(kb, pos_idx) {
                    Self::query_arg_value(
                        mc, kb, arg, arg_path, prefix, query,
                        pos_idx + 1, pos_total, named_keys, named_idx,
                        subst, match_mode, results, on_done,
                    );
                }
            }
        } else {
            let sym = named_keys[named_idx];
            let arg_path = prefix.appended(ArgPos::Named(sym));
            if let Some(mc) = node.concrete.get(&DiscrimKey::NamedKey(sym)) {
                if let Some(arg) = query.named_arg(kb, sym) {
                    Self::query_arg_value(
                        mc, kb, arg, arg_path, prefix, query,
                        pos_idx, pos_total, named_keys, named_idx + 1,
                        subst, match_mode, results, on_done,
                    );
                }
            }
        }
    }

    /// Process one arg value, then continue with the remaining args of the
    /// outer query via `query_args`. `arg_path` is the [`VarPath`] addressing
    /// THIS arg (the container `prefix` extended by this arg's step); `prefix`
    /// is the container's own path, used to continue its remaining args. A
    /// query var here binds to `arg_path`; descending into a nested compound
    /// uses `arg_path` as the nested container's prefix, so vars at any depth
    /// record a full path (WI-373 gap 3).
    #[allow(clippy::too_many_arguments)]
    fn query_arg_value<V: TermView>(
        node: &DiscrimNode<L>,
        kb: &KnowledgeBase,
        arg: ViewItem<'_>,
        arg_path: VarPath,
        prefix: &VarPath,
        outer: &V,
        pos_idx: usize,
        pos_total: usize,
        named_keys: &[Symbol],
        named_idx: usize,
        subst: SmallSubst,
        match_mode: bool,
        results: &mut Vec<(L, SmallSubst)>,
        on_done: &dyn Fn(&DiscrimNode<L>, SmallSubst, &mut Vec<(L, SmallSubst)>),
    ) {
        match arg.head(kb) {
            // Flex `Global`: in RESOLUTION a WILDCARD arg var — binds this
            // position to any stored subterm and continues. In MATCH mode it is
            // INERT (folded into the `DeBruijn`/`Opaque` branch below).
            ViewHead::Var(Var::Global(vid)) if !match_mode => {
                let s = subst.with_binding(vid, BindValue::Path(arg_path));
                Self::skip_subtree_then_continue(
                    node, kb, outer, pos_idx, pos_total, named_keys, named_idx,
                    prefix, s, match_mode, results, on_done,
                );
            }
            // `Rigid` skolem: a CONSTANT arg — follows only the same-id
            // `RigidVar` edge (plus universal var-edges a pattern var binds to
            // it), never a concrete arg or a different skolem.
            ViewHead::Var(Var::Rigid(vid)) => {
                Self::follow_key_then_continue(
                    node, &DiscrimKey::RigidVar(vid), arg, kb, outer,
                    pos_idx, pos_total, named_keys, named_idx, prefix,
                    subst, match_mode, results, on_done,
                );
            }
            // MATCH mode's flex `Global` joins `DeBruijn`/`Opaque`: an INERT arg
            // var — binds a stored pattern var to it, matches no concrete arg,
            // never self-binds. `DeBruijn` never reaches a resolution goal arg;
            // `Opaque` has no concrete key.
            ViewHead::Var(Var::Global(_) | Var::DeBruijn(_)) | ViewHead::Opaque => {
                for (tree_var, child) in &node.var_edges {
                    let branch = subst.clone().with_binding(tree_var.as_vid(), arg.as_bind_value());
                    Self::query_args(
                        child, kb, outer, pos_idx, pos_total, named_keys, named_idx,
                        prefix, branch, match_mode, results, on_done,
                    );
                }
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
                                    prefix, subst, match_mode, results, on_done,
                                );
                            };
                            // Descend with `arg_path` as the nested container's
                            // prefix — nested vars extend it, not restart at root.
                            Self::query_args(
                                n2, kb, &arg, 0, pos_arity, &inner_named_keys, 0,
                                &arg_path, subst.clone(), match_mode, results, &nested_cont,
                            );
                        }
                    }
                }
                for (tree_var, child) in &node.var_edges {
                    let branch = subst.clone().with_binding(tree_var.as_vid(), arg.as_bind_value());
                    Self::query_args(
                        child, kb, outer, pos_idx, pos_total, named_keys, named_idx,
                        prefix, branch, match_mode, results, on_done,
                    );
                }
            }
            ViewHead::Const(lit) => {
                Self::follow_key_then_continue(
                    node, &DiscrimKey::Lit(lit), arg, kb, outer,
                    pos_idx, pos_total, named_keys, named_idx, prefix,
                    subst, match_mode, results, on_done,
                );
            }
            ViewHead::Ident(sym) => {
                Self::follow_key_then_continue(
                    node, &DiscrimKey::Ident(sym), arg, kb, outer,
                    pos_idx, pos_total, named_keys, named_idx, prefix,
                    subst, match_mode, results, on_done,
                );
            }
            ViewHead::Ref(sym) => {
                Self::follow_key_then_continue(
                    node, &DiscrimKey::Ref(sym), arg, kb, outer,
                    pos_idx, pos_total, named_keys, named_idx, prefix,
                    subst, match_mode, results, on_done,
                );
            }
            ViewHead::Bottom => {
                Self::follow_key_then_continue(
                    node, &DiscrimKey::Bottom, arg, kb, outer,
                    pos_idx, pos_total, named_keys, named_idx, prefix,
                    subst, match_mode, results, on_done,
                );
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
        prefix: &VarPath,
        subst: SmallSubst,
        match_mode: bool,
        results: &mut Vec<(L, SmallSubst)>,
        on_done: &dyn Fn(&DiscrimNode<L>, SmallSubst, &mut Vec<(L, SmallSubst)>),
    ) {
        if let Some(child) = node.concrete.get(key) {
            Self::query_args(
                child, kb, outer, pos_idx, pos_total, named_keys, named_idx,
                prefix, subst.clone(), match_mode, results, on_done,
            );
        }
        for (tree_var, child) in &node.var_edges {
            let branch = subst.clone().with_binding(tree_var.as_vid(), arg.as_bind_value());
            Self::query_args(
                child, kb, outer, pos_idx, pos_total, named_keys, named_idx,
                prefix, branch, match_mode, results, on_done,
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
        prefix: &VarPath,
        subst: SmallSubst,
        match_mode: bool,
        results: &mut Vec<(L, SmallSubst)>,
        on_done: &dyn Fn(&DiscrimNode<L>, SmallSubst, &mut Vec<(L, SmallSubst)>),
    ) {
        Self::query_args(
            node, kb, outer, pos_idx, pos_total, named_keys, named_idx,
            prefix, subst.clone(), match_mode, results, on_done,
        );
        for (_, child) in &node.concrete {
            Self::skip_subtree_then_continue(
                child, kb, outer, pos_idx, pos_total, named_keys, named_idx,
                prefix, subst.clone(), match_mode, results, on_done,
            );
        }
        for (_, child) in &node.var_edges {
            Self::skip_subtree_then_continue(
                child, kb, outer, pos_idx, pos_total, named_keys, named_idx,
                prefix, subst.clone(), match_mode, results, on_done,
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
    fn wi436_nullary_constructor_fn_matches_bare_ref() {
        // WI-436: a fact whose arg is a nullary constructor APPLICATION `Fn{red}`
        // must be found by a query spelling the same constructor BARE `Ref(red)`
        // (and vice versa) — the two are one value. Both insert and query key the
        // arg under `DiscrimKey::Ref(red)` via the canonicalized `head()`.
        let mut env = TestEnv::new();
        let red = env.intern("Color.red");
        let color = env.intern("Color");
        // register `red` as a constructor of sort `Color` (Fn-form entity identity).
        let red_entity = env.alloc(Term::Fn {
            functor: red, pos_args: SmallVec::new(), named_args: SmallVec::new(),
        });
        let color_t = env.alloc(Term::Ref(color));
        env.kb.register_entity_of(red_entity, color_t);
        assert!(env.kb.is_constructor_symbol(red));

        let holds = env.intern("holds");
        let red_fn = env.alloc(Term::Fn {
            functor: red, pos_args: SmallVec::new(), named_args: SmallVec::new(),
        });
        let red_ref = env.alloc(Term::Ref(red));
        let fact_fn = env.alloc(Term::Fn {
            functor: holds, pos_args: SmallVec::from_elem(red_fn, 1), named_args: SmallVec::new(),
        });
        let query_ref = env.alloc(Term::Fn {
            functor: holds, pos_args: SmallVec::from_elem(red_ref, 1), named_args: SmallVec::new(),
        });

        // fact stored in `Fn{red}` form, queried in bare `Ref(red)` form → match.
        let mut tree: SubstTree<u32> = SubstTree::new();
        tree.insert_ground(&env.kb, &view(fact_fn), 1);
        let res = make_resolver(vec![(1, fact_fn)]);
        assert_eq!(tree.query_resolved(&env.kb, &view(query_ref), &res).len(), 1,
            "bare Ref(red) query must match a stored nullary Fn{{red}} fact");

        // …and the reverse: fact stored bare `Ref(red)`, queried as `Fn{red}`.
        let mut tree2: SubstTree<u32> = SubstTree::new();
        tree2.insert_ground(&env.kb, &view(query_ref), 2);
        let res2 = make_resolver(vec![(2, query_ref)]);
        assert_eq!(tree2.query_resolved(&env.kb, &view(fact_fn), &res2).len(), 1,
            "nullary Fn{{red}} query must match a stored bare Ref(red) fact");
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
            let bound = subst.resolve_as_value(vid).map(|v| v.expect_term()).expect("bound");
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
        assert_eq!(results[0].1.resolve_as_value(xv).map(|v| v.expect_term()).unwrap(), vid);
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
            let bound = subst.resolve_as_value(vid).map(|v| v.expect_term()).unwrap();
            match leaf { 1 => assert_eq!(bound, tf), 2 => assert_eq!(bound, tg), _ => panic!() }
        }
    }

    #[test]
    fn nested_var_binds_to_fact_subterm() {
        // WI-373 gap 3: a query var at a NESTED position must bind to the matched
        // fact's subterm. Insert ground fact f(g(42)), query f(g(?y)); ?y → 42.
        // Before the nested binding-extraction, ?y recorded no path and resolved
        // to None (the fact was found but the var was silently unbound).
        let mut env = TestEnv::new();
        let mut tree: SubstTree<u32> = SubstTree::new();
        let f = env.intern("f");
        let g = env.intern("g");
        let v42 = env.alloc(Term::Const(Literal::Int(42)));
        let g42 = env.alloc(Term::Fn { functor: g, pos_args: SmallVec::from_elem(v42, 1), named_args: SmallVec::new() });
        let fact = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(g42, 1), named_args: SmallVec::new() });
        tree.insert_ground(&env.kb, &view(fact), 1);

        let yv = env.fresh_var("y");
        let var_y = env.alloc(Term::Var(Var::Global(yv)));
        let gy = env.alloc(Term::Fn { functor: g, pos_args: SmallVec::from_elem(var_y, 1), named_args: SmallVec::new() });
        let pat = env.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(gy, 1), named_args: SmallVec::new() });
        let results = tree.query_resolved(&env.kb, &view(pat), |_| fact);
        assert_eq!(results.len(), 1, "fact should be found");
        let bound = results[0].1.resolve_as_value(yv).map(|v| v.expect_term());
        assert_eq!(bound, Some(v42), "nested ?y must bind to 42, got {:?}", bound);
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
