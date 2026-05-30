//! Unified view over `TermId`-backed and `Value`-backed terms.
//!
//! Per proposal 026.1 Q2. The resolver needs to unify a rule-head pattern
//! (always `TermId`) against a target that could be either KB-resident
//! (`TermId`) or an external-sourced runtime `Value`. `TermView` is the
//! read-only shape used on the target side of unification.
//!
//! WI-276: `Value::Node` (a reflect `Expr` occurrence) is now *structural*
//! here — its `head`/`pos_arg`/`named_arg` expose the underlying `Expr` so a
//! `[simp]` rule LHS can match against expression occurrences (the substrate
//! for the typer-phase rewriting engine, proposal 043). Previously it was
//! `Opaque`.
//!
//! This module defines the trait and implementations. Direct structural
//! unification via `match_view` lives in `kb::mod`.

use std::rc::Rc;

use crate::eval::value::Value;
use crate::intern::Symbol;

use super::node_occurrence::{EffectExprNode, Expr, NodeOccurrence, TypeChild, TypeNode};
use super::persist_subst::BindValue;
use super::term::{Literal, Term, TermId, Var, VarId};
use super::KnowledgeBase;

/// The outermost shape of a term/value, enough to drive unification
/// dispatch. Structural details beneath a head are fetched via
/// [`TermView::pos_arg`] / [`TermView::named_arg`].
#[derive(Clone, Debug)]
pub enum ViewHead {
    /// Logic variable (Global — DeBruijn has been opened).
    Var(VarId),
    /// Literal constant.
    Const(Literal),
    /// Function / constructor application. Used for both `Term::Fn` and
    /// `Value::Entity` / `Value::Tuple`, distinguished by whether `functor`
    /// is `Some`.
    Functor { functor: Option<Symbol>, pos_arity: usize, named_arity: usize },
    /// Reference to a named symbol.
    Ref(Symbol),
    /// Bare identifier (not yet resolved).
    Ident(Symbol),
    /// Bottom term `⊥`.
    Bottom,
    /// Anything else — closures, streams, lazies. Treated as opaque by
    /// unification (compare by pointer identity if needed).
    Opaque,
}

/// A child of a [`TermView`] — a `TermId` (borrowed from the KB's
/// hash-consed store), a `Value` (borrowed from the owning [`TermView`]),
/// or a reflect `Expr` occurrence child (`Node`). The `Node` variant *owns*
/// an `Rc<NodeOccurrence>` (a cheap clone) rather than borrowing, so that
/// [`TermView::as_bind_value`] can bind a matched child as `Value::Node`
/// (WI-276). `'a` is the lifetime of the borrowed `Value`.
///
/// `Clone` but **not** `Copy`: the `Node` variant carries an `Rc`.
#[derive(Clone, Debug)]
pub enum ViewItem<'a> {
    Term(TermId),
    Value(&'a Value),
    Node(Rc<NodeOccurrence>),
}

// ── Occurrence views (WI-276) ──────────────────────────────────
//
// `Value::Node` / `ViewItem::Node` expose a reflect `Expr` occurrence to the
// matcher. Only the Apply / Constructor / leaf forms are made structural —
// those a `[simp]` rule LHS matches; control-flow forms (Match / If / Let /
// Lambda / collection literals / *Within / …) stay `Opaque`. `Expr::DotApply`
// (added by WI-278) will get an arm here mapping to a `dot_apply` functor.

fn occ_head(occ: &NodeOccurrence, kb: &KnowledgeBase) -> ViewHead {
    // WI-342: a Value-carried Type / EffectExpression occurrence reads through
    // the same `ViewHead::Functor` as its hash-consed `Term::Fn` twin, so a
    // carrier-blind walker (resolver `match_view` today; the typer's
    // `unify_types` after P3) sees identical structure regardless of carrier.
    if let Some(tn) = occ.as_type() {
        return type_node_head(tn, kb);
    }
    if let Some(en) = occ.as_effect_expr() {
        return effect_expr_head(en, kb);
    }
    match occ.as_expr() {
        Some(Expr::Apply { functor, pos_args, named_args, .. }) => ViewHead::Functor {
            functor: Some(*functor),
            pos_arity: pos_args.len(),
            named_arity: named_args.len(),
        },
        Some(Expr::Constructor { name, pos_args, named_args }) => ViewHead::Functor {
            functor: Some(*name),
            pos_arity: pos_args.len(),
            named_arity: named_args.len(),
        },
        Some(Expr::Const(lit)) => ViewHead::Const(lit.clone()),
        Some(Expr::Ref(s)) => ViewHead::Ref(*s),
        Some(Expr::Ident(s)) => ViewHead::Ident(*s),
        Some(Expr::Var(Var::Global(vid))) => ViewHead::Var(*vid),
        // Rigid / DeBruijn vars, control-flow and post-elaboration forms,
        // and rule-head occurrences are opaque to rule-LHS matching.
        _ => ViewHead::Opaque,
    }
}

/// The i-th positional child occurrence of an Apply/Constructor occurrence.
/// Type / EffectExpression occurrences expose only named children (none
/// positional), so this is `None` for them.
fn occ_pos_child(occ: &NodeOccurrence, _kb: &KnowledgeBase, i: usize) -> Option<Rc<NodeOccurrence>> {
    match occ.as_expr()? {
        Expr::Apply { pos_args, .. } | Expr::Constructor { pos_args, .. } => {
            pos_args.get(i).map(Rc::clone)
        }
        _ => None,
    }
}

/// The named child keyed by `sym` of an Apply/Constructor occurrence, or — for
/// a Value-carried Type / EffectExpression occurrence (WI-342) — the matching
/// named field. A poisoned `TypeChild::Node` child is itself a child
/// occurrence; a `TypeChild::Ground` child is a hash-consed `TermId`, which
/// `occ_named_child` cannot return as an `Rc<NodeOccurrence>` — Type/EffectExpr
/// callers go through [`type_node_named`] / [`effect_expr_named`] (returning a
/// `ViewItem`) instead. This `Rc`-returning helper stays Expr-only.
fn occ_named_child(occ: &NodeOccurrence, _kb: &KnowledgeBase, sym: Symbol) -> Option<Rc<NodeOccurrence>> {
    let named = match occ.as_expr()? {
        Expr::Apply { named_args, .. } | Expr::Constructor { named_args, .. } => named_args,
        _ => return None,
    };
    named.iter().find(|(s, _)| *s == sym).map(|(_, c)| Rc::clone(c))
}

fn occ_named_keys(occ: &NodeOccurrence, kb: &KnowledgeBase) -> Vec<Symbol> {
    if let Some(tn) = occ.as_type() {
        return type_node_keys(tn, kb);
    }
    if let Some(en) = occ.as_effect_expr() {
        return effect_expr_keys(en, kb);
    }
    match occ.as_expr() {
        Some(Expr::Apply { named_args, .. }) | Some(Expr::Constructor { named_args, .. }) => {
            named_args.iter().map(|(s, _)| *s).collect()
        }
        _ => Vec::new(),
    }
}

// ── Type / EffectExpression view arms (WI-342) ──────────────────
//
// These read a `Value`-carried Type / EffectExpression occurrence through the
// SAME functor + named-key surface as its `Term::Fn` twin. Functor symbols are
// resolved via the (immutable) qualified-name table; field keys via the bare
// intern table — the exact symbols the `make_*` `TermId` builders used, so the
// two carriers are indistinguishable through `TermView`.
//
// Rep A (collapse): `parameterized.bindings` (a `List[TypeBinding]` of generic
// entities) is NOT exposed through the generic named-key surface in this slice
// — it is read type-specifically (`as_type`) and its carrier-faithful generic
// view is deferred to P3 (where `unify_parameterized`-on-`TermView` drives it).
//
// DEFERRED TO P3 (decided): symbol resolution here is provisional. (1) The
// `format!` + table lookup runs per view call; (2) `type_node_head` /
// `effect_expr_head` report `named_arity` from a hardcoded count while
// `type_node_keys` / `effect_expr_keys` resolve keys via `lookup_symbol` and
// `filter_map`-drop any not-yet-interned key — so on a KB where a field key was
// never interned, `head` arity and `named_keys` can disagree (a discrim walk
// would then mis-depth). Neither bites this slice: the only caller is the
// producer↔view test on a `register_prelude`d KB where every field key is
// interned. P3 replaces all of this with a KB-cached `TypeSyms` (mirroring
// `ReflectSyms` below) resolved once at prelude time — one source of truth for
// functor + field-key symbols, no per-call alloc, no silent drop — validated by
// the first live consumer.

fn type_functor_sym(kb: &KnowledgeBase, short: &str) -> Option<Symbol> {
    kb.try_resolve_symbol(&format!("anthill.prelude.Type.{short}"))
}

fn effect_functor_sym(kb: &KnowledgeBase, short: &str) -> Option<Symbol> {
    kb.try_resolve_symbol(&format!("anthill.prelude.EffectExpression.{short}"))
}

/// A `TypeChild` as a non-borrowing [`ViewItem`]: ground → `Term`, poisoned →
/// `Node` (a cheap `Rc` clone). Neither variant borrows from `child`, so the
/// returned item is free of the caller's borrow.
pub(crate) fn type_child_view_item<'a>(child: &TypeChild) -> ViewItem<'a> {
    match child {
        TypeChild::Ground(t) => ViewItem::Term(*t),
        TypeChild::Node(rc) => ViewItem::Node(Rc::clone(rc)),
    }
}

fn type_node_head(tn: &TypeNode, kb: &KnowledgeBase) -> ViewHead {
    let (short, named_arity) = match tn {
        // `bindings` deferred (Rep A) → exposed arity is `base` only.
        TypeNode::Denoted { .. } => ("denoted", 1),
        TypeNode::Parameterized { .. } => ("parameterized", 1),
        TypeNode::EffectsRows { .. } => ("effects_rows", 1),
        TypeNode::Arrow { .. } => ("arrow", 3),
        // Fields are not a uniformly-exposed named child (like Parameterized's
        // bindings); they're read via the dedicated `named_tuple_fields` reader.
        TypeNode::NamedTuple { .. } => ("named_tuple", 0),
    };
    match type_functor_sym(kb, short) {
        Some(f) => ViewHead::Functor { functor: Some(f), pos_arity: 0, named_arity },
        None => ViewHead::Opaque,
    }
}

fn type_node_keys(tn: &TypeNode, kb: &KnowledgeBase) -> Vec<Symbol> {
    let keys: &[&str] = match tn {
        TypeNode::Denoted { .. } => &["value"],
        TypeNode::Parameterized { .. } => &["base"],
        TypeNode::EffectsRows { .. } => &["effects_expr"],
        TypeNode::Arrow { .. } => &["param", "result", "effects"],
        TypeNode::NamedTuple { .. } => &[],
    };
    keys.iter().filter_map(|k| kb.lookup_symbol(k)).collect()
}

fn type_node_named<'a>(tn: &TypeNode, kb: &KnowledgeBase, sym: Symbol) -> Option<ViewItem<'a>> {
    let key = |k: &str| kb.lookup_symbol(k);
    match tn {
        TypeNode::Denoted { value } if Some(sym) == key("value") => {
            Some(ViewItem::Node(Rc::clone(value)))
        }
        TypeNode::Parameterized { base, .. } if Some(sym) == key("base") => {
            Some(type_child_view_item(base))
        }
        TypeNode::EffectsRows { effects_expr } if Some(sym) == key("effects_expr") => {
            Some(type_child_view_item(effects_expr))
        }
        TypeNode::Arrow { param, result, effects } => {
            if Some(sym) == key("param") {
                Some(type_child_view_item(param))
            } else if Some(sym) == key("result") {
                Some(type_child_view_item(result))
            } else if Some(sym) == key("effects") {
                Some(type_child_view_item(effects))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn effect_expr_head(en: &EffectExprNode, kb: &KnowledgeBase) -> ViewHead {
    let (short, named_arity) = match en {
        EffectExprNode::Merge { .. } => ("merge", 2),
        EffectExprNode::Present { .. } => ("present", 1),
        EffectExprNode::Absent { .. } => ("absent", 1),
        EffectExprNode::Open { .. } => ("open", 1),
        EffectExprNode::EmptyRow => ("empty_row", 0),
    };
    match effect_functor_sym(kb, short) {
        Some(f) => ViewHead::Functor { functor: Some(f), pos_arity: 0, named_arity },
        None => ViewHead::Opaque,
    }
}

fn effect_expr_keys(en: &EffectExprNode, kb: &KnowledgeBase) -> Vec<Symbol> {
    let keys: &[&str] = match en {
        EffectExprNode::Merge { .. } => &["left", "right"],
        EffectExprNode::Present { .. } | EffectExprNode::Absent { .. } => &["label"],
        EffectExprNode::Open { .. } => &["tail"],
        EffectExprNode::EmptyRow => &[],
    };
    keys.iter().filter_map(|k| kb.lookup_symbol(k)).collect()
}

fn effect_expr_named<'a>(
    en: &EffectExprNode,
    kb: &KnowledgeBase,
    sym: Symbol,
) -> Option<ViewItem<'a>> {
    let key = |k: &str| kb.lookup_symbol(k);
    match en {
        EffectExprNode::Merge { left, right } => {
            if Some(sym) == key("left") {
                Some(type_child_view_item(left))
            } else if Some(sym) == key("right") {
                Some(type_child_view_item(right))
            } else {
                None
            }
        }
        EffectExprNode::Present { label } | EffectExprNode::Absent { label }
            if Some(sym) == key("label") =>
        {
            Some(type_child_view_item(label))
        }
        EffectExprNode::Open { tail } if Some(sym) == key("tail") => {
            Some(type_child_view_item(tail))
        }
        _ => None,
    }
}

/// Shared `named_arg` for a Value-carried Type / EffectExpression occurrence —
/// returns a `ViewItem` (a ground child is a `Term`, a poisoned child a
/// `Node`). Returns `None` for any other kind, so Expr callers fall back to the
/// `Rc`-returning `occ_named_child`.
fn occ_type_named<'a>(
    occ: &NodeOccurrence,
    kb: &KnowledgeBase,
    sym: Symbol,
) -> Option<ViewItem<'a>> {
    if let Some(tn) = occ.as_type() {
        return type_node_named(tn, kb, sym);
    }
    if let Some(en) = occ.as_effect_expr() {
        return effect_expr_named(en, kb, sym);
    }
    None
}

/// Read-only view over a term or value, used on the target side of
/// unification. The blanket impls on `TermId` and `Value` mean callers can
/// pass either representation into `match_view` / future Value-aware
/// resolver paths.
pub trait TermView {
    fn head(&self, kb: &KnowledgeBase) -> ViewHead;
    fn pos_arg<'a>(&'a self, kb: &'a KnowledgeBase, i: usize) -> Option<ViewItem<'a>>;
    fn named_arg<'a>(&'a self, kb: &'a KnowledgeBase, sym: Symbol) -> Option<ViewItem<'a>>;

    /// The symbol keys of all named args, in canonical order. Used by the
    /// discrim tree walker to iterate named positions without needing GATs
    /// or borrow-through-trait. Allocating a `Vec` here parallels the
    /// existing SmallVec-clone that `query_node` already did on the
    /// TermId path.
    fn named_keys(&self, kb: &KnowledgeBase) -> Vec<Symbol>;

    /// Capture this view's identity as a [`BindValue`] — used when the
    /// tree's variable-edge captures the current query side. TermId-backed
    /// views produce `BindValue::Term`; Value-backed views clone into
    /// `BindValue::Value`. Called at the top level (when the query's head
    /// itself matches a tree-var) and at sub-arg var-edge captures.
    fn as_bind_value(&self) -> BindValue;

    /// The logic variable at this view's head, for discrimination-tree
    /// *indexing* (insert / remove of a stored pattern). Unlike [`head`],
    /// which collapses Rigid / DeBruijn vars to `Opaque` (goal-side
    /// semantics: a rigid goal var must not match concrete keys), the index
    /// side keys a stored-pattern variable of *any* kind as a var-edge.
    /// Returns the full `Var` so distinct binders (`DeBruijn(0)` vs
    /// `DeBruijn(1)`) key distinct edges. `None` for non-variable heads — the
    /// walk then keys on [`head`]. Default reads a `Global` var off [`head`];
    /// the `TermId` / `Value` carriers override to also surface Rigid /
    /// DeBruijn (WI-348).
    fn index_var(&self, kb: &KnowledgeBase) -> Option<Var> {
        match self.head(kb) {
            ViewHead::Var(vid) => Some(Var::Global(vid)),
            _ => None,
        }
    }
}

/// Wrapper so we can `impl TermView for TermIdView` without orphan-rule
/// issues on the bare `TermId` type.
#[derive(Clone, Copy, Debug)]
pub struct TermIdView(pub TermId);

impl TermView for TermIdView {
    fn head(&self, kb: &KnowledgeBase) -> ViewHead {
        match kb.get_term(self.0) {
            Term::Var(Var::Global(vid)) => ViewHead::Var(*vid),
            // Rigid (skolem) is opaque: it matches only stored patterns
            // that have a wildcard (var_edge) at this position, never
            // concrete-key patterns. WI-108 — without this, the discrim
            // would treat a Rigid like a flex var, allowing a goal
            // `pred(!rigid)` to falsely unify with a fact `pred(leaf)`.
            Term::Var(Var::Rigid(_)) => ViewHead::Opaque,
            Term::Var(Var::DeBruijn(_)) => ViewHead::Opaque,
            Term::Const(lit) => ViewHead::Const(lit.clone()),
            Term::Fn { functor, pos_args, named_args } => ViewHead::Functor {
                functor: Some(*functor),
                pos_arity: pos_args.len(),
                named_arity: named_args.len(),
            },
            Term::Ref(s) => ViewHead::Ref(*s),
            Term::Ident(s) => ViewHead::Ident(*s),
            Term::Bottom => ViewHead::Bottom,
            Term::ParseAux(_) => unreachable!(
                "parse-only Term::ParseAux variant reached the KB-side TermIdView",
            ),
        }
    }

    fn pos_arg<'a>(&'a self, kb: &'a KnowledgeBase, i: usize) -> Option<ViewItem<'a>> {
        match kb.get_term(self.0) {
            Term::Fn { pos_args, .. } => pos_args.get(i).copied().map(ViewItem::Term),
            _ => None,
        }
    }

    fn named_arg<'a>(&'a self, kb: &'a KnowledgeBase, sym: Symbol) -> Option<ViewItem<'a>> {
        match kb.get_term(self.0) {
            Term::Fn { named_args, .. } => named_args.iter()
                .find(|(s, _)| *s == sym)
                .map(|(_, t)| ViewItem::Term(*t)),
            _ => None,
        }
    }

    fn named_keys(&self, kb: &KnowledgeBase) -> Vec<Symbol> {
        match kb.get_term(self.0) {
            Term::Fn { named_args, .. } => named_args.iter().map(|(s, _)| *s).collect(),
            _ => Vec::new(),
        }
    }

    fn as_bind_value(&self) -> BindValue {
        BindValue::Term(self.0)
    }

    fn index_var(&self, kb: &KnowledgeBase) -> Option<Var> {
        match kb.get_term(self.0) {
            Term::Var(v) => Some(*v),
            _ => None,
        }
    }
}

impl TermView for Value {
    fn head(&self, kb: &KnowledgeBase) -> ViewHead {
        match self {
            Value::Term(tid) => TermIdView(*tid).head(kb),
            Value::Int(n) => ViewHead::Const(Literal::Int(*n)),
            Value::BigInt(n) => ViewHead::Const(Literal::BigInt(n.clone())),
            Value::Float(f) => ViewHead::Const(Literal::Float(ordered_float::OrderedFloat(*f))),
            Value::Bool(b) => ViewHead::Const(Literal::Bool(*b)),
            Value::Str(s) => ViewHead::Const(Literal::String(s.clone())),
            Value::Unit => ViewHead::Functor {
                functor: None,
                pos_arity: 0,
                named_arity: 0,
            },
            Value::Tuple { pos, named } => ViewHead::Functor {
                functor: None,
                pos_arity: pos.len(),
                named_arity: named.len(),
            },
            Value::Entity { functor, pos, named } => ViewHead::Functor {
                functor: Some(*functor),
                pos_arity: pos.len(),
                named_arity: named.len(),
            },
            // WI-276: a reflect Expr occurrence is structural — expose its Expr.
            // WI-342: Type / EffectExpr occurrences expose their functor too.
            Value::Node(occ) => occ_head(occ, kb),
            // WI-109: a value-level logic variable views the same as the
            // matching `Term::Var` (TermIdView): flex `Global` is a unifiable
            // var head; `Rigid` / `DeBruijn` are opaque (match stored
            // wildcard patterns only, never concrete-key patterns).
            Value::Var(Var::Global(vid)) => ViewHead::Var(*vid),
            Value::Var(Var::Rigid(_)) | Value::Var(Var::DeBruijn(_)) => ViewHead::Opaque,
            Value::Closure(_)
            | Value::Stream(_)
            | Value::Lazy(_)
            | Value::Substitution(_)
            | Value::Map(_)
            | Value::Cell(_)
            | Value::Requirement(_) => ViewHead::Opaque,
        }
    }

    fn pos_arg<'a>(&'a self, kb: &'a KnowledgeBase, i: usize) -> Option<ViewItem<'a>> {
        // Can't construct a temporary TermIdView and delegate — the
        // returned ViewItem would outlive it. Inline the TermId path.
        match self {
            Value::Term(tid) => match kb.get_term(*tid) {
                Term::Fn { pos_args, .. } => pos_args.get(i).copied().map(ViewItem::Term),
                _ => None,
            },
            Value::Tuple { pos, .. } => pos.get(i).map(ViewItem::Value),
            Value::Entity { pos, .. } => pos.get(i).map(ViewItem::Value),
            Value::Node(occ) => occ_pos_child(occ, kb, i).map(ViewItem::Node),
            _ => None,
        }
    }

    fn named_arg<'a>(&'a self, kb: &'a KnowledgeBase, sym: Symbol) -> Option<ViewItem<'a>> {
        match self {
            Value::Term(tid) => match kb.get_term(*tid) {
                Term::Fn { named_args, .. } => named_args.iter()
                    .find(|(s, _)| *s == sym)
                    .map(|(_, t)| ViewItem::Term(*t)),
                _ => None,
            },
            Value::Tuple { named, .. } => {
                named.iter().find(|(s, _)| *s == sym).map(|(_, v)| ViewItem::Value(v))
            }
            Value::Entity { named, .. } => {
                named.iter().find(|(s, _)| *s == sym).map(|(_, v)| ViewItem::Value(v))
            }
            // WI-342: a Type/EffectExpr child may be ground (`Term`) — handle
            // both via `occ_type_named`; fall back to the Expr `Rc` reader.
            Value::Node(occ) => occ_type_named(occ, kb, sym)
                .or_else(|| occ_named_child(occ, kb, sym).map(ViewItem::Node)),
            _ => None,
        }
    }

    fn named_keys(&self, kb: &KnowledgeBase) -> Vec<Symbol> {
        match self {
            Value::Term(tid) => match kb.get_term(*tid) {
                Term::Fn { named_args, .. } => named_args.iter().map(|(s, _)| *s).collect(),
                _ => Vec::new(),
            },
            Value::Tuple { named, .. } => named.iter().map(|(s, _)| *s).collect(),
            Value::Entity { named, .. } => named.iter().map(|(s, _)| *s).collect(),
            Value::Node(occ) => occ_named_keys(occ, kb),
            _ => Vec::new(),
        }
    }

    fn as_bind_value(&self) -> BindValue {
        match self {
            Value::Term(tid) => BindValue::Term(*tid),
            // Value::Node clones cheaply (Rc), preserving occurrence identity.
            other => BindValue::Value(other.clone()),
        }
    }

    fn index_var(&self, kb: &KnowledgeBase) -> Option<Var> {
        match self {
            Value::Term(tid) => match kb.get_term(*tid) {
                Term::Var(v) => Some(*v),
                _ => None,
            },
            Value::Var(v) => Some(*v),
            // Occurrence heads surface only `Global` vars; an occurrence whose
            // head is a Rigid / DeBruijn binder reads `Opaque` (`occ_head`), so
            // this returns `None` and the insert walk then keys on `head` —
            // which is `Opaque`, and so panics (discrim insert guard #1). That
            // is intentional for now: a value rule head carrying a DeBruijn
            // binder is Phase-C work (WI-348). Surfacing those binders as
            // distinct var-edges here is the Phase-C fix; until then they fail
            // loudly rather than silently mis-index (Phase A review guard #2).
            Value::Node(_) => match self.head(kb) {
                ViewHead::Var(vid) => Some(Var::Global(vid)),
                _ => None,
            },
            _ => None,
        }
    }
}

/// WI-277: an occurrence is itself a first-class match target. Implementing
/// `TermView` directly on `Rc<NodeOccurrence>` keeps the typer-phase rewrite
/// loop `Rc<NodeOccurrence> → Rc<NodeOccurrence>` — `match_view(lhs, &occ)`
/// reads the occurrence in place, the rebuilt result is the next `Rc` — with
/// no `Value::Node` wrap/unwrap between match and rebuild on each iteration.
/// (`Value::Node` still appears *inside* the substitution as a bound child,
/// which is intrinsic and a single `Rc` bump.) Reuses the `occ_*` helpers.
impl TermView for Rc<NodeOccurrence> {
    fn head(&self, kb: &KnowledgeBase) -> ViewHead {
        occ_head(self, kb)
    }

    fn pos_arg<'a>(&'a self, kb: &'a KnowledgeBase, i: usize) -> Option<ViewItem<'a>> {
        occ_pos_child(self, kb, i).map(ViewItem::Node)
    }

    fn named_arg<'a>(&'a self, kb: &'a KnowledgeBase, sym: Symbol) -> Option<ViewItem<'a>> {
        occ_type_named(self, kb, sym)
            .or_else(|| occ_named_child(self, kb, sym).map(ViewItem::Node))
    }

    fn named_keys(&self, kb: &KnowledgeBase) -> Vec<Symbol> {
        occ_named_keys(self, kb)
    }

    fn as_bind_value(&self) -> BindValue {
        BindValue::Value(Value::Node(Rc::clone(self)))
    }
}

impl TermView for ViewItem<'_> {
    fn head(&self, kb: &KnowledgeBase) -> ViewHead {
        match self {
            ViewItem::Term(t) => TermIdView(*t).head(kb),
            ViewItem::Value(v) => (**v).head(kb),
            ViewItem::Node(occ) => occ_head(occ, kb),
        }
    }

    fn pos_arg<'a>(&'a self, kb: &'a KnowledgeBase, i: usize) -> Option<ViewItem<'a>> {
        match self {
            ViewItem::Term(t) => match kb.get_term(*t) {
                Term::Fn { pos_args, .. } => pos_args.get(i).copied().map(ViewItem::Term),
                _ => None,
            },
            ViewItem::Value(v) => (*v).pos_arg(kb, i),
            ViewItem::Node(occ) => occ_pos_child(occ, kb, i).map(ViewItem::Node),
        }
    }

    fn named_arg<'a>(&'a self, kb: &'a KnowledgeBase, sym: Symbol) -> Option<ViewItem<'a>> {
        match self {
            ViewItem::Term(t) => match kb.get_term(*t) {
                Term::Fn { named_args, .. } => named_args.iter()
                    .find(|(s, _)| *s == sym)
                    .map(|(_, t)| ViewItem::Term(*t)),
                _ => None,
            },
            ViewItem::Value(v) => (*v).named_arg(kb, sym),
            ViewItem::Node(occ) => occ_type_named(occ, kb, sym)
                .or_else(|| occ_named_child(occ, kb, sym).map(ViewItem::Node)),
        }
    }

    fn named_keys(&self, kb: &KnowledgeBase) -> Vec<Symbol> {
        match self {
            ViewItem::Term(t) => match kb.get_term(*t) {
                Term::Fn { named_args, .. } => named_args.iter().map(|(s, _)| *s).collect(),
                _ => Vec::new(),
            },
            ViewItem::Value(v) => (*v).named_keys(kb),
            ViewItem::Node(occ) => occ_named_keys(occ, kb),
        }
    }

    fn as_bind_value(&self) -> BindValue {
        match self {
            ViewItem::Term(t) => BindValue::Term(*t),
            ViewItem::Value(v) => BindValue::Value((*v).clone()),
            ViewItem::Node(occ) => BindValue::Value(Value::Node(Rc::clone(occ))),
        }
    }

    fn index_var(&self, kb: &KnowledgeBase) -> Option<Var> {
        match self {
            ViewItem::Term(t) => match kb.get_term(*t) {
                Term::Var(v) => Some(*v),
                _ => None,
            },
            ViewItem::Value(v) => (*v).index_var(kb),
            // See `Value::index_var`: Node heads surface only `Global`; a
            // Rigid / DeBruijn occurrence head reads `Opaque` and so fails
            // loudly at insert until Phase C surfaces it as a var-edge
            // (Phase A review guard #2).
            ViewItem::Node(_) => match self.head(kb) {
                ViewHead::Var(vid) => Some(Var::Global(vid)),
                _ => None,
            },
        }
    }
}

// ── Reflect lens over an occurrence (WI-297) ────────────────────
//
// The plain `Rc<NodeOccurrence>` view (above) reads an occurrence in its
// *goal* shape — `Expr::Const(42)` → the literal `42`, `Expr::Apply{foo}` →
// `foo(...)`. The typing relation, however, matches expression structure as
// *reflect data*: `int_lit(value: ?)`, `apply(fn: ?f, args: ?Args)`, … . The
// `occurrence_term` builtin bridges the two by *showing* the same occurrence
// through this reflect lens — no hash-consed term is built and no subtree is
// copied: a leaf's payload child is the occurrence itself (read in its plain
// shape), compound children are the existing child occurrences, and only the
// head label is supplied by the lens.

/// Reflect-`Expr` constructor symbols the [`ReflectedExpr`] lens reports as
/// functors, resolved once from the KB. `None` when reflect isn't loaded (the
/// lens then reads `Opaque`, so nothing matches — fail-soft, not a panic).
#[derive(Clone, Copy, Default, Debug)]
pub struct ReflectSyms {
    pub int_lit: Option<Symbol>,
    pub bigint_lit: Option<Symbol>,
    pub float_lit: Option<Symbol>,
    pub string_lit: Option<Symbol>,
    pub bool_lit: Option<Symbol>,
    /// Field key `value` (the single named arg of every `*_lit` entity).
    pub value: Option<Symbol>,
}

impl ReflectSyms {
    /// Resolve the reflect symbols the lens needs. Qualified entity names go
    /// through `try_resolve_symbol` (already interned by the stdlib load);
    /// the bare field key `value` is interned so it matches the key the
    /// loader stored on the rule pattern.
    pub fn resolve(kb: &mut KnowledgeBase) -> Self {
        Self {
            int_lit: kb.try_resolve_symbol("anthill.reflect.Expr.int_lit"),
            bigint_lit: kb.try_resolve_symbol("anthill.reflect.Expr.bigint_lit"),
            float_lit: kb.try_resolve_symbol("anthill.reflect.Expr.float_lit"),
            string_lit: kb.try_resolve_symbol("anthill.reflect.Expr.string_lit"),
            bool_lit: kb.try_resolve_symbol("anthill.reflect.Expr.bool_lit"),
            value: Some(kb.intern("value")),
        }
    }
}

/// Reflect-shape `TermView` over a `NodeOccurrence` (WI-297). See the module
/// note above. Currently covers literal leaves (`Expr::Const` →
/// `int_lit`/`float_lit`/`string_lit`/`bool_lit`/`bigint_lit(value: …)`);
/// other `Expr` forms read `Opaque` until their reflected reading is added.
pub struct ReflectedExpr {
    occ: Rc<NodeOccurrence>,
    syms: ReflectSyms,
}

impl ReflectedExpr {
    pub fn new(occ: Rc<NodeOccurrence>, syms: ReflectSyms) -> Self {
        Self { occ, syms }
    }

    /// The reflect functor for a literal payload (e.g. `Int` → `int_lit`).
    fn lit_functor(&self, lit: &Literal) -> Option<Symbol> {
        match lit {
            Literal::Int(_) => self.syms.int_lit,
            Literal::BigInt(_) => self.syms.bigint_lit,
            Literal::Float(_) => self.syms.float_lit,
            Literal::String(_) => self.syms.string_lit,
            Literal::Bool(_) => self.syms.bool_lit,
            // Opaque handle literals have no reflect `*_lit` form.
            Literal::Handle(_, _) => None,
        }
    }
}

impl TermView for ReflectedExpr {
    fn head(&self, _kb: &KnowledgeBase) -> ViewHead {
        match self.occ.as_expr() {
            // A literal reflects as `*_lit(value: <the literal>)` — one named
            // arg, no positionals.
            Some(Expr::Const(lit)) => match self.lit_functor(lit) {
                Some(f) => ViewHead::Functor { functor: Some(f), pos_arity: 0, named_arity: 1 },
                None => ViewHead::Opaque,
            },
            _ => ViewHead::Opaque,
        }
    }

    fn pos_arg<'a>(&'a self, _kb: &'a KnowledgeBase, _i: usize) -> Option<ViewItem<'a>> {
        // Reflect `Expr` entities use named fields only.
        None
    }

    fn named_arg<'a>(&'a self, _kb: &'a KnowledgeBase, sym: Symbol) -> Option<ViewItem<'a>> {
        match self.occ.as_expr() {
            // `value` is the occurrence itself, read in its plain `Const`
            // shape — no new term, no copy.
            Some(Expr::Const(_)) if Some(sym) == self.syms.value => {
                Some(ViewItem::Node(Rc::clone(&self.occ)))
            }
            _ => None,
        }
    }

    fn named_keys(&self, _kb: &KnowledgeBase) -> Vec<Symbol> {
        match self.occ.as_expr() {
            Some(Expr::Const(_)) => self.syms.value.into_iter().collect(),
            _ => Vec::new(),
        }
    }

    fn as_bind_value(&self) -> BindValue {
        // If the whole reflected term binds a var (`occurrence_term(?e, ?t)`),
        // bind the occurrence itself — identity preserved.
        BindValue::Value(Value::Node(Rc::clone(&self.occ)))
    }
}
