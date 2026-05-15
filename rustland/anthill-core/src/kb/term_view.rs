//! Unified view over `TermId`-backed and `Value`-backed terms.
//!
//! Per proposal 026.1 Q2. The resolver needs to unify a rule-head pattern
//! (always `TermId`) against a target that could be either KB-resident
//! (`TermId`) or an external-sourced runtime `Value`. `TermView` is the
//! read-only shape used on the target side of unification.
//!
//! This module defines the trait and implementations. Direct structural
//! unification via `match_view` lives in `kb::mod`.

use crate::eval::value::Value;
use crate::intern::Symbol;

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

/// A child of a [`TermView`] — either a `TermId` (borrowed from the KB's
/// hash-consed store) or a `Value` (borrowed from the owning
/// [`TermView`]). `'a` is the lifetime of the borrowed view.
#[derive(Clone, Copy, Debug)]
pub enum ViewItem<'a> {
    Term(TermId),
    Value(&'a Value),
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
}

impl TermView for Value {
    fn head(&self, _kb: &KnowledgeBase) -> ViewHead {
        match self {
            Value::Term(tid) => TermIdView(*tid).head(_kb),
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
            Value::Closure(_)
            | Value::Stream(_)
            | Value::Lazy(_)
            | Value::Substitution(_)
            | Value::Map(_)
            | Value::Cell(_)
            | Value::Requirement(_)
            | Value::Node(_) => ViewHead::Opaque,
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
            Value::Tuple { pos, .. } | Value::Entity { pos, .. } => {
                pos.get(i).map(ViewItem::Value)
            }
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
            Value::Tuple { named, .. } | Value::Entity { named, .. } => {
                named.iter().find(|(s, _)| *s == sym).map(|(_, v)| ViewItem::Value(v))
            }
            _ => None,
        }
    }

    fn named_keys(&self, kb: &KnowledgeBase) -> Vec<Symbol> {
        match self {
            Value::Term(tid) => match kb.get_term(*tid) {
                Term::Fn { named_args, .. } => named_args.iter().map(|(s, _)| *s).collect(),
                _ => Vec::new(),
            },
            Value::Tuple { named, .. } | Value::Entity { named, .. } => {
                named.iter().map(|(s, _)| *s).collect()
            }
            _ => Vec::new(),
        }
    }

    fn as_bind_value(&self) -> BindValue {
        match self {
            Value::Term(tid) => BindValue::Term(*tid),
            other => BindValue::Value(other.clone()),
        }
    }
}

impl TermView for ViewItem<'_> {
    fn head(&self, kb: &KnowledgeBase) -> ViewHead {
        match self {
            ViewItem::Term(t) => TermIdView(*t).head(kb),
            ViewItem::Value(v) => (**v).head(kb),
        }
    }

    fn pos_arg<'a>(&'a self, kb: &'a KnowledgeBase, i: usize) -> Option<ViewItem<'a>> {
        match self {
            ViewItem::Term(t) => match kb.get_term(*t) {
                Term::Fn { pos_args, .. } => pos_args.get(i).copied().map(ViewItem::Term),
                _ => None,
            },
            ViewItem::Value(v) => (*v).pos_arg(kb, i),
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
        }
    }

    fn named_keys(&self, kb: &KnowledgeBase) -> Vec<Symbol> {
        match self {
            ViewItem::Term(t) => match kb.get_term(*t) {
                Term::Fn { named_args, .. } => named_args.iter().map(|(s, _)| *s).collect(),
                _ => Vec::new(),
            },
            ViewItem::Value(v) => (*v).named_keys(kb),
        }
    }

    fn as_bind_value(&self) -> BindValue {
        match self {
            ViewItem::Term(t) => BindValue::Term(*t),
            ViewItem::Value(v) => BindValue::Value((*v).clone()),
        }
    }
}
