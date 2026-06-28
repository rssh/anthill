/// NodeOccurrence — KB-side positional wrapper for source content.
///
/// Per `docs/design/occurrence-as-value-type.md`. Replaces the arena+ID
/// the legacy occurrence side-table model: every child slot in an `Expr` is a
/// `Rc<NodeOccurrence>`, alternating `NodeOccurrence ⇄ NodeKind ⇄ Expr ⇄ NodeOccurrence`
/// all the way down. The tree is `Rc`-linked from the start so reflection
/// bindings are cheap (`Rc::clone`), eval can stash on its frame stack
/// without lifetime threading, and cross-pass identity is `Rc::ptr_eq`.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use crate::intern::Symbol;
use crate::span::SourceSpan;

pub use super::occurrence::PassId;
use super::subst::Substitution;
use super::term::{Literal, Term, TermId, Var, VarId};
use super::typing::{get_named_arg, list_to_vec, unwrap_option};
use super::{KbId, KnowledgeBase};
use crate::eval::value::Value;

// ── Origin ──────────────────────────────────────────────────────

/// Provenance of an `Expr`-kind occurrence — `Source` for user-written,
/// `Synthesized { from, by }` for those produced by a later pass with a
/// back-pointer (Rc, not ID) to the originating source occurrence and the
/// pass that synthesized it.
#[derive(Clone, Debug)]
pub enum OccurrenceOrigin {
    Source,
    Synthesized {
        from: Rc<NodeOccurrence>,
        by: PassId,
    },
}

// ── NodeOccurrence ──────────────────────────────────────────────

/// Positional wrapper. Carries span + owner around content; the inner
/// `NodeKind` discriminates what kind of content (expression, rule head,
/// future kinds).
#[derive(Debug)]
pub struct NodeOccurrence {
    pub kind: NodeKind,
    pub span: SourceSpan,
    /// Symbol of the enclosing declaration (operation, rule label, ...).
    /// `None` for top-level / unknown context.
    pub owner: Option<Symbol>,
    /// WI-471: lazily-materialized, memoized intrinsic term form of this
    /// occurrence — `(KbId, TermId)`, the `KbId` tagging which store the
    /// `TermId` belongs to. Set once by [`cached_term`]; σ-independent (reads
    /// only the immutable structural spine, never the typer's `RefCell`
    /// annotations), so never invalidated. The cache owns the `+1` `alloc`
    /// returns and never releases it (pin-for-lifetime; `Drop` cannot reach the
    /// store), so it is excluded from the structural `Drop` walk — nothing to
    /// drain. Reclamation (deferred-release queue keyed by the `KbId`) is WI-472.
    pub(crate) term_cache: Cell<Option<(KbId, TermId)>>,
}

/// Iterative `Drop` for `NodeOccurrence`. The default Drop walks
/// every child `Rc<NodeOccurrence>` recursively, which costs one
/// host stack frame per source nesting level — fine for shallow
/// expressions but blows the default 2 MiB debug-build stack on the
/// 624-line typing_pass_spec.anthill (deeply nested let / match /
/// lambda chains). This implementation drains the entire subtree into
/// an explicit work stack: each iteration pops an `Rc`, tries to
/// unwrap it, and steals the unwrapped node's children before the
/// node drops naturally. Because we steal first, the natural Drop on
/// the unwrapped node finds an emptied `kind` and adds no further
/// frames; total host stack stays bounded at ~2 frames regardless of
/// source nesting.
impl Drop for NodeOccurrence {
    fn drop(&mut self) {
        let mut stack: Vec<Rc<NodeOccurrence>> = Vec::new();
        drain_node(self, &mut stack);
        while let Some(rc) = stack.pop() {
            if let Ok(mut inner) = Rc::try_unwrap(rc) {
                drain_node(&mut inner, &mut stack);
                // inner drops here; its kind has been emptied so the
                // recursive call into this Drop finds nothing to drain.
            }
            // Otherwise the Rc is shared — decrementing it leaves the
            // inner alive, no recursion to bound.
        }
    }
}

/// Extract every direct `Rc<NodeOccurrence>` child of `occ` into the
/// caller's work stack, replacing each slot with an empty
/// `Vec`/placeholder so the natural Drop of `occ` finds nothing to
/// recurse through.
fn drain_node(occ: &mut NodeOccurrence, stack: &mut Vec<Rc<NodeOccurrence>>) {
    match &mut occ.kind {
        NodeKind::Expr { expr, origin, .. } => {
            if let OccurrenceOrigin::Synthesized { from, .. } = origin {
                let placeholder = NodeOccurrence::new_expr(Expr::Bottom, empty_span(), None);
                stack.push(std::mem::replace(from, placeholder));
            }
            drain_expr_children(expr, stack);
        }
        NodeKind::Pattern(pat) => drain_pattern_children(pat, stack),
        NodeKind::Type(tn) => drain_type_node(tn, stack),
        NodeKind::EffectExpr(en) => drain_effect_expr_node(en, stack),
        NodeKind::RuleHead { .. } => {}
    }
}

/// WI-342: steal the one `Rc<NodeOccurrence>` a poisoned [`TypeChild`] holds
/// onto the work stack, leaving a trivially-dropped placeholder behind — so
/// the iterative `Drop` bounds host-stack depth over a `Type`/`EffectExpr`
/// spine just as it does over `Expr`/`Pattern`. A ground child holds only a
/// `TermId` (no `Rc`, nothing to drain).
fn drain_type_child(child: &mut TypeChild, stack: &mut Vec<Rc<NodeOccurrence>>) {
    if let TypeChild::Node(rc) = child {
        let placeholder = NodeOccurrence::new_expr(Expr::Bottom, empty_span(), None);
        stack.push(std::mem::replace(rc, placeholder));
    }
}

/// WI-342: drain every `Rc<NodeOccurrence>` child of a [`TypeNode`] — the
/// `denoted` value occurrence and each poisoned `TypeChild` — mirroring
/// [`drain_expr_children`] for the `Type` carrier.
fn drain_type_node(tn: &mut TypeNode, stack: &mut Vec<Rc<NodeOccurrence>>) {
    match tn {
        TypeNode::Denoted { value } => {
            let placeholder = NodeOccurrence::new_expr(Expr::Bottom, empty_span(), None);
            stack.push(std::mem::replace(value, placeholder));
        }
        TypeNode::Parameterized { base, bindings } => {
            drain_type_child(base, stack);
            for (_, c) in bindings.iter_mut() {
                drain_type_child(c, stack);
            }
        }
        TypeNode::EffectsRows { effects_expr } => drain_type_child(effects_expr, stack),
        TypeNode::Arrow { param, result, effects } => {
            drain_type_child(param, stack);
            drain_type_child(result, stack);
            drain_type_child(effects, stack);
        }
        TypeNode::ExprCarried { value, member } => {
            drain_type_child(value, stack);
            drain_type_child(member, stack);
        }
        TypeNode::NamedTuple { .. } => {
            // WI-361: `fields` is a `Value`-carried `List[TypeField]`. Its poisoned
            // leaves are `Value::Node`s whose own `Drop` is already iterative, and
            // the `Value::Entity` cons spine is shallow (tuple arity) — so there is
            // nothing to hoist onto the work stack here.
        }
    }
}

/// WI-342: drain every poisoned-child `Rc<NodeOccurrence>` of an
/// [`EffectExprNode`].
fn drain_effect_expr_node(en: &mut EffectExprNode, stack: &mut Vec<Rc<NodeOccurrence>>) {
    match en {
        EffectExprNode::Merge { left, right } => {
            drain_type_child(left, stack);
            drain_type_child(right, stack);
        }
        EffectExprNode::Present { label } | EffectExprNode::Absent { label } => {
            drain_type_child(label, stack)
        }
        EffectExprNode::Guarded { label, guard: _ } => {
            drain_type_child(label, stack);
            // `guard` is a `Value`-carried `List[reflect.Term]`; its `Value::Node`
            // leaves Drop iteratively and the cons spine is shallow — nothing to
            // hoist onto the work stack (as `TypeNode::NamedTuple`'s `fields`).
        }
        EffectExprNode::Open { tail } => drain_type_child(tail, stack),
        EffectExprNode::EmptyRow => {}
    }
}

/// WI-318: mirror of `drain_expr_children` for `Pattern`. Steals each
/// `Rc<NodeOccurrence>` child slot (sub-patterns + the Var `type_ann`)
/// into the caller's work stack, replacing each with an emptied
/// container so the natural `Drop` on the unwrapped node finds nothing
/// to recurse through.
fn drain_pattern_children(pat: &mut Pattern, stack: &mut Vec<Rc<NodeOccurrence>>) {
    match pat {
        Pattern::Var { type_ann, .. } => {
            if let Some(t) = type_ann.take() {
                stack.push(t);
            }
        }
        Pattern::Wildcard | Pattern::Literal { .. } => {}
        Pattern::Constructor { pos_args, named_args, .. } => {
            for c in std::mem::take(pos_args) { stack.push(c); }
            for (_, c) in std::mem::take(named_args) { stack.push(c); }
        }
        Pattern::Tuple { positional, named } => {
            for c in std::mem::take(positional) { stack.push(c); }
            for (_, c) in std::mem::take(named) { stack.push(c); }
        }
    }
}

/// Steal every child `Rc<NodeOccurrence>` slot of `expr`, pushing the
/// owned Rcs onto `stack`. Vec-backed slots use `mem::take` (one
/// pointer swap per Vec, regardless of length); single-Rc slots use
/// `mem::replace` with a fresh `Expr::Bottom` placeholder. The
/// non-destructive [`for_each_child`] walker can't share this body
/// because routing it through a per-child callback would force one
/// slot replacement per Vec element instead of one per Vec — material
/// for the Drop hot path.
fn drain_expr_children(expr: &mut Expr, stack: &mut Vec<Rc<NodeOccurrence>>) {
    let mk_placeholder = || NodeOccurrence::new_expr(Expr::Bottom, empty_span(), None);
    match expr {
        Expr::Apply { pos_args, named_args, type_args, .. } => {
            for c in std::mem::take(pos_args) { stack.push(c); }
            for (_, c) in std::mem::take(named_args) { stack.push(c); }
            // WI-342 S4b: a denoted-bearing type-arg is a `Value::Node`
            // occurrence — drain it (symmetric with `Let.type_annotation`).
            for (_, v) in std::mem::take(type_args) {
                if let Value::Node(occ) = v { stack.push(occ); }
            }
        }
        Expr::Constructor { pos_args, named_args, .. }
        | Expr::Instantiation { pos_args, named_args, .. } => {
            for c in std::mem::take(pos_args) { stack.push(c); }
            for (_, c) in std::mem::take(named_args) { stack.push(c); }
        }
        Expr::If { condition, then_branch, else_branch } => {
            stack.push(std::mem::replace(condition, mk_placeholder()));
            stack.push(std::mem::replace(then_branch, mk_placeholder()));
            stack.push(std::mem::replace(else_branch, mk_placeholder()));
        }
        Expr::Let { pattern, type_annotation, value, body } => {
            stack.push(std::mem::replace(pattern, mk_placeholder()));
            stack.push(std::mem::replace(value, mk_placeholder()));
            stack.push(std::mem::replace(body, mk_placeholder()));
            // WI-342: a denoted-bearing annotation is a `Value::Node` occurrence
            // — drain it onto the stack so a deeply nested type can't overflow the
            // iterative Drop this fn exists to prevent.
            if let Some(Value::Node(occ)) = type_annotation.take() {
                stack.push(occ);
            }
        }
        Expr::Match { scrutinee, branches } => {
            stack.push(std::mem::replace(scrutinee, mk_placeholder()));
            for mut b in std::mem::take(branches) {
                stack.push(std::mem::replace(&mut b.pattern, mk_placeholder()));
                stack.push(std::mem::replace(&mut b.body, mk_placeholder()));
                if let Some(g) = b.guard.take() {
                    stack.push(g);
                }
            }
        }
        Expr::Lambda { param, body } => {
            stack.push(std::mem::replace(param, mk_placeholder()));
            stack.push(std::mem::replace(body, mk_placeholder()));
        }
        Expr::Proof { conclude, body, .. } => {
            if let Some(c) = conclude.take() { stack.push(c); }
            stack.push(std::mem::replace(body, mk_placeholder()));
        }
        Expr::LambdaWithin { param, body, requirements } => {
            stack.push(std::mem::replace(param, mk_placeholder()));
            stack.push(std::mem::replace(body, mk_placeholder()));
            for r in std::mem::take(requirements) { stack.push(r); }
        }
        Expr::ListLit(es) | Expr::SetLit(es) => {
            for e in std::mem::take(es) { stack.push(e); }
        }
        Expr::TupleLit { positional, named } => {
            for e in std::mem::take(positional) { stack.push(e); }
            for (_, e) in std::mem::take(named) { stack.push(e); }
        }
        Expr::HoApply { predicate, args } => {
            stack.push(std::mem::replace(predicate, mk_placeholder()));
            for a in std::mem::take(args) { stack.push(a); }
        }
        Expr::DotApply { receiver, pos_args, named_args, .. } => {
            stack.push(std::mem::replace(receiver, mk_placeholder()));
            for c in std::mem::take(pos_args) { stack.push(c); }
            for (_, c) in std::mem::take(named_args) { stack.push(c); }
        }
        Expr::ApplyWithin { args, named_args, requirements, type_args, .. } => {
            for a in std::mem::take(args) { stack.push(a); }
            for (_, a) in std::mem::take(named_args) { stack.push(a); }
            for r in std::mem::take(requirements) { stack.push(r); }
            // WI-342 S4b: drain any denoted-bearing (`Value::Node`) type-arg.
            for (_, v) in std::mem::take(type_args) {
                if let Value::Node(occ) = v { stack.push(occ); }
            }
        }
        Expr::HoApplyWithin { predicate, args, requirements } => {
            stack.push(std::mem::replace(predicate, mk_placeholder()));
            for a in std::mem::take(args) { stack.push(a); }
            for r in std::mem::take(requirements) { stack.push(r); }
        }
        Expr::ConstructorWithin { pos_args, named_args, requirements, .. } => {
            for c in std::mem::take(pos_args) { stack.push(c); }
            for (_, c) in std::mem::take(named_args) { stack.push(c); }
            for r in std::mem::take(requirements) { stack.push(r); }
        }
        Expr::RequirementAtSort { chain, .. } => {
            stack.push(std::mem::replace(chain, mk_placeholder()));
        }
        Expr::ConstructRequirement { requirements, .. } => {
            for r in std::mem::take(requirements) { stack.push(r); }
        }
        Expr::Const(_) | Expr::Ref(_) | Expr::Ident(_)
        | Expr::Var(_) | Expr::Bottom | Expr::VarRef { .. } => {}
    }
}

impl NodeOccurrence {
    /// Build a source-origin expression occurrence.
    pub fn new_expr(expr: Expr, span: SourceSpan, owner: Option<Symbol>) -> Rc<Self> {
        Rc::new(NodeOccurrence {
            kind: NodeKind::Expr {
                expr,
                origin: OccurrenceOrigin::Source,
                classification: RefCell::new(None),
                resolved_type_args: RefCell::new(Vec::new()),
                inferred_type: RefCell::new(None),
            },
            span,
            owner,
            term_cache: Cell::new(None),
        })
    }

    /// WI-502 Step 3 — rebuild THIS `Expr` occurrence with a new `expr`,
    /// PRESERVING the typer-stamped `inferred_type` (and the `Synthesized`
    /// provenance origin). Every occurrence-rebuild path — De Bruijn open/close,
    /// substitution, simp reassembly — must use this instead of a bare
    /// `new_expr`/`synthesized_expr`, which hard-reset `inferred_type` to `None`:
    /// the "original WI-502 bug" that dropped the stamped type the instant a
    /// body was opened/renamed during resolution, so the occurrence sort-head read
    /// over the opened body read `None`.
    ///
    /// The carry is VERBATIM (σ is NOT applied to the type). That is sound for the
    /// occurrence sort-head read (`sort_functor_of_view` over `inferred_type`, e.g.
    /// the typer's `[simp]` firing guard), which returns the type's SORT HEAD —
    /// invariant under the type-parameter refinement a child substitution performs
    /// (`cons(?h,?t): List[?T]` keeps head `List`). A node whose head is itself a
    /// type-var widens to `None`, never a stale concrete sort — so there is no
    /// silent drift (the M6 refresh-boundary guarantee holds by head-only reads,
    /// not by re-deriving the type, which is the deferred compute-once entry).
    /// On a non-`Expr` self (no `inferred_type` slot) the carry is a no-op.
    pub fn rebuilt_expr(&self, expr: Expr) -> Rc<Self> {
        let rebuilt = match &self.kind {
            NodeKind::Expr { origin: OccurrenceOrigin::Synthesized { from, by }, .. } => {
                NodeOccurrence::synthesized_expr(expr, Rc::clone(from), *by, self.owner)
            }
            _ => NodeOccurrence::new_expr(expr, self.span, self.owner),
        };
        if let Some(ty) = self.inferred_type() {
            rebuilt.set_inferred_type(ty);
        }
        rebuilt
    }

    /// Build a synthesized expression occurrence — span inherited from
    /// the originating source occurrence `from`.
    pub fn synthesized_expr(
        expr: Expr,
        from: Rc<NodeOccurrence>,
        by: PassId,
        owner: Option<Symbol>,
    ) -> Rc<Self> {
        let span = from.span;
        Rc::new(NodeOccurrence {
            kind: NodeKind::Expr {
                expr,
                origin: OccurrenceOrigin::Synthesized { from, by },
                classification: RefCell::new(None),
                resolved_type_args: RefCell::new(Vec::new()),
                inferred_type: RefCell::new(None),
            },
            span,
            owner,
            term_cache: Cell::new(None),
        })
    }

    /// Build a rule-head occurrence.
    pub fn new_rule_head(
        functor: Symbol,
        pos_args: Vec<TermId>,
        named_args: Vec<(Symbol, TermId)>,
        span: SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<Self> {
        Rc::new(NodeOccurrence {
            kind: NodeKind::RuleHead {
                functor,
                pos_args,
                named_args,
            },
            span,
            owner,
            term_cache: Cell::new(None),
        })
    }

    /// Build a pattern occurrence (WI-318).
    pub fn new_pattern(pattern: Pattern, span: SourceSpan, owner: Option<Symbol>) -> Rc<Self> {
        Rc::new(NodeOccurrence {
            kind: NodeKind::Pattern(pattern),
            span,
            owner,
            term_cache: Cell::new(None),
        })
    }

    /// Build a Type occurrence (WI-342) — the `Value`-carried form of a
    /// `denoted`-containing `Type` entity.
    pub fn new_type(ty: TypeNode, span: SourceSpan, owner: Option<Symbol>) -> Rc<Self> {
        Rc::new(NodeOccurrence {
            kind: NodeKind::Type(ty),
            span,
            owner,
            term_cache: Cell::new(None),
        })
    }

    /// Build an EffectExpression occurrence (WI-342).
    pub fn new_effect_expr(
        expr: EffectExprNode,
        span: SourceSpan,
        owner: Option<Symbol>,
    ) -> Rc<Self> {
        Rc::new(NodeOccurrence {
            kind: NodeKind::EffectExpr(expr),
            span,
            owner,
            term_cache: Cell::new(None),
        })
    }

    /// If this occurrence wraps an expression, return it.
    pub fn as_expr(&self) -> Option<&Expr> {
        match &self.kind {
            NodeKind::Expr { expr, .. } => Some(expr),
            _ => None,
        }
    }

    /// If this occurrence wraps a pattern (WI-318), return it.
    pub fn as_pattern(&self) -> Option<&Pattern> {
        match &self.kind {
            NodeKind::Pattern(pat) => Some(pat),
            _ => None,
        }
    }

    /// If this occurrence wraps a Type (WI-342), return it.
    pub fn as_type(&self) -> Option<&TypeNode> {
        match &self.kind {
            NodeKind::Type(ty) => Some(ty),
            _ => None,
        }
    }

    /// If this occurrence wraps an EffectExpression (WI-342), return it.
    pub fn as_effect_expr(&self) -> Option<&EffectExprNode> {
        match &self.kind {
            NodeKind::EffectExpr(e) => Some(e),
            _ => None,
        }
    }

    /// Record the typer's `CallClass` for this occurrence. Only `Expr`-kind
    /// occurrences carry typer metadata; rule heads ignore the call.
    pub fn set_classification(&self, class: super::typing::CallClass) {
        if let NodeKind::Expr { classification, .. } = &self.kind {
            *classification.borrow_mut() = Some(Box::new(class));
        }
    }

    /// Record the typer-resolved operation type arguments for an
    /// apply call site (WI-272). `args` is positional in the callee's
    /// `[T1, T2, ...]` declaration order; each entry is the
    /// `(declared-name, resolved-type-term)`. No-op on non-Expr kinds.
    pub fn set_resolved_type_args(&self, args: Vec<(Symbol, TermId)>) {
        if let NodeKind::Expr { resolved_type_args, .. } = &self.kind {
            *resolved_type_args.borrow_mut() = args;
        }
    }

    /// Run `f` with a borrowed slice of the typer-resolved op type
    /// arguments populated by `set_resolved_type_args` (WI-272). The
    /// slice is empty when the callee has no type params, or when the
    /// typer hasn't run yet for this occurrence (e.g. a hand-built
    /// test fixture). RefCell-borrowed callback avoids cloning the
    /// underlying Vec on the hot apply path.
    pub fn with_resolved_type_args<R>(
        &self,
        f: impl FnOnce(&[(Symbol, TermId)]) -> R,
    ) -> R {
        match &self.kind {
            NodeKind::Expr { resolved_type_args, .. } => f(&resolved_type_args.borrow()),
            _ => f(&[]),
        }
    }

    /// Record the typer's inferred type for this occurrence (WI-284).
    /// Only `Expr`-kind occurrences carry typer metadata; rule heads
    /// ignore the call. Idempotent under re-typing — the last (most
    /// refined, e.g. expected-hint-constrained) type wins. WI-342: the
    /// inferred type is carrier-agnostic (`Value`) — a denoted-bearing type
    /// (a lambda arrow carrying `Modify[c]`) is stored as `Value::Node`
    /// rather than re-grounded; the sort-head read (`sort_functor_of_view` over
    /// this) widens it via [`TermView`].
    pub fn set_inferred_type(&self, ty: Value) {
        if let NodeKind::Expr { inferred_type, .. } = &self.kind {
            *inferred_type.borrow_mut() = Some(ty);
        }
    }

    /// The typer's inferred type for this occurrence, if typed (WI-284).
    /// `None` for rule heads, not-yet-typed occurrences, or ill-typed
    /// nodes. The basis for the occurrence's sort-head read
    /// (`sort_functor_of_view` over this).
    pub fn inferred_type(&self) -> Option<Value> {
        match &self.kind {
            NodeKind::Expr { inferred_type, .. } => inferred_type.borrow().clone(),
            _ => None,
        }
    }
}

// ── NodeKind ────────────────────────────────────────────────────

/// What kind of content this occurrence holds. The wrapper (span, owner)
/// is uniform; the kind discriminates the structural payload.
#[derive(Debug)]
pub enum NodeKind {
    /// Expression content — operation/lambda bodies, conditional branches,
    /// match arms, let values/bodies, etc.
    Expr {
        expr: Expr,
        origin: OccurrenceOrigin,
        /// Typer-attached classification (WI-231). Mutable because the
        /// typer writes after construction while other walkers may hold
        /// shared `Rc` references to this occurrence.
        classification: RefCell<Option<Box<super::typing::CallClass>>>,
        /// Typer-resolved operation type arguments for an
        /// `Expr::Apply` / `Expr::ApplyWithin` call site (WI-272),
        /// positionally in declaration order against the callee's
        /// declared `[T1, T2, ...]` parameters. Each entry is
        /// `(declared-param-name, resolved-type-term)`. Empty when the
        /// callee has no type params or this isn't an apply
        /// occurrence. Populated after the typer has unified the call's
        /// type-arg bindings with arg / expected types; the eval reads
        /// it on call entry and installs the values on
        /// `Frame.type_args`. See `docs/design/operation-call-model.md`
        /// §"Operation type arguments".
        resolved_type_args: RefCell<Vec<(Symbol, TermId)>>,
        /// Typer-attached inferred type for this occurrence (WI-284):
        /// the `TypeResult.ty` the typer computes but historically
        /// discarded. Kept here — a third per-node annotation alongside
        /// `classification` / `resolved_type_args` — so the type-directed
        /// `[simp]` engine can read each occurrence's least declared sort
        /// (`sort_functor_of_view` over `inferred_type`) without recomputing. Written
        /// by the typer's `Stamp` work-frame once a node's `TypeResult`
        /// is finalized; `None` until typed, or when the node is ill-typed.
        inferred_type: RefCell<Option<Value>>,
    },
    /// Rule head — positional wrapper around a Term-shaped head pattern.
    /// Args are `TermId` (KB-position content); the wrap exists for span
    /// + owner metadata only.
    RuleHead {
        functor: Symbol,
        pos_args: Vec<TermId>,
        named_args: Vec<(Symbol, TermId)>,
    },
    /// Pattern content — a match-time matcher (var binding, wildcard,
    /// literal, constructor destructure, tuple destructure). Patterns
    /// are not expressions: they have their own grammar (per `_pattern`
    /// in tree-sitter grammar.js — `pattern_var` / `pattern_wildcard` /
    /// `pattern_literal` / `pattern_constructor` / `pattern_tuple`) and
    /// are consumed by `eval/pattern.rs::match_pattern`, not the
    /// evaluator. WI-318: lifted from a TermId field on Lambda/Let/
    /// MatchBranch into a sibling NodeKind so the De Bruijn opener/
    /// closer + simp walkers handle pattern children uniformly via
    /// `for_each_pattern_child` + `reassemble_pattern`, dropping the
    /// per-pattern-field special-case arms that existed in the
    /// term-stored era.
    Pattern(Pattern),
    /// Type content (WI-342). The `Value`-carried form of a `Type` entity
    /// whose subtree transitively contains a `denoted` (so it cannot be a
    /// hash-consed `Term` — the carrier rule, see
    /// `docs/design/entity-representation-term-or-value.md` §2). Mirrors the
    /// `Type` sort (`stdlib/anthill/prelude/sort.anthill`). Sibling NodeKind
    /// per the WI-318 `Pattern` precedent: a distinct stdlib sort gets a
    /// distinct NodeKind. The poisoned spine is `Rc<NodeOccurrence>`-linked
    /// (uniform with `Expr`/`Pattern`, so `TermView` / `Drop` / occurrence
    /// substitution read it through the existing machinery); ground subtrees
    /// stay hash-consed `TermId` (carried in `TypeChild::Ground`).
    Type(TypeNode),
    /// EffectExpression content (WI-342). The sibling carrier for the
    /// `EffectExpression` sort, reached because a `denoted`-bearing effect
    /// label (`{-Modify[c]}`) poisons its containing row upward — the row is
    /// itself `Value`-carried (design doc §2). Kept a distinct NodeKind from
    /// `Type` because `EffectExpression` is a distinct sort.
    EffectExpr(EffectExprNode),
}

// ── Expr ────────────────────────────────────────────────────────

/// Structural expression IR. Every child slot is itself a
/// `Rc<NodeOccurrence>`; patterns stay as `TermId` (pattern reform is a
/// separate concern). Tagged-union over the apply / match / if / let /
/// lambda / instantiation / literal / requirement-rewrite forms.
#[derive(Debug)]
pub enum Expr {
    /// Direct function application — `apply(fn = f, args = [a, b])`.
    Apply {
        functor: Symbol,
        pos_args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
        /// Call-site operation type arguments (`op[T = Int](args)`).
        /// Each entry: `(Some(name), type)` for `T = Int`, or
        /// `(None, type)` for positional `Int`. Empty for untyped calls.
        /// WI-342 S4b: a carrier-agnostic `Value` — a value-in-type type-arg
        /// (the `3` in `g[3](x)`) rides as `Value::Node` once `make_denoted`
        /// is retired; a ground type-arg is `Value::Term`. Treated by the
        /// DeBruijn/σ walkers via the carrier-agnostic `*_value_type` helpers
        /// (a `Value::Node` type carries no vars, so it passes through).
        type_args: Vec<(Option<Symbol>, Value)>,
    },
    /// Higher-order application — `predicate(args...)` where predicate is
    /// an expression rather than a known operation symbol.
    HoApply {
        predicate: Rc<NodeOccurrence>,
        args: Vec<Rc<NodeOccurrence>>,
    },
    /// Entity construction — `MyEntity(field: value)`.
    Constructor {
        name: Symbol,
        pos_args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
    },
    /// `match` expression with branches.
    Match {
        scrutinee: Rc<NodeOccurrence>,
        branches: Vec<MatchBranch>,
    },
    /// `if cond then ... else ...` expression.
    If {
        condition: Rc<NodeOccurrence>,
        then_branch: Rc<NodeOccurrence>,
        else_branch: Rc<NodeOccurrence>,
    },
    /// `let pat = value in body`. WI-318: `pattern` is a Pattern-kind
    /// occurrence (typically `Pattern::Var { name, type_ann: None }`).
    /// `type_annotation` is the OUTER `: T` annotation from WI-185
    /// (`let p: T = …`). WI-342 S4a: a carrier-agnostic `Value` — a non-trivial
    /// (denoted-bearing) annotation rides as `Value::Node`. A `Value::Node` type
    /// carries only Ref/literal denoteds (no DeBruijn/Global vars), so the
    /// DeBruijn open/close + σ walkers treat it as opaque (see `*_value_type`).
    Let {
        pattern: Rc<NodeOccurrence>,
        type_annotation: Option<Value>,
        value: Rc<NodeOccurrence>,
        body: Rc<NodeOccurrence>,
    },
    /// Lambda — `(param) => body`. WI-318: `param` is a Pattern-kind
    /// occurrence (typically `Pattern::Var { name, type_ann: None }`
    /// for `lambda x -> ...` or `Pattern::Tuple` for
    /// `lambda (a, b) -> ...`).
    Lambda {
        param: Rc<NodeOccurrence>,
        body: Rc<NodeOccurrence>,
    },
    /// In-body / control-flow proof (proposal 025 §"In-body and
    /// control-flow proofs", WI-538) — `proof <target> [by <strategy>]
    /// [conclude <P>] end <body>`. The Tier-2 fallback for guarded-effect
    /// discharge: the typer proves the goal (the `conclude` occurrence if
    /// present, else the `target` rule's head) from the local Γ
    /// (`prove_from_gamma`), and on success `assume`s it into Γ for
    /// `body` — the proof-as-producer modification rule (proposal 050).
    Proof {
        /// Proof name: a rule reference (no `conclude`) or a citation
        /// handle (with `conclude`). Resolved at load (see
        /// `Expr::Proof` lowering).
        target: Symbol,
        /// `by <strategy>` tactic name (`derivation` ⇒ Tier-A inline;
        /// any other ⇒ Tier-B external). `None` ⇒ open obligation
        /// (contributes nothing to Γ).
        strategy: Option<Symbol>,
        /// `using` cited lemmas (resolved), for lexical-scope citation.
        using: Vec<Symbol>,
        /// The inline goal `conclude <P>`; `None` ⇒ goal is the `target`
        /// rule's head.
        conclude: Option<Rc<NodeOccurrence>>,
        /// The continuation expression after the proof.
        body: Rc<NodeOccurrence>,
    },
    /// Generic instantiation — `Name { bindings }`.
    Instantiation {
        name: Symbol,
        pos_args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
    },
    /// Method-call (dot) syntax — `receiver.name(args)` or `receiver.name`
    /// (WI-278). A pre-dispatch form emitted by the converter for
    /// value-receiver dot forms: the operation isn't resolved yet, only the
    /// textual member `name` and the receiver expression are known. The
    /// typer dispatches it (WI-279, proposal 043 §6) — once the receiver's
    /// least sort is known — by synthesizing an `Apply(op, [receiver, …args])`
    /// when `name` resolves to an operation declared on that sort, then
    /// re-typing that apply. No match ⇒ a `DotDispatchNoMatch` error at the
    /// dot's source span. `name`-less field access has empty arg lists; a
    /// method call carries its positional / named args.
    DotApply {
        receiver: Rc<NodeOccurrence>,
        name: Symbol,
        pos_args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
    },
    /// List literal `[a, b, c]`.
    ListLit(Vec<Rc<NodeOccurrence>>),
    /// Set literal `{a, b, c}`.
    SetLit(Vec<Rc<NodeOccurrence>>),
    /// Tuple literal `(a, b, key: c)`.
    TupleLit {
        positional: Vec<Rc<NodeOccurrence>>,
        named: Vec<(Symbol, Rc<NodeOccurrence>)>,
    },

    // ── Post-elaboration forms (req_insertion / typer rewrites) ─────

    /// `apply_within` — function application with a requirements channel.
    ApplyWithin {
        functor: Symbol,
        args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
        requirements: Vec<Rc<NodeOccurrence>>,
        /// Call-site operation type arguments (`op[T = Int](args)`),
        /// mirroring `Expr::Apply.type_args` (WI-272). Each entry is
        /// `(Some(name), type)` for `T = Int`, or `(None, type)` for
        /// positional `Int`. Empty when the call site doesn't bind any
        /// (the typer-resolved values for inferred slots live in
        /// `NodeKind::Expr.resolved_type_args`).
        /// WI-342 S4b: carrier-agnostic `Value`, mirroring `Apply.type_args`.
        type_args: Vec<(Option<Symbol>, Value)>,
    },
    /// Higher-order `apply_within`.
    HoApplyWithin {
        predicate: Rc<NodeOccurrence>,
        args: Vec<Rc<NodeOccurrence>>,
        requirements: Vec<Rc<NodeOccurrence>>,
    },
    /// Constructor with a requirements channel.
    ConstructorWithin {
        name: Symbol,
        pos_args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
        requirements: Vec<Rc<NodeOccurrence>>,
    },
    /// Lambda carrying captured requirements. WI-318: `param` is a
    /// Pattern-kind occurrence (see `Lambda.param`).
    LambdaWithin {
        param: Rc<NodeOccurrence>,
        body: Rc<NodeOccurrence>,
        requirements: Vec<Rc<NodeOccurrence>>,
    },
    /// `requirement_at_sort(chain, slot)` projection.
    RequirementAtSort {
        chain: Rc<NodeOccurrence>,
        slot: i64,
    },
    /// `construct_requirement(impl_functor, [sub-requirements])`.
    ConstructRequirement {
        impl_functor: Symbol,
        requirements: Vec<Rc<NodeOccurrence>>,
    },
    /// `var_ref(name)` — a body reading a `__req_*` requirement param.
    VarRef {
        name: Symbol,
    },

    // ── Leaves ──────────────────────────────────────────────────────
    Var(Var),
    Const(Literal),
    Ref(Symbol),
    Ident(Symbol),
    Bottom,
}

#[derive(Debug)]
pub struct MatchBranch {
    /// WI-318: pattern is now a Pattern-kind occurrence (or
    /// `Expr::Var`-kind for reflection meta-vars). Walked structurally
    /// by `for_each_child` via the `Match` arm.
    pub pattern: Rc<NodeOccurrence>,
    pub guard: Option<Rc<NodeOccurrence>>,
    pub body: Rc<NodeOccurrence>,
    pub span: SourceSpan,
}

// ── Pattern ─────────────────────────────────────────────────────

/// Structural pattern IR (WI-318). One-to-one with the surface
/// `_pattern` non-terminal in tree-sitter `grammar.js`
/// (`pattern_var` / `pattern_wildcard` / `pattern_literal` /
/// `pattern_constructor` / `pattern_tuple`). Each sub-pattern slot is
/// itself an `Rc<NodeOccurrence>` whose `.kind` is
/// `NodeKind::Pattern(...)` — so opener / closer / simp walkers handle
/// pattern children via the same `for_each_*_child` + reassemble
/// shape they use for `Expr`.
///
/// Patterns do NOT contain `Term::Var(DeBruijn)` in any production
/// path (the grammar's `pattern_var` is a bare identifier — see
/// `tree-sitter-anthill/grammar.js:975`); the binding name is a
/// `Symbol`, resolved as a frame-local at eval time, not as a rule
/// logical-var. The `type_ann` slot inside `Var` is an `Expr`-kind
/// occurrence (a TYPE expression — proposal 027.1 types-are-terms),
/// not a sub-pattern.
#[derive(Debug)]
pub enum Pattern {
    /// `pattern_var p` — bind the scrutinee to a frame-local named
    /// `name`. Optional `type_ann` carries the declared type for
    /// patterns that admit one (currently only via WI-185 `let p: T`
    /// at the outer Let.type_annotation; the Pattern's own `type_ann`
    /// is reserved for future grammar extensions).
    Var {
        name: Symbol,
        type_ann: Option<Rc<NodeOccurrence>>,
    },
    /// `_` — match anything, bind nothing.
    Wildcard,
    /// `42`, `"hi"`, `true`, etc. — match by literal value.
    Literal { value: Literal },
    /// `Cons(h, t)` — destructure an entity / tagged-term scrutinee.
    Constructor {
        name: Symbol,
        pos_args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
    },
    /// `(a, b)` / `(x: a, y: b)` — destructure a tuple scrutinee.
    Tuple {
        positional: Vec<Rc<NodeOccurrence>>,
        named: Vec<(Symbol, Rc<NodeOccurrence>)>,
    },
}

// ── TypeNode / EffectExprNode (WI-342) ──────────────────────────

/// A child slot of a [`TypeNode`] / [`EffectExprNode`] — either a **ground**
/// hash-consed subtree (no `denoted` beneath it, so it stays a `TermId`) or a
/// **poisoned** subtree on the `denoted` spine, carried as a sibling
/// `Rc<NodeOccurrence>` (a `NodeKind::Type` or `NodeKind::EffectExpr`). The
/// minimal-`Value`-spine principle: only the path from a container down to a
/// `denoted` is `Value`-carried; everything else stays interned.
///
/// `Rc<NodeOccurrence>` (not `Box<TypeNode>`) so a poisoned child is read
/// through `TermView::pos_arg`/`named_arg` as a `ViewItem::Node`, drained by
/// the iterative `Drop`, and spliced by `substitute_occurrence` — exactly the
/// machinery `Expr`/`Pattern` children already use.
#[derive(Clone, Debug)]
pub enum TypeChild {
    Ground(TermId),
    Node(Rc<NodeOccurrence>),
}

/// Structural `Type`-sort IR (WI-342). One arm per `Type` entity variant that
/// can sit on a `denoted` spine for the first migrated producer
/// (`{-Modify[c]}`). Variants the slice doesn't yet mint (`sort_ref`,
/// `type_var`, `nothing`, `named_tuple`) are not represented here — they are
/// always ground, so they ride in `TypeChild::Ground(TermId)`; arms are added
/// only when a producer carries one on a poisoned spine.
#[derive(Debug)]
pub enum TypeNode {
    /// `denoted(value: NodeOccurrence)` — the poison source. `value` is an
    /// `Expr`-kind occurrence (e.g. `Expr::Ref(c)`), identity-bearing and
    /// span-carrying, which is exactly why its containers cannot hash-cons.
    Denoted { value: Rc<NodeOccurrence> },
    /// `parameterized(base, bindings)` — `base` is usually a ground
    /// `sort_ref`; a binding's value is what carries the `denoted`.
    Parameterized {
        base: TypeChild,
        bindings: Vec<(Symbol, TypeChild)>,
    },
    /// `effects_rows(effects_expr: EffectExpression)` — the bridge from the
    /// `EffectExpression` sort into a `Type` slot; `effects_expr` wraps a
    /// `NodeKind::EffectExpr` child.
    EffectsRows { effects_expr: TypeChild },
    /// `arrow(param, result, effects)`.
    Arrow {
        param: TypeChild,
        result: TypeChild,
        effects: TypeChild,
    },
    /// `named_tuple(fields: List[TypeField])` — a tuple type whose fields are
    /// `TypeField(name, type)` records. WI-342: minted when a tuple literal has a
    /// field whose type is `denoted`-bearing (a `Value::Node`, e.g. a tuple element
    /// that is a lambda carrying `Modify[c]`). WI-361: `fields` is a `Value`-carried
    /// `List[TypeField]` mirroring the hash-consed term form `make_named_tuple_type`
    /// builds — a ground field type rides as `Value::Term`, a poisoned one as
    /// `Value::Node` — so `TermView` reads this carrier and its term twin
    /// identically (one `fields` child; no special-cased reader).
    NamedTuple { fields: Value },
    /// `expr_carried(value, member)` — the Node carrier for an expression-carried
    /// type projection whose receiver is COMPOUND (a field path `a.b`, not a single
    /// value ref). The ground single-ref form `s.T` rides a hash-consed
    /// `Fn{ExprCarried, value: Ref(s), member: Ref(M)}` term (no Node — see
    /// `KnowledgeBase::make_expr_carried`); THIS carrier is for `a.b.T`, where the
    /// receiver is itself an occurrence (a `DotApply` field access — now structural,
    /// WI-397). `value` is the receiver occurrence (`TypeChild::Node`); `member` is
    /// the projected type member as `TypeChild::Ground(Ref(sym))` — mirroring the
    /// term form so `TermView` reads both carriers identically.
    ExprCarried { value: TypeChild, member: TypeChild },
}

/// Structural `EffectExpression`-sort IR (WI-342). Mirrors the row algebra
/// (`merge`/`present`/`absent`/`open`/`empty_row`) in
/// `stdlib/anthill/prelude/sort.anthill`.
#[derive(Debug)]
pub enum EffectExprNode {
    /// `merge(left, right)` — row union; the canonical form right-folds atoms.
    Merge { left: TypeChild, right: TypeChild },
    /// `present(label: Type)` — a single present effect label.
    Present { label: TypeChild },
    /// `guarded(label: Type, guard: List[reflect.Term])` — a CONDITIONAL present
    /// effect (proposal 048 / WI-478): present iff `guard` is not refuted at the
    /// call site (discharge is WI-067; conservatively present until then). `label`
    /// is the effect `Type` (as in `Present`); `guard` is a `Value`-carried
    /// `List[reflect.Term]` of goal terms — mirroring [`TypeNode::NamedTuple`]'s
    /// `fields: Value`, so a ground guard rides as `Value::Term` and a denoted /
    /// occurrence-bearing one as `Value::Node`, read identically through `TermView`.
    Guarded { label: TypeChild, guard: Value },
    /// `absent(label: Type)` — a `-e` absence guarantee.
    Absent { label: TypeChild },
    /// `open(tail: Type)` — a row-variable tail.
    Open { tail: TypeChild },
    /// `empty_row` — the closed empty row (ground; no children).
    EmptyRow,
}

/// Walk a NodeOccurrence tree top-down, invoking `visit(occ, class)`
/// at every `NodeKind::Expr` whose `classification` RefCell is set.
/// Children of every Expr variant are visited regardless of whether
/// the parent itself was classified — so deeply-nested classified
/// applies are still surfaced.
///
/// Used by `kb::req_insertion::run` to find classified call sites in
/// `kb.op_bodies` post-WI-251. Public so tests + tooling can iterate
/// classifications without re-implementing the walk.
/// Pre-order traversal of a NodeOccurrence tree: invoke `visit` on
/// every node whose `classification` RefCell is set. Iterative — uses
/// an explicit work-stack so deeply-nested let / match / lambda
/// chains stay flat on the host stack regardless of source nesting
/// depth.
pub fn visit_classifications(
    root: &Rc<NodeOccurrence>,
    visit: &mut impl FnMut(&Rc<NodeOccurrence>, &super::typing::CallClass),
) {
    let mut stack: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(32);
    stack.push(Rc::clone(root));
    while let Some(occ) = stack.pop() {
        let NodeKind::Expr { expr, classification, .. } = &occ.kind else {
            continue;
        };
        if let Some(c) = classification.borrow().as_deref() {
            visit(&occ, c);
        }
        for_each_child(expr, |c| stack.push(Rc::clone(c)));
    }
}

/// Canonical non-destructive walker over the direct
/// `Rc<NodeOccurrence>` children of an `Expr`. Invokes `f` once per
/// child slot, in a fixed per-variant order (field order: positional
/// then named; for `Match`, scrutinee then each branch's body then
/// guard). That order is load-bearing: `simp_rewrite::reassemble`
/// consumes children positionally and relies on it matching this
/// enumeration. Pre/post-order *across the tree* is still the caller's
/// concern — drive your own work-stack for that.
#[inline]
pub fn for_each_child(expr: &Expr, mut f: impl FnMut(&Rc<NodeOccurrence>)) {
    match expr {
        Expr::Apply { pos_args, named_args, .. }
        | Expr::Constructor { pos_args, named_args, .. }
        | Expr::Instantiation { pos_args, named_args, .. } => {
            for c in pos_args.iter() { f(c); }
            for (_, c) in named_args.iter() { f(c); }
        }
        Expr::If { condition, then_branch, else_branch } => {
            f(condition);
            f(then_branch);
            f(else_branch);
        }
        Expr::Let { pattern, value, body, .. } => {
            f(pattern);
            f(value);
            f(body);
        }
        Expr::Match { scrutinee, branches } => {
            f(scrutinee);
            for b in branches.iter() {
                f(&b.pattern);
                f(&b.body);
                if let Some(g) = &b.guard { f(g); }
            }
        }
        Expr::Lambda { param, body } => {
            f(param);
            f(body);
        }
        Expr::Proof { conclude, body, .. } => {
            // WI-538: child order conclude?, body — must match
            // `drain_expr_children` and `simp_rewrite::reassemble`.
            if let Some(c) = conclude { f(c); }
            f(body);
        }
        Expr::ListLit(es) | Expr::SetLit(es) => {
            for e in es.iter() { f(e); }
        }
        Expr::TupleLit { positional, named } => {
            for e in positional.iter() { f(e); }
            for (_, e) in named.iter() { f(e); }
        }
        Expr::HoApply { predicate, args } => {
            f(predicate);
            for a in args.iter() { f(a); }
        }
        Expr::DotApply { receiver, pos_args, named_args, .. } => {
            f(receiver);
            for c in pos_args.iter() { f(c); }
            for (_, c) in named_args.iter() { f(c); }
        }
        Expr::ApplyWithin { args, named_args, requirements, .. } => {
            for a in args.iter() { f(a); }
            for (_, a) in named_args.iter() { f(a); }
            for r in requirements.iter() { f(r); }
        }
        Expr::HoApplyWithin { predicate, args, requirements } => {
            f(predicate);
            for a in args.iter() { f(a); }
            for r in requirements.iter() { f(r); }
        }
        Expr::ConstructorWithin { pos_args, named_args, requirements, .. } => {
            for c in pos_args.iter() { f(c); }
            for (_, c) in named_args.iter() { f(c); }
            for r in requirements.iter() { f(r); }
        }
        Expr::LambdaWithin { param, body, requirements } => {
            f(param);
            f(body);
            for r in requirements.iter() { f(r); }
        }
        Expr::RequirementAtSort { chain, .. } => f(chain),
        Expr::ConstructRequirement { requirements, .. } => {
            for r in requirements.iter() { f(r); }
        }
        Expr::Const(_) | Expr::Ref(_) | Expr::Ident(_)
        | Expr::Var(_) | Expr::Bottom | Expr::VarRef { .. } => {}
    }
}

/// WI-318: mirror of `for_each_child` for `Pattern`. Invokes `f` once
/// per direct `Rc<NodeOccurrence>` child slot of a pattern, in a fixed
/// per-variant order (field order: type_ann; then positional then
/// named). The order is load-bearing — `reassemble_pattern` consumes
/// children positionally and relies on it matching this enumeration.
#[inline]
pub fn for_each_pattern_child(pat: &Pattern, mut f: impl FnMut(&Rc<NodeOccurrence>)) {
    match pat {
        Pattern::Var { type_ann, .. } => {
            if let Some(t) = type_ann { f(t); }
        }
        Pattern::Wildcard | Pattern::Literal { .. } => {}
        Pattern::Constructor { pos_args, named_args, .. } => {
            for c in pos_args.iter() { f(c); }
            for (_, c) in named_args.iter() { f(c); }
        }
        Pattern::Tuple { positional, named } => {
            for c in positional.iter() { f(c); }
            for (_, c) in named.iter() { f(c); }
        }
    }
}

// WI-342: non-destructive `for_each_*` walkers over Type/EffectExpr children
// (the twins of `for_each_child` / `for_each_pattern_child`) are intentionally
// NOT added in this slice — the only consumers would be the rule-body var
// collectors / rewriters, which are deferred to P3 (see the symmetry note in
// `occurrence_has_unbound_var`). The destructive `Drop` analogs (`drain_type_
// node` / `drain_effect_expr_node`) ARE present because `Drop` totality is
// mandatory the moment the variants exist.

/// WI-318: mirror of `simp_rewrite::reassemble` for a `Pattern`-kind
/// occurrence. Replaces each child slot by consuming `new_children` in
/// `for_each_pattern_child` order; returns `occ` unchanged (same `Rc`)
/// when no child moved. Used by `open_debruijn_node` /
/// `node_to_debruijn` after walking a Pattern's children — patterns
/// have no DeBruijn vars at their own structure (names are Symbols,
/// literals are values), so the parent walker only needs to rebuild
/// when a child Expr-kind type_ann was rewritten.
pub fn reassemble_pattern(
    occ: &Rc<NodeOccurrence>,
    new_children: &[Rc<NodeOccurrence>],
) -> Rc<NodeOccurrence> {
    let pat = match &occ.kind {
        NodeKind::Pattern(p) => p,
        _ => return Rc::clone(occ),
    };
    // Detect any move first; if every new child is ptr-eq to the
    // original, reuse `occ`. Otherwise rebuild.
    let mut changed = false;
    {
        let mut i = 0;
        for_each_pattern_child(pat, |c| {
            if !Rc::ptr_eq(c, &new_children[i]) {
                changed = true;
            }
            i += 1;
        });
    }
    if !changed {
        return Rc::clone(occ);
    }
    let mut idx = 0;
    let mut take = || {
        let c = Rc::clone(&new_children[idx]);
        idx += 1;
        c
    };
    let new_pat = match pat {
        Pattern::Var { name, type_ann } => Pattern::Var {
            name: *name,
            type_ann: type_ann.as_ref().map(|_| take()),
        },
        Pattern::Wildcard => Pattern::Wildcard,
        Pattern::Literal { value } => Pattern::Literal { value: value.clone() },
        Pattern::Constructor { name, pos_args, named_args } => {
            let pos: Vec<Rc<NodeOccurrence>> = pos_args.iter().map(|_| take()).collect();
            let named: Vec<(Symbol, Rc<NodeOccurrence>)> = named_args
                .iter()
                .map(|(s, _)| (*s, take()))
                .collect();
            Pattern::Constructor { name: *name, pos_args: pos, named_args: named }
        }
        Pattern::Tuple { positional, named } => {
            let pos: Vec<Rc<NodeOccurrence>> = positional.iter().map(|_| take()).collect();
            let named_out: Vec<(Symbol, Rc<NodeOccurrence>)> = named
                .iter()
                .map(|(s, _)| (*s, take()))
                .collect();
            Pattern::Tuple { positional: pos, named: named_out }
        }
    };
    NodeOccurrence::new_pattern(new_pat, occ.span, occ.owner)
}

// ── De Bruijn opening (rule-body atoms) ─────────────────────────

/// WI-246: open a De Bruijn-encoded rule-body-atom occurrence into a
/// fresh-Global one — the occurrence analog of `term_from_debruijn`
/// (`mod.rs`), and faithful to it (that opener is itself recursive via
/// `map_fn_children`). Replaces each `Expr::Var(Var::DeBruijn(i))` leaf
/// with `Expr::Var(Var::Global(fresh[i]))`; unchanged subtrees keep their
/// `Rc` (only the ancestor chain to a remapped var is rebuilt).
///
/// Rule body atoms are usually predicate applications — `Apply`/`Constructor`/
/// `Instantiation`/`HoApply` over leaves — but reflection / typing rules match
/// expression structure as data, so a body atom can also carry control-flow /
/// post-elaboration forms (`Match`/`If`/`Let`/`Lambda`/… materialized as
/// reflect-`Expr` data — WI-296). Those are opened generically via
/// `for_each_child` + `simp_rewrite::reassemble`. Recursion depth is bounded by
/// the atom's structure.
pub fn open_debruijn_node(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    fresh: &[VarId],
) -> Rc<NodeOccurrence> {
    // WI-318: a Pattern-kind occurrence walks its children uniformly
    // (Pattern's own structure has no DeBruijn vars — names are
    // Symbols, literals are values). DeBruijn vars live only in
    // Expr-kind child slots like the Var's `type_ann`; recurse into
    // those via `for_each_pattern_child` + `reassemble_pattern`.
    if let Some(pat) = occ.as_pattern() {
        let mut opened: Vec<Rc<NodeOccurrence>> = Vec::new();
        for_each_pattern_child(pat, |c| opened.push(open_debruijn_node(kb, c, fresh)));
        return reassemble_pattern(occ, &opened);
    }
    // WI-378 step 2 / WI-342-P3: open DeBruijn vars inside a Type/EffectExpr
    // occurrence's spine — the inverse of `node_to_debruijn`'s Type arm.
    if matches!(occ.kind, NodeKind::Type(_) | NodeKind::EffectExpr(_)) {
        return rewrite_type_occurrence(&OpenTypeRewrite { fresh }, kb, occ)
            .unwrap_or_else(|| Rc::clone(occ));
    }
    let Some(expr) = occ.as_expr() else { return Rc::clone(occ) };
    let rebuilt: Option<Expr> = match expr {
        Expr::Var(Var::DeBruijn(idx)) => fresh
            .get(*idx as usize)
            .map(|&vid| Expr::Var(Var::Global(vid))),
        // WI-298: Apply.type_args is a TermId field that can carry DeBruijn
        // vars from the rule's shared space — open it via `term_from_debruijn`
        // alongside the occurrence children, mirroring `close_type_args` on
        // the closing side (`node_to_debruijn`).
        Expr::Apply { functor, pos_args, named_args, type_args } => {
            let (pos, c1) = open_vec(kb, pos_args, fresh);
            let (named, c2) = open_named(kb, named_args, fresh);
            let (ta, c3) = open_type_args(kb, type_args, fresh);
            (c1 || c2 || c3).then(|| Expr::Apply {
                functor: *functor,
                pos_args: pos,
                named_args: named,
                type_args: ta,
            })
        }
        Expr::Constructor { name, pos_args, named_args } => {
            let (pos, c1) = open_vec(kb, pos_args, fresh);
            let (named, c2) = open_named(kb, named_args, fresh);
            (c1 || c2).then(|| Expr::Constructor { name: *name, pos_args: pos, named_args: named })
        }
        Expr::Instantiation { name, pos_args, named_args } => {
            let (pos, c1) = open_vec(kb, pos_args, fresh);
            let (named, c2) = open_named(kb, named_args, fresh);
            (c1 || c2).then(|| Expr::Instantiation { name: *name, pos_args: pos, named_args: named })
        }
        Expr::HoApply { predicate, args } => {
            let p = open_debruijn_node(kb, predicate, fresh);
            let (a, c2) = open_vec(kb, args, fresh);
            let c1 = !Rc::ptr_eq(&p, predicate);
            (c1 || c2).then(|| Expr::HoApply { predicate: p, args: a })
        }
        // WI-298: Let.type_annotation is a TermId (a type expression — proposal
        // 027.1) that can carry DeBruijn vars from the rule's shared space —
        // open it via `term_from_debruijn` alongside the occurrence children,
        // mirroring the closing side (`node_to_debruijn`).
        Expr::Let { pattern, type_annotation, value, body } => {
            let new_pattern = open_debruijn_node(kb, pattern, fresh);
            let new_value = open_debruijn_node(kb, value, fresh);
            let new_body = open_debruijn_node(kb, body, fresh);
            let (new_ta, ta_changed) = open_option_value(kb, type_annotation, fresh);
            let c1 = !Rc::ptr_eq(&new_pattern, pattern);
            let c2 = !Rc::ptr_eq(&new_value, value);
            let c3 = !Rc::ptr_eq(&new_body, body);
            (c1 || c2 || c3 || ta_changed).then(|| Expr::Let {
                pattern: new_pattern,
                type_annotation: new_ta,
                value: new_value,
                body: new_body,
            })
        }
        // WI-298: ApplyWithin.type_args mirrors Apply.type_args; the generic
        // `_` arm below would leave them un-remapped because `for_each_child`
        // doesn't enumerate TermId fields. Explicit arm closes that gap and
        // mirrors `node_to_debruijn`'s ApplyWithin handling.
        Expr::ApplyWithin { functor, args, named_args, requirements, type_args } => {
            let (a, c1) = open_vec(kb, args, fresh);
            let (named, c2) = open_named(kb, named_args, fresh);
            let (reqs, c3) = open_vec(kb, requirements, fresh);
            let (ta, c4) = open_type_args(kb, type_args, fresh);
            (c1 || c2 || c3 || c4).then(|| Expr::ApplyWithin {
                functor: *functor,
                args: a,
                named_args: named,
                requirements: reqs,
                type_args: ta,
            })
        }
        // WI-296: a *child-bearing* form CAN occur at a rule-body atom
        // position — reflection / typing rules match expression structure as
        // data (e.g. `occurrence_term(?e, lambda(param: …, body: ?b))`,
        // `…match_expr(scrutinee: ?s, …)`). The materializer (`visit_fn`)
        // builds these as `Expr::Match`/`If`/`Let`/`Lambda`/… so we must open
        // their children rather than assert they can't appear. Open each
        // child (in `for_each_child` source order) and `reassemble`; genuine
        // leaves enumerate no children, so `reassemble` returns `occ`
        // unchanged.
        _ => {
            let mut opened: Vec<Rc<NodeOccurrence>> = Vec::new();
            for_each_child(expr, |c| opened.push(open_debruijn_node(kb, c, fresh)));
            return super::simp_rewrite::reassemble(occ, &opened);
        }
    };
    match rebuilt {
        // WI-502 Step 3: carry the stamped `inferred_type` through the rebuild.
        Some(e) => occ.rebuilt_expr(e),
        None => Rc::clone(occ),
    }
}

/// WI-246: the inverse of [`open_debruijn_node`] — close a fresh-Global
/// rule-body-atom occurrence into its De Bruijn form, the occurrence analog of
/// `KnowledgeBase::term_to_debruijn`. Replaces each `Expr::Var(Var::Global(vid))`
/// leaf whose `vid` is in `var_order` with `Expr::Var(Var::DeBruijn(idx))`,
/// using the SAME index convention as `term_to_debruijn`
/// (`idx = var_order.len() - 1 - position`), so a body built natively in the
/// loader (Global vars) lands in the De Bruijn form `with_fresh_vars` opens.
/// Globals not in `var_order` (e.g. an entity-expansion fresh var that the
/// rule's var collection also saw — it WILL be in `var_order`) are kept; a
/// genuinely-free Global stays Global. Unchanged subtrees keep their `Rc`.
///
/// This is the precise inverse of [`open_debruijn_node`] (the close/open
/// round-trip the resolver relies on). It rewrites `Var` leaves inside
/// `Rc<NodeOccurrence>` children AND inside the remaining `TermId`-typed
/// occurrence fields — `Let.type_annotation`, `Apply`/`ApplyWithin.type_args`
/// (post-WI-319 the pattern slots — Lambda/LambdaWithin.param, Let.pattern,
/// MatchBranch.pattern — are themselves Pattern-kind Rc<NodeOccurrence>
/// children, no longer TermId) — by running those through
/// `KnowledgeBase::term_to_debruijn` (hence `&mut self`). So a body atom is
/// fully De Bruijn-closed regardless of where its vars live, matching what the
/// prior `materialize(term_to_debruijn(t))` path produced (a var nested in such
/// a field is now in the rule's De Bruijn key space, e.g. for the typer).
/// WI-298 makes [`open_debruijn_node`] OPEN the same `TermId` fields back
/// symmetrically — the close/open round-trip is now uniform across child
/// occurrences and TermId fields.
pub fn node_to_debruijn(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    var_order: &[VarId],
) -> Rc<NodeOccurrence> {
    // WI-318: pattern occurrences walk uniformly — see the mirror
    // comment on `open_debruijn_node` for the rationale.
    if let Some(pat) = occ.as_pattern() {
        let mut closed: Vec<Rc<NodeOccurrence>> = Vec::new();
        for_each_pattern_child(pat, |c| closed.push(node_to_debruijn(kb, c, var_order)));
        return reassemble_pattern(occ, &closed);
    }
    // WI-378 step 2 / WI-342-P3: close vars inside a Type/EffectExpr occurrence's
    // spine (ground `TermId` children via `term_to_debruijn`, child occurrences by
    // recursion). The shared structural walk keeps close/open/σ in lockstep.
    if matches!(occ.kind, NodeKind::Type(_) | NodeKind::EffectExpr(_)) {
        return rewrite_type_occurrence(&CloseTypeRewrite { var_order }, kb, occ)
            .unwrap_or_else(|| Rc::clone(occ));
    }
    let Some(expr) = occ.as_expr() else { return Rc::clone(occ) };
    let rebuilt: Option<Expr> = match expr {
        Expr::Var(Var::Global(vid)) => var_order
            .iter()
            .position(|v| v == vid)
            .map(|pos| Expr::Var(Var::DeBruijn((var_order.len() - 1 - pos) as u32))),
        Expr::Apply { functor, pos_args, named_args, type_args } => {
            let (pos, c1) = close_vec(kb, pos_args, var_order);
            let (named, c2) = close_named(kb, named_args, var_order);
            let (ta, c3) = close_type_args(kb, type_args, var_order);
            (c1 || c2 || c3).then(|| Expr::Apply {
                functor: *functor,
                pos_args: pos,
                named_args: named,
                type_args: ta,
            })
        }
        Expr::Constructor { name, pos_args, named_args } => {
            let (pos, c1) = close_vec(kb, pos_args, var_order);
            let (named, c2) = close_named(kb, named_args, var_order);
            (c1 || c2).then(|| Expr::Constructor { name: *name, pos_args: pos, named_args: named })
        }
        Expr::Instantiation { name, pos_args, named_args } => {
            let (pos, c1) = close_vec(kb, pos_args, var_order);
            let (named, c2) = close_named(kb, named_args, var_order);
            (c1 || c2).then(|| Expr::Instantiation { name: *name, pos_args: pos, named_args: named })
        }
        Expr::HoApply { predicate, args } => {
            let p = node_to_debruijn(kb, predicate, var_order);
            let (a, c2) = close_vec(kb, args, var_order);
            let c1 = !Rc::ptr_eq(&p, predicate);
            (c1 || c2).then(|| Expr::HoApply { predicate: p, args: a })
        }
        // Reflect-data forms with `TermId`-typed pattern/param fields: close
        // both their occurrence children and those `TermId` fields (the latter
        // via `term_to_debruijn`), so a var living in a pattern/param is closed
        // to the same De Bruijn space as the rest of the rule.
        // WI-318: pattern is now a Pattern-kind Rc<NodeOccurrence>,
        // walked structurally via the explicit Let arm below.
        // WI-298: type_annotation (Option<TermId>) is a type expression
        // — close DeBruijn vars in it via `term_to_debruijn`, mirroring
        // `open_debruijn_node` on the opening side.
        // WI-318: Lambda / LambdaWithin no longer have a TermId-typed
        // param — the param is now a Pattern-kind Rc<NodeOccurrence>
        // that walks via the generic `for_each_child` + `reassemble`
        // path below. The explicit arms here are gone; fall-through
        // handles them uniformly.
        // WI-318: MatchBranch.pattern is now a Pattern-kind occurrence —
        // close it via the recursive node walker like any other child.
        // (Was: `kb.term_to_debruijn(br.pattern, var_order)`.)
        Expr::Let { pattern, type_annotation, value, body } => {
            let new_pattern = node_to_debruijn(kb, pattern, var_order);
            let new_value = node_to_debruijn(kb, value, var_order);
            let new_body = node_to_debruijn(kb, body, var_order);
            let (new_ta, ta_changed) = close_option_value(kb, type_annotation, var_order);
            let c1 = !Rc::ptr_eq(&new_pattern, pattern);
            let c2 = !Rc::ptr_eq(&new_value, value);
            let c3 = !Rc::ptr_eq(&new_body, body);
            (c1 || c2 || c3 || ta_changed).then(|| Expr::Let {
                pattern: new_pattern,
                type_annotation: new_ta,
                value: new_value,
                body: new_body,
            })
        }
        Expr::Match { scrutinee, branches } => {
            let s = node_to_debruijn(kb, scrutinee, var_order);
            let mut changed = !Rc::ptr_eq(&s, scrutinee);
            let mut new_branches: Vec<MatchBranch> = Vec::with_capacity(branches.len());
            for br in branches {
                let new_pattern = node_to_debruijn(kb, &br.pattern, var_order);
                if !Rc::ptr_eq(&new_pattern, &br.pattern) {
                    changed = true;
                }
                let guard = match &br.guard {
                    Some(g) => {
                        let ng = node_to_debruijn(kb, g, var_order);
                        if !Rc::ptr_eq(&ng, g) {
                            changed = true;
                        }
                        Some(ng)
                    }
                    None => None,
                };
                let body = node_to_debruijn(kb, &br.body, var_order);
                if !Rc::ptr_eq(&body, &br.body) {
                    changed = true;
                }
                new_branches.push(MatchBranch { pattern: new_pattern, guard, body, span: br.span });
            }
            changed.then(|| Expr::Match { scrutinee: s, branches: new_branches })
        }
        Expr::ApplyWithin { functor, args, named_args, requirements, type_args } => {
            let (a, c1) = close_vec(kb, args, var_order);
            let (named, c2) = close_named(kb, named_args, var_order);
            let (reqs, c3) = close_vec(kb, requirements, var_order);
            let (ta, c4) = close_type_args(kb, type_args, var_order);
            (c1 || c2 || c3 || c4).then(|| Expr::ApplyWithin {
                functor: *functor,
                args: a,
                named_args: named,
                requirements: reqs,
                type_args: ta,
            })
        }
        // Remaining child-bearing forms carry NO `TermId`-typed var fields
        // (If / DotApply / collection literals / *Within without param /
        // RequirementAtSort / ConstructRequirement): close their occurrence
        // children generically and reassemble, mirroring `open_debruijn_node`.
        _ => {
            let mut closed: Vec<Rc<NodeOccurrence>> = Vec::new();
            for_each_child(expr, |c| closed.push(node_to_debruijn(kb, c, var_order)));
            return super::simp_rewrite::reassemble(occ, &closed);
        }
    };
    match rebuilt {
        // WI-502 Step 3: carry the stamped `inferred_type` through the rebuild.
        Some(e) => occ.rebuilt_expr(e),
        None => Rc::clone(occ),
    }
}

fn close_vec(
    kb: &mut KnowledgeBase,
    items: &[Rc<NodeOccurrence>],
    var_order: &[VarId],
) -> (Vec<Rc<NodeOccurrence>>, bool) {
    let mut changed = false;
    let mut out = Vec::with_capacity(items.len());
    for c in items {
        let r = node_to_debruijn(kb, c, var_order);
        changed |= !Rc::ptr_eq(&r, c);
        out.push(r);
    }
    (out, changed)
}

fn close_named(
    kb: &mut KnowledgeBase,
    items: &[(Symbol, Rc<NodeOccurrence>)],
    var_order: &[VarId],
) -> (Vec<(Symbol, Rc<NodeOccurrence>)>, bool) {
    let mut changed = false;
    let mut out = Vec::with_capacity(items.len());
    for (s, c) in items {
        let r = node_to_debruijn(kb, c, var_order);
        changed |= !Rc::ptr_eq(&r, c);
        out.push((*s, r));
    }
    (out, changed)
}

/// Close vars inside a call site's `type_args` (`(name?, type-Value)` pairs)
/// via the carrier-agnostic `close_value_type` (WI-342 S4b): a ground
/// `Value::Term` closes through `term_to_debruijn`; a `Value::Node` type
/// passes through unchanged (it carries no vars).
fn close_type_args(
    kb: &mut KnowledgeBase,
    items: &[(Option<Symbol>, Value)],
    var_order: &[VarId],
) -> (Vec<(Option<Symbol>, Value)>, bool) {
    let mut changed = false;
    let mut out = Vec::with_capacity(items.len());
    for (name, v) in items {
        let (nv, ch) = close_value_type(kb, v, var_order);
        changed |= ch;
        out.push((*name, nv));
    }
    (out, changed)
}

/// WI-342/WI-378: DeBruijn-close the vars of a carrier-agnostic type `Value` —
/// a thin delegate to the shared [`map_value_type`] (a `Value::Node` now descends
/// the Type/EffectExpr spine; a `NamedTuple.fields` `Entity`/`Tuple` cons-list
/// recurses into its element field types). Twin of `open_value_type`.
fn close_value_type(kb: &mut KnowledgeBase, v: &Value, var_order: &[VarId]) -> (Value, bool) {
    map_value_type(&CloseTypeRewrite { var_order }, kb, v)
}

/// WI-298/WI-342: close vars inside an `Option<Value>` type field (today only
/// `Let.type_annotation`) — twin of `open_option_value`.
fn close_option_value(
    kb: &mut KnowledgeBase,
    item: &Option<Value>,
    var_order: &[VarId],
) -> (Option<Value>, bool) {
    match item {
        Some(v) => {
            let (nv, changed) = close_value_type(kb, v, var_order);
            (Some(nv), changed)
        }
        None => (None, false),
    }
}

fn open_vec(
    kb: &mut KnowledgeBase,
    items: &[Rc<NodeOccurrence>],
    fresh: &[VarId],
) -> (Vec<Rc<NodeOccurrence>>, bool) {
    let mut changed = false;
    let mut out = Vec::with_capacity(items.len());
    for c in items {
        let r = open_debruijn_node(kb, c, fresh);
        changed |= !Rc::ptr_eq(&r, c);
        out.push(r);
    }
    (out, changed)
}

fn open_named(
    kb: &mut KnowledgeBase,
    items: &[(Symbol, Rc<NodeOccurrence>)],
    fresh: &[VarId],
) -> (Vec<(Symbol, Rc<NodeOccurrence>)>, bool) {
    let mut changed = false;
    let mut out = Vec::with_capacity(items.len());
    for (s, c) in items {
        let r = open_debruijn_node(kb, c, fresh);
        changed |= !Rc::ptr_eq(&r, c);
        out.push((*s, r));
    }
    (out, changed)
}

/// WI-298/WI-342 S4b: open DeBruijn vars inside a call site's `type_args`
/// (`(name?, type-Value)` pairs) via the carrier-agnostic `open_value_type` —
/// the opener twin of `close_type_args`. A ground `Value::Term` opens through
/// `term_from_debruijn`; a `Value::Node` type passes through unchanged.
fn open_type_args(
    kb: &mut KnowledgeBase,
    items: &[(Option<Symbol>, Value)],
    fresh: &[VarId],
) -> (Vec<(Option<Symbol>, Value)>, bool) {
    let mut changed = false;
    let mut out = Vec::with_capacity(items.len());
    for (name, v) in items {
        let (nv, ch) = open_value_type(kb, v, fresh);
        changed |= ch;
        out.push((*name, nv));
    }
    (out, changed)
}

/// WI-342/WI-378: DeBruijn-open the vars of a carrier-agnostic type `Value` — the
/// inverse of `close_value_type`, delegating to the shared [`map_value_type`]
/// (a ground `Value::Term` via `term_from_debruijn`; a `Value::Node` descends the
/// type spine; a `NamedTuple.fields` cons-list recurses). Shared by
/// `Let.type_annotation` (`open_option_value`) and `Apply`/`ApplyWithin.type_args`
/// (`open_type_args`).
fn open_value_type(kb: &mut KnowledgeBase, v: &Value, fresh: &[VarId]) -> (Value, bool) {
    map_value_type(&OpenTypeRewrite { fresh }, kb, v)
}

/// WI-298/WI-342: open DeBruijn vars inside an `Option<Value>` type field (today
/// only `Let.type_annotation`) — the opener twin of `close_option_value`.
fn open_option_value(
    kb: &mut KnowledgeBase,
    item: &Option<Value>,
    fresh: &[VarId],
) -> (Option<Value>, bool) {
    match item {
        Some(v) => {
            let (nv, changed) = open_value_type(kb, v, fresh);
            (Some(nv), changed)
        }
        None => (None, false),
    }
}

// ── Type / EffectExpr var rewrite (WI-378 step 2 / WI-342-P3) ────
//
// A `Type` / `EffectExpression` occurrence is a `Value`-carried type whose
// `denoted` spine forbids hash-consing. Until this slice the three rule-var
// rewriters (`node_to_debruijn` close, `open_debruijn_node` open,
// `substitute_occurrence` σ) treated such an occurrence as opaque — they
// early-returned on a non-`Expr` node, so a logical var living in a `TypeChild`
// (a parameter binding `Vector[Int, ?n]`, an effect label `Modify[?c]`) was
// neither closed, opened, nor substituted. The var-collector likewise skipped
// it. No producer mints such a var today (denoteds are `Ref`/`Const`, type-vars
// stay ground `TypeChild::Ground` — see the carrier rule), so this is
// forward-correct substrate; wiring it lets the same machinery handle a type
// occurrence the moment a dependent-type producer (WI-373 gap 1) emits one.
//
// All three rewriters share ONE structural walk (`map_type_node` /
// `map_effect_node`) parameterized by [`TypeChildRewrite`] — each supplies how
// to rewrite a ground `TermId`, a child occurrence, and the `Value`-carried
// `NamedTuple.fields` — so the close/open/σ trio cannot drift out of lockstep
// over the type spine (the WI-378 anti-lockstep goal).

/// The per-carrier leaf operation a Type/EffectExpr structural rewrite needs:
/// how to rewrite a ground `TermId` and how to rewrite a child occurrence.
/// `Value`-carried children (`NamedTuple.fields`) are handled uniformly by
/// [`map_value_type`] in terms of these two leaves — so close/open/σ share ONE
/// definition of "rewrite a type Value" and cannot drift (the WI-378 goal).
trait TypeChildRewrite {
    /// Rewrite a ground type child (a hash-consed `TermId`); `bool` = changed.
    fn term(&self, kb: &mut KnowledgeBase, t: TermId) -> (TermId, bool);
    /// Rewrite a `Rc<NodeOccurrence>` child — a nested Type/EffectExpr node or a
    /// `Denoted` value occurrence — by recursing the owning rewriter.
    fn node(&self, kb: &mut KnowledgeBase, n: &Rc<NodeOccurrence>) -> Rc<NodeOccurrence>;
}

fn map_type_child<R: TypeChildRewrite>(
    r: &R,
    kb: &mut KnowledgeBase,
    child: &TypeChild,
) -> (TypeChild, bool) {
    match child {
        TypeChild::Ground(t) => {
            let (nt, ch) = r.term(kb, *t);
            (TypeChild::Ground(nt), ch)
        }
        TypeChild::Node(n) => {
            let nn = r.node(kb, n);
            let ch = !Rc::ptr_eq(&nn, n);
            (TypeChild::Node(nn), ch)
        }
    }
}

fn map_type_node<R: TypeChildRewrite>(
    r: &R,
    kb: &mut KnowledgeBase,
    tn: &TypeNode,
) -> (TypeNode, bool) {
    match tn {
        TypeNode::Denoted { value } => {
            let nv = r.node(kb, value);
            let ch = !Rc::ptr_eq(&nv, value);
            (TypeNode::Denoted { value: nv }, ch)
        }
        TypeNode::Parameterized { base, bindings } => {
            let (nbase, mut changed) = map_type_child(r, kb, base);
            let mut nbind = Vec::with_capacity(bindings.len());
            for (s, c) in bindings {
                let (nc, ch) = map_type_child(r, kb, c);
                changed |= ch;
                nbind.push((*s, nc));
            }
            (TypeNode::Parameterized { base: nbase, bindings: nbind }, changed)
        }
        TypeNode::EffectsRows { effects_expr } => {
            let (ne, ch) = map_type_child(r, kb, effects_expr);
            (TypeNode::EffectsRows { effects_expr: ne }, ch)
        }
        TypeNode::Arrow { param, result, effects } => {
            let (np, c1) = map_type_child(r, kb, param);
            let (nr, c2) = map_type_child(r, kb, result);
            let (nf, c3) = map_type_child(r, kb, effects);
            (TypeNode::Arrow { param: np, result: nr, effects: nf }, c1 || c2 || c3)
        }
        TypeNode::ExprCarried { value, member } => {
            let (nv, c1) = map_type_child(r, kb, value);
            let (nm, c2) = map_type_child(r, kb, member);
            (TypeNode::ExprCarried { value: nv, member: nm }, c1 || c2)
        }
        TypeNode::NamedTuple { fields } => {
            let (nf, ch) = map_value_type(r, kb, fields);
            (TypeNode::NamedTuple { fields: nf }, ch)
        }
    }
}

/// Rewrite a type-position `Value` under a [`TypeChildRewrite`] — the single
/// definition of "rewrite the vars of a type Value", shared by `close`/`open`/`σ`
/// (`close_value_type` / `open_value_type` / `subst_value_type` are thin
/// delegates). A ground `Value::Term` runs the leaf `term` op; a `Value::Node`
/// recurses the `node` rewriter (which now descends Type/EffectExpr spines); a
/// `Value::Entity`/`Tuple` (the `NamedTuple.fields` `List[TypeField]` cons-list,
/// whose element field-types can themselves be `Value::Term`/`Value::Node`)
/// recurses into its children — matching the head-side `close_value_head_debruijn`
/// and the occurs-check, which also descend that cons-list. A scalar / other
/// carrier has no vars (no-op).
fn map_value_type<R: TypeChildRewrite>(
    r: &R,
    kb: &mut KnowledgeBase,
    v: &Value,
) -> (Value, bool) {
    match v {
        Value::Term { id: t, .. } => {
            let (nt, ch) = r.term(kb, *t);
            (Value::term(nt), ch)
        }
        Value::Node(occ) => {
            let nn = r.node(kb, occ);
            let ch = !Rc::ptr_eq(&nn, occ);
            (Value::Node(nn), ch)
        }
        Value::Entity { functor, pos, named, .. } => {
            let (npos, c1) = map_value_seq(r, kb, pos);
            let (nnamed, c2) = map_value_named(r, kb, named);
            // Reuse the original (cheap Rc bump) when no child var changed — the
            // ptr-eq economy the Type/Expr rewriters keep.
            if c1 || c2 {
                (Value::Entity { functor: *functor, pos: Rc::from(npos), named: Rc::from(nnamed), ty: None }, true)
            } else {
                (v.clone(), false)
            }
        }
        Value::Tuple { pos, named, .. } => {
            let (npos, c1) = map_value_seq(r, kb, pos);
            let (nnamed, c2) = map_value_named(r, kb, named);
            if c1 || c2 {
                (Value::Tuple { pos: Rc::from(npos), named: Rc::from(nnamed), ty: None }, true)
            } else {
                (v.clone(), false)
            }
        }
        // Scalars / runtime carriers hold no type vars — leave untouched.
        other => (other.clone(), false),
    }
}

fn map_value_seq<R: TypeChildRewrite>(
    r: &R,
    kb: &mut KnowledgeBase,
    items: &[Value],
) -> (Vec<Value>, bool) {
    let mut changed = false;
    let mut out = Vec::with_capacity(items.len());
    for c in items {
        let (nc, ch) = map_value_type(r, kb, c);
        changed |= ch;
        out.push(nc);
    }
    (out, changed)
}

fn map_value_named<R: TypeChildRewrite>(
    r: &R,
    kb: &mut KnowledgeBase,
    items: &[(Symbol, Value)],
) -> (Vec<(Symbol, Value)>, bool) {
    let mut changed = false;
    let mut out = Vec::with_capacity(items.len());
    for (s, c) in items {
        let (nc, ch) = map_value_type(r, kb, c);
        changed |= ch;
        out.push((*s, nc));
    }
    (out, changed)
}

fn map_effect_node<R: TypeChildRewrite>(
    r: &R,
    kb: &mut KnowledgeBase,
    en: &EffectExprNode,
) -> (EffectExprNode, bool) {
    match en {
        EffectExprNode::Merge { left, right } => {
            let (nl, c1) = map_type_child(r, kb, left);
            let (nr, c2) = map_type_child(r, kb, right);
            (EffectExprNode::Merge { left: nl, right: nr }, c1 || c2)
        }
        EffectExprNode::Present { label } => {
            let (nl, ch) = map_type_child(r, kb, label);
            (EffectExprNode::Present { label: nl }, ch)
        }
        EffectExprNode::Guarded { label, guard } => {
            let (nl, c1) = map_type_child(r, kb, label);
            let (ng, c2) = map_value_type(r, kb, guard);
            (EffectExprNode::Guarded { label: nl, guard: ng }, c1 || c2)
        }
        EffectExprNode::Absent { label } => {
            let (nl, ch) = map_type_child(r, kb, label);
            (EffectExprNode::Absent { label: nl }, ch)
        }
        EffectExprNode::Open { tail } => {
            let (nt, ch) = map_type_child(r, kb, tail);
            (EffectExprNode::Open { tail: nt }, ch)
        }
        EffectExprNode::EmptyRow => (EffectExprNode::EmptyRow, false),
    }
}

/// Rebuild a Type/EffectExpr occurrence under a [`TypeChildRewrite`], reusing the
/// original `Rc` when nothing in the spine changed (the same ptr-eq economy the
/// `Expr`/`Pattern` rewriters use).
fn rewrite_type_occurrence<R: TypeChildRewrite>(
    r: &R,
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
) -> Option<Rc<NodeOccurrence>> {
    match &occ.kind {
        NodeKind::Type(tn) => {
            let (ntn, changed) = map_type_node(r, kb, tn);
            changed.then(|| NodeOccurrence::new_type(ntn, occ.span, occ.owner))
        }
        NodeKind::EffectExpr(en) => {
            let (nen, changed) = map_effect_node(r, kb, en);
            changed.then(|| NodeOccurrence::new_effect_expr(nen, occ.span, occ.owner))
        }
        _ => None,
    }
}

struct CloseTypeRewrite<'a> {
    var_order: &'a [VarId],
}
impl TypeChildRewrite for CloseTypeRewrite<'_> {
    fn term(&self, kb: &mut KnowledgeBase, t: TermId) -> (TermId, bool) {
        let nt = kb.term_to_debruijn(t, self.var_order);
        (nt, nt != t)
    }
    fn node(&self, kb: &mut KnowledgeBase, n: &Rc<NodeOccurrence>) -> Rc<NodeOccurrence> {
        node_to_debruijn(kb, n, self.var_order)
    }
}

struct OpenTypeRewrite<'a> {
    fresh: &'a [VarId],
}
impl TypeChildRewrite for OpenTypeRewrite<'_> {
    fn term(&self, kb: &mut KnowledgeBase, t: TermId) -> (TermId, bool) {
        let nt = kb.term_from_debruijn(t, self.fresh);
        (nt, nt != t)
    }
    fn node(&self, kb: &mut KnowledgeBase, n: &Rc<NodeOccurrence>) -> Rc<NodeOccurrence> {
        open_debruijn_node(kb, n, self.fresh)
    }
}

struct SubstTypeRewrite<'a> {
    subst: &'a Substitution,
}
impl TypeChildRewrite for SubstTypeRewrite<'_> {
    fn term(&self, kb: &mut KnowledgeBase, t: TermId) -> (TermId, bool) {
        let nt = kb.apply_subst(t, self.subst);
        (nt, nt != t)
    }
    fn node(&self, kb: &mut KnowledgeBase, n: &Rc<NodeOccurrence>) -> Rc<NodeOccurrence> {
        substitute_occurrence(kb, n, self.subst)
    }
}

/// WI-246: does the occurrence contain any `Expr::Var(Var::Global)` leaf?
/// In a σ-substituted goal occurrence every remaining Global-var leaf is
/// unbound (bound ones were spliced by [`substitute_occurrence`]), so this is
/// the occurrence analog of `KnowledgeBase::is_ground`'s "has unbound var"
/// test. Iterative pre-order — flat host stack regardless of nesting.
///
/// WI-298: also descends into `NodeKind::Pattern` occurrences via
/// `for_each_pattern_child` so a Global living in a pattern's nested
/// type-annotation Expr child is detected — symmetric with
/// `node_to_debruijn` / `open_debruijn_node`, which both walk Pattern
/// children uniformly.
pub fn occurrence_has_unbound_var(root: &Rc<NodeOccurrence>) -> bool {
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(root)];
    while let Some(occ) = stack.pop() {
        match &occ.kind {
            NodeKind::Expr { expr, .. } => match expr {
                Expr::Var(Var::Global(_)) => return true,
                _ => for_each_child(expr, |c| stack.push(Rc::clone(c))),
            },
            NodeKind::Pattern(pat) => {
                for_each_pattern_child(pat, |c| stack.push(Rc::clone(c)));
            }
            NodeKind::RuleHead { .. } => {}
            // WI-378 step 2 / WI-342-P3: a var inside a Type/EffectExpr occurrence
            // IS now walked — but via the type-field twins (`collect_value_type` /
            // the `*_value_type` rewriters), reached where a type `Value` sits
            // (`Apply.type_args` / `Let.type_annotation`). This `for_each_child`-
            // driven walk reaches a Type occurrence only once the deferred
            // type-field→occurrence-child migration routes those fields through
            // `for_each_child` — which must also thread `kb` here (this walker has
            // none, so it can't read a ground `TypeChild::Ground(TermId)`). Until
            // then a type occurrence reaching here is a bug, so assert.
            NodeKind::Type(_) | NodeKind::EffectExpr(_) => {
                debug_assert!(false, "type/effect occurrence in for_each_child var walk (type-field migration must thread kb here)");
            }
        }
    }
    false
}

/// WI-067 / proposal 050: does an occurrence reference a binder / parameter via
/// an `Expr::VarRef` (the node-carrier twin of the `var_ref(name)` term)? The
/// open-world-parameter floundering gate (`resolve.rs` `step_naf` / `step_builtin`)
/// reads a Γ goal/guard carried as a `Value::Node` through this; the `Value::Term`
/// twin is `KnowledgeBase::value_has_open_world_ref` (its `term_has_var_ref`
/// helper). The two carriers are symmetric: both match ONLY the canonical binder
/// form (`Expr::VarRef` / the `var_ref` functor), never a bare `Ref`/`Ident` — a
/// guard's binders are normalized to that form and `Γ` is built with it
/// ([`binder_ref_value`]), while a bare `Ref` is a closed datum (sort/op/const).
/// Pre-order child walk.
pub fn occurrence_has_var_ref(root: &Rc<NodeOccurrence>) -> bool {
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(root)];
    while let Some(occ) = stack.pop() {
        match &occ.kind {
            NodeKind::Expr { expr, .. } => match expr {
                Expr::VarRef { .. } => return true,
                _ => for_each_child(expr, |c| stack.push(Rc::clone(c))),
            },
            NodeKind::Pattern(pat) => {
                for_each_pattern_child(pat, |c| stack.push(Rc::clone(c)));
            }
            NodeKind::RuleHead { .. } => {}
            NodeKind::Type(_) | NodeKind::EffectExpr(_) => {}
        }
    }
    false
}

/// Collect the distinct `Var::Global` ids occurring in an occurrence (deduped
/// via `seen`), recursing into children. The occurrence twin of the term-side
/// `collect_vars_rec` — which likewise collects only `Var::Global` (Rigid /
/// DeBruijn ignored). Used by `with_fresh_vars`'s legacy path to gather a
/// rule's body vars without reading the term body (WI-246).
///
/// WI-298: also descends into `NodeKind::Pattern` occurrences via
/// `for_each_pattern_child` — symmetric with `node_to_debruijn` and
/// `open_debruijn_node`. Without this descent a Global living only in a
/// pattern's nested type-annotation Expr child would escape the legacy
/// rule-body var collection.
pub(super) fn collect_occurrence_global_vars(
    root: &Rc<NodeOccurrence>,
    vars: &mut Vec<VarId>,
    seen: &mut std::collections::HashSet<u32>,
) {
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(root)];
    while let Some(occ) = stack.pop() {
        match &occ.kind {
            NodeKind::Expr { expr, .. } => match expr {
                Expr::Var(Var::Global(vid)) => {
                    if seen.insert(vid.raw()) {
                        vars.push(*vid);
                    }
                }
                _ => for_each_child(expr, |c| stack.push(Rc::clone(c))),
            },
            NodeKind::Pattern(pat) => {
                for_each_pattern_child(pat, |c| stack.push(Rc::clone(c)));
            }
            NodeKind::RuleHead { .. } => {}
            // WI-378 step 2 / WI-342-P3: see the note in `occurrence_has_unbound_var`
            // — type-position vars are walked via `collect_value_type`; a type
            // occurrence reaching this no-`kb` `for_each_child` walk awaits the
            // type-field→child migration (which must thread `kb`), so assert.
            NodeKind::Type(_) | NodeKind::EffectExpr(_) => {
                debug_assert!(false, "type/effect occurrence in for_each_child var walk (type-field migration must thread kb here)");
            }
        }
    }
}

/// Forward-order twin of [`collect_occurrence_global_vars`]: collects the
/// distinct `Var::Global` ids in first-occurrence order matching the term-side
/// `collect_vars_rec` (positional args before named, depth-first, siblings
/// left-to-right) — NOT the stack-reversed sibling order of the legacy resolver
/// collector. Load-time De Bruijn numbering is assigned from this order, so it
/// must mirror the term walk it replaced — otherwise rule-body numbering (and
/// the occurrence-hashed rule cache key, WI-246) would shift. Used by
/// `finalize_rule_debruijn_nodes` to gather a rule's vars from head + occurrence
/// body without ever building the dropped term body.
///
/// CRUCIAL: must collect EVERY var that [`node_to_debruijn`] later closes,
/// otherwise an uncollected var stays a stray `Global` in the stored rule body
/// (escaping per-call freshening) and arity undercounts it. `for_each_child`
/// reaches only `Rc<NodeOccurrence>` children, so the reflect-data forms that
/// carry vars in `TermId`-typed pattern / param / type-annotation / type-arg
/// fields (`Let` / `Lambda` / `LambdaWithin` / `Match` / `Apply` / `ApplyWithin`
/// — see `node_to_debruijn`) need those fields walked term-side too. They are
/// collected AFTER the occurrence children so a var that ALSO appears in a
/// collectible child position keeps that earlier first-occurrence slot (a strict
/// no-op for such vars); only vars living *exclusively* in a `TermId` field are
/// newly appended.
pub(super) fn collect_occurrence_global_vars_ordered(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    vars: &mut Vec<VarId>,
    seen: &mut std::collections::HashSet<u32>,
) {
    match &occ.kind {
        NodeKind::Expr { expr, .. } => match expr {
            Expr::Var(Var::Global(vid)) => {
                if seen.insert(vid.raw()) {
                    vars.push(*vid);
                }
            }
            _ => {
                for_each_child(expr, |c| {
                    collect_occurrence_global_vars_ordered(kb, c, vars, seen)
                });
                collect_expr_termid_field_vars(kb, expr, vars, seen);
            }
        },
        // WI-298: descend into Pattern children so a Global living only in
        // a pattern's nested type-annotation Expr leaf is collected. Without
        // this descent the loader's first-occurrence-order arity walk would
        // miss it, leaving the rule's `node_to_debruijn` close to misplace
        // the var (or worse, undercount arity). Symmetric with
        // `node_to_debruijn`'s Pattern arm.
        NodeKind::Pattern(pat) => {
            for_each_pattern_child(pat, |c| {
                collect_occurrence_global_vars_ordered(kb, c, vars, seen)
            });
        }
        NodeKind::RuleHead { .. } => {}
        // WI-378 step 2 / WI-342-P3: this collector's type-position vars are
        // gathered by `collect_expr_termid_field_vars` → `collect_value_type`,
        // which now descends a Type/EffectExpr occurrence (symmetric with the
        // `*_value_type` rewriters). A type occurrence reaching THIS direct
        // `for_each_child` arm awaits the type-field→child migration (which must
        // thread `kb`); until then it would undercount arity, so assert.
        NodeKind::Type(_) | NodeKind::EffectExpr(_) => {
            debug_assert!(false, "type/effect occurrence in for_each_child var walk (type-field migration must thread kb here)");
        }
    }
}

/// Collect `Var::Global` ids from an `Expr`'s type-positional fields — the
/// `type_args` / `type_annotation` that `for_each_child` does not descend but
/// `node_to_debruijn` closes. The COLLECT twin of the closer's `close_type_args`
/// / `close_option_value`: it walks the SAME fields and reads each type `Value`
/// through [`collect_value_type`] (twin of `close_value_type`), so the var set
/// gathered here is exactly the set `node_to_debruijn` later closes — the
/// "keep in lockstep with `node_to_debruijn`" constraint is now structural
/// (twin functions), not a hand-maintained parallel (WI-378 step 1).
fn collect_expr_termid_field_vars(
    kb: &KnowledgeBase,
    expr: &Expr,
    vars: &mut Vec<VarId>,
    seen: &mut std::collections::HashSet<u32>,
) {
    match expr {
        Expr::Apply { type_args, .. } | Expr::ApplyWithin { type_args, .. } => {
            collect_type_args_vars(kb, type_args, vars, seen)
        }
        Expr::Let { type_annotation, .. } => {
            collect_option_value(kb, type_annotation, vars, seen)
        }
        // WI-318: Lambda / LambdaWithin params and MatchBranch.pattern are
        // Pattern-kind occurrences walked by `for_each_child` in the caller.
        _ => {}
    }
}

/// Collect the free Global vars of a type `Value` — the COLLECT twin of
/// [`map_value_type`] (used by `close`/`open`/`σ`), walking the SAME carriers so
/// the var set gathered here is exactly the set those rewriters close (WI-378).
/// A `Value::Term` reads via `collect_vars_rec`; a `Value::Node` descends the
/// Type/EffectExpr spine; a `Value::Entity`/`Tuple` (the `NamedTuple.fields`
/// `List[TypeField]` cons-list) recurses into its element field types; scalars /
/// other carriers contribute nothing.
fn collect_value_type(
    kb: &KnowledgeBase,
    v: &Value,
    vars: &mut Vec<VarId>,
    seen: &mut std::collections::HashSet<u32>,
) {
    match v {
        Value::Term { id: t, .. } => kb.collect_vars_rec(*t, vars, seen),
        Value::Node(occ) => collect_type_or_expr_node_vars(kb, occ, vars, seen),
        Value::Entity { pos, named, .. } | Value::Tuple { pos, named, .. } => {
            for c in pos.iter() {
                collect_value_type(kb, c, vars, seen);
            }
            for (_, c) in named.iter() {
                collect_value_type(kb, c, vars, seen);
            }
        }
        _ => {}
    }
}

/// Collect the free Global vars from a child occurrence sitting inside a
/// Type/EffectExpr spine: it is itself a `Type` node, an `EffectExpr` node, or
/// an `Expr` (a `Denoted` value, e.g. `Expr::Ref`). Dispatch on its kind — the
/// COLLECT analog of the `node` arm of [`map_type_node`] (used by the
/// rewriters). Mirrors the structural walk so collect/close/open/σ stay in
/// lockstep over the type spine (WI-378).
fn collect_type_or_expr_node_vars(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    vars: &mut Vec<VarId>,
    seen: &mut std::collections::HashSet<u32>,
) {
    match &occ.kind {
        NodeKind::Type(tn) => collect_type_node_vars(kb, tn, vars, seen),
        NodeKind::EffectExpr(en) => collect_effect_node_vars(kb, en, vars, seen),
        // A `Denoted` value (or any other) occurrence is an `Expr` — collect via
        // the ordered Expr walk so first-occurrence order matches the term walk.
        _ => collect_occurrence_global_vars_ordered(kb, occ, vars, seen),
    }
}

/// Collect Global vars in one [`TypeChild`] — ground term via `collect_vars_rec`,
/// child occurrence by recursion. COLLECT twin of [`map_type_child`].
fn collect_type_child(
    kb: &KnowledgeBase,
    child: &TypeChild,
    vars: &mut Vec<VarId>,
    seen: &mut std::collections::HashSet<u32>,
) {
    match child {
        TypeChild::Ground(t) => kb.collect_vars_rec(*t, vars, seen),
        TypeChild::Node(n) => collect_type_or_expr_node_vars(kb, n, vars, seen),
    }
}

/// COLLECT twin of [`map_type_node`]: walk a `TypeNode`'s children gathering
/// Global vars (WI-378 step 2 / WI-342-P3).
fn collect_type_node_vars(
    kb: &KnowledgeBase,
    tn: &TypeNode,
    vars: &mut Vec<VarId>,
    seen: &mut std::collections::HashSet<u32>,
) {
    match tn {
        TypeNode::Denoted { value } => collect_type_or_expr_node_vars(kb, value, vars, seen),
        TypeNode::Parameterized { base, bindings } => {
            collect_type_child(kb, base, vars, seen);
            for (_, c) in bindings {
                collect_type_child(kb, c, vars, seen);
            }
        }
        TypeNode::EffectsRows { effects_expr } => collect_type_child(kb, effects_expr, vars, seen),
        TypeNode::Arrow { param, result, effects } => {
            collect_type_child(kb, param, vars, seen);
            collect_type_child(kb, result, vars, seen);
            collect_type_child(kb, effects, vars, seen);
        }
        TypeNode::ExprCarried { value, member } => {
            collect_type_child(kb, value, vars, seen);
            collect_type_child(kb, member, vars, seen);
        }
        TypeNode::NamedTuple { fields } => collect_value_type(kb, fields, vars, seen),
    }
}

/// COLLECT twin of [`map_effect_node`].
fn collect_effect_node_vars(
    kb: &KnowledgeBase,
    en: &EffectExprNode,
    vars: &mut Vec<VarId>,
    seen: &mut std::collections::HashSet<u32>,
) {
    match en {
        EffectExprNode::Merge { left, right } => {
            collect_type_child(kb, left, vars, seen);
            collect_type_child(kb, right, vars, seen);
        }
        EffectExprNode::Present { label } | EffectExprNode::Absent { label } => {
            collect_type_child(kb, label, vars, seen)
        }
        EffectExprNode::Guarded { label, guard } => {
            collect_type_child(kb, label, vars, seen);
            collect_value_type(kb, guard, vars, seen);
        }
        EffectExprNode::Open { tail } => collect_type_child(kb, tail, vars, seen),
        EffectExprNode::EmptyRow => {}
    }
}

/// Collect twin of [`close_type_args`].
fn collect_type_args_vars(
    kb: &KnowledgeBase,
    items: &[(Option<Symbol>, Value)],
    vars: &mut Vec<VarId>,
    seen: &mut std::collections::HashSet<u32>,
) {
    for (_, v) in items {
        collect_value_type(kb, v, vars, seen);
    }
}

/// Collect twin of [`close_option_value`].
fn collect_option_value(
    kb: &KnowledgeBase,
    item: &Option<Value>,
    vars: &mut Vec<VarId>,
    seen: &mut std::collections::HashSet<u32>,
) {
    if let Some(v) = item {
        collect_value_type(kb, v, vars, seen);
    }
}

/// WI-471: the occurrence's intrinsic structural term form, materialized on
/// demand and memoized in `occ.term_cache`. Because `alloc` hash-conses, two
/// structurally-identical occurrences yield the SAME `TermId` — recovering
/// hash-cons identity for a `Node` without making it term-backed (the
/// drift-proof alternative to a separate structural fingerprint: it routes
/// through the one `Term` `Eq`/`Hash`, adding no second definition of
/// structural equality).
///
/// **Ownership: the returned `TermId` is BORROWED.** The cache owns the single
/// `+1` the final `alloc` returns and never releases it (pin-for-lifetime;
/// `Drop` cannot reach the store), so the term lives until KB teardown. Callers
/// must NOT `release` the result — unlike [`occurrence_to_term`], whose result
/// is *owned* — because releasing it would drop the cache's only refcount and
/// dangle the memoized id. The stamped `KbId` lets a future deferred-release
/// queue (WI-472) reclaim it.
///
/// Reads only the immutable structural spine (never the typer's `RefCell`
/// annotations), so the result is stable for the occurrence's life — set once,
/// never invalidated. Only the ROOT occurrence is memoized; children are
/// re-materialized by `occurrence_to_term` on each miss (their own `term_cache`
/// is untouched here). Takes `&Rc<NodeOccurrence>` (like [`occurrence_to_term`]);
/// a caller holding an occurrence reachable from `kb` clones the `Rc` out first
/// to avoid the `&mut kb` / `&occ` borrow clash.
pub fn cached_term(kb: &mut KnowledgeBase, occ: &Rc<NodeOccurrence>) -> TermId {
    // A hit is valid only for the KB that stamped it — a `TermId` indexes one
    // `TermStore`. Same KB → return the memoized id. A foreign stamp (the same
    // occurrence read against a different KB; rare, occurrences are normally
    // single-KB) is re-materialized against THIS store and re-stamped — never
    // returned blindly (that would index the wrong store). The prior store's
    // `+1` stays pinned there, reclaimed at its own teardown.
    if let Some((id, t)) = occ.term_cache.get() {
        if id == kb.id {
            return t;
        }
    }
    let t = occurrence_to_term(kb, occ);
    occ.term_cache.set(Some((kb.id, t)));
    t
}

/// WI-246: reify a rule-body-atom occurrence to a hash-consed `TermId` — the
/// reverse of [`materialize_from_handle`]. Used ONLY at genuine term/identity
/// boundaries (the resolver's dedup `seen_goals` key and `Solution.residual`),
/// never for goal dispatch (goals match via `TermView`). Recursion is bounded
/// by the goal-atom structure (predicate applications over leaves); control-
/// flow forms can't appear at a goal position and fall to `⊥`.
pub fn occurrence_to_term(kb: &mut KnowledgeBase, occ: &Rc<NodeOccurrence>) -> TermId {
    match try_occurrence_to_term(kb, occ) {
        Some(t) => t,
        // A *child-bearing* control-flow / post-elaboration form can't occur at
        // a goal position — assert (debug) so a future violation fails a test
        // rather than silently reifying to ⊥, matching `substitute_occurrence`'s
        // guard. Callers that legitimately may see such forms (reflection-pattern
        // reification, WI-297) use `try_occurrence_to_term` instead.
        None => {
            debug_assert!(
                false,
                "occurrence_to_term: unexpected non-goal Expr: {:?}",
                occ.as_expr().map(std::mem::discriminant),
            );
            kb.alloc(Term::Bottom)
        }
    }
}

/// WI-297: total variant of [`occurrence_to_term`] — returns `None` for a
/// child-bearing control-flow form (`If`/`Let`/`Match`/`Lambda`/`HoApply`/…)
/// instead of asserting. `Bottom`/absent reify to `⊥` (`Some`). Used by
/// `occurrence_term`'s arg reification, where a reflection pattern of such a
/// form is simply not yet supported (no match) rather than a bug.
///
/// WI-298: a `NodeKind::Pattern` occurrence reifies via `pattern_to_term`
/// to its reflect-Term shape (var_pattern / wildcard / literal_pattern /
/// constructor_pattern / tuple_pattern); the latter recursively converts
/// nested Expr-kind type-annotation children via `occurrence_to_term`,
/// so a var inside a Pattern's annotation lands as `Term::Var`. Without
/// this route a Pattern child reached as a sub-occurrence would have
/// fallen to the `None => kb.alloc(Term::Bottom)` arm below — silently
/// reifying to ⊥ instead of the reflect-Pattern shape callers expect.
/// (Note: `pattern_to_term` resolves `anthill.reflect.Pattern.*` symbols,
/// so this path requires a prelude-loaded KB; the existing in-tree
/// callers — `occurrence_term` builtins in resolve.rs and the typer —
/// always run on such a KB.)
pub fn try_occurrence_to_term(kb: &mut KnowledgeBase, occ: &Rc<NodeOccurrence>) -> Option<TermId> {
    if let NodeKind::Pattern(_) = &occ.kind {
        return Some(pattern_to_term(kb, occ));
    }
    // WI-390: a Type / EffectExpr occurrence lowers faithfully to its hash-consed
    // term twin (mirroring the `make_*_type` builders), so a denoted-bearing type
    // round-trips through the term store instead of the former `None`→⊥ loss.
    // (A denoted's value is a qualified `Expr::Ref` — a globally-unique
    // Param/Field/CallbackParam place — which lowers to a bare `Term::Ref`, correct
    // because the qualified symbol IS the binding-site identity. A genuinely-local
    // `Expr::VarRef` (an unqualified lambda/`let` binder; no producer mints one in a
    // denoted today) is the deferred case: it would need `make_positioned` with a
    // resolved `pos`, so a bare `VarRef` reaching here stays a non-goal `None`.)
    if let Some(tn) = occ.as_type() {
        return Some(type_node_to_term(kb, tn));
    }
    if let Some(en) = occ.as_effect_expr() {
        return Some(effect_node_to_term(kb, en));
    }
    Some(match occ.as_expr() {
        Some(Expr::Var(v)) => kb.alloc(Term::Var(*v)),
        Some(Expr::Const(lit)) => kb.alloc(Term::Const(lit.clone())),
        Some(Expr::Ref(s)) => kb.alloc(Term::Ref(*s)),
        Some(Expr::Ident(s)) => kb.alloc(Term::Ident(*s)),
        Some(Expr::Apply { functor, pos_args, named_args, .. }) => {
            occ_build_fn(kb, *functor, pos_args, named_args)
        }
        Some(Expr::Constructor { name, pos_args, named_args })
        | Some(Expr::Instantiation { name, pos_args, named_args }) => {
            occ_build_fn(kb, *name, pos_args, named_args)
        }
        // WI-302 (WI-390 lossless lowering): a value FIELD-PATH (`c.contents`,
        // the carried value of a compound `denoted`) lowers to its `dot_apply`
        // term twin — `dot_apply(receiver, name, args: nil)` — built BYTE-IDENTICAL
        // to the loader's `LoadBuildFrame::DotApply` (same functor, same
        // `[receiver, name, args]` key order, same nullary-`nil` args list), so the
        // WI-425 occurrence↔term isomorphism holds and a compound-denoted-bearing
        // type round-trips through the term store instead of asserting to `⊥`. Only
        // the ARG-LESS field access is minted in a denoted; an args-bearing dot CALL
        // stays a non-goal `None` (reified by the `_` arm — not minted here).
        Some(Expr::DotApply { receiver, name, pos_args, named_args })
            if pos_args.is_empty() && named_args.is_empty() =>
        {
            let recv = occurrence_to_term(kb, receiver);
            let dot_apply = kb.resolve_symbol("anthill.reflect.Expr.dot_apply");
            let name_ref = kb.alloc(Term::Ref(*name));
            let args_nil = build_list_termid(kb, &[]);
            let (k_receiver, k_name, k_args) =
                (kb.intern("receiver"), kb.intern("name"), kb.intern("args"));
            kb.alloc(Term::Fn {
                functor: dot_apply,
                pos_args: smallvec::SmallVec::new(),
                named_args: smallvec::SmallVec::from_slice(&[
                    (k_receiver, recv),
                    (k_name, name_ref),
                    (k_args, args_nil),
                ]),
            })
        }
        // WI-537: a `var_ref(name)` lowers to its reflect term twin
        // `Fn{Expr.var_ref, name: Ref(name)}` — the inverse of `build_expr_leaf`,
        // byte-identical to its `TermView` view (`occ_head` reads VarRef as
        // `Functor{var_ref}` with the same `name: Ref` child). So a Γ goal/fact
        // over a binder round-trips through the term store (and the resolver's
        // `goal_value_to_term`) instead of the former non-goal `None` — which
        // tripped this function's debug_assert and reified the binder to ⊥.
        Some(Expr::VarRef { name }) => kb.make_var_ref_term(*name),
        // WI-027: a list literal `[…]` reifies to its `ListLiteral(…)` term twin
        // — the inverse of the `"ListLiteral" => Expr::ListLit` occurrence build —
        // so a goal (or a `forall ?x in […]` quantifier) carrying a
        // non-desugared list literal round-trips through the term store instead
        // of asserting to ⊥. Pure data, legitimately hash-consable.
        Some(Expr::ListLit(elems)) => {
            let functor = kb.resolve_symbol("anthill.reflect.ListLiteral");
            occ_build_fn(kb, functor, elems, &[])
        }
        // WI-559: a set literal `{…}` reifies to its `SetLiteral(…)` term twin
        // (elements in `pos_args`, like `ListLiteral`) — the inverse of the
        // `"SetLiteral" => Expr::SetLit` occurrence build. Without this arm a
        // set literal reaching reify fell to the `_ => None` non-goal arm and
        // hit `occurrence_to_term`'s debug_assert / silent ⊥.
        Some(Expr::SetLit(elems)) => {
            let functor = kb.resolve_symbol("anthill.reflect.SetLiteral");
            occ_build_fn(kb, functor, elems, &[])
        }
        // WI-559: a tuple literal `(…)` reifies to its `TupleLiteral(…)` term
        // twin — elements ride in `named_args` (positional → `_1`/`_2` labels),
        // the inverse of the `"TupleLiteral" => Expr::TupleLit` build. Same
        // motivation as `SetLit` above.
        Some(Expr::TupleLit { positional, named }) => {
            let functor = kb.resolve_symbol("anthill.reflect.TupleLiteral");
            occ_build_fn(kb, functor, positional, named)
        }
        Some(Expr::Bottom) | None => kb.alloc(Term::Bottom),
        // Child-bearing / non-goal form: no goal-term shape.
        _ => return None,
    })
}

/// WI-297: build a `cons(head:, tail:) | nil` list whose elements are the
/// given child occurrences — used by `sub_occurrences`. Only the spine is
/// constructed (as `Expr::Constructor` cons cells); the elements keep their
/// identity (the passed `Rc`s). Named args are stored canonically (sorted by
/// symbol index) to match the `Value`/discrim-tree invariant. `span` (the
/// parent's) is reused for the synthesized cells.
pub fn build_occurrence_cons_list(
    kb: &KnowledgeBase,
    items: Vec<Rc<NodeOccurrence>>,
    span: SourceSpan,
    nil_sym: Symbol,
    cons_sym: Symbol,
    head_sym: Symbol,
    tail_sym: Symbol,
) -> Rc<NodeOccurrence> {
    // Nullary `nil` follows the Ref convention (bare `nil` loads as
    // `Term::Ref`), so build it as an `Expr::Ref` leaf — not a 0-ary
    // `Constructor` (which would read as a `Functor` and miss a `nil` pattern).
    let mut list = NodeOccurrence::new_expr(Expr::Ref(nil_sym), span, None);
    for item in items.into_iter().rev() {
        // Canonical (declared `cons(head, tail)`) field order — the
        // order-sensitive discrim matcher requires it to align with the loaded
        // pattern (not interning order). See `KnowledgeBase::sort_named_canonical`.
        let mut named = vec![(head_sym, item), (tail_sym, list)];
        kb.sort_named_canonical(cons_sym, &mut named);
        list = NodeOccurrence::new_expr(
            Expr::Constructor { name: cons_sym, pos_args: Vec::new(), named_args: named },
            span,
            None,
        );
    }
    list
}

fn occ_build_fn(
    kb: &mut KnowledgeBase,
    functor: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) -> TermId {
    let mut pos: smallvec::SmallVec<[TermId; 4]> = smallvec::SmallVec::new();
    for c in pos_args {
        pos.push(occurrence_to_term(kb, c));
    }
    let mut named: smallvec::SmallVec<[(Symbol, TermId); 2]> = smallvec::SmallVec::new();
    for (s, c) in named_args {
        named.push((*s, occurrence_to_term(kb, c)));
    }
    kb.alloc(Term::Fn { functor, pos_args: pos, named_args: named })
}

// ── WI-390: faithful Value/occurrence → Term lowering ───────────

/// A [`TypeChild`] → `TermId`: a ground child passes through verbatim, a
/// poisoned (`denoted`-bearing) child lowers via the now-lossless
/// [`occurrence_to_term`].
fn type_child_to_term(kb: &mut KnowledgeBase, child: &TypeChild) -> TermId {
    match child {
        TypeChild::Ground(t) => *t,
        TypeChild::Node(occ) => occurrence_to_term(kb, occ),
    }
}

/// WI-390: lower a `Type`-sort occurrence to its hash-consed term twin, mirroring
/// the `make_*_type` builders so a `value_to_term(occ)` is byte-identical to the
/// loader's ground build of the same type. Arrows reuse the *non*-canonicalizing
/// [`KnowledgeBase::make_arrow_from_effects_rows`] (the `effects` child is already
/// a canonical `effects_rows`; re-canonicalizing would change bytes).
fn type_node_to_term(kb: &mut KnowledgeBase, tn: &TypeNode) -> TermId {
    match tn {
        TypeNode::Denoted { value } => {
            let v = occurrence_to_term(kb, value);
            kb.make_denoted(v)
        }
        TypeNode::Parameterized { base, bindings } => {
            let base_t = type_child_to_term(kb, base);
            let mut binding_ts: Vec<(Symbol, TermId)> = Vec::with_capacity(bindings.len());
            for (s, c) in bindings {
                binding_ts.push((*s, type_child_to_term(kb, c)));
            }
            kb.make_parameterized_type(base_t, &binding_ts)
        }
        TypeNode::EffectsRows { effects_expr } => {
            let e = type_child_to_term(kb, effects_expr);
            kb.make_effects_rows_type(e)
        }
        TypeNode::Arrow { param, result, effects } => {
            let p = type_child_to_term(kb, param);
            let r = type_child_to_term(kb, result);
            let e = type_child_to_term(kb, effects);
            kb.make_arrow_from_effects_rows(p, r, e)
        }
        TypeNode::ExprCarried { value, member } => {
            // A compound-receiver projection is ELIMINATED to a concrete type before
            // term-lowering, so this faithful twin (mirroring the single-ref
            // `make_expr_carried`) is rarely hit; it keeps the lowering total. The
            // receiver lowers via the shared child path; `member` is a ground
            // `Ref(sym)` by construction.
            let v = type_child_to_term(kb, value);
            let member_sym = match member {
                TypeChild::Ground(t) => match kb.get_term(*t) {
                    Term::Ref(s) => Some(*s),
                    _ => None,
                },
                TypeChild::Node(_) => None,
            };
            match member_sym {
                Some(s) => kb.make_expr_carried(v, s),
                None => {
                    // Non-Ref member — unreachable via `make_expr_carried_occ` (always a
                    // ground `Ref`). Rebuild the `ExprCarried` Fn faithfully (mirroring
                    // `make_expr_carried`'s shape) rather than silently dropping the
                    // member projection to `v` (loud-over-silent).
                    let m = type_child_to_term(kb, member);
                    let ec = kb.resolve_symbol("anthill.prelude.TypeExtractor.ExprCarried");
                    let vk = kb.intern("value");
                    let mk = kb.intern("member");
                    let mut named: smallvec::SmallVec<[(Symbol, TermId); 2]> = smallvec::SmallVec::new();
                    named.push((vk, v));
                    named.push((mk, m));
                    // Canonicalize via the same funnel as `make_expr_carried` (WI-299) so this
                    // hand-built twin shares the declared-field-order layout — else the two
                    // would hash-cons to distinct `ExprCarried` TermIds for the same logical
                    // projection and the positional discrim matcher would silently miss.
                    kb.make_entity_term(ec, smallvec::SmallVec::new(), named)
                }
            }
        }
        TypeNode::NamedTuple { fields } => {
            // `fields` is a `Value`-carried `List[NamedTupleElement]` (structurally
            // the same list `make_named_tuple_type` builds), so lower it via
            // `value_to_term` and wrap in the `NamedTuple` functor. The `Err`
            // branch can't fire (a tuple field type is structure, never an opaque
            // handle); guard it loudly rather than silently dropping the fields.
            let fields_t = value_to_term(kb, fields).unwrap_or_else(|e| {
                debug_assert!(false, "named_tuple fields not term-representable: {e:?}");
                kb.alloc(Term::Bottom)
            });
            let nt_sym = kb.resolve_symbol("anthill.prelude.TypeExtractor.NamedTuple");
            let fields_key = kb.intern("fields");
            let mut named_args: smallvec::SmallVec<[(Symbol, TermId); 2]> = smallvec::SmallVec::new();
            named_args.push((fields_key, fields_t));
            kb.alloc(Term::Fn { functor: nt_sym, pos_args: smallvec::SmallVec::new(), named_args })
        }
    }
}

/// WI-390: lower an `EffectExpression`-sort occurrence to its term twin, mirroring
/// the `make_effect_expression_*` builders.
fn effect_node_to_term(kb: &mut KnowledgeBase, en: &EffectExprNode) -> TermId {
    match en {
        EffectExprNode::Merge { left, right } => {
            let l = type_child_to_term(kb, left);
            let r = type_child_to_term(kb, right);
            kb.make_effect_expression_merge(l, r)
        }
        EffectExprNode::Present { label } => {
            let l = type_child_to_term(kb, label);
            kb.make_effect_expression_present(l)
        }
        EffectExprNode::Guarded { label, guard } => {
            let l = type_child_to_term(kb, label);
            // `guard` is a `Value`-carried `List[reflect.Term]`; lower it via the
            // total `value_to_term` boundary (as `NamedTuple`'s `fields`). Goal
            // terms / occurrences are always term-representable, so the `Err`
            // branch is a loud guard, never a silent drop.
            let guard_t = value_to_term(kb, guard).unwrap_or_else(|e| {
                debug_assert!(false, "guarded guard not term-representable: {e:?}");
                kb.alloc(Term::Bottom)
            });
            kb.make_effect_expression_guarded(l, guard_t)
        }
        EffectExprNode::Absent { label } => {
            let l = type_child_to_term(kb, label);
            kb.make_effect_expression_absent(l)
        }
        EffectExprNode::Open { tail } => {
            let t = type_child_to_term(kb, tail);
            kb.make_effect_expression_open(t)
        }
        EffectExprNode::EmptyRow => kb.make_effect_expression_empty_row(),
    }
}

/// WI-390 — the faithful, total `Value → Term` boundary. `Ok(term)` for the
/// **structural subset**: a `Value::Node` lowers via the now-lossless
/// [`occurrence_to_term`] (so a denoted-bearing type round-trips), an `Entity`
/// recurses through `value_to_term` (a nested `Node` lowers, not errors), and the
/// scalar / `Term` / `Var` leaves reuse [`KnowledgeBase::alloc_from_value`].
/// `Err` for the opaque runtime handles (`Closure`/`Stream`/`Map`/`Cell`/
/// `Substitution`/`Requirement`) and the term-less `Unit`/`Tuple` — the honest
/// residue, never a panic or a lossy term. Unlike `alloc_from_value` (which
/// rejects *every* `Node`), this is `Node`-aware: it is the one converter to use
/// where a value-in-type may ride (e.g. a `requires`/`provides` spec).
pub fn value_to_term(
    kb: &mut KnowledgeBase,
    v: &Value,
) -> Result<TermId, crate::kb::execute::LowerError> {
    match v {
        // A value-in-type occurrence — lossless via occurrence_to_term (WI-390).
        Value::Node(occ) => Ok(occurrence_to_term(kb, occ)),
        // Recurse via value_to_term (NOT alloc_from_value) so a nested Node child
        // lowers faithfully instead of erroring. Canonical named-arg order mirrors
        // alloc_from_value (declared field order, else Symbol::index()).
        Value::Entity { functor, pos, named, .. } => {
            let mut pos_args: smallvec::SmallVec<[TermId; 4]> = smallvec::SmallVec::new();
            for p in pos.iter() {
                pos_args.push(value_to_term(kb, p)?);
            }
            let mut named_args: smallvec::SmallVec<[(Symbol, TermId); 2]> = smallvec::SmallVec::new();
            for (sym, nv) in named.iter() {
                named_args.push((*sym, value_to_term(kb, nv)?));
            }
            // WI-500: desugar positional → named (the shared rank-among-not-named
            // rule) BEFORE the canonical sort, so a positional entity lowers to the
            // SAME named shape the loader / discrim tree key on — mirrors
            // `alloc_from_value`.
            let named_syms: smallvec::SmallVec<[Symbol; 2]> =
                named_args.iter().map(|(s, _)| *s).collect();
            match kb.positional_to_named_plan(*functor, &named_syms, pos_args.len()) {
                crate::kb::resolve::PositionalPlan::Skip => {}
                crate::kb::resolve::PositionalPlan::Assign(fields) => {
                    for (i, pv) in std::mem::take(&mut pos_args).into_iter().enumerate() {
                        named_args.push((fields[i], pv));
                    }
                }
                crate::kb::resolve::PositionalPlan::OverArity { declared, unfilled } => {
                    return Err(crate::kb::execute::LowerError::OverArityConstructor {
                        functor: kb.resolve_sym(*functor).to_string(),
                        given: pos_args.len(),
                        unfilled,
                        declared: declared
                            .iter()
                            .map(|s| kb.resolve_sym(*s).to_string())
                            .collect::<Vec<_>>()
                            .join(", "),
                    });
                }
            }
            // Canonical named-arg order via the shared `sort_named_canonical` (the
            // single source of truth the discrim tree matches against) — declared
            // field order, else `Symbol::index()`.
            kb.sort_named_canonical(*functor, &mut named_args);
            Ok(kb.alloc(Term::Fn { functor: *functor, pos_args, named_args }))
        }
        // Scalars / Term / Var convert; opaque + Unit + Tuple error — identical to
        // alloc_from_value, and none of these carry a Node, so reuse it.
        other => kb.alloc_from_value(other),
    }
}

// ── Substitution over a rule-body-atom occurrence ───────────────

/// WI-246: apply a resolution substitution σ to a rule-body-atom occurrence
/// — the occurrence analog of `KnowledgeBase::apply_subst` over a
/// `Value::Node` goal. Walks the occurrence *template* (preserving its
/// structure, including any typer dot-rewrites) and replaces each **bound**
/// `Expr::Var(Var::Global)` leaf with its σ value; **unbound** var leaves are
/// kept verbatim, since the resolver binds them later (the opposite of the
/// `[simp]` RHS builder `substitute_to_occurrence`, which collapses unbound
/// vars to `⊥` under its all-vars-bound invariant). Unchanged subtrees keep
/// their `Rc` (only the ancestor chain to a substituted leaf is rebuilt).
///
/// A var bound to a matched child occurrence (`Value::Node`) is spliced in
/// place (identity preserved); a var bound to a compound term is materialized
/// via the var-preserving pair `apply_subst` + `materialize_from_handle` (so
/// nested unbound vars inside the bound value survive as `Expr::Var` too); a
/// scalar binding becomes a `Const`.
///
/// Like `open_debruijn_node`, the recursion depth is bounded by the atom's
/// (shallow) template structure — bound *values* are expanded by the
/// iterative `apply_subst`/`materialize_from_handle`, not by this recursion —
/// so the host stack stays flat. Forms that can't occur at a rule-body atom
/// position pass through unchanged.
/// WI-318: read a TermId in a lambda/let/match param/pattern position and
/// build the corresponding `Rc<NodeOccurrence>`. Two cases:
///
/// 1. **Structural pattern term** (`var_pattern` / `wildcard` /
///    `literal_pattern` / `constructor_pattern` / `tuple_pattern`) →
///    `NodeKind::Pattern(...)` mirroring the term's structure.
/// 2. **Logical variable** (`Term::Var`) — a *meta-variable* in a
///    reflection rule body atom like `lambda(param: ?x, body: ?b)`. The
///    `?x` here doesn't represent a pattern; it's bound at SLD time to
///    whatever pattern appears in the matched lambda. → `NodeKind::Expr`
///    with `Expr::Var(...)`, the same shape the rest of the rule-body
///    walkers expect.
///
/// Used at the loader / materializer build sites that feed a TermId
/// through `BuildFrame::Lambda` (etc.) and need to surface the
/// param/pattern as an `Rc<NodeOccurrence>` in the lifted
/// `Expr::Lambda.param` slot. The reverse of `pattern_to_term`.
///
/// `span` is propagated to the synthesized occurrence (no per-node
/// span tracking on the term side; caller supplies the parent span as
/// a coarse fallback). An unrecognized Fn functor falls back to
/// `Pattern::Wildcard` to avoid cascading panics.
pub fn term_to_param_occurrence(
    kb: &KnowledgeBase,
    tid: TermId,
    span: SourceSpan,
) -> Rc<NodeOccurrence> {
    use smallvec::SmallVec;
    let term = kb.get_term(tid).clone();
    // WI-511: a 0-ary pattern reflect constructor (only `wildcard`) is stored
    // in the canonical `Ref(c)` form after the alloc flip, so treat `Ref(c)` as
    // the nullary application `Fn{c,[],[]}` and dispatch on the functor exactly
    // like the `Fn` form. A `Ref` that is NOT a reflect pattern constructor
    // falls to the `_ =>` arm below (`term_pattern_as_expr_occ` → `Expr::Ref`),
    // identical to the old Expr-leaf behaviour.
    let (functor, named_args): (Symbol, SmallVec<[(Symbol, TermId); 2]>) = match &term {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        Term::Ref(s) => (*s, SmallVec::new()),
        // Logical Var in pattern position → reflection meta-var.
        Term::Var(v) => return NodeOccurrence::new_expr(Expr::Var(*v), span, None),
        // Other non-Fn/Ref terms (Const / Ident / Bottom) — surface
        // as an Expr leaf so the walkers stay uniform.
        Term::Const(lit) => return NodeOccurrence::new_expr(Expr::Const(lit.clone()), span, None),
        Term::Ident(s) => return NodeOccurrence::new_expr(Expr::Ident(*s), span, None),
        _ => return NodeOccurrence::new_expr(Expr::Bottom, span, None),
    };
    // WI-318: dispatch on QUALIFIED name (not short name) to avoid
    // collisions with user-defined entities whose short name happens to
    // be one of {var_pattern, wildcard, …}. This mirrors cpp-gen's
    // analyse_pattern_occ.
    let functor_qn = kb.qualified_name_of(functor);
    let pat = match functor_qn {
        "anthill.reflect.Pattern.var_pattern" => {
            // Grammar-emitted var_pattern always has a `name: Ref(sym)`.
            // Reflection rules can carry `var_pattern(name: ?x, …)` as
            // DATA — `?x` becomes a logical Var after rule encoding,
            // which doesn't fit the `name: Symbol` field. In that case
            // fall through to the Expr-kind term representation so
            // structural matchers see it as data.
            match extract_term_ref_sym(kb, &named_args, "name") {
                Some(name) => {
                    // WI-318: preserve `type_ann: some(t)` if present.
                    // The grammar's `pattern_var` doesn't surface a
                    // type annotation today (`type_ann: none()` from the
                    // loader), but proposal 035 and typing_pass_spec
                    // already reference annotated var_patterns. The
                    // value is wrapped in `some(value: <type>)` (the
                    // anthill.prelude.Option.some shape) by the loader.
                    let type_ann = extract_option_some_value(kb, &named_args, "type_ann")
                        .map(|t| term_to_expr_leaf_occ(kb, t, span));
                    Pattern::Var { name, type_ann }
                }
                None => return term_pattern_as_expr_occ(kb, tid, span),
            }
        }
        "anthill.reflect.Pattern.wildcard" => Pattern::Wildcard,
        "anthill.reflect.Pattern.literal_pattern" => {
            // CLAUDE.md: avoid silent fallbacks. If `value` isn't a
            // Term::Const (e.g. a logical Var via a reflection-data
            // synthesizer), surface the pattern as Expr instead of
            // silently coercing to `Literal::Int(0)`.
            match extract_literal_arg(kb, &named_args, "value") {
                Some(lit) => Pattern::Literal { value: lit },
                None => return term_pattern_as_expr_occ(kb, tid, span),
            }
        }
        "anthill.reflect.Pattern.constructor_pattern" => {
            match extract_term_ref_sym(kb, &named_args, "name") {
                Some(name) => {
                    let pos_args: Vec<Rc<NodeOccurrence>> = extract_named_list(kb, &named_args, "args")
                        .iter()
                        .map(|&t| term_to_param_occurrence(kb, t, span))
                        .collect();
                    // WI-445: named sub-patterns (`Box(v: some(x))`) ride a
                    // `named: List[NamedPattern]` field; surface each
                    // `(field, sub-pattern occurrence)` so the typer / eval
                    // bind them by field name.
                    let named_subs: Vec<(Symbol, Rc<NodeOccurrence>)> =
                        extract_named_list(kb, &named_args, "named")
                            .iter()
                            .filter_map(|&np| read_named_pattern_term(kb, np))
                            .map(|(field, sub)| (field, term_to_param_occurrence(kb, sub, span)))
                            .collect();
                    Pattern::Constructor { name, pos_args, named_args: named_subs }
                }
                None => return term_pattern_as_expr_occ(kb, tid, span),
            }
        }
        "anthill.reflect.Pattern.tuple_pattern" => {
            let positional: Vec<Rc<NodeOccurrence>> = extract_named_list(kb, &named_args, "elements")
                .iter()
                .map(|&t| term_to_param_occurrence(kb, t, span))
                .collect();
            Pattern::Tuple { positional, named: Vec::new() }
        }
        _ => {
            // Unknown functor in a pattern slot: surface as Expr-kind so
            // downstream walkers see the term shape as data, rather
            // than silently coercing to Pattern::Wildcard (which would
            // make any match unconditionally succeed). The reflection-
            // meta-var path also takes this fall-through.
            return term_pattern_as_expr_occ(kb, tid, span);
        }
    };
    NodeOccurrence::new_pattern(pat, span, None)
}

/// WI-318: read `field: some(value: t)` from `named_args` and return
/// `Some(t)`; return `None` for `none()` or a missing field. Mirrors
/// the `Option` cons-list shape the loader emits (load.rs::build_some
/// / build_none).
fn extract_option_some_value(
    kb: &KnowledgeBase,
    named_args: &[(Symbol, TermId)],
    field: &str,
) -> Option<TermId> {
    let (_, tid) = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == field)?;
    match kb.get_term(*tid) {
        Term::Fn { functor, named_args: inner, .. } => {
            // `some(value: t)` — Option.some has qualified name
            // anthill.prelude.Option.some.
            let qn = kb.qualified_name_of(*functor);
            if qn != "anthill.prelude.Option.some" {
                return None;
            }
            inner.iter()
                .find(|(s, _)| kb.resolve_sym(*s) == "value")
                .map(|(_, t)| *t)
        }
        _ => None,
    }
}

/// WI-318: build an Expr-kind leaf occurrence for a `TermId` that names
/// a type / value expression (typically a type position). Used by the
/// Pattern::Var.type_ann surfacer — type expressions go through the
/// same surface as the rest of the rule body. Compound types (Fn)
/// surface as `Expr::Apply` (the parameterised/named/sort-ref shapes
/// the typer reads as terms-as-types).
fn term_to_expr_leaf_occ(
    kb: &KnowledgeBase,
    tid: TermId,
    span: SourceSpan,
) -> Rc<NodeOccurrence> {
    match kb.get_term(tid).clone() {
        Term::Var(v) => NodeOccurrence::new_expr(Expr::Var(v), span, None),
        Term::Const(lit) => NodeOccurrence::new_expr(Expr::Const(lit), span, None),
        Term::Ref(s) => NodeOccurrence::new_expr(Expr::Ref(s), span, None),
        Term::Ident(s) => NodeOccurrence::new_expr(Expr::Ident(s), span, None),
        Term::Fn { functor, pos_args, named_args } => {
            // Surface a type-position Fn as an Expr::Apply with NO
            // type_args (these are types-as-terms; the args are the
            // type's structural components). Children pass through
            // `term_to_expr_leaf_occ` so a nested Var is preserved as
            // an Expr::Var occurrence.
            let pos: Vec<Rc<NodeOccurrence>> = pos_args
                .iter()
                .map(|&t| term_to_expr_leaf_occ(kb, t, span))
                .collect();
            let named: Vec<(Symbol, Rc<NodeOccurrence>)> = named_args
                .iter()
                .map(|&(s, t)| (s, term_to_expr_leaf_occ(kb, t, span)))
                .collect();
            NodeOccurrence::new_expr(
                Expr::Apply { functor, pos_args: pos, named_args: named, type_args: Vec::new() },
                span,
                None,
            )
        }
        _ => NodeOccurrence::new_expr(Expr::Bottom, span, None),
    }
}

/// WI-318: fall-back surfacer for a "pattern term whose ground structure
/// can't be captured by the `Pattern` enum" — typically a reflection
/// rule's `var_pattern(name: ?x, …)` where the name is a logical Var.
/// Surface as an `Expr::Apply` over the children so structural matchers
/// see it as data. Children are recursively projected: nested
/// var_pattern / constructor_pattern / tuple_pattern keep the
/// Pattern-or-Expr decision per-node, so a ground sub-pattern still
/// becomes Pattern-kind and only the non-ground spine stays Expr.
fn term_pattern_as_expr_occ(
    kb: &KnowledgeBase,
    tid: TermId,
    span: SourceSpan,
) -> Rc<NodeOccurrence> {
    match kb.get_term(tid).clone() {
        Term::Fn { functor, pos_args, named_args } => {
            let pos: Vec<Rc<NodeOccurrence>> = pos_args
                .iter()
                .map(|&t| term_pattern_child_as_occ(kb, t, span))
                .collect();
            let named: Vec<(Symbol, Rc<NodeOccurrence>)> = named_args
                .iter()
                .map(|&(s, t)| (s, term_pattern_child_as_occ(kb, t, span)))
                .collect();
            NodeOccurrence::new_expr(
                Expr::Apply { functor, pos_args: pos, named_args: named, type_args: Vec::new() },
                span,
                None,
            )
        }
        Term::Var(v) => NodeOccurrence::new_expr(Expr::Var(v), span, None),
        Term::Const(lit) => NodeOccurrence::new_expr(Expr::Const(lit), span, None),
        Term::Ref(s) => NodeOccurrence::new_expr(Expr::Ref(s), span, None),
        Term::Ident(s) => NodeOccurrence::new_expr(Expr::Ident(s), span, None),
        _ => NodeOccurrence::new_expr(Expr::Bottom, span, None),
    }
}

/// Per-child projection inside a non-ground pattern term (see
/// `term_pattern_as_expr_occ`): a child that's itself a recognised
/// pattern term goes back through `term_to_param_occurrence` (so a
/// ground sub-pattern surfaces as Pattern-kind); otherwise it's lifted
/// to an Expr leaf so structural matchers see the right shape.
fn term_pattern_child_as_occ(
    kb: &KnowledgeBase,
    tid: TermId,
    span: SourceSpan,
) -> Rc<NodeOccurrence> {
    match kb.get_term(tid) {
        Term::Fn { functor, .. } => {
            let name = kb.resolve_sym(*functor);
            if matches!(
                name,
                "var_pattern" | "wildcard" | "literal_pattern"
                    | "constructor_pattern" | "tuple_pattern"
            ) {
                return term_to_param_occurrence(kb, tid, span);
            }
            term_pattern_as_expr_occ(kb, tid, span)
        }
        Term::Var(v) => NodeOccurrence::new_expr(Expr::Var(*v), span, None),
        Term::Const(lit) => NodeOccurrence::new_expr(Expr::Const(lit.clone()), span, None),
        // WI-511: the nullary `wildcard` pattern is the canonical `Ref(wildcard)`;
        // route it through `term_to_param_occurrence` so it surfaces as
        // Pattern::Wildcard, not an `Expr::Ref` data leaf.
        Term::Ref(s) if kb.resolve_sym(*s) == "wildcard" => {
            term_to_param_occurrence(kb, tid, span)
        }
        Term::Ref(s) => NodeOccurrence::new_expr(Expr::Ref(*s), span, None),
        Term::Ident(s) => NodeOccurrence::new_expr(Expr::Ident(*s), span, None),
        _ => NodeOccurrence::new_expr(Expr::Bottom, span, None),
    }
}

/// WI-445: build a reflect `NamedPattern(name: Ref(field), pattern: sub)` term
/// — the element shape of a constructor pattern's `named` list. The single
/// source of truth for that shape, shared by the loader
/// (`LoadBuildFrame::PatternConstructor`) and [`pattern_to_term`] so the
/// occurrence↔term round-trip cannot drift. Read back with
/// [`read_named_pattern_term`].
pub(crate) fn build_named_pattern_term(
    kb: &mut KnowledgeBase,
    field: Symbol,
    sub_pattern: TermId,
) -> TermId {
    use smallvec::SmallVec;
    let np_functor = kb.resolve_symbol("anthill.reflect.NamedPattern");
    let name_key = kb.intern("name");
    let pattern_key = kb.intern("pattern");
    let field_ref = kb.alloc(Term::Ref(field));
    kb.alloc(Term::Fn {
        functor: np_functor,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(name_key, field_ref), (pattern_key, sub_pattern)]),
    })
}

/// WI-445: read a reflect `NamedPattern(name: Ref(field), pattern: sub)` term
/// into `(field_symbol, sub_pattern_term)`. The element shape of a constructor
/// pattern's `named` list. Returns `None` for a malformed element. Shared by
/// the typer (`extend_env_from_pattern`) and eval (`match_constructor_pattern`).
pub(crate) fn read_named_pattern_term(kb: &KnowledgeBase, tid: TermId) -> Option<(Symbol, TermId)> {
    let Term::Fn { named_args, .. } = kb.get_term(tid) else { return None; };
    let field = extract_term_ref_sym(kb, named_args, "name")?;
    let pat = named_args
        .iter()
        .find(|(s, _)| kb.resolve_sym(*s) == "pattern")
        .map(|(_, t)| *t)?;
    Some((field, pat))
}

fn extract_term_ref_sym(
    kb: &KnowledgeBase,
    named_args: &[(Symbol, TermId)],
    field: &str,
) -> Option<Symbol> {
    let (_, tid) = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == field)?;
    match kb.get_term(*tid) {
        Term::Ref(s) => Some(*s),
        Term::Ident(s) => Some(*s),
        _ => None,
    }
}
fn extract_literal_arg(
    kb: &KnowledgeBase,
    named_args: &[(Symbol, TermId)],
    field: &str,
) -> Option<Literal> {
    let (_, tid) = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == field)?;
    match kb.get_term(*tid) {
        Term::Const(lit) => Some(lit.clone()),
        _ => None,
    }
}
fn extract_named_list(
    kb: &KnowledgeBase,
    named_args: &[(Symbol, TermId)],
    field: &str,
) -> Vec<TermId> {
    let Some((_, tid)) = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == field) else {
        return Vec::new();
    };
    list_to_vec(kb, *tid)
}

/// WI-318: convert a Pattern-kind occurrence back to the reflect-Term
/// shape (`var_pattern` / `wildcard` / `literal_pattern` /
/// `constructor_pattern` / `tuple_pattern`) that the loader used to
/// store before the lift. A bridge for consumers (typer's
/// `extend_env_from_pattern` / `extract_pattern_type_ann`, the printer,
/// reflection) that still operate on the term form. Each pattern
/// child is recursively converted (they too are Pattern-kind), so a
/// nested constructor pattern lowers to a cons-list of converted
/// children — byte-identical to what `load_pattern_*` produced.
///
/// Panics (debug) if `occ` isn't a Pattern-kind occurrence.
pub fn pattern_to_term(kb: &mut KnowledgeBase, occ: &Rc<NodeOccurrence>) -> TermId {
    let pat = match &occ.kind {
        NodeKind::Pattern(p) => p,
        // WI-318: `term_to_param_occurrence` legitimately surfaces Expr-
        // kind occurrences for reflection meta-vars (a `lambda(param:
        // ?x, …)` body atom has param kind Expr::Var, not Pattern).
        // Reify those back via `occurrence_to_term` instead of
        // returning Bottom — Bottom would silently make match_pattern /
        // extend_env_from_pattern no-op without a diagnostic.
        NodeKind::Expr { .. } => return occurrence_to_term(kb, occ),
        // RuleHead in a pattern slot is genuinely unreachable — bodies
        // are GOAL positions, never RuleHead. Surface as Bottom + assert
        // for the caller (only fires in debug).
        NodeKind::RuleHead { .. } => {
            debug_assert!(false, "pattern_to_term: RuleHead in pattern slot");
            return kb.alloc(Term::Bottom);
        }
        // WI-342: a Type/EffectExpr occurrence in a pattern slot is
        // unreachable (patterns never carry types). Mirror RuleHead.
        NodeKind::Type(_) | NodeKind::EffectExpr(_) => {
            debug_assert!(false, "pattern_to_term: Type/EffectExpr in pattern slot");
            return kb.alloc(Term::Bottom);
        }
    };
    use smallvec::SmallVec;
    let name_key = kb.intern("name");
    let type_ann_key = kb.intern("type_ann");
    let args_key = kb.intern("args");
    let value_key = kb.intern("value");
    let elements_key = kb.intern("elements");
    match pat {
        Pattern::Var { name, type_ann } => {
            let name_ref = kb.alloc(Term::Ref(*name));
            let type_ann_tid = match type_ann {
                Some(t) => {
                    let inner = occurrence_to_term(kb, t);
                    build_some(kb, inner)
                }
                None => build_none(kb),
            };
            let functor = kb.resolve_symbol("anthill.reflect.Pattern.var_pattern");
            kb.alloc(Term::Fn {
                functor,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[(name_key, name_ref), (type_ann_key, type_ann_tid)]),
            })
        }
        Pattern::Wildcard => {
            let functor = kb.resolve_symbol("anthill.reflect.Pattern.wildcard");
            kb.alloc(Term::Fn { functor, pos_args: SmallVec::new(), named_args: SmallVec::new() })
        }
        Pattern::Literal { value } => {
            let value_tid = kb.alloc(Term::Const(value.clone()));
            let functor = kb.resolve_symbol("anthill.reflect.Pattern.literal_pattern");
            kb.alloc(Term::Fn {
                functor,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[(value_key, value_tid)]),
            })
        }
        Pattern::Constructor { name, pos_args, named_args } => {
            // Constructor patterns canonically lower to
            // `constructor_pattern(name: Ref, args: List[Pattern])`, plus a
            // `named: List[NamedPattern]` (WI-445) for `Foo(field: pat)`
            // sub-patterns — the inverse of `term_to_param_occurrence`. The
            // `named` key is omitted when empty, keeping the positional form
            // byte-identical.
            let name_ref = kb.alloc(Term::Ref(*name));
            let args: Vec<TermId> = pos_args
                .iter()
                .map(|c| pattern_to_term(kb, c))
                .collect();
            let args_list = build_list_termid(kb, &args);
            let functor = kb.resolve_symbol("anthill.reflect.Pattern.constructor_pattern");
            let mut na: SmallVec<[(Symbol, TermId); 2]> =
                SmallVec::from_slice(&[(name_key, name_ref), (args_key, args_list)]);
            if !named_args.is_empty() {
                let named_key = kb.intern("named");
                let elems: Vec<TermId> = named_args
                    .iter()
                    .map(|(field, sub)| {
                        let sub_term = pattern_to_term(kb, sub);
                        build_named_pattern_term(kb, *field, sub_term)
                    })
                    .collect();
                let named_list = build_list_termid(kb, &elems);
                na.push((named_key, named_list));
            }
            kb.alloc(Term::Fn { functor, pos_args: SmallVec::new(), named_args: na })
        }
        Pattern::Tuple { positional, .. } => {
            // Tuple patterns lower to `tuple_pattern(elements: List[...])`.
            let elements: Vec<TermId> = positional
                .iter()
                .map(|c| pattern_to_term(kb, c))
                .collect();
            let elements_list = build_list_termid(kb, &elements);
            let functor = kb.resolve_symbol("anthill.reflect.Pattern.tuple_pattern");
            kb.alloc(Term::Fn {
                functor,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[(elements_key, elements_list)]),
            })
        }
    }
}

/// Internal helper: build a cons-list TermId from a slice of element
/// TermIds (mirror of `load.rs::build_list` over the same `cons`/`nil`
/// shape).
fn build_list_termid(kb: &mut KnowledgeBase, items: &[TermId]) -> TermId {
    use smallvec::SmallVec;
    let nil_sym = kb.resolve_symbol("anthill.prelude.List.nil");
    let cons_sym = kb.resolve_symbol("anthill.prelude.List.cons");
    let head_key = kb.intern("head");
    let tail_key = kb.intern("tail");
    let mut acc = kb.alloc(Term::Fn {
        functor: nil_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    for &item in items.iter().rev() {
        acc = kb.alloc(Term::Fn {
            functor: cons_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(head_key, item), (tail_key, acc)]),
        });
    }
    acc
}

/// Internal helper: build `anthill.prelude.Option.some(value: t)` / `none()`.
fn build_some(kb: &mut KnowledgeBase, t: TermId) -> TermId {
    use smallvec::SmallVec;
    let some_sym = kb.resolve_symbol("anthill.prelude.Option.some");
    let value_key = kb.intern("value");
    kb.alloc(Term::Fn {
        functor: some_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(value_key, t)]),
    })
}
fn build_none(kb: &mut KnowledgeBase) -> TermId {
    use smallvec::SmallVec;
    let none_sym = kb.resolve_symbol("anthill.prelude.Option.none");
    kb.alloc(Term::Fn {
        functor: none_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    })
}

pub fn substitute_occurrence(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    subst: &Substitution,
) -> Rc<NodeOccurrence> {
    // WI-318: walk through Pattern-kind occurrences uniformly — their
    // structure has no `Expr::Var` leaves to bind (names are Symbols),
    // but their Expr-kind type_ann children CAN hold a `Var::Global`
    // that the substitution should rewrite. Mirror of the
    // `open_debruijn_node` Pattern arm.
    if let Some(pat) = occ.as_pattern() {
        let mut subst_children: Vec<Rc<NodeOccurrence>> = Vec::new();
        for_each_pattern_child(pat, |c| subst_children.push(substitute_occurrence(kb, c, subst)));
        return reassemble_pattern(occ, &subst_children);
    }
    // WI-378 step 2 / WI-342-P3: apply σ inside a Type/EffectExpr occurrence's
    // spine (a Global in a ground `TermId` child via `apply_subst`, child
    // occurrences by recursion) — symmetric with the De Bruijn rewriters.
    if matches!(occ.kind, NodeKind::Type(_) | NodeKind::EffectExpr(_)) {
        return rewrite_type_occurrence(&SubstTypeRewrite { subst }, kb, occ)
            .unwrap_or_else(|| Rc::clone(occ));
    }
    let Some(expr) = occ.as_expr() else { return Rc::clone(occ) };
    let rebuilt: Option<Rc<NodeOccurrence>> = match expr {
        Expr::Var(Var::Global(vid)) => return subst_var_leaf(kb, *vid, subst, occ),
        // WI-298: Apply.type_args is a TermId field — apply σ to it via
        // `apply_subst` so a Global appearing in a type argument gets the same
        // rewrite as elsewhere, mirroring the opener's `open_type_args` arm.
        Expr::Apply { functor, pos_args, named_args, type_args } => {
            let (pos, c1) = subst_vec(kb, pos_args, subst);
            let (named, c2) = subst_named(kb, named_args, subst);
            let (ta, c3) = subst_type_args(kb, type_args, subst);
            (c1 || c2 || c3).then(|| {
                NodeOccurrence::new_expr(
                    Expr::Apply {
                        functor: *functor,
                        pos_args: pos,
                        named_args: named,
                        type_args: ta,
                    },
                    occ.span,
                    occ.owner,
                )
            })
        }
        Expr::Constructor { name, pos_args, named_args } => {
            let (pos, c1) = subst_vec(kb, pos_args, subst);
            let (named, c2) = subst_named(kb, named_args, subst);
            (c1 || c2).then(|| {
                NodeOccurrence::new_expr(
                    Expr::Constructor { name: *name, pos_args: pos, named_args: named },
                    occ.span,
                    occ.owner,
                )
            })
        }
        Expr::Instantiation { name, pos_args, named_args } => {
            let (pos, c1) = subst_vec(kb, pos_args, subst);
            let (named, c2) = subst_named(kb, named_args, subst);
            (c1 || c2).then(|| {
                NodeOccurrence::new_expr(
                    Expr::Instantiation { name: *name, pos_args: pos, named_args: named },
                    occ.span,
                    occ.owner,
                )
            })
        }
        Expr::HoApply { predicate, args } => {
            let p = substitute_occurrence(kb, predicate, subst);
            let (a, c2) = subst_vec(kb, args, subst);
            let c1 = !Rc::ptr_eq(&p, predicate);
            (c1 || c2).then(|| {
                NodeOccurrence::new_expr(Expr::HoApply { predicate: p, args: a }, occ.span, occ.owner)
            })
        }
        // WI-298: Let.type_annotation is a TermId — apply σ to it via
        // `apply_subst` alongside the occurrence children, mirroring the
        // opener's explicit Let arm. The generic fall-through below would
        // leave it un-substituted because `for_each_child` skips TermId
        // fields.
        Expr::Let { pattern, type_annotation, value, body } => {
            let new_pattern = substitute_occurrence(kb, pattern, subst);
            let new_value = substitute_occurrence(kb, value, subst);
            let new_body = substitute_occurrence(kb, body, subst);
            let (new_ta, ta_changed) = subst_option_value(kb, type_annotation, subst);
            let c1 = !Rc::ptr_eq(&new_pattern, pattern);
            let c2 = !Rc::ptr_eq(&new_value, value);
            let c3 = !Rc::ptr_eq(&new_body, body);
            (c1 || c2 || c3 || ta_changed).then(|| {
                NodeOccurrence::new_expr(
                    Expr::Let {
                        pattern: new_pattern,
                        type_annotation: new_ta,
                        value: new_value,
                        body: new_body,
                    },
                    occ.span,
                    occ.owner,
                )
            })
        }
        // WI-298: ApplyWithin.type_args mirrors Apply.type_args. The generic
        // fall-through would leave them un-substituted; explicit arm closes
        // that gap, parallel to the opener.
        Expr::ApplyWithin { functor, args, named_args, requirements, type_args } => {
            let (a, c1) = subst_vec(kb, args, subst);
            let (named, c2) = subst_named(kb, named_args, subst);
            let (reqs, c3) = subst_vec(kb, requirements, subst);
            let (ta, c4) = subst_type_args(kb, type_args, subst);
            (c1 || c2 || c3 || c4).then(|| {
                NodeOccurrence::new_expr(
                    Expr::ApplyWithin {
                        functor: *functor,
                        args: a,
                        named_args: named,
                        requirements: reqs,
                        type_args: ta,
                    },
                    occ.span,
                    occ.owner,
                )
            })
        }
        // WI-296: a *child-bearing* control-flow / post-elaboration form CAN
        // occur at a rule-body atom position — reflection / typing rules match
        // expression structure as data (e.g. `occurrence_term(?e, lambda(...))`).
        // Substitute into each child (in `for_each_child` source order) and
        // reassemble, mirroring `open_debruijn_node`. Genuine leaves enumerate
        // no children, so `reassemble` returns `occ` unchanged.
        _ => {
            let mut subst_children: Vec<Rc<NodeOccurrence>> = Vec::new();
            for_each_child(expr, |c| subst_children.push(substitute_occurrence(kb, c, subst)));
            return super::simp_rewrite::reassemble(occ, &subst_children);
        }
    };
    // WI-502 Step 3: the explicit arms above build the rebuilt node via
    // `new_expr` (which resets `inferred_type` to `None`); carry `occ`'s stamped
    // type onto it here, in one place. (The `_` arm already returned via
    // `reassemble`, which carries the type itself.) Verbatim carry is sound for
    // `min_sort`'s head-only read — see `NodeOccurrence::rebuilt_expr`.
    rebuilt
        .map(|n| {
            if let Some(ty) = occ.inferred_type() {
                n.set_inferred_type(ty);
            }
            n
        })
        .unwrap_or_else(|| Rc::clone(occ))
}

/// WI-342 E2 — rewrite `Expr::Ref(s)` leaves to `Expr::Ref(map[s])` inside a
/// `Value`-carried `Type` / `EffectExpression` effect-label occurrence. The
/// occurrence analog of `typing::substitute_ref_syms`: re-keys a callee's
/// `Modify[c]` to the caller's `Modify[s]` (call-site param substitution) and a
/// fresh result-region to the enclosing op's `result` (region escape). Only the
/// spines an effect label takes are walked (`denoted` / `parameterized` /
/// `effects_rows` / `arrow` + the row algebra); a `Ground` `TypeChild` carries no
/// occurrence `Ref` (its hash-consed `Term::Ref`s are re-keyed by the term-world
/// `substitute_ref_syms`), so it passes through. A non-`Type`/`EffectExpr`
/// occurrence is never an effect label and is returned unchanged.
pub(crate) fn substitute_ref_syms_occ(
    occ: &Rc<NodeOccurrence>,
    map: &std::collections::HashMap<Symbol, Symbol>,
) -> Rc<NodeOccurrence> {
    match &occ.kind {
        NodeKind::Type(tn) => {
            let rebuilt = match tn {
                TypeNode::Denoted { value } => TypeNode::Denoted {
                    value: rewrite_ref_expr(value, map),
                },
                TypeNode::Parameterized { base, bindings } => TypeNode::Parameterized {
                    base: rewrite_ref_child(base, map),
                    bindings: bindings
                        .iter()
                        .map(|(s, c)| (*s, rewrite_ref_child(c, map)))
                        .collect(),
                },
                TypeNode::EffectsRows { effects_expr } => TypeNode::EffectsRows {
                    effects_expr: rewrite_ref_child(effects_expr, map),
                },
                TypeNode::Arrow { param, result, effects } => TypeNode::Arrow {
                    param: rewrite_ref_child(param, map),
                    result: rewrite_ref_child(result, map),
                    effects: rewrite_ref_child(effects, map),
                },
                TypeNode::NamedTuple { fields } => TypeNode::NamedTuple {
                    fields: rewrite_ref_value(fields, map),
                },
                TypeNode::ExprCarried { value, member } => TypeNode::ExprCarried {
                    value: rewrite_ref_child(value, map),
                    member: rewrite_ref_child(member, map),
                },
            };
            NodeOccurrence::new_type(rebuilt, occ.span, occ.owner)
        }
        NodeKind::EffectExpr(en) => {
            let rebuilt = match en {
                EffectExprNode::Merge { left, right } => EffectExprNode::Merge {
                    left: rewrite_ref_child(left, map),
                    right: rewrite_ref_child(right, map),
                },
                EffectExprNode::Present { label } => EffectExprNode::Present {
                    label: rewrite_ref_child(label, map),
                },
                EffectExprNode::Guarded { label, guard } => EffectExprNode::Guarded {
                    label: rewrite_ref_child(label, map),
                    guard: rewrite_ref_value(guard, map),
                },
                EffectExprNode::Absent { label } => EffectExprNode::Absent {
                    label: rewrite_ref_child(label, map),
                },
                EffectExprNode::Open { tail } => EffectExprNode::Open {
                    tail: rewrite_ref_child(tail, map),
                },
                EffectExprNode::EmptyRow => EffectExprNode::EmptyRow,
            };
            NodeOccurrence::new_effect_expr(rebuilt, occ.span, occ.owner)
        }
        _ => Rc::clone(occ),
    }
}

/// Re-key Refs inside a [`TypeChild`]. `Ground` is hash-consed `Term` (re-keyed,
/// if ever needed, by the term-world `substitute_ref_syms`); `Node` recurses.
fn rewrite_ref_child(
    child: &TypeChild,
    map: &std::collections::HashMap<Symbol, Symbol>,
) -> TypeChild {
    match child {
        TypeChild::Ground(t) => TypeChild::Ground(*t),
        TypeChild::Node(n) => TypeChild::Node(substitute_ref_syms_occ(n, map)),
    }
}

/// WI-361: re-key `Ref` symbols inside a `Value`-carried child (a `named_tuple`'s
/// `fields` `List[TypeField]`), mirroring [`rewrite_ref_child`]: a ground
/// `Value::Term` passes through (a hash-consed `Term` carries no renamable
/// occurrence ref), a poisoned `Value::Node` re-keys via [`substitute_ref_syms_occ`],
/// and a `Value::Entity`/`Tuple` rebuilds with its children rewritten. Scalars /
/// other carriers pass through unchanged.
fn rewrite_ref_value(value: &Value, map: &std::collections::HashMap<Symbol, Symbol>) -> Value {
    match value {
        Value::Node(occ) => Value::Node(substitute_ref_syms_occ(occ, map)),
        Value::Entity { functor, pos, named, .. } => Value::Entity {
            functor: *functor,
            pos: pos.iter().map(|v| rewrite_ref_value(v, map)).collect(),
            named: named.iter().map(|(s, v)| (*s, rewrite_ref_value(v, map))).collect(),
            ty: None,
        },
        Value::Tuple { pos, named, .. } => Value::Tuple {
            pos: pos.iter().map(|v| rewrite_ref_value(v, map)).collect(),
            named: named.iter().map(|(s, v)| (*s, rewrite_ref_value(v, map))).collect(),
            ty: None,
        },
        other => other.clone(),
    }
}

/// Re-key a `denoted`'s carried value. A single `Expr::Ref(s)` (`Modify[c]`) is
/// the common shape; WI-302 also mints a `DotApply` FIELD-PATH chain
/// (`Modify[c.contents]` / `Modify[result.a]`, proposal 027.1), whose head value
/// `Ref` must be re-keyed exactly like the single-`Ref` case — the field segments
/// are not values to re-map. So recurse the receiver spine and re-key its head;
/// the field names pass through. A richer carried value (bound-name reference,
/// nested NON-field apply) still needs alpha-aware rewrite — deferred with the
/// same TODO as `unify_denoted_view`; it passes through unchanged.
fn rewrite_ref_expr(
    occ: &Rc<NodeOccurrence>,
    map: &std::collections::HashMap<Symbol, Symbol>,
) -> Rc<NodeOccurrence> {
    match &occ.kind {
        NodeKind::Expr { expr: Expr::Ref(s), .. } => {
            if let Some(&new_sym) = map.get(s) {
                return NodeOccurrence::new_expr(Expr::Ref(new_sym), occ.span, occ.owner);
            }
        }
        // WI-302: a value field-access path (`c.contents`) — re-key the receiver's
        // head `Ref` (the value being substituted at the call site); a field access
        // carries no call args.
        NodeKind::Expr {
            expr: Expr::DotApply { receiver, name, pos_args, named_args },
            ..
        } if pos_args.is_empty() && named_args.is_empty() => {
            let new_recv = rewrite_ref_expr(receiver, map);
            if !Rc::ptr_eq(&new_recv, receiver) {
                return NodeOccurrence::new_expr(
                    Expr::DotApply {
                        receiver: new_recv,
                        name: *name,
                        pos_args: Vec::new(),
                        named_args: Vec::new(),
                    },
                    occ.span,
                    occ.owner,
                );
            }
        }
        _ => {}
    }
    Rc::clone(occ)
}

/// WI-298/WI-342 S4b: apply σ to a call site's `type_args` (`(name?,
/// type-Value)` pairs) via the carrier-agnostic `subst_value_type` — the
/// substitution twin of `open_type_args` / `close_type_args`. A ground
/// `Value::Term` is rewritten via `apply_subst`; a `Value::Node` type carries
/// no σ-substitutable vars, so it passes through unchanged.
fn subst_type_args(
    kb: &mut KnowledgeBase,
    items: &[(Option<Symbol>, Value)],
    subst: &Substitution,
) -> (Vec<(Option<Symbol>, Value)>, bool) {
    let mut changed = false;
    let mut out = Vec::with_capacity(items.len());
    for (name, v) in items {
        let (nv, ch) = subst_value_type(kb, v, subst);
        changed |= ch;
        out.push((*name, nv));
    }
    (out, changed)
}

/// WI-342/WI-378: apply σ to the vars of a carrier-agnostic type `Value` — a thin
/// delegate to the shared [`map_value_type`] (a `Value::Node` descends the type
/// spine; a `NamedTuple.fields` cons-list recurses), the σ twin of
/// `close_value_type` / `open_value_type`.
fn subst_value_type(kb: &mut KnowledgeBase, v: &Value, subst: &Substitution) -> (Value, bool) {
    map_value_type(&SubstTypeRewrite { subst }, kb, v)
}

/// WI-298/WI-342: apply σ to an `Option<Value>` type field (today only
/// `Let.type_annotation`) — the substitution twin of `open_option_value` /
/// `close_option_value`.
fn subst_option_value(
    kb: &mut KnowledgeBase,
    item: &Option<Value>,
    subst: &Substitution,
) -> (Option<Value>, bool) {
    match item {
        Some(v) => {
            let (nv, changed) = subst_value_type(kb, v, subst);
            (Some(nv), changed)
        }
        None => (None, false),
    }
}

/// Resolve a `Expr::Var(Global)` leaf against σ. `None` ⇒ unbound, keep the
/// leaf (returned as a clone of the original `occ`). See
/// [`substitute_occurrence`] for the binding-case semantics.
fn subst_var_leaf(
    kb: &mut KnowledgeBase,
    vid: VarId,
    subst: &Substitution,
    occ: &Rc<NodeOccurrence>,
) -> Rc<NodeOccurrence> {
    // `TermId` is `Copy`, so binding `*t` ends the immutable borrow of `subst`
    // at the match, freeing the `&mut kb` call below.
    let t = match subst.resolve_as_value(vid) {
        None => return Rc::clone(occ), // unbound: keep the variable leaf
        Some(Value::Node(o)) => return Rc::clone(o), // matched child: splice in place
        Some(Value::Term { id: t, .. }) => *t,
        Some(scalar) => match scalar_value_expr(scalar) {
            Some(expr) => return NodeOccurrence::new_expr(expr, occ.span, occ.owner),
            // Structured non-`Term` values (`Value::Entity`/`Tuple` from
            // external rows) aren't materialized to occurrences yet — that
            // path lands when the resolver's external-row binding is wired.
            // Fail loud rather than silently produce ⊥ (which would discard a
            // genuine binding); the gate's relational rules bind only
            // term-shaped values, so this is unreachable today.
            None => panic!(
                "substitute_occurrence: goal var bound to non-scalar Value ({}) — \
                 occurrence materialization for external-row bindings is not yet \
                 implemented (WI-246)",
                scalar.type_name(),
            ),
        },
    };
    // Bound to a (possibly compound) term: deep-apply σ in term-land (keeps
    // nested unbound vars as `Term::Var`), then materialize to an occurrence
    // (keeps them as `Expr::Var`).
    let applied = kb.apply_subst(t, subst);
    materialize_from_handle(kb, applied)
}

/// Map a *scalar* `Value` to its `Expr::Const` leaf — shared with
/// `simp_rewrite::subst_visit`. Returns `None` for non-scalar values
/// (`Node`/`Term` are handled by callers; structured/opaque values have no
/// `Const` form), letting each caller choose its own non-scalar policy.
pub(super) fn scalar_value_expr(v: &Value) -> Option<Expr> {
    Some(match v {
        Value::Int(n) => Expr::Const(Literal::Int(*n)),
        Value::BigInt(n) => Expr::Const(Literal::BigInt(n.clone())),
        Value::Float(f) => Expr::Const(Literal::Float(ordered_float::OrderedFloat(*f))),
        Value::Bool(b) => Expr::Const(Literal::Bool(*b)),
        Value::Str(s) => Expr::Const(Literal::String(s.clone())),
        // WI-109: a value-level logic variable has a direct `Expr::Var` leaf
        // — so an occurrence var bound to a `Value::Var` reconstructs as a
        // variable rather than tripping the caller's non-scalar policy.
        Value::Var(var) => Expr::Var(*var),
        _ => return None,
    })
}

fn subst_vec(
    kb: &mut KnowledgeBase,
    items: &[Rc<NodeOccurrence>],
    subst: &Substitution,
) -> (Vec<Rc<NodeOccurrence>>, bool) {
    let mut changed = false;
    let mut out = Vec::with_capacity(items.len());
    for c in items {
        let r = substitute_occurrence(kb, c, subst);
        changed |= !Rc::ptr_eq(&r, c);
        out.push(r);
    }
    (out, changed)
}

fn subst_named(
    kb: &mut KnowledgeBase,
    items: &[(Symbol, Rc<NodeOccurrence>)],
    subst: &Substitution,
) -> (Vec<(Symbol, Rc<NodeOccurrence>)>, bool) {
    let mut changed = false;
    let mut out = Vec::with_capacity(items.len());
    for (s, c) in items {
        let r = substitute_occurrence(kb, c, subst);
        changed |= !Rc::ptr_eq(&r, c);
        out.push((*s, r));
    }
    (out, changed)
}

// ── Materialization from KB-encoded handle tree ─────────────────

/// Materialize a NodeOccurrence from a stored expression term.
/// WI-251: the legacy `Handle(Occurrence, _)` wrapper is gone — every
/// child slot in the Term tree holds its inner expression term
/// directly. Spans come from `kb.term_span()` (populated by
/// `load.rs::create_occurrence`); when the term wasn't recorded, the
/// wrapping NodeOccurrence carries a zero span.
///
/// WI-253 — fully iterative via explicit work + result stacks. The
/// recursive trio (`materialize_from_handle` → `expr_from_term` →
/// `handle_child`) was ~3 host stack frames per source nesting
/// level, blowing Rust's default 2 MiB debug-build thread stack on
/// the 624-line typing-pass spec. The iterative version runs in
/// constant host stack regardless of source nesting; the loop builds
/// Exprs bottom-up by popping completed children off `results`.
pub fn materialize_from_handle(
    kb: &KnowledgeBase,
    root: TermId,
) -> Rc<NodeOccurrence> {
    let mut work: Vec<WorkOp> = vec![WorkOp::Visit(root)];
    let mut results: Vec<Rc<NodeOccurrence>> = Vec::new();

    while let Some(op) = work.pop() {
        match op {
            WorkOp::Visit(t) => visit_term(kb, t, &mut work, &mut results),
            WorkOp::Build(frame) => build_frame(kb, frame, &mut results),
        }
    }

    debug_assert_eq!(
        results.len(),
        1,
        "materialize_from_handle: expected exactly one result on the stack, got {}",
        results.len(),
    );
    results.pop().expect("root produced no NodeOccurrence")
}

/// WI-304: build the LEAF `NodeOccurrence` for a single op-body Term — the
/// native counterpart to the leaf arms of `visit_term` / `visit_fn`. The
/// op-body loader calls this directly as it converts each parse-IR leaf into
/// its KB Term, so the op body no longer round-trips through the lossy
/// term→occurrence re-walk in `materialize_from_handle`.
///
/// Only genuine leaves reach here: `Const`/`Var`/`Ref`/`Ident`/`Bottom`, and
/// the *concrete* reflect literal/var-ref forms (`int_lit(value: <Const>)`,
/// `var_ref(name: <Ref>)`) the loader emits for op-body literals. Any other
/// `Term::Fn` — or a literal/var-ref with a non-leaf payload — is a bug (an
/// op body never produces a reflection *pattern*); we panic.
pub(crate) fn build_expr_leaf(kb: &KnowledgeBase, t: TermId) -> Rc<NodeOccurrence> {
    let span = kb.term_span(t).unwrap_or_else(empty_span);
    let expr = match kb.get_term(t).clone() {
        Term::Const(lit) => Expr::Const(lit),
        Term::Var(v) => Expr::Var(v),
        Term::Ref(s) => Expr::Ref(s),
        Term::Ident(s) => Expr::Ident(s),
        Term::Bottom => Expr::Bottom,
        Term::Fn { functor, named_args, .. } => {
            let qn = kb.qualified_name_of(functor);
            let short = kb.resolve_sym(functor);
            match expr_form_key(qn, short) {
                "int_lit" | "float_lit" | "bigint_lit" | "string_lit" | "bool_lit" => {
                    match get_named_arg(kb, &named_args, "value").map(|v| kb.get_term(v)) {
                        Some(Term::Const(lit)) => Expr::Const(lit.clone()),
                        other => panic!(
                            "build_expr_leaf: literal form with non-Const value: {other:?}",
                        ),
                    }
                }
                "var_ref" => match named_ref(kb, &named_args, "name") {
                    Some(name) => Expr::VarRef { name },
                    None => panic!("build_expr_leaf: var_ref with non-Ref name"),
                },
                key => panic!(
                    "build_expr_leaf: non-leaf Term::Fn reached the leaf builder (key={key})",
                ),
            }
        }
        Term::ParseAux(_) => panic!("build_expr_leaf: Term::ParseAux reached leaf builder"),
    };
    NodeOccurrence::new_expr(expr, span, None)
}

/// A work-stack item. `Visit` examines a TermId and either pushes a
/// completed leaf NodeOccurrence onto `results`, or pushes a `Build`
/// frame followed by `Visit`s for each child (in reverse order so
/// they pop in source order). `Build` pops the completed children
/// from `results` and assembles the parent NodeOccurrence.
enum WorkOp {
    Visit(TermId),
    Build(BuildFrame),
}

/// Parent-assembly metadata captured at Visit time so the matching
/// `Build` step can re-shape the popped child NodeOccurrences into
/// the right `Expr` variant.
pub(crate) enum BuildFrame {
    /// Empty / missing slot — push a synthesized Bottom occurrence.
    Bottom,
    If { span: SourceSpan },
    Let { span: SourceSpan, pattern: TermId, type_annotation: Option<Value> },
    Lambda { span: SourceSpan, param: TermId },
    /// In-body / control-flow proof (WI-538). Children on the result
    /// stack are `[body, conclude?]`; the resolved target / strategy /
    /// using clauses are carried here.
    Proof {
        span: SourceSpan,
        target: Symbol,
        strategy: Option<Symbol>,
        using: Vec<Symbol>,
        has_conclude: bool,
    },
    Match { span: SourceSpan, branches: Vec<BranchMeta> },
    Apply {
        span: SourceSpan,
        functor: Symbol,
        pos_count: usize,
        named_keys: Vec<Symbol>,
        type_args: Vec<(Option<Symbol>, Value)>,
    },
    Constructor { span: SourceSpan, name: Symbol, pos_count: usize, named_keys: Vec<Symbol> },
    /// `dot_apply(receiver, name, args)` — the receiver is the single child
    /// visited after the args, so it pops last (see `build_frame`).
    DotApply { span: SourceSpan, name: Symbol, pos_count: usize, named_keys: Vec<Symbol> },
    ApplyWithin {
        span: SourceSpan, functor: Symbol,
        pos_count: usize, named_keys: Vec<Symbol>,
        requirements_count: usize,
        type_args: Vec<(Option<Symbol>, Value)>,
    },
    RequirementAtSort { span: SourceSpan, slot: i64 },
    ConstructRequirement { span: SourceSpan, impl_functor: Symbol, requirements_count: usize },
    ListLit { span: SourceSpan, count: usize },
    SetLit { span: SourceSpan, count: usize },
    /// A `TupleLiteral`'s elements ride in `named_args` (positional surface
    /// `(a, b)` becomes `_1`/`_2` labels; declared names stay) — so the frame
    /// carries the keys, like `UnknownFn`. `pos_count` covers any positional
    /// elements (always 0 for the converter's shape, kept for faithfulness).
    TupleLit { span: SourceSpan, pos_count: usize, named_keys: Vec<Symbol> },
    /// Fallback for unknown `Term::Fn` shapes — treated as a generic
    /// Apply with the functor as-is. `pos_count` and `named_keys`
    /// follow the original `Term::Fn` arg arrangement (not the
    /// ApplyArg cons-list shape used by recognised forms).
    UnknownFn { span: SourceSpan, functor: Symbol, pos_count: usize, named_keys: Vec<Symbol> },
}

pub(crate) struct BranchMeta {
    pub(crate) pattern: TermId,
    pub(crate) has_guard: bool,
    pub(crate) span: SourceSpan,
}

fn visit_term(
    kb: &KnowledgeBase,
    t: TermId,
    work: &mut Vec<WorkOp>,
    results: &mut Vec<Rc<NodeOccurrence>>,
) {
    let span = kb.term_span(t).unwrap_or_else(empty_span);
    let term = kb.get_term(t).clone();
    match term {
        Term::Const(lit) => results.push(NodeOccurrence::new_expr(Expr::Const(lit), span, None)),
        Term::Var(v) => results.push(NodeOccurrence::new_expr(Expr::Var(v), span, None)),
        Term::Ref(s) => results.push(NodeOccurrence::new_expr(Expr::Ref(s), span, None)),
        Term::Ident(s) => results.push(NodeOccurrence::new_expr(Expr::Ident(s), span, None)),
        Term::Bottom => results.push(NodeOccurrence::new_expr(Expr::Bottom, span, None)),
        Term::Fn { functor, pos_args, named_args } => {
            let qn = kb.qualified_name_of(functor);
            let short = kb.resolve_sym(functor);
            let key = expr_form_key(qn, short);
            visit_fn(kb, t, span, functor, &pos_args, &named_args, key, work, results);
        }
        Term::ParseAux(_) => unreachable!(
            "parse-only Term::ParseAux variant reached node_occurrence materialization",
        ),
    }
}

/// Visit handler for `Term::Fn` cases — dispatches on the
/// last-segment functor key. Children to materialize get pushed as
/// `Visit` ops in REVERSE order (so the first child pops first), with
/// the matching `Build` frame pushed first (so it pops last).
fn visit_fn(
    kb: &KnowledgeBase,
    t: TermId,
    span: SourceSpan,
    functor: Symbol,
    pos_args: &smallvec::SmallVec<[TermId; 4]>,
    named_args: &smallvec::SmallVec<[(Symbol, TermId); 2]>,
    key: &str,
    work: &mut Vec<WorkOp>,
    results: &mut Vec<Rc<NodeOccurrence>>,
) {
    match key {
        "int_lit" | "float_lit" | "bigint_lit" | "string_lit" | "bool_lit" => {
            match get_named_arg(kb, named_args, "value").map(|v| kb.get_term(v)) {
                // Concrete op-body literal → the internal literal leaf.
                Some(Term::Const(lit)) => {
                    results.push(NodeOccurrence::new_expr(Expr::Const(lit.clone()), span, None));
                }
                // Non-literal `value` ⇒ reflection data (a pattern such as
                // `int_lit(value: ?)`); keep it structural (WI-297) so
                // `occurrence_term` can match it.
                _ => push_unknown_fn(span, functor, pos_args, named_args, work),
            }
        }
        "var_ref" => {
            match named_ref(kb, named_args, "name") {
                Some(sym) => {
                    results.push(NodeOccurrence::new_expr(Expr::VarRef { name: sym }, span, None));
                }
                // Non-name `name` (e.g. `var_ref(name: ?n)`) ⇒ reflection data;
                // keep structural (WI-297).
                None => push_unknown_fn(span, functor, pos_args, named_args, work),
            }
        }
        "if_expr" => {
            let cond = get_named_arg(kb, named_args, "cond");
            let then_b = get_named_arg(kb, named_args, "then_branch");
            let else_b = get_named_arg(kb, named_args, "else_branch");
            work.push(WorkOp::Build(BuildFrame::If { span }));
            push_visit_or_bottom(work, else_b);
            push_visit_or_bottom(work, then_b);
            push_visit_or_bottom(work, cond);
        }
        "let_expr" => {
            let pattern = get_named_arg(kb, named_args, "pattern").unwrap_or(t);
            // WI-342: this term→occurrence rebuild reads the ground `type_name`
            // TermId off the reflect term — it rides as a ground `Value::Term`.
            let type_annotation = get_named_arg(kb, named_args, "type_name").map(Value::term);
            let value = get_named_arg(kb, named_args, "value");
            let body = get_named_arg(kb, named_args, "body");
            work.push(WorkOp::Build(BuildFrame::Let { span, pattern, type_annotation }));
            push_visit_or_bottom(work, body);
            push_visit_or_bottom(work, value);
        }
        "lambda_expr" => {
            let param = get_named_arg(kb, named_args, "param").unwrap_or(t);
            let body = get_named_arg(kb, named_args, "body");
            work.push(WorkOp::Build(BuildFrame::Lambda { span, param }));
            push_visit_or_bottom(work, body);
        }
        "proof_stmt" => {
            // WI-538: rebuild Expr::Proof from a stored `proof_stmt`
            // term (the inverse of the loader's BuildFrame::Proof). The
            // target/strategy/using clauses are leaf metadata; body and
            // optional conclude are the child occurrences.
            match named_ref(kb, named_args, "target") {
                Some(target) => {
                    let strategy = named_ref(kb, named_args, "strategy");
                    // WI-538: the `proof_stmt` KB term carries no `using`
                    // cites — they ride only on the live-load occurrence
                    // (citation metadata, not a child), so a rebuild from
                    // the term yields an empty `using`. A follow-on
                    // encodes them when `using`-as-hypotheses lands.
                    let using: Vec<Symbol> = Vec::new();
                    let conclude = get_named_arg(kb, named_args, "conclude");
                    let body = get_named_arg(kb, named_args, "body");
                    work.push(WorkOp::Build(BuildFrame::Proof {
                        span,
                        target,
                        strategy,
                        using,
                        has_conclude: conclude.is_some(),
                    }));
                    if let Some(c) = conclude {
                        push_visit_or_bottom(work, Some(c));
                    }
                    push_visit_or_bottom(work, body);
                }
                // Malformed `proof_stmt(name: ?n)` ⇒ reflection data; keep
                // structural (mirrors the `var_ref` None arm).
                None => push_unknown_fn(span, functor, pos_args, named_args, work),
            }
        }
        "match_expr" => {
            let scrutinee = get_named_arg(kb, named_args, "scrutinee");
            let branches_tid = get_named_arg(kb, named_args, "branches");
            // Collect branch metadata + Visits in source order, then
            // push in reverse so the work stack pops them in order.
            let mut branches: Vec<BranchMeta> = Vec::new();
            let mut child_visits: Vec<WorkOp> = Vec::new();
            if let Some(list_tid) = branches_tid {
                for br_tid in list_to_vec(kb, list_tid) {
                    let Term::Fn { named_args: ba, .. } = kb.get_term(br_tid) else { continue };
                    let pattern = get_named_arg(kb, ba, "pattern").unwrap_or(br_tid);
                    let body = get_named_arg(kb, ba, "body");
                    let guard_slot = get_named_arg(kb, ba, "guard")
                        .and_then(|opt| unwrap_option(kb, opt));
                    let has_guard = guard_slot.is_some();
                    let branch_span = empty_span();
                    branches.push(BranchMeta { pattern, has_guard, span: branch_span });
                    // Push children in REVERSE of pop order: results
                    // stack will then have, top→bottom, b0_body,
                    // b0_guard?, b1_body, b1_guard?, ... Build's pop
                    // peels them off in source order branch-by-branch.
                    if let Some(g) = guard_slot {
                        child_visits.push(WorkOp::Visit(g));
                    }
                    child_visits.push(visit_or_bottom_op(body));
                }
            }
            work.push(WorkOp::Build(BuildFrame::Match { span, branches }));
            // Branches first (in reverse so pops in order), then scrutinee last (pops first).
            for v in child_visits.into_iter().rev() {
                work.push(v);
            }
            push_visit_or_bottom(work, scrutinee);
        }
        "apply" => {
            let fn_sym = named_ref(kb, named_args, "fn").unwrap_or(functor);
            let args_tid = get_named_arg(kb, named_args, "args");
            let type_args = collect_type_args(kb, get_named_arg(kb, named_args, "type_args"));
            push_apply_like_args(
                kb, args_tid,
                |span_, pos_count, named_keys| {
                    BuildFrame::Apply {
                        span: span_, functor: fn_sym, pos_count, named_keys,
                        type_args: type_args.clone(),
                    }
                },
                span, work,
            );
        }
        "constructor" => {
            let name = named_ref(kb, named_args, "name").unwrap_or(functor);
            let args_tid = get_named_arg(kb, named_args, "args");
            push_apply_like_args(
                kb, args_tid,
                |span_, pos_count, named_keys| {
                    BuildFrame::Constructor { span: span_, name, pos_count, named_keys }
                },
                span, work,
            );
        }
        "dot_apply" => {
            let name = named_ref(kb, named_args, "name").unwrap_or(functor);
            let receiver = get_named_arg(kb, named_args, "receiver");
            let args_tid = get_named_arg(kb, named_args, "args");
            let (pos_count, named_keys, arg_visits) = collect_apply_arg_visits(kb, args_tid);
            work.push(WorkOp::Build(BuildFrame::DotApply { span, name, pos_count, named_keys }));
            // Args first (reversed → pop in source order), receiver last so
            // it pops after the args in `build_frame`.
            for v in arg_visits.into_iter().rev() { work.push(v); }
            push_visit_or_bottom(work, receiver);
        }
        "apply_within" => {
            let fn_sym = named_ref(kb, named_args, "fn").unwrap_or(functor);
            let args_tid = get_named_arg(kb, named_args, "args");
            let reqs_tid = get_named_arg(kb, named_args, "requirements");
            let type_args = collect_type_args(kb, get_named_arg(kb, named_args, "type_args"));
            // First collect args + requirements into reversed visit
            // slots, then push Build with the right counts.
            let (pos_count, named_keys, arg_visits) = collect_apply_arg_visits(kb, args_tid);
            let (req_count, req_visits) = collect_list_visits(kb, reqs_tid);
            work.push(WorkOp::Build(BuildFrame::ApplyWithin {
                span, functor: fn_sym, pos_count, named_keys,
                requirements_count: req_count,
                type_args,
            }));
            // Push requirements first (pop last), then args.
            for v in req_visits.into_iter().rev() { work.push(v); }
            for v in arg_visits.into_iter().rev() { work.push(v); }
        }
        "requirement_at_sort" => {
            let chain = get_named_arg(kb, named_args, "chain");
            let slot = get_named_arg(kb, named_args, "slot")
                .and_then(|t| match kb.get_term(t) {
                    Term::Const(Literal::Int(n)) => Some(*n),
                    _ => None,
                })
                .unwrap_or(0);
            work.push(WorkOp::Build(BuildFrame::RequirementAtSort { span, slot }));
            push_visit_or_bottom(work, chain);
        }
        "construct_requirement" => {
            let impl_functor = named_ref(kb, named_args, "impl_functor").unwrap_or(functor);
            let reqs_tid = get_named_arg(kb, named_args, "requirements");
            let (count, visits) = collect_list_visits(kb, reqs_tid);
            work.push(WorkOp::Build(BuildFrame::ConstructRequirement {
                span, impl_functor, requirements_count: count,
            }));
            for v in visits.into_iter().rev() { work.push(v); }
        }
        "ListLiteral" => {
            // A `ListLiteral` term stores its elements as `pos_args` (see the
            // converter's `CollectionLiteral` build), NOT as a `cons`/`nil` spine
            // — so read them directly. `collect_list_visits` (a cons/nil walker)
            // would silently yield zero, dropping every element (the bug WI-027's
            // un-desugared `forall ?x in [a, b]` collection first exposed). A
            // `ListLiteral` never carries a tail (the `[h | t]` head-tail surface
            // was removed, WI-560), so `pos_args` is the complete element list.
            let visits: Vec<WorkOp> = pos_args.iter().map(|&e| WorkOp::Visit(e)).collect();
            let count = visits.len();
            work.push(WorkOp::Build(BuildFrame::ListLit { span, count }));
            for v in visits.into_iter().rev() { work.push(v); }
        }
        "SetLiteral" => {
            // WI-559: a `SetLiteral` stores its elements as `pos_args` (the
            // converter's `SetLiteral` build uses `alloc_fn_term`, positional
            // only), exactly like `ListLiteral` — so read them directly.
            // `collect_list_visits` (a cons/nil walker) would silently yield
            // zero, dropping every element (the same pre-existing data-loss bug
            // WI-027 fixed for `ListLiteral`).
            let visits: Vec<WorkOp> = pos_args.iter().map(|&e| WorkOp::Visit(e)).collect();
            let count = visits.len();
            work.push(WorkOp::Build(BuildFrame::SetLit { span, count }));
            for v in visits.into_iter().rev() { work.push(v); }
        }
        "TupleLiteral" => {
            // WI-559: a `TupleLiteral` stores its elements as `named_args` —
            // positional surface `(a, b)` becomes `_1`/`_2` labels, declared
            // names stay (see convert.rs `TupleLiteral` build) — NOT a cons/nil
            // spine, so `collect_list_visits` would silently drop every element.
            // Push pos then named exactly as `push_unknown_fn`/`pop_apply_like`
            // expect (named reversed, then pos reversed).
            let pos_count = pos_args.len();
            let named_keys: Vec<Symbol> = named_args.iter().map(|(s, _)| *s).collect();
            work.push(WorkOp::Build(BuildFrame::TupleLit { span, pos_count, named_keys }));
            for &(_, v) in named_args.iter().rev() { work.push(WorkOp::Visit(v)); }
            for &v in pos_args.iter().rev() { work.push(WorkOp::Visit(v)); }
        }
        _ => push_unknown_fn(span, functor, pos_args, named_args, work),
    }
    let _ = results; // kept in case future variants want direct push
}

/// Materialize an unrecognized `Term::Fn` as a generic *structural* occurrence
/// (`Expr::Apply`-shaped: functor + visited children, no Const/Ref leaf
/// collapse). Used for genuinely-unknown functors and — critically (WI-297) —
/// for reflect leaf-entity calls whose fields are non-literal: a reflection
/// *pattern* like `int_lit(value: ?)` or `var_ref(name: ?n)` must stay
/// structural so a rule body atom (`occurrence_term(?e, int_lit(value: ?))`)
/// survives loading. Collapsing those to `Const`/`VarRef`/`⊥` is only correct
/// for concrete op-body expressions, where the field is a literal/known name.
fn push_unknown_fn(
    span: SourceSpan,
    functor: Symbol,
    pos_args: &smallvec::SmallVec<[TermId; 4]>,
    named_args: &smallvec::SmallVec<[(Symbol, TermId); 2]>,
    work: &mut Vec<WorkOp>,
) {
    let pos_count = pos_args.len();
    let named_keys: Vec<Symbol> = named_args.iter().map(|(s, _)| *s).collect();
    work.push(WorkOp::Build(BuildFrame::UnknownFn { span, functor, pos_count, named_keys }));
    for &(_, v) in named_args.iter().rev() {
        work.push(WorkOp::Visit(v));
    }
    for &v in pos_args.iter().rev() {
        work.push(WorkOp::Visit(v));
    }
}

/// Walk a cons-list of `ApplyArg(name, value)` entities and produce
/// `(pos_count, named_keys, visits)` for the apply-like Build path.
/// `pos_count + named_keys.len()` equals the number of Visits the
/// caller must push to feed the matching Build frame.
fn collect_apply_arg_visits(
    kb: &KnowledgeBase,
    list_tid: Option<TermId>,
) -> (usize, Vec<Symbol>, Vec<WorkOp>) {
    let mut pos_count = 0usize;
    let mut named_keys: Vec<Symbol> = Vec::new();
    let mut visits: Vec<WorkOp> = Vec::new();
    let Some(tid) = list_tid else { return (0, named_keys, visits); };
    for arg_tid in list_to_vec(kb, tid) {
        let Term::Fn { named_args: aa, .. } = kb.get_term(arg_tid) else { continue };
        let value = get_named_arg(kb, aa, "value");
        let arg_name = get_named_arg(kb, aa, "name").and_then(|t| some_name(kb, t));
        match arg_name {
            None => { pos_count += 1; visits.push(visit_or_bottom_op(value)); }
            Some(s) => { named_keys.push(s); visits.push(visit_or_bottom_op(value)); }
        }
    }
    (pos_count, named_keys, visits)
}

/// Walk a plain `cons(head, tail) | nil` element list and produce
/// `(count, visits)`. Each entry becomes one Visit op.
/// Walk a cons-list of `type_arg(name: Option[Ref], value: Type)`
/// entries and return `(name, value)` pairs in declaration order;
/// `None` for the name means positional.
pub(crate) fn collect_type_args(
    kb: &KnowledgeBase,
    list_tid: Option<TermId>,
) -> Vec<(Option<Symbol>, Value)> {
    let Some(tid) = list_tid else { return Vec::new(); };
    list_to_vec(kb, tid)
        .into_iter()
        .filter_map(|entry| {
            let entry_args = match kb.get_term(entry) {
                Term::Fn { named_args, .. } => named_args.clone(),
                _ => return None,
            };
            let name_opt = get_named_arg(kb, &entry_args, "name")
                .and_then(|t| some_name(kb, t));
            let value = get_named_arg(kb, &entry_args, "value")?;
            // WI-342 S4b: the term-side handle holds a ground `TermId`, so the
            // materialized occurrence type-arg is `Value::Term`. The loader's
            // direct occurrence build mints a `Value::Node` for a value-in-type
            // arg once `make_denoted` is retired; this term-round-trip path
            // stays ground (the term handle cannot carry a denoted occurrence).
            Some((name_opt, Value::term(value)))
        })
        .collect()
}

fn collect_list_visits(
    kb: &KnowledgeBase,
    list_tid: Option<TermId>,
) -> (usize, Vec<WorkOp>) {
    let Some(tid) = list_tid else { return (0, Vec::new()); };
    let elems = list_to_vec(kb, tid);
    let visits: Vec<WorkOp> = elems.into_iter().map(WorkOp::Visit).collect();
    (visits.len(), visits)
}

/// Helper for apply/constructor: builds the Build frame via `mk` and
/// pushes Visits for each arg in reverse.
fn push_apply_like_args(
    kb: &KnowledgeBase,
    args_tid: Option<TermId>,
    mk: impl FnOnce(SourceSpan, usize, Vec<Symbol>) -> BuildFrame,
    span: SourceSpan,
    work: &mut Vec<WorkOp>,
) {
    let (pos_count, named_keys, visits) = collect_apply_arg_visits(kb, args_tid);
    work.push(WorkOp::Build(mk(span, pos_count, named_keys)));
    for v in visits.into_iter().rev() { work.push(v); }
}

#[inline]
fn push_visit_or_bottom(work: &mut Vec<WorkOp>, slot: Option<TermId>) {
    work.push(visit_or_bottom_op(slot));
}

#[inline]
fn visit_or_bottom_op(slot: Option<TermId>) -> WorkOp {
    match slot {
        Some(t) => WorkOp::Visit(t),
        None => WorkOp::Build(BuildFrame::Bottom),
    }
}

pub(crate) fn build_frame(
    kb: &KnowledgeBase,
    frame: BuildFrame,
    results: &mut Vec<Rc<NodeOccurrence>>,
) {
    match frame {
        BuildFrame::Bottom => results.push(bottom_node()),
        BuildFrame::If { span } => {
            // results stack (top → bottom after Visits):
            //   else_branch, then_branch, condition
            let else_branch = results.pop().expect("if: missing else_branch");
            let then_branch = results.pop().expect("if: missing then_branch");
            let condition = results.pop().expect("if: missing condition");
            let expr = Expr::If { condition, then_branch, else_branch };
            results.push(NodeOccurrence::new_expr(expr, span, None));
        }
        BuildFrame::Let { span, pattern, type_annotation } => {
            // WI-318: build the Pattern-kind pattern occurrence from the
            // TermId carried in the BuildFrame, same as BuildFrame::Lambda.
            let body = results.pop().expect("let: missing body");
            let value = results.pop().expect("let: missing value");
            let pattern_occ = term_to_param_occurrence(kb, pattern, span);
            let expr = Expr::Let { pattern: pattern_occ, type_annotation, value, body };
            results.push(NodeOccurrence::new_expr(expr, span, None));
        }
        BuildFrame::Lambda { span, param } => {
            // WI-318: build the Pattern-kind param occurrence from the
            // TermId carried in the BuildFrame. `term_to_param_occurrence` reads
            // the loader-emitted var_pattern / constructor_pattern /
            // ... shape and produces the structural Pattern equivalent.
            let body = results.pop().expect("lambda: missing body");
            let param_occ = term_to_param_occurrence(kb, param, span);
            let expr = Expr::Lambda { param: param_occ, body };
            results.push(NodeOccurrence::new_expr(expr, span, None));
        }
        BuildFrame::Proof { span, target, strategy, using, has_conclude } => {
            // WI-538: results stack (top → bottom): conclude?, body.
            let conclude = if has_conclude {
                Some(results.pop().expect("proof: missing conclude"))
            } else {
                None
            };
            let body = results.pop().expect("proof: missing body");
            let expr = Expr::Proof { target, strategy, using, conclude, body };
            results.push(NodeOccurrence::new_expr(expr, span, None));
        }
        BuildFrame::Match { span, mut branches } => {
            // results stack contents (top → bottom):
            //   bN_guard?, bN_body, bN-1_guard?, bN-1_body, ..., b0_guard?, b0_body, scrutinee
            // Pop branches in REVERSE source order.
            let mut built_branches: Vec<MatchBranch> = Vec::with_capacity(branches.len());
            while let Some(meta) = branches.pop() {
                let guard = if meta.has_guard {
                    Some(results.pop().expect("match: missing guard"))
                } else {
                    None
                };
                let body = results.pop().expect("match: missing branch body");
                // WI-318: convert the BranchMeta's pattern TermId to a
                // Pattern-kind (or Expr-kind for reflection meta-vars)
                // occurrence, mirroring BuildFrame::Lambda / Let.
                let pattern = term_to_param_occurrence(kb, meta.pattern, meta.span);
                built_branches.push(MatchBranch {
                    pattern,
                    guard,
                    body,
                    span: meta.span,
                });
            }
            built_branches.reverse();
            let scrutinee = results.pop().expect("match: missing scrutinee");
            let expr = Expr::Match { scrutinee, branches: built_branches };
            results.push(NodeOccurrence::new_expr(expr, span, None));
        }
        BuildFrame::Apply { span, functor, pos_count, named_keys, type_args } => {
            let (pos_args, named_args) = pop_apply_like(results, pos_count, named_keys);
            let expr = Expr::Apply { functor, pos_args, named_args, type_args };
            results.push(NodeOccurrence::new_expr(expr, span, None));
        }
        BuildFrame::Constructor { span, name, pos_count, named_keys } => {
            let (pos_args, named_args) = pop_apply_like(results, pos_count, named_keys);
            let expr = Expr::Constructor { name, pos_args, named_args };
            results.push(NodeOccurrence::new_expr(expr, span, None));
        }
        BuildFrame::DotApply { span, name, pos_count, named_keys } => {
            // Args are on top (pushed after the receiver Visit); pop them
            // first, then the receiver underneath.
            let (pos_args, named_args) = pop_apply_like(results, pos_count, named_keys);
            let receiver = results.pop().expect("dot_apply: missing receiver");
            let expr = Expr::DotApply { receiver, name, pos_args, named_args };
            results.push(NodeOccurrence::new_expr(expr, span, None));
        }
        BuildFrame::ApplyWithin {
            span, functor, pos_count, named_keys, requirements_count, type_args,
        } => {
            // results stack (top → bottom):
            //   req_{R-1}, ..., req_0, named_{N-1}, ..., named_0, pos_{P-1}, ..., pos_0
            let mut requirements: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(requirements_count);
            for _ in 0..requirements_count {
                requirements.push(results.pop().expect("apply_within: missing requirement"));
            }
            requirements.reverse();
            let (pos_args, named_args) = pop_apply_like(results, pos_count, named_keys);
            let expr = Expr::ApplyWithin {
                functor, args: pos_args, named_args, requirements, type_args,
            };
            results.push(NodeOccurrence::new_expr(expr, span, None));
        }
        BuildFrame::RequirementAtSort { span, slot } => {
            let chain = results.pop().expect("requirement_at_sort: missing chain");
            let expr = Expr::RequirementAtSort { chain, slot };
            results.push(NodeOccurrence::new_expr(expr, span, None));
        }
        BuildFrame::ConstructRequirement { span, impl_functor, requirements_count } => {
            let mut requirements: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(requirements_count);
            for _ in 0..requirements_count {
                requirements.push(results.pop().expect("construct_requirement: missing entry"));
            }
            requirements.reverse();
            let expr = Expr::ConstructRequirement { impl_functor, requirements };
            results.push(NodeOccurrence::new_expr(expr, span, None));
        }
        BuildFrame::ListLit { span, count } => {
            let elems = pop_n(results, count);
            results.push(NodeOccurrence::new_expr(Expr::ListLit(elems), span, None));
        }
        BuildFrame::SetLit { span, count } => {
            let elems = pop_n(results, count);
            results.push(NodeOccurrence::new_expr(Expr::SetLit(elems), span, None));
        }
        BuildFrame::TupleLit { span, pos_count, named_keys } => {
            let (positional, named) = pop_apply_like(results, pos_count, named_keys);
            let expr = Expr::TupleLit { positional, named };
            results.push(NodeOccurrence::new_expr(expr, span, None));
        }
        BuildFrame::UnknownFn { span, functor, pos_count, named_keys } => {
            let (pos_args, named_args) = pop_apply_like(results, pos_count, named_keys);
            let expr = Expr::Apply { functor, pos_args, named_args, type_args: Vec::new() };
            results.push(NodeOccurrence::new_expr(expr, span, None));
        }
    }
}

fn pop_apply_like(
    results: &mut Vec<Rc<NodeOccurrence>>,
    pos_count: usize,
    named_keys: Vec<Symbol>,
) -> (Vec<Rc<NodeOccurrence>>, Vec<(Symbol, Rc<NodeOccurrence>)>) {
    // results stack (top → bottom):
    //   named_{N-1}, ..., named_0, pos_{P-1}, ..., pos_0
    let n_named = named_keys.len();
    let mut named: Vec<(Symbol, Rc<NodeOccurrence>)> = Vec::with_capacity(n_named);
    for key in named_keys.iter().rev() {
        named.push((*key, results.pop().expect("apply: missing named arg")));
    }
    named.reverse();
    let pos = pop_n(results, pos_count);
    (pos, named)
}

fn pop_n(results: &mut Vec<Rc<NodeOccurrence>>, n: usize) -> Vec<Rc<NodeOccurrence>> {
    let mut out: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(n);
    for _ in 0..n {
        out.push(results.pop().expect("apply: missing positional arg"));
    }
    out.reverse();
    out
}

#[inline]
fn empty_span() -> SourceSpan {
    SourceSpan::new(crate::span::SourceId::from_raw(0), 0, 0)
}

fn bottom_node() -> Rc<NodeOccurrence> {
    NodeOccurrence::new_expr(Expr::Bottom, empty_span(), None)
}

/// Normalize an Expr-form functor name to its last segment, so the
/// dispatch works whether the loader emitted a qualified name like
/// `anthill.reflect.Expr.apply` or a hand-built test produced the
/// bare short name `apply`. We prefer the qualified name as the
/// source of truth; if its last segment is empty (unlikely), fall
/// back to the short name.
fn expr_form_key<'a>(qn: &'a str, short: &'a str) -> &'a str {
    let last = qn.rsplit('.').next().unwrap_or(qn);
    if last.is_empty() { short } else { last }
}

/// WI-246: whether `materialize_from_handle` special-cases a `Term::Fn` with
/// this functor — i.e. would build something OTHER than the generic
/// `push_unknown_fn → Expr::Apply` (a literal `Const` leaf, a `var_ref`, a
/// control-flow `If`/`Let`/`Lambda`/`Match`, a reflect `apply`/`constructor`/
/// `dot_apply`/`*_within`/requirement form, or a `ListLit`/`SetLit`/`TupleLit`).
/// The loader's native rule-body-atom builder routes these to the materialize
/// fallback — their occurrence shape isn't a plain `Apply`, and the `*_lit`
/// keys collapse a concrete `value` to a `Const` leaf — and builds only the
/// generic-application + leaf cases natively. Mirrors `visit_fn`'s match arms;
/// keep the two in sync.
pub fn is_reflect_form_functor(kb: &KnowledgeBase, functor: Symbol) -> bool {
    let qn = kb.qualified_name_of(functor);
    let short = kb.resolve_sym(functor);
    matches!(
        expr_form_key(qn, short),
        "int_lit" | "float_lit" | "bigint_lit" | "string_lit" | "bool_lit"
            | "var_ref" | "if_expr" | "let_expr" | "lambda_expr" | "match_expr"
            | "proof_stmt"
            | "apply" | "constructor" | "dot_apply" | "apply_within"
            | "requirement_at_sort" | "construct_requirement"
            | "ListLiteral" | "SetLiteral" | "TupleLiteral"
    )
}

/// Extract the `Symbol` of a `Ref(sym)` or `Ident(sym)` from a named-arg slot.
fn named_ref(
    kb: &KnowledgeBase,
    named_args: &smallvec::SmallVec<[(Symbol, TermId); 2]>,
    key: &str,
) -> Option<Symbol> {
    let tid = get_named_arg(kb, named_args, key)?;
    match kb.get_term(tid) {
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        _ => None,
    }
}

/// Unwrap an `Option`-shaped term and extract its inner symbol via `Ref`.
/// Returns `None` for `none` or any non-Ref payload.
fn some_name(kb: &KnowledgeBase, tid: TermId) -> Option<Symbol> {
    let inner = unwrap_option(kb, tid)?;
    match kb.get_term(inner) {
        Term::Ref(s) => Some(*s),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intern::SymbolTable;
    use crate::span::{SourceId, SourceSpan};

    fn make_span() -> SourceSpan {
        SourceSpan::new(SourceId::from_raw(0), 0, 10)
    }

    #[test]
    fn build_expr_apply() {
        let mut symbols = SymbolTable::new();
        let f = symbols.intern("f");
        let span = make_span();
        let const42 = NodeOccurrence::new_expr(
            Expr::Const(Literal::Int(42)),
            span,
            None,
        );
        let apply = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: f,
                pos_args: vec![const42],
                named_args: vec![],
                type_args: vec![],
            },
            span,
            None,
        );
        match apply.as_expr().unwrap() {
            Expr::Apply { functor, pos_args, .. } => {
                assert_eq!(*functor, f);
                assert_eq!(pos_args.len(), 1);
            }
            _ => panic!("expected Apply"),
        }
    }

    #[test]
    fn open_debruijn_node_opens_control_flow_forms() {
        // WI-296: a rule-body atom can carry a child-bearing control-flow form
        // (reflection / typing rules match expression structure as data, e.g.
        // `occurrence_term(?e, if_expr(cond: ?c, ...))`). The opener must
        // descend into it and remap DeBruijn -> Global rather than assert it
        // can't occur (the old `_`-arm panic). WI-298: opener now threads
        // `&mut KnowledgeBase` so it can remap DeBruijn vars inside TermId
        // fields (Let.type_annotation, Apply/ApplyWithin.type_args).
        let mut kb = KnowledgeBase::new();
        let v = kb.intern("v");
        let span = make_span();
        let cond = NodeOccurrence::new_expr(Expr::Var(Var::DeBruijn(0)), span, None);
        let then_b = NodeOccurrence::new_expr(Expr::Const(Literal::Int(1)), span, None);
        let else_b = NodeOccurrence::new_expr(Expr::Const(Literal::Int(2)), span, None);
        let if_occ = NodeOccurrence::new_expr(
            Expr::If { condition: cond, then_branch: then_b, else_branch: else_b },
            span,
            None,
        );
        let fresh = [VarId::new(7, v)];
        // Must not panic, and the nested DeBruijn(0) must remap to Global(7).
        let opened = open_debruijn_node(&mut kb, &if_occ, &fresh);
        match opened.as_expr().unwrap() {
            Expr::If { condition, .. } => match condition.as_expr().unwrap() {
                Expr::Var(Var::Global(vid)) => assert_eq!(vid.raw(), 7),
                other => panic!("condition should be a Global var, got {other:?}"),
            },
            other => panic!("expected If, got {other:?}"),
        }

        // A post-elaboration form `reassemble` formerly dropped (its `_` arm
        // returned the original, discarding opened children — WI-296 review):
        // RequirementAtSort. Its child must still open DeBruijn -> Global.
        let chain = NodeOccurrence::new_expr(Expr::Var(Var::DeBruijn(0)), span, None);
        let req = NodeOccurrence::new_expr(
            Expr::RequirementAtSort { chain, slot: 0 },
            span,
            None,
        );
        match open_debruijn_node(&mut kb, &req, &fresh).as_expr().unwrap() {
            Expr::RequirementAtSort { chain, .. } => match chain.as_expr().unwrap() {
                Expr::Var(Var::Global(vid)) => assert_eq!(vid.raw(), 7),
                other => panic!("chain should be a Global var, got {other:?}"),
            },
            other => panic!("expected RequirementAtSort, got {other:?}"),
        }
    }

    #[test]
    fn materialize_dot_apply_field_form() {
        // WI-278: a `dot_apply(receiver, name)` reflect term with no args
        // (field access `recv.name`) round-trips to `Expr::DotApply` with an
        // empty arg list and the receiver materialized as a child.
        use smallvec::SmallVec;
        let mut kb = KnowledgeBase::new();
        let dot = kb.intern("dot_apply");
        let name = kb.intern("size");
        let receiver_key = kb.intern("receiver");
        let name_key = kb.intern("name");
        let recv = kb.alloc(Term::Const(Literal::Int(5)));
        let name_ref = kb.alloc(Term::Ref(name));
        let term = kb.alloc(Term::Fn {
            functor: dot,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(name_key, name_ref), (receiver_key, recv)]),
        });

        let occ = materialize_from_handle(&kb, term);
        match occ.as_expr() {
            Some(Expr::DotApply { receiver, name: n, pos_args, named_args }) => {
                assert_eq!(*n, name);
                assert!(pos_args.is_empty() && named_args.is_empty(), "field form has no args");
                assert!(
                    matches!(receiver.as_expr(), Some(Expr::Const(Literal::Int(5)))),
                    "receiver should materialize as Const(5)"
                );
            }
            other => panic!("expected DotApply, got {other:?}"),
        }
    }

    #[test]
    fn materialize_dot_apply_method_form() {
        // WI-278: `dot_apply(receiver, name, args = [ApplyArg(value)])` —
        // method call `recv.name(arg)` — round-trips with its positional arg.
        use smallvec::SmallVec;
        let mut kb = KnowledgeBase::new();
        let dot = kb.intern("dot_apply");
        let name = kb.intern("map");
        let receiver_key = kb.intern("receiver");
        let name_key = kb.intern("name");
        let args_key = kb.intern("args");
        let value_key = kb.intern("value");

        let apply_arg_sym = kb.intern("ApplyArg");
        let nil_sym = kb.intern("nil");
        let cons_sym = kb.intern("cons");
        let head_key = kb.intern("head");
        let tail_key = kb.intern("tail");

        let recv = kb.alloc(Term::Const(Literal::Int(1)));
        let name_ref = kb.alloc(Term::Ref(name));
        let arg_val = kb.alloc(Term::Const(Literal::Int(9)));
        let apply_arg = kb.alloc(Term::Fn {
            functor: apply_arg_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(value_key, arg_val)]),
        });
        let nil = kb.alloc(Term::Fn {
            functor: nil_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let cons = kb.alloc(Term::Fn {
            functor: cons_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(head_key, apply_arg), (tail_key, nil)]),
        });
        let term = kb.alloc(Term::Fn {
            functor: dot,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (name_key, name_ref),
                (receiver_key, recv),
                (args_key, cons),
            ]),
        });

        let occ = materialize_from_handle(&kb, term);
        match occ.as_expr() {
            Some(Expr::DotApply { receiver, name: n, pos_args, named_args }) => {
                assert_eq!(*n, name);
                assert!(named_args.is_empty());
                assert_eq!(pos_args.len(), 1, "one positional arg");
                assert!(
                    matches!(pos_args[0].as_expr(), Some(Expr::Const(Literal::Int(9)))),
                    "arg should materialize as Const(9)"
                );
                assert!(
                    matches!(receiver.as_expr(), Some(Expr::Const(Literal::Int(1)))),
                    "receiver should materialize as Const(1)"
                );
            }
            other => panic!("expected DotApply, got {other:?}"),
        }
    }

    #[test]
    fn open_debruijn_remaps_var_leaves() {
        // WI-246: a De Bruijn rule-body atom `gt(DeBruijn(0), 3)` opens to
        // `gt(Global(v0), 3)`; the unchanged `3` leaf keeps its Rc identity.
        // WI-298: opener now threads `&mut KnowledgeBase` for TermId-field
        // remap.
        use crate::kb::term::Var;
        let mut kb = KnowledgeBase::new();
        let gt = kb.intern("gt");
        let xname = kb.intern("x");
        let span = make_span();
        let db0 = NodeOccurrence::new_expr(Expr::Var(Var::DeBruijn(0)), span, None);
        let three = NodeOccurrence::new_expr(Expr::Const(Literal::Int(3)), span, None);
        let atom = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: gt,
                pos_args: vec![db0, Rc::clone(&three)],
                named_args: vec![],
                type_args: vec![],
            },
            span,
            None,
        );
        let v0 = VarId::new(7, xname);
        let opened = open_debruijn_node(&mut kb, &atom, &[v0]);
        match opened.as_expr() {
            Some(Expr::Apply { functor, pos_args, .. }) => {
                assert_eq!(*functor, gt);
                assert!(
                    matches!(pos_args[0].as_expr(), Some(Expr::Var(Var::Global(v))) if *v == v0),
                    "DeBruijn(0) should open to Global(v0), got {:?}",
                    pos_args[0].as_expr()
                );
                assert!(Rc::ptr_eq(&pos_args[1], &three), "unchanged const child keeps identity");
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    #[test]
    fn node_to_debruijn_closes_var_leaves_and_round_trips() {
        // WI-246: the loader builds a Global-var atom `gt(Global(v0), 3)`;
        // `node_to_debruijn` closes it to `gt(DeBruijn(0), 3)` (matching
        // `term_to_debruijn`'s `len-1-pos` convention), and `open_debruijn_node`
        // re-opens it to a fresh Global — the loader→resolution round-trip.
        use crate::kb::term::Var;
        let mut kb = KnowledgeBase::new();
        let gt = kb.intern("gt");
        let xname = kb.intern("x");
        let span = make_span();
        let v0 = VarId::new(7, xname);
        let var0 = NodeOccurrence::new_expr(Expr::Var(Var::Global(v0)), span, None);
        let three = NodeOccurrence::new_expr(Expr::Const(Literal::Int(3)), span, None);
        let atom = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: gt,
                pos_args: vec![var0, Rc::clone(&three)],
                named_args: vec![],
                type_args: vec![],
            },
            span,
            None,
        );

        // Single-var order: v0 is the only (=last) entry → DeBruijn 0.
        let closed = node_to_debruijn(&mut kb, &atom, &[v0]);
        match closed.as_expr() {
            Some(Expr::Apply { functor, pos_args, .. }) => {
                assert_eq!(*functor, gt);
                assert!(
                    matches!(pos_args[0].as_expr(), Some(Expr::Var(Var::DeBruijn(0)))),
                    "Global(v0) should close to DeBruijn(0), got {:?}",
                    pos_args[0].as_expr()
                );
                assert!(Rc::ptr_eq(&pos_args[1], &three), "unchanged const child keeps identity");
            }
            other => panic!("expected Apply, got {other:?}"),
        }

        // Re-open with a fresh global: the leaf comes back as that global.
        let v_fresh = VarId::new(42, xname);
        let reopened = open_debruijn_node(&mut kb, &closed, &[v_fresh]);
        match reopened.as_expr() {
            Some(Expr::Apply { pos_args, .. }) => assert!(
                matches!(pos_args[0].as_expr(), Some(Expr::Var(Var::Global(v))) if *v == v_fresh),
                "round-trip should re-open DeBruijn(0) to the fresh global",
            ),
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    #[test]
    fn node_to_debruijn_uses_len_minus_one_minus_pos_index() {
        // Two vars [a, b]: position 0 (a) → DeBruijn 1, position 1 (b, last) →
        // DeBruijn 0 — exactly `term_to_debruijn`'s convention, so a natively
        // built body aligns with the De Bruijn-converted head.
        use crate::kb::term::Var;
        let mut kb = KnowledgeBase::new();
        let p = kb.intern("p");
        let aname = kb.intern("a");
        let bname = kb.intern("b");
        let span = make_span();
        let a = VarId::new(1, aname);
        let b = VarId::new(2, bname);
        let atom = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: p,
                pos_args: vec![
                    NodeOccurrence::new_expr(Expr::Var(Var::Global(a)), span, None),
                    NodeOccurrence::new_expr(Expr::Var(Var::Global(b)), span, None),
                ],
                named_args: vec![],
                type_args: vec![],
            },
            span,
            None,
        );
        let closed = node_to_debruijn(&mut kb, &atom, &[a, b]);
        let Some(Expr::Apply { pos_args, .. }) = closed.as_expr() else { panic!("expected Apply") };
        assert!(matches!(pos_args[0].as_expr(), Some(Expr::Var(Var::DeBruijn(1)))));
        assert!(matches!(pos_args[1].as_expr(), Some(Expr::Var(Var::DeBruijn(0)))));
    }

    #[test]
    fn lambda_param_round_trip_through_pattern_occurrence() {
        // WI-318: with param lifted to a Pattern-kind Rc<NodeOccurrence>,
        // the De Bruijn closer/opener no longer needs a special arm for
        // it — the structural for_each_child + reassemble walk uniformly
        // handles the param's children (currently always empty for a
        // typical `Pattern::Var { name: Symbol, type_ann: None }`).
        // Verify a Lambda built with a Pattern::Var param round-trips
        // through node_to_debruijn unchanged (no vars to remap, but the
        // walker still must accept it).
        use crate::kb::term::Var;
        let mut kb = KnowledgeBase::new();
        let xname = kb.intern("x");
        let span = make_span();
        let v0 = VarId::new(7, xname);
        let param = NodeOccurrence::new_pattern(
            Pattern::Var { name: xname, type_ann: None },
            span,
            None,
        );
        let body = NodeOccurrence::new_expr(Expr::Var(Var::Global(v0)), span, None);
        let lambda = NodeOccurrence::new_expr(Expr::Lambda { param, body }, span, None);

        let closed = node_to_debruijn(&mut kb, &lambda, &[v0]);
        match closed.as_expr() {
            Some(Expr::Lambda { param, body }) => {
                assert!(
                    matches!(param.as_pattern(), Some(Pattern::Var { .. })),
                    "param stays a Pattern-kind occurrence after close",
                );
                assert!(
                    matches!(body.as_expr(), Some(Expr::Var(Var::DeBruijn(0)))),
                    "body var closes to DeBruijn(0)",
                );
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    #[test]
    fn collect_ordered_picks_up_vars_in_apply_type_args_wi318() {
        // WI-318: with patterns lifted out of TermId fields, the remaining
        // TermId-bearing positions reachable by node_to_debruijn (and that
        // for_each_child does NOT descend into) are the type-position
        // TermIds: Apply.type_args, ApplyWithin.type_args, and Let.type_
        // annotation. `collect_occurrence_global_vars_ordered` must still
        // collect a Global living exclusively in one of those — otherwise
        // it would be left as a stray Global (escaping per-call freshening)
        // and the rule's arity would undercount it.
        //
        // This test exercises Apply.type_args specifically. (See the older
        // `collect_ordered_picks_up_vars_in_apply_type_args` below for the
        // pre-WI-318 sibling.)
        use crate::kb::term::Var;
        let mut kb = KnowledgeBase::new();
        let xname = kb.intern("x");
        let yname = kb.intern("y");
        let span = make_span();

        let vx = VarId::new(7, xname);
        let vy = VarId::new(8, yname);
        // An Apply whose type_args carry Global(vx); body args reference vy.
        let type_arg_tid = kb.alloc(Term::Var(Var::Global(vx)));
        let body_arg = NodeOccurrence::new_expr(Expr::Var(Var::Global(vy)), span, None);
        let f_sym = kb.intern("f");
        let apply = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: f_sym,
                pos_args: vec![body_arg],
                named_args: vec![],
                type_args: vec![(None, Value::term(type_arg_tid))],
            },
            span,
            None,
        );

        let mut vars = Vec::new();
        let mut seen = std::collections::HashSet::new();
        collect_occurrence_global_vars_ordered(&kb, &apply, &mut vars, &mut seen);

        assert!(vars.contains(&vx), "type_args-only var vx must be collected, got {vars:?}");
        assert!(vars.contains(&vy), "body-arg var vy must be collected, got {vars:?}");
        assert_eq!(vars, vec![vy, vx], "child vars first, then TermId-field vars");

        // Closing leaves NO stray Global:
        let closed = node_to_debruijn(&mut kb, &apply, &vars);
        let Some(Expr::Apply { type_args, .. }) = closed.as_expr() else {
            panic!("expected Apply");
        };
        let Value::Term { id: ta, .. } = &type_args[0].1 else { panic!("type-arg must be Value::Term") };
        assert!(
            matches!(kb.get_term(*ta), Term::Var(Var::DeBruijn(_))),
            "type_args var must close to DeBruijn (no stray Global), got {:?}",
            kb.get_term(*ta)
        );
    }

    #[test]
    fn wi298_open_remaps_debruijn_inside_apply_type_args() {
        // WI-298: a rule whose body has `Apply.type_args` containing
        // DeBruijn(0) must, on opening, surface the fresh `Global(v0)` in
        // that type-arg slot — mirroring `node_to_debruijn`'s
        // `close_type_args` on the closing side. Without the WI-298 fix
        // the opener cloned `type_args` verbatim, leaving the stored
        // DeBruijn in place.
        use crate::kb::term::Var;
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("f");
        let xname = kb.intern("x");
        let span = make_span();
        // A type_args entry holding a DeBruijn(0) leaf (the rule's shared
        // De Bruijn space).
        let ta_db = kb.alloc(Term::Var(Var::DeBruijn(0)));
        let atom = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: f,
                pos_args: vec![],
                named_args: vec![],
                type_args: vec![(None, Value::term(ta_db))],
            },
            span,
            None,
        );
        let v0 = VarId::new(7, xname);
        let opened = open_debruijn_node(&mut kb, &atom, &[v0]);
        let Some(Expr::Apply { type_args, .. }) = opened.as_expr() else {
            panic!("expected Apply");
        };
        let Value::Term { id: ta, .. } = &type_args[0].1 else { panic!("type-arg must be Value::Term") };
        let Term::Var(Var::Global(vid)) = kb.get_term(*ta) else {
            panic!("type_args entry should open to Global, got {:?}", kb.get_term(*ta));
        };
        assert_eq!(*vid, v0, "type_args DeBruijn(0) must open to fresh Global(v0)");
    }

    #[test]
    fn wi471_cached_term_recovers_hash_cons_identity() {
        // WI-471: cached_term materializes (through the hash-consing TermStore)
        // and memoizes an occurrence's intrinsic term form. Verifies (1) two
        // distinct occurrences of the SAME structure → the SAME TermId; (2) a
        // DIFFERENT structure → a DIFFERENT TermId; (3) set-once / KbId-stamped /
        // idempotent; (4) a read against a FOREIGN KB re-materializes + re-stamps
        // (the KbId guard) rather than returning a TermId from the wrong store.
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("f");
        let span = make_span();
        let build = |n: i64| {
            let arg = NodeOccurrence::new_expr(Expr::Const(Literal::Int(n)), span, None);
            NodeOccurrence::new_expr(
                Expr::Apply {
                    functor: f,
                    pos_args: vec![arg],
                    named_args: vec![],
                    type_args: vec![],
                },
                span,
                None,
            )
        };
        let o1 = build(42);
        let o2 = build(42);
        assert!(!std::rc::Rc::ptr_eq(&o1, &o2), "distinct Rc allocations");
        assert!(o1.term_cache.get().is_none(), "cache starts empty");

        // (1) identical structure → identical hash-consed TermId.
        let t1 = cached_term(&mut kb, &o1);
        let t2 = cached_term(&mut kb, &o2);
        assert_eq!(t1, t2, "structurally-identical occurrences share one TermId");

        // (2) different structure → different TermId (a constant-returning stub
        // would fail here).
        let o3 = build(43);
        assert_ne!(cached_term(&mut kb, &o3), t1, "f(43) must not collide with f(42)");

        // (3) memoized: populated, stamped with this KB's id, idempotent.
        let cached = o1.term_cache.get().expect("cache populated after demand");
        assert_eq!(cached.1, t1, "cache holds the materialized TermId");
        assert_eq!(cached.0, kb.id, "cache stamped with this KB's id");
        assert_eq!(cached_term(&mut kb, &o1), t1, "second demand is idempotent");

        // (4) KbId guard: reading o1 against a FOREIGN KB re-materializes against
        // that store and re-stamps — it must NOT return kb's TermId blindly.
        let mut kb2 = KnowledgeBase::new();
        assert_ne!(kb.id, kb2.id, "distinct KBs get distinct ids");
        let t_in_kb2 = cached_term(&mut kb2, &o1);
        assert_eq!(o1.term_cache.get().unwrap().0, kb2.id, "re-stamped for the foreign KB");
        assert!(
            matches!(kb2.get_term(t_in_kb2), Term::Fn { .. }),
            "returned id is a live term in kb2's store",
        );
    }

    #[test]
    fn wi298_open_remaps_debruijn_inside_let_type_annotation() {
        // WI-298: a Let occurrence in a rule body whose `type_annotation` and
        // `body` both contain a leaf `Var::DeBruijn(0)` (the rule's shared
        // De Bruijn space). Opening with `fresh = [v0]` must remap BOTH the
        // body leaf and the type_annotation TermId to the same `Global(v0)`,
        // so a hypothetical `?p` shared between the annotation and the body
        // resolves to one fresh global. Without the WI-298 fix the
        // annotation kept its DeBruijn in place.
        use crate::kb::term::Var;
        let mut kb = KnowledgeBase::new();
        let xname = kb.intern("x");
        let span = make_span();
        let v0 = VarId::new(7, xname);
        // Pattern: `Pattern::Var { name: x, type_ann: None }`.
        let pattern = NodeOccurrence::new_pattern(
            Pattern::Var { name: xname, type_ann: None },
            span,
            None,
        );
        // value/body are bare literals — uninteresting for this test.
        let value = NodeOccurrence::new_expr(Expr::Const(Literal::Int(1)), span, None);
        let body = NodeOccurrence::new_expr(Expr::Var(Var::DeBruijn(0)), span, None);
        // Annotation: a DeBruijn(0) standing for ?p in type position.
        let ta_db = kb.alloc(Term::Var(Var::DeBruijn(0)));
        let let_occ = NodeOccurrence::new_expr(
            Expr::Let {
                pattern,
                type_annotation: Some(Value::term(ta_db)),
                value,
                body,
            },
            span,
            None,
        );
        let opened = open_debruijn_node(&mut kb, &let_occ, &[v0]);
        let Some(Expr::Let { type_annotation, body, .. }) = opened.as_expr() else {
            panic!("expected Let");
        };
        let Some(Value::Term { id: ta, .. }) = type_annotation else {
            panic!("type_annotation should still be Some after open");
        };
        let Term::Var(Var::Global(ta_vid)) = kb.get_term(*ta) else {
            panic!("type_annotation should open to Global, got {:?}", kb.get_term(*ta));
        };
        assert_eq!(*ta_vid, v0, "type_annotation DeBruijn(0) must open to fresh Global(v0)");
        // And the body's ?p must have opened to the SAME global — the
        // observable property the acceptance criterion calls for.
        let Some(Expr::Var(Var::Global(body_vid))) = body.as_expr() else {
            panic!("body should be Global, got {:?}", body.as_expr());
        };
        assert_eq!(*body_vid, v0, "body var and type_annotation var must share the same fresh global");
    }

    #[test]
    fn wi298_close_remaps_global_inside_let_type_annotation() {
        // WI-298: complementing the opener test — node_to_debruijn must also
        // close a Global living in `Let.type_annotation` into the rule's
        // shared De Bruijn space, mirroring the opener. Without this the
        // stored rule body would carry a stray Global that escaped
        // per-call freshening.
        use crate::kb::term::Var;
        let mut kb = KnowledgeBase::new();
        let xname = kb.intern("x");
        let span = make_span();
        let v0 = VarId::new(7, xname);
        let pattern = NodeOccurrence::new_pattern(
            Pattern::Var { name: xname, type_ann: None },
            span,
            None,
        );
        let value = NodeOccurrence::new_expr(Expr::Const(Literal::Int(1)), span, None);
        let body = NodeOccurrence::new_expr(Expr::Var(Var::Global(v0)), span, None);
        let ta_global = kb.alloc(Term::Var(Var::Global(v0)));
        let let_occ = NodeOccurrence::new_expr(
            Expr::Let {
                pattern,
                type_annotation: Some(Value::term(ta_global)),
                value,
                body,
            },
            span,
            None,
        );
        let closed = node_to_debruijn(&mut kb, &let_occ, &[v0]);
        let Some(Expr::Let { type_annotation, body, .. }) = closed.as_expr() else {
            panic!("expected Let");
        };
        let Some(Value::Term { id: ta, .. }) = type_annotation else {
            panic!("type_annotation should still be Some after close");
        };
        assert!(
            matches!(kb.get_term(*ta), Term::Var(Var::DeBruijn(0))),
            "Let.type_annotation Global must close to DeBruijn(0), got {:?}",
            kb.get_term(*ta),
        );
        assert!(
            matches!(body.as_expr(), Some(Expr::Var(Var::DeBruijn(0)))),
            "Let.body Global must close to DeBruijn(0), got {:?}",
            body.as_expr(),
        );
    }

    #[test]
    fn wi298_substitute_applies_sigma_to_apply_type_args() {
        // WI-298: `substitute_occurrence` must apply σ to the TermId
        // entries of `Apply.type_args`. Without the fix it cloned them
        // verbatim, so a rule-param Global in a call-site type argument
        // would not be replaced by its head-matched concrete value.
        use crate::kb::term::Var;
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("f");
        let int_sym = kb.intern("Int64");
        let xname = kb.intern("x");
        let span = make_span();
        let v0 = VarId::new(7, xname);
        // A type_args entry holding Global(v0).
        let ta_global = kb.alloc(Term::Var(Var::Global(v0)));
        let atom = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: f,
                pos_args: vec![],
                named_args: vec![],
                type_args: vec![(None, Value::term(ta_global))],
            },
            span,
            None,
        );
        let int_ref = kb.alloc(Term::Ref(int_sym));
        let mut subst = Substitution::new();
        subst.bind(&kb, v0, int_ref);

        let out = substitute_occurrence(&mut kb, &atom, &subst);
        let Some(Expr::Apply { type_args, .. }) = out.as_expr() else {
            panic!("expected Apply, got {:?}", out.as_expr());
        };
        let Value::Term { id: ta, .. } = &type_args[0].1 else { panic!("type-arg must be Value::Term") };
        assert_eq!(
            *ta, int_ref,
            "Apply.type_args must be substituted to Ref(Int) under σ; got {:?}",
            kb.get_term(*ta),
        );
    }

    #[test]
    fn wi298_substitute_applies_sigma_to_let_type_annotation() {
        // WI-298: the substitute_occurrence Let arm must apply σ to
        // type_annotation, mirroring the Apply arm. Without the explicit Let
        // arm the generic _ fall-through would skip the TermId field.
        use crate::kb::term::Var;
        let mut kb = KnowledgeBase::new();
        let int_sym = kb.intern("Int64");
        let xname = kb.intern("x");
        let span = make_span();
        let v0 = VarId::new(7, xname);
        let pattern = NodeOccurrence::new_pattern(
            Pattern::Var { name: xname, type_ann: None },
            span,
            None,
        );
        let value = NodeOccurrence::new_expr(Expr::Const(Literal::Int(1)), span, None);
        let body = NodeOccurrence::new_expr(Expr::Const(Literal::Int(2)), span, None);
        let ta_global = kb.alloc(Term::Var(Var::Global(v0)));
        let let_occ = NodeOccurrence::new_expr(
            Expr::Let {
                pattern,
                type_annotation: Some(Value::term(ta_global)),
                value,
                body,
            },
            span,
            None,
        );
        let int_ref = kb.alloc(Term::Ref(int_sym));
        let mut subst = Substitution::new();
        subst.bind(&kb, v0, int_ref);

        let out = substitute_occurrence(&mut kb, &let_occ, &subst);
        let Some(Expr::Let { type_annotation, .. }) = out.as_expr() else {
            panic!("expected Let, got {:?}", out.as_expr());
        };
        let Some(Value::Term { id: ta, .. }) = type_annotation else {
            panic!("type_annotation should still be Some after subst");
        };
        assert_eq!(
            *ta, int_ref,
            "Let.type_annotation must be substituted to Ref(Int) under σ; got {:?}",
            kb.get_term(*ta),
        );
    }

    #[test]
    fn wi298_apply_within_type_args_round_trip_through_debruijn() {
        // WI-298: the new explicit ApplyWithin arms in open/close handle
        // type_args symmetrically with Apply. A Global → DeBruijn → Global
        // round-trip should reproduce the fresh var.
        use crate::kb::term::Var;
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("f");
        let tname = kb.intern("t");
        let span = make_span();
        let v0 = VarId::new(7, tname);
        let ta_global = kb.alloc(Term::Var(Var::Global(v0)));
        let atom = NodeOccurrence::new_expr(
            Expr::ApplyWithin {
                functor: f,
                args: vec![],
                named_args: vec![],
                requirements: vec![],
                type_args: vec![(None, Value::term(ta_global))],
            },
            span,
            None,
        );
        // Close: Global(v0) → DeBruijn(0).
        let closed = node_to_debruijn(&mut kb, &atom, &[v0]);
        let Some(Expr::ApplyWithin { type_args, .. }) = closed.as_expr() else {
            panic!("expected ApplyWithin after close");
        };
        let Value::Term { id: ta, .. } = &type_args[0].1 else { panic!("type-arg must be Value::Term") };
        assert!(
            matches!(kb.get_term(*ta), Term::Var(Var::DeBruijn(0))),
            "ApplyWithin.type_args Global must close to DeBruijn(0); got {:?}",
            kb.get_term(*ta),
        );
        // Open with fresh global: DeBruijn(0) → Global(v_fresh).
        let v_fresh = VarId::new(42, tname);
        let reopened = open_debruijn_node(&mut kb, &closed, &[v_fresh]);
        let Some(Expr::ApplyWithin { type_args, .. }) = reopened.as_expr() else {
            panic!("expected ApplyWithin after open");
        };
        let Value::Term { id: ta, .. } = &type_args[0].1 else { panic!("type-arg must be Value::Term") };
        let Term::Var(Var::Global(vid)) = kb.get_term(*ta) else {
            panic!("type_args entry should open to Global, got {:?}", kb.get_term(*ta));
        };
        assert_eq!(*vid, v_fresh, "round-trip must yield the fresh global");
    }

    #[test]
    fn collect_ordered_picks_up_vars_in_apply_type_args() {
        // The `Apply.type_args` counterpart of the param-only case: a var that
        // lives only in a type argument (closed by `node_to_debruijn` via
        // `close_type_args`) must be collected.
        use crate::kb::term::Var;
        let mut kb = KnowledgeBase::new();
        let tname = kb.intern("t");
        let f = kb.intern("f");
        let span = make_span();
        let vt = VarId::new(9, tname);
        let ta_tid = kb.alloc(Term::Var(Var::Global(vt)));
        let atom = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: f,
                pos_args: vec![],
                named_args: vec![],
                type_args: vec![(None, Value::term(ta_tid))],
            },
            span,
            None,
        );

        let mut vars = Vec::new();
        let mut seen = std::collections::HashSet::new();
        collect_occurrence_global_vars_ordered(&kb, &atom, &mut vars, &mut seen);
        assert_eq!(vars, vec![vt], "type-arg var must be collected, got {vars:?}");
    }

    /// Build the rule-body atom `gt(Global(v0), 3)` and return `(atom, v0,
    /// gt, three_child)` for the substitution tests below.
    fn gt_atom(kb: &mut KnowledgeBase) -> (Rc<NodeOccurrence>, VarId, Symbol, Rc<NodeOccurrence>) {
        let gt = kb.intern("gt");
        let xname = kb.intern("x");
        let span = make_span();
        let v0 = VarId::new(7, xname);
        let var0 = NodeOccurrence::new_expr(Expr::Var(Var::Global(v0)), span, None);
        let three = NodeOccurrence::new_expr(Expr::Const(Literal::Int(3)), span, None);
        let atom = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: gt,
                pos_args: vec![var0, Rc::clone(&three)],
                named_args: vec![],
                type_args: vec![],
            },
            span,
            None,
        );
        (atom, v0, gt, three)
    }

    #[test]
    fn substitute_occurrence_keeps_unbound_var() {
        // WI-246: an unbound `Expr::Var(Global)` survives substitution as the
        // same variable leaf (not ⊥); with no bound leaf the whole atom keeps
        // its Rc identity.
        let mut kb = KnowledgeBase::new();
        let (atom, v0, _gt, _three) = gt_atom(&mut kb);
        let out = substitute_occurrence(&mut kb, &atom, &Substitution::new());
        assert!(Rc::ptr_eq(&out, &atom), "no bound leaf → atom unchanged (identity)");
        match out.as_expr() {
            Some(Expr::Apply { pos_args, .. }) => assert!(
                matches!(pos_args[0].as_expr(), Some(Expr::Var(Var::Global(v))) if *v == v0),
                "unbound var leaf preserved",
            ),
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    #[test]
    fn substitute_occurrence_binds_scalar() {
        // A var bound to a scalar becomes a `Const`; the unchanged sibling
        // keeps its Rc identity.
        let mut kb = KnowledgeBase::new();
        let (atom, v0, _gt, three) = gt_atom(&mut kb);
        let mut subst = Substitution::new();
        subst.bind_value(&kb, v0, Value::Int(42));
        let out = substitute_occurrence(&mut kb, &atom, &subst);
        match out.as_expr() {
            Some(Expr::Apply { pos_args, .. }) => {
                assert!(
                    matches!(pos_args[0].as_expr(), Some(Expr::Const(Literal::Int(42)))),
                    "bound var → Const(42), got {:?}",
                    pos_args[0].as_expr()
                );
                assert!(Rc::ptr_eq(&pos_args[1], &three), "unchanged sibling keeps identity");
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    /// WI-502 Step 3 — `rebuilt_expr` carries the stamped `inferred_type` onto
    /// the rebuilt occurrence (the helper every rebuild path now routes through).
    #[test]
    fn rebuilt_expr_preserves_inferred_type() {
        let mut kb = KnowledgeBase::new();
        let int64 = kb.make_sort_ref_by_name("Int64");
        let node = NodeOccurrence::new_expr(Expr::Bottom, make_span(), None);
        node.set_inferred_type(Value::term(int64));
        let rebuilt = node.rebuilt_expr(Expr::Const(Literal::Int(1)));
        assert!(
            matches!(rebuilt.inferred_type(), Some(Value::Term { id: t, .. }) if t == int64),
            "rebuilt occurrence must carry the stamped inferred_type",
        );
    }

    /// WI-502 Step 3 — substituting a child must NOT drop the parent atom's
    /// stamped type (the "original WI-502 bug"). A bound var forces the Apply to
    /// rebuild; the rebuilt node must retain `inferred_type`.
    #[test]
    fn substitute_occurrence_carries_inferred_type() {
        let mut kb = KnowledgeBase::new();
        let (atom, v0, _gt, _three) = gt_atom(&mut kb);
        let bool_ty = kb.make_sort_ref_by_name("Bool");
        atom.set_inferred_type(Value::term(bool_ty));
        let mut subst = Substitution::new();
        subst.bind_value(&kb, v0, Value::Int(42)); // change a child → forces rebuild
        let out = substitute_occurrence(&mut kb, &atom, &subst);
        assert!(!Rc::ptr_eq(&out, &atom), "the atom should have been rebuilt");
        assert!(
            matches!(out.inferred_type(), Some(Value::Term { id: t, .. }) if t == bool_ty),
            "substitute_occurrence must carry the parent atom's inferred_type",
        );
    }

    #[test]
    fn substitute_occurrence_splices_node_in_place() {
        // A var bound to a matched child occurrence (`Value::Node`) is spliced
        // in place, preserving the occurrence's Rc identity (and provenance).
        let mut kb = KnowledgeBase::new();
        let (atom, v0, _gt, _three) = gt_atom(&mut kb);
        let payload = NodeOccurrence::new_expr(Expr::Bottom, make_span(), None);
        let mut subst = Substitution::new();
        subst.bind_value(&kb, v0, Value::Node(Rc::clone(&payload)));
        let out = substitute_occurrence(&mut kb, &atom, &subst);
        match out.as_expr() {
            Some(Expr::Apply { pos_args, .. }) => assert!(
                Rc::ptr_eq(&pos_args[0], &payload),
                "Value::Node binding spliced in place (identity preserved)",
            ),
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    #[test]
    fn substitute_occurrence_materializes_bound_term_preserving_nested_var() {
        // A var bound to a compound term materializes to an occurrence, and a
        // nested *unbound* var inside that term survives as `Expr::Var` — the
        // var-preservation invariant the `[simp]` RHS builder lacks.
        use smallvec::SmallVec;
        let mut kb = KnowledgeBase::new();
        let (atom, v0, _gt, _three) = gt_atom(&mut kb);
        let s = kb.intern("s");
        let yname = kb.intern("y");
        let v1 = VarId::new(8, yname);
        // bind v0 → s(Global(v1)), with v1 left unbound
        let inner_var = kb.alloc(Term::Var(Var::Global(v1)));
        let compound = kb.alloc(Term::Fn {
            functor: s,
            pos_args: SmallVec::from_elem(inner_var, 1),
            named_args: SmallVec::new(),
        });
        let mut subst = Substitution::new();
        subst.bind_value(&kb, v0, Value::term(compound));
        let out = substitute_occurrence(&mut kb, &atom, &subst);
        match out.as_expr() {
            Some(Expr::Apply { pos_args, .. }) => match pos_args[0].as_expr() {
                Some(Expr::Apply { functor, pos_args: inner, .. }) => {
                    assert_eq!(*functor, s);
                    assert!(
                        matches!(inner[0].as_expr(), Some(Expr::Var(Var::Global(v))) if *v == v1),
                        "nested unbound var preserved as Expr::Var, got {:?}",
                        inner[0].as_expr()
                    );
                }
                other => panic!("expected materialized s(...), got {other:?}"),
            },
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    #[test]
    fn substitute_occurrence_substitutes_named_arg() {
        // Exercises `subst_named`: a named arg whose value is a bound var gets
        // substituted, the field symbol survives, and an unbound positional
        // sibling is preserved.
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("f");
        let key = kb.intern("k");
        let xname = kb.intern("x");
        let yname = kb.intern("y");
        let span = make_span();
        let vx = VarId::new(7, xname);
        let vy = VarId::new(8, yname);
        let pos_var = NodeOccurrence::new_expr(Expr::Var(Var::Global(vx)), span, None);
        let named_var = NodeOccurrence::new_expr(Expr::Var(Var::Global(vy)), span, None);
        let atom = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: f,
                pos_args: vec![pos_var],
                named_args: vec![(key, named_var)],
                type_args: vec![],
            },
            span,
            None,
        );
        let mut subst = Substitution::new();
        subst.bind_value(&kb, vy, Value::Int(99)); // bind only the named arg
        let out = substitute_occurrence(&mut kb, &atom, &subst);
        match out.as_expr() {
            Some(Expr::Apply { pos_args, named_args, .. }) => {
                assert!(
                    matches!(pos_args[0].as_expr(), Some(Expr::Var(Var::Global(v))) if *v == vx),
                    "unbound positional preserved",
                );
                assert_eq!(named_args[0].0, key, "field symbol survives");
                assert!(
                    matches!(named_args[0].1.as_expr(), Some(Expr::Const(Literal::Int(99)))),
                    "named-arg var substituted, got {:?}",
                    named_args[0].1.as_expr()
                );
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    #[test]
    fn substitute_occurrence_passes_through_non_var_leaves() {
        // A `Ref` child (and any non-`Var` leaf) passes through untouched,
        // keeping Rc identity — exercising the leaf/`_` passthrough arm.
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("f");
        let r = kb.intern("WorkItem");
        let span = make_span();
        let ref_child = NodeOccurrence::new_expr(Expr::Ref(r), span, None);
        let atom = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: f,
                pos_args: vec![Rc::clone(&ref_child)],
                named_args: vec![],
                type_args: vec![],
            },
            span,
            None,
        );
        let out = substitute_occurrence(&mut kb, &atom, &Substitution::new());
        assert!(Rc::ptr_eq(&out, &atom), "no substitutable leaf → whole atom keeps identity");
        match out.as_expr() {
            Some(Expr::Apply { pos_args, .. }) => {
                assert!(Rc::ptr_eq(&pos_args[0], &ref_child), "Ref leaf preserved by identity");
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    #[test]
    fn rc_ptr_eq_identity() {
        let span = make_span();
        let occ = NodeOccurrence::new_expr(Expr::Bottom, span, None);
        let cloned = Rc::clone(&occ);
        assert!(Rc::ptr_eq(&occ, &cloned));
    }

    // ── WI-378 step 2 / WI-342-P3: Type-occurrence var walk ─────────
    //
    // No producer mints a logical var inside a Type occurrence today (denoteds
    // are Ref/Const, type-vars stay ground TypeChild::Ground), so these tests
    // hand-build the substrate case: a `Parameterized` type carrying a `Var` in
    // BOTH a ground `TypeChild::Ground(TermId)` binding and a `TypeChild::Node`
    // child occurrence (the shape a denoted-bearing dependent type would mint).
    // They pin that collect / De Bruijn close+open / σ all descend the type spine.

    /// Build `param(base = Bottom, bg = Ground(Var(vg)), bn = Node(Var(vn)))`.
    fn type_with_vars(kb: &mut KnowledgeBase, vg: VarId, vn: VarId) -> Rc<NodeOccurrence> {
        let span = make_span();
        let base_t = kb.alloc(Term::Const(Literal::Int(0)));
        let vg_t = kb.alloc(Term::Var(Var::Global(vg)));
        let bg = kb.intern("bg");
        let bn = kb.intern("bn");
        let node_child = NodeOccurrence::new_expr(Expr::Var(Var::Global(vn)), span, None);
        NodeOccurrence::new_type(
            TypeNode::Parameterized {
                base: TypeChild::Ground(base_t),
                bindings: vec![
                    (bg, TypeChild::Ground(vg_t)),
                    (bn, TypeChild::Node(node_child)),
                ],
            },
            span,
            None,
        )
    }

    /// Pull the two binding children out of a `Parameterized` type occurrence.
    fn param_bindings(occ: &Rc<NodeOccurrence>) -> (TypeChild, TypeChild) {
        match &occ.kind {
            NodeKind::Type(TypeNode::Parameterized { bindings, .. }) => {
                (bindings[0].1.clone(), bindings[1].1.clone())
            }
            other => panic!("expected Parameterized type, got {other:?}"),
        }
    }

    #[test]
    fn type_occurrence_collects_vars_in_ground_and_node_children() {
        let mut kb = KnowledgeBase::new();
        let name = kb.intern("v");
        let vg = VarId::new(1, name);
        let vn = VarId::new(2, name);
        let ty = type_with_vars(&mut kb, vg, vn);

        let mut vars = Vec::new();
        let mut seen = std::collections::HashSet::new();
        collect_value_type(&kb, &Value::Node(Rc::clone(&ty)), &mut vars, &mut seen);
        // base (ground const) has no var; bindings collect vg then vn, in order.
        assert_eq!(vars, vec![vg, vn], "both ground- and node-child vars collected, in order");
    }

    #[test]
    fn type_occurrence_close_open_roundtrips_vars() {
        let mut kb = KnowledgeBase::new();
        let name = kb.intern("v");
        let vg = VarId::new(1, name);
        let vn = VarId::new(2, name);
        let ty = type_with_vars(&mut kb, vg, vn);

        // Close with order [vg, vn]: vg (pos 0) → DeBruijn(1), vn (pos 1) → DeBruijn(0).
        let closed = node_to_debruijn(&mut kb, &ty, &[vg, vn]);
        let (bg, bn) = param_bindings(&closed);
        match bg {
            TypeChild::Ground(t) => assert!(
                matches!(kb.terms.get(t), Term::Var(Var::DeBruijn(1))),
                "ground binding var closes to DeBruijn(1), got {:?}", kb.terms.get(t),
            ),
            other => panic!("expected Ground, got {other:?}"),
        }
        match bn {
            TypeChild::Node(n) => assert!(
                matches!(n.as_expr(), Some(Expr::Var(Var::DeBruijn(0)))),
                "node-child var closes to DeBruijn(0), got {:?}", n.as_expr(),
            ),
            other => panic!("expected Node, got {other:?}"),
        }

        // Open maps DeBruijn(i) → fresh[i] (the resolver's per-index freshening).
        // With fresh [fa, fb]: the ground child's DeBruijn(1) → fb, the node
        // child's DeBruijn(0) → fa — proving open descends the Type spine and
        // remaps both carriers by index.
        let fa = VarId::new(10, name);
        let fb = VarId::new(11, name);
        let opened = open_debruijn_node(&mut kb, &closed, &[fa, fb]);
        let (bg, bn) = param_bindings(&opened);
        match bg {
            TypeChild::Ground(t) => assert!(
                matches!(kb.terms.get(t), Term::Var(Var::Global(v)) if *v == fb),
                "ground binding DeBruijn(1) re-opens to Global(fresh[1]=fb), got {:?}", kb.terms.get(t),
            ),
            other => panic!("expected Ground, got {other:?}"),
        }
        match bn {
            TypeChild::Node(n) => assert!(
                matches!(n.as_expr(), Some(Expr::Var(Var::Global(v))) if *v == fa),
                "node-child DeBruijn(0) re-opens to Global(fresh[0]=fa)",
            ),
            other => panic!("expected Node, got {other:?}"),
        }
    }

    #[test]
    fn type_occurrence_unchanged_when_no_var_in_order() {
        // Behavior-preserving: closing with a var_order that misses the type's
        // vars leaves the occurrence untouched (same Rc) — the no-var denoted
        // path the loader actually exercises today.
        let mut kb = KnowledgeBase::new();
        let name = kb.intern("v");
        let vg = VarId::new(1, name);
        let vn = VarId::new(2, name);
        let ty = type_with_vars(&mut kb, vg, vn);
        let other = VarId::new(99, name);
        let closed = node_to_debruijn(&mut kb, &ty, &[other]);
        assert!(Rc::ptr_eq(&closed, &ty), "no var in order → occurrence keeps identity");
    }

    #[test]
    fn type_occurrence_named_tuple_field_var_is_walked() {
        // A `NamedTuple` carries its fields as a `Value`-carried cons-list
        // (`Value::Entity`/`Tuple`), whose element field-types are themselves
        // type `Value`s. A var inside one must be collected and closed — the
        // gap the shared `map_value_type` / `collect_value_type` Entity/Tuple
        // recursion closes (mirroring `close_value_head_debruijn` / occurs-check).
        let mut kb = KnowledgeBase::new();
        let name = kb.intern("v");
        let v = VarId::new(5, name);
        let f = kb.intern("cons");
        let span = make_span();
        let v_t = kb.alloc(Term::Var(Var::Global(v)));
        // fields = entity(cons, pos = [Term(Var v)]) — a one-element field carrier.
        let fields = Value::Entity {
            functor: f,
            pos: Rc::from(vec![Value::term(v_t)]),
            named: Rc::from(Vec::<(Symbol, Value)>::new()),
            ty: None,
        };
        let nt = NodeOccurrence::new_type(TypeNode::NamedTuple { fields }, span, None);

        // Collect descends the cons-list and finds v.
        let mut vars = Vec::new();
        let mut seen = std::collections::HashSet::new();
        collect_value_type(&kb, &Value::Node(Rc::clone(&nt)), &mut vars, &mut seen);
        assert_eq!(vars, vec![v], "var inside a NamedTuple field type is collected");

        // Close descends and turns it into DeBruijn(0) (single-var order).
        let closed = node_to_debruijn(&mut kb, &nt, &[v]);
        match &closed.kind {
            NodeKind::Type(TypeNode::NamedTuple { fields: Value::Entity { pos, .. } }) => {
                match &pos[0] {
                    Value::Term { id: t, .. } => assert!(
                        matches!(kb.terms.get(*t), Term::Var(Var::DeBruijn(0))),
                        "field-type var closes to DeBruijn(0), got {:?}", kb.terms.get(*t),
                    ),
                    other => panic!("expected Term field type, got {other:?}"),
                }
            }
            other => panic!("expected NamedTuple Entity fields, got {other:?}"),
        }
    }

    #[test]
    fn type_occurrence_substitute_rewrites_ground_var() {
        let mut kb = KnowledgeBase::new();
        let name = kb.intern("v");
        let vg = VarId::new(1, name);
        let vn = VarId::new(2, name);
        let ty = type_with_vars(&mut kb, vg, vn);

        // σ = { vg ↦ 7 }. The ground binding's Var(vg) becomes 7; vn unbound stays.
        let seven = kb.alloc(Term::Const(Literal::Int(7)));
        let mut subst = Substitution::new();
        subst.bind(&kb, vg, seven);
        let out = substitute_occurrence(&mut kb, &ty, &subst);
        let (bg, bn) = param_bindings(&out);
        match bg {
            TypeChild::Ground(t) => assert_eq!(t, seven, "vg in a ground type child rewrites to 7"),
            other => panic!("expected Ground, got {other:?}"),
        }
        match bn {
            TypeChild::Node(n) => assert!(
                matches!(n.as_expr(), Some(Expr::Var(Var::Global(v))) if *v == vn),
                "unbound vn stays a Global var",
            ),
            other => panic!("expected Node, got {other:?}"),
        }
    }

    #[test]
    fn synthesized_inherits_span() {
        let mut symbols = SymbolTable::new();
        let pass_sym = symbols.intern("anthill.kb.passes.test_pass");
        let pass = PassId::from_symbol(pass_sym);
        let source_span = SourceSpan::new(SourceId::from_raw(0), 100, 200);
        let source = NodeOccurrence::new_expr(Expr::Bottom, source_span, None);

        let synth = NodeOccurrence::synthesized_expr(
            Expr::Const(Literal::Int(1)),
            Rc::clone(&source),
            pass,
            None,
        );

        assert_eq!(synth.span, source_span);
        match &synth.kind {
            NodeKind::Expr { origin: OccurrenceOrigin::Synthesized { from, by }, .. } => {
                assert!(Rc::ptr_eq(from, &source));
                assert_eq!(by.symbol(), pass_sym);
            }
            _ => panic!("expected synthesized Expr"),
        }
    }

    #[test]
    fn wi559_set_literal_round_trips_through_occurrence() {
        // WI-559: a `SetLiteral` term stores its elements as `pos_args` (like
        // `ListLiteral`). The term→occurrence build formerly walked a cons/nil
        // spine (`collect_list_visits`), which silently yielded zero — every
        // element dropped. The build now reads `pos_args`, and reify mints the
        // `SetLiteral` term twin, so a set literal round-trips losslessly.
        use crate::kb::load::register_prelude;
        use smallvec::SmallVec;
        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        let set_sym = kb.resolve_symbol("anthill.reflect.SetLiteral");
        let a = kb.alloc(Term::Const(Literal::Int(1)));
        let b = kb.alloc(Term::Const(Literal::Int(2)));
        let set_tid = kb.alloc(Term::Fn {
            functor: set_sym,
            pos_args: SmallVec::from_slice(&[a, b]),
            named_args: SmallVec::new(),
        });

        let occ = materialize_from_handle(&kb, set_tid);
        match occ.as_expr() {
            Some(Expr::SetLit(elems)) => {
                assert_eq!(elems.len(), 2, "both set elements must survive the build");
                assert!(matches!(elems[0].as_expr(), Some(Expr::Const(Literal::Int(1)))));
                assert!(matches!(elems[1].as_expr(), Some(Expr::Const(Literal::Int(2)))));
            }
            other => panic!("expected SetLit, got {other:?}"),
        }

        let round = occurrence_to_term(&mut kb, &occ);
        assert_eq!(round, set_tid, "set literal must reify to its original term twin");
    }

    #[test]
    fn wi559_tuple_literal_round_trips_through_occurrence() {
        // WI-559: a `TupleLiteral` term stores its elements as `named_args`
        // (positional surface `(a, b)` → `_1`/`_2` labels; declared names stay).
        // The build formerly walked a cons/nil spine and dropped every element;
        // it now reads `named_args`, and reify mints the `TupleLiteral` twin.
        use crate::kb::load::register_prelude;
        use smallvec::SmallVec;
        let mut kb = KnowledgeBase::new();
        register_prelude(&mut kb);
        let tuple_sym = kb.resolve_symbol("anthill.reflect.TupleLiteral");
        // The converter encodes positional surface `(a, b)` as `_1`/`_2` labels
        // (convert.rs `intern_positional_label`), so build that exact shape.
        let k1 = kb.intern("_1");
        let k2 = kb.intern("_2");
        let a = kb.alloc(Term::Const(Literal::Int(1)));
        let b = kb.alloc(Term::Const(Literal::Int(2)));
        let tuple_tid = kb.alloc(Term::Fn {
            functor: tuple_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(k1, a), (k2, b)]),
        });

        let occ = materialize_from_handle(&kb, tuple_tid);
        match occ.as_expr() {
            Some(Expr::TupleLit { positional, named }) => {
                assert!(positional.is_empty(), "tuple elements ride in named_args");
                assert_eq!(named.len(), 2, "both tuple elements must survive the build");
                assert_eq!(named[0].0, k1);
                assert_eq!(named[1].0, k2);
                assert!(matches!(named[0].1.as_expr(), Some(Expr::Const(Literal::Int(1)))));
                assert!(matches!(named[1].1.as_expr(), Some(Expr::Const(Literal::Int(2)))));
            }
            other => panic!("expected TupleLit, got {other:?}"),
        }

        let round = occurrence_to_term(&mut kb, &occ);
        assert_eq!(round, tuple_tid, "tuple literal must reify to its original term twin");
    }
}
