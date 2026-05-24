/// NodeOccurrence — KB-side positional wrapper for source content.
///
/// Per `docs/design/occurrence-as-value-type.md`. Replaces the arena+ID
/// the legacy occurrence side-table model: every child slot in an `Expr` is a
/// `Rc<NodeOccurrence>`, alternating `NodeOccurrence ⇄ NodeKind ⇄ Expr ⇄ NodeOccurrence`
/// all the way down. The tree is `Rc`-linked from the start so reflection
/// bindings are cheap (`Rc::clone`), eval can stash on its frame stack
/// without lifetime threading, and cross-pass identity is `Rc::ptr_eq`.

use std::cell::RefCell;
use std::rc::Rc;

use crate::intern::Symbol;
use crate::span::SourceSpan;

pub use super::occurrence::PassId;
use super::subst::Substitution;
use super::term::{Literal, Term, TermId, Var, VarId};
use super::typing::{get_named_arg, list_to_vec, unwrap_option};
use super::KnowledgeBase;
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
    if let NodeKind::Expr { expr, origin, .. } = &mut occ.kind {
        if let OccurrenceOrigin::Synthesized { from, .. } = origin {
            let placeholder = NodeOccurrence::new_expr(Expr::Bottom, empty_span(), None);
            stack.push(std::mem::replace(from, placeholder));
        }
        drain_expr_children(expr, stack);
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
        Expr::Apply { pos_args, named_args, .. }
        | Expr::Constructor { pos_args, named_args, .. }
        | Expr::Instantiation { pos_args, named_args, .. } => {
            for c in std::mem::take(pos_args) { stack.push(c); }
            for (_, c) in std::mem::take(named_args) { stack.push(c); }
        }
        Expr::If { condition, then_branch, else_branch } => {
            stack.push(std::mem::replace(condition, mk_placeholder()));
            stack.push(std::mem::replace(then_branch, mk_placeholder()));
            stack.push(std::mem::replace(else_branch, mk_placeholder()));
        }
        Expr::Let { value, body, .. } => {
            stack.push(std::mem::replace(value, mk_placeholder()));
            stack.push(std::mem::replace(body, mk_placeholder()));
        }
        Expr::Match { scrutinee, branches } => {
            stack.push(std::mem::replace(scrutinee, mk_placeholder()));
            for mut b in std::mem::take(branches) {
                stack.push(std::mem::replace(&mut b.body, mk_placeholder()));
                if let Some(g) = b.guard.take() {
                    stack.push(g);
                }
            }
        }
        Expr::Lambda { body, .. } | Expr::LambdaWithin { body, .. } => {
            stack.push(std::mem::replace(body, mk_placeholder()));
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
        Expr::ApplyWithin { args, named_args, requirements, .. } => {
            for a in std::mem::take(args) { stack.push(a); }
            for (_, a) in std::mem::take(named_args) { stack.push(a); }
            for r in std::mem::take(requirements) { stack.push(r); }
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
        })
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
        })
    }

    /// If this occurrence wraps an expression, return it.
    pub fn as_expr(&self) -> Option<&Expr> {
        match &self.kind {
            NodeKind::Expr { expr, .. } => Some(expr),
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
    /// refined, e.g. expected-hint-constrained) type wins.
    pub fn set_inferred_type(&self, ty: TermId) {
        if let NodeKind::Expr { inferred_type, .. } = &self.kind {
            *inferred_type.borrow_mut() = Some(ty);
        }
    }

    /// The typer's inferred type for this occurrence, if typed (WI-284).
    /// `None` for rule heads, not-yet-typed occurrences, or ill-typed
    /// nodes. The basis for `min_sort` (`typing::min_sort`).
    pub fn inferred_type(&self) -> Option<TermId> {
        match &self.kind {
            NodeKind::Expr { inferred_type, .. } => *inferred_type.borrow(),
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
        /// (`min_sort`, `typing::min_sort`) without recomputing. Written
        /// by the typer's `Stamp` work-frame once a node's `TypeResult`
        /// is finalized; `None` until typed, or when the node is ill-typed.
        inferred_type: RefCell<Option<TermId>>,
    },
    /// Rule head — positional wrapper around a Term-shaped head pattern.
    /// Args are `TermId` (KB-position content); the wrap exists for span
    /// + owner metadata only.
    RuleHead {
        functor: Symbol,
        pos_args: Vec<TermId>,
        named_args: Vec<(Symbol, TermId)>,
    },
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
        type_args: Vec<(Option<Symbol>, TermId)>,
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
    /// `let pat = value in body`.
    Let {
        pattern: TermId,
        type_annotation: Option<TermId>,
        value: Rc<NodeOccurrence>,
        body: Rc<NodeOccurrence>,
    },
    /// Lambda — `(param) => body`.
    Lambda {
        param: TermId,
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
    /// `[simp]` dot rules (`default_dot` / `dot_field`, proposal 043 §6)
    /// rewrite it — once the receiver's type is known — into an `Apply`
    /// (method) or a field access (field). A `DotApply` reaching the typer
    /// is a no-match error at its source span. `name`-less field access has
    /// empty arg lists; a method call carries its positional / named args.
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
        type_args: Vec<(Option<Symbol>, TermId)>,
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
    /// Lambda carrying captured requirements.
    LambdaWithin {
        param: TermId,
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
    pub pattern: TermId,
    pub guard: Option<Rc<NodeOccurrence>>,
    pub body: Rc<NodeOccurrence>,
    pub span: SourceSpan,
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
        Expr::Let { value, body, .. } => {
            f(value);
            f(body);
        }
        Expr::Match { scrutinee, branches } => {
            f(scrutinee);
            for b in branches.iter() {
                f(&b.body);
                if let Some(g) = &b.guard { f(g); }
            }
        }
        Expr::Lambda { body, .. } => f(body),
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
        Expr::LambdaWithin { body, requirements, .. } => {
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
pub fn open_debruijn_node(occ: &Rc<NodeOccurrence>, fresh: &[VarId]) -> Rc<NodeOccurrence> {
    let Some(expr) = occ.as_expr() else { return Rc::clone(occ) };
    let rebuilt: Option<Expr> = match expr {
        Expr::Var(Var::DeBruijn(idx)) => fresh
            .get(*idx as usize)
            .map(|&vid| Expr::Var(Var::Global(vid))),
        Expr::Apply { functor, pos_args, named_args, type_args } => {
            let (pos, c1) = open_vec(pos_args, fresh);
            let (named, c2) = open_named(named_args, fresh);
            (c1 || c2).then(|| Expr::Apply {
                functor: *functor,
                pos_args: pos,
                named_args: named,
                type_args: type_args.clone(),
            })
        }
        Expr::Constructor { name, pos_args, named_args } => {
            let (pos, c1) = open_vec(pos_args, fresh);
            let (named, c2) = open_named(named_args, fresh);
            (c1 || c2).then(|| Expr::Constructor { name: *name, pos_args: pos, named_args: named })
        }
        Expr::Instantiation { name, pos_args, named_args } => {
            let (pos, c1) = open_vec(pos_args, fresh);
            let (named, c2) = open_named(named_args, fresh);
            (c1 || c2).then(|| Expr::Instantiation { name: *name, pos_args: pos, named_args: named })
        }
        Expr::HoApply { predicate, args } => {
            let p = open_debruijn_node(predicate, fresh);
            let (a, c2) = open_vec(args, fresh);
            let c1 = !Rc::ptr_eq(&p, predicate);
            (c1 || c2).then(|| Expr::HoApply { predicate: p, args: a })
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
            for_each_child(expr, |c| opened.push(open_debruijn_node(c, fresh)));
            return super::simp_rewrite::reassemble(occ, &opened);
        }
    };
    match rebuilt {
        Some(e) => NodeOccurrence::new_expr(e, occ.span, occ.owner),
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
/// `Rc<NodeOccurrence>` children AND inside the `TermId`-typed occurrence fields
/// of materialized reflect-data forms — `Let.pattern`/`type_annotation`,
/// `Lambda`/`LambdaWithin.param`, `Match` branch patterns, and
/// `Apply`/`ApplyWithin.type_args` — by running those through
/// `KnowledgeBase::term_to_debruijn` (hence `&mut self`). So a body atom is
/// fully De Bruijn-closed regardless of where its vars live, matching what the
/// prior `materialize(term_to_debruijn(t))` path produced (a var nested in such
/// a field is now in the rule's De Bruijn key space, e.g. for the typer). Note:
/// `open_debruijn_node` still does not OPEN those `TermId` fields back — same as
/// before — but reflect-data patterns are matched as data, not resolved as
/// goals, so they are never opened at a goal position.
pub fn node_to_debruijn(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    var_order: &[VarId],
) -> Rc<NodeOccurrence> {
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
        Expr::Let { pattern, type_annotation, value, body } => {
            let new_pattern = kb.term_to_debruijn(*pattern, var_order);
            let new_type_ann = type_annotation.map(|t| kb.term_to_debruijn(t, var_order));
            let v = node_to_debruijn(kb, value, var_order);
            let b = node_to_debruijn(kb, body, var_order);
            let changed = new_pattern != *pattern
                || new_type_ann != *type_annotation
                || !Rc::ptr_eq(&v, value)
                || !Rc::ptr_eq(&b, body);
            changed.then(|| Expr::Let {
                pattern: new_pattern,
                type_annotation: new_type_ann,
                value: v,
                body: b,
            })
        }
        Expr::Lambda { param, body } => {
            let new_param = kb.term_to_debruijn(*param, var_order);
            let b = node_to_debruijn(kb, body, var_order);
            (new_param != *param || !Rc::ptr_eq(&b, body))
                .then(|| Expr::Lambda { param: new_param, body: b })
        }
        Expr::LambdaWithin { param, body, requirements } => {
            let new_param = kb.term_to_debruijn(*param, var_order);
            let b = node_to_debruijn(kb, body, var_order);
            let (reqs, c) = close_vec(kb, requirements, var_order);
            (new_param != *param || !Rc::ptr_eq(&b, body) || c)
                .then(|| Expr::LambdaWithin { param: new_param, body: b, requirements: reqs })
        }
        Expr::Match { scrutinee, branches } => {
            let s = node_to_debruijn(kb, scrutinee, var_order);
            let mut changed = !Rc::ptr_eq(&s, scrutinee);
            let mut new_branches: Vec<MatchBranch> = Vec::with_capacity(branches.len());
            for br in branches {
                let new_pattern = kb.term_to_debruijn(br.pattern, var_order);
                if new_pattern != br.pattern {
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
        Some(e) => NodeOccurrence::new_expr(e, occ.span, occ.owner),
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

/// Close vars inside a call site's `type_args` (`(name?, type-TermId)` pairs)
/// via `term_to_debruijn`. `term_to_debruijn` returns the same hash-consed
/// `TermId` when nothing changed, so `changed` tracks real rewrites.
fn close_type_args(
    kb: &mut KnowledgeBase,
    items: &[(Option<Symbol>, TermId)],
    var_order: &[VarId],
) -> (Vec<(Option<Symbol>, TermId)>, bool) {
    let mut changed = false;
    let mut out = Vec::with_capacity(items.len());
    for &(name, t) in items {
        let nt = kb.term_to_debruijn(t, var_order);
        changed |= nt != t;
        out.push((name, nt));
    }
    (out, changed)
}

fn open_vec(items: &[Rc<NodeOccurrence>], fresh: &[VarId]) -> (Vec<Rc<NodeOccurrence>>, bool) {
    let mut changed = false;
    let out = items
        .iter()
        .map(|c| {
            let r = open_debruijn_node(c, fresh);
            changed |= !Rc::ptr_eq(&r, c);
            r
        })
        .collect();
    (out, changed)
}

fn open_named(
    items: &[(Symbol, Rc<NodeOccurrence>)],
    fresh: &[VarId],
) -> (Vec<(Symbol, Rc<NodeOccurrence>)>, bool) {
    let mut changed = false;
    let out = items
        .iter()
        .map(|(s, c)| {
            let r = open_debruijn_node(c, fresh);
            changed |= !Rc::ptr_eq(&r, c);
            (*s, r)
        })
        .collect();
    (out, changed)
}

/// WI-246: does the occurrence contain any `Expr::Var(Var::Global)` leaf?
/// In a σ-substituted goal occurrence every remaining Global-var leaf is
/// unbound (bound ones were spliced by [`substitute_occurrence`]), so this is
/// the occurrence analog of `KnowledgeBase::is_ground`'s "has unbound var"
/// test. Iterative pre-order — flat host stack regardless of nesting.
pub fn occurrence_has_unbound_var(root: &Rc<NodeOccurrence>) -> bool {
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(root)];
    while let Some(occ) = stack.pop() {
        match occ.as_expr() {
            Some(Expr::Var(Var::Global(_))) => return true,
            Some(expr) => for_each_child(expr, |c| stack.push(Rc::clone(c))),
            None => {}
        }
    }
    false
}

/// Collect the distinct `Var::Global` ids occurring in an occurrence (deduped
/// via `seen`), recursing into children. The occurrence twin of the term-side
/// `collect_vars_rec` — which likewise collects only `Var::Global` (Rigid /
/// DeBruijn ignored). Used by `with_fresh_vars`'s legacy path to gather a
/// rule's body vars without reading the term body (WI-246).
pub(super) fn collect_occurrence_global_vars(
    root: &Rc<NodeOccurrence>,
    vars: &mut Vec<VarId>,
    seen: &mut std::collections::HashSet<u32>,
) {
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(root)];
    while let Some(occ) = stack.pop() {
        match occ.as_expr() {
            Some(Expr::Var(Var::Global(vid))) => {
                if seen.insert(vid.raw()) {
                    vars.push(*vid);
                }
            }
            Some(expr) => for_each_child(expr, |c| stack.push(Rc::clone(c))),
            None => {}
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
    match occ.as_expr() {
        Some(Expr::Var(Var::Global(vid))) => {
            if seen.insert(vid.raw()) {
                vars.push(*vid);
            }
        }
        Some(expr) => {
            for_each_child(expr, |c| {
                collect_occurrence_global_vars_ordered(kb, c, vars, seen)
            });
            collect_expr_termid_field_vars(kb, expr, vars, seen);
        }
        None => {}
    }
}

/// Collect `Var::Global` ids from the `TermId`-typed var-bearing fields of an
/// `Expr` — the pattern / param / type-annotation / type-arg fields that
/// `for_each_child` does not descend but [`node_to_debruijn`] closes. Kept in
/// lockstep with `node_to_debruijn`'s `term_to_debruijn` calls: any field closed
/// there must be collected here.
fn collect_expr_termid_field_vars(
    kb: &KnowledgeBase,
    expr: &Expr,
    vars: &mut Vec<VarId>,
    seen: &mut std::collections::HashSet<u32>,
) {
    match expr {
        Expr::Apply { type_args, .. } | Expr::ApplyWithin { type_args, .. } => {
            for (_, t) in type_args {
                kb.collect_vars_rec(*t, vars, seen);
            }
        }
        Expr::Let { pattern, type_annotation, .. } => {
            kb.collect_vars_rec(*pattern, vars, seen);
            if let Some(t) = type_annotation {
                kb.collect_vars_rec(*t, vars, seen);
            }
        }
        Expr::Lambda { param, .. } | Expr::LambdaWithin { param, .. } => {
            kb.collect_vars_rec(*param, vars, seen);
        }
        Expr::Match { branches, .. } => {
            for b in branches {
                kb.collect_vars_rec(b.pattern, vars, seen);
            }
        }
        _ => {}
    }
}

/// WI-246: structural equality of two occurrences — used by
/// `Value::structural_eq` so the resolver's non-linear-pattern consistency
/// check (a head var bound at two goal positions) treats two structurally-
/// equal-but-distinct occurrence sub-parts as equal (e.g. the two `green`s in
/// `list_contains(green, cons(head: green, …))`). Compares the goal-relevant
/// forms (Apply / Constructor / Instantiation / leaves) recursively; other
/// forms compare unequal (conservative).
pub fn occurrence_structural_eq(a: &Rc<NodeOccurrence>, b: &Rc<NodeOccurrence>) -> bool {
    if Rc::ptr_eq(a, b) {
        return true;
    }
    match (a.as_expr(), b.as_expr()) {
        (Some(Expr::Var(x)), Some(Expr::Var(y))) => x == y,
        (Some(Expr::Const(x)), Some(Expr::Const(y))) => x == y,
        (Some(Expr::Ref(x)), Some(Expr::Ref(y))) => x == y,
        (Some(Expr::Ident(x)), Some(Expr::Ident(y))) => x == y,
        (Some(Expr::Bottom), Some(Expr::Bottom)) => true,
        (
            Some(Expr::Apply { functor: fa, pos_args: pa, named_args: na, .. }),
            Some(Expr::Apply { functor: fb, pos_args: pb, named_args: nb, .. }),
        ) => fa == fb && occ_children_eq(pa, na, pb, nb),
        (
            Some(Expr::Constructor { name: fa, pos_args: pa, named_args: na })
            | Some(Expr::Instantiation { name: fa, pos_args: pa, named_args: na }),
            Some(Expr::Constructor { name: fb, pos_args: pb, named_args: nb })
            | Some(Expr::Instantiation { name: fb, pos_args: pb, named_args: nb }),
        ) => fa == fb && occ_children_eq(pa, na, pb, nb),
        _ => false,
    }
}

fn occ_children_eq(
    pa: &[Rc<NodeOccurrence>],
    na: &[(Symbol, Rc<NodeOccurrence>)],
    pb: &[Rc<NodeOccurrence>],
    nb: &[(Symbol, Rc<NodeOccurrence>)],
) -> bool {
    pa.len() == pb.len()
        && na.len() == nb.len()
        && pa.iter().zip(pb).all(|(x, y)| occurrence_structural_eq(x, y))
        && na.iter().zip(nb).all(|((ka, va), (kb, vb))| ka == kb && occurrence_structural_eq(va, vb))
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
pub fn try_occurrence_to_term(kb: &mut KnowledgeBase, occ: &Rc<NodeOccurrence>) -> Option<TermId> {
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
pub fn substitute_occurrence(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    subst: &Substitution,
) -> Rc<NodeOccurrence> {
    let Some(expr) = occ.as_expr() else { return Rc::clone(occ) };
    let rebuilt: Option<Rc<NodeOccurrence>> = match expr {
        Expr::Var(Var::Global(vid)) => return subst_var_leaf(kb, *vid, subst, occ),
        Expr::Apply { functor, pos_args, named_args, type_args } => {
            let (pos, c1) = subst_vec(kb, pos_args, subst);
            let (named, c2) = subst_named(kb, named_args, subst);
            (c1 || c2).then(|| {
                NodeOccurrence::new_expr(
                    Expr::Apply {
                        functor: *functor,
                        pos_args: pos,
                        named_args: named,
                        type_args: type_args.clone(),
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
    rebuilt.unwrap_or_else(|| Rc::clone(occ))
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
        Some(Value::Term(t)) => *t,
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
            WorkOp::Build(frame) => build_frame(frame, &mut results),
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
enum BuildFrame {
    /// Empty / missing slot — push a synthesized Bottom occurrence.
    Bottom,
    If { span: SourceSpan },
    Let { span: SourceSpan, pattern: TermId, type_annotation: Option<TermId> },
    Lambda { span: SourceSpan, param: TermId },
    Match { span: SourceSpan, branches: Vec<BranchMeta> },
    Apply {
        span: SourceSpan,
        functor: Symbol,
        pos_count: usize,
        named_keys: Vec<Symbol>,
        type_args: Vec<(Option<Symbol>, TermId)>,
    },
    Constructor { span: SourceSpan, name: Symbol, pos_count: usize, named_keys: Vec<Symbol> },
    /// `dot_apply(receiver, name, args)` — the receiver is the single child
    /// visited after the args, so it pops last (see `build_frame`).
    DotApply { span: SourceSpan, name: Symbol, pos_count: usize, named_keys: Vec<Symbol> },
    ApplyWithin {
        span: SourceSpan, functor: Symbol,
        pos_count: usize, named_keys: Vec<Symbol>,
        requirements_count: usize,
        type_args: Vec<(Option<Symbol>, TermId)>,
    },
    RequirementAtSort { span: SourceSpan, slot: i64 },
    ConstructRequirement { span: SourceSpan, impl_functor: Symbol, requirements_count: usize },
    ListLit { span: SourceSpan, count: usize },
    SetLit { span: SourceSpan, count: usize },
    TupleLit { span: SourceSpan, count: usize },
    /// Fallback for unknown `Term::Fn` shapes — treated as a generic
    /// Apply with the functor as-is. `pos_count` and `named_keys`
    /// follow the original `Term::Fn` arg arrangement (not the
    /// ApplyArg cons-list shape used by recognised forms).
    UnknownFn { span: SourceSpan, functor: Symbol, pos_count: usize, named_keys: Vec<Symbol> },
}

struct BranchMeta {
    pattern: TermId,
    has_guard: bool,
    span: SourceSpan,
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
            let type_annotation = get_named_arg(kb, named_args, "type_name");
            let value = get_named_arg(kb, named_args, "value");
            let body = get_named_arg(kb, named_args, "body");
            work.push(WorkOp::Build(BuildFrame::Let { span, pattern, type_annotation }));
            push_visit_or_bottom(work, body);
            push_visit_or_bottom(work, value);
        }
        "lambda" => {
            let param = get_named_arg(kb, named_args, "param").unwrap_or(t);
            let body = get_named_arg(kb, named_args, "body");
            work.push(WorkOp::Build(BuildFrame::Lambda { span, param }));
            push_visit_or_bottom(work, body);
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
            let (count, visits) = collect_list_visits(kb, Some(t));
            work.push(WorkOp::Build(BuildFrame::ListLit { span, count }));
            for v in visits.into_iter().rev() { work.push(v); }
        }
        "SetLiteral" => {
            let (count, visits) = collect_list_visits(kb, Some(t));
            work.push(WorkOp::Build(BuildFrame::SetLit { span, count }));
            for v in visits.into_iter().rev() { work.push(v); }
        }
        "TupleLiteral" => {
            let (count, visits) = collect_list_visits(kb, Some(t));
            work.push(WorkOp::Build(BuildFrame::TupleLit { span, count }));
            for v in visits.into_iter().rev() { work.push(v); }
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
fn collect_type_args(
    kb: &KnowledgeBase,
    list_tid: Option<TermId>,
) -> Vec<(Option<Symbol>, TermId)> {
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
            Some((name_opt, value))
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

fn build_frame(frame: BuildFrame, results: &mut Vec<Rc<NodeOccurrence>>) {
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
            let body = results.pop().expect("let: missing body");
            let value = results.pop().expect("let: missing value");
            let expr = Expr::Let { pattern, type_annotation, value, body };
            results.push(NodeOccurrence::new_expr(expr, span, None));
        }
        BuildFrame::Lambda { span, param } => {
            let body = results.pop().expect("lambda: missing body");
            let expr = Expr::Lambda { param, body };
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
                built_branches.push(MatchBranch {
                    pattern: meta.pattern,
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
        BuildFrame::TupleLit { span, count } => {
            let elems = pop_n(results, count);
            let expr = Expr::TupleLit { positional: elems, named: Vec::new() };
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
            | "var_ref" | "if_expr" | "let_expr" | "lambda" | "match_expr"
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
        // can't occur (the old `_`-arm panic).
        let mut symbols = SymbolTable::new();
        let v = symbols.intern("v");
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
        let opened = open_debruijn_node(&if_occ, &fresh);
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
        match open_debruijn_node(&req, &fresh).as_expr().unwrap() {
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
        use crate::kb::term::Var;
        let mut symbols = SymbolTable::new();
        let gt = symbols.intern("gt");
        let xname = symbols.intern("x");
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
        let opened = open_debruijn_node(&atom, &[v0]);
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
        let reopened = open_debruijn_node(&closed, &[v_fresh]);
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
    fn node_to_debruijn_closes_vars_in_termid_pattern_fields() {
        // WI-246 follow-on: a reflect-data `lambda` atom carries its param as a
        // `TermId` (not an occ child). `node_to_debruijn` must close a Global var
        // living there to De Bruijn — via `term_to_debruijn` — so it lands in the
        // rule's De Bruijn key space (e.g. for the typer), matching the prior
        // materialize(term_to_debruijn(t)) path.
        use crate::kb::term::Var;
        let mut kb = KnowledgeBase::new();
        let xname = kb.intern("x");
        let span = make_span();
        let v0 = VarId::new(7, xname);
        // param TermId holds Global(v0); body is a separate occ var leaf.
        let param_tid = kb.alloc(Term::Var(Var::Global(v0)));
        let body = NodeOccurrence::new_expr(Expr::Var(Var::Global(v0)), span, None);
        let lambda = NodeOccurrence::new_expr(Expr::Lambda { param: param_tid, body }, span, None);

        let closed = node_to_debruijn(&mut kb, &lambda, &[v0]);
        match closed.as_expr() {
            Some(Expr::Lambda { param, body }) => {
                assert!(
                    matches!(kb.get_term(*param), Term::Var(Var::DeBruijn(0))),
                    "param TermId var should close to DeBruijn(0), got {:?}",
                    kb.get_term(*param)
                );
                assert!(
                    matches!(body.as_expr(), Some(Expr::Var(Var::DeBruijn(0)))),
                    "body occ var should also close to DeBruijn(0)",
                );
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    #[test]
    fn collect_ordered_picks_up_vars_living_only_in_termid_fields() {
        // WI-246 soundness guard: `node_to_debruijn` closes vars in a reflect-
        // data form's `TermId`-typed param/pattern/type-arg fields, which
        // `for_each_child` never visits. `collect_occurrence_global_vars_ordered`
        // must still collect a var that lives EXCLUSIVELY in such a field —
        // otherwise it would be left a stray Global (escaping per-call
        // freshening) and the rule's arity would undercount it.
        use crate::kb::term::Var;
        let mut kb = KnowledgeBase::new();
        let xname = kb.intern("x");
        let yname = kb.intern("y");
        let span = make_span();

        // A `lambda` whose param holds Global(vx) and whose body mentions only
        // Global(vy) — vx appears nowhere in an occurrence-child position.
        let vx = VarId::new(7, xname);
        let vy = VarId::new(8, yname);
        let param_tid = kb.alloc(Term::Var(Var::Global(vx)));
        let body = NodeOccurrence::new_expr(Expr::Var(Var::Global(vy)), span, None);
        let lambda = NodeOccurrence::new_expr(Expr::Lambda { param: param_tid, body }, span, None);

        let mut vars = Vec::new();
        let mut seen = std::collections::HashSet::new();
        collect_occurrence_global_vars_ordered(&kb, &lambda, &mut vars, &mut seen);

        assert!(vars.contains(&vx), "param-only var vx must be collected, got {vars:?}");
        assert!(vars.contains(&vy), "body var vy must be collected, got {vars:?}");
        // Children walked before TermId fields: vy (occ child) precedes vx (param).
        assert_eq!(vars, vec![vy, vx], "child vars first, then TermId-field vars");

        // And the closing pass then leaves NO stray Global: with vx in var_order,
        // the param closes to a DeBruijn index.
        let closed = node_to_debruijn(&mut kb, &lambda, &vars);
        let Some(Expr::Lambda { param, .. }) = closed.as_expr() else {
            panic!("expected Lambda");
        };
        assert!(
            matches!(kb.get_term(*param), Term::Var(Var::DeBruijn(_))),
            "param var must close to DeBruijn (no stray Global), got {:?}",
            kb.get_term(*param)
        );
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
                type_args: vec![(None, ta_tid)],
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
        subst.bind_value(v0, Value::Int(42));
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

    #[test]
    fn substitute_occurrence_splices_node_in_place() {
        // A var bound to a matched child occurrence (`Value::Node`) is spliced
        // in place, preserving the occurrence's Rc identity (and provenance).
        let mut kb = KnowledgeBase::new();
        let (atom, v0, _gt, _three) = gt_atom(&mut kb);
        let payload = NodeOccurrence::new_expr(Expr::Bottom, make_span(), None);
        let mut subst = Substitution::new();
        subst.bind_value(v0, Value::Node(Rc::clone(&payload)));
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
        subst.bind_value(v0, Value::Term(compound));
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
        subst.bind_value(vy, Value::Int(99)); // bind only the named arg
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
}
