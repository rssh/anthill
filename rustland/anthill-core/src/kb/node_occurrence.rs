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
use super::term::{Literal, Term, TermId, Var};
use super::typing::{get_named_arg, list_to_vec, unwrap_option};
use super::KnowledgeBase;

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

impl NodeOccurrence {
    /// Build a source-origin expression occurrence.
    pub fn new_expr(expr: Expr, span: SourceSpan, owner: Option<Symbol>) -> Rc<Self> {
        Rc::new(NodeOccurrence {
            kind: NodeKind::Expr {
                expr,
                origin: OccurrenceOrigin::Source,
                classification: RefCell::new(None),
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
pub fn visit_classifications(
    occ: &Rc<NodeOccurrence>,
    visit: &mut impl FnMut(&Rc<NodeOccurrence>, &super::typing::CallClass),
) {
    let NodeKind::Expr { expr, classification, .. } = &occ.kind else {
        return;
    };
    if let Some(c) = classification.borrow().as_deref() {
        visit(occ, c);
    }
    match expr {
        Expr::Apply { pos_args, named_args, .. }
        | Expr::Constructor { pos_args, named_args, .. } => {
            for c in pos_args.iter() { visit_classifications(c, visit); }
            for (_, c) in named_args.iter() { visit_classifications(c, visit); }
        }
        Expr::If { condition, then_branch, else_branch } => {
            visit_classifications(condition, visit);
            visit_classifications(then_branch, visit);
            visit_classifications(else_branch, visit);
        }
        Expr::Let { value, body, .. } => {
            visit_classifications(value, visit);
            visit_classifications(body, visit);
        }
        Expr::Match { scrutinee, branches } => {
            visit_classifications(scrutinee, visit);
            for b in branches.iter() {
                visit_classifications(&b.body, visit);
                if let Some(g) = &b.guard {
                    visit_classifications(g, visit);
                }
            }
        }
        Expr::Lambda { body, .. } => visit_classifications(body, visit),
        Expr::ListLit(es) | Expr::SetLit(es) => {
            for e in es.iter() { visit_classifications(e, visit); }
        }
        Expr::TupleLit { positional, named } => {
            for e in positional.iter() { visit_classifications(e, visit); }
            for (_, e) in named.iter() { visit_classifications(e, visit); }
        }
        Expr::HoApply { predicate, args } => {
            visit_classifications(predicate, visit);
            for a in args.iter() { visit_classifications(a, visit); }
        }
        Expr::ApplyWithin { args, named_args, requirements, .. } => {
            for a in args.iter() { visit_classifications(a, visit); }
            for (_, a) in named_args.iter() { visit_classifications(a, visit); }
            for r in requirements.iter() { visit_classifications(r, visit); }
        }
        Expr::HoApplyWithin { predicate, args, requirements } => {
            visit_classifications(predicate, visit);
            for a in args.iter() { visit_classifications(a, visit); }
            for r in requirements.iter() { visit_classifications(r, visit); }
        }
        Expr::ConstructorWithin { pos_args, named_args, requirements, .. } => {
            for c in pos_args.iter() { visit_classifications(c, visit); }
            for (_, c) in named_args.iter() { visit_classifications(c, visit); }
            for r in requirements.iter() { visit_classifications(r, visit); }
        }
        Expr::LambdaWithin { body, requirements, .. } => {
            visit_classifications(body, visit);
            for r in requirements.iter() { visit_classifications(r, visit); }
        }
        Expr::Instantiation { pos_args, named_args, .. } => {
            for c in pos_args.iter() { visit_classifications(c, visit); }
            for (_, c) in named_args.iter() { visit_classifications(c, visit); }
        }
        Expr::RequirementAtSort { chain, .. } => visit_classifications(chain, visit),
        Expr::ConstructRequirement { requirements, .. } => {
            for r in requirements.iter() { visit_classifications(r, visit); }
        }
        Expr::Const(_) | Expr::Ref(_) | Expr::Ident(_)
        | Expr::Var(_) | Expr::Bottom | Expr::VarRef { .. } => {}
    }
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
    Apply { span: SourceSpan, functor: Symbol, pos_count: usize, named_keys: Vec<Symbol> },
    Constructor { span: SourceSpan, name: Symbol, pos_count: usize, named_keys: Vec<Symbol> },
    ApplyWithin {
        span: SourceSpan, functor: Symbol,
        pos_count: usize, named_keys: Vec<Symbol>,
        requirements_count: usize,
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
            let lit_term = get_named_arg(kb, named_args, "value").map(|v| kb.get_term(v));
            let expr = match lit_term {
                Some(Term::Const(lit)) => Expr::Const(lit.clone()),
                _ => Expr::Bottom,
            };
            results.push(NodeOccurrence::new_expr(expr, span, None));
        }
        "var_ref" => {
            let expr = match named_ref(kb, named_args, "name") {
                Some(sym) => Expr::VarRef { name: sym },
                None => Expr::Bottom,
            };
            results.push(NodeOccurrence::new_expr(expr, span, None));
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
            push_apply_like_args(
                kb, args_tid,
                |span_, pos_count, named_keys| {
                    BuildFrame::Apply { span: span_, functor: fn_sym, pos_count, named_keys }
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
        "apply_within" => {
            let fn_sym = named_ref(kb, named_args, "fn").unwrap_or(functor);
            let args_tid = get_named_arg(kb, named_args, "args");
            let reqs_tid = get_named_arg(kb, named_args, "requirements");
            // First collect args + requirements into reversed visit
            // slots, then push Build with the right counts.
            let (pos_count, named_keys, arg_visits) = collect_apply_arg_visits(kb, args_tid);
            let (req_count, req_visits) = collect_list_visits(kb, reqs_tid);
            work.push(WorkOp::Build(BuildFrame::ApplyWithin {
                span, functor: fn_sym, pos_count, named_keys,
                requirements_count: req_count,
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
        _ => {
            // Fallback for unknown Fn — walk pos_args + named_args
            // as a generic Apply with the functor as-is. Children get
            // visited (rather than collapsed into Const/Ref leaves),
            // so non-Const inner terms still produce NodeOccurrences.
            let pos_count = pos_args.len();
            let named_keys: Vec<Symbol> = named_args.iter().map(|(s, _)| *s).collect();
            work.push(WorkOp::Build(BuildFrame::UnknownFn {
                span, functor, pos_count, named_keys,
            }));
            for &(_, v) in named_args.iter().rev() {
                work.push(WorkOp::Visit(v));
            }
            for &v in pos_args.iter().rev() {
                work.push(WorkOp::Visit(v));
            }
        }
    }
    let _ = results; // kept in case future variants want direct push
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
        BuildFrame::Apply { span, functor, pos_count, named_keys } => {
            let (pos_args, named_args) = pop_apply_like(results, pos_count, named_keys);
            let expr = Expr::Apply { functor, pos_args, named_args };
            results.push(NodeOccurrence::new_expr(expr, span, None));
        }
        BuildFrame::Constructor { span, name, pos_count, named_keys } => {
            let (pos_args, named_args) = pop_apply_like(results, pos_count, named_keys);
            let expr = Expr::Constructor { name, pos_args, named_args };
            results.push(NodeOccurrence::new_expr(expr, span, None));
        }
        BuildFrame::ApplyWithin {
            span, functor, pos_count, named_keys, requirements_count,
        } => {
            // results stack (top → bottom):
            //   req_{R-1}, ..., req_0, named_{N-1}, ..., named_0, pos_{P-1}, ..., pos_0
            let mut requirements: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(requirements_count);
            for _ in 0..requirements_count {
                requirements.push(results.pop().expect("apply_within: missing requirement"));
            }
            requirements.reverse();
            let (pos_args, named_args) = pop_apply_like(results, pos_count, named_keys);
            let expr = Expr::ApplyWithin { functor, args: pos_args, named_args, requirements };
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
            let expr = Expr::Apply { functor, pos_args, named_args };
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
