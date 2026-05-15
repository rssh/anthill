/// NodeOccurrence — KB-side positional wrapper for source content.
///
/// Per `docs/design/occurrence-as-value-type.md`. Replaces the arena+ID
/// `OccurrenceStore` model: every child slot in an `Expr` is a
/// `Rc<NodeOccurrence>`, alternating `NodeOccurrence ⇄ NodeKind ⇄ Expr ⇄ NodeOccurrence`
/// all the way down. The tree is `Rc`-linked from the start so reflection
/// bindings are cheap (`Rc::clone`), eval can stash on its frame stack
/// without lifetime threading, and cross-pass identity is `Rc::ptr_eq`.

use std::cell::RefCell;
use std::rc::Rc;

use crate::intern::Symbol;
use crate::span::SourceSpan;

use super::occurrence::OccurrenceId;
pub use super::occurrence::PassId;
use super::term::{HandleKind, Literal, Term, TermId, Var};
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

// ── Materialization from KB-encoded handle tree ─────────────────

/// Materialize the value-typed NodeOccurrence tree rooted at `occ_id`,
/// walking the loader's KB-encoded Handle/Term tree. Used by the loader
/// to populate `kb.op_bodies` after `convert_expr_child` finishes
/// building the Handle-wrapped term tree.
///
/// This is the conversion-boundary helper while the codebase still
/// carries both representations. Once consumer migration finishes, the
/// loader will build NodeOccurrence trees directly and this walker goes
/// away alongside the Handle wrapper.
pub fn materialize_from_occurrence(
    kb: &KnowledgeBase,
    occ_id: OccurrenceId,
) -> Rc<NodeOccurrence> {
    let term_id = kb.occurrence_store().term(occ_id);
    let span = kb.occurrence_store().span(occ_id);
    let owner = kb.occurrence_store().owner(occ_id);
    let expr = expr_from_term(kb, term_id);
    NodeOccurrence::new_expr(expr, span, owner)
}

/// Materialize a NodeOccurrence from a Handle-wrapped term. If the term
/// is not a Handle, falls back to building an Expr around it with a
/// zero/synthetic span — the loader's invariant (post-WI-241) is that
/// every Expr child slot IS a Handle, so the fallback is just defensive.
pub fn materialize_from_handle(
    kb: &KnowledgeBase,
    handle: TermId,
) -> Rc<NodeOccurrence> {
    if let Term::Const(Literal::Handle(HandleKind::Occurrence, raw)) = kb.get_term(handle) {
        return materialize_from_occurrence(kb, OccurrenceId::from_raw(*raw));
    }
    // Fallback for non-Handle terms — wrap with an empty span.
    let expr = expr_from_term(kb, handle);
    let span = SourceSpan::new(crate::span::SourceId::from_raw(0), 0, 0);
    NodeOccurrence::new_expr(expr, span, None)
}

fn expr_from_term(kb: &KnowledgeBase, term_id: TermId) -> Expr {
    let term = kb.get_term(term_id);
    match term {
        Term::Const(lit) => Expr::Const(lit.clone()),
        Term::Var(v) => Expr::Var(*v),
        Term::Ref(s) => Expr::Ref(*s),
        Term::Ident(s) => Expr::Ident(*s),
        Term::Bottom => Expr::Bottom,
        Term::Fn { functor, pos_args, named_args } => {
            let qn = kb.qualified_name_of(*functor);
            match qn {
                // Literal-entity forms — extract the wrapped Literal.
                "anthill.reflect.Expr.int_lit"
                | "anthill.reflect.Expr.float_lit"
                | "anthill.reflect.Expr.bigint_lit"
                | "anthill.reflect.Expr.string_lit"
                | "anthill.reflect.Expr.bool_lit" => {
                    let value_tid = get_named_arg(kb, named_args, "value");
                    match value_tid.map(|t| kb.get_term(t)) {
                        Some(Term::Const(lit)) => Expr::Const(lit.clone()),
                        _ => Expr::Bottom,
                    }
                }
                "anthill.reflect.Expr.var_ref" => {
                    let name = named_ref(kb, named_args, "name");
                    match name {
                        Some(sym) => Expr::VarRef { name: sym },
                        None => Expr::Bottom,
                    }
                }
                "anthill.reflect.Expr.if_expr" => {
                    let cond = handle_child(kb, get_named_arg(kb, named_args, "cond"));
                    let then_branch = handle_child(kb, get_named_arg(kb, named_args, "then_branch"));
                    let else_branch = handle_child(kb, get_named_arg(kb, named_args, "else_branch"));
                    Expr::If { condition: cond, then_branch, else_branch }
                }
                "anthill.reflect.Expr.let_expr" => {
                    let pattern = get_named_arg(kb, named_args, "pattern").unwrap_or(term_id);
                    let value = handle_child(kb, get_named_arg(kb, named_args, "value"));
                    let body = handle_child(kb, get_named_arg(kb, named_args, "body"));
                    let type_annotation = get_named_arg(kb, named_args, "type_name");
                    Expr::Let { pattern, type_annotation, value, body }
                }
                "anthill.reflect.Expr.lambda" => {
                    let param = get_named_arg(kb, named_args, "param").unwrap_or(term_id);
                    let body = handle_child(kb, get_named_arg(kb, named_args, "body"));
                    Expr::Lambda { param, body }
                }
                "anthill.reflect.Expr.match_expr" => {
                    let scrutinee = handle_child(kb, get_named_arg(kb, named_args, "scrutinee"));
                    let branches_tid = get_named_arg(kb, named_args, "branches");
                    let branches = branches_tid
                        .map(|t| materialize_match_branches(kb, t))
                        .unwrap_or_default();
                    Expr::Match { scrutinee, branches }
                }
                "anthill.reflect.Expr.apply" => {
                    let fn_sym = named_ref(kb, named_args, "fn").unwrap_or(*functor);
                    let (pos, named) = materialize_apply_args(kb, get_named_arg(kb, named_args, "args"));
                    Expr::Apply { functor: fn_sym, pos_args: pos, named_args: named }
                }
                "anthill.reflect.Expr.constructor" => {
                    let ctor_sym = named_ref(kb, named_args, "name").unwrap_or(*functor);
                    let (pos, named) = materialize_apply_args(kb, get_named_arg(kb, named_args, "args"));
                    Expr::Constructor { name: ctor_sym, pos_args: pos, named_args: named }
                }
                "anthill.reflect.Expr.apply_within" => {
                    let fn_sym = named_ref(kb, named_args, "fn").unwrap_or(*functor);
                    let (pos, named) = materialize_apply_args(kb, get_named_arg(kb, named_args, "args"));
                    let requirements = materialize_node_list(kb, get_named_arg(kb, named_args, "requirements"));
                    Expr::ApplyWithin {
                        functor: fn_sym,
                        args: pos,
                        named_args: named,
                        requirements,
                    }
                }
                "anthill.reflect.Expr.requirement_at_sort" => {
                    let chain = handle_child(kb, get_named_arg(kb, named_args, "chain"));
                    let slot = get_named_arg(kb, named_args, "slot")
                        .and_then(|t| match kb.get_term(t) {
                            Term::Const(Literal::Int(n)) => Some(*n),
                            _ => None,
                        })
                        .unwrap_or(0);
                    Expr::RequirementAtSort { chain, slot }
                }
                "anthill.reflect.Expr.construct_requirement" => {
                    let impl_functor = named_ref(kb, named_args, "impl_functor").unwrap_or(*functor);
                    let requirements = materialize_node_list(kb, get_named_arg(kb, named_args, "requirements"));
                    Expr::ConstructRequirement { impl_functor, requirements }
                }
                "anthill.reflect.ListLiteral" => {
                    Expr::ListLit(materialize_node_list(kb, Some(term_id)))
                }
                "anthill.reflect.SetLiteral" => {
                    Expr::SetLit(materialize_node_list(kb, Some(term_id)))
                }
                "anthill.reflect.TupleLiteral" => {
                    let nodes = materialize_node_list(kb, Some(term_id));
                    Expr::TupleLit { positional: nodes, named: Vec::new() }
                }
                _ => {
                    // Fallback: any other Fn term — preserve positional + named args
                    // as Apply with the functor as-is. Children that are Handles get
                    // materialized; non-Handle children become Const/Ref leaves.
                    let pos_args: Vec<Rc<NodeOccurrence>> = pos_args
                        .iter()
                        .map(|&t| handle_child(kb, Some(t)))
                        .collect();
                    let named: Vec<(Symbol, Rc<NodeOccurrence>)> = named_args
                        .iter()
                        .map(|&(s, t)| (s, handle_child(kb, Some(t))))
                        .collect();
                    Expr::Apply { functor: *functor, pos_args, named_args: named }
                }
            }
        }
    }
}

/// Materialize a child slot from a `Handle(occ_id)` term. If the slot is
/// not a Handle (defensive), wrap its content with an empty span.
fn handle_child(kb: &KnowledgeBase, slot: Option<TermId>) -> Rc<NodeOccurrence> {
    match slot {
        Some(t) => materialize_from_handle(kb, t),
        None => {
            let span = SourceSpan::new(crate::span::SourceId::from_raw(0), 0, 0);
            NodeOccurrence::new_expr(Expr::Bottom, span, None)
        }
    }
}

/// Walk a `cons(head, tail) | nil` cons-list and materialize each entry
/// as a child NodeOccurrence. Each entry is expected to be a Handle.
fn materialize_node_list(kb: &KnowledgeBase, list_tid: Option<TermId>) -> Vec<Rc<NodeOccurrence>> {
    let Some(tid) = list_tid else { return Vec::new(); };
    list_to_vec(kb, tid)
        .into_iter()
        .map(|h| materialize_from_handle(kb, h))
        .collect()
}

/// Walk a cons-list of `ApplyArg(name, value)` entities, splitting into
/// positional (name=none) and named (name=some(Ref(sym))) buckets.
fn materialize_apply_args(
    kb: &KnowledgeBase,
    list_tid: Option<TermId>,
) -> (Vec<Rc<NodeOccurrence>>, Vec<(Symbol, Rc<NodeOccurrence>)>) {
    let mut pos = Vec::new();
    let mut named = Vec::new();
    let Some(tid) = list_tid else { return (pos, named); };
    for arg_tid in list_to_vec(kb, tid) {
        let Term::Fn { named_args: aa, .. } = kb.get_term(arg_tid) else { continue };
        let node = handle_child(kb, get_named_arg(kb, aa, "value"));
        let arg_name = get_named_arg(kb, aa, "name").and_then(|t| some_name(kb, t));
        match arg_name {
            Some(s) => named.push((s, node)),
            None => pos.push(node),
        }
    }
    (pos, named)
}

/// Walk a cons-list of MatchBranch entities and build MatchBranch values.
fn materialize_match_branches(kb: &KnowledgeBase, list_tid: TermId) -> Vec<MatchBranch> {
    list_to_vec(kb, list_tid)
        .into_iter()
        .filter_map(|br_tid| {
            let Term::Fn { named_args: ba, .. } = kb.get_term(br_tid) else { return None };
            let pattern = get_named_arg(kb, ba, "pattern").unwrap_or(br_tid);
            let body = handle_child(kb, get_named_arg(kb, ba, "body"));
            let guard = get_named_arg(kb, ba, "guard")
                .and_then(|t| unwrap_option(kb, t))
                .map(|inner| materialize_from_handle(kb, inner));
            let span = SourceSpan::new(crate::span::SourceId::from_raw(0), 0, 0);
            Some(MatchBranch { pattern, guard, body, span })
        })
        .collect()
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
