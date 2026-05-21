//! WI-277 — typer-phase `[simp]` rewriting engine.
//!
//! The second firing site for `[simp]` equational rules (proposal 043 /
//! `docs/design/simp-rewrite-design.md`). As a separate pass over operation
//! bodies (before `type_check_sorts`/`req_insertion`), it fires matching
//! `[simp]` equations LHS→RHS bottom-up over the `NodeOccurrence` tree and
//! writes the rewritten, redex-free tree back via `set_op_body_node`. This
//! is the resolver's `apply_eq_rules` (`resolve.rs`) counterpart for the
//! occurrence representation — "one rewriter, two phases."
//!
//! Reuse: matching is the existing discrimination tree via `match_view`
//! (`Rc<NodeOccurrence>` is a `TermView`, WI-276/277); DeBruijn opening is
//! the KB's `term_from_debruijn`. The only occurrence-specific piece is the
//! build side, [`substitute_to_occurrence`], which constructs the RHS as a
//! `NodeOccurrence` (carrying span + `Synthesized` provenance) on top of the
//! shared `walk_view`.
//!
//! Scope (WI-277): guard-free equations (`is_equation` + `[simp]`, empty
//! body) — e.g. `add(?x, 0) = ?x`. Type-directed/guarded dispatch (`dot`,
//! proposal 043 §6) is WI-278.
//!
//! v1 limitation — recursion depth: `rewrite`/`map_children`/
//! `substitute_to_occurrence` recurse over occurrence-tree depth, whereas the
//! sibling `NodeOccurrence::Drop` and the typing pass use explicit work-stacks
//! to survive deeply-nested bodies (the 624-line typing_pass_spec.anthill).
//! The `run` fast-path makes this pass inert until a `[simp]` rule exists, so
//! it cannot overflow today; converting the walk to a work-stack is a
//! prerequisite for WI-278 (which ships rules that fire on real bodies).

use std::rc::Rc;

use crate::eval::value::Value;
use crate::intern::Symbol;

use super::load::meta_has_flag;
use super::node_occurrence::{Expr, MatchBranch, NodeKind, NodeOccurrence, OccurrenceOrigin};
use super::occurrence::PassId;
use super::subst::Substitution;
use super::term::{Literal, Term, TermId, Var, VarId};
use super::{KnowledgeBase, RuleId};

/// Per-node fixpoint bound — mirrors `apply_eq_rules`'s fuel (`resolve.rs`),
/// keeping the two firing sites' termination policy aligned.
const SIMP_FUEL: usize = 100;

const PASS_NAME: &str = "anthill.kb.passes.simp_rewrite";

/// Entry point: rewrite every operation body by firing `[simp]` equations,
/// writing each rewritten (redex-free) tree back into `kb.op_bodies`.
pub fn run(kb: &mut KnowledgeBase) {
    // Fast path: with no `[simp]` equations in the index there is nothing to
    // fire, so skip the whole walk. `by_functor(eq)` holds only indexed
    // (`[simp]`/`[unfold]`) equations post-WI-139, so this is the common case
    // (e.g. every stdlib-only load).
    let eq_sym = kb.intern("eq");
    let has_simp = kb
        .by_functor(eq_sym)
        .into_iter()
        .any(|rid| kb.is_equation(rid) && meta_has_flag(kb, kb.rule_meta(rid), "simp"));
    if !has_simp {
        return;
    }
    let pass = kb.register_pass(PASS_NAME);
    // Snapshot (op_sym, body) so we don't hold a borrow on `op_bodies` while
    // rewriting (which mutates `kb` — fresh vars, interning).
    let bodies: Vec<(Symbol, Rc<NodeOccurrence>)> =
        kb.op_bodies_iter().map(|(s, n)| (s, Rc::clone(n))).collect();
    for (op_sym, body) in bodies {
        let rewritten = rewrite(kb, &body, pass, SIMP_FUEL);
        if !Rc::ptr_eq(&rewritten, &body) {
            kb.set_op_body_node(op_sym, rewritten);
        }
    }
}

/// Bottom-up rewrite: rewrite children first, then try firing a `[simp]`
/// equation at this node; on a firing, re-rewrite the result to fixpoint
/// (fuel-bounded). Leftmost-innermost, matching the typer's walk order and
/// `apply_eq_rules`.
fn rewrite(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    pass: PassId,
    fuel: usize,
) -> Rc<NodeOccurrence> {
    if fuel == 0 {
        return Rc::clone(occ);
    }
    let with_children = map_children(kb, occ, pass, fuel);
    match try_fire(kb, &with_children, pass) {
        Some(fired) => rewrite(kb, &fired, pass, fuel - 1),
        None => with_children,
    }
}

/// Try to fire a `[simp]` equation at this node. Returns the rewritten
/// occurrence, or `None` if no equation matches.
fn try_fire(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    pass: PassId,
) -> Option<Rc<NodeOccurrence>> {
    let node_functor = match occ.as_expr()? {
        Expr::Apply { functor, .. } => *functor,
        Expr::Constructor { name, .. } => *name,
        _ => return None,
    };
    let eq_sym = kb.intern("eq");
    // All equational rule heads are indexed under `eq`; WI-139 keeps only
    // `[simp]`/`[unfold]`-tagged equations in the index. Reuse that index.
    for rid in kb.by_functor(eq_sym) {
        if !kb.is_equation(rid) || !meta_has_flag(kb, kb.rule_meta(rid), "simp") {
            continue;
        }
        // Cheap pre-filter on the stored (DeBruijn) head, before opening.
        if stored_lhs_functor(kb, rid) != Some(node_functor) {
            continue;
        }
        let (lhs, rhs) = match open_equation(kb, rid) {
            Some(pair) => pair,
            None => continue,
        };
        // `occ` is itself a `TermView` (WI-277), so we match the rule LHS
        // against it in place — no `Value::Node` wrapping.
        if let Some(subst) = kb.match_view(lhs, occ) {
            if subst.is_contradiction() {
                continue;
            }
            return Some(substitute_to_occurrence(kb, rhs, &subst, occ, pass));
        }
    }
    None
}

/// The functor of an equation's LHS, read from the *stored* head (no
/// DeBruijn opening). Used to skip non-matching rules before the
/// allocate-heavy `open_equation`.
fn stored_lhs_functor(kb: &KnowledgeBase, rid: RuleId) -> Option<Symbol> {
    let head = kb.rule_head(rid);
    let lhs = match kb.get_term(head) {
        Term::Fn { pos_args, .. } if pos_args.len() == 2 => pos_args[0],
        _ => return None,
    };
    match kb.get_term(lhs) {
        Term::Fn { functor, .. } => Some(*functor),
        _ => None,
    }
}

/// Open an equation's DeBruijn vars to fresh globals and return its
/// `(lhs, rhs)` as matchable/buildable terms. Uses the KB's
/// `term_from_debruijn` (the same opener `with_fresh_vars` uses) — not a
/// reimplementation of the resolver's rule-opening.
fn open_equation(kb: &mut KnowledgeBase, rid: RuleId) -> Option<(TermId, TermId)> {
    let arity = kb.rule_arity(rid);
    let head = kb.rule_head(rid);
    let opened = if arity > 0 {
        let name = kb.intern("_");
        let fresh: Vec<VarId> = (0..arity).map(|_| kb.fresh_var(name)).collect();
        kb.term_from_debruijn(head, &fresh)
    } else {
        head
    };
    match kb.get_term(opened) {
        Term::Fn { pos_args, .. } if pos_args.len() == 2 => Some((pos_args[0], pos_args[1])),
        _ => None,
    }
}

/// Build the RHS as a fresh `NodeOccurrence`, resolving rule variables to
/// their matched bindings via the shared `walk_view`. A variable bound to a
/// matched child occurrence (`Value::Node`) is reused in place (identity
/// preserved); a functor builds a synthesized `Apply`; a literal builds a
/// `Const`. New nodes carry `origin: Synthesized { from, by }`.
fn substitute_to_occurrence(
    kb: &KnowledgeBase,
    term: TermId,
    subst: &Substitution,
    from: &Rc<NodeOccurrence>,
    pass: PassId,
) -> Rc<NodeOccurrence> {
    let synth = |expr: Expr| NodeOccurrence::synthesized_expr(expr, Rc::clone(from), pass, from.owner);
    match kb.walk_view(term, subst) {
        // Reused matched child — keep its identity (and provenance).
        Value::Node(occ) => occ,
        Value::Term(t) => match kb.get_term(t) {
            Term::Fn { functor, pos_args, named_args } => {
                let functor = *functor;
                let pos: Vec<_> = pos_args
                    .iter()
                    .map(|&c| substitute_to_occurrence(kb, c, subst, from, pass))
                    .collect();
                let named: Vec<_> = named_args
                    .iter()
                    .map(|&(s, c)| (s, substitute_to_occurrence(kb, c, subst, from, pass)))
                    .collect();
                synth(Expr::Apply { functor, pos_args: pos, named_args: named, type_args: Vec::new() })
            }
            Term::Const(lit) => synth(Expr::Const(lit.clone())),
            Term::Ref(s) => synth(Expr::Ref(*s)),
            Term::Ident(s) => synth(Expr::Ident(*s)),
            // An unbound RHS var or `⊥` yields `⊥`; a well-formed `[simp]`
            // rule binds every RHS var, so the post-rewrite type-check
            // surfaces any genuinely unbound case as an error.
            _ => synth(Expr::Bottom),
        },
        Value::Int(n) => synth(Expr::Const(Literal::Int(n))),
        Value::BigInt(n) => synth(Expr::Const(Literal::BigInt(n))),
        Value::Float(f) => synth(Expr::Const(Literal::Float(ordered_float::OrderedFloat(f)))),
        Value::Bool(b) => synth(Expr::Const(Literal::Bool(b))),
        Value::Str(s) => synth(Expr::Const(Literal::String(s.to_string()))),
        // Tuple/Entity/closures/etc. are not expected as a structural RHS
        // binding in WI-277; leave a `⊥` for the type-check to flag.
        _ => synth(Expr::Bottom),
    }
}

// ── child rewriting (bottom-up reconstruction) ─────────────────────
//
// Non-destructive analog of `node_occurrence::drain_expr_children`: rewrite
// each direct child, and rebuild the node only if some child changed
// (`Rc::ptr_eq`), preserving span/owner. Post-elaboration forms (`*Within`,
// requirement projections, `var_ref`) don't occur before `type_check_sorts`,
// so they (and the leaves) pass through unchanged.

fn rewrite_one(
    kb: &mut KnowledgeBase,
    child: &Rc<NodeOccurrence>,
    pass: PassId,
    fuel: usize,
) -> (Rc<NodeOccurrence>, bool) {
    let r = rewrite(kb, child, pass, fuel);
    let changed = !Rc::ptr_eq(&r, child);
    (r, changed)
}

fn rewrite_vec(
    kb: &mut KnowledgeBase,
    items: &[Rc<NodeOccurrence>],
    pass: PassId,
    fuel: usize,
) -> (Vec<Rc<NodeOccurrence>>, bool) {
    let mut changed = false;
    let out = items
        .iter()
        .map(|c| {
            let (r, c1) = rewrite_one(kb, c, pass, fuel);
            changed |= c1;
            r
        })
        .collect();
    (out, changed)
}

fn rewrite_named(
    kb: &mut KnowledgeBase,
    items: &[(Symbol, Rc<NodeOccurrence>)],
    pass: PassId,
    fuel: usize,
) -> (Vec<(Symbol, Rc<NodeOccurrence>)>, bool) {
    let mut changed = false;
    let out = items
        .iter()
        .map(|(s, c)| {
            let (r, c1) = rewrite_one(kb, c, pass, fuel);
            changed |= c1;
            (*s, r)
        })
        .collect();
    (out, changed)
}

fn map_children(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    pass: PassId,
    fuel: usize,
) -> Rc<NodeOccurrence> {
    let expr = match occ.as_expr() {
        Some(e) => e,
        None => return Rc::clone(occ),
    };
    let rebuilt: Option<Expr> = match expr {
        Expr::Apply { functor, pos_args, named_args, type_args } => {
            let (pos, c1) = rewrite_vec(kb, pos_args, pass, fuel);
            let (named, c2) = rewrite_named(kb, named_args, pass, fuel);
            (c1 || c2).then(|| Expr::Apply {
                functor: *functor,
                pos_args: pos,
                named_args: named,
                type_args: type_args.clone(),
            })
        }
        Expr::Constructor { name, pos_args, named_args } => {
            let (pos, c1) = rewrite_vec(kb, pos_args, pass, fuel);
            let (named, c2) = rewrite_named(kb, named_args, pass, fuel);
            (c1 || c2).then(|| Expr::Constructor { name: *name, pos_args: pos, named_args: named })
        }
        Expr::Instantiation { name, pos_args, named_args } => {
            let (pos, c1) = rewrite_vec(kb, pos_args, pass, fuel);
            let (named, c2) = rewrite_named(kb, named_args, pass, fuel);
            (c1 || c2).then(|| Expr::Instantiation { name: *name, pos_args: pos, named_args: named })
        }
        Expr::HoApply { predicate, args } => {
            let (pred, c1) = rewrite_one(kb, predicate, pass, fuel);
            let (a, c2) = rewrite_vec(kb, args, pass, fuel);
            (c1 || c2).then(|| Expr::HoApply { predicate: pred, args: a })
        }
        Expr::If { condition, then_branch, else_branch } => {
            let (c, c1) = rewrite_one(kb, condition, pass, fuel);
            let (t, c2) = rewrite_one(kb, then_branch, pass, fuel);
            let (e, c3) = rewrite_one(kb, else_branch, pass, fuel);
            (c1 || c2 || c3).then(|| Expr::If { condition: c, then_branch: t, else_branch: e })
        }
        Expr::Let { pattern, type_annotation, value, body } => {
            let (v, c1) = rewrite_one(kb, value, pass, fuel);
            let (b, c2) = rewrite_one(kb, body, pass, fuel);
            (c1 || c2).then(|| Expr::Let {
                pattern: *pattern,
                type_annotation: *type_annotation,
                value: v,
                body: b,
            })
        }
        Expr::Lambda { param, body } => {
            let (b, c1) = rewrite_one(kb, body, pass, fuel);
            c1.then(|| Expr::Lambda { param: *param, body: b })
        }
        Expr::Match { scrutinee, branches } => {
            let (scr, c1) = rewrite_one(kb, scrutinee, pass, fuel);
            let mut c2 = false;
            let new_branches: Vec<MatchBranch> = branches
                .iter()
                .map(|br| {
                    let (body, cb) = rewrite_one(kb, &br.body, pass, fuel);
                    let guard = br.guard.as_ref().map(|g| {
                        let (gr, cg) = rewrite_one(kb, g, pass, fuel);
                        c2 |= cg;
                        gr
                    });
                    c2 |= cb;
                    MatchBranch { pattern: br.pattern, guard, body, span: br.span }
                })
                .collect();
            (c1 || c2).then(|| Expr::Match { scrutinee: scr, branches: new_branches })
        }
        Expr::ListLit(es) => {
            let (e, c1) = rewrite_vec(kb, es, pass, fuel);
            c1.then(|| Expr::ListLit(e))
        }
        Expr::SetLit(es) => {
            let (e, c1) = rewrite_vec(kb, es, pass, fuel);
            c1.then(|| Expr::SetLit(e))
        }
        Expr::TupleLit { positional, named } => {
            let (pos, c1) = rewrite_vec(kb, positional, pass, fuel);
            let (nm, c2) = rewrite_named(kb, named, pass, fuel);
            (c1 || c2).then(|| Expr::TupleLit { positional: pos, named: nm })
        }
        // Leaves and post-elaboration forms: nothing to rewrite into.
        _ => None,
    };
    let new_expr = match rebuilt {
        Some(e) => e,
        None => return Rc::clone(occ),
    };
    // Preserve provenance: if this node was itself synthesized by an earlier
    // firing in this run, keep its `Synthesized { from, by }` when a child is
    // rewritten under it (rather than reverting to `Source`).
    match &occ.kind {
        NodeKind::Expr { origin: OccurrenceOrigin::Synthesized { from, by }, .. } => {
            NodeOccurrence::synthesized_expr(new_expr, Rc::clone(from), *by, occ.owner)
        }
        _ => NodeOccurrence::new_expr(new_expr, occ.span, occ.owner),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::span::{SourceId, SourceSpan};
    use smallvec::SmallVec;

    /// Build the `[simp]` equation `eq(add(?x, 0), ?x)` head + `[simp]` meta,
    /// returning `(eq_head, meta, add_sym)` without asserting.
    fn build_add_zero(kb: &mut KnowledgeBase) -> (TermId, TermId, Symbol) {
        let eq_sym = kb.intern("eq");
        let add = kb.intern("add");
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let zero = kb.alloc(Term::Const(Literal::Int(0)));
        let lhs = kb.alloc(Term::Fn {
            functor: add,
            pos_args: SmallVec::from_slice(&[var_x, zero]),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[lhs, var_x]),
            named_args: SmallVec::new(),
        });
        let simp_sym = kb.intern("simp");
        let meta_sym = kb.intern("meta");
        let tru = kb.alloc(Term::Const(Literal::Bool(true)));
        let meta = kb.alloc(Term::Fn {
            functor: meta_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(simp_sym, tru)]),
        });
        (eq_head, meta, add)
    }

    /// Assert `add_zero` as a ground-headed fact (Global vars, arity 0 — the
    /// minimal shape, like `simplify_variable_equation`).
    fn assert_add_zero(kb: &mut KnowledgeBase) -> Symbol {
        let (eq_head, meta, add) = build_add_zero(kb);
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        kb.assert_fact(eq_head, sort, domain, Some(meta));
        add
    }

    /// Assert `add_zero` via the DeBruijn path (`assert_rule_debruijn`, arity
    /// > 0) — the shape real `[simp]` rules take after loading. Exercises
    /// `open_equation`'s `term_from_debruijn` branch.
    fn assert_add_zero_db(kb: &mut KnowledgeBase) -> Symbol {
        let (eq_head, meta, add) = build_add_zero(kb);
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        kb.assert_rule_debruijn(eq_head, vec![], sort, domain, Some(meta));
        add
    }

    fn span() -> SourceSpan {
        SourceSpan::new(SourceId::from_raw(0), 0, 10)
    }

    #[test]
    fn guard_free_simp_rule_rewrites_op_body() {
        let mut kb = KnowledgeBase::new();
        let add = assert_add_zero(&mut kb);

        // op body: add(7, 0)
        let seven = NodeOccurrence::new_expr(Expr::Const(Literal::Int(7)), span(), None);
        let zero_occ = NodeOccurrence::new_expr(Expr::Const(Literal::Int(0)), span(), None);
        let body = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: add,
                pos_args: vec![Rc::clone(&seven), zero_occ],
                named_args: vec![],
                type_args: vec![],
            },
            span(),
            None,
        );
        let foo = kb.intern("foo");
        kb.set_op_body_node(foo, Rc::clone(&body));

        run(&mut kb);

        let rewritten = kb.op_body_node(foo).expect("op body present");
        // add(7, 0) fired add_zero → ?x, i.e. the reused `7` child occurrence.
        assert!(
            matches!(rewritten.as_expr(), Some(Expr::Const(Literal::Int(7)))),
            "expected Const(7), got {:?}",
            rewritten.as_expr()
        );
        assert!(
            Rc::ptr_eq(rewritten, &seven),
            "rewritten body should reuse the matched `7` child occurrence (identity preserved)"
        );
    }

    #[test]
    fn nested_redex_rewrites_and_parent_rebuilds() {
        let mut kb = KnowledgeBase::new();
        let add = assert_add_zero(&mut kb);
        let wrap = kb.intern("wrap");

        // op body: wrap(add(7, 0)) — the redex is nested; the parent `wrap`
        // must be rebuilt with the rewritten child.
        let seven = NodeOccurrence::new_expr(Expr::Const(Literal::Int(7)), span(), None);
        let zero_occ = NodeOccurrence::new_expr(Expr::Const(Literal::Int(0)), span(), None);
        let inner = NodeOccurrence::new_expr(
            Expr::Apply { functor: add, pos_args: vec![Rc::clone(&seven), zero_occ], named_args: vec![], type_args: vec![] },
            span(),
            None,
        );
        let body = NodeOccurrence::new_expr(
            Expr::Apply { functor: wrap, pos_args: vec![inner], named_args: vec![], type_args: vec![] },
            span(),
            None,
        );
        let foo = kb.intern("foo");
        kb.set_op_body_node(foo, body);

        run(&mut kb);

        let rewritten = kb.op_body_node(foo).expect("op body present");
        match rewritten.as_expr() {
            Some(Expr::Apply { functor, pos_args, .. }) => {
                assert_eq!(*functor, wrap);
                assert_eq!(pos_args.len(), 1);
                assert!(
                    matches!(pos_args[0].as_expr(), Some(Expr::Const(Literal::Int(7)))),
                    "inner add(7,0) should have rewritten to 7"
                );
                assert!(Rc::ptr_eq(&pos_args[0], &seven));
            }
            other => panic!("expected wrap(7), got {other:?}"),
        }
    }

    #[test]
    fn typer_and_resolver_phases_agree() {
        // The same `[simp]` rule reduces add(7, 0) → 7 in BOTH the resolver
        // (term, via simplify/apply_eq_rules) and the typer phase (occurrence,
        // via run) — the phase-agreement invariant (proposal 043 §4.7).
        let mut kb = KnowledgeBase::new();
        let add = assert_add_zero(&mut kb);

        // Resolver phase: simplify the term add(7, 0).
        let seven_t = kb.alloc(Term::Const(Literal::Int(7)));
        let zero_t = kb.alloc(Term::Const(Literal::Int(0)));
        let add_t = kb.alloc(Term::Fn {
            functor: add,
            pos_args: SmallVec::from_slice(&[seven_t, zero_t]),
            named_args: SmallVec::new(),
        });
        assert_eq!(kb.simplify(add_t), seven_t, "resolver phase: add(7,0) → 7");

        // Typer phase: rewrite the occurrence add(7, 0).
        let seven_o = NodeOccurrence::new_expr(Expr::Const(Literal::Int(7)), span(), None);
        let zero_o = NodeOccurrence::new_expr(Expr::Const(Literal::Int(0)), span(), None);
        let body = NodeOccurrence::new_expr(
            Expr::Apply { functor: add, pos_args: vec![Rc::clone(&seven_o), zero_o], named_args: vec![], type_args: vec![] },
            span(),
            None,
        );
        let foo = kb.intern("foo");
        kb.set_op_body_node(foo, body);
        run(&mut kb);

        let rewritten = kb.op_body_node(foo).expect("op body present");
        assert!(
            matches!(rewritten.as_expr(), Some(Expr::Const(Literal::Int(7)))),
            "typer phase: add(7,0) → 7, got {:?}",
            rewritten.as_expr()
        );
    }

    #[test]
    fn debruijn_simp_rule_rewrites_op_body() {
        // Real-world shape: a `[simp]` rule stored with DeBruijn vars
        // (`assert_rule_debruijn`, as the loader produces) still fires —
        // `open_equation` opens it via `term_from_debruijn`.
        let mut kb = KnowledgeBase::new();
        let add = assert_add_zero_db(&mut kb);

        let seven = NodeOccurrence::new_expr(Expr::Const(Literal::Int(7)), span(), None);
        let zero_occ = NodeOccurrence::new_expr(Expr::Const(Literal::Int(0)), span(), None);
        let body = NodeOccurrence::new_expr(
            Expr::Apply { functor: add, pos_args: vec![Rc::clone(&seven), zero_occ], named_args: vec![], type_args: vec![] },
            span(),
            None,
        );
        let foo = kb.intern("foo");
        kb.set_op_body_node(foo, body);

        run(&mut kb);

        let rewritten = kb.op_body_node(foo).expect("op body present");
        assert!(
            matches!(rewritten.as_expr(), Some(Expr::Const(Literal::Int(7)))),
            "DeBruijn [simp] rule: add(7,0) → 7, got {:?}",
            rewritten.as_expr()
        );
        assert!(Rc::ptr_eq(rewritten, &seven));
    }

    #[test]
    fn multi_step_rewrite_reaches_fixpoint_and_preserves_synthesized_origin() {
        // Two rules: f(?y) = g(add(?y, 0))  and  add(?x, 0) = ?x.
        // f(7) fires → synthesized g(add(7,0)); the engine re-rewrites that to
        // fixpoint → add(7,0) fires → g(7). The g node was synthesized, then
        // rebuilt when its child changed: it must keep its Synthesized origin.
        let mut kb = KnowledgeBase::new();
        let add = assert_add_zero(&mut kb);
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");
        let f = kb.intern("f");
        let g = kb.intern("g");
        let y_sym = kb.intern("y");
        let vy = kb.fresh_var(y_sym);
        let var_y = kb.alloc(Term::Var(Var::Global(vy)));
        let zero = kb.alloc(Term::Const(Literal::Int(0)));
        let add_y0 = kb.alloc(Term::Fn { functor: add, pos_args: SmallVec::from_slice(&[var_y, zero]), named_args: SmallVec::new() });
        let g_add = kb.alloc(Term::Fn { functor: g, pos_args: SmallVec::from_elem(add_y0, 1), named_args: SmallVec::new() });
        let f_y = kb.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(var_y, 1), named_args: SmallVec::new() });
        let eq_head = kb.alloc(Term::Fn { functor: eq_sym, pos_args: SmallVec::from_slice(&[f_y, g_add]), named_args: SmallVec::new() });
        let meta = {
            let simp_sym = kb.intern("simp");
            let meta_sym = kb.intern("meta");
            let tru = kb.alloc(Term::Const(Literal::Bool(true)));
            kb.alloc(Term::Fn { functor: meta_sym, pos_args: SmallVec::new(), named_args: SmallVec::from_slice(&[(simp_sym, tru)]) })
        };
        kb.assert_fact(eq_head, sort, domain, Some(meta));

        let seven = NodeOccurrence::new_expr(Expr::Const(Literal::Int(7)), span(), None);
        let body = NodeOccurrence::new_expr(
            Expr::Apply { functor: f, pos_args: vec![seven], named_args: vec![], type_args: vec![] },
            span(),
            None,
        );
        let foo = kb.intern("foo");
        kb.set_op_body_node(foo, body);

        run(&mut kb);

        let rewritten = kb.op_body_node(foo).expect("op body present");
        match rewritten.as_expr() {
            Some(Expr::Apply { functor, pos_args, .. }) => {
                assert_eq!(*functor, g, "f(7) should reduce to g(...)");
                assert!(
                    matches!(pos_args[0].as_expr(), Some(Expr::Const(Literal::Int(7)))),
                    "g's child add(7,0) should have reduced to 7 (fixpoint)"
                );
            }
            other => panic!("expected g(7), got {other:?}"),
        }
        assert!(
            matches!(&rewritten.kind, NodeKind::Expr { origin: OccurrenceOrigin::Synthesized { .. }, .. }),
            "the rebuilt g node should keep its Synthesized origin"
        );
    }
}
