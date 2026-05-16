//! WI-231 — requirement-insertion pass.
//!
//! Per `docs/design/operation-call-model.md` §"Pass structure: typer
//! first, requirement-insertion separate", the typer and the IR
//! elaboration step are distinct passes. The typer walks bodies and
//! *tags* each spec-op apply site's `NodeOccurrence` with a
//! `CallClass` on its `RefCell`. This pass consumes those
//! classifications and emits the corresponding IR rewrites into
//! `kb.dispatch_rewrites`.
//!
//! WI-251: source-of-truth for classifications moved from the legacy
//! `OccurrenceStore.classifications` side-table to the
//! `NodeOccurrence`'s own RefCell. This pass walks `kb.op_bodies`
//! trees to collect tagged occurrences, then re-builds a TermId-form
//! apply (with the right functor + args) so the existing
//! `record_apply_*` helpers can populate `dispatch_rewrites` and
//! `dispatch_origin` — reflection / proof tooling that inspects the
//! elaborated Term shape keeps working. Runtime reads CallClass
//! directly off the NodeOccurrence (post-WI-248) so the term-keyed
//! redirect is now diagnostic-only.

use std::collections::HashMap;
use std::rc::Rc;

use smallvec::SmallVec;

use crate::intern::Symbol;
use crate::kb::node_occurrence::{Expr, NodeKind, NodeOccurrence};
use crate::kb::term::{Term, TermId};
use crate::kb::typing::{
    record_apply_rewrite, record_apply_within_concrete,
    record_apply_within_rewrite, requires_chain, CallClass, RequiresEntry,
};
use crate::kb::KnowledgeBase;

/// WI-231 — entry point: walk every operation body in `kb.op_bodies`,
/// find classified Apply occurrences, and emit the corresponding IR
/// rewrite. Idempotent: re-running on a kb where rewrites already
/// exist is a no-op (the `record_*` helpers check
/// `kb.dispatch_rewrites.contains_key` before emitting).
pub fn run(kb: &mut KnowledgeBase) {
    // Collect into Vecs so we don't hold a borrow on `kb.op_bodies`
    // while emitting (each `record_*` mutates `kb.dispatch_rewrites`).
    let body_roots: Vec<Rc<NodeOccurrence>> =
        kb.op_bodies_iter().map(|(_, b)| b.clone()).collect();
    let mut raw_entries: Vec<RawClassified> = Vec::new();
    for root in &body_roots {
        collect_classified(root, &mut raw_entries);
    }

    // Materialize each classified Apply into a Term::Fn apply that
    // the existing `record_*` helpers can act on. Each helper rewrites
    // the synthesized apply (replacing the `fn` slot with the impl
    // symbol) and inserts the (rewritten → spec_op_sym) pair into
    // `dispatch_origin`, which is what tooling and the WI-218 tests
    // observe.
    let entries: Vec<ClassifiedApply> = raw_entries
        .into_iter()
        .map(|raw| materialize_apply(kb, raw))
        .collect();

    let mut chain_cache: HashMap<Symbol, Vec<RequiresEntry>> = HashMap::new();

    for entry in entries {
        let ClassifiedApply { apply_term, named_args, pos_args, class } = entry;
        match class {
            CallClass::PinNow { spec_op_sym, impl_op_sym } => {
                record_apply_rewrite(
                    kb, apply_term, &named_args, &pos_args,
                    spec_op_sym, impl_op_sym,
                );
            }
            CallClass::ConcreteApplyWithin {
                fn_target_sym,
                callee_spec_sort,
                spec_op_sym,
                enclosing_sort,
                resolved_tree,
                ..
            } => {
                let caller_requires = chain_for(kb, &mut chain_cache, enclosing_sort);
                record_apply_within_concrete(
                    kb, apply_term, &named_args, &pos_args,
                    fn_target_sym, callee_spec_sort, spec_op_sym,
                    enclosing_sort, &caller_requires, resolved_tree.as_ref(),
                );
            }
            CallClass::DeferToRequirement { spec_op_sym, slot, enclosing_sort, .. } => {
                record_apply_within_rewrite(
                    kb, apply_term, &named_args, &pos_args,
                    spec_op_sym, enclosing_sort, slot,
                );
            }
        }
    }
}

/// Pre-materialization: the apply's structural identity plus the
/// already-clone'd `CallClass` payload. Held in a Vec so we can drop
/// the immutable borrow on `kb.op_bodies` before allocating fresh
/// Term::Fn shapes for the helpers.
struct RawClassified {
    /// Apply functor — the `fn` symbol the typer was looking at.
    functor: Symbol,
    class: CallClass,
}

struct ClassifiedApply {
    apply_term: TermId,
    named_args: SmallVec<[(Symbol, TermId); 2]>,
    pos_args: SmallVec<[TermId; 4]>,
    class: CallClass,
}

/// Walk a body NodeOccurrence tree, pushing one `RawClassified` per
/// Apply whose `classification` RefCell is set. Children are walked
/// irrespective of classification — a deeply-nested classified apply
/// is still emitted.
fn collect_classified(
    occ: &Rc<NodeOccurrence>,
    out: &mut Vec<RawClassified>,
) {
    let NodeKind::Expr { expr, classification, .. } = &occ.kind else {
        return;
    };
    if let Expr::Apply { functor, .. } = expr {
        if let Some(class) = classification.borrow().as_deref() {
            out.push(RawClassified {
                functor: *functor,
                class: class.clone(),
            });
        }
    }
    walk_children(expr, out);
}

fn walk_children(expr: &Expr, out: &mut Vec<RawClassified>) {
    match expr {
        Expr::Apply { pos_args, named_args, .. }
        | Expr::Constructor { pos_args, named_args, .. } => {
            for c in pos_args.iter() { collect_classified(c, out); }
            for (_, c) in named_args.iter() { collect_classified(c, out); }
        }
        Expr::If { condition, then_branch, else_branch } => {
            collect_classified(condition, out);
            collect_classified(then_branch, out);
            collect_classified(else_branch, out);
        }
        Expr::Let { value, body, .. } => {
            collect_classified(value, out);
            collect_classified(body, out);
        }
        Expr::Match { scrutinee, branches } => {
            collect_classified(scrutinee, out);
            for b in branches.iter() {
                collect_classified(&b.body, out);
                if let Some(g) = &b.guard {
                    collect_classified(g, out);
                }
            }
        }
        Expr::Lambda { body, .. } => collect_classified(body, out),
        Expr::ListLit(es) | Expr::SetLit(es) => {
            for e in es.iter() { collect_classified(e, out); }
        }
        Expr::TupleLit { positional, named } => {
            for e in positional.iter() { collect_classified(e, out); }
            for (_, e) in named.iter() { collect_classified(e, out); }
        }
        Expr::HoApply { predicate, args } => {
            collect_classified(predicate, out);
            for a in args.iter() { collect_classified(a, out); }
        }
        Expr::ApplyWithin { args, named_args, requirements, .. } => {
            for a in args.iter() { collect_classified(a, out); }
            for (_, a) in named_args.iter() { collect_classified(a, out); }
            for r in requirements.iter() { collect_classified(r, out); }
        }
        Expr::HoApplyWithin { predicate, args, requirements } => {
            collect_classified(predicate, out);
            for a in args.iter() { collect_classified(a, out); }
            for r in requirements.iter() { collect_classified(r, out); }
        }
        Expr::ConstructorWithin { pos_args, named_args, requirements, .. } => {
            for c in pos_args.iter() { collect_classified(c, out); }
            for (_, c) in named_args.iter() { collect_classified(c, out); }
            for r in requirements.iter() { collect_classified(r, out); }
        }
        Expr::LambdaWithin { body, requirements, .. } => {
            collect_classified(body, out);
            for r in requirements.iter() { collect_classified(r, out); }
        }
        Expr::Instantiation { pos_args, named_args, .. } => {
            for c in pos_args.iter() { collect_classified(c, out); }
            for (_, c) in named_args.iter() { collect_classified(c, out); }
        }
        Expr::RequirementAtSort { chain, .. } => collect_classified(chain, out),
        Expr::ConstructRequirement { requirements, .. } => {
            for r in requirements.iter() { collect_classified(r, out); }
        }
        Expr::Const(_) | Expr::Ref(_) | Expr::Ident(_)
        | Expr::Var(_) | Expr::Bottom | Expr::VarRef { .. } => {}
    }
}

/// Synthesize a Term-form apply for the existing `record_*` helpers.
/// Shape: `apply(fn = Ref(functor), args = nil)` — the helpers only
/// look at the `fn` slot to identify the spec op and at the args
/// slot's structure for rewrite; for the rewrite-table population they
/// don't need the original args.
fn materialize_apply(kb: &mut KnowledgeBase, raw: RawClassified) -> ClassifiedApply {
    let apply_qn = kb.intern("anthill.reflect.Expr.apply");
    let fn_field = kb.intern("fn");
    let args_field = kb.intern("args");
    let nil_qn = kb.intern("nil");
    let nil_term = kb.alloc(Term::Fn {
        functor: nil_qn,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    let fn_ref = kb.alloc(Term::Ref(raw.functor));
    let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
    named.push((fn_field, fn_ref));
    named.push((args_field, nil_term));
    let apply_term = kb.alloc(Term::Fn {
        functor: apply_qn,
        pos_args: SmallVec::new(),
        named_args: named.clone(),
    });
    ClassifiedApply {
        apply_term,
        named_args: named,
        pos_args: SmallVec::new(),
        class: raw.class,
    }
}

/// WI-232 — fetch the caller's `requires` chain for `enclosing_sort`,
/// computing it at most once per sort across the whole pass.
fn chain_for(
    kb: &mut KnowledgeBase,
    cache: &mut HashMap<Symbol, Vec<RequiresEntry>>,
    enclosing_sort: Option<Symbol>,
) -> Vec<RequiresEntry> {
    let s = match enclosing_sort {
        Some(s) => s,
        None => return Vec::new(),
    };
    if let Some(cached) = cache.get(&s) {
        return cached.clone();
    }
    let chain = requires_chain(kb, s);
    cache.insert(s, chain.clone());
    chain
}
