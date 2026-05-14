//! WI-231 — requirement-insertion pass.
//!
//! Per `docs/design/operation-call-model.md` §"Pass structure: typer
//! first, requirement-insertion separate", the typer and the IR
//! elaboration step are distinct passes. The typer walks bodies and
//! *tags* each spec-op apply site's `OccurrenceEntry` with a
//! `CallClass` on the `OccurrenceStore`. This pass consumes those
//! classifications and emits the corresponding IR rewrites into
//! `kb.dispatch_rewrites`.
//!
//! Separating the two passes makes:
//! - **Alternative elaborations possible.** A different codegen target
//!   (e.g., Rust monomorphization) can skip this pass and emit its
//!   own elaboration from the same classification side-table.
//! - **The "typed-but-unelaborated" IR a real state.** Calling
//!   `type_check_sorts` without `req_insertion::run` leaves
//!   `dispatch_rewrites` empty — useful for reflection / proof tooling
//!   that wants pre-elaboration IR.
//! - **A single-pass projection step.** All ProjectionSyms /
//!   requires_tree cache lookups consolidate at the pass entry,
//!   instead of being scattered across the typer's recursion.
//!
//! `run(kb)` is the canonical entry point; external code can replace
//! it by reading `kb.occurrence_store().classifications_iter()` and
//! emitting its own rewrites.
//!
//! WI-232: chain memoization. Per-enclosing-sort `requires_chain` is
//! computed at most once per pass invocation.
//!
//! WI-235: let-hoist phase. After per-call rewrites are emitted, a
//! second pass identifies `construct_requirement` dispatching-dict
//! expressions that appear multiple times within the same operation
//! body (matched by hash-consed TermId) and rewrites them to share a
//! single `let_expr` binding at the body root. Saves N-1 arena
//! allocations per body invocation for each duplicated dict shape.

use std::collections::HashMap;

use smallvec::SmallVec;

use crate::intern::Symbol;
use crate::kb::load::build_cons_list;
use crate::kb::term::{Term, TermId};
use crate::kb::typing::{
    record_apply_rewrite, record_apply_within_concrete,
    record_apply_within_rewrite, requires_chain, CallClass, RequiresEntry,
};
use crate::kb::KnowledgeBase;

/// WI-231 — entry point: walk every classification produced by the
/// typer and emit the corresponding IR rewrite. Idempotent: re-running
/// on a kb where rewrites already exist is a no-op (the `record_*`
/// helpers check `kb.dispatch_rewrites.contains_key` before emitting).
pub fn run(kb: &mut KnowledgeBase) {
    // Collect into a Vec so we don't hold a borrow on the store while
    // emitting (each `record_*` mutates `kb.dispatch_rewrites`). The
    // classification lives on the apply site's `OccurrenceEntry`; the
    // `record_*` helpers key off the apply `TermId`, recovered here.
    let entries: Vec<(TermId, CallClass)> = kb
        .occurrence_store()
        .classifications_iter()
        .map(|(occ, v)| (kb.occurrence_store().term(occ), v.clone()))
        .collect();

    let mut chain_cache: HashMap<Symbol, Vec<RequiresEntry>> = HashMap::new();
    // WI-235: track ConcreteApplyWithin emissions paired with the
    // owning op symbol for the hoist phase below.
    let mut concrete_by_op: HashMap<Symbol, Vec<TermId>> = HashMap::new();

    for (apply_term, class) in entries {
        let (named_args, pos_args) = match kb.get_term(apply_term).clone() {
            Term::Fn { named_args, pos_args, .. } => (named_args, pos_args),
            _ => continue,
        };

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
                enclosing_op_sym,
                resolved_tree,
            } => {
                let caller_requires = chain_for(kb, &mut chain_cache, enclosing_sort);
                let emitted = record_apply_within_concrete(
                    kb, apply_term, &named_args, &pos_args,
                    fn_target_sym, callee_spec_sort, spec_op_sym,
                    &caller_requires, resolved_tree.as_ref(),
                );
                if emitted {
                    if let Some(op_sym) = enclosing_op_sym {
                        concrete_by_op.entry(op_sym).or_default().push(apply_term);
                    }
                }
            }
            CallClass::DeferToRequirement { spec_op_sym, slot, .. } => {
                record_apply_within_rewrite(
                    kb, apply_term, &named_args, &pos_args,
                    spec_op_sym, slot,
                );
            }
        }
    }

    // WI-235 hoist phase.
    hoist_duplicate_dispatching_dicts(kb, &concrete_by_op);
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

/// WI-235 — for each operation body, find `construct_requirement`
/// dispatching-dict expressions emitted by more than one
/// `apply_within` site and let-bind them at the body root. Each
/// duplicate site is rewritten to read `var_ref(<synth_name>)`
/// instead of inlining the constructor.
///
/// Only `construct_requirement` shapes are hoisted: `requirement_at_current`
/// and `requirement_at_sort` reduce to a frame-local read + handle clone
/// (no arena alloc), so there's nothing to dedupe.
fn hoist_duplicate_dispatching_dicts(
    kb: &mut KnowledgeBase,
    concrete_by_op: &HashMap<Symbol, Vec<TermId>>,
) {
    let Some(syms) = HoistSyms::resolve(kb) else { return };

    // Sort by op's underlying u32 so the hoist counter assigns synth
    // names in a deterministic order across runs (HashMap iteration is
    // unordered; downstream tooling keyed on body terms would otherwise
    // see name churn).
    let mut ops: Vec<&Symbol> = concrete_by_op.keys().collect();
    ops.sort_by_key(|s| s.index());

    // `dispatch_rewrites` is keyed by the (hash-consed) apply TermId.
    // Two operations can contain a *structurally identical* `apply_within`
    // term — hash-consing makes them the same TermId. The hoist rewrites
    // `dispatch_rewrites[apply_tid]` to read this op's `var_ref(__hoist_N)`,
    // so a term shared across ops would have its rewrite overwritten by
    // whichever op is processed last, and the other ops' frames would
    // hit `var_ref(__hoist_N) unbound`. Such cross-op-shared apply terms
    // must NOT be per-op hoisted — they keep their op-agnostic phase-1
    // rewrite instead. (A principled fix keys `dispatch_rewrites` by
    // `(op, TermId)`; that is a larger eval-side change, filed separately.)
    let cross_op_shared: std::collections::HashSet<TermId> = {
        let mut seen_in: HashMap<TermId, Symbol> = HashMap::new();
        let mut shared = std::collections::HashSet::new();
        for (&op, tids) in concrete_by_op.iter() {
            for &t in tids {
                match seen_in.get(&t) {
                    Some(&other) if other != op => { shared.insert(t); }
                    _ => { seen_in.entry(t).or_insert(op); }
                }
            }
        }
        shared
    };

    let mut counter: u32 = 0;
    for &op_sym_ref in &ops {
        let op_sym = *op_sym_ref;
        let apply_tids: Vec<TermId> = concrete_by_op[&op_sym].iter()
            .copied()
            .filter(|t| !cross_op_shared.contains(t))
            .collect();
        if apply_tids.len() < 2 {
            continue;
        }
        let apply_tids = &apply_tids;
        let Some(body_root) = crate::kb::op_info::lookup_operation_info(kb, op_sym)
            .and_then(|r| r.body)
        else { continue };

        // Bucket apply sites by their dispatching-dict TermId (hash-consed →
        // structurally-identical construct_requirements share an id).
        // Each value stores (original_apply_tid, rewritten_aw_tid) pairs so
        // the rewrite loop below skips a second dispatch_rewrites lookup.
        let mut dict_uses: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::new();
        let spec_op_for_apply: HashMap<TermId, Symbol> = apply_tids.iter()
            .filter_map(|&t| kb.dispatch_origin.get(
                &kb.dispatch_rewrites.get(&t).copied()?
            ).copied().map(|s| (t, s)))
            .collect();
        for &apply_tid in apply_tids {
            let Some(rewritten_tid) = kb.dispatch_rewrites.get(&apply_tid).copied()
            else { continue };
            let Some(dict_expr) = extract_dispatching_dict(kb, rewritten_tid, &syms)
            else { continue };
            if !is_construct_requirement(kb, dict_expr, &syms) {
                continue;
            }
            dict_uses.entry(dict_expr).or_default().push((apply_tid, rewritten_tid));
        }

        let mut dict_keys: Vec<&TermId> = dict_uses.keys().collect();
        dict_keys.sort_by_key(|t| t.raw());
        let mut hoists: Vec<(Symbol, TermId, Vec<(TermId, TermId)>)> = Vec::new();
        for dict_key in dict_keys {
            let applies = &dict_uses[dict_key];
            if applies.len() <= 1 {
                continue;
            }
            let name = kb.intern(&format!("__hoist_{counter}"));
            counter += 1;
            hoists.push((name, *dict_key, applies.clone()));
        }
        if hoists.is_empty() {
            continue;
        }

        for (name, _dict_expr, applies) in &hoists {
            let var_ref_term = build_var_ref(kb, &syms, *name);
            let new_requirements = build_cons_list(
                kb, &[var_ref_term], syms.nil, syms.cons, syms.head, syms.tail,
            );
            for &(apply_tid, rewritten_tid) in applies {
                let new_rewritten = with_apply_within_requirements(
                    kb, rewritten_tid, new_requirements, &syms,
                );
                if let Some(new_tid) = new_rewritten {
                    // Overwrite the phase-1 rewrite and update dispatch_origin
                    // so reflection / `dispatch_origin_of(new_tid)` returns
                    // the spec-op symbol rather than `None`.
                    kb.dispatch_rewrites.insert(apply_tid, new_tid);
                    if let Some(spec_op) = spec_op_for_apply.get(&apply_tid).copied() {
                        kb.dispatch_origin.insert(new_tid, spec_op);
                    }
                }
            }
        }

        let mut wrapped = body_root;
        for (name, dict_expr, _) in hoists.iter().rev() {
            wrapped = build_let_expr(kb, &syms, *name, *dict_expr, wrapped);
        }
        kb.set_op_body_override(op_sym, wrapped);
    }
}

/// Cached stdlib symbols consumed by the hoist phase.
struct HoistSyms {
    apply_within: Symbol,
    construct_requirement: Symbol,
    let_expr: Symbol,
    var_ref: Symbol,
    var_pattern: Symbol,
    cons: Symbol,
    nil: Symbol,
    none_: Symbol,
    requirements: Symbol,
    head: Symbol,
    tail: Symbol,
    name: Symbol,
    pattern: Symbol,
    value: Symbol,
    body: Symbol,
    type_ann: Symbol,
}

impl HoistSyms {
    fn resolve(kb: &mut KnowledgeBase) -> Option<Self> {
        Some(Self {
            apply_within: kb.try_resolve_symbol("anthill.reflect.Expr.apply_within")?,
            construct_requirement: kb.try_resolve_symbol(
                "anthill.reflect.Expr.construct_requirement",
            )?,
            let_expr: kb.try_resolve_symbol("anthill.reflect.Expr.let_expr")?,
            var_ref: kb.try_resolve_symbol("anthill.reflect.Expr.var_ref")?,
            var_pattern: kb.try_resolve_symbol("anthill.reflect.Pattern.var_pattern")?,
            cons: kb.try_resolve_symbol("anthill.prelude.List.cons")?,
            nil: kb.try_resolve_symbol("anthill.prelude.List.nil")?,
            none_: kb.try_resolve_symbol("anthill.prelude.Option.none")?,
            requirements: kb.intern("requirements"),
            head: kb.intern("head"),
            tail: kb.intern("tail"),
            name: kb.intern("name"),
            pattern: kb.intern("pattern"),
            value: kb.intern("value"),
            body: kb.intern("body"),
            type_ann: kb.intern("type_ann"),
        })
    }
}

/// Pull `requirements[0]` (the cons-list head) out of a rewritten
/// apply_within term. None when the term shape doesn't match (e.g.,
/// requirements channel is `nil`).
fn extract_dispatching_dict(
    kb: &KnowledgeBase,
    aw_tid: TermId,
    syms: &HoistSyms,
) -> Option<TermId> {
    let Term::Fn { functor, named_args, .. } = kb.get_term(aw_tid) else { return None };
    if *functor != syms.apply_within {
        return None;
    }
    let reqs_tid = lookup_named(named_args, syms.requirements)?;
    let Term::Fn { functor: list_fn, named_args: list_named, .. } = kb.get_term(reqs_tid)
    else { return None };
    if *list_fn != syms.cons {
        return None;
    }
    lookup_named(list_named, syms.head)
}

fn lookup_named(
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
    key: Symbol,
) -> Option<TermId> {
    named_args.iter().find(|(k, _)| *k == key).map(|(_, v)| *v)
}

fn is_construct_requirement(kb: &KnowledgeBase, tid: TermId, syms: &HoistSyms) -> bool {
    matches!(
        kb.get_term(tid),
        Term::Fn { functor, .. } if *functor == syms.construct_requirement
    )
}

fn build_var_ref(kb: &mut KnowledgeBase, syms: &HoistSyms, name_sym: Symbol) -> TermId {
    let name_ref = kb.alloc(Term::Ref(name_sym));
    kb.alloc(Term::Fn {
        functor: syms.var_ref,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(syms.name, name_ref)]),
    })
}

/// Rebuild an apply_within term with a new `requirements` field, preserving
/// `fn` and `args`.
fn with_apply_within_requirements(
    kb: &mut KnowledgeBase,
    aw_tid: TermId,
    new_requirements: TermId,
    syms: &HoistSyms,
) -> Option<TermId> {
    let (functor, mut named, pos) = match kb.get_term(aw_tid).clone() {
        Term::Fn { functor, named_args, pos_args, .. } => (functor, named_args, pos_args),
        _ => return None,
    };
    if functor != syms.apply_within {
        return None;
    }
    for (k, v) in named.iter_mut() {
        if *k == syms.requirements {
            *v = new_requirements;
        }
    }
    Some(kb.alloc(Term::Fn { functor, pos_args: pos, named_args: named }))
}

/// Build `let_expr(pattern: var_pattern(name=name_sym, type_ann=none),
///                value: value_tid, body: body_tid)`.
fn build_let_expr(
    kb: &mut KnowledgeBase,
    syms: &HoistSyms,
    name_sym: Symbol,
    value_tid: TermId,
    body_tid: TermId,
) -> TermId {
    let name_ref = kb.alloc(Term::Ref(name_sym));
    let none = kb.alloc(Term::Fn {
        functor: syms.none_,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    let pattern = kb.alloc(Term::Fn {
        functor: syms.var_pattern,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(syms.name, name_ref), (syms.type_ann, none)]),
    });
    kb.alloc(Term::Fn {
        functor: syms.let_expr,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (syms.pattern, pattern),
            (syms.value, value_tid),
            (syms.body, body_tid),
        ]),
    })
}
