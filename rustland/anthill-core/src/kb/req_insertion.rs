//! WI-231 — requirement-insertion pass.
//!
//! Per `docs/design/operation-call-model.md` §"Pass structure: typer
//! first, requirement-insertion separate", the typer and the IR
//! elaboration step are distinct passes. The typer walks bodies and
//! *tags* each spec-op apply site with a `CallClass` row in
//! `kb.call_classifications` (a side-table). This pass consumes that
//! side-table and emits the corresponding IR rewrites into
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
//! it by reading `kb.call_classifications_iter()` and emitting its
//! own rewrites.
//!
//! WI-232: chain memoization. The pre-WI-232 pass recomputed
//! `requires_chain(enclosing_sort)` once per classification row, so a
//! sort with N spec-op calls walked the chain N times. After WI-232 the
//! pass keeps a per-sort cache and computes each chain at most once.
//! For `DeferToRequirement` rows the matched entry is now carried in
//! `CallClass.resolved_spec` itself, so the chain is only needed for
//! the projection-list construction inside `record_apply_within_rewrite`.

use std::collections::HashMap;

use crate::intern::Symbol;
use crate::kb::term::Term;
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
    // Collect into a Vec so we don't hold a borrow on the map while
    // emitting (each `record_*` mutates `kb.dispatch_rewrites`).
    let entries: Vec<(crate::kb::term::TermId, CallClass)> = kb
        .call_classifications_iter()
        .map(|(k, v)| (k, v.clone()))
        .collect();

    // WI-232: per-enclosing-sort chain cache. The chain is stable across
    // every call site sharing the same enclosing sort, so compute once
    // and clone the slice into each `record_*` call. Keyed by the
    // enclosing sort symbol; absent key means "no enclosing sort" (chain
    // is empty).
    let mut chain_cache: HashMap<Symbol, Vec<RequiresEntry>> = HashMap::new();

    for (apply_term, class) in entries {
        // Re-extract named_args / pos_args from the apply term itself.
        // Skip if the term isn't a Fn (shouldn't happen — the typer
        // only classifies apply Fns).
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
                resolved_tree,
            } => {
                let caller_requires = chain_for(kb, &mut chain_cache, enclosing_sort);
                record_apply_within_concrete(
                    kb, apply_term, &named_args, &pos_args,
                    fn_target_sym, callee_spec_sort, spec_op_sym,
                    &caller_requires, resolved_tree.as_ref(),
                );
            }
            CallClass::DeferToRequirement {
                spec_op_sym,
                op_short_sym,
                resolved_spec,
                slot,
                enclosing_sort,
            } => {
                let caller_requires = chain_for(kb, &mut chain_cache, enclosing_sort);
                record_apply_within_rewrite(
                    kb, apply_term, &named_args, &pos_args,
                    spec_op_sym, op_short_sym,
                    resolved_spec.required_sort, slot,
                    &caller_requires,
                );
            }
        }
    }
}

/// WI-232 — fetch the caller's `requires` chain for `enclosing_sort`,
/// computing it at most once per sort across the whole pass. Returns
/// a clone of the cached vec so the borrow on `cache` is released
/// before the caller passes the slice into the `&mut KB` record_*
/// helpers.
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
