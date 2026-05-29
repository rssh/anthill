//! WI-314 — region / escape masking for the `Modify[result]` effect.
//!
//! A constructor like `Cell.new : Modify[result]` is honest about
//! initializing the fresh region it returns (proposal 045 §5.5). Left
//! unmasked that effect goes *viral*: every cell-allocating operation
//! would have to redeclare it. This module is the operation-boundary
//! masking that stops the virality without lying about the effect at the
//! call site:
//!
//! - a `Modify[<result-region>]` (a fresh region produced by a sub-call,
//!   e.g. `Cell.new`) is **dropped** when the operation's return type
//!   cannot carry that region — the cell is discarded (`make_and_read :
//!   Int`), so the write is unobservable;
//! - it is **kept**, re-keyed to the operation's own `result`, when the
//!   return type *can* carry it (`make : Cell`) — the op honestly
//!   allocates a fresh region it hands out;
//! - effects on **let/match-bound locals** keep their existing drop
//!   (`external_effects`); effects on **parameters** stay external.
//!
//! Organization (option 3′ of
//! `docs/brainstorms/region-analysis-organization.md`): a factored,
//! separately-testable region/effect module the typer calls at its
//! existing operation-boundary frame — not scattered inline, not a
//! post-typer pass, not a generic plugin-engine. The interface is
//! deliberately plugin-shaped (`env + return-type + effect row → masked /
//! re-keyed row`) so it promotes cleanly to the fused typer plugin-engine
//! tracked as WI-315 when a second mini-phase arrives. It is the narrow
//! *result-reachability* slice of proposal 046; 046 grows the same module
//! with full provenance / aliasing / higher-order cases.

use std::collections::{HashMap, HashSet};

use super::term::{Term, TermId};
use super::KnowledgeBase;
use super::typing::{
    external_effects, extract_effect_resource_sym, extract_sort_ref_sym, substitute_ref_syms,
    TypingEnv,
};
use crate::intern::Symbol;

/// The sorts admitted by `Modifiable[T = …]` facts (`{Cell}` in the
/// current stdlib). A result type that structurally mentions one of these
/// can carry a freshly-allocated region out of the operation, so a
/// `Modify[result]` on such an op is kept rather than masked. Sourcing the
/// set from the facts (rather than hard-coding `Cell`) means a future
/// `Modifiable` resource that grows a `Modify[result]` constructor is
/// handled without touching this module.
pub(crate) fn region_sorts(kb: &KnowledgeBase) -> HashSet<Symbol> {
    let mut out = HashSet::new();
    let modifiable = match kb.try_resolve_symbol("anthill.prelude.Modifiable") {
        Some(s) => s,
        None => return out, // no Modifiable facts loaded — nothing admits a region
    };
    for rid in kb.by_functor(modifiable) {
        collect_sort_refs(kb, kb.rule_head(rid), modifiable, &mut out);
    }
    out
}

/// Collect every `sort_ref` symbol reachable in `term`, skipping `skip`
/// (the `Modifiable` head itself). Robust to either fact-head shape —
/// `Modifiable[T = Cell]` stored as `Fn{functor: Modifiable, T: Cell}` or
/// as `parameterized(sort_ref(Modifiable), bindings: [T = Cell])`.
fn collect_sort_refs(kb: &KnowledgeBase, term: TermId, skip: Symbol, out: &mut HashSet<Symbol>) {
    if let Some(s) = extract_sort_ref_sym(kb, term) {
        if s != skip {
            out.insert(s);
        }
        return;
    }
    // `Modifiable[T = Cell]` stores the type-arg as a bare `Ref(Cell)`, not a
    // `sort_ref`, so a plain reference names the admitted sort too.
    if let Term::Ref(s) = kb.get_term(term) {
        if *s != skip {
            out.insert(*s);
        }
        return;
    }
    for child in kb.get_term(term).subterms() {
        collect_sort_refs(kb, child, skip, out);
    }
}

/// True when `sym` is an operation's reserved return-value name
/// (`<op>.result`, proposal 041) — the resource a constructor's
/// `Modify[result]` refers to. Field-projection forms (`result.a`) are
/// deferred: no constructor emits them yet.
///
/// WI-341 step 1: this is now a **symbol-identity** membership test against
/// the result-binder set populated by `scan_operation_params` — not a
/// spelling match on the symbol's name. Symbols already carry identity; the
/// prior `rsplit('.') == "result"` encoded the result-region *role* in the
/// name and parsed it back, which mis-classified any unrelated symbol whose
/// last segment happened to be `result`. Identity membership removes that
/// fragility (and the string work).
pub(crate) fn is_result_region_sym(kb: &KnowledgeBase, sym: Symbol) -> bool {
    kb.is_result_binder(sym)
}

/// Whether `ty` can carry a modifiable region out of the operation — i.e.
/// its own type structure mentions a `regions` sort (directly, via a tuple
/// field, a list / parameterized type-arg, or a bare type variable, for
/// which it conservatively returns `true` and keeps the effect).
///
/// NARROW-SLICE LIMITATION (WI-314): this inspects the *return type's
/// structure* only. A region reachable solely through a returned **named
/// sort's field** (e.g. `-> Pair` where `Pair` has a `Cell` field) is not
/// seen, so such a `Modify[result]` is masked — an unsound drop. Closing it
/// needs type-param-aware reachability over sort definitions, deferred to
/// proposal 046. Unreachable in the current stdlib: no op returns a
/// fresh-cell-bearing named sort.
pub(crate) fn result_type_admits_region(
    kb: &KnowledgeBase,
    ty: TermId,
    regions: &HashSet<Symbol>,
) -> bool {
    if let Some(s) = extract_sort_ref_sym(kb, ty) {
        if regions.contains(&s) {
            return true;
        }
    }
    if let Term::Ref(s) = kb.get_term(ty) {
        if regions.contains(s) {
            return true;
        }
    }
    kb.get_term(ty)
        .subterms()
        .iter()
        .any(|&child| result_type_admits_region(kb, child, regions))
}

/// Re-key an effect's resource symbol `from` → `to` (a callee's
/// `Cell.new.result` → the enclosing op's own `result`), so the propagated
/// label is well-scoped in the caller and matches its declaration.
fn rekey_resource(kb: &mut KnowledgeBase, effect: TermId, from: Symbol, to: Symbol) -> TermId {
    let mut map = HashMap::new();
    map.insert(from, to);
    substitute_ref_syms(kb, effect, &map)
}

/// Operation-boundary effect masking (WI-314). Given the body's derived
/// effect row, the op's return type, and its reserved `result` symbol,
/// return the externally-visible row: locals dropped, escaping fresh
/// regions kept (re-keyed to `result`), non-escaping fresh regions
/// dropped, parameters left external. See the module header.
pub(crate) fn op_boundary_effects(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    return_type: TermId,
    op_result_sym: Option<Symbol>,
    regions: &HashSet<Symbol>,
    effects: &[TermId],
) -> Vec<TermId> {
    // 1. Existing local-resource drop (let/match-bound names).
    let after_local = external_effects(kb, env, effects);
    // 2. Result-region masking, keyed on whether the result can carry one.
    let admits = result_type_admits_region(kb, return_type, regions);
    let mut out: Vec<TermId> = Vec::with_capacity(after_local.len());
    for effect in after_local {
        match extract_effect_resource_sym(kb, effect) {
            Some(sym) if is_result_region_sym(kb, sym) => {
                if admits {
                    // Escapes via the result — re-key to the op's own
                    // `result` and keep (the op honestly allocates).
                    let kept = match op_result_sym {
                        Some(target) => rekey_resource(kb, effect, sym, target),
                        None => effect,
                    };
                    if !out.contains(&kept) {
                        out.push(kept);
                    }
                }
                // else: the fresh region cannot reach the result — drop.
            }
            _ => {
                // Parameter / unknown resource — external, keep.
                if !out.contains(&effect) {
                    out.push(effect);
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// WI-341 step 1: `is_result_region_sym` is identity-based, not
    /// spelling-based. A symbol whose name merely *ends in* `.result` but
    /// was never registered as an operation's result binder must NOT be
    /// classified as a result region (the pre-WI-341 `rsplit('.') ==
    /// "result"` match would have wrongly returned true here). A registered
    /// result-binder symbol returns true.
    #[test]
    fn result_region_is_identity_not_spelling() {
        let mut kb = KnowledgeBase::new();

        // A symbol spelled like a result name but NOT a registered binder —
        // e.g. a user sort/field that happens to be called `result`.
        let lookalike = kb.intern("SomeSort.result");
        assert!(
            !is_result_region_sym(&kb, lookalike),
            "an unregistered `*.result` symbol must not be a result region \
             (identity, not spelling)"
        );

        // A genuinely registered op result binder is recognised.
        let real = kb.intern("Cell.new.result");
        kb.register_result_binder(real);
        assert!(
            is_result_region_sym(&kb, real),
            "a registered result-binder symbol must be recognised"
        );

        // And the lookalike is still rejected after another binder exists.
        assert!(!is_result_region_sym(&kb, lookalike));
    }
}
