//! WI-20260911-5G28A S3 (proposal 060 §2.2, `docs/design/060-implementation.md` §7.3) —
//! derive `anthill.reflect.SortDomain` for every sort that HAS a domain, CONDITIONAL for a
//! parametric one: `List provides SortDomain[T = List[T = T]] :- SortDomain[T = T]`.
//!
//! The same shape `type_value_derive` runs — one conjunctive clause over the carrier's
//! parameters, in declaration order — over a narrower population: a sort the loader derived
//! (or an author wrote) a domain for, which is `KnowledgeBase::has_domain_member`.
//!
//! **WHAT READS THE ROWS, and so what the gate below asks.** A typed head whose bound NAMES
//! its sort never needs one: the typed-head sweep calls that sort's `domain` directly, the
//! provider being written in the bound. The rows are read where the type is a VARIABLE —
//! the implicit `SortDomain` read the sweep generates for such a bound, routed at a citation
//! against the caller's slots and provisions, or derived from a carried type in mode (in) —
//! and wherever an author writes `SortDomain` into a requirement.

use std::collections::HashSet;

use crate::intern::Symbol;
use crate::kb::term::Term;
use crate::kb::KnowledgeBase;

/// Assert the derived rows. Runs after `expand_rule_head_bound_type_params`, the last pass
/// that edits a bound, so the gate reads the bounds the sweep will; and before the typer,
/// which resolves `requires SortDomain[…]` against the provider relation.
///
/// THE DEMAND GATE, `type_value_derive`'s and measured the same way. Deriving a row for
/// each of the stdlib's domain-bearing sorts cost ~55 ms per load in a debug build (median
/// of three, `ANTHILL_LOAD_TIMING=1`): `type_check_sorts` +36, `check_provider_requires`
/// +12, `eq_derive::run` +4, this pass +3.5 — the typer walking a bigger provision relation.
/// So nothing is derived until something can read it: a requirement that names the spec,
/// or a clause bound that is a type variable. The stdlib has neither, so a load that uses
/// neither pays nothing.
pub(crate) fn run(kb: &mut KnowledgeBase) -> Vec<super::load::LoadError> {
    let Some(spec) = kb.try_resolve_symbol(super::typing::SORT_DOMAIN_SPEC) else {
        return Vec::new();
    };
    if !super::typing::any_requirement_names_spec(kb, spec) && !any_bound_is_a_type_variable(kb) {
        return Vec::new();
    }
    // The provision relation's obligations, `derive_forwarded_provisions`' at its load site:
    // the index dropped so the reads below hit the live relation, the requires-chain cache
    // invalidated and the index rebuilt after. HERE, past the gate, and not at the call
    // site: a closed gate must cost nothing, and an index rebuild on every load is not
    // nothing.
    kb.provides_index = None;
    let spec_canon = kb.canonical_sort_sym(spec);
    // Carriers that already provide it — this pass's own rows from an earlier load phase.
    let already: HashSet<Symbol> = super::typing::provision_carriers_of_spec(kb, spec)
        .into_iter()
        .map(|c| kb.canonical_sort_sym(c))
        .collect();
    for s in super::type_value_derive::declared_sorts(kb) {
        let cs = kb.canonical_sort_sym(s);
        if cs == spec_canon || already.contains(&cs) || !kb.has_domain_member(s) {
            continue;
        }
        let params: Vec<Symbol> = kb.type_param_syms_of(s).to_vec();
        let conds: Vec<(Symbol, Symbol)> = params.into_iter().map(|p| (spec, p)).collect();
        super::eq_derive::assert_derived_provision(kb, s, spec, &conds);
    }
    kb.invalidate_requires_chain_cache();
    super::typing::build_provides_index(kb);
    Vec::new()
}

/// Does any clause carry a head bound that is a bare type VARIABLE (`?x: T`) — the bound the
/// typed-head sweep gives an implicit `SortDomain` read?
fn any_bound_is_a_type_variable(kb: &KnowledgeBase) -> bool {
    kb.live_rule_ids_iter().any(|rid| {
        kb.rule_type_bounds(rid)
            .iter()
            .any(|(_, t)| matches!(kb.get_term(*t), Term::Var(_)))
    })
}
