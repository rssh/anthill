//! WI-20260911-5G28A S3, WI-20260925-SHED7 (proposal 060 §2.3, 067) — the `SortDomain`
//! and `Fillable` PROVISION ROWS of every sort that has a domain.
//!
//! ```text
//! List provides SortDomain[T = List[T = T]] :- SortDomain[T = T]
//! List provides Fillable[T = List[T = T]]   :- SortDomain[T = T]
//! ```
//!
//! WHICH RELATION RUNS A PROVIDER'S `fill` is its `SortDomain` entry's
//! (`KnowledgeBase::sort_domain`) — a map of the rule member's own, found by the dictionary's
//! `impl`. Not a row of the sort's OPERATION table: that table is keyed by SHORT name, so a
//! `fill` row collided with any operation the sort has or inherits under that name — in one
//! load phase the relation took the operation's dispatch, across two the operation lost its
//! row — and `Dictionary.ops` listed the relation as a callable operation.
//!
//! The rows follow the layout `kb::fill_derive` recorded for the sort: ONE CONDITION PER
//! PARAMETER A FIELD FILLS, in declaration order — the order of the dictionary's subs, so a
//! dictionary the typer constructs from these rows is read by the derived `fill` clause
//! exactly as one the resolver builds from a type. `SortedSet`'s `O`, which no field fills,
//! is no condition.
//!
//! `Fillable`'s row is asserted beside `SortDomain`'s because `SortDomain provides Fillable`
//! is a conversion every carrier owes, and the pass that materializes conversions has run
//! before this one — and derives nothing for a CONDITIONAL row in any case.
//!
//! **WHAT READS THE ROWS, and so what the gate below asks.** Not the resolver: it builds a
//! `SortDomain` dictionary from a type structurally, one level at a time
//! (`KnowledgeBase::domain_evidence`), because a sort has one domain and nothing is chosen.
//! Not a citation either: the typer routes a clause's `SortDomain` read the same way, from
//! the type (`typing::sort_domain_route`). What reads them is the general requirement
//! machinery, where a WRITTEN requirement names the spec — the call site of
//! `operation countAt[X]() requires SortDomain[T = X]` resolves `SortDomain[T = Colour]`
//! against the provider relation like any other requirement.

use std::collections::HashSet;

use crate::intern::Symbol;
use crate::kb::KnowledgeBase;

/// Assert the provision rows. Runs after `expand_rule_head_bound_type_params`, the last pass
/// that edits a bound, so the gate reads the bounds the sweep will; and before the typer,
/// which resolves `requires SortDomain[…]` against the provider relation.
///
/// THE DEMAND GATE, `type_value_derive`'s and measured the same way. Deriving the rows for
/// every sort with a domain — two per sort since SHED7, `SortDomain` and `Fillable`, and
/// the primitives' — cost ~115 ms per load in a debug build (`ANTHILL_LOAD_TIMING=1`,
/// 2026-09-25): `check_provider_requires` +64, `type_check_sorts` +52, `eq_derive::run`
/// +7 — the typer re-validating a bigger provision relation. So no row is derived until
/// something reads one: a written requirement that names `SortDomain` or `Fillable`. The
/// stdlib writes none, so a load that writes none pays nothing.
pub(crate) fn run(kb: &mut KnowledgeBase) -> Vec<super::load::LoadError> {
    let Some(spec) = kb.try_resolve_symbol(super::typing::SORT_DOMAIN_SPEC) else {
        return Vec::new();
    };
    let fillable = kb.try_resolve_symbol(super::typing::FILLABLE_SPEC);
    let asked: Vec<Symbol> = std::iter::once(spec).chain(fillable).collect();
    if !super::typing::any_requirement_names_one_of(kb, &asked) {
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
    let mut sorts: Vec<Symbol> = kb.sort_domains.keys().copied().collect();
    // Registration order would be nicer than a hash walk; the symbol's index is the order
    // the sorts were interned in, which is stable for one program.
    sorts.sort_by_key(|s| s.index());
    for s in sorts {
        if s == spec_canon || already.contains(&s) {
            continue;
        }
        let Some(entry) = kb.sort_domain(s).cloned() else {
            continue;
        };
        // Each condition is the parameter the sort DECLARES for it — not the `j`-th of its
        // type parameters, which counts a WI-452 marked structured one too.
        let conds: Vec<(Symbol, Symbol)> = entry
            .conditions
            .iter()
            .filter_map(|&j| {
                super::fill_derive::condition_param_sym(kb, s, &entry.params, j).map(|p| (spec, p))
            })
            .collect();
        super::eq_derive::assert_derived_provision(kb, s, spec, &conds);
        if let Some(fillable) = fillable {
            super::eq_derive::assert_derived_provision(kb, s, fillable, &conds);
        }
    }
    kb.invalidate_requires_chain_cache();
    super::typing::build_provides_index(kb);
    // ONE LAYOUT (`typing::sort_domain_sub_offset`): the derived `fill` clauses read their
    // conditions at the offset the loader recorded, and a dictionary the typer builds from
    // these rows must hold them there. Checked now that the rows exist, because a drift
    // would not fail anything — it would hand an element's `fill` the wrong dictionary.
    let mut errors = Vec::new();
    let mut entries: Vec<(Symbol, super::fill_derive::SortDomainEntry)> = kb
        .sort_domains
        .iter()
        .filter(|(_, e)| !e.conditions.is_empty())
        .map(|(&s, e)| (s, e.clone()))
        .collect();
    // In the sorts' interning order, as the rows above, so the errors come out alike on every run.
    entries.sort_by_key(|(s, _)| s.index());
    for (s, e) in entries {
        let want = e.sub_offset + e.conditions.len();
        let got = super::typing::sort_domain_dict_len(kb, s);
        if got != Some(want) {
            errors.push(super::load::LoadError::Other {
                message: format!(
                    "WI-20260925-SHED7: `{}`'s `SortDomain` dictionary is laid out with {got:?} \
                     subs by the typer, where its derived `fill` reads {want} (its conditions \
                     at offset {}) — the two layouts disagree",
                    kb.qualified_name_of(s),
                    e.sub_offset,
                ),
            });
        }
    }
    errors
}
