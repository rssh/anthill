//! Per-predicate translation policy lookup (proposal 030 phase δ).
//!
//! Reads `TranslationPolicy(predicate, backend, policy)` facts from
//! the KB and resolves them at codegen time. Per-backend defaults
//! kick in when no fact is present:
//!   - `LiftedAxiom` for predicates appearing in any `using` clause
//!     (mechanical: a citing proof needs the predicate's claim
//!     forall-quantified as a hypothesis, which is what LiftedAxiom
//!     emits).
//!   - `Inline` otherwise — preserves today's "always inline"
//!     behavior for predicates with no cite-side use.
//!
//! v0 wiring: prove.rs already routes `using`-cited predicates
//! through `lift_rule_to_implication_clause` (which is the
//! LiftedAxiom shape — declare-fun + assert-forall equivalence).
//! This module formalizes the dispatch so future code can query
//! the policy directly rather than threading the cite list around.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::typing::get_named_arg;

/// One of the four lowering strategies the kernel currently
/// distinguishes (proposal 030 §Per-predicate translation policy).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PredicatePolicy {
    Inline,
    DefineFun,
    DeclareFun,
    LiftedAxiom,
}

/// Look up the explicit `TranslationPolicy(predicate, backend, ...)`
/// fact for a given predicate-and-backend pair, or fall back to the
/// inferred default.
///
/// `cited_predicates` is the set of predicate QNs that appear in
/// some proof's `using` clause across the project — used to drive
/// the LiftedAxiom default. The caller is responsible for
/// collecting this set; for the v0 prove driver it equals the
/// union of every `ProofRecord.using` field.
pub fn policy_for(
    kb: &KnowledgeBase,
    predicate: &str,
    backend: &str,
    cited_predicates: &std::collections::BTreeSet<String>,
) -> PredicatePolicy {
    if let Some(p) = lookup_explicit_policy(kb, predicate, backend) {
        return p;
    }
    if cited_predicates.contains(predicate) {
        return PredicatePolicy::LiftedAxiom;
    }
    PredicatePolicy::Inline
}

/// Walk `TranslationPolicy` facts looking for an exact (predicate,
/// backend) match. Returns the first found policy, or None if no
/// such fact exists.
fn lookup_explicit_policy(
    kb: &KnowledgeBase,
    predicate: &str,
    backend: &str,
) -> Option<PredicatePolicy> {
    let policy_sym = kb.try_resolve_symbol(
        "anthill.realization.policy.TranslationPolicy"
    )?;
    for rid in kb.rules_by_functor(policy_sym) {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head(rid);
        let named = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args,
            _ => continue,
        };
        // Skip malformed records (non-string `predicate` / `backend`
        // fields) — only user-asserted policy facts are matched.
        // (WI-515: the synthetic schema-declaration fact this filter
        // also used to exclude is no longer asserted.)
        let pred = match read_string_field(kb, named, "predicate") {
            Some(s) => s, None => continue,
        };
        let bk = match read_string_field(kb, named, "backend") {
            Some(s) => s, None => continue,
        };
        if pred != predicate || bk != backend { continue; }
        let policy_tid = match get_named_arg(kb, named, "policy") {
            Some(t) => t, None => continue,
        };
        if let Some(p) = decode_policy_term(kb, policy_tid) {
            return Some(p);
        }
    }
    None
}

fn decode_policy_term(kb: &KnowledgeBase, tid: TermId) -> Option<PredicatePolicy> {
    let functor = match kb.get_term(tid) {
        Term::Fn { functor, .. } => *functor,
        Term::Ref(s) | Term::Ident(s) => *s,
        _ => return None,
    };
    let qn = kb.qualified_name_of(functor);
    let short = qn.rsplit('.').next().unwrap_or(qn);
    match short {
        "Inline" => Some(PredicatePolicy::Inline),
        "DefineFun" => Some(PredicatePolicy::DefineFun),
        "DeclareFun" => Some(PredicatePolicy::DeclareFun),
        "LiftedAxiom" => Some(PredicatePolicy::LiftedAxiom),
        _ => None,
    }
}

fn read_string_field(
    kb: &KnowledgeBase,
    named: &smallvec::SmallVec<[(anthill_core::intern::Symbol, TermId); 2]>,
    key: &str,
) -> Option<String> {
    let tid = get_named_arg(kb, named, key)?;
    if let Term::Const(Literal::String(s)) = kb.get_term(tid) {
        Some(s.clone())
    } else {
        None
    }
}
