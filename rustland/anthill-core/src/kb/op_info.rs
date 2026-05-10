//! WI-054 — unified `OperationInfo` lookup.
//!
//! Three callers used to walk `OperationInfo` facts independently:
//! `kb::typing::lookup_operation_info_full`,
//! `kb::typing::check_operation_bodies` (hand-inlined), and
//! `eval::eval::lookup_operation_body`. They each picked different
//! fields out of the same record. This module collapses the walk
//! into one helper that returns a complete `OpInfoRecord`; callers
//! then read whatever fields they need.

use smallvec::SmallVec;

use crate::intern::Symbol;

use super::term::{Term, TermId};
use super::typing::{list_to_vec, resolve_handle, unwrap_option};
use super::KnowledgeBase;

/// Full `OperationInfo` view for one operation symbol.
#[derive(Debug, Clone)]
pub struct OpInfoRecord {
    pub op_sym: Symbol,
    /// Each entry: `(param_name_symbol, declared_type_term)`.
    pub params: Vec<(Symbol, TermId)>,
    pub return_type: TermId,
    pub effects: Vec<TermId>,
    /// Resolved body term — `None` when the operation is body-less
    /// (a spec op declaration). Handle wrappers are unwrapped via
    /// `resolve_handle` so callers see the real expression term.
    pub body: Option<TermId>,
}

/// Walk `OperationInfo` facts, returning the record for `op_sym` if
/// any. None means no OperationInfo fact carries `name = op_sym`.
pub fn lookup_operation_info(kb: &KnowledgeBase, op_sym: Symbol) -> Option<OpInfoRecord> {
    let op_info_sym = kb.try_resolve_symbol("anthill.reflect.OperationInfo")?;
    for rid in kb.by_functor(op_info_sym) {
        if !kb.rule_body(rid).is_empty() { continue; }
        let head = kb.rule_head(rid);
        let named_args = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args.clone(),
            _ => continue,
        };

        let name_match = find_named(kb, &named_args, "name")
            .and_then(|v| match kb.get_term(v) {
                Term::Ref(s) => Some(*s),
                _ => None,
            });
        if name_match != Some(op_sym) { continue; }

        let return_type = find_named(kb, &named_args, "return_type")?;
        let effects = find_named(kb, &named_args, "effects")
            .map(|t| list_to_vec(kb, t))
            .unwrap_or_default();
        let params = extract_params(kb, &named_args);
        let body = find_named(kb, &named_args, "body")
            .and_then(|opt| unwrap_option(kb, opt))
            .map(|h| resolve_handle(kb, h));

        return Some(OpInfoRecord {
            op_sym,
            params,
            return_type,
            effects,
            body,
        });
    }
    None
}

fn find_named(
    kb: &KnowledgeBase,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
    key: &str,
) -> Option<TermId> {
    named_args.iter()
        .find(|(s, _)| kb.resolve_sym(*s) == key)
        .map(|(_, v)| *v)
}

fn extract_params(
    kb: &KnowledgeBase,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
) -> Vec<(Symbol, TermId)> {
    let params_tid = match find_named(kb, named_args, "params") {
        Some(t) => t,
        None => return Vec::new(),
    };
    list_to_vec(kb, params_tid)
        .into_iter()
        .filter_map(|param_tid| {
            let pargs = match kb.get_term(param_tid) {
                Term::Fn { named_args, .. } => named_args,
                _ => return None,
            };
            let pname = find_named(kb, pargs, "name").and_then(|v| match kb.get_term(v) {
                Term::Ref(s) => Some(*s),
                _ => None,
            })?;
            let ptype = find_named(kb, pargs, "type_name")?;
            Some((pname, ptype))
        })
        .collect()
}
