//! Shared carrier-agnostic KB readers for the reflect introspection surface
//! (WI-551 gap-5 part (a)).
//!
//! There are two realizations of `anthill.reflect.KB.*`: the interpreter
//! eval-time builtins ([`super::builtins`], producing dynamically-typed `Value`
//! cons-lists) and the host-Rust bridge ([`super::bridge`], producing the
//! statically-typed `SortInfo` / `OperationInfo` / `FieldInfo` / `DescriptionInfo`
//! structs). They answer the SAME questions over the SAME KB facts — and had
//! independently re-walked them, drifting per-op (the WI-545 / WI-548 parity
//! tax). This module is the one walk for the *introspection record ops*: each
//! `read_*` returns a neutral record of `TermId`s / carrier-agnostic `Value`s,
//! and each realization maps those records to its own output type.
//!
//! Term reification (`reify` / `reflect`) and the per-parameter `FieldInfo`
//! decode are NOT yet shared — they still have a realization in each file (the
//! interpreter builds `Value` trees, the bridge the generated `TermRepr` enum,
//! and the two pick different in-band name carriers: a `Ref` term vs a `Symbol`).
//! Folding those onto a shared walk is the residual of part (a), filed separately.
//!
//! Carrier-faithful, both ways. A value-fact head (an `OperationInfo` with a
//! `denoted` effect `Modify[c]`, an entity with a value-in-type field) is a
//! `Value::Entity` whose fields ride as their own `Value`s (a `denoted` label /
//! field type is a `Value::Node`). The interpreter is dynamically typed, so it
//! holds those `Value`s directly. The bridge is NOT confined to ground terms
//! either: its struct fields are the reflect `Term` / `NodeOccurrence` carriers,
//! which are newtypes around `Value` (`ReflectTerm(Value)` /
//! `ReflectNodeOccurrence(Value)`) and so carry a `Value::Node` verbatim. Both
//! realizations therefore map these records the same way — the bridge wraps a
//! field `Value` with `rterm` / `ReflectNodeOccurrence::new` rather than skipping
//! it (the prior `facts_by_sort_name` Term-only skip is gone). The one residual
//! limitation, shared by both, is that an op whose `name` or `return_type` is
//! itself `denoted` (not a ground `TermId`) is skipped — see [`read_operations`].

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::op_info;
use anthill_core::kb::term::{Literal, Term as CoreTerm, TermId, Var};
use anthill_core::kb::term_view::TermView;
use anthill_core::kb::{KnowledgeBase, RuleId};

// ── Leaf helpers ────────────────────────────────────────────────

/// The short (last dotted segment) of a qualified name.
pub(crate) fn short_of(qualified: &str) -> &str {
    qualified.rsplit('.').next().unwrap_or(qualified)
}

/// A displayable name for any `TermId` — the head symbol of a `Ref`/`Ident`/
/// `Fn`, the rendering of a literal, or a sigil'd var.
pub(crate) fn term_display_name(kb: &KnowledgeBase, id: TermId) -> String {
    match kb.get_term(id) {
        CoreTerm::Ref(sym) | CoreTerm::Ident(sym) => kb.resolve_sym(*sym).to_string(),
        CoreTerm::Fn { functor, .. } => kb.resolve_sym(*functor).to_string(),
        CoreTerm::Const(Literal::String(s)) => s.clone(),
        CoreTerm::Const(Literal::Int(n)) => n.to_string(),
        CoreTerm::Const(Literal::BigInt(n)) => n.to_string(),
        CoreTerm::Const(Literal::Float(f)) => f.to_string(),
        CoreTerm::Const(Literal::Bool(b)) => b.to_string(),
        CoreTerm::Const(Literal::Handle(kind, id)) => format!("<{:?}:{}>", kind, id),
        CoreTerm::Var(Var::Global(vid)) => format!("?{}", kb.resolve_sym(vid.name())),
        CoreTerm::Var(Var::DeBruijn(n)) => format!("?_{n}"),
        CoreTerm::Var(Var::Rigid(vid)) => format!("!{}", kb.resolve_sym(vid.name())),
        CoreTerm::Bottom => "⊥".into(),
        CoreTerm::ParseAux(_) => "<parse-aux>".into(),
    }
}

/// Walk a prelude `cons(head:_, tail:_)` chain ending in `nil` and collect the
/// head elements as `TermId`s. Cells are matched by their short functor name
/// (`cons`/`nil`) and `head`/`tail` field names — the only such constructors in
/// a loaded KB are the prelude `List` ones.
pub(crate) fn collect_list_terms(kb: &KnowledgeBase, list_tid: TermId) -> Vec<TermId> {
    let mut results = vec![];
    let mut current = list_tid;
    loop {
        match kb.get_term(current) {
            CoreTerm::Fn { functor, named_args, .. } => {
                let name = kb.resolve_sym(*functor);
                if name == "nil" {
                    break;
                }
                if name == "cons" {
                    let head = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "head");
                    let tail = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "tail");
                    if let Some(&(_, h)) = head {
                        results.push(h);
                    }
                    match tail {
                        Some(&(_, t)) => current = t,
                        None => break,
                    }
                } else {
                    break;
                }
            }
            _ => break,
        }
    }
    results
}

/// Named args of a fact head, read carrier-agnostically via [`TermView`]. A
/// non-`Term` field (none of the ground reflect schemas have one) has no
/// `TermId` and is omitted.
pub(crate) fn term_named_args(kb: &KnowledgeBase, head: &Value) -> Vec<(Symbol, TermId)> {
    head.named_keys(kb)
        .into_iter()
        .filter_map(|k| head.named_arg(kb, k).and_then(|i| i.as_term_id()).map(|t| (k, t)))
        .collect()
}

/// Positional args of a fact head, carrier-agnostic peer of [`term_named_args`].
pub(crate) fn term_pos_args(kb: &KnowledgeBase, head: &Value) -> Vec<TermId> {
    let mut out = Vec::new();
    let mut i = 0;
    while let Some(item) = head.pos_arg(kb, i) {
        if let Some(t) = item.as_term_id() {
            out.push(t);
        }
        i += 1;
    }
    out
}

/// Every fact in a sort bucket, with its head read carrier-agnostically as a
/// [`Value`] (a `Value::Term` for a ground fact, a `Value::Entity`/`Value::Node`
/// for a value fact). Callers that are `Term`-only filter on the carrier.
pub(crate) fn facts_by_sort_name(kb: &mut KnowledgeBase, sort_name: &str) -> Vec<(RuleId, Value)> {
    let sort_term = kb.make_name_term(sort_name);
    kb.by_sort(sort_term)
        .into_iter()
        .map(|rid| (rid, kb.rule_head_value(rid).clone()))
        .collect()
}

/// Collect the names of every `Member` of a given `kind` (`Constructor`,
/// `Operation`, …) under `parent_name`. Matches the parent by full OR short name.
pub(crate) fn members_of_kind(kb: &mut KnowledgeBase, parent_name: &str, kind: &str) -> Vec<String> {
    let mut results = vec![];
    for (_rid, head) in facts_by_sort_name(kb, "Member") {
        let pos = term_pos_args(kb, &head);
        if pos.len() == 3 {
            let member_kind = term_display_name(kb, pos[1]);
            let member_parent = term_display_name(kb, pos[2]);
            if member_kind == kind
                && (member_parent == parent_name || short_of(&member_parent) == parent_name)
            {
                results.push(term_display_name(kb, pos[0]));
            }
        }
    }
    results
}

// ── Per-op record readers ───────────────────────────────────────

/// One `SortInfo` fact, decoded to its field `TermId`s. `SortInfo` heads are
/// ground by design, so every field is a hash-consed `TermId`.
pub(crate) struct SortRecord {
    pub name: TermId,
    pub definition: TermId,
    pub kind: Option<TermId>,
    pub constructors: Vec<TermId>,
    pub operations: Vec<TermId>,
    pub parameters: Vec<TermId>,
    pub requires: Vec<TermId>,
}

/// Read every `SortInfo` fact (optionally namespace-prefix filtered). Queried by
/// the `SortInfo` functor so the value-in-type `SortAlias`, which shares the
/// `"Sort"` bucket (WI-366), is not picked up. A fact missing `name` or
/// `definition` is skipped (incomplete record).
pub(crate) fn read_sort_infos(kb: &mut KnowledgeBase, namespace: Option<&str>) -> Vec<SortRecord> {
    let Some(sort_info) = kb.try_resolve_symbol("anthill.reflect.SortInfo") else {
        return Vec::new();
    };
    let facts: Vec<Value> = kb
        .rules_by_functor(sort_info)
        .into_iter()
        .filter(|rid| kb.is_fact(*rid))
        .map(|rid| kb.rule_head_value(rid).clone())
        .collect();
    let f_name = kb.intern("name");
    let f_definition = kb.intern("definition");
    let f_kind = kb.intern("kind");
    let f_constructors = kb.intern("constructors");
    let f_operations = kb.intern("operations");
    let f_parameters = kb.intern("parameters");
    let f_requires = kb.intern("requires");

    let mut out = Vec::new();
    for head in &facts {
        let named = term_named_args(kb, head);
        let field = |key: Symbol| named.iter().find(|(n, _)| *n == key).map(|(_, t)| *t);

        let name = match field(f_name) {
            Some(t) => t,
            None => continue,
        };
        let definition = match field(f_definition) {
            Some(t) => t,
            None => continue,
        };
        if let Some(ns) = namespace {
            if !term_display_name(kb, name).starts_with(ns) {
                continue;
            }
        }
        let list = |key: Symbol| field(key).map(|t| collect_list_terms(kb, t)).unwrap_or_default();
        out.push(SortRecord {
            name,
            definition,
            kind: field(f_kind),
            constructors: list(f_constructors),
            operations: list(f_operations),
            parameters: list(f_parameters),
            requires: list(f_requires),
        });
    }
    out
}

/// One `OperationInfo` fact for a sort, decoded carrier-faithfully through the
/// `op_info` funnel. `name` / `return_type` / `meta` / the `params` FieldInfo
/// list are ground `TermId`s; `effects` / `requires` / `ensures` are
/// carrier-agnostic `Value`s (a `denoted` label rides as a `Value::Node`). An op
/// whose `name` or `return_type` is itself `denoted` (not a ground `TermId`) is
/// skipped — mirrors the interpreter's prior loop.
pub(crate) struct OperationRecord {
    pub name: TermId,
    pub return_type: TermId,
    pub params: Vec<TermId>,
    pub effects: Vec<Value>,
    pub requires: Vec<Value>,
    pub ensures: Vec<Value>,
    pub meta: TermId,
}

/// Read the `OperationInfo` facts whose domain is `sort_name` (full or short).
pub(crate) fn read_operations(kb: &mut KnowledgeBase, sort_name: &str) -> Vec<OperationRecord> {
    let op_sort = kb.make_name_term("Operation");
    let meta_default_sym = kb.intern("meta");
    let mut out = Vec::new();
    for rid in kb.by_sort(op_sort) {
        if !kb.is_fact(rid) {
            continue;
        }
        let head = kb.rule_head_value(rid).clone();
        let name = match op_info::head_field_term(kb, &head, "name") {
            Some(t) => t,
            None => continue,
        };
        let domain_name = term_display_name(kb, kb.fact_domain(rid));
        if domain_name != sort_name && short_of(&domain_name) != sort_name {
            continue;
        }
        let return_type = match op_info::head_field_term(kb, &head, "return_type") {
            Some(t) => t,
            None => continue,
        };
        let params = op_info::head_field_term(kb, &head, "params")
            .map(|t| collect_list_terms(kb, t))
            .unwrap_or_default();
        let effects = op_info::effects_of_head(kb, &head);
        let requires = op_info::clause_list_field(kb, &head, "requires");
        let ensures = op_info::clause_list_field(kb, &head, "ensures");
        // `meta` defaults to a bare `meta` ref when the fact omits it (the loader
        // always emits `meta(...)`, so the default is a parity-only fallback).
        let meta = op_info::head_field_term(kb, &head, "meta")
            .unwrap_or_else(|| kb.alloc(CoreTerm::Ref(meta_default_sym)));
        out.push(OperationRecord {
            name,
            return_type,
            params,
            effects,
            requires,
            ensures,
            meta,
        });
    }
    out
}

/// One `Description(target, content, index)` fact. The index is the stored
/// 0-based per-target index (WI-438), not a global enumeration.
pub(crate) struct DescriptionRecord {
    pub target: TermId,
    pub content: String,
    pub index: i64,
}

/// Read every `Description` fact, optionally filtered to `target` (full or short
/// name). A fact with fewer than three positional args, or a non-integer index,
/// is skipped.
pub(crate) fn read_descriptions(
    kb: &mut KnowledgeBase,
    target: Option<&str>,
) -> Vec<DescriptionRecord> {
    let mut out = Vec::new();
    for (_rid, head) in facts_by_sort_name(kb, "Description") {
        let pos = term_pos_args(kb, &head);
        if pos.len() < 3 {
            continue;
        }
        let index = match kb.get_term(pos[2]) {
            CoreTerm::Const(Literal::Int(n)) => *n,
            _ => continue,
        };
        if let Some(t) = target {
            let target_name = term_display_name(kb, pos[0]);
            if target_name != t && short_of(&target_name) != t {
                continue;
            }
        }
        out.push(DescriptionRecord {
            target: pos[0],
            content: term_display_name(kb, pos[1]),
            index,
        });
    }
    out
}

/// The entity matching `name` (full or short functor name), read carrier-
/// agnostically: the `(field_name, field_type)` pairs, where a field type rides
/// as its own `Value` (a `denoted` field type is a `Value::Node`, surfaced
/// verbatim by both realizations). Entity names are unique per sort, so at most
/// one entity matches (first wins).
pub(crate) struct EntityFieldsRecord {
    pub fields: Vec<(Symbol, Value)>,
}

/// Find the `Entity` fact for `name` and decode its fields. `None` if no entity
/// matches.
pub(crate) fn read_entity_fields(kb: &mut KnowledgeBase, name: &str) -> Option<EntityFieldsRecord> {
    for (_rid, head) in facts_by_sort_name(kb, "Entity") {
        let (functor, named): (Symbol, Vec<(Symbol, Value)>) = match &head {
            Value::Term { id: t, .. } => match kb.get_term(*t) {
                CoreTerm::Fn { functor, named_args, .. } => (
                    *functor,
                    named_args.iter().map(|&(s, tid)| (s, Value::term(tid))).collect(),
                ),
                _ => continue,
            },
            Value::Entity { functor, named, .. } => (*functor, named.to_vec()),
            _ => continue,
        };
        let functor_name = kb.resolve_sym(functor).to_string();
        if functor_name != name && short_of(&functor_name) != name {
            continue;
        }
        return Some(EntityFieldsRecord { fields: named });
    }
    None
}

/// The head `Value`s of every `Rule` fact whose domain is `sort_name` (full or
/// short). Each realization reifies these to its own term-repr form.
pub(crate) fn rule_heads_for_sort(kb: &mut KnowledgeBase, sort_name: &str) -> Vec<Value> {
    let mut out = Vec::new();
    for (rid, head) in facts_by_sort_name(kb, "Rule") {
        let domain_name = term_display_name(kb, kb.fact_domain(rid));
        if domain_name != sort_name && short_of(&domain_name) != sort_name {
            continue;
        }
        out.push(head);
    }
    out
}

