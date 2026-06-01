//! WI-054 — unified `OperationInfo` lookup.
//!
//! Three callers used to walk `OperationInfo` facts independently:
//! `kb::typing::lookup_operation_info_full`,
//! `kb::typing::check_operation_bodies` (hand-inlined), and
//! `eval::eval::lookup_operation_body`. They each picked different
//! fields out of the same record. This module collapses the walk
//! into one helper that returns a complete `OpInfoRecord`; callers
//! then read whatever fields they need.

use std::rc::Rc;

use crate::eval::value::Value;
use crate::intern::Symbol;

use super::node_occurrence::NodeOccurrence;
use super::term::{Term, TermId};
use super::term_view::{TermView, ViewHead, ViewItem};
use super::typing::list_to_vec;
use super::KnowledgeBase;

/// Full `OperationInfo` view for one operation symbol.
///
/// WI-251 — the legacy `body: Option<TermId>` and `body_occ:
/// Option<OccurrenceId>` fields were removed. The body is now sourced
/// exclusively from `kb.op_body_node(op_sym)` as a value-typed
/// `Rc<NodeOccurrence>`. Consumers that need a body inspect
/// `body_node` directly.
#[derive(Debug, Clone)]
pub struct OpInfoRecord {
    pub op_sym: Symbol,
    /// Each entry: `(param_name_symbol, declared_type)`. WI-341 Stage A: the
    /// type is carrier-agnostic `Value` — a callback parameter whose arrow
    /// effect is `denoted`-bearing (`Modify[a]`) is a `Value::Node` arrow that
    /// cannot be a hash-consed `TermId`. A ground param type is a `Value::Term`.
    /// Read carrier-faithfully from the `OperationInfo` head (value fact when any
    /// param/effect is `Node`), never materialized back to a term.
    pub params: Vec<(Symbol, Value)>,
    /// WI-341: carrier-agnostic — a denoted-bearing return type (an op returning
    /// a `Modify`-carrying callback) is a `Value::Node`; ground returns are
    /// `Value::Term`. Read carrier-faithfully, never materialized to a term.
    pub return_type: Value,
    /// Effect labels, carrier-agnostic `Value`s read directly from the
    /// `OperationInfo` fact (WI-348). A ground label (`Error`) is a
    /// `Value::Term`; a `denoted`-bearing label (`Modify[c]`) is a `Value::Node`
    /// — the fact is then a *value fact* and these labels ride in its value
    /// effects list, not a side-table.
    pub effects: Vec<Value>,
    /// Operation-level type parameters from `operation foo[A, B](...)`.
    /// Each entry: `(name_symbol, Var(VarId) term)`. The typer matches
    /// call-site bindings against this table to seed its substitution.
    pub type_params: Vec<(Symbol, TermId)>,
    /// Body NodeOccurrence read from `kb.op_bodies`. `None` when the
    /// operation is body-less (a spec op declaration).
    pub body_node: Option<Rc<NodeOccurrence>>,
}

/// Walk `OperationInfo` facts, returning the record for `op_sym` if
/// any. None means no OperationInfo fact carries `name = op_sym`.
///
/// WI-348: carrier-agnostic. The head may be a hash-consed `Term::Fn`
/// (`Value::Term`) or — for an op with a `denoted`-bearing effect (`Modify[c]`)
/// — a `Value::Entity` *value fact* carrying a value effects list. Every field
/// is read through the head's [`TermView`], so both carriers funnel through one
/// walk; the effects field decodes to `Vec<Value>` (term list → `Value::Term`s,
/// value list → its elements verbatim, preserving `Value::Node` identity).
pub fn lookup_operation_info(kb: &KnowledgeBase, op_sym: Symbol) -> Option<OpInfoRecord> {
    let op_info_sym = kb.try_resolve_symbol("anthill.reflect.OperationInfo")?;
    for rid in kb.rules_by_functor(op_info_sym) {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head_value(rid);

        let name_match = head_field_term(kb, head, "name")
            .and_then(|v| match kb.get_term(v) {
                Term::Ref(s) => Some(*s),
                _ => None,
            });
        if name_match != Some(op_sym) { continue; }

        let return_type = head_field_value(kb, head, "return_type")?;
        let effects = effects_of_head(kb, head);
        let params = extract_params(kb, head_field(kb, head, "params"));
        let type_params = extract_type_params(kb, head_field_term(kb, head, "type_params"));
        let body_node = kb.op_body_node(op_sym).cloned();
        return Some(OpInfoRecord {
            op_sym,
            params,
            return_type,
            effects,
            type_params,
            body_node,
        });
    }
    None
}

/// Find a named field of a carrier-agnostic head, by short name. Both `Term`
/// and `Value` carriers expose their named args through `TermView`.
fn head_field<'a>(kb: &'a KnowledgeBase, head: &'a Value, key: &str) -> Option<ViewItem<'a>> {
    head.named_keys(kb)
        .into_iter()
        .find(|s| kb.resolve_sym(*s) == key)
        .and_then(|sym| head.named_arg(kb, sym))
}

/// A named field as a ground `TermId`, when it is one (every `OperationInfo`
/// field except `effects` is ground regardless of head carrier). Shared with
/// the other carrier-agnostic `OperationInfo` walks, in-crate and out (WI-348).
pub fn head_field_term(kb: &KnowledgeBase, head: &Value, key: &str) -> Option<TermId> {
    match head_field(kb, head, key)? {
        ViewItem::Term(t) => Some(t),
        ViewItem::Value(Value::Term(t)) => Some(*t),
        _ => None,
    }
}

/// A named field as a carrier-agnostic `Value` — for fields that may be
/// `denoted`-bearing (`return_type`, a `params` FieldInfo type). A hash-consed
/// `Term` field reads as `Value::Term`; a `Value::Node` field is returned
/// verbatim (occurrence preserved, never materialized to a term). WI-341 Stage A.
pub fn head_field_value(kb: &KnowledgeBase, head: &Value, key: &str) -> Option<Value> {
    Some(match head_field(kb, head, key)? {
        ViewItem::Term(t) => Value::Term(t),
        ViewItem::Value(v) => v.clone(),
        ViewItem::Node(occ) => Value::Node(occ),
    })
}

/// The operation symbol carried in an `OperationInfo` head's `name` field
/// (`Term::Ref`), for the by-functor walks that match a fact to an op symbol.
/// Carrier-agnostic (WI-348) — `pub` so out-of-crate consumers (codegen) can
/// match a fact to its op symbol without reading the head as a term.
pub fn head_name_ref(kb: &KnowledgeBase, head: &Value) -> Option<Symbol> {
    match kb.get_term(head_field_term(kb, head, "name")?) {
        Term::Ref(s) => Some(*s),
        _ => None,
    }
}

/// Decode the `effects` field to carrier-agnostic labels. A hash-consed head
/// stores a `TermId` cons-list (each element wrapped `Value::Term`); a value
/// fact stores a value cons-list whose elements (possibly `Value::Node`) are
/// returned verbatim, preserving occurrence identity. `pub` so the reflect
/// builtins (`KB.operations`) read effects carrier-faithfully (WI-348).
pub fn effects_of_head(kb: &KnowledgeBase, head: &Value) -> Vec<Value> {
    match head_field(kb, head, "effects") {
        Some(ViewItem::Term(t)) => list_to_vec(kb, t).into_iter().map(Value::Term).collect(),
        Some(ViewItem::Value(Value::Term(t))) => {
            list_to_vec(kb, *t).into_iter().map(Value::Term).collect()
        }
        Some(ViewItem::Value(v)) => value_list_to_vec(kb, v),
        _ => Vec::new(),
    }
}

/// Walk a value cons/nil list (the value-fact twin of [`list_to_vec`]) into its
/// element `Value`s. Cells are `Value::Entity`s over the prelude `cons`/`nil`
/// constructors; each `head` element is returned as-is (a `Value::Node` keeps
/// its occurrence identity). A ground `Value::Term` tail is decoded as a term
/// list for robustness against mixed shapes.
fn value_list_to_vec(kb: &KnowledgeBase, mut v: &Value) -> Vec<Value> {
    let cons_sym = kb.try_resolve_symbol("anthill.prelude.List.cons");
    let mut out: Vec<Value> = Vec::new();
    loop {
        match v {
            Value::Entity { functor, named, .. } if Some(*functor) == cons_sym => {
                let head_el = named.iter().find(|(s, _)| kb.resolve_sym(*s) == "head").map(|(_, x)| x);
                let tail = named.iter().find(|(s, _)| kb.resolve_sym(*s) == "tail").map(|(_, x)| x);
                match (head_el, tail) {
                    (Some(h), Some(t)) => {
                        out.push(h.clone());
                        v = t;
                    }
                    _ => break,
                }
            }
            Value::Term(t) => {
                out.extend(list_to_vec(kb, *t).into_iter().map(Value::Term));
                break;
            }
            _ => break, // nil cell, or a shape that is not a cons list
        }
    }
    out
}

/// Walk a `type_params` list (a ground `TermId` list). Each entry is a
/// `Term::Var(Global(vid))`; the surface name comes from `vid.name()`.
fn extract_type_params(kb: &KnowledgeBase, tp_tid: Option<TermId>) -> Vec<(Symbol, TermId)> {
    let tp_tid = match tp_tid {
        Some(t) => t,
        None => return Vec::new(),
    };
    list_to_vec(kb, tp_tid)
        .into_iter()
        .filter_map(|var_tid| match kb.get_term(var_tid) {
            Term::Var(crate::kb::term::Var::Global(vid)) => Some((vid.name(), var_tid)),
            _ => None,
        })
        .collect()
}

/// Decode the `params` field to `(name, type)` pairs carrier-faithfully. The
/// params list AND each `FieldInfo` may be hash-consed (`Term`) or — when a
/// param type is `denoted`-bearing (a callback's `Modify[a]` arrow) — value
/// carriers; the type is returned as a `Value`, preserving `Value::Node`
/// occurrence identity and **never** materialized back to a term. Mirrors
/// [`effects_of_head`] (WI-341 Stage A).
fn extract_params(kb: &KnowledgeBase, params_field: Option<ViewItem>) -> Vec<(Symbol, Value)> {
    let items: Vec<Value> = match params_field {
        Some(ViewItem::Term(t)) => list_to_vec(kb, t).into_iter().map(Value::Term).collect(),
        Some(ViewItem::Value(Value::Term(t))) => {
            list_to_vec(kb, *t).into_iter().map(Value::Term).collect()
        }
        Some(ViewItem::Value(v)) => value_list_to_vec(kb, v),
        _ => return Vec::new(),
    };
    items
        .into_iter()
        .filter_map(|fi| {
            let name = view_ref_sym(kb, head_field(kb, &fi, "name")?)?;
            let ptype = head_field_value(kb, &fi, "type_name")?;
            Some((name, ptype))
        })
        .collect()
}

/// The symbol a `name`-field `ViewItem` refers to. Carrier-agnostic: a ref reads
/// as `ViewHead::Ref` through `TermView` whether the field is a hash-consed
/// `Term::Ref`, a `Value::Term(Ref)`, or a `Value::Node` `Expr::Ref` occurrence —
/// so no `kb.get_term` (which would only see the `Term` carrier).
fn view_ref_sym(kb: &KnowledgeBase, item: ViewItem) -> Option<Symbol> {
    match item.head(kb) {
        ViewHead::Ref(s) => Some(s),
        _ => None,
    }
}
