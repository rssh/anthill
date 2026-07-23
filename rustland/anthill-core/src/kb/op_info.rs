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
    /// WI-347 — precondition clauses (the `requires` field). Each entry is one
    /// clause: a goal term, or a `conjunction(g1, …)` when the clause had several
    /// goals. **Includes** the auto-inferred `EffectsRuntime[Effects=E]` requires
    /// appended by the loader (WI-320); a consumer comparing user preconditions
    /// filters those out (see `check_override_refinement`). WI-366 B2:
    /// carrier-agnostic `Value` — a denoted-bearing precondition (`requires
    /// Modify[c]`) is a `Value::Node` that a hash-consed `TermId` can't hold; a
    /// ground clause is a `Value::Term`. Read carrier-faithfully, never
    /// materialized back to a term (mirrors `params`/`effects`).
    pub requires: Vec<Value>,
    /// WI-347 — postcondition clauses (the `ensures` field), same per-clause shape
    /// and carrier-agnostic `Value` as `requires` (WI-366 B2). No auto-inferred
    /// entries are mixed in.
    pub ensures: Vec<Value>,
    /// WI-087 — operation attributes: the `meta(key: value, ...)` term lowered
    /// from the operation's `meta_block`. `None` when the operation carries no
    /// attributes (an empty `meta()` reads back as `None`). Inspect with
    /// [`crate::kb::load::meta_has_flag`] / [`crate::kb::load::meta_value`].
    pub meta: Option<TermId>,
}

/// WI-656 — the body-INDEPENDENT half of an operation's `OperationInfo`: every
/// field of [`OpInfoRecord`] except the body node. Cached per operation in
/// [`crate::kb::KnowledgeBase`]'s `op_records` so `lookup_operation_info` is an
/// O(1) map hit instead of an O(N_ops) linear scan of the `OperationInfo` facts
/// (which, per operation-reference during inference, was quadratic). Load-stable:
/// the typer rewrites bodies, never signatures, so a cached copy never goes stale
/// within a load.
#[derive(Debug, Clone)]
pub struct OpSignature {
    pub params: Vec<(Symbol, Value)>,
    pub return_type: Value,
    pub effects: Vec<Value>,
    pub type_params: Vec<(Symbol, TermId)>,
    pub requires: Vec<Value>,
    pub ensures: Vec<Value>,
    pub meta: Option<TermId>,
}

/// WI-656 — the unified per-operation record: an operation's cached
/// [`OpSignature`] and its (mutable) body node, keyed by op symbol in
/// [`crate::kb::KnowledgeBase`]'s `op_records`. Replaces the former standalone
/// `op_bodies` map — the body now lives here beside the signature, so the typer's
/// signature lookup and body access are one O(1) hit. `signature` is `None` until
/// [`build_op_signatures`] populates it; `body` is `None` for a body-less spec op
/// and is written in place by `set_op_body_node` (the `[simp]`-rewrite write-back),
/// so it is never a stale snapshot.
#[derive(Debug, Clone, Default)]
pub struct OperationRecord {
    pub signature: Option<OpSignature>,
    pub body: Option<Rc<NodeOccurrence>>,
}

/// WI-398: every operation's `(symbol, params)` in ONE pass over the `OperationInfo`
/// facts. The signature-wellformedness check (a cyclic cross-parameter projection)
/// must cover EVERY operation — body-less free specs included — which the body-type-
/// check pass (`check_operation_bodies`, keyed off `op_bodies`/`SortInfo`) does not
/// reach. Carrier-agnostic, mirroring [`lookup_operation_info`]'s param decode.
pub fn all_operation_params(kb: &KnowledgeBase) -> Vec<(Symbol, Vec<(Symbol, Value)>)> {
    operation_info_fact_heads(kb)
        .into_iter()
        .map(|(op_sym, head)| (op_sym, extract_params(kb, head_field(kb, head, "params"))))
        .collect()
}

/// WI-701: every operation's `(symbol, declared effect labels)` in ONE pass over the
/// `OperationInfo` facts — the effect-row twin of [`all_operation_params`]. Returns
/// ONE entry PER FACT, deliberately un-deduped by symbol: a spec op and its impl are
/// separate `OperationInfo` facts, each with its OWN declared row, and the
/// Branch×External co-occurrence gate (proposal 054 §"`Branch` and `External`") must
/// see every declared row — not just the first-fact-only [`lookup_operation_info`]
/// cache. Carrier-agnostic via [`effects_of_head`] (a `denoted`-bearing label rides
/// as a `Value::Node`, a ground one as a `Value::Term`).
pub fn all_operation_effects(kb: &KnowledgeBase) -> Vec<(Symbol, Vec<Value>)> {
    operation_info_fact_heads(kb)
        .into_iter()
        .map(|(op_sym, head)| (op_sym, effects_of_head(kb, head)))
        .collect()
}

/// `(op_sym, &head)` for every `OperationInfo` FACT — the shared walk behind
/// [`all_operation_params`] / [`all_operation_effects`]. ONE entry PER FACT (a spec op
/// and its impl are separate facts, each with its own signature); each `&Value` head
/// borrows `kb`. A fact whose head carries no resolvable `name` ref is skipped.
fn operation_info_fact_heads(kb: &KnowledgeBase) -> Vec<(Symbol, &Value)> {
    let Some(op_info_sym) = kb.try_resolve_symbol("anthill.reflect.OperationInfo") else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for rid in kb.rules_by_functor(op_info_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let head = kb.rule_head_value(rid);
        let Some(op_sym) = head_name_ref(kb, head) else { continue };
        out.push((op_sym, head));
    }
    out
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
    // WI-656 fast path: the operation's signature is cached in its record (built
    // once by `build_op_signatures`), so this is an O(1) map hit rather than an
    // O(N_ops) scan of every `OperationInfo` fact. The body is read from the same
    // record — mutated in place by `set_op_body_node`, so never a stale snapshot.
    if let Some(rec) = kb.op_record(op_sym) {
        if let Some(sig) = &rec.signature {
            return Some(op_info_from_signature(op_sym, sig, rec.body.clone()));
        }
    }
    // Fallback: the linear scan. Taken by any lookup that runs BEFORE
    // `build_op_signatures` — the const-purity gate and eq-dispatch-table build
    // during load, when the index is still empty — or on a KB that never
    // type-checks. Post-typecheck callers (the typer, then eval / reflect /
    // codegen) hit the fast path above. Ground truth — behaviour-identical to the
    // pre-WI-656 code, only slower — so the index is a pure accelerator, never a
    // correctness change.
    let op_info_sym = kb.try_resolve_symbol("anthill.reflect.OperationInfo")?;
    for rid in kb.rules_by_functor(op_info_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let head = kb.rule_head_value(rid);
        if head_name_ref(kb, head) != Some(op_sym) {
            continue;
        }
        let sig = extract_signature_from_head(kb, head)?;
        return Some(op_info_from_signature(op_sym, &sig, kb.op_body_node(op_sym).cloned()));
    }
    None
}

/// WI-818 (review): does `op_sym` have a DECLARED signature — an `OperationInfo`
/// fact / cached record — without materializing the full [`OpInfoRecord`]
/// (whose construction clones every per-field Vec)? The dispatch fall-through
/// needs only PRESENCE to pick its error variant, and it sits on a path the
/// resolver bridge probes speculatively per candidate and residualizes, where
/// a full record build per probe is pure waste. Same two tiers as
/// [`lookup_operation_info`]: the WI-656 record fast path, then the
/// pre-`build_op_signatures` fact scan.
pub fn operation_is_declared(kb: &KnowledgeBase, op_sym: Symbol) -> bool {
    if let Some(rec) = kb.op_record(op_sym) {
        if rec.signature.is_some() {
            return true;
        }
    }
    let Some(op_info_sym) = kb.try_resolve_symbol("anthill.reflect.OperationInfo") else {
        return false;
    };
    kb.rules_by_functor(op_info_sym)
        .into_iter()
        .any(|rid| kb.is_fact(rid) && head_name_ref(kb, kb.rule_head_value(rid)) == Some(op_sym))
}

/// WI-656 — decode the body-independent [`OpSignature`] from an `OperationInfo`
/// fact head. The SINGLE field-decode, shared by [`lookup_operation_info`]'s
/// fallback and [`build_op_signatures`], so a cached signature and a scanned one
/// can never disagree. `None` when the head lacks a `return_type` (malformed —
/// the pre-WI-656 code likewise bailed the whole lookup on a missing `return_type`).
fn extract_signature_from_head(kb: &KnowledgeBase, head: &Value) -> Option<OpSignature> {
    let return_type = head_field_value(kb, head, "return_type")?;
    let effects = effects_of_head(kb, head);
    let params = extract_params(kb, head_field(kb, head, "params"));
    let type_params = extract_type_params(kb, head_field_term(kb, head, "type_params"));
    let requires = clause_list_field(kb, head, "requires");
    let ensures = clause_list_field(kb, head, "ensures");
    // WI-087: an empty `meta()` (the no-attributes case) reports as `None`.
    let meta = head_field_term(kb, head, "meta").filter(|t| meta_term_nonempty(kb, *t));
    Some(OpSignature { params, return_type, effects, type_params, requires, ensures, meta })
}

/// WI-656 — assemble the public [`OpInfoRecord`] from a cached [`OpSignature`]
/// plus the operation's (freshly read) body node, so a `[simp]`-rewritten body is
/// always seen. The signature fields are cloned out of the cache.
fn op_info_from_signature(
    op_sym: Symbol,
    sig: &OpSignature,
    body_node: Option<Rc<NodeOccurrence>>,
) -> OpInfoRecord {
    OpInfoRecord {
        op_sym,
        params: sig.params.clone(),
        return_type: sig.return_type.clone(),
        effects: sig.effects.clone(),
        type_params: sig.type_params.clone(),
        body_node,
        requires: sig.requires.clone(),
        ensures: sig.ensures.clone(),
        meta: sig.meta,
    }
}

/// WI-656 — populate every operation's cached [`OpSignature`] in `kb.op_records`
/// in ONE pass over the `OperationInfo` facts, collapsing what was an O(N_ops)
/// scan per `lookup_operation_info` call — quadratic across the typer's per-node
/// lookups — into O(N_ops) once. Cheap; run at the start of type-checking, by when
/// every `OperationInfo` fact is asserted. The body node in each record is untouched.
///
/// Mirrors the fallback scan EXACTLY, so the fast path stays a pure accelerator:
/// only the FIRST `OperationInfo` fact per name is consulted (`seen`), well-formed
/// or not. When that first fact is malformed — no `return_type`, so
/// [`extract_signature_from_head`] is `None` — NOTHING is cached; the fast path
/// then misses and the fallback re-derives the same `None` from that first fact.
/// Caching a *later* well-formed fact instead would flip the op from unresolved to
/// resolved, diverging from the scan (a `/code-review`-flagged latent case — no
/// loader emits a `return_type`-less head today). A re-run OVERWRITES each op's
/// signature from its current first fact, so a re-typecheck after a signature change
/// refreshes (a retracted op's entry would persist, but nothing mutates
/// `OperationInfo` post-load).
pub fn build_op_signatures(kb: &mut KnowledgeBase) {
    let Some(op_info_sym) = kb.try_resolve_symbol("anthill.reflect.OperationInfo") else {
        return;
    };
    // Collect under the immutable borrow, then insert — the head decode reads
    // `&kb` while the record insert needs `&mut kb`. `seen` keeps only the FIRST
    // fact per op, so a later duplicate the scan would never reach is ignored.
    let mut seen: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
    let mut sigs: Vec<(Symbol, OpSignature)> = Vec::new();
    for rid in kb.rules_by_functor(op_info_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let head = kb.rule_head_value(rid);
        let Some(op_sym) = head_name_ref(kb, head) else {
            continue;
        };
        if !seen.insert(op_sym) {
            continue;
        }
        // A malformed first fact caches nothing (signature stays `None`) — the
        // fallback then reproduces the same `None`, so the paths agree.
        if let Some(sig) = extract_signature_from_head(kb, head) {
            sigs.push((op_sym, sig));
        }
    }
    for (op_sym, sig) in sigs {
        kb.op_records.entry(op_sym).or_default().signature = Some(sig);
    }
}

/// WI-087: a `meta(...)` term carries attributes iff it has at least one named
/// arg. An empty `meta()` (the no-attributes default the loader always emits)
/// reports as having none, so `OpInfoRecord::meta` is `None` for it.
fn meta_term_nonempty(kb: &KnowledgeBase, meta_tid: TermId) -> bool {
    matches!(kb.get_term(meta_tid), Term::Fn { named_args, .. } if !named_args.is_empty())
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
        ViewItem::Value(Value::Term { id: t, .. }) => Some(*t),
        _ => None,
    }
}

/// A named field as a carrier-agnostic `Value` — for fields that may be
/// `denoted`-bearing (`return_type`, a `params` FieldInfo type). A hash-consed
/// `Term` field reads as `Value::Term`; a `Value::Node` field is returned
/// verbatim (occurrence preserved, never materialized to a term). WI-341 Stage A.
pub fn head_field_value(kb: &KnowledgeBase, head: &Value, key: &str) -> Option<Value> {
    Some(match head_field(kb, head, key)? {
        ViewItem::Term(t) => Value::term(t),
        ViewItem::Value(v) => v.clone(),
        ViewItem::Node(occ) => Value::Node(occ),
    })
}

/// Decode a clause-list field (`requires` / `ensures`) to its clause `Value`s
/// carrier-faithfully (WI-366 B2). The field is a cons-list built by
/// `convert_clause_list`; a hash-consed head stores a `TermId` list (each element
/// wrapped `Value::Term`), a value fact a value list whose elements (possibly
/// `Value::Node` for a denoted precondition) are returned verbatim. Mirrors
/// [`effects_of_head`]. `pub` so the reflect builtins (`KB.operations`) surface
/// `requires`/`ensures` carrier-faithfully (WI-548), matching the host bridge.
pub fn clause_list_field(kb: &KnowledgeBase, head: &Value, key: &str) -> Vec<Value> {
    match head_field(kb, head, key) {
        Some(ViewItem::Term(t)) => list_to_vec(kb, t).into_iter().map(Value::term).collect(),
        Some(ViewItem::Value(Value::Term { id: t, .. })) => {
            list_to_vec(kb, *t).into_iter().map(Value::term).collect()
        }
        Some(ViewItem::Value(v)) => value_list_to_vec(kb, v),
        _ => Vec::new(),
    }
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
        Some(ViewItem::Term(t)) => list_to_vec(kb, t).into_iter().map(Value::term).collect(),
        Some(ViewItem::Value(Value::Term { id: t, .. })) => {
            list_to_vec(kb, *t).into_iter().map(Value::term).collect()
        }
        Some(ViewItem::Value(v)) => value_list_to_vec(kb, v),
        _ => Vec::new(),
    }
}

/// Walk a value cons/nil list (the value-fact twin of [`list_to_vec`]) into its
/// element `Value`s. Cells are `Value::Entity`s over the prelude `cons`/`nil`
/// constructors; each `head` element is returned as-is (a `Value::Node` keeps
/// its occurrence identity). A ground `Value::Term` tail is decoded as a term
/// list for robustness against mixed shapes. `pub(crate)` so the WI-067 guard
/// discharge can read a denoted-label guarded atom's `build_value_list` guard.
pub(crate) fn value_list_to_vec(kb: &KnowledgeBase, mut v: &Value) -> Vec<Value> {
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
            Value::Term { id: t, .. } => {
                out.extend(list_to_vec(kb, *t).into_iter().map(Value::term));
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
        Some(ViewItem::Term(t)) => list_to_vec(kb, t).into_iter().map(Value::term).collect(),
        Some(ViewItem::Value(Value::Term { id: t, .. })) => {
            list_to_vec(kb, *t).into_iter().map(Value::term).collect()
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
