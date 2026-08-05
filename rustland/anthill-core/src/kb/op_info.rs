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
use super::term::{Term, TermId, Var};
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
    /// Each entry: `(name_symbol, the parameter's own logical variable)`. The
    /// typer matches call-site bindings against this table to seed its
    /// substitution.
    ///
    /// WI-849: a `Var`, not the `TermId` of a `Term::Var` — the entries ARE
    /// variables (the loader mints each one via `fresh_var`, `kb/load.rs`
    /// `load_operation`), and the term spelling made every reader destructure
    /// `kb.get_term(tid)` back to a `Var` and SILENTLY DROP anything else. The
    /// var is the whole content: the `Symbol` is `vid.name()` on this side, and
    /// a reader that wants a term carrier re-allocs `Term::Var(v)`, which
    /// hash-conses to the identical `TermId` the loader built.
    ///
    /// Deliberately NOT `Value` / `ViewItem`: a variable is not a carrier, so
    /// carrier-neutrality buys nothing here — `Value::Var` would only re-admit
    /// carriers that cannot occur, and `ViewItem<'a>` borrows `kb`, which this
    /// record (cloned out of the [`OpSignature`] cache, then read under `&mut
    /// KnowledgeBase`) cannot hold.
    pub type_params: Vec<(Symbol, Var)>,
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
    pub type_params: Vec<(Symbol, Var)>,
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

/// WI-943 — the canonical logical variable `op_sym` DECLARES for the type parameter
/// whose short name is `short`, or `None` when it declares no such parameter.
///
/// THE ONE AUTHORITY for an operation type parameter's identity. The loader mints
/// exactly one `fresh_var` per declared parameter (`kb/load.rs` `load_operation`) and
/// publishes it here; `rigidify_op_type_params` skolemizes THAT var, and
/// [`crate::kb::typing`]'s `type_param_global_var` resolves a written occurrence of the
/// parameter through this function. An operation parameter has no `SortAlias`, so this
/// is the only place its canonical variable is recorded — one store, nothing to
/// disagree with.
///
/// Keyed by SHORT NAME because that is how the loader interns each entry's `Symbol`
/// (`kb.intern("T")`), not as the op-scoped `<ns>.<op>.T` local a body reference
/// resolves to — the same two keyings WI-708 bridges in the other direction
/// (`op_scoped_type_param_symbol`).
///
/// [`declared_arity`]'s sibling in shape: the same two tiers (the WI-656 cached record,
/// then [`lookup_operation_info`] for calls before `build_op_signatures`) and the same
/// reason for existing — reading one variable should not build an [`OpInfoRecord`] on
/// the path that already has the answer cached.
pub fn declared_type_param_var(kb: &KnowledgeBase, op_sym: Symbol, short: &str) -> Option<Var> {
    let pick = |tps: &[(Symbol, Var)]| -> Option<Var> {
        tps.iter().find(|(n, _)| kb.local_name_of(*n) == short).map(|(_, v)| *v)
    };
    if let Some(sig) = kb.op_record(op_sym).and_then(|r| r.signature.as_ref()) {
        return pick(&sig.type_params);
    }
    pick(&lookup_operation_info(kb, op_sym)?.type_params)
}

/// WI-886 — how many parameters does `op_sym` DECLARE? [`operation_is_declared`]'s
/// sibling: same two tiers (the WI-656 cached record, then the pre-
/// `build_op_signatures` fact scan), and the same reason for existing — reading one
/// number should not build an [`OpInfoRecord`], whose construction clones every
/// per-field `Vec` to be dropped immediately.
///
/// ONE OWNER for a question two host backends ask of the same mappings. The rust
/// runtime checks a registered `host_fn`'s arity against this at
/// `register_operation_mappings` (`eval/builtins.rs`), and cpp-gen checks an
/// expression template's `$N` slots against it at `HostOpTable::from_kb`. Before this
/// the two were written separately and could not share: the cheap path is
/// `kb.op_record`, which is `pub(crate)`, so a backend crate could only reach
/// `lookup_operation_info` — the very call the rust side documents itself as avoiding.
pub fn declared_arity(kb: &KnowledgeBase, op_sym: Symbol) -> Option<usize> {
    if let Some(n) = kb
        .op_record(op_sym)
        .and_then(|r| r.signature.as_ref())
        .map(|s| s.params.len())
    {
        return Some(n);
    }
    lookup_operation_info(kb, op_sym).map(|r| r.params.len())
}

/// WI-656 — decode the body-independent [`OpSignature`] from an `OperationInfo`
/// fact head. The SINGLE field-decode, shared by [`lookup_operation_info`]'s
/// fallback and [`build_op_signatures`], so a cached signature and a scanned one
/// can never disagree. `None` when the head lacks a `return_type` (malformed —
/// the pre-WI-656 code likewise bailed the whole lookup on a missing `return_type`).
fn extract_signature_from_head(kb: &KnowledgeBase, head: &Value) -> Option<OpSignature> {
    let type_params = extract_type_params(kb, head);
    signature_from_head_with_type_params(kb, head, type_params)
}

/// [`extract_signature_from_head`] with the `type_params` already decoded — for
/// [`build_op_signatures`], which needs BOTH halves of that decode (the usable
/// parameters and the offenders to report) and must not walk the list twice to get
/// them. `head_field` is not free: it resolves every named key to a `&str` and string-
/// compares, per field, per operation, on every type-check.
fn signature_from_head_with_type_params(
    kb: &KnowledgeBase,
    head: &Value,
    type_params: Vec<(Symbol, Var)>,
) -> Option<OpSignature> {
    let return_type = head_field_value(kb, head, "return_type")?;
    let effects = effects_of_head(kb, head);
    let params = extract_params(kb, head_field(kb, head, "params"));
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
///
/// WI-849 — RETURNS the `type_params` entries that are not logical variables, as
/// `(op symbol, the offending value)`, for the caller to RENDER and report. It travels
/// unrendered because this site has no printer, and as a carrier-agnostic `Value`
/// because a value-fact head's bad entry has no `TermId` to travel as (review). Carried out of THIS pass
/// rather than found by a second sweep: this one already visits every fact and decodes
/// every `type_params` list, and it defines WHICH fact each operation is read from —
/// so the report covers exactly the facts the system consults, no more (a shadowed
/// duplicate is not read, so its contents are not diagnosed) and no less.
#[must_use = "the malformed type-param entries must be reported, not dropped"]
pub fn build_op_signatures(kb: &mut KnowledgeBase) -> Vec<(Symbol, Value)> {
    let Some(op_info_sym) = kb.try_resolve_symbol("anthill.reflect.OperationInfo") else {
        return Vec::new();
    };
    // Collect under the immutable borrow, then insert — the head decode reads
    // `&kb` while the record insert needs `&mut kb`. `seen` keeps only the FIRST
    // fact per op, so a later duplicate the scan would never reach is ignored.
    let mut seen: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
    let mut sigs: Vec<(Symbol, OpSignature)> = Vec::new();
    let mut malformed: Vec<(Symbol, Value)> = Vec::new();
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
        // ONE decode, both halves: the usable parameters go into the cached signature,
        // the offenders out to the caller to render and report. Splitting here rather
        // than in a helper keeps the decode's shape honest — `type_param_entries` takes
        // the list's `TermId` and hands back, per element, either the decoded parameter
        // or that element's `TermId` unchanged; there is nothing to convert an
        // undecodable entry INTO, so it passes through as the handle it arrived as.
        let mut type_params = Vec::new();
        for entry in type_param_entries(kb, head) {
            match entry {
                Ok(p) => type_params.push(p),
                Err(bad) => malformed.push((op_sym, bad)),
            }
        }
        // A malformed first fact caches nothing (signature stays `None`) — the
        // fallback then reproduces the same `None`, so the paths agree.
        if let Some(sig) = signature_from_head_with_type_params(kb, head, type_params) {
            sigs.push((op_sym, sig));
        }
    }
    for (op_sym, sig) in sigs {
        kb.op_records.entry(op_sym).or_default().signature = Some(sig);
    }
    malformed
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
        .find(|s| kb.local_name_of(*s) == key)
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
                let head_el = named.iter().find(|(s, _)| kb.local_name_of(*s) == "head").map(|(_, x)| x);
                let tail = named.iter().find(|(s, _)| kb.local_name_of(*s) == "tail").map(|(_, x)| x);
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

/// Walk a `type_params` list (a ground `TermId` list) into the parameters' own
/// logical variables. Each entry is a `Term::Var(Global(vid))`; the surface name
/// comes from `vid.name()`.
///
/// WI-849 — an entry that is not a `Term::Var(Global)` is skipped HERE and reported via
/// [`type_param_entries`]' `Err` half, which [`build_op_signatures`] carries out of its
/// pass. The skip is not the silent one it replaced:
/// this decode runs under `&KnowledgeBase`, has no error channel, and is reached from
/// load-time paths that run BEFORE the typer exists (the const-purity gate, the
/// eq-dispatch table build), so it is the wrong place to raise from. The sweep that
/// visits every `OperationInfo` fact exactly once — [`build_op_signatures`], called
/// from `type_check_sorts_collect` where the error list lives — is the right one.
///
/// A dropped op type param is invisible in four ways at once, which is why it must be
/// reported SOMEWHERE: [`crate::kb::typing`]'s `check_unconstrained_type_params` never
/// checks it; `resolve_call_type_arg_targets` cannot find its label, so `op[T = …]`
/// reports `NoSuchTypeParam` naming the USER's call for a malformed DECLARATION;
/// `rigidify_op_type_params` never skolemizes it, so the body sees a solvable flex var
/// instead of a rigid (WI-392); and `seed_op_type_args` has nothing to match.
///
/// REACHABILITY, measured twice — and the second measurement is why this is a report
/// rather than a panic. WI-849 found that a hand-written
/// `fact OperationInfo(name: <any resolvable symbol>, return_type: …,
/// type_params: cons(head: 42, tail: nil()), …)` reached this arm from ordinary user
/// source: `type_params` is not a declared field of the stdlib `OperationInfo` entity
/// (the loader appends it via `kb.alloc`, bypassing term conversion), and an undeclared
/// label was accepted everywhere. WI-851 closed THAT — an undeclared constructor label
/// is now refused at load — so no source spelling reaches here today.
///
/// The report stays anyway, and stays non-fatal: what WI-851 closed is the TERM
/// CONVERSION path, not this decode's contract. A producer that asserts an
/// `OperationInfo` fact directly (as the loader itself does) still bypasses that
/// refusal, and a panic would then take down a load over metadata the user never wrote.
fn extract_type_params(kb: &KnowledgeBase, head: &Value) -> Vec<(Symbol, Var)> {
    type_param_entries(kb, head).into_iter().filter_map(|e| e.ok()).collect()
}

/// One `type_params` entry: the decoded parameter, or the thing that could not be one.
/// The SINGLE decode behind both halves — [`extract_type_params`] keeps the `Ok`s,
/// [`build_op_signatures`] reports the `Err`s — so the two can never disagree about
/// which entries were usable.
///
/// CARRIER-NEUTRAL, and the offender is a `Value` rather than a `TermId` for a reason
/// that is structural, not stylistic (review): an `OperationInfo` head is a value fact
/// whenever any param/return/effect is `denoted`-bearing, and a non-term-carried entry
/// — or a non-term-carried FIELD — has NO `TermId` to name it, so a `TermId`-typed error
/// channel could not report the very cases it exists for. Reading the field with the
/// term-only `head_field_term` had the same blind spot one level up: it returns `None`
/// for a value-carried field, indistinguishable from "this operation declares no type
/// parameters". Mirrors [`effects_of_head`] / [`clause_list_field`] / [`extract_params`],
/// which are all carrier-neutral for exactly this reason.
///
/// A field that is present but is NOT A LIST AT ALL (`type_params: 42`) reports as one
/// offender — the field itself. Previously it decoded to zero entries and zero reports,
/// so the operation simply appeared to have no type parameters: the same silent-drop
/// class as a bad element, one layer out.
fn type_param_entries(kb: &KnowledgeBase, head: &Value) -> Vec<Result<(Symbol, Var), Value>> {
    let Some(field) = head_field(kb, head, "type_params") else {
        return Vec::new();
    };
    let field: Value = match field {
        ViewItem::Term(t) => Value::term(t),
        ViewItem::Value(v) => v.clone(),
        ViewItem::Node(occ) => Value::Node(occ),
    };
    let Some(items) = list_items_strict(kb, &field) else {
        return vec![Err(field)];
    };
    items
        .into_iter()
        .map(|entry| match &entry {
            Value::Term { id, .. } => match kb.get_term(*id) {
                Term::Var(Var::Global(vid)) => Ok((vid.name(), Var::Global(*vid))),
                _ => Err(entry),
            },
            Value::Var(Var::Global(vid)) => Ok((vid.name(), Var::Global(*vid))),
            _ => Err(entry),
        })
        .collect()
}

/// A cons/nil list's elements, or `None` when `v` is NOT a list — the distinction
/// [`list_to_vec`] and [`value_list_to_vec`] both erase by `break`ing out of the walk
/// and returning what they had. Carrier-neutral, so a term list and a value list decode
/// alike. Only the top of the spine is classified; a malformed TAIL still truncates, as
/// it does for every other list field.
fn list_items_strict(kb: &KnowledgeBase, v: &Value) -> Option<Vec<Value>> {
    let nil_sym = kb.try_resolve_symbol("anthill.prelude.List.nil");
    let is_nil = |name: &str| name == "nil";
    match v {
        Value::Term { id, .. } => match kb.get_term(*id) {
            Term::Ref(s) if is_nil(kb.local_name_of(*s)) => Some(Vec::new()),
            Term::Fn { functor, .. } => {
                let name = kb.local_name_of(*functor);
                if is_nil(name) {
                    Some(Vec::new())
                } else if name == "cons" {
                    Some(list_to_vec(kb, *id).into_iter().map(Value::term).collect())
                } else {
                    None
                }
            }
            _ => None,
        },
        Value::Entity { functor, .. } => {
            let name = kb.local_name_of(*functor);
            if is_nil(name) || Some(*functor) == nil_sym {
                Some(Vec::new())
            } else if name == "cons" {
                Some(value_list_to_vec(kb, v))
            } else {
                None
            }
        }
        // The `Term::Ref(nil)` arm above, on the other carrier of the same
        // symbol: an empty list is a bare `nil` reference, and reaching `_ =>
        // None` here would classify it MALFORMED rather than empty.
        //
        // Matched to the `Term` arm EXACTLY — local name only. The `Entity` arm
        // below also accepts `Some(*functor) == nil_sym`; adding that here would
        // make this carrier answer on a qualified `nil` its own twin rejects,
        // i.e. codify a new cross-carrier disagreement while fixing one.
        Value::SymbolRef(s) if is_nil(kb.local_name_of(*s)) => Some(Vec::new()),
        _ => None,
    }
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
