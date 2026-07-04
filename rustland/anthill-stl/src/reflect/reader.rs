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
//! Term reification (`reify` / `reflect`) is now shared too (WI-555): the one
//! [`reify_walk`] / [`reflect_walk`] each way walks the `Const`/`Var`/`Ref`/`Fn`
//! structure, and a realization supplies a [`ReifyBuilder`] / [`ReflectReader`]
//! that maps the neutral leaves to its carrier — reconciling the different
//! in-band name carrier (a `Ref` term vs a `Symbol`) at that single boundary.
//! The per-parameter `FieldInfo` decode is the one remaining per-realization
//! reader.
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
use anthill_core::kb::term_view::{TermView, ViewHead};
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

/// The `(field_name, field_type)` pairs of the entity declaration matching
/// `name` (full or short constructor name), read carrier-agnostically — a
/// `denoted` field type rides as its own `Value::Node`, surfaced verbatim by
/// both realizations. `None` if no registered entity matches. Backed by the
/// KB's `entity_field_types` registry via [`KnowledgeBase::resolve_entity_functor`]
/// (WI-515: the same-functor "schema fact" under sort `Entity` is gone — a
/// fact carrying TYPE terms in data slots polluted every var-quantified query
/// over the constructor); an ambiguous short name resolves to the minimal
/// qualified name, deterministically.
pub(crate) fn read_entity_fields(kb: &KnowledgeBase, name: &str) -> Option<Vec<(Symbol, Value)>> {
    let functor = kb.resolve_entity_functor(name)?;
    let fields = kb
        .entity_field_types(functor)
        .expect("resolve_entity_functor returns a registered functor")
        .to_vec();
    Some(fields)
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

// ── Shared term reify / reflect walk (WI-555) ───────────────────
//
// The forward `reify` (a KB term → a flat term-repr) and inverse `reflect`
// (a term-repr → a KB term) each had a realization per caller: the interpreter
// builds `Value::Entity` `TermRepr` trees ([`super::builtins`]), the host bridge
// the generated `TermRepr` enum ([`super::bridge`]). Both are the SAME recursion
// over the `Const`/`Var`/`Ref`/`Fn`/`Bottom` structure — differing only in the
// output carrier and in the in-band NAME carrier (a `Ref` term vs a `Symbol`).
// [`reify_walk`] / [`reflect_walk`] are the one walk each way; a realization
// supplies a [`ReifyBuilder`] / [`ReflectReader`] that maps the neutral leaves
// to its carrier, reconciling the name representation at that single boundary.

/// The display name of a var of any kind, in the spelling both reify
/// realizations use: a bare name for a flex `Global`, `!name` for a `Rigid`
/// skolem, `_n` for a bound `DeBruijn`.
pub(crate) fn var_repr_name(kb: &KnowledgeBase, var: Var) -> String {
    match var {
        Var::Global(vid) => kb.resolve_sym(vid.name()).to_string(),
        Var::Rigid(vid) => format!("!{}", kb.resolve_sym(vid.name())),
        Var::DeBruijn(n) => format!("_{n}"),
    }
}

/// Maps the neutral leaves of a term-structure walk to a realization's output
/// carrier. [`reify_walk`] calls exactly one method per node; each realization
/// decides the carrier (a `Value::Entity` tree vs the generated `TermRepr`
/// enum) and how a `Ref`/`Fn` name rides (a `Ref` term vs a `Symbol`). `kb` is
/// threaded so a realization can allocate an in-band name term.
pub(crate) trait ReifyBuilder {
    type Repr;
    fn on_literal(&mut self, kb: &mut KnowledgeBase, lit: Literal) -> Self::Repr;
    fn on_var(&mut self, kb: &mut KnowledgeBase, name: String) -> Self::Repr;
    fn on_ref(&mut self, kb: &mut KnowledgeBase, name: Symbol) -> Self::Repr;
    fn on_fn(&mut self, kb: &mut KnowledgeBase, functor: Symbol, args: Vec<Self::Repr>)
        -> Self::Repr;
}

/// Walk any [`TermView`] carrier and reify it via `builder`. The single reifier
/// behind both `KB::reify` and `KB::rules` for every realization: it reads
/// structure through `TermView`, so a hash-consed `TermId`, a `Value::Node`
/// occurrence, or a `Value::Entity` all produce the same shape. A `⊥` reifies as
/// a `Ref` named `"⊥"` (both realizations' prior behavior); a functor-less
/// aggregate or opaque value in a term slot panics loudly.
pub(crate) fn reify_walk<V: TermView, B: ReifyBuilder>(
    kb: &mut KnowledgeBase,
    view: &V,
    builder: &mut B,
) -> B::Repr {
    // A var of any kind → a `VarRepr`. `index_var` surfaces Global / Rigid /
    // DeBruijn uniformly, including a var-headed `Value::Node` occurrence (whose
    // `head` reads `Opaque`); the `ViewHead::Var` arm below covers the carriers
    // whose `head` does surface the var. Either path yields the same name.
    if let Some(var) = view.index_var(kb) {
        return builder.on_var(kb, var_repr_name(kb, var));
    }
    // `head` returns an owned `ViewHead` (no borrow retained), so each arm is
    // free to take `&mut kb` for `kb.intern` / the builder callback / the
    // recursion. In the `Fn` arm the children are materialized to owned
    // `Value`s BEFORE recursing, so no `ViewItem` borrow spans a mutation.
    match view.head(kb) {
        ViewHead::Var(var) => builder.on_var(kb, var_repr_name(kb, var)),
        ViewHead::Const(lit) => builder.on_literal(kb, lit),
        ViewHead::Ref(sym) | ViewHead::Ident(sym) => builder.on_ref(kb, sym),
        // Both realizations reify `⊥` as a `Ref` named `"⊥"`.
        ViewHead::Bottom => {
            let bottom = kb.intern("⊥");
            builder.on_ref(kb, bottom)
        }
        ViewHead::Functor { functor: Some(functor), pos_arity, named_arity } => {
            let named_keys = view.named_keys(kb);
            let mut children = Vec::with_capacity(pos_arity + named_arity);
            for i in 0..pos_arity {
                let child = view.pos_arg(kb, i).unwrap_or_else(|| {
                    panic!("reify_walk: positional arg {i} missing below arity {pos_arity}")
                });
                children.push(child.to_value());
            }
            // A key from `named_keys` MUST resolve via `named_arg` (same backing
            // store); a `None` is a carrier bug, surfaced loudly (mirrors the
            // positional arm) rather than silently dropping the argument.
            for key in named_keys {
                let child = view.named_arg(kb, key).unwrap_or_else(|| {
                    panic!("reify_walk: named arg from named_keys missing in named_arg lookup")
                });
                children.push(child.to_value());
            }
            let mut args = Vec::with_capacity(children.len());
            for child in &children {
                args.push(reify_walk(kb, child, builder));
            }
            builder.on_fn(kb, functor, args)
        }
        ViewHead::Functor { functor: None, .. } | ViewHead::Opaque => panic!(
            "reify_walk: non-term carrier in a Term slot (functor-less aggregate \
             or opaque value)",
        ),
    }
}

/// The neutral shape a reified term-repr decodes to — the inverse of the
/// [`ReifyBuilder`] leaves. `Fn` children are again `R`, so [`reflect_walk`]
/// recurses carrier-agnostically. A `⊥` and a `QuotedRepr` have no dedicated
/// shape: the former decodes to a `Ref`, the latter to a `Const` string (both
/// resolved inside a realization's [`ReflectReader::classify`]).
pub(crate) enum ReflectShape<R> {
    Const(Literal),
    Var(String),
    Ref(Symbol),
    Fn(Symbol, Vec<R>),
}

/// Classifies one node of a term-repr into a [`ReflectShape`]. The realization
/// reconciles its in-band name carrier here (the interpreter reads a `Ref` term,
/// the bridge a `Symbol`), so [`reflect_walk`] sees only neutral leaves. The
/// associated `Error` lets the dynamically-typed interpreter reader signal a
/// malformed repr while the closed-enum bridge reader stays `Infallible`.
pub(crate) trait ReflectReader: Sized {
    type Error;
    fn classify(self, kb: &KnowledgeBase) -> Result<ReflectShape<Self>, Self::Error>;
}

/// Rebuild a hash-consed KB term from a term-repr, classified via `R`. The one
/// inverse behind both `KB::reflect` realizations; the allocation of each core
/// term (`Const` / `Var` / `Ref` / `Fn`) lives here, so a realization only
/// decodes leaves. A `VarRepr` mints a fresh `Global` (mirrors both prior
/// realizations).
pub(crate) fn reflect_walk<R: ReflectReader>(
    kb: &mut KnowledgeBase,
    repr: R,
) -> Result<TermId, R::Error> {
    match repr.classify(kb)? {
        ReflectShape::Const(lit) => Ok(kb.alloc(CoreTerm::Const(lit))),
        ReflectShape::Var(name) => {
            let sym = kb.intern(&name);
            let vid = kb.fresh_var(sym);
            Ok(kb.alloc(CoreTerm::Var(Var::Global(vid))))
        }
        ReflectShape::Ref(sym) => Ok(kb.alloc(CoreTerm::Ref(sym))),
        ReflectShape::Fn(functor, children) => {
            let mut ids = Vec::with_capacity(children.len());
            for child in children {
                ids.push(reflect_walk(kb, child)?);
            }
            Ok(kb.alloc(CoreTerm::Fn {
                functor,
                pos_args: ids.into(),
                named_args: Default::default(),
            }))
        }
    }
}

