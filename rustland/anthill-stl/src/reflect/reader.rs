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
use anthill_core::kb::ClauseKind;
use anthill_core::kb::KnowledgeBase;

// ── Leaf helpers ────────────────────────────────────────────────

/// The short (last dotted segment) of a qualified name.
pub(crate) fn short_of(qualified: &str) -> &str {
    qualified.rsplit('.').next().unwrap_or(qualified)
}

/// A displayable name for any `TermId` — the head symbol of a `Ref`/`Ident`/
/// `Fn`, the rendering of a literal, or a sigil'd var.
pub(crate) fn term_display_name(kb: &KnowledgeBase, id: TermId) -> String {
    match kb.get_term(id) {
        CoreTerm::Ref(sym) | CoreTerm::Ident(sym) => kb.local_name_of(*sym).to_string(),
        CoreTerm::Fn { functor, .. } => kb.local_name_of(*functor).to_string(),
        CoreTerm::Const(Literal::String(s)) => s.clone(),
        CoreTerm::Const(Literal::Int(n)) => n.to_string(),
        CoreTerm::Const(Literal::BigInt(n)) => n.to_string(),
        CoreTerm::Const(Literal::Float(f)) => f.to_string(),
        CoreTerm::Const(Literal::Bool(b)) => b.to_string(),
        CoreTerm::Var(Var::Global(vid)) => format!("?{}", kb.local_name_of(vid.name())),
        CoreTerm::Var(Var::DeBruijn(n)) => format!("?_{n}"),
        CoreTerm::Var(Var::Rigid(vid)) => format!("!{}", kb.local_name_of(vid.name())),
        CoreTerm::Bottom => "⊥".into(),
        CoreTerm::ParseAux(_) => "<parse-aux>".into(),
    }
}

/// The head functor / ident / ref symbol of a `TermId` — the by-reference peer
/// of [`term_display_name`] (it covers the same `Ref`/`Ident`/`Fn` name-bearing
/// arms, so a domain that `term_display_name` matched by string this matches by
/// symbol). Used to match a fact's domain or a `Member`'s parent against an
/// already-resolved sort symbol (WI-632). `None` for a literal, variable, or `⊥`
/// (they name no functor). The anthill-stl analog of core's `pub(crate)`
/// `KnowledgeBase::head_functor`, unreachable from this crate.
pub(crate) fn term_head_sym(kb: &KnowledgeBase, id: TermId) -> Option<Symbol> {
    match kb.get_term(id) {
        CoreTerm::Ref(s) | CoreTerm::Ident(s) | CoreTerm::Fn { functor: s, .. } => Some(*s),
        _ => None,
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
            CoreTerm::Fn {
                functor,
                named_args,
                ..
            } => {
                let name = kb.local_name_of(*functor);
                if name == "nil" {
                    break;
                }
                if name == "cons" {
                    let head = named_args
                        .iter()
                        .find(|(s, _)| kb.local_name_of(*s) == "head");
                    let tail = named_args
                        .iter()
                        .find(|(s, _)| kb.local_name_of(*s) == "tail");
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
        .filter_map(|k| {
            head.named_arg(kb, k)
                .and_then(|i| i.as_term_id())
                .map(|t| (k, t))
        })
        .collect()
}

/// Every asserted row of the declared fact functor `qualified_functor`.
///
/// Reflection rows are declared entities, so readers enumerate their functors
/// through the extent seam rather than leaking a resident `RuleId` bucket.
fn facts_by_functor(kb: &KnowledgeBase, qualified_functor: &str, reader: &str) -> Vec<Value> {
    let Some(functor) = kb.try_resolve_symbol(qualified_functor) else {
        return Vec::new();
    };
    kb.read_facts(
        functor,
        &[],
        anthill_core::kb::extent::BodiedRulePolicy::Refuse,
    )
    .unwrap_or_else(|e| panic!("reflect {reader} read: {e}"))
}

/// Collect the names of every `MemberInfo` of a given `kind` (`Constructor`,
/// `Operation`, …) whose parent is the resolved sort `parent_sym` (WI-632:
/// matched by functor symbol, not by display-name string).
pub(crate) fn members_of_kind(
    kb: &mut KnowledgeBase,
    parent_sym: Symbol,
    kind: &str,
) -> Vec<String> {
    let name_field = kb.intern("name");
    let kind_field = kb.intern("kind");
    let parent_field = kb.intern("parent");
    let mut results = vec![];
    for head in facts_by_functor(kb, "anthill.reflect.MemberInfo", "MemberInfo") {
        let named = term_named_args(kb, &head);
        let field = |key| {
            named
                .iter()
                .find(|(name, _)| *name == key)
                .map(|(_, value)| *value)
        };
        let (Some(name), Some(member_kind), Some(parent)) =
            (field(name_field), field(kind_field), field(parent_field))
        else {
            continue;
        };
        let member_kind = term_display_name(kb, member_kind);
        if short_of(&member_kind) == kind && term_head_sym(kb, parent) == Some(parent_sym) {
            results.push(term_display_name(kb, name));
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
    let facts = kb
        .read_facts(
            sort_info,
            &[],
            anthill_core::kb::extent::BodiedRulePolicy::Refuse,
        )
        .unwrap_or_else(|e| panic!("reflect SortInfo read: {e}"));
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
        let list = |key: Symbol| {
            field(key)
                .map(|t| collect_list_terms(kb, t))
                .unwrap_or_default()
        };
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
    /// The operation's own type parameters, as the logical variables the loader
    /// minted. Ground `TermId`s (each a `Term::Var`), so they need no `Value`.
    pub type_params: Vec<TermId>,
    pub meta: TermId,
}

/// Read the `OperationInfo` facts whose domain is the resolved sort `sort_sym`
/// (WI-632: matched by functor symbol, not by display-name string).
pub(crate) fn read_operations(kb: &mut KnowledgeBase, sort_sym: Symbol) -> Vec<OperationRecord> {
    let meta_default_sym = kb.intern("meta");
    let mut out = Vec::new();
    for head in facts_by_functor(kb, "anthill.reflect.OperationInfo", "OperationInfo") {
        let name = match op_info::head_field_term(kb, &head, "name") {
            Some(t) => t,
            None => continue,
        };
        let Some(op_sym) = op_info::head_name_ref(kb, &head) else {
            continue;
        };
        let Some(scope_sym) = kb.declaring_scope_symbol(op_sym) else {
            continue;
        };
        if scope_sym != sort_sym {
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
        let type_params = op_info::head_field_term(kb, &head, "type_params")
            .map(|t| collect_list_terms(kb, t))
            .unwrap_or_default();
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
            type_params,
            meta,
        });
    }
    out
}

/// One `DescriptionInfo(target, content, index)` fact. The index is the stored
/// 0-based per-target index (WI-438), not a global enumeration.
pub(crate) struct DescriptionRecord {
    pub target: TermId,
    pub content: String,
    pub index: i64,
}

/// Read every `DescriptionInfo` fact, optionally filtered to `target` (full or
/// short name). A malformed or incomplete record is skipped.
pub(crate) fn read_descriptions(
    kb: &mut KnowledgeBase,
    target: Option<&str>,
) -> Vec<DescriptionRecord> {
    let target_field = kb.intern("target");
    let content_field = kb.intern("content");
    let index_field = kb.intern("index");
    let mut out = Vec::new();
    for head in facts_by_functor(kb, "anthill.reflect.DescriptionInfo", "DescriptionInfo") {
        let named = term_named_args(kb, &head);
        let field = |key| {
            named
                .iter()
                .find(|(name, _)| *name == key)
                .map(|(_, value)| *value)
        };
        let (Some(record_target), Some(content), Some(index_term)) = (
            field(target_field),
            field(content_field),
            field(index_field),
        ) else {
            continue;
        };
        let index = match kb.get_term(index_term) {
            CoreTerm::Const(Literal::Int(n)) => *n,
            _ => continue,
        };
        if let Some(t) = target {
            let target_name = term_display_name(kb, record_target);
            if target_name != t && short_of(&target_name) != t {
                continue;
            }
        }
        out.push(DescriptionRecord {
            target: record_target,
            content: term_display_name(kb, content),
            index,
        });
    }
    out
}

/// The head `Value`s of every `Rule` fact whose domain is the resolved sort
/// `sort_sym` (WI-632: matched by functor symbol, not by display-name string).
/// Each realization reifies these to its own term-repr form.
///
/// WI-922 — selects on `by_domain`, the index that actually discriminates here,
/// and applies the clause KIND as a filter. This used to enumerate every
/// `Rule`-keyed clause KB-wide through the retired `by_sort` index and then
/// discard all but one domain's. The set is unchanged: that index's entity-child
/// union could never contribute here, `Rule` being a kind, not a sort.
pub(crate) fn rule_heads_for_sort(kb: &mut KnowledgeBase, sort_sym: Symbol) -> Vec<Value> {
    kb.program_clauses_by_domain(sort_sym)
        .into_iter()
        .filter(|clause| clause.clause_kind == ClauseKind::Rule)
        .map(|clause| clause.head)
        .collect()
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
        Var::Global(vid) => kb.local_name_of(vid.name()).to_string(),
        Var::Rigid(vid) => format!("!{}", kb.local_name_of(vid.name())),
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
    fn on_fn(
        &mut self,
        kb: &mut KnowledgeBase,
        functor: Symbol,
        args: Vec<Self::Repr>,
    ) -> Self::Repr;
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
        ViewHead::Ident(sym) => builder.on_ref(kb, sym),
        // WI-20260902-CZJ2N — A NULLARY APPLICATION REIFIES AS `RefRepr`, NOT AS AN
        // ARGUMENT-LESS `FnRepr`, and this arm has to precede the general `Functor` one
        // to say so. The retired `ViewHead::Ref` carried the distinction before; one
        // term deserves one repr, which is the split this ticket exists to remove.
        //
        // IT IS WIDER THAN THE HEAD IT REPLACES, and that is stated because it is a
        // reflect-SURFACE change. `ViewHead::Ref` covered `Term::Ref(s)` for any `s`
        // plus `Fn{c, [], []}` for a registered CONSTRUCTOR; this covers every nullary
        // head, so two shapes move from `FnRepr(f, [])` to `RefRepr(f)`: a canon-EXEMPT
        // `Fn{S, [], []}` of a `SymbolKind::Sort` name (the empty `ListLiteral()` the
        // reload-faithful printer writes is the live one), and the nullary `Expr::Apply`
        // `Loader::nullary_op_call_or_ref` now mints for `:- flag`.
        //
        // CENSUSED, not assumed: the corpus has ONE consumer of these constructors —
        // `examples/guardians/lib/gate.anthill`'s `repr_name` / `spec_of_row` — and it
        // reads BOTH arms for a nullary name, by its own comment's design ("Reading only
        // one of them would work for sorts and silently fail for entities"). So the move
        // is invisible to it. The PRINTER is unaffected either way: `persistence::print`
        // reads the raw `Term::Fn` and still writes `ListLiteral()` with its parentheses
        // in reload-faithful mode, so the persistence round trip does not go through
        // here.
        ViewHead::Functor {
            functor: Some(sym),
            pos_arity: 0,
            named_arity: 0,
        } => builder.on_ref(kb, sym),
        // Both realizations reify `⊥` as a `Ref` named `"⊥"`.
        ViewHead::Bottom => {
            let bottom = kb.intern("⊥");
            builder.on_ref(kb, bottom)
        }
        ViewHead::Functor {
            functor: Some(functor),
            pos_arity,
            named_arity,
        } => {
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
