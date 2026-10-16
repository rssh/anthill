//! WI-314 — region / escape masking for the `Modify[result]` effect.
//!
//! A constructor like `Cell.new : Modify[result]` is honest about
//! initializing the fresh region it returns (proposal 045 §5.5). Left
//! unmasked that effect goes *viral*: every cell-allocating operation
//! would have to redeclare it. This module is the operation-boundary
//! masking that stops the virality without lying about the effect at the
//! call site:
//!
//! - a `Modify[<result-region>]` (a fresh region produced by a sub-call,
//!   e.g. `Cell.new`) is **dropped** when the operation's return type
//!   cannot carry that region — the cell is discarded (`make_and_read :
//!   Int64`), so the write is unobservable;
//! - it is **kept**, re-keyed to the operation's own `result`, when the
//!   return type *can* carry it (`make : Cell`) — the op honestly
//!   allocates a fresh region it hands out;
//! - effects on **let/match-bound locals** keep their existing drop
//!   (`external_effects`); effects on **parameters** stay external.
//!
//! Organization (option 3′ of
//! `docs/brainstorms/region-analysis-organization.md`): a factored,
//! separately-testable region/effect module the typer calls at its
//! existing operation-boundary frame — not scattered inline, not a
//! post-typer pass, not a generic plugin-engine. The interface is
//! deliberately plugin-shaped (`env + return-type + effect row → masked /
//! re-keyed row`) so it promotes cleanly to the fused typer plugin-engine
//! tracked as WI-315 when a second mini-phase arrives. It is the narrow
//! *result-reachability* slice of proposal 046; 046 grows the same module
//! with full provenance / aliasing / higher-order cases.

use std::collections::{HashMap, HashSet};

use smallvec::SmallVec;

use super::resolve::ResolveConfig;
use super::term::{Term, TermId};
use super::term_view::TermView;
use super::typing::{
    external_effects, extract_effect_resource_sym, extract_type, extract_type_param,
    substitute_ref_syms, TypeExtractor, TypingEnv,
};
use super::KnowledgeBase;
use crate::eval::value::Value;
use crate::intern::{Symbol, SymbolKind};

/// The MODIFIABLE SORTS: the sort each `Modifiable[T = …]` claim's `T` binding names
/// (its head sort — `Cell` for `Cell[V = V]`, never a type parameter), closed over
/// `provides` — a sort that provides a modifiable sort is one, a refinement being the
/// resource its spec is (`NonMonotonicStore provides Store`, and `Store` claims
/// `Modifiable`). Built once per pass, so a reader asks `contains`.
///
/// The one set behind every reading of "a `Modify` can fire here" ([`type_admits_modify`]):
/// result masking, the boundary's re-key targets, and `check_modify_targets`. It used to
/// collect every sort reachable ANYWHERE in a claim's head — an over-approximation meant
/// for masking — so `provides Modifiable[T = Box[V = Int64]]` put `Int64` in it and every
/// `Modify` over an `Int64` place then passed the declaration check, program-wide
/// (WI-20260823-TR8CF review). A result that merely MENTIONS a modifiable sort is still
/// kept: [`admits_modify`] walks the type's arguments and fields for it. The reflect op
/// `anthill.reflect.is_modifiable` asks the same predicate, so reflection and the kernel
/// cannot disagree.
///
/// ONE CHANNEL, THE PROVISION RELATION (WI-862, WI-20260917-S8JYF). A claim is a
/// `provides Modifiable[T = …]` wherever it is written — a sort body, or a `namespace
/// <Carrier>` secondary entry. A raw `fact Modifiable[T = X]` claims nothing about any
/// spec and is not read; reading the raw-fact index alone once went blind on the
/// migrated stdlib (`is_modifiable(Cell)` answered false).
///
/// COST: one bucket of the keyed provider index per modifiable sort (`Modifiable`'s, then
/// each found sort's providers), not a walk of the relation. `type_check_sorts` computes
/// it once per typing pass and threads it in (WI-20260920-E3DC5: it once ran per SORT,
/// 204 times on a stdlib load, each a full walk — the `debug_assert` at its old site in
/// `check_operation_bodies` pins the hoist's loop-invariance); `check_modify_targets` and
/// the written-row gate compute it lazily, only when some place needs judging; the
/// reflect op per call.
pub(crate) fn region_sorts(kb: &KnowledgeBase) -> HashSet<Symbol> {
    let mut out = HashSet::new();
    let Some(modifiable) = kb.try_resolve_symbol("anthill.prelude.Modifiable") else {
        return out; // no Modifiable claims loaded — nothing admits a region
    };
    let mut queue: Vec<Symbol> = Vec::new();
    for (_, view) in super::typing::provisions_of_spec(kb, modifiable) {
        let claimed = extract_type_param(kb, &view, "T").and_then(|bound| type_head_sort(kb, &bound));
        if let Some(sort) = claimed.filter(|&s| !super::typing::is_sort_param_symbol(kb, s)) {
            if out.insert(sort) {
                queue.push(sort);
            }
        }
    }
    // Closed over `provides`: each modifiable sort's own providers, to a fixpoint — a
    // provider of a provider is one too.
    while let Some(sort) = queue.pop() {
        for (provider, _) in super::typing::provisions_of_spec(kb, sort) {
            if out.insert(provider) {
                queue.push(provider);
            }
        }
    }
    out
}

/// The head sort a type NAMES: `Cell` for both the bare `Cell` and the
/// parameterized `Cell[V = Int64]`. `None` for a type that names no sort (a type
/// variable, an arrow, a value-in-type). Carrier-agnostic via `extract_type`, so
/// either fact-head encoding (term-backed `Fn{S, named}` or deep
/// `parameterized(base, bindings)`) reads the same.
fn type_head_sort<V: TermView>(kb: &KnowledgeBase, ty: &V) -> Option<Symbol> {
    match extract_type(kb, ty) {
        TypeExtractor::SortRef(s) => Some(s),
        TypeExtractor::Parameterized { base, .. } => Some(base),
        _ => None,
    }
}

/// True when `sym` is an operation's reserved return-value name
/// (`<op>.result`, proposal 041) — the resource a constructor's
/// `Modify[result]` refers to. Field-projection forms (`result.a`) are
/// deferred: no constructor emits them yet.
///
/// WI-341 step 1: this is now a **symbol-identity** membership test against
/// the result-binder set populated by `scan_operation_params` — not a
/// spelling match on the symbol's name. Symbols already carry identity; the
/// prior `rsplit('.') == "result"` encoded the result-region *role* in the
/// name and parsed it back, which mis-classified any unrelated symbol whose
/// last segment happened to be `result`. Identity membership removes that
/// fragility (and the string work).
pub(crate) fn is_result_region_sym(kb: &KnowledgeBase, sym: Symbol) -> bool {
    kb.is_result_binder(sym)
}

/// Whether `ty` can carry a modifiable region out of the operation — the one
/// predicate [`type_admits_modify`] (WI-20260823-TR8CF). It used to be a walk of its
/// own over the type's structure, and the two disagreed: an arrow's PARAMETER types were
/// walked here (a `Cell` its later caller supplies counted as carried out) and refused
/// there, so an operation could be asked to declare a `Modify[result]` the declaration
/// check then refused, and a region
/// reachable only through a returned named sort's FIELD (`-> Pair`, a `Cell` inside)
/// was masked — WI-314's recorded narrow slice, an unsound drop, now gone because the
/// shared walk follows fields.
pub(crate) fn result_type_admits_region<V: TermView>(
    kb: &KnowledgeBase,
    ty: &V,
    regions: &HashSet<Symbol>,
) -> bool {
    type_admits_modify(kb, ty, regions)
}

/// Whether a place of type `ty` can be the target of a `Modify`. `Modify` fires only
/// on a modifiable type (`Modifiable`, `effects.anthill`; proposal 037 Rule 8), and
/// this is the one reading of it: result masking ([`result_type_admits_region`]), the
/// boundary's re-key targets, the vacuous-label drop, and `check_modify_targets`'
/// refusal all ask it, so an operation is never asked to declare a label the
/// declaration check refuses (WI-20260823-TR8CF). Read so that a place is refused only
/// when its type is known to hold none: it admits when the type is a modifiable sort
/// ([`region_sorts`]), has a type argument that admits (`List[T = Cell]`), is a data
/// sort an entity field of which admits (`Wrap` holding a `Cell`), is a tuple with such
/// a field, or is a type variable or parameter (it may be instantiated with a `Cell`)
/// or anything else this does not read. A function value — an arrow, or `Function[A,
/// B]` — admits through what it RETURNS and never through its parameters, which its
/// later caller supplies. An effect row never admits, nor a sort with no constructors
/// that is not modifiable (`Int64`).
pub(crate) fn type_admits_modify<V: TermView>(kb: &KnowledgeBase, ty: &V, regions: &HashSet<Symbol>) -> bool {
    admits_modify(kb, ty, regions, true, &mut HashSet::new(), None)
}

/// [`type_admits_modify`]'s DEFINITE reading: the same walk, with whatever it cannot read
/// — a type variable, an unbound parameter (a bare `List`'s element), an unbound
/// `Function` result, a shape it does not know — counted as admitting NONE. What the
/// reflect op `anthill.reflect.is_modifiable` answers: a query wants "yes, a `Modify` can
/// fire here", where the typer refuses only on "no, it cannot". On a concrete type the two
/// agree, the walk being one.
pub(crate) fn type_definitely_admits_modify<V: TermView>(
    kb: &KnowledgeBase,
    ty: &V,
    regions: &HashSet<Symbol>,
) -> bool {
    admits_modify(kb, ty, regions, false, &mut HashSet::new(), None)
}

/// [`type_admits_modify`]'s walk. `free` is set while an entity field of some
/// sort is read: the canonical variables of that sort's type parameters which
/// the application being followed bound to a type that does not admit. A field
/// declaration writes a parameter AS that variable (`cons(head: T, …)` reads
/// `head` as an anonymous variable, the one `T` published — WI-954), so a
/// variable not there is unknown. `unknown` is what anything unknown answers — `true` for
/// the typer, `false` for the definite reading. `visiting` is the sorts whose fields are
/// being read further up (a recursive sort's own field decides nothing new).
fn admits_modify<V: TermView>(
    kb: &KnowledgeBase,
    ty: &V,
    regions: &HashSet<Symbol>,
    unknown: bool,
    visiting: &mut HashSet<Symbol>,
    free: Option<&HashSet<u32>>,
) -> bool {
    let var_admits = |id: u32| unknown && !free.is_some_and(|ids| ids.contains(&id));
    // The type of a function value, written as an application.
    let is_function = |s: Symbol| kb.qualified_name_of(s) == "anthill.prelude.Function";
    match extract_type(kb, ty) {
        TypeExtractor::SortRef(s) => {
            if regions.contains(&s) {
                true
            } else if super::typing::is_sort_param_symbol(kb, s) {
                param_var_id(kb, s).map_or(unknown, var_admits)
            } else if is_function(s) {
                // `Function` with its result unbound: it may return anything.
                unknown
            } else {
                // Its own parameters, if it has any, are unbound here: nothing is known
                // of them, so they answer as anything unknown does.
                fields_admit_modify(kb, s, regions, unknown, visiting, &HashSet::new())
            }
        }
        TypeExtractor::FlexVar { id, .. } => var_admits(id),
        TypeExtractor::TypeVar(_) | TypeExtractor::Skolem { .. } => unknown,
        TypeExtractor::Parameterized { base, bindings } => {
            if regions.contains(&base) {
                return true;
            }
            if is_function(base) {
                // A function value carries out what it RETURNS (`B`), never what it is
                // handed (`A`); an unbound `B` may be anything.
                return bindings
                    .iter()
                    .find(|(param, _)| kb.local_name_of(*param) == "B")
                    .map_or(unknown, |(_, result)| admits_modify(kb, result, regions, unknown, visiting, free));
            }
            let mut bound_free = HashSet::new();
            for (param, value) in &bindings {
                if admits_modify(kb, value, regions, unknown, visiting, free) {
                    return true;
                }
                let name = kb.local_name_of(*param);
                let declared = kb
                    .type_param_syms_of(base)
                    .iter()
                    .find(|&&p| kb.local_name_of(p) == name);
                if let Some(id) = declared.and_then(|&p| param_var_id(kb, p)) {
                    bound_free.insert(id);
                }
            }
            fields_admit_modify(kb, base, regions, unknown, visiting, &bound_free)
        }
        TypeExtractor::NamedTuple(fields) => fields
            .iter()
            .any(|(_, t)| admits_modify(kb, t, regions, unknown, visiting, free)),
        // A function value carries out what it returns: a closure handing back its fresh
        // cell (`-> (x: Int64) -> Cell`) carries the cell; its parameters' types are the
        // later caller's to supply, never carried out (`-> (c: Cell) -> Int64`).
        TypeExtractor::Arrow { result, .. } => admits_modify(kb, &result, regions, unknown, visiting, free),
        TypeExtractor::PolyType { body, .. } => admits_modify(kb, &body, regions, unknown, visiting, free),
        // An effect row or a value standing in a type: no value of the place's own.
        TypeExtractor::Nothing | TypeExtractor::EffectsRows(_) | TypeExtractor::Denoted(_) => false,
        _ => unknown,
    }
}

/// The id of the canonical variable a type parameter is written as (WI-954).
pub(crate) fn param_var_id(kb: &KnowledgeBase, param: Symbol) -> Option<u32> {
    let var = kb.canonical_type_param_var(param)?;
    match extract_type(kb, &Value::term(var)) {
        TypeExtractor::FlexVar { id, .. } => Some(id),
        _ => None,
    }
}

/// Whether some entity field of `sort` admits a `Modify` ([`admits_modify`]),
/// `free` holding the variables of the sort's parameters bound to a type that
/// does not.
fn fields_admit_modify(
    kb: &KnowledgeBase,
    sort: Symbol,
    regions: &HashSet<Symbol>,
    unknown: bool,
    visiting: &mut HashSet<Symbol>,
    free: &HashSet<u32>,
) -> bool {
    if !visiting.insert(sort) {
        return false;
    }
    let field_types: Vec<Value> = kb
        .field_constructors_of_sort(sort)
        .into_iter()
        .filter_map(|c| kb.entity_field_types(c))
        .flat_map(|fields| fields.iter().map(|(_, t)| t.clone()))
        .collect();
    let admits = field_types
        .iter()
        .any(|t| admits_modify(kb, t, regions, unknown, visiting, Some(free)));
    visiting.remove(&sort);
    admits
}

/// Re-key an effect's resource symbol `from` → `to` (a callee's
/// `Cell.new.result` → the enclosing op's own `result`), so the propagated
/// label is well-scoped in the caller and matches its declaration.
fn rekey_resource(kb: &mut KnowledgeBase, effect: TermId, from: Symbol, to: Symbol) -> TermId {
    let mut map = HashMap::new();
    map.insert(from, to);
    substitute_ref_syms(kb, effect, &map)
}

/// WI-342 effects-vertical: carrier-agnostic [`rekey_resource`]. A ground label
/// re-keys via `substitute_ref_syms`; a `Value::Node` label needs occurrence
/// `Ref` rewrite — deferred to E2 (no Node effect label is minted pre-E2).
fn rekey_resource_value(kb: &mut KnowledgeBase, effect: &Value, from: Symbol, to: Symbol) -> Value {
    match effect {
        Value::Term { id: t, .. } => Value::term(rekey_resource(kb, *t, from, to)),
        // WI-342 E2: re-key the `Ref` spine of a `Value::Node` label (a callee's
        // fresh `Modify[c]` → the enclosing op's `Modify[result]`) via the
        // occurrence rewriter — the carrier peer of `rekey_resource`.
        Value::Node(occ) => {
            let mut map = HashMap::new();
            map.insert(from, to);
            Value::Node(super::node_occurrence::substitute_ref_syms_occ(occ, &map))
        }
        other => other.clone(),
    }
}

/// Push `effect` into `out` unless a structurally-equal label is already present.
/// `Value` has no `PartialEq`; WI-486 dedups via the carrier-aware
/// [`views_structurally_equal`] so a ground `Value::Term` label and a now-live
/// `Value::Node` label (`Modify[c]`) of the same structure dedup across carriers
/// (the old carrier-blind compare called those distinct).
fn push_effect_dedup(kb: &KnowledgeBase, out: &mut Vec<Value>, effect: Value) {
    if !out
        .iter()
        .any(|e| crate::kb::term_view::views_structurally_equal(kb, e, &effect))
    {
        out.push(effect);
    }
}

/// WI-657(11): resolve an operation's reserved `<op>.result` symbol (the re-key
/// target for a `Modify[result]` that escapes via the return value). Split out so
/// [`op_boundary_effects`] can resolve it LAZILY — only when the result-region or
/// callback-param arm actually fires — instead of the caller resolving it eagerly
/// for every typed op (the common effect-free op never needs it).
/// WI-1122-era note: `pub(crate)` because [`crate::kb::typing`]'s override-refinement
/// pass needs the same symbol to align a spec op's result binder with an override's
/// (contract clauses over `result` are otherwise incomparable — the two binders are
/// distinct symbols). One resolver rather than two spellings of the same `format!`.
pub(crate) fn resolve_op_result_sym(kb: &KnowledgeBase, op_sym: Symbol) -> Option<Symbol> {
    let sym = kb.try_resolve_symbol(&format!("{}.result", kb.qualified_name_of(op_sym)))?;
    // The NAME is not the property; the KIND is. `<op>.<param>.result` is minted
    // for a callback's result with kind `CallbackResult`, and a type parameter
    // spelled `result` merges into the same symbol via `define`'s add_kind path,
    // so a lookalike must not be treated as the op's own binder — the rule
    // `region::result_region_is_kind_not_spelling` pins.
    kb.is_result_binder(sym).then_some(sym)
}

/// Operation-boundary effect masking (WI-314 + WI-353). Given the body's
/// derived effect row and the op's return type (the op's reserved `<op>.result`
/// re-key target is resolved lazily inside — WI-657(11)), return the
/// externally-visible row: locals dropped, escaping fresh regions kept (re-keyed to
/// `result`), non-escaping fresh regions dropped, parameters left external. See the
/// module header.
///
/// WI-353 — the `Modify` slice of `effect_derive` (proposal 046). A `Modify` on
/// a **callback parameter** place (`<op>.f.a`, kind `CallbackParam`) is not a
/// caller-visible resource as written: the binder `a` is meaningless outside the
/// callback's arrow. Such a label is resolved against the op's own data by the
/// WI-352 flow facts — `keep_modify(f.a, into)` (checking mode) over the op's
/// argument places + `result` — and kept re-keyed to each `into` that holds
/// (input origin → that input; fresh output escaping the result → `result`,
/// gated on the same return-type escape test as WI-314; a place whose feeds the
/// flow pass did not trace → every input and `result`; none of these →
/// dropped). Mixed provenance (a foldLeft accumulator fed by both the seed and
/// the callback's own output) keeps the union. `op_sym` supplies those candidate
/// `into` places (`SymbolTable::arg_places`).
pub(crate) fn op_boundary_effects(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    return_type: &Value,
    op_sym: Symbol,
    regions: &HashSet<Symbol>,
    effects: &[Value],
) -> Vec<Value> {
    // WI-657(11): the op's `<op>.result` symbol, resolved LAZILY (see
    // [`resolve_op_result_sym`]). Only the result-region masking arm and the (rare)
    // callback-param arm read it, so the common effect-free op skips the
    // `format!("{op}.result")` + `try_resolve` the caller previously ran for EVERY
    // typed op. `Option<Option<_>>`: outer `None` = not yet resolved, inner = the
    // resolution result (itself possibly `None`).
    let mut op_result_sym_memo: Option<Option<Symbol>> = None;
    // 1. Existing local-resource drop (let/match-bound names).
    let after_local = external_effects(kb, env, effects);
    // 2. Result-region masking, keyed on whether the result can carry one — asked of
    // the type's structure through the view, whichever carrier it rides. A result
    // type that was no term answered "no" outright, as a function value's; so an
    // operation returning a fresh cell through a type that holds a value, or one
    // written through an alias, had its `Modify[result]` masked and owed no
    // declaration (MEASURED: `dup(n: Int64) -> Cell` loaded with the `Cell` on an
    // occurrence).
    let admits = result_type_admits_region(kb, return_type, regions);
    // WI-353: candidate `into` places for a callback-parameter `Modify` — the
    // op's own DATA argument places plus its `result`. Built lazily (only the
    // rare `CallbackParam` arm reads it; the common op carries no such effect).
    let mut into_candidates: Option<Vec<Symbol>> = None;
    let mut out: Vec<Value> = Vec::with_capacity(after_local.len());
    for effect in after_local {
        match extract_effect_resource_sym(kb, &effect) {
            Some(sym) if is_result_region_sym(kb, sym) => {
                if admits {
                    // Escapes via the result — re-key to the op's own
                    // `result` and keep (the op honestly allocates).
                    let result_place = *op_result_sym_memo
                        .get_or_insert_with(|| resolve_op_result_sym(kb, op_sym));
                    let kept = match result_place {
                        Some(target) => rekey_resource_value(kb, &effect, sym, target),
                        None => effect,
                    };
                    push_effect_dedup(kb, &mut out, kept);
                }
                // else: the fresh region cannot reach the result — drop.
            }
            // A place of ANOTHER operation's callback is not this op's to mask:
            // its feeds are that op's, none of whose places is a candidate below,
            // so the classifier would drop it whatever it does. It falls to the
            // last arm and stays as written. Identity is enough: every operation
            // (an `operation` block's entries too) gets its own symbol, whose
            // scope `scan_operation_params` registers its places under, and the
            // typer types the body under that same symbol.
            Some(sym)
                if kb.kind_of(sym) == Some(SymbolKind::CallbackParam)
                    && kb.symbols.declaring_scope(sym).map(|s| s.owner()) == Some(op_sym) =>
            {
                // WI-353: a callback parameter's latent `Modify[f.a]`. Resolve
                // its origin(s) by flow reachability and keep one re-keyed label
                // per candidate `into` place that `keep_modify` holds for. `kind`
                // is not consulted — v1 re-keys every edge as `direct` (re-key to
                // the whole source), a sound coarsening (046 §"Role of kind").
                // WI-657(11): resolve `<op>.result` once for this (rare) arm via
                // the shared memo; the `into_candidates` closure captures the plain
                // `Copy` value, and the gate below reuses it.
                let op_result =
                    *op_result_sym_memo.get_or_insert_with(|| resolve_op_result_sym(kb, op_sym));
                let candidates = into_candidates.get_or_insert_with(|| {
                    // DATA places only: the op's params a `Modify` can fire on +
                    // its `result` (gated below by `admits`). A callback param is a
                    // function value, never a modifiable re-key target — exclude it
                    // (a `() -> T` one too, whose argument places are empty), and
                    // every param whose type admits no `Modify` (`Int64`, a
                    // `Function[…]`), which re-keying would charge with one that
                    // then spreads to every caller.
                    let mut v: Vec<Symbol> = kb
                        .symbols
                        .arg_places(op_sym)
                        .iter()
                        .copied()
                        .filter(|&p| {
                            !kb.symbols.is_callable(p) && param_admits_modify(kb, op_sym, p, regions)
                        })
                        .collect();
                    if let Some(r) = op_result {
                        v.push(r);
                    }
                    v
                });
                // `keep_modify` is queried in *checking* mode against each
                // candidate (the enumerate form `keep_modify(p, ?r)` residualizes
                // on the `provenance` builtin's unbound output; WI-352 caveat).
                for &into in candidates.iter() {
                    if !keep_modify_holds(kb, sym, into) {
                        continue;
                    }
                    // Re-keying to the op result is additionally gated on the
                    // return type actually being able to carry the region — the
                    // same WI-314 escape test: a fresh output that *reaches* the
                    // result by dataflow but a result type that cannot hold it is
                    // masked. Re-keying to an input place keeps unconditionally
                    // (the input is externally visible).
                    if op_result == Some(into) && !admits {
                        continue;
                    }
                    let kept = rekey_resource_value(kb, &effect, sym, into);
                    push_effect_dedup(kb, &mut out, kept);
                }
                // No candidate held → drop. That needs evidence: `keep_modify`
                // drops only a place `flow_derive` marked `traced` — every value
                // reaching it followed to a source — whose sources are all fresh
                // and non-escaping (absence is the drop, 046 feed spec). A place
                // whose feed the pass did not follow (an ordinary call's result,
                // a callback aliased or handed on) has no `traced` fact and is
                // kept on every candidate: the all-to-all fallback, the
                // flow-presence conservative axis (046 §"Role of kind").
            }
            // A `Modify` re-keyed onto this op's OWN parameter whose type admits none —
            // a generic callee instantiated at `Int64` (`touch[T](x: T) effects
            // Modify[x]` called as `touch(n)`). Nothing at such a place can be mutated,
            // so the label is vacuous and dropped (user, 2026-10-16), and the caller owes
            // no declaration the declaration check would refuse. A WRITTEN `Modify[n]` on
            // a concrete non-modifiable type is still refused, by `check_modify_targets`.
            Some(sym)
                if kb.kind_of(sym) == Some(SymbolKind::Param)
                    && kb.symbols.declaring_scope(sym).map(|s| s.owner()) == Some(op_sym)
                    && is_modify_effect(kb, &effect)
                    && !param_admits_modify(kb, op_sym, sym, regions) => {}
            _ => {
                // Parameter / unknown resource / another op's callback place —
                // external, keep.
                push_effect_dedup(kb, &mut out, effect);
            }
        }
    }
    out
}

/// Whether `op_sym`'s parameter place `param` is of a type a `Modify` can fire on
/// ([`type_admits_modify`]), its type read off the operation's signature by name. A
/// parameter the signature does not list is not known to admit none, so it admits.
fn param_admits_modify(kb: &KnowledgeBase, op_sym: Symbol, param: Symbol, regions: &HashSet<Symbol>) -> bool {
    let name = kb.local_name_of(param);
    kb.op_record(op_sym)
        .and_then(|r| r.signature.as_ref())
        .and_then(|sig| sig.params.iter().find(|(q, _)| kb.local_name_of(*q) == name))
        .is_none_or(|(_, ty)| type_admits_modify(kb, ty, regions))
}

/// Whether `effect` is a `Modify` label (the prelude's).
fn is_modify_effect(kb: &KnowledgeBase, effect: &Value) -> bool {
    match extract_type(kb, effect) {
        TypeExtractor::Parameterized { base, .. } | TypeExtractor::SortRef(base) => {
            kb.qualified_name_of(base) == "anthill.prelude.Modify"
        }
        _ => false,
    }
}

/// WI-353: whether `keep_modify(place, into)` holds via the WI-352 `feed` rules
/// + `provenance` builtin, queried in **checking** mode (both arguments ground).
/// The enumerate form `keep_modify(place, ?r)` residualizes — the resolver
/// delays a rule whose body has the `provenance` builtin with an unbound output
/// — so the boundary classifier instead checks each candidate `into` place it
/// already has in hand (the op's inputs + result). A genuine, residual-free
/// solution is required. An absent `feed` substrate (e.g. `reflect/feed` not
/// loaded) yields `true`: with no flow facts nothing proves the label may drop,
/// so it is kept on every candidate.
///
/// The `.any()` scans *all* solutions — it must NOT be reduced to
/// `max_solutions: 1` + first-solution: the resolver can return a residual
/// (delayed) solution before the residual-free one, so taking only the first
/// would report `false` for a label that genuinely holds (an unsound drop).
fn keep_modify_holds(kb: &mut KnowledgeBase, place: Symbol, into: Symbol) -> bool {
    let km = match kb.try_resolve_symbol("anthill.reflect.feed.keep_modify") {
        Some(s) => s,
        None => return true,
    };
    let p_term = kb.alloc(Term::Ref(place));
    let into_term = kb.alloc(Term::Ref(into));
    let goal = kb.alloc(Term::Fn {
        functor: km,
        pos_args: SmallVec::from_slice(&[p_term, into_term]),
        named_args: SmallVec::new(),
    });
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .any(|s| s.residual.is_empty())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// WI-352: `is_result_region_sym` is kind-based, not spelling-based. A
    /// symbol whose name merely *ends in* `.result` but is not classified
    /// `SymbolKind::OpResult` must NOT be a result region (the pre-WI-341
    /// `rsplit('.') == "result"` match would have wrongly returned true). A
    /// symbol classified `OpResult` returns true. (WI-341 first moved this off
    /// spelling onto symbol identity; WI-351 used a side-table; WI-352 makes
    /// the symbol's kind carry the truth.)
    #[test]
    fn result_region_is_kind_not_spelling() {
        let mut kb = KnowledgeBase::new();

        // A symbol spelled like a result name but NOT classified `OpResult` —
        // e.g. a user sort/field that happens to be called `result`.
        let lookalike = kb.intern("SomeSort.result");
        assert!(
            !is_result_region_sym(&kb, lookalike),
            "a non-`OpResult` `*.result` symbol must not be a result region \
             (kind, not spelling)"
        );

        // A symbol classified `OpResult` is recognised.
        let root_scope = kb.global_scope();
        let real = kb.symbols.define(
            "Cell.new.result",
            "Cell.new.result",
            crate::intern::SymbolKind::OpResult,
            root_scope,
        );
        assert!(
            is_result_region_sym(&kb, real),
            "an `OpResult`-kind symbol must be recognised"
        );

        // And the lookalike is still rejected.
        assert!(!is_result_region_sym(&kb, lookalike));
    }
}

/// WI-353 — the `Modify` slice of `effect_derive` (proposal 046): the
/// `op_boundary_effects` callback-parameter classifier, exercised against the
/// **real** WI-352 flow facts (derived from each op's body) and the **real**
/// registered places. The input effect row is built synthetically (`modify_label`,
/// keyed to the genuine `CallbackParam` place the loader registered), so a label
/// no source program puts in a row can be asked too. The same verdicts from
/// source, through the whole pipeline, are `wi341_callback_modify_test`.
#[cfg(test)]
mod wi353_tests {
    use super::*;
    use std::collections::HashSet;

    const OPS: &str = r#"
namespace anthill.test.wi353
  import anthill.prelude.{List, Unit, Cell, Int64}
  import anthill.prelude.List.{cons, nil}

  -- foreach: the callback is applied to each element of `l`, so the element
  -- place `f.a` is fed `element_of` from `l`.
  operation each(l: List[T = Cell], f: (a: Cell) -> Unit) -> Unit =
    match l
      case nil() -> ()
      case cons(h, rest) -> f(h)

  -- foldLeft over a region-bearing accumulator. The accumulator place `f.a`
  -- is fed by the seed `z` (an input) AND the callback's own output `f.result`
  -- (a fresh value, escaping through the `Cell` result).
  operation foldCell(xs: List[T = Cell], z: Cell, f: (a: Cell, t: Cell) -> Cell) -> Cell =
    match xs
      case nil() -> z
      case cons(h, rest) -> foldCell(rest, f(z, h), f)

  -- Same shape, but the result type `Int64` cannot carry a region — the
  -- escaping-to-result component is masked.
  operation foldInt(xs: List[T = Int64], z: Int64, f: (a: Int64, t: Int64) -> Int64) -> Int64 =
    match xs
      case nil() -> z
      case cons(h, rest) -> foldInt(rest, f(z, h), f)
end
"#;

    fn load_ops() -> KnowledgeBase {
        crate::kb::test_support::load_stdlib(Some(OPS))
    }

    fn sym(kb: &KnowledgeBase, qn: &str) -> Symbol {
        kb.try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("resolve {qn}"))
    }

    /// A synthetic ground `Modify[T = <resource>]` label, the shape the loader's
    /// value-in-type lowering produces (`parameterized` + `denoted(Ref(_))`).
    fn modify_label(kb: &mut KnowledgeBase, resource: Symbol) -> Value {
        // WI-366: production mints a Node `Modify[resource]` via `make_denoted_occ`
        // (the value-in-type carrier); build the SAME carrier here — the
        // carrier-agnostic `op_boundary_effects` / `extract_type` readers accept it,
        // and no ground-`denoted` producer remains. The `Modify` base is a real
        // `sort_ref` (a well-formed `parameterized` type, WI-361).
        use crate::kb::node_occurrence::TypeChild;
        use crate::span::{SourceId, SourceSpan};
        let base = kb.make_sort_ref_by_name("Modify");
        let t = kb.intern("T");
        let sp = SourceSpan::new(SourceId::from_raw(0), 0, 0);
        let denoted = kb.make_denoted_occ_ref(resource, sp, None);
        Value::Node(kb.make_parameterized_occ(
            TypeChild::Interned(base),
            vec![(t, TypeChild::Node(denoted))],
            sp,
            None,
        ))
    }

    fn resources(kb: &KnowledgeBase, row: &[Value]) -> HashSet<Symbol> {
        row.iter()
            .filter_map(|e| extract_effect_resource_sym(kb, e))
            .collect()
    }

    /// Run `op_boundary_effects` for `<op_qn>` with a return type of sort `ret`
    /// and a single synthetic `Modify[<op_qn>.<modify_on>]` input label; return
    /// the resource-symbol set of the masked row.
    fn boundary(
        kb: &mut KnowledgeBase,
        op_qn: &str,
        ret_qn: &str,
        modify_on: &str,
    ) -> HashSet<Symbol> {
        let resource = format!("{op_qn}.{modify_on}");
        boundary_of(kb, op_qn, ret_qn, &resource)
    }

    /// `boundary` for a label on any place, `resource_qn` qualified in full.
    fn boundary_of(
        kb: &mut KnowledgeBase,
        op_qn: &str,
        ret_qn: &str,
        resource_qn: &str,
    ) -> HashSet<Symbol> {
        let op_sym = sym(kb, op_qn);
        let regions = region_sorts(kb);
        let ret = sym(kb, ret_qn);
        let ret_ty = Value::term(kb.alloc(Term::Ref(ret)));
        let resource = sym(kb, resource_qn);
        let row = vec![modify_label(kb, resource)];
        let env = TypingEnv::empty();
        // WI-657(11): `<op>.result` is now resolved lazily inside op_boundary_effects.
        let out = op_boundary_effects(kb, &env, &ret_ty, op_sym, &regions, &row);
        resources(kb, &out)
    }

    #[test]
    fn foreach_callback_modify_surfaces_on_list() {
        let mut kb = load_ops();
        let l = sym(&kb, "anthill.test.wi353.each.l");
        let got = boundary(
            &mut kb,
            "anthill.test.wi353.each",
            "anthill.prelude.Unit",
            "f.a",
        );
        assert_eq!(
            got,
            [l].into_iter().collect(),
            "foreach: a Modify on the element param `f.a` must surface as Modify[l]"
        );
    }

    #[test]
    fn fold_accumulator_mixed_provenance_keeps_seed_and_result() {
        let mut kb = load_ops();
        let z = sym(&kb, "anthill.test.wi353.foldCell.z");
        let result = sym(&kb, "anthill.test.wi353.foldCell.result");
        let got = boundary(
            &mut kb,
            "anthill.test.wi353.foldCell",
            "anthill.prelude.Cell",
            "f.a",
        );
        assert_eq!(
            got,
            [z, result].into_iter().collect(),
            "foldLeft accumulator is fed by the seed `z` (input) AND the fresh \
             callback output escaping the Cell result — keep both, the union"
        );
    }

    /// An all-`Int64` fold: neither component survives. The result type cannot
    /// carry the region (the WI-314 escape test masks the escaping-to-result
    /// component), and the seed `z: Int64` admits no `Modify` — `Modify` fires
    /// only on a modifiable type — so the input component is masked too. It kept
    /// `{z}` before the input targets were gated by type.
    #[test]
    fn fold_over_types_admitting_no_modify_masks_both_components() {
        let mut kb = load_ops();
        let got = boundary(
            &mut kb,
            "anthill.test.wi353.foldInt",
            "anthill.prelude.Int64",
            "f.a",
        );
        assert_eq!(
            got,
            HashSet::new(),
            "an `Int64` result cannot carry the region and an `Int64` seed admits no \
             `Modify`: nothing survives"
        );
    }

    #[test]
    fn element_param_modify_surfaces_on_source_list_only() {
        // `foldCell.f.t` is fed `element_of` from `xs` only — a Modify on it
        // surfaces on `xs`, not on the seed `z` or the `result`.
        let mut kb = load_ops();
        let xs = sym(&kb, "anthill.test.wi353.foldCell.xs");
        let got = boundary(
            &mut kb,
            "anthill.test.wi353.foldCell",
            "anthill.prelude.Cell",
            "f.t",
        );
        assert_eq!(
            got,
            [xs].into_iter().collect(),
            "the element param `f.t` comes only from `xs`"
        );
    }

    /// A label on ANOTHER operation's callback place is not `each`'s to mask: it
    /// stays as written. Without the owner check it went to `keep_modify` against
    /// `each`'s candidates, none of which `foldCell`'s flow facts name, and was
    /// dropped (both places traced). FAILS with the owner check backed out.
    #[test]
    fn another_ops_callback_place_stays_as_written() {
        let mut kb = load_ops();
        let foreign = sym(&kb, "anthill.test.wi353.foldCell.f.a");
        let got = boundary_of(
            &mut kb,
            "anthill.test.wi353.each",
            "anthill.prelude.Unit",
            "anthill.test.wi353.foldCell.f.a",
        );
        assert_eq!(
            got,
            [foreign].into_iter().collect(),
            "a foreign callback place is external to `each`: kept, not re-keyed or dropped"
        );
    }
}

/// WI-20260823-TR8CF — result masking and the declaration check ask one predicate.
#[cfg(test)]
mod tr8cf_tests {
    use super::*;

    const SRC: &str = r#"
namespace anthill.test.tr8cfmask
  import anthill.prelude.{Int64, Cell}
  operation mk_fn() -> (u: Cell[V = Int64]) -> Int64
end
"#;

    /// A function value carries no region out, though a `Cell` is among its parameter
    /// types. FAILS with masking's own walk restored: it walked the arrow's children and
    /// answered yes, so an op returning such a value could be asked to declare a
    /// `Modify[result]` the declaration check refuses.
    #[test]
    fn a_function_value_result_carries_no_region() {
        let kb = crate::kb::test_support::load_stdlib(Some(SRC));
        let op = kb
            .try_resolve_symbol("anthill.test.tr8cfmask.mk_fn")
            .expect("mk_fn");
        let ret = kb
            .op_record(op)
            .and_then(|r| r.signature.as_ref())
            .map(|sig| sig.return_type.clone())
            .expect("mk_fn's return type");
        let regions = region_sorts(&kb);
        assert!(!result_type_admits_region(&kb, &ret, &regions));
    }
}
