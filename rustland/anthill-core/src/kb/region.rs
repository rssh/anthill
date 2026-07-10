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
use super::KnowledgeBase;
use super::typing::{
    external_effects, extract_effect_resource_sym, extract_sort_ref_sym, substitute_ref_syms,
    TypingEnv,
};
use crate::eval::value::Value;
use crate::intern::{Symbol, SymbolKind};

/// The sorts admitted by `Modifiable[T = …]` facts (`{Cell}` in the
/// current stdlib). A result type that structurally mentions one of these
/// can carry a freshly-allocated region out of the operation, so a
/// `Modify[result]` on such an op is kept rather than masked. Sourcing the
/// set from the facts (rather than hard-coding `Cell`) means a future
/// `Modifiable` resource that grows a `Modify[result]` constructor is
/// handled without touching this module.
pub(crate) fn region_sorts(kb: &KnowledgeBase) -> HashSet<Symbol> {
    let mut out = HashSet::new();
    let modifiable = match kb.try_resolve_symbol("anthill.prelude.Modifiable") {
        Some(s) => s,
        None => return out, // no Modifiable facts loaded — nothing admits a region
    };
    for rid in kb.rules_by_functor(modifiable) {
        let Some(head) = kb.fact_head_term(rid) else { continue };
        collect_sort_refs(kb, head, modifiable, &mut out);
    }
    out
}

/// Collect every `sort_ref` symbol reachable in `term`, skipping `skip`
/// (the `Modifiable` head itself). Robust to either fact-head shape —
/// `Modifiable[T = Cell]` stored as `Fn{functor: Modifiable, T: Cell}` or
/// as `parameterized(sort_ref(Modifiable), bindings: [T = Cell])`.
fn collect_sort_refs(kb: &KnowledgeBase, term: TermId, skip: Symbol, out: &mut HashSet<Symbol>) {
    // `extract_sort_ref_sym` names the sort for both a deep `sort_ref` and the
    // bare `Ref(Cell)` a `Modifiable[T = Cell]` type-arg takes (WI-361), so one
    // check covers both fact-head shapes.
    if let Some(s) = extract_sort_ref_sym(kb, &super::term_view::TermIdView(term)) {
        if s != skip {
            out.insert(s);
        }
        return;
    }
    for child in kb.get_term(term).subterms() {
        collect_sort_refs(kb, child, skip, out);
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

/// Whether `ty` can carry a modifiable region out of the operation — i.e.
/// its own type structure mentions a `regions` sort (directly, via a tuple
/// field, a list / parameterized type-arg, or a bare type variable, for
/// which it conservatively returns `true` and keeps the effect).
///
/// NARROW-SLICE LIMITATION (WI-314): this inspects the *return type's
/// structure* only. A region reachable solely through a returned **named
/// sort's field** (e.g. `-> Pair` where `Pair` has a `Cell` field) is not
/// seen, so such a `Modify[result]` is masked — an unsound drop. Closing it
/// needs type-param-aware reachability over sort definitions, deferred to
/// proposal 046. Unreachable in the current stdlib: no op returns a
/// fresh-cell-bearing named sort.
pub(crate) fn result_type_admits_region(
    kb: &KnowledgeBase,
    ty: TermId,
    regions: &HashSet<Symbol>,
) -> bool {
    // `extract_sort_ref_sym` names the sort for both a deep `sort_ref` and the
    // bare `Ref(S)` a type-arg takes (WI-361).
    if let Some(s) = extract_sort_ref_sym(kb, &super::term_view::TermIdView(ty)) {
        if regions.contains(&s) {
            return true;
        }
    }
    // WI-361: a term-backed parameterized region (`-> Cell[V]` = `Fn{Cell, named}`)
    // carries its base sort as the FUNCTOR, which `subterms()` excludes — check it
    // directly so the region is still admitted (the deep `parameterized(base:
    // sort_ref(Cell), …)` form keeps the base reachable via the subterm recursion).
    if let Term::Fn { functor, .. } = kb.get_term(ty) {
        if regions.contains(functor) {
            return true;
        }
    }
    kb.get_term(ty)
        .subterms()
        .iter()
        .any(|&child| result_type_admits_region(kb, child, regions))
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
fn resolve_op_result_sym(kb: &KnowledgeBase, op_sym: Symbol) -> Option<Symbol> {
    kb.try_resolve_symbol(&format!("{}.result", kb.qualified_name_of(op_sym)))
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
/// gated on the same return-type escape test as WI-314; neither → dropped).
/// Mixed provenance (a foldLeft accumulator fed by both the seed and the
/// callback's own output) keeps the union. `op_sym` supplies those candidate
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
    // 2. Result-region masking, keyed on whether the result can carry one.
    // WI-341: the return type is carrier-agnostic. A `Value::Node` return type is
    // denoted-bearing — an op returning a `Modify`-carrying callback; a function
    // value carries no escaping DATA region, so it does not admit one (and such
    // an op never has a `Modify[result]` in its row to mask anyway).
    let admits = match return_type {
        Value::Term { id: t, .. } => result_type_admits_region(kb, *t, regions),
        _ => false,
    };
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
                    let result_place =
                        *op_result_sym_memo.get_or_insert_with(|| resolve_op_result_sym(kb, op_sym));
                    let kept = match result_place {
                        Some(target) => rekey_resource_value(kb, &effect, sym, target),
                        None => effect,
                    };
                    push_effect_dedup(kb, &mut out, kept);
                }
                // else: the fresh region cannot reach the result — drop.
            }
            Some(sym) if kb.kind_of(sym) == Some(SymbolKind::CallbackParam) => {
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
                    // DATA places only: the op's non-callback params + its
                    // `result`. A callback param is a function value, never a
                    // modifiable re-key target — exclude it (a `Param` carries
                    // its arrow's places, so `arg_places` non-empty marks it).
                    let mut v: Vec<Symbol> = kb
                        .symbols
                        .arg_places(op_sym)
                        .iter()
                        .copied()
                        .filter(|&p| kb.symbols.arg_places(p).is_empty())
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
                // No candidate held → drop. Sound when the WI-352 flow facts
                // fully captured the feed: the callback was fed a fresh,
                // non-escaping local (absence is the drop, 046 feed spec).
                // LIMITATION (v1, mirrors the WI-314 narrow slice above): if
                // `flow_derive` under-approximated the feed — e.g. the callback
                // arg is a library-accessor result, or a nested-callback
                // application it does not model — there is *also* no solution, so
                // the label is dropped: an unsound drop. Not reachable from
                // source yet (a callback's `Modify[a]` cannot reach the boundary
                // until the binder→place front-end, WI-341/342); when it goes
                // live the sound coarse fallback is the doc's all-to-all keep
                // (046 §"Role of kind", the flow-presence conservative axis).
            }
            _ => {
                // Parameter / unknown resource — external, keep.
                push_effect_dedup(kb, &mut out, effect);
            }
        }
    }
    out
}

/// WI-353: whether `keep_modify(place, into)` holds via the WI-352 `feed` rules
/// + `provenance` builtin, queried in **checking** mode (both arguments ground).
/// The enumerate form `keep_modify(place, ?r)` residualizes — the resolver
/// delays a rule whose body has the `provenance` builtin with an unbound output
/// — so the boundary classifier instead checks each candidate `into` place it
/// already has in hand (the op's inputs + result). A genuine, residual-free
/// solution is required; an absent `feed` substrate (e.g. `reflect/feed` not
/// loaded) yields `false` (nothing to keep), leaving the label to drop.
///
/// The `.any()` scans *all* solutions — it must NOT be reduced to
/// `max_solutions: 1` + first-solution: the resolver can return a residual
/// (delayed) solution before the residual-free one, so taking only the first
/// would report `false` for a label that genuinely holds (an unsound drop).
fn keep_modify_holds(kb: &mut KnowledgeBase, place: Symbol, into: Symbol) -> bool {
    let km = match kb.try_resolve_symbol("anthill.reflect.feed.keep_modify") {
        Some(s) => s,
        None => return false,
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
        let real = kb.symbols.define(
            "Cell.new.result",
            "Cell.new.result",
            crate::intern::SymbolKind::OpResult,
            0,
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
/// registered places. The input effect row is built synthetically — a callback's
/// `Modify[<its own arrow param>]` cannot yet reach the boundary from source (the
/// binder→place wiring is WI-341/342), so `modify_label` stands in for it,
/// keyed to the genuine `CallbackParam` place the loader registered.
#[cfg(test)]
mod wi353_tests {
    use super::*;
    use crate::kb::load::{self, NullResolver};
    use crate::parse;
    use std::collections::HashSet;
    use std::path::{Path, PathBuf};

    const OPS: &str = r#"
namespace anthill.test.wi353
  import anthill.prelude.{List, Unit, Cell, Int64}

  -- foreach: the callback is applied to each element of `l`, so the element
  -- place `f.a` is fed `element_of` from `l`.
  operation each(l: List[T = Cell], f: (a: Cell) -> Unit) -> Unit =
    match l
      case nil() -> unit
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

    fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
        if dir.is_dir() {
            for e in std::fs::read_dir(dir).unwrap() {
                let p = e.unwrap().path();
                if p.is_dir() {
                    collect(&p, out);
                } else if p.extension().is_some_and(|x| x == "anthill") {
                    out.push(p);
                }
            }
        }
    }

    fn load_ops() -> KnowledgeBase {
        let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../stdlib/anthill");
        let mut files = Vec::new();
        collect(&dir, &mut files);
        let mut parsed: Vec<_> = files
            .iter()
            .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).unwrap())
            .collect();
        parsed.push(parse::parse(OPS).expect("parse ops"));
        let refs: Vec<_> = parsed.iter().collect();
        let mut kb = KnowledgeBase::new();
        load::register_prelude(&mut kb);
        kb.register_standard_builtins();
        // flow_derive runs in the load pipeline regardless of typecheck outcome.
        let _ = load::load_all(&mut kb, &refs, &NullResolver);
        kb
    }

    fn sym(kb: &KnowledgeBase, qn: &str) -> Symbol {
        kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("resolve {qn}"))
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
            TypeChild::Ground(base),
            vec![(t, TypeChild::Node(denoted))],
            sp,
            None,
        ))
    }

    fn resources(kb: &KnowledgeBase, row: &[Value]) -> HashSet<Symbol> {
        row.iter().filter_map(|e| extract_effect_resource_sym(kb, e)).collect()
    }

    /// Run `op_boundary_effects` for `<op_qn>` with a return type of sort `ret`
    /// and a single synthetic `Modify[<op_qn>.<modify_on>]` input label; return
    /// the resource-symbol set of the masked row.
    fn boundary(kb: &mut KnowledgeBase, op_qn: &str, ret_qn: &str, modify_on: &str) -> HashSet<Symbol> {
        let op_sym = sym(kb, op_qn);
        let regions = region_sorts(kb);
        let ret = sym(kb, ret_qn);
        let ret_ty = Value::term(kb.alloc(Term::Ref(ret)));
        let resource = sym(kb, &format!("{op_qn}.{modify_on}"));
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
        let got = boundary(&mut kb, "anthill.test.wi353.each", "anthill.prelude.Unit", "f.a");
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
        let got = boundary(&mut kb, "anthill.test.wi353.foldCell", "anthill.prelude.Cell", "f.a");
        assert_eq!(
            got,
            [z, result].into_iter().collect(),
            "foldLeft accumulator is fed by the seed `z` (input) AND the fresh \
             callback output escaping the Cell result — keep both, the union"
        );
    }

    #[test]
    fn fold_result_type_cannot_carry_region_masks_it() {
        let mut kb = load_ops();
        let z = sym(&kb, "anthill.test.wi353.foldInt.z");
        let got = boundary(&mut kb, "anthill.test.wi353.foldInt", "anthill.prelude.Int64", "f.a");
        assert_eq!(
            got,
            [z].into_iter().collect(),
            "an `Int64` result cannot carry the region: the escaping-to-result \
             component is masked (WI-314 escape test); only the seed `z` survives"
        );
    }

    #[test]
    fn element_param_modify_surfaces_on_source_list_only() {
        // `foldCell.f.t` is fed `element_of` from `xs` only — a Modify on it
        // surfaces on `xs`, not on the seed `z` or the `result`.
        let mut kb = load_ops();
        let xs = sym(&kb, "anthill.test.wi353.foldCell.xs");
        let got = boundary(&mut kb, "anthill.test.wi353.foldCell", "anthill.prelude.Cell", "f.t");
        assert_eq!(
            got,
            [xs].into_iter().collect(),
            "the element param `f.t` comes only from `xs`"
        );
    }
}
