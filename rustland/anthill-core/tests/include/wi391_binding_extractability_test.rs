//! WI-391: a spec BINDING VALUE used in a type position lowers to the CANONICAL,
//! EXTRACTABLE `Ref(S)` shape on BOTH emission paths — `fact Spec[…]` (parse
//! `convert_type_value` → `Ref`) and `provides`/`requires Spec[…]` (loader
//! `sort_binding_to_value` → `Ref`). Before WI-391 the `provides`/`requires` path lowered a
//! concrete bare-sort binding (`T = Int64`) to a nullary `Fn{Int64}` via `name_to_sort_term`
//! — a shape `type_head` classifies as MALFORMED → `TypeExtractor::Error`, violating the
//! §5.3 EXTRACTABILITY CRITERION ("no type is ever an opaque value; every type value's
//! backing term classifies into exactly one structural TypeExtractor variant").
//!
//! Decision (user, "normalize early"): normalize at the PRODUCER, not at the consumer — so
//! the binding is `Ref(Int64)` (a `SortRef`), byte-identical to the `fact`-head path; the
//! kind (a dispatch wildcard type-param vs a concrete sort) is recovered DOWNSTREAM from the
//! symbol (`is_sort_param_symbol`), never from the shape. This retired the scattered late
//! `normalize_ground_leaf` patches (the consumer-side normalization).
//!
//! Acceptance (ticket): after the decision, extract() over every stored type-position value
//! in the loaded stdlib yields a non-Error variant.

use anthill_core::intern::Symbol;
use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::typing::{extract_type, get_named_arg, TypeExtractor};
use anthill_core::kb::KnowledgeBase;

/// The (param, value) binding pairs of a spec `SortView` term — its named args.
fn spec_binding_values(kb: &KnowledgeBase, spec: TermId) -> Vec<(Symbol, TermId)> {
    match kb.get_term(spec) {
        Term::Fn { named_args, .. } => named_args.iter().copied().collect(),
        _ => Vec::new(),
    }
}

/// The binding value a spec carries for the (short-named) member `short`.
fn binding_named(kb: &KnowledgeBase, spec: TermId, short: &str) -> Option<TermId> {
    spec_binding_values(kb, spec)
        .into_iter()
        .find(|(p, _)| kb.resolve_sym(*p) == short)
        .map(|(_, v)| v)
}

/// The `spec` term of the `SortProvidesInfo` fact whose `sort_ref` is `carrier_qn`.
fn provides_spec_for(kb: &KnowledgeBase, carrier_qn: &str) -> Option<TermId> {
    let info = kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo")?;
    let carrier = kb.try_resolve_symbol(carrier_qn)?;
    for rid in kb.rules_by_functor(info) {
        if !kb.is_fact(rid) {
            continue;
        }
        let Some(named) = kb.fact_head_named_args(rid) else { continue };
        let Some(sr) = get_named_arg(kb, &named, "sort_ref") else { continue };
        let matches_carrier = match kb.get_term(sr) {
            Term::Ref(s) => *s == carrier,
            Term::Fn { functor, .. } => *functor == carrier,
            _ => false,
        };
        if matches_carrier {
            return get_named_arg(kb, &named, "spec");
        }
    }
    None
}

const FIXTURE: &str = r#"
namespace test.wi391
  import anthill.prelude.Int64
  sort WI391Spec
    sort T = ?
  end
  sort FactCarrier
    fact WI391Spec[T = Int64]
  end
  sort ProvCarrier
    provides WI391Spec[T = Int64]
  end
end
"#;

/// THE WI-391 OUTCOME: a concrete bare-sort binding (`T = Int64`) extracts as `SortRef`
/// (non-Error) on BOTH the `fact` and `provides` paths, and the two now produce a
/// BYTE-IDENTICAL hash-consed `Ref(Int64)` — the divergence (`Ref` vs nullary `Fn`) is gone.
#[test]
fn concrete_binding_extracts_as_sortref_and_fact_provides_unify() {
    let kb = crate::common::load_kb_with(FIXTURE);
    let int64 = kb
        .try_resolve_symbol("anthill.prelude.Int64")
        .expect("Int64 sort");

    let fact_spec = provides_spec_for(&kb, "test.wi391.FactCarrier").expect("FactCarrier spec");
    let prov_spec = provides_spec_for(&kb, "test.wi391.ProvCarrier").expect("ProvCarrier spec");
    let fact_t = binding_named(&kb, fact_spec, "T").expect("fact T binding");
    let prov_t = binding_named(&kb, prov_spec, "T").expect("provides T binding");

    for (label, t) in [("fact", fact_t), ("provides", prov_t)] {
        match extract_type(&kb, &t) {
            TypeExtractor::SortRef(s) => assert_eq!(
                s, int64,
                "{label} `T = Int64` binding must extract as SortRef(Int64)"
            ),
            other => panic!(
                "{label} `T = Int64` binding must be the extractable SortRef shape, got {other:?} \
                 (backing term {:?})",
                kb.get_term(t)
            ),
        }
    }
    assert_eq!(
        fact_t, prov_t,
        "WI-391: the `fact` and `provides` concrete bindings must be the SAME canonical \
         hash-consed `Ref(Int64)` term (byte-identical SortProvidesInfo)"
    );
}

/// ACCEPTANCE SWEEP (ticket): extract() over EVERY stored type-position binding value of
/// EVERY `SortProvidesInfo` / `SortRequiresInfo` fact in the loaded stdlib yields a non-Error
/// TypeExtractor variant. (Value-fact specs — denoted-bearing effect rows — are term-only
/// skipped via `fact_head_named_args`; the ground/term specs this sweep covers are exactly
/// where the nullary-`Fn` Error arose.)
///
/// WI-449 CLOSED the last carve-out: `fact Effect[T = Modify[?]]` / `Effect[T = Error[?]]`
/// lowered their binding VALUE to a POSITIONAL `Fn{Modify, pos:[?], named:[]}` (parse builds
/// these without the `type_params_of_sort` it lacks), which `type_head` classifies as Error.
/// The loader's `canonicalize_fact_binding_value` now maps such values positional→named (the
/// same lowering `sort_inst_to_value` applies on the `provides` path), so NO binding extracts
/// as Error anymore — the toleration is gone and any Error is a hard failure.
#[test]
fn stdlib_spec_bindings_all_extract_non_error() {
    let kb = crate::common::load_kb_with("");
    let mut checked = 0usize;
    for info in [
        "anthill.reflect.SortProvidesInfo",
        "anthill.reflect.SortRequiresInfo",
    ] {
        let Some(sym) = kb.try_resolve_symbol(info) else { continue };
        for rid in kb.rules_by_functor(sym) {
            if !kb.is_fact(rid) {
                continue;
            }
            let Some(named) = kb.fact_head_named_args(rid) else { continue };
            let Some(spec) = get_named_arg(&kb, &named, "spec") else { continue };
            for (param, val) in spec_binding_values(&kb, spec) {
                assert!(
                    !matches!(extract_type(&kb, &val), TypeExtractor::Error),
                    "{info} binding `{}` = {:?} extracts as TypeExtractor::Error — every stored \
                     type-position value must classify into a structural TypeExtractor variant \
                     (WI-391 / WI-449 / §5.3 extractability criterion)",
                    kb.resolve_sym(param),
                    kb.get_term(val),
                );
                checked += 1;
            }
        }
    }
    assert!(
        checked > 0,
        "expected to extract over at least one stdlib spec binding value"
    );
    eprintln!("WI-391/449 extractability sweep: {checked} spec bindings, all non-Error");
}

// ── WI-449: the FACT path canonicalizes POSITIONAL / NESTED parameterized binding
// values (gap 1: a positional-parameterized VALUE `Modify[?]`; gap 2: a nested
// positional parameterized binding `Inner[Int64]` the parser used to flatten to
// `Ref(Inner)`), so every fact-derived spec binding extracts non-Error AND is
// byte-identical to the equivalent `provides` binding.

const W449_FIXTURE: &str = r#"
namespace test.wi449
  import anthill.prelude.{Int64, Modify}
  -- gap 1: the binding VALUE is itself positional-parameterized (`Modify[?]`).
  sort W449Effect
    sort T = ?
  end
  sort W449EffCarrier
    fact W449Effect[T = Modify[?]]
  end
  -- gap 2: a NESTED positional parameterized binding (`W449Inner[Int64]`), emitted
  -- via both the `fact` (positional) and `provides` (explicit-named) paths.
  sort W449Inner
    sort E = ?
  end
  sort W449Outer
    sort C = ?
  end
  sort W449FactCarrier
    fact W449Outer[W449Inner[Int64]]
  end
  sort W449ProvCarrier
    provides W449Outer[C = W449Inner[Int64]]
  end
end
"#;

/// The base sort symbol a canonical spec binding value names: the functor of a
/// `SortView(base-name, …)`'s `pos[0]` (the wrapped form `sort_inst_to_value` /
/// `canonicalize_fact_binding_value` build for a parameterized binding), or a bare
/// `Ref` / `Fn` functor. Mirrors the loader's `unwrap_spec_view` reader.
fn binding_base_sym(kb: &KnowledgeBase, tid: TermId) -> Option<Symbol> {
    match kb.get_term(tid) {
        Term::Fn { functor, pos_args, .. } => {
            if kb.qualified_name_of(*functor).ends_with("SortView") {
                pos_args.first().and_then(|p| match kb.get_term(*p) {
                    Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => {
                        Some(*functor)
                    }
                    _ => None,
                })
            } else {
                Some(*functor)
            }
        }
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        _ => None,
    }
}

/// GAP 1: `fact Effect[T = Modify[?]]` — the positional-parameterized binding VALUE
/// `Modify[?]` (`Fn{Modify, pos:[?], named:[]}` as parsed, which `type_head`
/// classifies as `Error`) is re-lowered to the canonical `SortView(Modify, T = ?)`
/// carrier, so it extracts non-Error and names `Modify`.
#[test]
fn fact_positional_parameterized_binding_value_extracts_non_error() {
    let kb = crate::common::load_kb_with(W449_FIXTURE);
    let modify = kb
        .try_resolve_symbol("anthill.prelude.Modify")
        .expect("Modify sort");

    let spec = provides_spec_for(&kb, "test.wi449.W449EffCarrier").expect("W449EffCarrier spec");
    let t = binding_named(&kb, spec, "T").expect("T binding");
    assert!(
        !matches!(extract_type(&kb, &t), TypeExtractor::Error),
        "`T = Modify[?]` must canonicalize to an extractable shape, got Error (backing term {:?})",
        kb.get_term(t)
    );
    assert_eq!(
        binding_base_sym(&kb, t),
        Some(modify),
        "`T = Modify[?]` must name Modify (backing term {:?})",
        kb.get_term(t)
    );
}

/// GAP 2: a NESTED positional parameterized binding `W449Inner[Int64]` PRESERVES its
/// inner arg (no longer flattened to `Ref(W449Inner)`), and the `fact` and `provides`
/// emissions produce a BYTE-IDENTICAL hash-consed binding — fact ≡ provides parity now
/// holds for parameterized bindings, not just the WI-391 bare-sort case.
#[test]
fn fact_nested_parameterized_binding_matches_provides() {
    let kb = crate::common::load_kb_with(W449_FIXTURE);
    let inner = kb
        .try_resolve_symbol("test.wi449.W449Inner")
        .expect("W449Inner sort");
    let int64 = kb
        .try_resolve_symbol("anthill.prelude.Int64")
        .expect("Int64 sort");

    let fact_spec = provides_spec_for(&kb, "test.wi449.W449FactCarrier").expect("fact spec");
    let prov_spec = provides_spec_for(&kb, "test.wi449.W449ProvCarrier").expect("provides spec");
    let fact_c = binding_named(&kb, fact_spec, "C").expect("fact C binding");
    let prov_c = binding_named(&kb, prov_spec, "C").expect("provides C binding");

    // The fact binding names W449Inner and PRESERVES its inner `E = Int64` arg (it is
    // no longer flattened to a bare `Ref(W449Inner)` that drops the argument).
    assert_eq!(
        binding_base_sym(&kb, fact_c),
        Some(inner),
        "fact `C` must name W449Inner (backing term {:?})",
        kb.get_term(fact_c)
    );
    let e = binding_named(&kb, fact_c, "E").expect("inner E binding preserved, not dropped");
    assert!(
        matches!(extract_type(&kb, &e), TypeExtractor::SortRef(s) if s == int64),
        "the nested `Int64` arg must survive, got {:?}",
        kb.get_term(e)
    );

    assert_eq!(
        fact_c, prov_c,
        "WI-449: the `fact` and `provides` nested-parameterized bindings must be the SAME \
         canonical hash-consed term (byte-identical SortProvidesInfo)"
    );
}
