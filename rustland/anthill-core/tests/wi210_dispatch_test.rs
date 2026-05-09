//! WI-210 — spec/impl call-site dispatch via fact.
//!
//! Phase 1: the loader auto-emits `SortProvidesInfo` for
//! `fact Spec[bindings]` clauses appearing inside a sort body, when
//! the named functor is itself a parameterized sort. This brings
//! `fact` in line with the existing `provides` clause path so the
//! existing proposal-030 / WI-119 specialization-witness machinery
//! (and WI-210's upcoming dispatch query) can find the impl.

mod common;

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver, LoadResult};
use anthill_core::kb::typing::lookup_spec_op_dispatch;
use anthill_core::parse;
use anthill_core::persistence::print::TermPrinter;

/// Phase 1/2 helper: discards errors. Used by tests that only inspect
/// post-load KB state (e.g. SortProvidesInfo emission) and don't
/// require the load to be error-free.
fn load_with(extra: &str) -> KnowledgeBase {
    load_capturing_errors(extra).0
}

/// Phase 3 helper: returns errors so dispatch-failure diagnostics
/// can be asserted directly. The WI-210 dispatch-failure marker
/// surfaces as a LoadError via load_phase_inner's all_errors.
fn load_capturing_errors(
    extra: &str,
) -> (KnowledgeBase, LoadResult, Vec<load::LoadError>) {
    let stdlib = common::stdlib_dir();
    let files = common::collect_anthill_files(&stdlib);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(r) => (kb, r, vec![]),
        Err(errs) => (kb, LoadResult::default(), errs),
    }
}

/// Render every `SortProvidesInfo` head the KB knows about, sorted.
fn provides_info_heads(kb: &mut KnowledgeBase) -> Vec<String> {
    let sym = kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo")
        .expect("SortProvidesInfo registered");
    let rids: Vec<_> = kb.by_functor(sym).into_iter().collect();
    let heads: Vec<_> = rids.iter().map(|&r| kb.rule_head(r)).collect();
    let printer = TermPrinter::new(kb);
    let mut out: Vec<String> = heads.into_iter()
        .map(|h| printer.print_term(h))
        .collect();
    out.sort();
    out
}

#[test]
fn fact_clause_inside_sort_body_emits_provides_info() {
    // Mirror of the `provides_clause_emits_specialization_proof_record`
    // test in specialization_witness_test.rs, but using the `fact`
    // sugar form. The kernel-language spec §1418 says `fact S[T]`
    // inside a sort body means spec satisfaction; this test pins
    // that the loader actually emits the SortProvidesInfo so
    // downstream consumers find it.
    let src = r#"
        namespace wi210.fact_emits
          export Wi210SpecA, Wi210ImplB
          sort Wi210SpecA
            sort State = ?
          end
          sort Wi210ImplB
            fact Wi210SpecA[State = Wi210ImplB]
          end
        end
    "#;
    let mut kb = load_with(src);
    let heads = provides_info_heads(&mut kb);
    let found = heads.iter().any(|h|
        h.contains("Wi210ImplB") && h.contains("Wi210SpecA")
    );
    assert!(found,
        "expected SortProvidesInfo for Wi210ImplB/Wi210SpecA; saw:\n{heads:#?}");
}

#[test]
fn fact_clause_outside_sort_does_not_emit_provides_info() {
    // Namespace-level facts must NOT emit SortProvidesInfo —
    // SortProvidesInfo's sort_ref must be a sort, not a namespace.
    // (The existing `provides_block` form for namespaces does
    // something different — it's the cross-language Implementation
    // path, not in-anthill spec satisfaction.)
    let src = r#"
        namespace wi210.fact_outside
          export Wi210OutSpec
          sort Wi210OutSpec
            sort State = ?
          end
          fact Wi210OutSpec[State = Wi210OutSpec]
        end
    "#;
    let mut kb = load_with(src);
    let heads = provides_info_heads(&mut kb);
    // Search for a SortProvidesInfo whose sort_ref is the namespace
    // wi210.fact_outside (not a sort) — this would be the unwanted
    // emission. The bare fact itself is fine; it's the auto-emit we
    // must avoid here.
    let bad = heads.iter().any(|h|
        h.contains("Wi210OutSpec") && h.contains("sort_ref: wi210")
    );
    assert!(!bad,
        "namespace-level fact must not emit SortProvidesInfo with the \
         namespace as sort_ref; saw:\n{heads:#?}");
}

#[test]
fn fact_for_non_spec_sort_does_not_emit_provides_info() {
    // `fact RegularSort(...)` where RegularSort has no type params
    // is asserting an instance of a constructor-shaped sort, not
    // claiming spec satisfaction. Must NOT emit SortProvidesInfo.
    let src = r#"
        namespace wi210.non_spec
          export Wi210Color, Wi210Holder
          sort Wi210Color
            entity wi210_red
            entity wi210_green
          end
          sort Wi210Holder
            fact Wi210Color[count = 0]
          end
        end
    "#;
    // Wi210Color has no `sort X = ?` decl, so the gate must skip
    // SortProvidesInfo emission regardless of whether the binding
    // shape is parametric-looking. Using a literal (`0`) for the
    // value keeps the fixture independent of cross-sort name
    // resolution.
    // Wi210Color has no `sort X = ?` decl, so even with bracket
    // notation this should not be treated as spec satisfaction.
    let mut kb = load_with(src);
    let heads = provides_info_heads(&mut kb);
    let found = heads.iter().any(|h|
        h.contains("Wi210Holder") && h.contains("Wi210Color")
    );
    assert!(!found,
        "fact for non-parametric sort must not emit SortProvidesInfo; saw:\n{heads:#?}");
}

// ─── Phase 2: spec-op detection helper ──────────────────────────

#[test]
fn lookup_spec_op_dispatch_recognizes_body_less_op_on_parametric_sort() {
    // WorkItemStore declares `commit` without a body; State is `?`;
    // this op is dispatch-eligible.
    let src = r#"
        namespace wi210p2.spec
          export Wi210Spec
          sort Wi210Spec
            sort State = ?
            operation wi210_op(s: State) -> State
          end
        end
    "#;
    let kb = load_with(src);
    let op_sym = kb.try_resolve_symbol("wi210p2.spec.Wi210Spec.wi210_op")
        .expect("op symbol registered");
    let parent = lookup_spec_op_dispatch(&kb, op_sym)
        .expect("body-less op on parametric sort should be a spec op");
    let parent_qn = kb.qualified_name_of(parent);
    assert_eq!(parent_qn, "wi210p2.spec.Wi210Spec",
        "spec-op's parent sort should be Wi210Spec; got {parent_qn}");
}

#[test]
fn lookup_spec_op_dispatch_rejects_op_with_body() {
    // Op has a body — even though the parent has type params, this
    // op is the impl, not the spec.
    let src = r#"
        namespace wi210p2.with_body
          export Wi210Impl
          sort Wi210Impl
            sort State = ?
            operation wi210_op(s: State) -> State = s
          end
        end
    "#;
    let kb = load_with(src);
    let op_sym = kb.try_resolve_symbol("wi210p2.with_body.Wi210Impl.wi210_op")
        .expect("op symbol registered");
    assert!(lookup_spec_op_dispatch(&kb, op_sym).is_none(),
        "op with body must not be a spec op (would dispatch to itself)");
}

#[test]
fn lookup_spec_op_dispatch_rejects_op_on_non_parametric_sort() {
    // Sort has no `sort X = ?` declaration; this op is just a
    // free-standing operation, not a spec op.
    let src = r#"
        namespace wi210p2.no_params
          export Wi210Plain
          sort Wi210Plain
            entity wi210_e
            operation wi210_op(x: Wi210Plain) -> Wi210Plain
          end
        end
    "#;
    let kb = load_with(src);
    let op_sym = kb.try_resolve_symbol("wi210p2.no_params.Wi210Plain.wi210_op")
        .expect("op symbol registered");
    assert!(lookup_spec_op_dispatch(&kb, op_sym).is_none(),
        "op on non-parametric sort must not be a spec op");
}

// ─── Phase 3: dispatch hook in check_apply ──────────────────────

/// Returns the diagnostic error strings (from env.diagnostics) tagged
/// with "WI-210 dispatch failed" — the marker we push when Phase 3
/// finds zero or multiple matching impls.
fn dispatch_diagnostics(errors: &[anthill_core::kb::load::LoadError]) -> Vec<String> {
    errors.iter()
        .map(|e| format!("{e:?}"))
        .filter(|s| s.contains("WI-210 dispatch failed"))
        .collect()
}

#[test]
fn dispatch_succeeds_when_unique_impl_matches() {
    // A spec with one type param + one body-less op, an impl that
    // pins State, and a caller that invokes Spec.op. Phase 3 should
    // find a unique impl via SortProvidesInfo and succeed.
    let src = r#"
        namespace wi210p3.unique
          export Wi210Spec3, Wi210Impl3, Wi210Caller3
          sort Wi210Spec3
            sort State = ?
            operation spec_op(s: State) -> State
          end
          sort Wi210Impl3
            entity wi210_i3
            fact Wi210Spec3[State = Wi210Impl3]
            operation spec_op(s: Wi210Impl3) -> Wi210Impl3 = s
          end
          sort Wi210Caller3
            entity wi210_c3
            operation use_spec(x: Wi210Impl3) -> Wi210Impl3 =
              Wi210Spec3.spec_op(x)
          end
        end
    "#;
    let (_kb, _result, errors) = load_capturing_errors(src);
    let diag = dispatch_diagnostics(&errors);
    assert!(diag.is_empty(),
        "expected no WI-210 dispatch errors; got:\n{diag:#?}\n\
         all errors: {errors:#?}");
}

#[test]
fn dispatch_legacy_when_no_provides_records_exist() {
    // Spec exists with no `provides`/`fact Spec[…]` declarations
    // anywhere. WI-210 is opt-in per spec: `NoCandidates` is a
    // no-op so legacy stdlib specs (Numeric, Map, …) keep working.
    let src = r#"
        namespace wi210p3.no_impl
          export Wi210Spec4, Wi210Caller4
          sort Wi210Spec4
            sort State = ?
            operation spec_op(s: State) -> State
          end
          sort Wi210Caller4
            entity wi210_c4
            operation use_spec(x: Wi210Caller4) -> Wi210Caller4 =
              Wi210Spec4.spec_op(x)
          end
        end
    "#;
    let (_kb, _result, errors) = load_capturing_errors(src);
    let diag = dispatch_diagnostics(&errors);
    assert!(diag.is_empty(),
        "spec with zero SortProvidesInfo records must not trigger \
         WI-210 dispatch failure (opt-in per spec); got: {diag:#?}");
}

#[test]
fn dispatch_fails_when_provides_exist_but_none_match_bindings() {
    // Spec has an impl for one binding (Wi210Carrier4a) but the
    // caller invokes with a different type (Wi210Carrier4b). With
    // the opt-in trigger satisfied (≥1 SortProvidesInfo for the
    // spec) and zero matching candidates, dispatch fails.
    let src = r#"
        namespace wi210p3.bind_mismatch
          export Wi210Spec4, Wi210Carrier4a, Wi210Carrier4b, Wi210Impl4a, Wi210Caller4
          sort Wi210Spec4
            sort State = ?
            operation spec_op(s: State) -> State
          end
          sort Wi210Carrier4a
            entity wi210_carrier4a
          end
          sort Wi210Carrier4b
            entity wi210_carrier4b
          end
          sort Wi210Impl4a
            entity wi210_i4a
            fact Wi210Spec4[State = Wi210Carrier4a]
            operation spec_op(s: Wi210Carrier4a) -> Wi210Carrier4a = s
          end
          sort Wi210Caller4
            entity wi210_c4
            operation use_spec(x: Wi210Carrier4b) -> Wi210Carrier4b =
              Wi210Spec4.spec_op(x)
          end
        end
    "#;
    let (_kb, _result, errors) = load_capturing_errors(src);
    let diag = dispatch_diagnostics(&errors);
    assert!(!diag.is_empty(),
        "expected dispatch failure for binding mismatch; got: {errors:#?}");
    assert!(diag.iter().any(|d| d.contains("Wi210Spec4")),
        "expected diagnostic to mention Wi210Spec4; got:\n{diag:#?}");
}

#[test]
fn dispatch_fails_when_two_impls_share_binding() {
    // Two impls both claim `Spec5[State = Carrier5]` — the call's
    // bindings would match both, so coherence rule (C) rejects.
    let src = r#"
        namespace wi210p3.ambig
          export Wi210Spec5, Wi210Carrier5, Wi210ImplA5, Wi210ImplB5, Wi210Caller5
          sort Wi210Spec5
            sort State = ?
            operation spec_op(s: State) -> State
          end
          sort Wi210Carrier5
            entity wi210_carrier5
          end
          sort Wi210ImplA5
            entity wi210_ia5
            fact Wi210Spec5[State = Wi210Carrier5]
            operation spec_op(s: Wi210Carrier5) -> Wi210Carrier5 = s
          end
          sort Wi210ImplB5
            entity wi210_ib5
            fact Wi210Spec5[State = Wi210Carrier5]
            operation spec_op(s: Wi210Carrier5) -> Wi210Carrier5 = s
          end
          sort Wi210Caller5
            entity wi210_c5
            operation use_spec(x: Wi210Carrier5) -> Wi210Carrier5 =
              Wi210Spec5.spec_op(x)
          end
        end
    "#;
    let (_kb, _result, errors) = load_capturing_errors(src);
    let diag = dispatch_diagnostics(&errors);
    assert!(!diag.is_empty(),
        "expected dispatch failure for two-matching-impls case; got: {errors:#?}");
}

#[test]
fn store_anthill_emits_provides_info_for_workitemstore() {
    // End-to-end: anthill-todo's actual store.anthill writes
    // `fact WorkItemStore[State = WIS]` inside `sort
    // FileBasedWorkitemStore`. After WI-210 phase 1, this should
    // produce a SortProvidesInfo record.
    use std::path::PathBuf;

    let workspace = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .ancestors().nth(2).unwrap().to_path_buf();
    let store_path = workspace.join("anthill-todo/store.anthill");
    let store_src = std::fs::read_to_string(&store_path)
        .expect("read anthill-todo/store.anthill");

    let mut kb = load_with(&store_src);
    let heads = provides_info_heads(&mut kb);
    let found = heads.iter().any(|h|
        h.contains("FileBasedWorkitemStore") && h.contains("WorkItemStore")
    );
    assert!(found,
        "expected SortProvidesInfo recording FileBasedWorkitemStore as \
         WorkItemStore impl; saw:\n{heads:#?}");
}
