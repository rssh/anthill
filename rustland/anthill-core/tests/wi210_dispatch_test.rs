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
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;
use anthill_core::persistence::print::TermPrinter;

fn load_with(extra: &str) -> KnowledgeBase {
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
    let _ = load::load_all(&mut kb, &refs, &NullResolver);
    kb
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
            fact Wi210Color[bound = wi210_red]
          end
        end
    "#;
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
