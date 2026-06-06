//! WI-407 — the loader emits `SortProvidesInfo` for NON-PARAMETRIC spec
//! `fact <Spec>` declarations, so a declared is-a hierarchy built from
//! non-parametric specs is visible to subtyping.
//!
//! The Store hierarchy is entirely non-parametric:
//!   `sort QueryableStore { fact Store }`  / `sort BulkStore { fact Store }`
//!   `fact BulkStore[IndexedFileStore]` / `fact QueryableStore[IndexedFileStore]`
//! Pre-WI-407, `maybe_emit_fact_provides_info` early-returned on
//! `spec_params.is_empty()`, so NONE of these became provider edges and
//! `IndexedFileStore <: Store` was invisible (the gap WI-385's arg/field
//! validation surfaced — see WI-385). WI-407 emits the edges and the transitive
//! `sort_provides` (user decision "transitive everywhere") chains them.
//!
//! These are checked through RETURN-type conformance (`check_operation_bodies`),
//! which is enforced regardless of WI-385's not-yet-landed argument validation:
//! `operation f(x: A) -> B = x` loads clean iff `A <: B`.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn load_errors(extras: &[&str]) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    for ex in extras {
        parsed.push(parse::parse(ex).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// 1-hop, sort-body form: `sort QueryableStore { fact Store }` ⟹
/// `QueryableStore <: Store`.
#[test]
fn queryable_store_widens_to_store() {
    let src = r#"
namespace test.wi407.q_widen
  import anthill.persistence.{Store, QueryableStore}
  operation widen(q: QueryableStore) -> Store = q
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "QueryableStore is-a Store via `fact Store`; returning it as Store must conform: {errs:?}",
    );
}

/// 1-hop, top-level form: `fact BulkStore[IndexedFileStore]` ⟹
/// `IndexedFileStore <: BulkStore` (carrier = the leading positional).
#[test]
fn indexed_file_store_widens_to_bulk_store() {
    let src = r#"
namespace test.wi407.ifs_bulk
  import anthill.persistence.{BulkStore}
  import anthill.persistence.filesystem.{IndexedFileStore}
  operation widen(ifs: IndexedFileStore) -> BulkStore = ifs
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "IndexedFileStore is-a BulkStore via `fact BulkStore[IndexedFileStore]`: {errs:?}",
    );
}

/// 2-hop, the headline case: `IndexedFileStore → BulkStore/QueryableStore →
/// Store`. Recognized only because BOTH the top-level and sort-body
/// non-parametric edges are emitted AND `sort_provides` is transitive.
#[test]
fn indexed_file_store_widens_to_store_transitively() {
    let src = r#"
namespace test.wi407.ifs_store
  import anthill.persistence.{Store}
  import anthill.persistence.filesystem.{IndexedFileStore}
  operation widen(ifs: IndexedFileStore) -> Store = ifs
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "IndexedFileStore <: Store via the 2-hop provider chain: {errs:?}",
    );
}

/// The relation is NOT vacuous: a value that genuinely does not provide `Store`
/// is still rejected by return conformance, so WI-407 widened the relation
/// exactly along the declared `provides` edges and nowhere else.
#[test]
fn unrelated_sort_return_still_rejected() {
    let src = r#"
namespace test.wi407.bad
  import anthill.persistence.{Store}
  import anthill.prelude.{String}
  operation bad(s: String) -> Store = s
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "String does not provide Store; returning it as Store must be rejected",
    );
}

/// A `fact <DataSort>[X]` is a DATA fact, NOT an is-a edge — even when the data
/// sort is declared AFTER the fact (forward reference). The spec-vs-data gate
/// (`sort_has_constructors`) must read load-order-independent scan-time symbol
/// info, not the incrementally-built `entity_parent` index: otherwise `FwdColor`
/// (whose `entity` children are not registered until its body loads, AFTER the
/// fact) is misclassified as a spec and a bogus `FwdHolder provides FwdColor`
/// edge lets the unrelated `FwdHolder` widen to `FwdColor`.
#[test]
fn data_sort_fact_does_not_widen_forward_ref() {
    let src = r#"
namespace test.wi407.fwd
  sort FwdHolder
    entity fwd_h
  end
  fact FwdColor[FwdHolder]
  sort FwdColor
    entity fwd_red
    entity fwd_green
  end
  operation widen(h: FwdHolder) -> FwdColor = h
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("FwdColor")),
        "FwdColor is a data sort (entity fwd_red/green), so `fact FwdColor[FwdHolder]` is a data \
         fact, not is-a; FwdHolder must NOT widen to FwdColor even though FwdColor is declared \
         after the fact. errs: {errs:?}",
    );
}

/// Same as above with the data sort declared BEFORE the fact — the classification
/// is identical (no edge), proving the result is independent of source order.
#[test]
fn data_sort_fact_does_not_widen_safe_order() {
    let src = r#"
namespace test.wi407.safe
  sort SafeColor
    entity safe_red
    entity safe_green
  end
  sort SafeHolder
    entity safe_h
  end
  fact SafeColor[SafeHolder]
  operation widen(h: SafeHolder) -> SafeColor = h
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("SafeColor")),
        "SafeColor is a data sort, so `fact SafeColor[SafeHolder]` is a data fact, not is-a; \
         SafeHolder must NOT widen to SafeColor. errs: {errs:?}",
    );
}
