//! WI-407 — the loader emits `SortProvidesInfo` for NON-PARAMETRIC spec
//! `fact <Spec>` declarations, so a declared is-a hierarchy built from
//! non-parametric specs is visible to subtyping.
//!
//! The Store hierarchy is entirely non-parametric:
//!   `sort QueryableStore { fact Store }`  / `sort BulkStore { fact Store }`
//!   `fact QueryableStore[IndexedFileStore]`
//! Pre-WI-407, `maybe_emit_fact_provides_info` early-returned on
//! `spec_params.is_empty()`, so NONE of these became provider edges and
//! `IndexedFileStore <: Store` was invisible (the gap WI-385's arg/field
//! validation surfaced — see WI-385). WI-407 emits the edges and the transitive
//! `sort_provides` (user decision "transitive everywhere") chains them.
//!
//! These are checked through RETURN-type conformance (`check_operation_bodies`),
//! which is enforced regardless of WI-385's not-yet-landed argument validation:
//! `operation f(x: A) -> B = x` loads clean iff `A <: B`.
//!
//! WI-931 moved the carrier-side half of the fixture. `fact
//! QueryableStore[IndexedFileStore]` now lives in the RUST host closure
//! (`rustland/anthill-stl/anthill/persistence.anthill`), because a satisfaction
//! fact may only stand where the spec's operations are backed and
//! `anthill.persistence`'s are host primitives — so this file loads the host
//! bindings too. The `BulkStore` leg is gone entirely: neither file backend
//! provides it while `pull` has no anthill-callable implementation (WI-932), so
//! the 1-hop case is now spelled on `QueryableStore`, which is the same edge
//! shape (a top-level `fact <Spec>[X]` over a non-parametric spec).

/// Stdlib + host bindings + `extras`, returning the load errors. The local copy of
/// this sequence was kept only because it loaded the stdlib ALONE; once WI-931
/// moved the fixture into the host closure it became `try_load_kb_with_files`
/// exactly, so it calls that.
fn load_errors(extras: &[&str]) -> Vec<String> {
    crate::common::try_load_kb_with_files(extras).err().unwrap_or_default()
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

/// 1-hop, top-level form: `fact QueryableStore[IndexedFileStore]` ⟹
/// `IndexedFileStore <: QueryableStore` (carrier = the leading positional).
#[test]
fn indexed_file_store_widens_to_queryable_store() {
    let src = r#"
namespace test.wi407.ifs_queryable
  import anthill.persistence.{QueryableStore}
  import anthill.persistence.filesystem.{IndexedFileStore}
  operation widen(ifs: IndexedFileStore) -> QueryableStore = ifs
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "IndexedFileStore is-a QueryableStore via `fact QueryableStore[IndexedFileStore]`: {errs:?}",
    );
}

/// 2-hop, the headline case: `IndexedFileStore → QueryableStore → Store`.
/// Recognized only because BOTH the top-level and sort-body non-parametric
/// edges are emitted AND `sort_provides` is transitive.
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
