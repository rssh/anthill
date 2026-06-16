//! WI-488 — close the WI-401 escape gate on the PRODUCER side for TUPLE /
//! named_tuple component returns (sibling of WI-457/468/480, which closed the
//! CONSUMER side).
//!
//! `abstracting_return_error` keyed on `sort_functor_of_view`, which is `None`
//! for a tuple / named_tuple carrier — so a tuple return whose COMPONENT is a
//! bare-spec provider upcast was never inspected:
//!   `operation mkBare(m: MemStore) -> (KVStore, Bool) = (m, true)`
//! loaded clean (verified by the WI-480 probes). Each abstracting tuple
//! component is the §5 avoidance problem exactly as a bare top-level return is —
//! `KVStore.K`/`.V` would escape with no `ensures` rooting them.
//!
//! The fix recurses `abstracting_return_error` into the tuple components
//! PAIRWISE (body component vs return component), re-applying the UNCHANGED
//! bare-vs-manifest-vs-ensures gate per component. Its `same_symbol` short-circuit
//! spares an input-rooted / equal component, and its `unbound` check spares a
//! manifest one, so the per-component reuse honours the "must NOT reject" cases
//! without restating them.
//!
//! Scope note (verified by `parameterized_nominal_abstracting_return_rejected`):
//! tuple components are the only gap. A NOMINAL parameterized return abstracting a
//! type-arg (`-> BoxT[T = KVStore]` from a body `BoxT[T = MemStore]`) is rejected
//! even earlier, as an INVARIANT-param type MISMATCH, so it never reaches this
//! gate — tuple components are covariant, nominal type-args are not.

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

// The §5 KVStore factory fixture (mirrors wi480): a parametric spec `KVStore[K, V]`,
// a concrete backend `MemStore` that provides it, and a parameterized `BoxT[T]`.
const PRELUDE: &str = r#"
  import anthill.prelude.{String, Bool}
  sort KVStore
    sort K = ?
    sort V = ?
  end
  sort MemStore
    provides KVStore[K = String, V = String]
    entity memStore
  end
  sort BoxT
    sort T = ?
    entity boxedT(item: T)
  end
"#;

fn is_escape(errs: &[String]) -> bool {
    errs.iter().any(|e| e.contains("abstracting return") || e.contains("escape"))
}

/// THE GAP: a producer whose tuple COMPONENT abstracts a concrete provider up to
/// the bare spec — `mkBare(m: MemStore) -> (KVStore, Bool) = (m, true)`. Must be
/// flagged at the producer: `KVStore.K`/`.V` escape with no `ensures`.
#[test]
fn tuple_component_abstracting_producer_flagged() {
    let src = format!(
        "namespace test.wi488.tuple\n{PRELUDE}\n  operation mkBare(m: MemStore) -> (KVStore, Bool) = (m, true)\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        is_escape(&errs),
        "a tuple-component abstracting producer must be flagged (WI-488), got: {errs:?}",
    );
}

/// THE GAP (nested): the abstracting component is itself nested inside another
/// tuple — `((KVStore, Bool), Bool)` from `((m, true), true)`. The recursion
/// descends both levels and flags the inner `MemStore -> KVStore` upcast.
#[test]
fn nested_tuple_component_abstracting_producer_flagged() {
    let src = format!(
        "namespace test.wi488.nested\n{PRELUDE}\n  operation mkBare(m: MemStore) -> ((KVStore, Bool), Bool) = ((m, true), true)\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        is_escape(&errs),
        "a NESTED tuple-component abstracting producer must be flagged (WI-488), got: {errs:?}",
    );
}

/// MUST NOT REJECT — a CONCRETE tuple component: `mkConcrete -> (MemStore, Bool)`.
/// The component's sort matches its declared type (`same_symbol`), nothing abstract
/// escapes.
#[test]
fn tuple_component_concrete_producer_not_flagged() {
    let src = format!(
        "namespace test.wi488.concrete\n{PRELUDE}\n  operation mkConcrete(m: MemStore) -> (MemStore, Bool) = (m, true)\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "a concrete tuple-component producer must NOT be flagged (WI-488), got: {errs:?}",
    );
}

/// MUST NOT REJECT — an INPUT-ROOTED bare tuple component:
/// `mkBareOk(k: KVStore) -> (KVStore, Bool) = (k, true)`. The bare component's
/// abstractness is the input `k`'s (interface-rooted), not a hidden local — the
/// per-component gate short-circuits on `same_symbol` (`KVStore == KVStore`).
#[test]
fn tuple_component_input_rooted_producer_not_flagged() {
    let src = format!(
        "namespace test.wi488.inputrooted\n{PRELUDE}\n  operation mkBareOk(k: KVStore) -> (KVStore, Bool) = (k, true)\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "an input-rooted bare tuple-component producer must NOT be flagged (WI-488), got: {errs:?}",
    );
}

/// MUST NOT REJECT — a MANIFEST tuple component:
/// `-> (KVStore[K = String, V = String], Bool)`. Every member of the component spec
/// is bound, so the per-component gate finds no unbound member and admits it.
#[test]
fn tuple_component_manifest_producer_not_flagged() {
    let src = format!(
        "namespace test.wi488.manifest\n{PRELUDE}\n  operation mkManifest(m: MemStore) -> (KVStore[K = String, V = String], Bool) = (m, true)\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "a manifest tuple-component producer must NOT be flagged (WI-488), got: {errs:?}",
    );
}

/// SCOPE / FINDING — a NOMINAL parameterized return abstracting a type-arg
/// (`-> BoxT[T = KVStore]` from a body `BoxT[T = MemStore]`) is NOT a WI-488 escape:
/// nominal type-args are INVARIANT, so the body `BoxT[T = MemStore]` does not conform
/// to `BoxT[T = KVStore]` and is rejected as a TYPE MISMATCH — strictly earlier than,
/// and never reaching, the abstracting-return gate. (Tuple components are covariant,
/// which is why they alone slipped.) This guards that the case stays rejected.
#[test]
fn parameterized_nominal_abstracting_return_rejected() {
    let src = format!(
        "namespace test.wi488.paramnominal\n{PRELUDE}\n  operation mkBox(m: MemStore) -> BoxT[T = KVStore] = boxedT(m)\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        !errs.is_empty() && errs.iter().any(|e| e.contains("mismatch")) && !is_escape(&errs),
        "a nominal parameterized type-arg abstraction must stay rejected as a type MISMATCH, \
         NOT reach the abstracting-return gate (WI-488 finding); got: {errs:?}",
    );
}

/// THE GAP (named tuple, REORDERED fields): the abstracting component is a NAMED
/// tuple field whose position differs between body and return —
/// `(a: m, b: true)` returned as `-> (b: Bool, a: KVStore)`. Conformance aligns by
/// NAME (`a`<:`a` is the MemStore→KVStore upcast, `b`<:`b` ok), so the body
/// conforms; the gate must align by name too — a raw positional zip would pair
/// `a:MemStore` with `b:Bool` and MISS the escape on `a`.
#[test]
fn named_tuple_reordered_component_abstracting_producer_flagged() {
    let src = format!(
        "namespace test.wi488.reordered\n{PRELUDE}\n  operation mkBare(m: MemStore) -> (b: Bool, a: KVStore) = (a: m, b: true)\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        is_escape(&errs),
        "a REORDERED named-tuple-component abstracting producer must be flagged via name alignment (WI-488), got: {errs:?}",
    );
}
