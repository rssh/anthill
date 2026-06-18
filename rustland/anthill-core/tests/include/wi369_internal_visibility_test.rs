//! WI-369: enforce `internal` visibility (kernel-language.md §8.6). An
//! `internal` constructor / sort / operation is "hidden from outside the
//! declaring scope" — it resolves within its own scope (and lexical
//! descendants) but a cross-scope reference is a load-blocking
//! `ForbiddenInternalAccess`. Previously `internal` was parsed but decorative.

/// A sort with an `internal` carrier constructor `mk`, plus a PUBLIC operation
/// `make` that constructs it from within the same scope (must stay clean).
const BOX_SRC: &str = r#"
sort test.wi369.box.Box
  import anthill.prelude.Int64
  internal entity mk(v: Int64)
  operation make(x: Int64) -> Box
  =
    mk(v: x)
end
"#;

/// Cross-scope consumer that only uses the PUBLIC operation — must load clean.
const GOOD_SRC: &str = r#"
namespace test.wi369.good
  import anthill.prelude.Int64
  import test.wi369.box.Box
  operation use_make(x: Int64) -> Box
  =
    Box.make(x: x)
end
"#;

/// Cross-scope consumer that reaches past the public API and constructs the
/// `internal` carrier directly (qualified) — must be a load error naming `mk`.
const BAD_QUALIFIED_SRC: &str = r#"
namespace test.wi369.bad
  import anthill.prelude.Int64
  import test.wi369.box.Box
  operation sneak(x: Int64) -> Box
  =
    Box.mk(v: x)
end
"#;

/// Cross-scope BARE construction reached through `requires` (the variant is
/// exposed by the sort, but `internal` hides it) — must error naming `mk`.
const BAD_REQUIRES_SRC: &str = r#"
sort test.wi369.badreq.Q
  import anthill.prelude.Int64
  requires test.wi369.box.Box
  operation sneak2(x: Int64) -> Box
  =
    mk(v: x)
end
"#;

/// Cross-scope SELECTIVE IMPORT of the internal constructor — must error at the
/// import naming `mk`.
const BAD_IMPORT_SRC: &str = r#"
namespace test.wi369.badimp
  import anthill.prelude.Int64
  import test.wi369.box.Box.{mk}
  operation sneak3(x: Int64) -> Box
  =
    mk(v: x)
end
"#;

/// Cross-scope PROJECTION of a field whose owning entity is internal
/// (`b.v` where `v` belongs to the internal `mk`) — must error naming `v`.
const BAD_PROJECTION_SRC: &str = r#"
sort test.wi369.badproj.Peeker
  import anthill.prelude.Int64
  import test.wi369.box.Box
  operation peek(b: Box) -> Int64
  =
    b.v
end
"#;

/// A Box with an internal `mk` AND a PUBLIC sibling entity `pubmk` and a nested
/// `Child` sort. Used by the selectivity control and the transitive-leak guard.
const BOX2_SRC: &str = r#"
sort test.wi369.box2.Box
  import anthill.prelude.Int64
  internal entity mk(v: Int64)
  entity pubmk(v: Int64)
  sort Child
    import anthill.prelude.Int64
    entity leaf(n: Int64)
  end
end
"#;

/// Control: a PUBLIC sibling entity in the same sort as an internal one is
/// still constructible cross-scope — `internal` is selective, not all-or-nothing.
const PUBLIC_SIBLING_SRC: &str = r#"
namespace test.wi369.pubuser
  import anthill.prelude.Int64
  import test.wi369.box2.Box
  operation build(x: Int64) -> Box
  =
    Box.pubmk(v: x)
end
"#;

/// Regression (reviewer-found leak 1): an internal name reached TRANSITIVELY —
/// through a non-enclosing parent (`requires Box.Child`) whose own enclosing
/// parent is `Box` — must still be hidden. A per-hop `locals` filter missed
/// this; the post-resolution visibility gate catches it.
const TRANSITIVE_LEAK_SRC: &str = r#"
sort test.wi369.box2.Sneaker
  import anthill.prelude.Int64
  import test.wi369.box2.Box
  requires test.wi369.box2.Box.Child
  operation sneak_t(x: Int64) -> Box
  =
    mk(v: x)
end
"#;

/// Regression (reviewer-found leak 2): an internal name legitimately imported
/// into a DESCENDANT, then RE-EXPORTED to a consumer that reaches the descendant
/// as a non-enclosing parent, must still be hidden. The per-hop filter inspected
/// only `locals` (not `imports`); the post-resolution gate catches it.
const REEXPORT_BOX_SRC: &str = r#"
sort test.wi369.reexp.Box
  import anthill.prelude.Int64
  internal entity mk(v: Int64)
  namespace inner
    import test.wi369.reexp.Box.mk
  end
end
"#;
const REEXPORT_CONSUMER_SRC: &str = r#"
namespace test.wi369.reexp.consumer
  import anthill.prelude.Int64
  import test.wi369.reexp.Box
  import test.wi369.reexp.Box.inner.*
  operation sneak_re(x: Int64) -> Box
  =
    mk(v: x)
end
"#;

fn errors_of(sources: &[&str]) -> Vec<String> {
    match crate::common::try_load_kb_with_files(sources) {
        Ok(_) => Vec::new(),
        Err(errs) => errs,
    }
}

/// Same-scope construction (`make` building `mk` inside `Box`) and cross-scope
/// use of the public operation both load clean — `internal` does not restrict
/// the declaring scope or the public surface.
#[test]
fn same_scope_and_public_api_use_is_clean() {
    crate::common::try_load_kb_with_files(&[BOX_SRC, GOOD_SRC]).unwrap_or_else(|errs| {
        panic!("same-scope construction + public-API cross-scope use must load; got: {errs:?}")
    });
}

/// Cross-scope QUALIFIED construction of the internal constructor errors at
/// load, and the diagnostic names the offending symbol.
#[test]
fn cross_scope_qualified_construction_of_internal_errors() {
    let errs = errors_of(&[BOX_SRC, BAD_QUALIFIED_SRC]);
    assert!(
        errs.iter().any(|e| e.contains("internal") && e.contains("mk")),
        "constructing the internal `mk` from another scope must error naming it; got: {errs:?}",
    );
}

/// Cross-scope BARE construction reached via `requires` (variant exposure) is
/// hidden by `internal` — must error naming `mk`.
#[test]
fn cross_scope_bare_construction_via_requires_errors() {
    let errs = errors_of(&[BOX_SRC, BAD_REQUIRES_SRC]);
    assert!(
        errs.iter().any(|e| e.contains("internal") && e.contains("mk")),
        "bare `mk` reached through `requires` must be hidden by internal; got: {errs:?}",
    );
}

/// Selectively importing the internal constructor into another scope is a
/// forbidden cross-scope reference — must error naming `mk`.
#[test]
fn cross_scope_selective_import_of_internal_errors() {
    let errs = errors_of(&[BOX_SRC, BAD_IMPORT_SRC]);
    assert!(
        errs.iter().any(|e| e.contains("internal") && e.contains("mk")),
        "selective import of internal `mk` must be forbidden; got: {errs:?}",
    );
}

/// Cross-scope PROJECTION of a field on an internal entity (`b.v`) is forbidden
/// — reading the field would alias encapsulated state. Must error naming `v`.
#[test]
fn cross_scope_field_projection_of_internal_errors() {
    let errs = errors_of(&[BOX_SRC, BAD_PROJECTION_SRC]);
    assert!(
        errs.iter().any(|e| e.contains("internal") && e.contains("v")),
        "projecting a field of the internal `mk` from another scope must error; got: {errs:?}",
    );
}

/// Selectivity control: a PUBLIC sibling entity in the same sort as an internal
/// one is still constructible cross-scope — `internal` hides only what is marked.
#[test]
fn public_sibling_entity_is_visible_cross_scope() {
    crate::common::try_load_kb_with_files(&[BOX2_SRC, PUBLIC_SIBLING_SRC])
        .unwrap_or_else(|errs| panic!("a public sibling of an internal entity must stay usable; got: {errs:?}"));
}

/// Regression: an internal name reached TRANSITIVELY through a non-enclosing
/// parent's enclosing grandparent must be hidden (reviewer-found leak 1).
#[test]
fn cross_scope_transitive_internal_via_requires_errors() {
    let errs = errors_of(&[BOX2_SRC, TRANSITIVE_LEAK_SRC]);
    assert!(
        errs.iter().any(|e| e.contains("internal") && e.contains("mk")),
        "transitively-reached internal `mk` must be hidden; got: {errs:?}",
    );
}

/// Regression: an internal name imported into a descendant and RE-EXPORTED via
/// a wildcard import must be hidden at the re-importing scope (reviewer-found
/// leak 2 — the per-hop filter missed `imports`).
#[test]
fn cross_scope_reexport_of_internal_errors() {
    let errs = errors_of(&[REEXPORT_BOX_SRC, REEXPORT_CONSUMER_SRC]);
    assert!(
        errs.iter().any(|e| e.contains("internal") && e.contains("mk")),
        "re-exported internal `mk` must stay hidden at the consumer; got: {errs:?}",
    );
}
