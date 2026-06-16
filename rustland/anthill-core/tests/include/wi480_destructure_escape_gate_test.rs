//! WI-480 — close the WI-401 escape-gate gap for DESTRUCTURING-pattern `let`
//! bindings (sibling of WI-468's single-`Pattern::Var` laundering).
//!
//! WI-468 sees through a returned `let s = … ; s` to the binding's VALUE node, but
//! `let_bound_var_name` returned `None` for any non-`Pattern::Var` binder, so a
//! destructured name was never tracked in the `LeafScope`. A returned component var
//! then fell back to its laundered annotation-component type and slipped
//! `same_symbol`. The vectors false-accepted before this ticket — each laundering a
//! provider upcast that happens AT the let:
//!   * tuple-literal      `let (s, _): (KVStore, Bool) = (m, true) ; s`
//!   * constructor-literal `let boxed(s): Box = boxed(m) ; s`
//!   * opaque + annotation `let (s, _): (KVStore, Bool) = mkConcrete(m) ; s`
//!       (mkConcrete `-> (MemStore, Bool)` — the annotation widens the concrete
//!        component, exactly like the direct `-> KVStore = m` form)
//!
//! The fix: a destructuring binder records each destructured name → a PROJECTION
//! (the binding VALUE node + a selector path). The leaf walk threads the path: a
//! literal tuple / constructor is projected STRUCTURALLY (down to the concrete
//! element node, chased as WI-468), an opaque value (a call) or an input param is
//! projected at the TYPE level — and in every case the UNCHANGED
//! `abstracting_return_error` is re-applied to the seen-through component type. Its
//! `same_symbol` short-circuit is exactly the line between a laundered concrete
//! upcast (flagged) and an interface-rooted abstract (spared).
//!
//! Consistent-model decision (user, 2026-06-16): the BARE interface-propagation case
//! `let (s, _) = mkBareOk(k) ; s` (the producer exposes a bare-spec tuple component
//! through its OWN signature) is NOT flagged — the component roots in the producer's
//! declared interface, so the consumer adds no hidden abstraction. The PRODUCER's own
//! tuple-component escape is a separate, producer-side concern, gated since WI-488
//! (a producer abstracting a CONCRETE component up to a bare spec, like
//! `mkBare(m: MemStore) -> (KVStore, Bool)`, is now flagged at the producer); the
//! interface-propagation producer used here is unflagged because its bare component
//! is INPUT-ROOTED.
//!
//! Must NOT reject (verified below): a destructured value NOT in return position, a
//! same-sort / input-rooted destructure, a manifest destructure, and the bare
//! interface-propagation case above.

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

// The §5 KVStore factory fixture (mirrors wi457): a parametric spec `KVStore[K, V]`,
// two divergent concrete backends, a `Box` entity wrapping a `KVStore` field, and an
// opaque `mkpair` returning a `(KVStore, Bool)` tuple.
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
  sort DiskStore
    provides KVStore[K = String, V = String]
    entity diskStore(path: String)
  end
  sort Box
    entity boxed(item: KVStore)
  end
  operation mkConcrete(m: MemStore) -> (MemStore, Bool) = (m, true)
"#;

fn is_escape(errs: &[String]) -> bool {
    errs.iter().any(|e| e.contains("abstracting return") || e.contains("escape"))
}

/// THE GAP (tuple-literal value): `let (s, _): (KVStore, Bool) = (m, true) ; s` —
/// the destructured `s` is upcast to the bare spec via the annotation component, then
/// returned. Must be flagged: `KVStore.K`/`.V` would escape with no `ensures`.
#[test]
fn tuple_literal_destructure_laundering_escape() {
    let src = format!(
        "namespace test.wi480.tuplelit\n{PRELUDE}\n  operation openStore(m: MemStore) -> KVStore =\n    let (s, _): (KVStore, Bool) = (m, true)\n    s\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        is_escape(&errs),
        "a tuple-literal destructure laundering a provider upcast must be flagged (WI-480), got: {errs:?}",
    );
}

/// THE GAP (constructor-literal value): `let boxed(s): Box = boxed(m) ; s` — the
/// destructured field var `s` carries the field's bare-spec type. Must be flagged.
#[test]
fn constructor_literal_destructure_laundering_escape() {
    let src = format!(
        "namespace test.wi480.ctorlit\n{PRELUDE}\n  operation openStore(m: MemStore) -> KVStore =\n    let boxed(s): Box = boxed(m)\n    s\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        is_escape(&errs),
        "a constructor-literal destructure laundering a provider upcast must be flagged (WI-480), got: {errs:?}",
    );
}

/// THE GAP (opaque value + annotation): `let (s, _): (KVStore, Bool) = mkConcrete(m) ; s`
/// — the value is a CALL with a CONCRETE component (`mkConcrete -> (MemStore, Bool)`),
/// no literal element node to see through; the annotation `(KVStore, Bool)` widens
/// the concrete component to the bare spec at the let. Must be flagged: the launder
/// happens here, exactly like the direct `-> KVStore = m` form. Seen through at the
/// TYPE level (the value's component type `MemStore`), the gate fires.
#[test]
fn opaque_concrete_annotation_destructure_laundering_escape() {
    let src = format!(
        "namespace test.wi480.opaque\n{PRELUDE}\n  operation openStore(m: MemStore) -> KVStore =\n    let (s, _): (KVStore, Bool) = mkConcrete(m)\n    s\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        is_escape(&errs),
        "an opaque-value destructure whose annotation launders a concrete component must be flagged (WI-480), got: {errs:?}",
    );
}

/// MUST NOT REJECT — the BARE interface-propagation case:
/// `let (s, _) = mkBareOk(k) ; s` where `mkBareOk -> (KVStore, Bool)` exposes a
/// bare-spec component through its OWN signature (no annotation laundering at the
/// let). The abstract `KVStore` roots in mkBareOk's declared interface, so the
/// consumer adds no hidden abstraction — seen through at the TYPE level the component
/// is the bare `KVStore == ret_sort`, which `same_symbol` spares. mkBareOk itself is
/// unflagged because its bare component is INPUT-ROOTED (WI-488 flags only a producer
/// abstracting a CONCRETE component up to a bare spec — see the producer-side test).
#[test]
fn opaque_bare_interface_propagation_not_flagged() {
    let src = format!(
        "namespace test.wi480.barexx\n{PRELUDE}\n  operation mkBareOk(k: KVStore) -> (KVStore, Bool) = (k, true)\n  operation openStore(k: KVStore) -> KVStore =\n    let (s, _) = mkBareOk(k)\n    s\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "a bare interface-propagation destructure must NOT be flagged (consistent with the input-rooted producer; WI-480/WI-488), got: {errs:?}",
    );
}

/// THE GAP (nested launder): a let-laundered var placed as a TUPLE ELEMENT, then
/// destructured and returned — `let x: KVStore = m ; let (s,_): (KVStore, Bool) = (x, true) ; s`.
/// A TYPE projection of `(x, true)` reads `x`'s LAUNDERED stamped type (`KVStore ==
/// ret_sort`) and would miss it; the fix projects the tuple-literal STRUCTURALLY to
/// the element node `x`, then chases `x` → its value `m` (`MemStore`) → flagged.
#[test]
fn laundered_var_in_tuple_element_escape() {
    let src = format!(
        "namespace test.wi480.nested\n{PRELUDE}\n  operation openStore(m: MemStore) -> KVStore =\n    let x: KVStore = m\n    let (s, _): (KVStore, Bool) = (x, true)\n    s\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        is_escape(&errs),
        "a laundered var nested in a tuple element must be flagged via structural see-through (WI-480), got: {errs:?}",
    );
}

/// MUST NOT REJECT — a destructured value NOT in return position. The body returns
/// something else, so `s` is never a tail leaf.
#[test]
fn destructure_not_returned_not_flagged() {
    let src = format!(
        "namespace test.wi480.notret\n{PRELUDE}\n  operation openStore(m: MemStore) -> Bool =\n    let (s, _): (KVStore, Bool) = (m, true)\n    true\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "a destructured provider that is NOT returned must not be flagged (WI-480), got: {errs:?}",
    );
}

/// MUST NOT REJECT — a same-sort / input-rooted destructure: the tuple comes from a
/// parameter, so the returned component's abstractness is the input's (interface
/// rooted), not a hidden local. `s` sees through to the input tuple element.
#[test]
fn same_sort_input_rooted_destructure_not_flagged() {
    let src = format!(
        "namespace test.wi480.sameinput\n{PRELUDE}\n  operation openStore(a: KVStore, b: Bool) -> KVStore =\n    let (s, _): (KVStore, Bool) = (a, b)\n    s\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "a same-sort input-rooted destructure must not be flagged (WI-480), got: {errs:?}",
    );
}

/// MUST NOT REJECT — an OPAQUE input-rooted destructure: the tuple is a parameter
/// `p: (KVStore, Bool)` (no literal element, no annotation widening). Seen through at
/// the TYPE level the component is the bare `KVStore == ret_sort`, input-rooted, so
/// `same_symbol` spares it (the abstractness is the caller's).
#[test]
fn opaque_input_param_destructure_not_flagged() {
    let src = format!(
        "namespace test.wi480.inparam\n{PRELUDE}\n  operation openStore(p: (KVStore, Bool)) -> KVStore =\n    let (s, _) = p\n    s\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "an opaque input-rooted destructure must not be flagged (WI-480), got: {errs:?}",
    );
}

/// MUST NOT REJECT — a MANIFEST return through a destructuring let: the annotation
/// and return bind every member, so the seen-through value's gate finds no unbound
/// member and admits it.
#[test]
fn manifest_destructure_return_not_flagged() {
    let src = format!(
        "namespace test.wi480.manifest\n{PRELUDE}\n  operation openStore(m: MemStore) -> KVStore[K = String, V = String] =\n    let (s, _): (KVStore[K = String, V = String], Bool) = (m, true)\n    s\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "a manifest-spec return through a destructure must not be flagged (WI-480), got: {errs:?}",
    );
}
