//! WI-457 — close the WI-401 escape-gate gap for JOIN bodies. The §5 strict base
//! model is escape-free: a return that provides an abstract spec only by UPCASTING
//! a concrete carrier (leaving the spec's member unbound, no `ensures` vouching)
//! is rejected (`abstracting_return_error`). The direct form
//! `-> KVStore = memStore` was caught, but the JOIN form
//! `-> KVStore = if persistent then diskStore else memStore` slipped through: the
//! branch-join widens the divergent concrete providers up to the bare spec, so the
//! joined `body_ty == ret_sort` and the gate's `same_symbol(body_sort, ret_sort)`
//! short-circuit returned no error. WI-457 re-applies the gate to each branch LEAF.
//!
//! Must NOT reject (verified below): a fully-manifest-spec join, a same-sort
//! (input-rooted) join. The `ensures`-vouched join is covered by the unchanged
//! existential marker (wi402_existential_return_test stays green).

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

// The §5 KVStore factory fixture: a parametric spec `KVStore[K, V]` and two
// divergent concrete backends, each providing it at the same bindings.
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
"#;

fn is_escape(errs: &[String]) -> bool {
    errs.iter().any(|e| e.contains("abstracting return") || e.contains("escape"))
}

/// THE GAP: a bare-spec return whose body is an `if` joining two divergent concrete
/// providers must now be rejected — the abstract member `KVStore.K`/`.V` would
/// escape via the join with no `ensures` vouching for it.
#[test]
fn if_join_provider_upcast_to_bare_spec_rejected() {
    let src = format!(
        "namespace test.wi457.ifjoin\n{PRELUDE}\n  operation openStore(persistent: Bool) -> KVStore =\n    if persistent then diskStore(\"/tmp/kv\") else memStore\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        is_escape(&errs),
        "a bare-spec `if`-join of divergent providers must be flagged as an abstracting return, got: {errs:?}",
    );
}

/// Same escape via a `match` join — exercises the match leaf-collection path.
#[test]
fn match_join_provider_upcast_to_bare_spec_rejected() {
    let src = format!(
        "namespace test.wi457.matchjoin\n{PRELUDE}\n  sort Backend\n    entity useDisk\n    entity useMem\n  end\n  operation openStore(b: Backend) -> KVStore =\n    match b\n      case useDisk -> diskStore(\"/tmp/kv\")\n      case useMem -> memStore\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        is_escape(&errs),
        "a bare-spec `match`-join of divergent providers must be flagged as an abstracting return, got: {errs:?}",
    );
}

/// MUST NOT REJECT — a fully-manifest return binds every spec member, so nothing
/// abstract escapes (this is the §5 worked example, mirrored from wi402).
#[test]
fn manifest_join_accepted() {
    let src = format!(
        "namespace test.wi457.manifest\n{PRELUDE}\n  operation openStore(persistent: Bool) -> KVStore[K = String, V = String] =\n    if persistent then diskStore(\"/tmp/kv\") else memStore\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(errs.is_empty(), "a fully-manifest join must typecheck, got: {errs:?}");
}

/// MUST NOT REJECT — a same-sort join: both branches are input-rooted `KVStore`
/// values (params), so the return's abstractness is the inputs', not a hidden
/// local. `abstracting_return_error` short-circuits on `same_symbol` per leaf.
#[test]
fn same_sort_input_rooted_join_accepted() {
    let src = format!(
        "namespace test.wi457.samesort\n{PRELUDE}\n  operation pick(a: KVStore, b: KVStore, persistent: Bool) -> KVStore =\n    if persistent then a else b\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "a same-sort (input-rooted) join must NOT be rejected as an escape, got: {errs:?}",
    );
}

/// REGRESSION — the DIRECT provider upcast `-> KVStore = memStore` stays rejected
/// (the WI-401 case the join form was bypassing).
#[test]
fn direct_provider_upcast_still_rejected() {
    let src = format!(
        "namespace test.wi457.direct\n{PRELUDE}\n  operation openStore(s: MemStore) -> KVStore = s\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        is_escape(&errs),
        "the direct provider upcast must still be rejected, got: {errs:?}",
    );
}

/// MUST NOT REJECT — a nested `if` whose leaves are all input-rooted is fine; the
/// recursion must reach the true leaves, not stop at the outer `if`.
#[test]
fn nested_same_sort_join_accepted() {
    let src = format!(
        "namespace test.wi457.nested\n{PRELUDE}\n  operation pick3(a: KVStore, b: KVStore, c: KVStore, p: Bool, q: Bool) -> KVStore =\n    if p then a else if q then b else c\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "a nested same-sort join must NOT be rejected, got: {errs:?}",
    );
}

/// A NESTED join hiding a provider upcast in an inner branch is still caught — the
/// leaf recursion descends into the inner `if`.
#[test]
fn nested_join_inner_provider_upcast_rejected() {
    let src = format!(
        "namespace test.wi457.nestedbad\n{PRELUDE}\n  operation openStore(a: KVStore, p: Bool, q: Bool) -> KVStore =\n    if p then a else if q then diskStore(\"/tmp/kv\") else memStore\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        is_escape(&errs),
        "a provider upcast in an inner branch must still be flagged, got: {errs:?}",
    );
}

/// WI-468: a LET-binding ANNOTATION launders a provider upcast past the gate —
/// `let s : KVStore = memStore ; s` widens `s` to the bare spec, so the returned
/// tail leaf carries `KVStore` (== ret_sort) and slips `same_symbol`. This is NOT
/// the WI-457 join vector (it leaks with no `if`/`match` at all — see the body
/// here). The fix sees through the returned let-bound `s` to its VALUE node
/// (`memStore`, stamped its own `MemStore`), re-applying the gate to that.
#[test]
fn let_value_annotation_laundering_escape() {
    let src = format!(
        "namespace test.wi457.launder\n{PRELUDE}\n  operation openStore(m: MemStore) -> KVStore =\n    let s: KVStore = m\n    s\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        is_escape(&errs),
        "a let-annotation-laundered provider upcast must be flagged (WI-468), got: {errs:?}",
    );
}

/// WI-468: a join bound to a `let` VALUE and returned through the variable launders
/// the same way (`let s : KVStore = if … ; s`). The see-through pushes the value
/// node (the `if`) back onto the walk, so its concrete branch leaves are gated.
#[test]
fn let_value_join_laundering_escape() {
    let src = format!(
        "namespace test.wi457.launderjoin\n{PRELUDE}\n  operation openStore(persistent: Bool) -> KVStore =\n    let s: KVStore = if persistent then diskStore(\"/tmp/kv\") else memStore\n    s\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        is_escape(&errs),
        "a let-value JOIN laundered through a returned variable must be flagged (WI-468), got: {errs:?}",
    );
}

/// WI-468: the see-through chains through multiple let hops — `let a = m ; let s =
/// a ; s` resolves `s` → `a` → `m` (`MemStore`), still an escape.
#[test]
fn let_value_chained_alias_laundering_escape() {
    let src = format!(
        "namespace test.wi457.launderchain\n{PRELUDE}\n  operation openStore(m: MemStore) -> KVStore =\n    let a: KVStore = m\n    let s: KVStore = a\n    s\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        is_escape(&errs),
        "a chained let-alias laundering must be flagged through the multi-hop see-through (WI-468), got: {errs:?}",
    );
}

/// WI-468 must-NOT-reject: a let-bound provider NOT in return position is fine —
/// the body returns something else, so the variable is never a tail leaf and the
/// see-through never reaches its value. (`s` is bound but unused in the return.)
#[test]
fn let_value_not_returned_not_flagged() {
    let src = format!(
        "namespace test.wi457.notret\n{PRELUDE}\n  operation openStore(m: MemStore) -> Bool =\n    let s: KVStore = m\n    true\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "a let-bound provider that is NOT returned must not be flagged (WI-468), got: {errs:?}",
    );
}

/// WI-468 must-NOT-reject: a same-sort (input-rooted) let — `f(k: KVStore) -> KVStore
/// = let s: KVStore = k ; s` — sees through `s` to `k` (`KVStore`), which
/// short-circuits on `same_symbol`. No hidden local escapes (the abstractness is the
/// input's, interface-rooted).
#[test]
fn let_value_same_sort_input_rooted_not_flagged() {
    let src = format!(
        "namespace test.wi457.sameinput\n{PRELUDE}\n  operation openStore(k: KVStore) -> KVStore =\n    let s: KVStore = k\n    s\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "a same-sort input-rooted let-return must not be flagged (WI-468), got: {errs:?}",
    );
}

/// WI-468 must-NOT-reject: a MANIFEST return through a laundering let — the
/// annotation and return bind every member (`KVStore[K = String, V = String]`), so
/// the seen-through value's gate finds no unbound member and admits it.
#[test]
fn let_value_manifest_return_not_flagged() {
    let src = format!(
        "namespace test.wi457.manifest\n{PRELUDE}\n  operation openStore(m: MemStore) -> KVStore[K = String, V = String] =\n    let s: KVStore[K = String, V = String] = m\n    s\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "a manifest-spec return (all members bound) through a let must not be flagged (WI-468), got: {errs:?}",
    );
}
