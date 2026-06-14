//! WI-402 (existential half): `ensures Spec[C]` — the output dual of `requires`
//! (docs/design/path-dependent-types.md §5, "`ensures Spec[C]` — the output dual of
//! `requires`").
//!
//! An operation `-> C ensures Spec[C, bindings]` introduces `C` as an op-discharged
//! EXISTENTIAL carrier: the body witnesses it with a concrete provider, the caller
//! sees the spec with the carrier abstract, and at eval the dictionary flows OUT with
//! the concrete value (dispatch on its runtime sort). The loader rewrites the return
//! type to the ensures spec with the carrier dropped — the BOUND case (`ensures
//! Spec[C, K = String]`) reduces to the delivered manifest-return half (so the members
//! are concrete); the UNBOUND case (`ensures Spec[C]`) is a bare-Spec return admitted
//! by the ensures-aware WI-401 gate (the `ensures` is the "made so by an ensures
//! manifest" admit-form §5 names — without it a bare/partial upcast still escapes).
//!
//! NB the dispatch surface is the DOTTED / receiver form (`store.describe()` /
//! `Spec.op(store, …)`); a direct `describe(store)` call to a body-less spec op does
//! not resolve regardless of the existential (a pre-existing spec-op-call limitation),
//! so these fixtures use the dotted form the design's worked example uses.

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

/// The KVStore factory of design §5: two divergent backends, each providing the spec at
/// the same bindings, joined by an `if` under an `ensures Spec[C]` existential return.
const FACTORY: &str = r#"
  import anthill.prelude.{String, Bool}
  sort KVStore
    sort K = ?
    sort V = ?
    operation describe(s: KVStore) -> String
  end
  sort MemStore
    provides KVStore[K = String, V = String]
    entity memStore
    operation describe(s: MemStore) -> String = "mem"
  end
  sort DiskStore
    provides KVStore[K = String, V = String]
    entity diskStore(path: String)
    operation describe(s: DiskStore) -> String = "disk"
  end
"#;

/// BOUND existential (`ensures Spec[C, K = String, V = String]`): the two-backend factory
/// type-checks — the branch-join has no LUB (Mem vs Disk), and the ensures spec is the
/// upper bound it unifies on; the body's manifest provider conformance is the delivered
/// bound half.
#[test]
fn bound_existential_factory_admitted() {
    let src = format!(
        "namespace test.wi402x.bound\n{FACTORY}\n  operation openStore(persistent: Bool) -> C ensures KVStore[C, K = String, V = String] =\n    if persistent then diskStore(\"/d\") else memStore\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(errs.is_empty(), "bound existential factory must type-check, got: {errs:?}");
}

/// Binding-precise: a member the body's providers contradict (`K = Int64` vs the provided
/// `K = String`) stays a loud mismatch — the rewritten return IS the ensures spec, so its
/// bindings are checked against the body.
#[test]
fn bound_existential_wrong_binding_rejected() {
    let src = format!(
        "namespace test.wi402x.wrong\n  import anthill.prelude.{{String, Int64, Bool}}\n  sort KVStore\n    sort K = ?\n    sort V = ?\n  end\n  sort MemStore\n    provides KVStore[K = String, V = String]\n    entity memStore\n  end\n  operation openStore(p: Bool) -> C ensures KVStore[C, K = Int64, V = String] = memStore\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("type mismatch")),
        "a K = Int64 ensures against a K = String provider must be rejected, got: {errs:?}"
    );
}

/// UNBOUND existential (`ensures Spec[C]`, members abstract): a bare-Spec return is
/// ADMITTED because the `ensures` vouches for it (the interface-rooted existential of §5).
#[test]
fn unbound_existential_return_admitted() {
    let src = r#"
namespace test.wi402x.unbound
  import anthill.prelude.String
  sort KVStore
    sort K = ?
    sort V = ?
  end
  sort MemStore
    provides KVStore[K = String, V = String]
    entity memStore
  end
  operation openOne(m: MemStore) -> C ensures KVStore[C] = m
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "unbound `ensures Spec[C]` return must be admitted, got: {errs:?}");
}

/// The `ensures` is LOAD-BEARING: the SAME bare-Spec return WITHOUT an `ensures` clause is
/// still the WI-401 abstracting (sealing) return — rejected so the base model stays
/// escape-free. (Contrast `unbound_existential_return_admitted`, which only adds `ensures`.)
#[test]
fn bare_return_without_ensures_still_rejected() {
    let src = r#"
namespace test.wi402x.noensures
  import anthill.prelude.String
  sort KVStore
    sort K = ?
    sort V = ?
  end
  sort MemStore
    provides KVStore[K = String, V = String]
    entity memStore
  end
  operation openOne(m: MemStore) -> KVStore = m
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("abstracting return") || e.contains("escape")),
        "a bare-spec return WITHOUT an `ensures` must stay rejected (WI-401), got: {errs:?}"
    );
}

/// A CONCRETE return carrying an `ensures` postcondition (`-> MemStore ensures
/// KVStore[MemStore, …]`) is NOT an existential — the return name resolves to a real sort,
/// so the detection leaves it alone (no rewrite). Regression guard for the detector.
#[test]
fn concrete_return_with_ensures_not_rewritten() {
    let src = r#"
namespace test.wi402x.concrete
  import anthill.prelude.String
  sort KVStore
    sort K = ?
    sort V = ?
  end
  sort MemStore
    provides KVStore[K = String, V = String]
    entity memStore
  end
  operation openMem(m: MemStore) -> MemStore ensures KVStore[MemStore, K = String, V = String] = m
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "concrete return + ensures postcondition must still load, got: {errs:?}");
}

/// REGRESSION (review finding): the ensures-aware gate skip must be SCOPED to ops the
/// loader actually existential-rewrote — NOT any op whose `ensures` names the bare return
/// sort. A bare REAL-sort return (`-> DataProvider`, the WI-401 sealing escape) carrying an
/// `ensures DataProvider[K = String]` is NOT rewritten (the written type is a concrete sort),
/// so its abstract member would still escape — it must stay rejected.
#[test]
fn bare_real_sort_return_with_ensures_still_rejected() {
    let src = r#"
namespace test.wi402x.seal
  import anthill.prelude.String
  sort DataProvider
    sort K = ?
  end
  sort SubscriberStore
    provides DataProvider[K = String]
    entity subscriberStore
  end
  operation seal(s: SubscriberStore) -> DataProvider ensures DataProvider[K = String] = s
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("abstracting return") || e.contains("escape")),
        "a bare real-sort return is not existential-rewritten; its `ensures` must NOT admit \
         the sealing escape, got: {errs:?}"
    );
}

/// REGRESSION (review finding): stripping the carrier must drop ONLY the carrier SLOT (the
/// first positional), never a named member binding whose VALUE is the carrier (`V = C`, a
/// member typed as the result itself). The rewritten return must still carry `V = C` — proven
/// here by the diagnostic naming it (`expected Spec[K = String, V = C]`); were `V` dropped as
/// if it were the carrier, the diagnostic would read `Spec[K = String]` (a silently partial
/// manifest). NB the carrier-valued-member FORM itself — unifying the abstract carrier `C`
/// with a provider's concrete `V` — is a separate, not-yet-supported conformance gap (so this
/// op does not fully type-check); the test pins only that the member is not silently stripped.
#[test]
fn carrier_valued_member_binding_is_kept() {
    let src = r#"
namespace test.wi402x.selfval
  import anthill.prelude.String
  sort Spec
    sort K = ?
    sort V = ?
  end
  sort Node
    provides Spec[K = String, V = Node]
    entity node
  end
  operation make(n: Node) -> C ensures Spec[C, K = String, V = C] = n
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("V = C")),
        "the `V = C` member must be KEPT in the rewritten return (not stripped as the carrier \
         slot) — the diagnostic must name it, got: {errs:?}"
    );
}

/// CALLER: the existential result is usable through the spec interface — `store.describe()`
/// on an `openStore(…) : KVStore` (abstract carrier) resolves against `KVStore.describe`.
#[test]
fn existential_result_dotted_dispatch_typechecks() {
    let src = format!(
        "namespace test.wi402x.caller\n{FACTORY}\n  operation openStore(persistent: Bool) -> C ensures KVStore[C, K = String, V = String] =\n    if persistent then diskStore(\"/d\") else memStore\n  operation client(p: Bool) -> String =\n    let store = openStore(p)\n    store.describe()\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(errs.is_empty(), "dotted dispatch on an existential result must type-check, got: {errs:?}");
}

/// EVAL — the DICT FLOWS OUT: `openStore` returns a concrete `memStore`/`diskStore`
/// carrying its real sort; `store.describe()` dispatches on that RUNTIME sort (never on
/// the abstract static return type). `clientDisk` ⟹ "disk", `clientMem` ⟹ "mem" proves
/// the right backend's impl ran — the eval dual of `req_insertion`'s dict-in.
#[test]
fn existential_dict_flows_out_at_eval() {
    let src = format!(
        "namespace test.wi402x.eval\n{FACTORY}\n  operation openStore(persistent: Bool) -> C ensures KVStore[C, K = String, V = String] =\n    if persistent then diskStore(\"/d\") else memStore\n  operation clientDisk() -> String = openStore(true).describe()\n  operation clientMem() -> String = openStore(false).describe()\nend\n"
    );
    let mut interp = crate::common::interp_for(&src);
    match interp.call("test.wi402x.eval.clientDisk", &[]) {
        Ok(anthill_core::eval::Value::Str(s)) => assert_eq!(
            s, "disk",
            "openStore(true) returns diskStore; describe must dispatch on its runtime sort"
        ),
        other => panic!("clientDisk should eval to \"disk\" via dict-out dispatch; got {other:?}"),
    }
    match interp.call("test.wi402x.eval.clientMem", &[]) {
        Ok(anthill_core::eval::Value::Str(s)) => assert_eq!(
            s, "mem",
            "openStore(false) returns memStore; describe must dispatch on its runtime sort"
        ),
        other => panic!("clientMem should eval to \"mem\" via dict-out dispatch; got {other:?}"),
    }
}
