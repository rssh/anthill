//! WI-402 (bound/manifest half): binding-precise provider admissibility
//! (docs/design/path-dependent-types.md §5, "ensures Spec[C]" — the BOUND regime).
//! A value of a concrete carrier sort conforms to a PARAMETERIZED spec type the
//! carrier provides, iff every binding the expected type carries matches the
//! carrier's provider fact (`SubscriberStore provides DataProvider[K = String]`
//! ⟹ `-> DataProvider[K = String] = s` typechecks; `-> DataProvider[K = Int64]`
//! stays rejected). Pre-WI-402 even the matching form was rejected: provider
//! admissibility was confined to the bare↔bare arm of `types_compatible`, so the
//! manifest return of the §5 worked example was unwritable. The UNBOUND regime
//! (`ensures Spec[C]`, the interface-rooted existential) remains WI-402's open
//! scope — not covered here.

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

const PRELUDE: &str = r#"
  import anthill.prelude.{String, Int64}
  sort DataProvider
    sort K = ?
  end
  sort SubscriberStore
    provides DataProvider[K = String]
    entity subscriberStore
  end
  sort Plain
    entity plain
  end
"#;

/// The §5 manifest return: the carrier provides the spec WITH the expected binding,
/// so nothing abstract escapes (the WI-401 gate's "full manifest" admit-form) and the
/// conformance check must accept the provider upcast.
#[test]
fn manifest_provider_return_accepted() {
    let src = format!(
        "namespace test.wi402.ret\n{PRELUDE}\n  operation open(s: SubscriberStore) -> DataProvider[K = String] = s\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(errs.is_empty(), "manifest provider return must typecheck, got: {errs:?}");
}

/// Same, returning a freshly constructed entity value (provision read through the
/// entity's parent sort, not a param's declared type).
#[test]
fn manifest_provider_entity_return_accepted() {
    let src = format!(
        "namespace test.wi402.ent\n{PRELUDE}\n  operation open() -> DataProvider[K = String] = subscriberStore\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(errs.is_empty(), "entity-literal provider return must typecheck, got: {errs:?}");
}

/// Binding-precise means binding-CHECKED: a manifest the provider contradicts stays
/// loudly rejected (`K = Int` vs the provided `K = String`).
#[test]
fn manifest_provider_wrong_binding_rejected() {
    let src = format!(
        "namespace test.wi402.wrong\n{PRELUDE}\n  operation open(s: SubscriberStore) -> DataProvider[K = Int64] = s\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("type mismatch")),
        "K = Int64 manifest from a K = String provider must be rejected, got: {errs:?}"
    );
}

/// A sort with NO provision for the spec must stay rejected — the new accept is
/// gated on the provider fact, not on the spec being parameterized.
#[test]
fn non_provider_stays_rejected() {
    let src = format!(
        "namespace test.wi402.nonprov\n{PRELUDE}\n  operation open(p: Plain) -> DataProvider[K = String] = p\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("type mismatch")),
        "a non-providing carrier must not conform to the spec, got: {errs:?}"
    );
}

/// The requires-input dual (§5: requires evidences abstract INPUTS): a providing
/// carrier is accepted where a parameterized spec PARAM is declared.
#[test]
fn manifest_provider_arg_accepted() {
    let src = format!(
        "namespace test.wi402.arg\n{PRELUDE}\n  operation use(p: DataProvider[K = String]) -> Int64 = 1\n  operation call(s: SubscriberStore) -> Int64 = use(s)\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(errs.is_empty(), "provider arg vs manifest spec param must typecheck, got: {errs:?}");
}

/// Arg-position twin of the wrong-binding rejection.
#[test]
fn manifest_provider_arg_wrong_binding_rejected() {
    let src = format!(
        "namespace test.wi402.argwrong\n{PRELUDE}\n  operation use(p: DataProvider[K = Int64]) -> Int64 = 1\n  operation call(s: SubscriberStore) -> Int64 = use(s)\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("type mismatch")),
        "K = Int64 param given a K = String provider must be rejected, got: {errs:?}"
    );
}

/// The §5 worked example (KVStore factory), fully bound: two DIFFERENT concrete
/// backends, each providing the spec at the same bindings, joined by an `if` under
/// the manifest return type.
#[test]
fn kvstore_factory_fully_bound_accepted() {
    let src = r#"
namespace test.wi402.factory
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
  operation openStore(persistent: Bool) -> KVStore[K = String, V = String] =
    if persistent then diskStore("/tmp/kv") else memStore
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "fully-bound two-backend factory must typecheck, got: {errs:?}");
}

/// ACCEPTANCE ANCHOR (WI-391-gated): a provider binding to a STRUCTURED value
/// (`K = List[T = Int64]`) should conform when the expected binding matches
/// structurally. Today it false-rejects: the provides fact stores the NESTED plain
/// sort name (`Int64`) as a nullary `Fn{S}`, which `type_head` classifies as `Error`
/// — the §5.3 extractability-criterion violation whose global lowering decision is
/// WI-391. Un-ignore when WI-391 lowers fact-binding values to extractable shapes.
#[test]
#[ignore = "WI-391: nested provider-binding leaves ride the nullary-Fn shape; lowering decision pending"]
fn structured_provider_binding_accepted() {
    let src = r#"
namespace test.wi402.structok
  import anthill.prelude.{Int64, List}
  sort DataProvider
    sort K = ?
  end
  sort BatchStore
    provides DataProvider[K = List[T = Int64]]
    entity batchStore
  end
  operation open(b: BatchStore) -> DataProvider[K = List[T = Int64]] = b
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "structured provider binding must typecheck, got: {errs:?}");
}

/// Structured-binding twin of the wrong-binding rejection.
#[test]
fn structured_provider_binding_mismatch_rejected() {
    let src = r#"
namespace test.wi402.structwrong
  import anthill.prelude.{Int64, String, List}
  sort DataProvider
    sort K = ?
  end
  sort BatchStore
    provides DataProvider[K = List[T = Int64]]
    entity batchStore
  end
  operation open(b: BatchStore) -> DataProvider[K = List[T = String]] = b
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("type mismatch")),
        "structurally different provider binding must be rejected, got: {errs:?}"
    );
}

/// A PARTIAL manifest still escapes (§5: "a partial ensures still escapes") — the
/// WI-401 abstracting-return gate keeps firing for the member the manifest leaves
/// unbound, even now that the conformance check itself accepts matching bindings.
#[test]
fn partial_manifest_return_stays_rejected() {
    let src = r#"
namespace test.wi402.partial
  import anthill.prelude.String
  sort KVStore
    sort K = ?
    sort V = ?
  end
  sort MemStore
    provides KVStore[K = String, V = String]
    entity memStore
  end
  operation openStore(m: MemStore) -> KVStore[K = String] = m
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("abstracting return") || e.contains("escape")),
        "partial manifest must still be flagged as an abstracting return, got: {errs:?}"
    );
}
