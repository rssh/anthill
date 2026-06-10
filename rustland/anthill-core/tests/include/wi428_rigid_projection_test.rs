//! WI-428: `RigidTypeProjection` — the TYPE-receiver projection (`P.Key` /
//! `MemStore.Key`), the type-keyed sibling of the value-headed `ExprCarried`
//! (design `docs/design/path-dependent-types.md` §5.3).
//!
//! Formation is RIGID BY CONSTRUCTION, validated at the typer's elimination sites
//! (where the `requires` chain is complete regardless of source order):
//!
//!   - a MANIFEST subject (`MemStore.Key`, a concrete sort) δ-grounds via
//!     `project_type_member` and never survives as a stored type;
//!   - a member the bound application binds MANIFESTLY grounds THROUGH the bound
//!     (`requires Storage[C = P, Key = String]` ⟹ `P.Key = String`); the stored
//!     application is auto-completed, so an unwritten param's placeholder binding
//!     (`Key = Storage.Key`, var-keyed) does NOT count as manifest;
//!   - a bound-OPEN member off a rigid type param (`P.Key` under
//!     `requires Storage[C = P]`) stays a rigid NEUTRAL, compared by the ζ arm
//!     (same member + same declaring sort + same subject — a check, never a binding);
//!   - a member NO bound mentioning the subject declares is a LOUD error;
//!   - the spec sort itself as subject (`Storage.Key`) is the `T#K`
//!     carrier-conflation and is LOUDLY rejected.

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

/// The shared spec + carrier sorts: `Storage` declares a carrier param `C` plus the
/// members `Key` / `Val`; `MemStore` provides it with manifest bindings.
const STORAGE: &str = r#"
  sort Storage
    sort C = ?
    sort Key = ?
    sort Val = ?
    operation get(s: C, k: Key) -> Val
  end

  sort MemStore
    provides Storage[C = MemStore, Key = String, Val = Int64]
    entity memStore
    operation get(s: MemStore, k: String) -> Int64 = 0
  end
"#;

fn with_storage(ns: &str, rest: &str) -> String {
    format!(
        "namespace test.wi428.{ns}\n  import anthill.prelude.{{String, Int64}}\n{STORAGE}\n{rest}\nend\n"
    )
}

/// Within-operation path identity: `P.Key` in a param and the declared return are the
/// SAME rigid neutral (`requires Storage[C = P]` leaves `Key` bound-open), so `= k`
/// conforms via the ζ arm.
#[test]
fn rigid_param_within_op_identity() {
    let src = with_storage(
        "identity",
        r#"
  sort Wrapper
    sort P = ?
    requires Storage[C = P]
    entity wrapper(provider: P)
    operation getKey(w: Wrapper, k: P.Key) -> P.Key = k
  end
"#,
    );
    assert!(
        load_errors(&[&src]).is_empty(),
        "P.Key is the same rigid neutral in param and return positions",
    );
}

/// ζ soundness: distinct members off the same subject are DISTINCT neutrals — a body
/// returning `k : P.Key` under a declared `-> P.Val` is rejected.
#[test]
fn rigid_param_distinct_members_rejected() {
    let src = with_storage(
        "distinct_members",
        r#"
  sort Wrapper
    sort P = ?
    requires Storage[C = P]
    entity wrapper(provider: P)
    operation bad(w: Wrapper, k: P.Key) -> P.Val = k
  end
"#,
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("type mismatch")),
        "P.Key and P.Val are distinct rigid neutrals; got: {errs:?}",
    );
}

/// ζ soundness: the same member off DISTINCT subjects stays distinct — `P.Key` does
/// not conform to `Q.Key` (non-injectivity: never decomposed into `P =?= Q`). Also
/// exercises carrier-precise bound matching: each subject finds only the `requires`
/// entry MENTIONING it, with two same-spec bounds present.
#[test]
fn rigid_param_distinct_subjects_rejected() {
    let src = with_storage(
        "distinct_subjects",
        r#"
  sort Wrapper
    sort P = ?
    sort Q = ?
    requires Storage[C = P]
    requires Storage[C = Q]
    entity wrapper(a: P, b: Q)
    operation bad(w: Wrapper, k: P.Key) -> Q.Key = k
  end
"#,
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("type mismatch")),
        "P.Key and Q.Key are distinct rigid neutrals; got: {errs:?}",
    );
}

/// δ-through-the-bound: a MANIFEST binding in the `requires` application grounds the
/// projection at formation — `requires Storage[C = P, Key = String]` ⟹ `P.Key =
/// String`, so a body returning it conforms to `-> String`.
#[test]
fn delta_through_the_bound_grounds() {
    let src = with_storage(
        "delta_bound",
        r#"
  sort Wrapper
    sort P = ?
    requires Storage[C = P, Key = String]
    entity wrapper(provider: P)
    operation idK(w: Wrapper, k: P.Key) -> String = k
  end
"#,
    );
    assert!(
        load_errors(&[&src]).is_empty(),
        "P.Key δ-grounds to String through the bound's manifest binding",
    );
}

/// The δ-through-the-bound grounding is REAL: the grounded `P.Key` is `String`, so a
/// body returning it under a declared `-> Int64` is rejected with the concrete types.
#[test]
fn delta_through_the_bound_wrong_return_rejected() {
    let src = with_storage(
        "delta_bound_wrong",
        r#"
  sort Wrapper
    sort P = ?
    requires Storage[C = P, Key = String]
    entity wrapper(provider: P)
    operation idK(w: Wrapper, k: P.Key) -> Int64 = k
  end
"#,
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("Int64") && e.contains("String")),
        "grounded P.Key is String, rejected against -> Int64 with concrete types; got: {errs:?}",
    );
}

/// Formation rule 3: a member the bound's spec does not declare is a LOUD error,
/// never a silent neutral.
#[test]
fn undeclared_member_is_loud() {
    let src = with_storage(
        "undeclared",
        r#"
  sort Wrapper
    sort P = ?
    requires Storage[C = P]
    entity wrapper(provider: P)
    operation bad(w: Wrapper, k: P.Nope) -> P.Nope = k
  end
"#,
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("cannot project")),
        "P.Nope: no bound mentioning P declares 'Nope' — loud; got: {errs:?}",
    );
}

/// Formation: a subject with NO `requires` bound mentioning it cannot project at all.
#[test]
fn no_bound_mentioning_subject_is_loud() {
    let src = with_storage(
        "no_bound",
        r#"
  sort Plain
    sort Q = ?
    entity plain(x: Q)
    operation bad(p: Plain, k: Q.Key) -> Q.Key = k
  end
"#,
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("no `requires` bound")),
        "Q has no bound lending it members; got: {errs:?}",
    );
}

/// A MANIFEST concrete-sort subject δ-grounds through its `provides` binding:
/// `MemStore.Key = String` (the projection never survives as a stored type).
#[test]
fn concrete_sort_subject_manifest_grounds() {
    let src = with_storage(
        "concrete",
        "  operation probe(k: MemStore.Key) -> String = k\n",
    );
    assert!(
        load_errors(&[&src]).is_empty(),
        "MemStore provides Storage[Key = String] ⟹ MemStore.Key = String",
    );
}

/// The concrete grounding is REAL: `MemStore.Key` is `String`, rejected against
/// `-> Int64` with the concrete types (not an opaque head conforming to anything).
#[test]
fn concrete_sort_subject_wrong_return_rejected() {
    let src = with_storage(
        "concrete_wrong",
        "  operation probe(k: MemStore.Key) -> Int64 = k\n",
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("Int64") && e.contains("String")),
        "MemStore.Key is String; got: {errs:?}",
    );
}

/// The `T#K` guard: projecting off the BARE SPEC SORT itself (`Storage.Key` outside
/// the sort) would conflate distinct carriers — loudly rejected, never the old
/// warning + degenerate nominal.
#[test]
fn bare_spec_subject_rejected() {
    let src = with_storage(
        "bare_spec",
        "  operation probe(s: Storage, k: Storage.Key) -> Storage.Key = k\n",
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("conflate distinct carriers")),
        "Storage.Key off the bare spec is the T#K conflation — loud; got: {errs:?}",
    );
}

/// δ-through-the-bound for an OPAQUE NOMINAL binding (`Key = Token`, `sort Token = ?`
/// at namespace level): a user-written binding is manifest even when its target is an
/// opaque sort — only the auto-completed placeholder (the spec's OWN param) and a
/// sibling param of the declaring sort stay rigid (review-probe regression, WI-428).
#[test]
fn delta_through_bound_opaque_nominal_grounds() {
    let src = r#"
namespace test.wi428.token
  sort Token = ?
  sort Storage
    sort C = ?
    sort Key = ?
    operation get(s: C, k: Key) -> Key
  end
  sort Wrapper
    sort P = ?
    requires Storage[C = P, Key = Token]
    entity wrapper(provider: P)
    operation idK(w: Wrapper, k: P.Key) -> Token = k
  end
end
"#;
    assert!(
        load_errors(&[src]).is_empty(),
        "Key = Token is a user-written manifest binding ⟹ P.Key δ-grounds to Token",
    );
}

/// A binding to a SIBLING param of the declaring sort (`Key = K`) stays the rigid
/// NEUTRAL — cross-param δ needs the rigid-substitution coherence of the call/body
/// world (the recorded increment-B gap; over-rejection, never a wrong ground type).
#[test]
fn sibling_param_binding_stays_neutral() {
    let src = r#"
namespace test.wi428.sibling
  sort Storage
    sort C = ?
    sort Key = ?
    operation get(s: C, k: Key) -> Key
  end
  sort Wrapper
    sort P = ?
    sort K = ?
    requires Storage[C = P, Key = K]
    entity wrapper(provider: P, seed: K)
    operation idK(w: Wrapper, k: P.Key) -> K = k
  end
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("P.Key")),
        "cross-param δ is the increment-B gap: P.Key stays neutral (sound over-rejection); \
         got: {errs:?}",
    );
}

/// A NON-param child of a sort is a qualified CHILD reference, never hijacked into a
/// projection: `Outer.Inner` (a nested alias sort) resolves to the child symbol —
/// identical to the bare in-scope `Inner` (review-probe regression, WI-428).
#[test]
fn nested_child_sort_qualified_ref_resolves() {
    let src = r#"
namespace test.wi428.child
  import anthill.prelude.String
  sort Outer
    sort Inner = String
    entity outer
  end
  operation probeOp(x: Outer.Inner) -> Outer.Inner = x
end
"#;
    assert!(
        load_errors(&[src]).is_empty(),
        "Outer.Inner is a qualified child ref (Inner is not a `sort X = ?` param), \
         resolved like the bare name",
    );
}

/// A relatively-spelled qualified enum-entity reference in type position
/// (`TypeExtractor.SortRef` under an import) resolves as the child, never classified
/// as a projection (review-probe regression, WI-428).
#[test]
fn qualified_enum_entity_ref_preserved() {
    let src = r#"
namespace test.wi428.enumref
  import anthill.prelude.TypeExtractor
  operation probeOp(x: TypeExtractor.SortRef) -> TypeExtractor.SortRef = x
end
"#;
    assert!(
        load_errors(&[src]).is_empty(),
        "Enum.Entity relative qualified refs resolve via child lookup, not projection",
    );
}

/// INSIDE the declaring sort, `Storage.Key` is the qualified spelling of the bare
/// in-scope param `Key` (design §5.3 bare-spec rule) — identical to writing `Key`.
#[test]
fn self_qualified_member_inside_sort() {
    let src = format!(
        "namespace test.wi428.selfq\n  import anthill.prelude.{{String, Int64}}\n{}\nend\n",
        r#"
  sort Storage
    sort C = ?
    sort Key = ?
    sort Val = ?
    operation get(s: C, k: Key) -> Val
    operation idKey(s: C, k: Storage.Key) -> Key = k
  end
"#,
    );
    assert!(
        load_errors(&[&src]).is_empty(),
        "Storage.Key inside Storage ≡ bare Key",
    );
}
