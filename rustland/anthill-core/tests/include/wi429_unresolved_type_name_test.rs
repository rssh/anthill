//! WI-429: an unresolvable Capitalized dotted name in TYPE position is a LOUD
//! load error — never the old advisory `UnresolvedName` warning + a degenerate
//! nominal sort literally named `"Storage.Key"` (which false-rejected valid
//! programs and conflated distinct positions into one meaningless global
//! nominal). Two layers:
//!
//!   1. `remap_name`'s NotFound arm upgrades a dotted Capitalized-member name
//!      in type position to the load-blocking `UnresolvedTypeName` (a typo'd
//!      head / a 3-segment non-name falls through every classifier).
//!   2. An end-of-load sweep (`validate_rigid_projection_formations`) runs the
//!      eliminator's formation validation on every STORED
//!      `RigidTypeProjection`, so a malformed projection in a position the
//!      typer never eliminates (an entity FIELD type) fails the load too —
//!      previously it sat silent (WI-428 review feedback).

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

/// The shared spec + carrier (mirrors the WI-428 fixture): `Storage` declares
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
        "namespace test.wi429.{ns}\n  import anthill.prelude.{{String, Int64}}\n{STORAGE}\n{rest}\nend\n"
    )
}

/// A typo'd HEAD (`MemStoer.Key`) resolves as nothing — neither a value
/// projection, nor a type-receiver projection, nor a qualified ref — and must
/// be a hard load error, not a warning + a nominal sort named "MemStoer.Key".
#[test]
fn typo_head_in_type_position_is_hard_error() {
    let src = with_storage(
        "typo_head",
        "  operation probe(k: MemStoer.Key) -> String = k\n",
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("unresolved type name") && e.contains("MemStoer.Key")),
        "typo'd head must be the load-blocking UnresolvedTypeName; got: {errs:?}",
    );
}

/// A 3-segment dotted name that resolves as nothing is the same hard error
/// (the WI-428 classifier is two-segment only; the join must not warn+mint).
#[test]
fn unresolvable_three_segment_type_name_is_hard_error() {
    let src = with_storage(
        "three_seg",
        "  operation probe(k: Nope.Such.Thing) -> String = k\n",
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("unresolved type name") && e.contains("Nope.Such.Thing")),
        "unresolvable 3-segment type name must be load-blocking; got: {errs:?}",
    );
}

/// ENTITY-FIELD position — the typer never eliminates a field type, so before
/// the WI-429 sweep a typo'd member (`MemStore.Kye`) loaded SILENTLY as a
/// stored malformed projection. The end-of-load formation sweep rejects it.
#[test]
fn field_position_typo_member_is_hard_error() {
    let src = with_storage(
        "field_typo",
        "  sort Holder\n    entity hold(k: MemStore.Kye)\n  end\n",
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("Kye")),
        "typo'd member in a never-eliminated field position must fail the load; got: {errs:?}",
    );
}

/// ENTITY-FIELD position, bare-spec subject: `Storage.Key` outside the sort is
/// the `T#K` carrier-conflation — rejected by the sweep even though no
/// elimination site ever sees the field type.
#[test]
fn field_position_bare_spec_projection_is_hard_error() {
    let src = with_storage(
        "field_bare_spec",
        "  sort Holder\n    entity hold(k: Storage.Key)\n  end\n",
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("conflate distinct carriers")),
        "bare-spec projection in a field position must fail the load; got: {errs:?}",
    );
}

/// The sweep validates formation only — a MANIFEST projection in a field
/// position (`MemStore.Key`, grounded through the `provides` binding) is
/// well-formed and the program loads clean.
#[test]
fn field_position_manifest_projection_loads_clean() {
    let src = with_storage(
        "field_manifest",
        "  sort Holder\n    entity hold(k: MemStore.Key)\n  end\n",
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "manifest MemStore.Key (= String via provides) is well-formed in a field; got: {errs:?}",
    );
}

/// A VALID rigid-param projection in a field position (`P.Key` under
/// `requires Storage[C = P]`) is well-formed (the rigid neutral) — the sweep
/// must not reject the forms WI-428 deliberately admits.
#[test]
fn field_position_rigid_param_projection_loads_clean() {
    let src = with_storage(
        "field_rigid",
        r#"
  sort Wrapper
    sort P = ?
    requires Storage[C = P]
    entity wrapper(provider: P, k: P.Key)
  end
"#,
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "P.Key under requires Storage[C = P] is the valid rigid neutral; got: {errs:?}",
    );
}
