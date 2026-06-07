//! WI-397: expression-carried type projection with a COMPOUND receiver (`a.b.T`).
//!
//! WI-376 delivered the single value-reference receiver (`s.T`), which rides a
//! ground `Fn{ExprCarried, value: Ref(s), member: Ref(M)}` term. A COMPOUND
//! receiver — a field path like `s.cell.T` — has a receiver that is itself an
//! occurrence (a `DotApply` field access), so it rides the `TypeNode::ExprCarried`
//! Node carrier. For this to index into the discrimination tree (the op's
//! `OperationInfo` fact embeds the return type), `DotApply` had to become STRUCTURAL
//! in `occ_head` (its `dot_apply` term twin) rather than `Opaque` — WI-397.
//!
//! The eliminator resolves the receiver path's static type (head param type from the
//! call's argument, then each field's type via the receiver's type-args — the same
//! substitution pattern field types use), then projects the member. Eliminated at the
//! CALL site (check_apply_iter), like the single-ref form.
//!
//! Design: `docs/design/path-dependent-types.md` §1 (the `s.provider.K` trace) + §6
//! seam map (WI-397). The member projected here is a DIRECT type-param of the field's
//! sort (`Inner[T = String].T`); projecting a member off a PROVIDED spec is a separate
//! follow-on, and an ABSTRACT receiver stays the existing loud error.

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

/// `getT(s: Wrapper) -> s.cell.T` threads through a COMPOUND receiver: calling it on
/// a `Wrapper[P = Inner[T = String]]` resolves `s.cell : Inner[T = String]` (the
/// field `cell : P` substituted) then `.T = String`, so returning the call where
/// `String` is declared CONFORMS.
#[test]
fn compound_projection_threads_field_then_member() {
    let ok = r#"
namespace test.wi397.ok
  import anthill.prelude.String
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Wrapper
    sort P = ?
    entity wrap(cell: P)
  end
  operation getT(s: Wrapper) -> s.cell.T
  operation caller(w: Wrapper[P = Inner[T = String]]) -> String = getT(w)
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "getT(w) is Wrapper[P=Inner[T=String]].cell.T = Inner[T=String].T = String; \
         returning it as String must conform",
    );
}

/// The compound projection is REAL: `getT(w)` is `String`, so returning it where
/// `Int64` is declared must be REJECTED — the field path did not invent a fresh type.
#[test]
fn compound_projection_wrong_member_is_rejected() {
    let wrong = r#"
namespace test.wi397.wrong
  import anthill.prelude.{String, Int64}
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Wrapper
    sort P = ?
    entity wrap(cell: P)
  end
  operation getT(s: Wrapper) -> s.cell.T
  operation caller(w: Wrapper[P = Inner[T = String]]) -> Int64 = getT(w)
end
"#;
    assert!(
        !load_errors(&[wrong]).is_empty(),
        "getT(w) is String, not Int64 — the wrong declared return must be rejected",
    );
}

/// A field path the receiver's sort does NOT declare is a loud error, never a silent
/// fresh var: `s.nope.T` names a field `nope` that `Wrapper` has no constructor for.
#[test]
fn compound_projection_missing_field_is_loud_error() {
    let bad = r#"
namespace test.wi397.missing
  import anthill.prelude.{String, Int64}
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Wrapper
    sort P = ?
    entity wrap(cell: P)
  end
  operation getT(s: Wrapper) -> s.nope.T
  operation caller(w: Wrapper[P = Inner[T = String]]) -> String = getT(w)
end
"#;
    let errs = load_errors(&[bad]);
    assert!(
        errs.iter().any(|e| e.contains("nope") || e.contains("field")),
        "projecting off a non-existent field must be a loud error; got: {errs:?}",
    );
}

/// A multi-constructor receiver where ALL variants declare the field with the SAME
/// type resolves deterministically (order-independent) — `Multi[P = Inner[T =
/// String]].cell.T = String`. (`resolve_field_type` enumerates constructors from a
/// HashMap, so it must agree across all variants, not pick the first.)
#[test]
fn compound_projection_uniform_multi_ctor_field_resolves() {
    let ok = r#"
namespace test.wi397.multi_ok
  import anthill.prelude.String
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  enum Multi
    sort P = ?
    entity a(cell: P)
    entity b(cell: P)
  end
  operation getT(s: Multi) -> s.cell.T
  operation caller(w: Multi[P = Inner[T = String]]) -> String = getT(w)
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "all variants declare `cell: P`, so the field type is unambiguous and resolves to String",
    );
}

/// A multi-constructor receiver whose variants declare the same field name with
/// DIFFERENT types is AMBIGUOUS — a loud error, never an order-dependent pick (the
/// determinism fix: `constructors_of_sort` iterates a non-deterministic HashMap).
#[test]
fn compound_projection_divergent_multi_ctor_field_is_loud_error() {
    let bad = r#"
namespace test.wi397.multi_bad
  import anthill.prelude.{String, Int64}
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  enum Multi
    sort P = ?
    entity a(cell: P)
    entity b(cell: Int64)
  end
  operation getT(s: Multi) -> s.cell.T
  operation caller(w: Multi[P = Inner[T = String]]) -> String = getT(w)
end
"#;
    let errs = load_errors(&[bad]);
    assert!(
        errs.iter().any(|e| e.contains("differing") || e.contains("ambiguous") || e.contains("cell")),
        "a field declared with differing types across variants must be a loud error; got: {errs:?}",
    );
}
