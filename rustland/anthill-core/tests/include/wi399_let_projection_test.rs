//! WI-399: projection elimination LIFTED from `check_apply_iter` alone to every
//! typing site that holds the env. WI-376/397/398 discharge expression-carried
//! projections (`s.cell.T`) only at an operation CALL, via `param_to_arg_type`. A
//! projection written as a `let`-binding ANNOTATION was never eliminated: the raw
//! `ExprCarried` head leaked into the value-vs-annotation conformance check, where
//! it matched NOTHING — so a CONFORMING value (`let k: s.cell.T = "abc"` on a
//! `String` member) was wrongly REJECTED with a garbled `expected ?.T`, and a
//! contradicting value's diagnostic was equally opaque.
//!
//! The fix discharges the projection at the `let` site (`visit_type`'s `Let` arm),
//! resolving the receiver's type from the env's `var_bindings` — the let-binding peer
//! of the call-site `param_to_arg_type`. The eliminated type then drives BOTH the
//! value's expected and the conformance check, so the member type (`String`) is what
//! the value is checked against. A projection whose receiver type is NOT concretely
//! known in scope (a bare / abstract receiver, a missing member) is a LOUD error, and
//! `unify_types` now refuses any un-eliminated projection head rather than silently
//! passing it to the structural fallback (the "loud error where the receiver type is
//! not known" half).
//!
//! Design: `docs/design/expansion-during-unification.md` §4 (Placement) + §7 Layer 2.
//! Spun out of WI-376.

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

/// A `let` annotation that is a projection off a CONCRETE in-scope binding conforms:
/// `let k: s.cell.T = "abc"` on `s : Wrapper[P = Inner[T = String]]` resolves
/// `s.cell : Inner[T = String]` then `.T = String`, so binding a `String` value is
/// well-typed. (Before WI-399 the raw `s.cell.T` leaked into the conformance check and
/// this CONFORMING program was wrongly rejected.)
#[test]
fn let_projection_annotation_conforms() {
    let ok = r#"
namespace test.wi399.let_ok
  import anthill.prelude.String
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Wrapper
    sort P = ?
    entity wrap(cell: P)
  end
  operation foo(s: Wrapper[P = Inner[T = String]]) -> String =
    let k: s.cell.T = "abc"
    k
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "let k: s.cell.T resolves to String for s: Wrapper[P=Inner[T=String]]; \
         binding \"abc\" (String) must conform",
    );
}

/// The let-annotation projection is REAL: `k : s.cell.T` is `String`, so binding an
/// `Int64` value must be REJECTED — the annotation is not an opaque head that absorbs
/// any value, it is the eliminated `String`.
#[test]
fn let_projection_annotation_wrong_value_is_rejected() {
    let wrong = r#"
namespace test.wi399.let_wrong
  import anthill.prelude.{String, Int64}
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Wrapper
    sort P = ?
    entity wrap(cell: P)
  end
  operation foo(s: Wrapper[P = Inner[T = String]]) -> String =
    let k: s.cell.T = 42
    "done"
end
"#;
    let errs = load_errors(&[wrong]);
    assert!(
        errs.iter().any(|e| e.contains("String") && e.contains("Int64")),
        "k : s.cell.T is String, so binding 42 (Int64) must be rejected against String; \
         got: {errs:?}",
    );
}

/// A single-segment projection (`s.T`) in a `let` annotation threads too: `let k: s.T`
/// on `s : Box[T = String]` resolves `.T = String`, so a `String` value conforms.
/// (Proves the lift is not special-cased to the compound `a.b.T` form.)
#[test]
fn let_single_segment_projection_conforms() {
    let ok = r#"
namespace test.wi399.let_single
  import anthill.prelude.String
  sort Box
    sort T = ?
    entity box(v: T)
  end
  operation foo(s: Box[T = String]) -> String =
    let k: s.T = "abc"
    k
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "let k: s.T resolves to String for s: Box[T=String]; binding \"abc\" must conform",
    );
}

/// LOUD error where the receiver type is NOT concretely known: `s : Wrapper` leaves
/// `P` unbound, so `s.cell.T` cannot resolve — abstract-receiver projection is the
/// parked follow-on, and must surface as a LOUD diagnostic, never a silent accept (and
/// never the opaque-head leak that the old path produced).
#[test]
fn let_projection_abstract_receiver_is_loud_error() {
    let bad = r#"
namespace test.wi399.let_abstract
  import anthill.prelude.String
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Wrapper
    sort P = ?
    entity wrap(cell: P)
  end
  operation foo(s: Wrapper) -> String =
    let k: s.cell.T = "abc"
    k
end
"#;
    let errs = load_errors(&[bad]);
    assert!(
        errs.iter().any(|e| e.contains("abstract-receiver") || e.contains("not concretely")),
        "s: Wrapper leaves P unbound, so s.cell.T must be a loud abstract-receiver error; \
         got: {errs:?}",
    );
}

/// A `let` annotation that projects a member the receiver's sort does NOT declare is a
/// loud missing-member error — the elimination distinguishes a genuinely-missing member
/// from an unbound one, and neither silently passes.
#[test]
fn let_projection_missing_member_is_loud_error() {
    let bad = r#"
namespace test.wi399.let_missing
  import anthill.prelude.String
  sort Box
    sort T = ?
    entity box(v: T)
  end
  operation foo(s: Box[T = String]) -> String =
    let k: s.Nope = "abc"
    k
end
"#;
    let errs = load_errors(&[bad]);
    assert!(
        errs.iter().any(|e| e.contains("Nope") || e.contains("no member")),
        "s.Nope projects a member Box does not declare — must be a loud error; got: {errs:?}",
    );
}
