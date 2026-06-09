//! WI-400 (body-site, MANIFEST half): a projection PARAMETER type (`k: s.cell.T`) is
//! discharged against the OTHER params' DECLARED types when the operation BODY is
//! checked — the body-check peer of the call-site elimination (`check_apply_iter` /
//! WI-398, which discharges against ARGUMENT types). Before this, `check_operation_bodies`
//! bound a projection param RAW into the body env, so the body's use of it compared the
//! un-eliminated `ExprCarried` and failed (`unify_types` refuses it, WI-399) — even when
//! the receiver's declared type made the member MANIFEST.
//!
//! This covers the MANIFEST receiver: `s: Wrapper[P = Inner[T = String]]` ⟹
//! `k : s.cell.T` δ-grounds to `String`, in both forward and reverse declaration order
//! (the elimination is order-independent, like the call-site WI-398). The ABSTRACT
//! receiver (`s: State`, `P` open ⟹ `k : ⟨s.provider⟩.K` a rigid neutral) is WI-400's
//! remaining, soundness-critical core (the §1 path-dependent example); its acceptance is
//! specified in path-dependent-types.md §4.1 and its faithful test is written with that
//! core (see the note at the end of this file).
//!
//! Design: `docs/design/path-dependent-types.md` §4.1 ("the operation-body site is
//! WI-400's PRIMARY site") + its test matrix.

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

/// A MANIFEST projection param type in a BODY δ-grounds and the body type-checks:
/// `idElem(s: Wrapper[P = Inner[T = String]], k: s.cell.T) -> String = k` — `k` binds as
/// `String` (not the raw `?.T` neutral), so returning `k` conforms to `String`.
#[test]
fn body_site_manifest_projection_grounds() {
    let ok = r#"
namespace test.wi400.body_ok
  import anthill.prelude.String
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Wrapper
    sort P = ?
    entity wrap(cell: P)
  end
  operation idElem(s: Wrapper[P = Inner[T = String]], k: s.cell.T) -> String = k
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "k : s.cell.T δ-grounds to String at body-binding, so `= k` conforms to -> String",
    );
}

/// The body-site δ-ground is REAL: `k` is `String`, so a body returning it under a
/// declared `-> Int64` is rejected — the param is the eliminated `String`, not an opaque
/// head that conforms to anything.
#[test]
fn body_site_manifest_projection_wrong_return_rejected() {
    let wrong = r#"
namespace test.wi400.body_wrong
  import anthill.prelude.{String, Int64}
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Wrapper
    sort P = ?
    entity wrap(cell: P)
  end
  operation idElem(s: Wrapper[P = Inner[T = String]], k: s.cell.T) -> Int64 = k
end
"#;
    let errs = load_errors(&[wrong]);
    assert!(
        errs.iter().any(|e| e.contains("Int64") && e.contains("String")),
        "k : s.cell.T is String, so a body returning it under -> Int64 must be rejected; \
         got: {errs:?}",
    );
}

/// CHAIN feed-forward, FORWARD declaration order: an eliminated param type feeds forward,
/// so a later param may project an EARLIER (already-eliminated) one. `b: a.P` grounds to
/// `Mid[Q=Inner[T=String]]` off the manifest `a`, then `c: b.Q` grounds to
/// `Inner[T=String]` off the eliminated `b`.
#[test]
fn body_site_chain_feeds_forward() {
    let ok = r#"
namespace test.wi400.body_chain
  import anthill.prelude.String
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Mid
    sort Q = ?
    entity mid(q: Q)
  end
  sort Outer
    sort P = ?
    entity outer(p: P)
  end
  operation chain(a: Outer[P = Mid[Q = Inner[T = String]]], b: a.P, c: b.Q) -> Inner[T = String] = c
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "b: a.P grounds off manifest a, then c: b.Q grounds off the eliminated b (feed-forward)",
    );
}

/// The body-site elimination is ORDER-INDEPENDENT (peer of the call-site, WI-398's
/// `cross_param_projection_receiver_declared_after_is_ordered`): the SAME chain declared
/// in REVERSE dependency order (`c` before `b` before `a`) must still type-check. The
/// fixpoint discharges `b` off the manifest `a` in pass 1 and `c` off the eliminated `b`
/// in pass 2 — declaration order does not matter, only the (acyclic) dependency does.
#[test]
fn body_site_reverse_order_chain_feeds_forward() {
    let ok = r#"
namespace test.wi400.body_chain_rev
  import anthill.prelude.String
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Mid
    sort Q = ?
    entity mid(q: Q)
  end
  sort Outer
    sort P = ?
    entity outer(p: P)
  end
  operation chain(c: b.Q, b: a.P, a: Outer[P = Mid[Q = Inner[T = String]]]) -> Inner[T = String] = c
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "reverse-declared chain (c, b, a) must type-check at the body site, like at the call site",
    );
}

// REMAINING SCOPE (WI-400 core): an ABSTRACT receiver in a body should keep the
// projection as a rigid NEUTRAL (path-identity) so the §1 example type-checks in its own
// generality (the abstract→neutral relaxation + the σ-equality ζ arm). No on-disk anchor
// is added here yet: a faithful gate needs the receiver's abstract type to DECLARE the
// projected member (a bound / `requires` so `s.provider.K` is well-formed, not "no member
// K"), plus dispatch on the abstract receiver — machinery the core itself introduces. The
// acceptance is specified in docs/design/path-dependent-types.md §4.1 (test matrix); the
// faithful test is written WITH that core, not pre-committed here in a form that would
// fail for unrelated reasons.
