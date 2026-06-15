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

// ── WI-400 CORE: abstract-stays-poly (neutral formation) + ζ (σ-equality of receivers) ──
//
// An ABSTRACT receiver projection no longer ERRORS at formation — it forms a rigid
// NEUTRAL (`project_type_member` → `ProjResult::Neutral`, co-delivering WI-376
// abstract-stays-poly), PROVIDED the member is declared on the receiver's interface: a
// declared-but-unbound type-parameter of a concrete sort, OR (for an abstract type-variable
// receiver) a member lent by the declaring sort's `requires Spec[param]` bound. Two
// neutrals are the SAME type iff they project the SAME member off σ-EQUAL (here:
// structurally-equal) receivers — the ζ arm of `unify_types` / `types_compatible`. A
// neutral never equals a concrete type, and the head is NON-INJECTIVE (two distinct
// receivers stay distinct, never forced equal). Design: path-dependent-types.md §4 / §4.1.

/// §4.1 "abstract-stays-poly" + path-identity (the §1 shape, WITHIN one operation). With
/// `State requires DataProvider[P]` and `DataProvider` declaring `K`, the projection
/// `s.provider.K` off the abstract `s.provider : P` is a well-formed rigid neutral, and
/// `idK(s: State, k: s.provider.K) -> s.provider.K = k` type-checks: `k`'s type and the
/// declared return are the SAME neutral (same receiver `s.provider`, same member `K`), so
/// ζ accepts. (The full §1 body `s.provider.hasKey(k)` additionally needs abstract spec-op
/// DISPATCH through the `requires` bound — a separate concern from the projection/ζ core.)
#[test]
fn abstract_projection_path_identity_within_op() {
    let ok = r#"
namespace test.wi400.zeta_idk
  sort DataProvider
    sort K = ?
  end
  sort State
    sort P = ?
    requires DataProvider[P]
    entity state(provider: P)
  end
  operation idK(s: State, k: s.provider.K) -> s.provider.K = k
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "s.provider.K forms a neutral (P abstract, K lent by `requires DataProvider[P]`); \
         returning k: s.provider.K as the SAME s.provider.K conforms by ζ path-identity; \
         got: {:?}",
        load_errors(&[ok]),
    );
}

/// §4.1 "Non-decomposition" — the soundness core. `ExprCarried` is a NON-INJECTIVE head:
/// `s.provider.K` and `t.provider.K` may coincide without `s = t`, so ζ must NOT decompose
/// `s.provider.K =?= t.provider.K` into `s =?= t`. `bad(s: State, t: State, k: s.provider.K)
/// -> t.provider.K = k` returns `k : s.provider.K` under a declared `t.provider.K` — DISTINCT
/// receivers, so ζ refuses (never forces `s = t`), and the body is rejected.
#[test]
fn abstract_projection_distinct_receivers_rejected() {
    let bad = r#"
namespace test.wi400.zeta_bad
  sort DataProvider
    sort K = ?
  end
  sort State
    sort P = ?
    requires DataProvider[P]
    entity state(provider: P)
  end
  operation bad(s: State, t: State, k: s.provider.K) -> t.provider.K = k
end
"#;
    let errs = load_errors(&[bad]);
    assert!(
        errs.iter().any(|e| e.contains("s.provider.K") && e.contains("t.provider.K")),
        "distinct receivers s vs t must NOT be forced equal — k: s.provider.K returned as \
         t.provider.K must be rejected (non-injective head); got: {errs:?}",
    );
}

/// §4.1 "abstract-stays-poly" — the WI-399 loud error is now reachable only for a GENUINELY
/// missing member, not an unbound one. A member that NO `requires` bound lends the abstract
/// receiver's type-parameter (`State requires DataProvider[P]`, and DataProvider has no
/// member `Bogus`) is a loud error, never a silent neutral.
#[test]
fn abstract_projection_missing_member_is_loud() {
    let bad = r#"
namespace test.wi400.zeta_missing
  sort DataProvider
    sort K = ?
  end
  sort State
    sort P = ?
    requires DataProvider[P]
    entity state(provider: P)
  end
  operation bad(s: State, k: s.provider.Bogus) -> s.provider.Bogus = k
end
"#;
    let errs = load_errors(&[bad]);
    assert!(
        errs.iter().any(|e| e.contains("Bogus") && (e.contains("requires") || e.contains("declares a member"))),
        "no `requires` bound declares a member Bogus, so s.provider.Bogus must be a loud \
         error (not a silent neutral); got: {errs:?}",
    );
}

// ── WI-400 INCREMENT C: eager let-alias (the `let y = z ⟹ y.M ≡ z.M` Scala divergence) ──
//
// A `let` whose value is a STABLE receiver path (a var / field-access chain — immutable
// `let` ⟹ one runtime value) records the bound name's CANONICAL receiver on the env. A
// projection `y.M` formed at a later let site is canonicalized through that map BEFORE
// elimination, so it carries the SAME receiver as the aliased path and the ζ arm equates
// them. Anthill identifies a path type by UNIFYING the receiver (`let y = z ⟹ y.M ≡ z.M`),
// where Scala leaves `y.M ≠ z.M` (nominal over the syntactic path). Design §4.1 / §"headline".

/// `let y = p` aliases `y` to the param `p`, so `let m: y.K = k` resolves `y.K` to the SAME
/// neutral as `k`'s declared `p.K` and conforms — and returning `m` as `-> p.K` conforms
/// too. Without eager-let-alias `y.K` would be a projection off the let-bound `y` (its own
/// distinct receiver) and `≢ p.K`, so `let m: y.K = k` would be rejected; the alias
/// canonicalizes the receiver `y` to `p`. (`p : DataProvider` with `K` a declared
/// type-parameter projects the bare-sort neutral `p.K`, sidestepping value-position field
/// access, which is a separate unsupported form — design §5.1.)
#[test]
fn let_alias_canonicalizes_receiver() {
    let ok = r#"
namespace test.wi400.let_alias_ok
  sort DataProvider
    sort K = ?
  end
  operation f(p: DataProvider, k: p.K) -> p.K =
    let y = p
    let m: y.K = k
    m
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "let y = p ⟹ y.K ≡ p.K, so `let m: y.K = k` conforms and `m` returns as p.K; \
         got: {:?}",
        load_errors(&[ok]),
    );
}

/// The alias canonicalizes to the RIGHT receiver — `let y = p` makes `y.K` the `p`
/// projection, NOT the `q` one. So `m : y.K` (= `p.K`) returned under a declared `q.K` is
/// REJECTED (distinct receivers, the non-injective head). Proves the alias is not a blanket
/// "any projection matches" — `let y = z; let w = other ⟹ y.M ≢ w.M`.
#[test]
fn let_alias_distinct_receiver_rejected() {
    let bad = r#"
namespace test.wi400.let_alias_bad
  sort DataProvider
    sort K = ?
  end
  operation g(p: DataProvider, q: DataProvider, k: p.K) -> q.K =
    let y = p
    let m: y.K = k
    m
end
"#;
    let errs = load_errors(&[bad]);
    assert!(
        errs.iter().any(|e| e.contains("p.K") && e.contains("q.K")),
        "y aliases p, so m : p.K must be rejected under a -> q.K return (distinct \
         receivers); got: {errs:?}",
    );
}

/// An UNSTABLE let value (a call) does NOT alias — `y` stays its OWN neutral receiver, so
/// `y.K ≢ p.K`. The §4.1 stability rule: only a value-reference / field-access path
/// canonicalizes (immutable `let` ⟹ one runtime value); `let y = pick(p)` mints a fresh
/// value. So `let m: y.K = k` (`k : p.K`) is REJECTED — the alias did not silently equate
/// `y.K` with `p.K`. Contrast `let_alias_canonicalizes_receiver` (same shape, stable value).
#[test]
fn let_unstable_value_does_not_alias() {
    let bad = r#"
namespace test.wi400.let_unstable
  sort DataProvider
    sort K = ?
    operation pick(p: DataProvider) -> DataProvider
  end
  operation g(p: DataProvider, k: p.K) -> p.K =
    let y = p.pick()
    let m: y.K = k
    m
end
"#;
    let errs = load_errors(&[bad]);
    assert!(
        errs.iter().any(|e| e.contains("y.K") && e.contains("p.K")),
        "let y = pick(p) is unstable, so y.K does NOT alias p.K; `let m: y.K = k` must be \
         rejected (k : p.K ≢ y.K); got: {errs:?}",
    );
}

/// Soundness: re-binding an aliased name to an UNSTABLE value CLEARS the stale alias. A
/// `let y = p` (alias `y → p`) shadowed by `let y = pick(p)` (unstable) must NOT keep the
/// old alias — otherwise `let m: y.K = k` would canonicalize `y.K` to `p.K` and wrongly
/// accept, even though the shadowing `y` is a fresh value whose `y.K ≢ p.K`. (Regression
/// for a /code-review-found false-accept.)
#[test]
fn let_alias_cleared_on_unstable_rebind() {
    let bad = r#"
namespace test.wi400.let_rebind
  sort DataProvider
    sort K = ?
    operation pick(p: DataProvider) -> DataProvider
  end
  operation g(p: DataProvider, k: p.K) -> p.K =
    let y = p
    let y = p.pick()
    let m: y.K = k
    m
end
"#;
    let errs = load_errors(&[bad]);
    assert!(
        errs.iter().any(|e| e.contains("y.K") && e.contains("p.K")),
        "the shadowing `let y = pick(p)` must clear the stale `y → p` alias, so `y.K ≢ p.K` \
         and `let m: y.K = k` is rejected; got: {errs:?}",
    );
}
