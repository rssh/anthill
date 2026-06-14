//! WI-383 §5.4 — higher-kinded emulation via RIGID-FUNCTOR APPLICATIONS (`F[T = A]`).
//!
//! A higher-kinded sort param `F` — written in the MARKED enclosing-list form
//! `sort Box[F[T]]` (WI-451; `F[T]` desugars to a `sort F { sort T = ? }` marked a
//! non-rigid type variable, WI-452) — is a type CONSTRUCTOR; an application `F[T = A]`
//! binds its member `T`, with the element types `A` / `B` as PER-OPERATION type params
//! (`operation fmap[A, B](…)`, §5.4 "CpsMonad's only parameter is its type constructor
//! F[T]"). Per the §5.4 model (`docs/design/path-dependent-types.md`), an application is
//! the INJECTIVE dual of the NON-injective `RigidTypeProjection` (`C.Elem`):
//! `F[T = A] ≟ F[T = B] ⟹ A ≟ B`, and a differing FUNCTOR (`F` vs `G`) or BINDING never
//! unifies. At the DEFINITION site the marked `?F` skolemizes to a RIGID (never a logic
//! var), so the fragment is first-order/decidable — the Miller-pattern concern arises
//! only in rule bodies (flexible `?f(?x)` heads).
//!
//! PROBE OUTCOME (WI-383 piece 3, 2026-06-13): injective decomposition is ALREADY FREE
//! via the existing parameterized `unify_types` arm — `F[T = A]` is the term backing
//! `Fn{F, named:[(T, A)]}`, so `unify_parameterized` decomposes it structurally (functor
//! equality + per-binding unify) with no HK-specific code. These tests PIN that the
//! decomposition is sound (accepts correct applications, rejects a wrong binding or a
//! wrong functor) so a future typer change cannot silently break HK injectivity. The
//! structured-param member registration (piece 1) and the rule-body surface (piece 4
//! loads; the Miller guard is a resolver/SLD concern) are pinned too. CONCRETE FILL
//! (`F := Option` via an instance fact) is covered by WI-453's tests; here the abstract
//! spec keeps `F` skolemized at the def-site, so decomposition is against a fixed-but-
//! arbitrary functor.

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

/// Piece 1: a marked HK sort param `F` (enclosing form `Box[F[T]]`, member `T`) plus
/// applications `F[T = A]` / `F[T = B]` in operation signatures — element types `A` /
/// `B` as per-operation type params — parses, loads, and typechecks. The §5.4
/// marked-carrier surface, pinned.
#[test]
fn structured_param_application_surface_loads() {
    let snippet = r#"namespace test.hk.base
  sort Box[F[T]]
    operation wrap[A](a: A) -> F[T = A]
    operation fmap[A, B](fa: F[T = A], f: (A) -> B) -> F[T = B]
  end
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(errs.is_empty(), "marked-carrier HK surface should load: {errs:?}");
}

/// Piece 3 (ACCEPT): a body whose result is an application of the SAME functor with the
/// SAME binding typechecks — `reFmap` returns `fmap(fa, f) : F[T = B]` against its declared
/// `F[T = B]`, a decomposition `F[T = B] ≟ F[T = B]` via the parameterized arm.
#[test]
fn rigid_functor_application_decomposes_accept() {
    let snippet = r#"namespace test.hk.pt
  sort Box[F[T]]
    operation fmap[A, B](fa: F[T = A], f: (A) -> B) -> F[T = B]
    operation reFmap[A, B](fa: F[T = A], f: (A) -> B) -> F[T = B] = fmap(fa, f)
  end
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(errs.is_empty(), "reFmap (-> F[T=B], returns F[T=B]) should typecheck: {errs:?}");
}

/// Piece 3 (REJECT, wrong binding): injectivity — `wrongFmap` returns `fmap(...) : F[T = B]`
/// but declares `F[T = A]`; `F[T = B] ≟ F[T = A]` must FAIL (the bindings, distinct rigids,
/// clash). This is the soundness core: applications are NOT opaque-equal.
#[test]
fn rigid_functor_application_rejects_wrong_binding() {
    let snippet = r#"namespace test.hk.wrong
  sort Box[F[T]]
    operation fmap[A, B](fa: F[T = A], f: (A) -> B) -> F[T = B]
    operation wrongFmap[A, B](fa: F[T = A], f: (A) -> B) -> F[T = A] = fmap(fa, f)
  end
end
"#;
    let errs = load_errors(&[snippet]);
    // The rejection is sound AND the diagnostic DISTINGUISHES the bindings: the skolemized
    // op type-params print as `?A` vs `?B` (not two identical `?_`), so `expected != got` is
    // legible — `rigidify_op_type_params` names each rigid after its parameter's short name.
    assert!(
        errs.iter().any(|e| {
            e.contains("wrongFmap") && e.contains("mismatch") && e.contains("?A") && e.contains("?B")
        }),
        "wrongFmap must be rejected with a binding-distinct diagnostic (?A vs ?B); got: {errs:?}"
    );
}

/// Piece 3 (REJECT, wrong functor): decomposition checks the FUNCTOR head, not just the
/// binding — `confused` returns `wrapG(a) : G[T = A]` but declares `F[T = A]`; `F ≠ G`
/// rejects. (Here the diagnostic distinguishes the functors: `expected F[...], got G[...]`.)
/// TWO marked HK carriers in one enclosing list (`Box[F[T], G[T]]`).
#[test]
fn rigid_functor_application_rejects_wrong_functor() {
    let snippet = r#"namespace test.hk.fg
  sort Box[F[T], G[T]]
    operation wrapG[A](a: A) -> G[T = A]
    operation confused[A](a: A) -> F[T = A] = wrapG(a)
  end
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        errs.iter().any(|e| e.contains("confused") && e.contains("mismatch")),
        "confused (-> F[T=A], returns G[T=A]) MUST be rejected on the functor; got: {errs:?}"
    );
}

/// A NESTED application `F[T = F[T = A]]` (the `flatten` argument shape) decomposes too —
/// `viaFlatten` passes its `F[T = F[T = A]]` argument straight to `flatten`.
#[test]
fn nested_application_decomposes() {
    let snippet = r#"namespace test.hk.nest
  sort Box[F[T]]
    operation flatten[A](ffa: F[T = F[T = A]]) -> F[T = A]
    operation viaFlatten[A](ffa: F[T = F[T = A]]) -> F[T = A] = flatten(ffa)
  end
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(errs.is_empty(), "nested F[T=F[T=A]] pass-through should typecheck: {errs:?}");
}

/// Piece 4 (surface): the proposal-002 monad-law rules — including the FLEXIBLE-head
/// application `?f(?x)` (the Miller-pattern case) — parse and LOAD clean. The Miller
/// guard proper is a resolver/SLD concern (when the rules RUN), not a typecheck-time one.
#[test]
fn monad_law_rule_bodies_load() {
    let snippet = r#"namespace test.hk.laws
  sort CpsMonad[F[T]]
    operation pure[A](a: A) -> F[T = A]
    operation flatMap[A, B](fa: F[T = A], f: (A) -> F[T = B]) -> F[T = B]
    rule left_id: flatMap(pure(?x), ?f) = ?f(?x)
    rule right_id: flatMap(?m, pure) = ?m
  end
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(errs.is_empty(), "monad-law rules (flexible head ?f(?x)) should load: {errs:?}");
}

/// The full proposal-002 `CpsMonad` operation surface (marked carrier `F[T]`, `pure`/
/// `map`/`flatMap`, derived `flatten` with the nested application) loads and typechecks —
/// the dotty-cps `CpsMonad[F[_]]` shape, modulo instances (WI-431/WI-453) and the
/// hyphenated `bind-then` Kleisli op (a name-syntax concern, omitted here).
#[test]
fn full_cpsmonad_operation_surface_loads() {
    let snippet = r#"namespace test.hk.cps
  sort CpsMonad[F[T]]
    operation pure[A](a: A) -> F[T = A]
    operation map[A, B](fa: F[T = A], f: (A) -> B) -> F[T = B]
    operation flatMap[A, B](fa: F[T = A], f: (A) -> F[T = B]) -> F[T = B]
    operation flatten[A](ffa: F[T = F[T = A]]) -> F[T = A]
  end
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(errs.is_empty(), "CpsMonad operation surface should load: {errs:?}");
}
