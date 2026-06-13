//! WI-431 — INSTANCE FACTS, rule 1: **coverage moves to the fact**.
//!
//! A retroactive typeclass instance is an op-valued provision fact:
//!
//! ```anthill
//! fact CpsMonad[F = Option, pure = optionPure, flatMap = optionFlatMap]
//! ```
//!
//! The op-valued bindings (`pure = optionPure`, …) ARE the dictionary entries
//! that back the spec's operations for the carrier — so adding a typeclass to a
//! carrier modifies neither the carrier nor the spec (design
//! `path-dependent-types.md` §5.4). Per rule 1, `check_provider_operations` now
//! treats an op bound in the instance fact as backed: coverage is satisfied when
//! every spec op is bound in the fact OR defaulted on the spec, and a spec op
//! that is NEITHER is still a loud `UnbackedProviderOperation` error.
//!
//! This increment is the LOADER coverage half only. The runtime dict-builder
//! reading these op bindings (eval dispatch), the op-binding signature
//! validation, the coherence rule (two instance facts ⇒ loud ambiguity), and the
//! witness-sort non-provision rule are subsequent WI-431 increments.

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

/// Rule 1 (ACCEPT): the §5.4 `CpsMonad` instance fact — `Option` retroactively
/// satisfies `CpsMonad` with `pure = optionPure, flatMap = optionFlatMap`. The
/// op-valued bindings back `pure`/`flatMap` for the concrete carrier `Option`,
/// which owns NEITHER op and on whose spec NEITHER is defaulted; pre-WI-431 this
/// failed coverage with `provides … but backs no operation`.
#[test]
fn instance_fact_op_binding_satisfies_coverage() {
    let snippet = r#"namespace test.wi431.cps_accept
  import anthill.prelude.Option

  sort CpsMonad
    sort F
      sort T = ?
    end
    sort A = ?
    sort B = ?
    operation pure(a: A) -> F[T = A]
    operation flatMap(fa: F[T = A], f: (A) -> F[T = B]) -> F[T = B]
  end

  operation optionPure[A](a: A) -> Option[T = A] = some(a)
  operation optionFlatMap[A, B](fa: Option[T = A], f: (A) -> Option[T = B]) -> Option[T = B] =
    match fa
      case some(x) -> f(x)
      case none() -> none

  fact CpsMonad[F = Option, pure = optionPure, flatMap = optionFlatMap]
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        errs.is_empty(),
        "instance fact whose op bindings cover every spec op should load clean: {errs:?}"
    );
}

/// Rule 1 (REJECT, loud): an instance fact that binds `pure` but NOT `flatMap`,
/// where `flatMap` has no spec default, must still error loudly — coverage moved
/// to the fact, so a missing op binding is the gap. Critically, the type-valued
/// binding `F = Option` (a `Sort`, not an `Operation`) is NOT mistaken for
/// op-coverage of `flatMap`.
#[test]
fn instance_fact_missing_op_binding_is_loud() {
    let snippet = r#"namespace test.wi431.cps_missing
  import anthill.prelude.Option

  sort CpsMonad
    sort F
      sort T = ?
    end
    sort A = ?
    sort B = ?
    operation pure(a: A) -> F[T = A]
    operation flatMap(fa: F[T = A], f: (A) -> F[T = B]) -> F[T = B]
  end

  operation optionPure[A](a: A) -> Option[T = A] = some(a)

  fact CpsMonad[F = Option, pure = optionPure]
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        errs.iter().any(|e| e.contains("backs no operation") && e.contains("flatMap")),
        "missing flatMap binding (no default) must be a loud UnbackedProviderOperation: {errs:?}"
    );
    // `pure` IS bound — it must NOT be reported.
    assert!(
        !errs.iter().any(|e| e.contains("backs no operation") && e.contains("CpsMonad.pure")),
        "the bound `pure` op must not be reported as unbacked: {errs:?}"
    );
}

/// Rule 1 (default coexists): a spec op with a DEFAULT body (`idF`, a derived op
/// like §5.4's `flatten`) stays a spec default — it needs no instance-fact
/// binding. The fact binds only the primitives `pure`/`flatMap`; `idF` is
/// covered by its default.
#[test]
fn instance_fact_spec_default_op_needs_no_binding() {
    let snippet = r#"namespace test.wi431.cps_default
  import anthill.prelude.Option

  sort CpsMonad
    sort F
      sort T = ?
    end
    sort A = ?
    sort B = ?
    operation pure(a: A) -> F[T = A]
    operation flatMap(fa: F[T = A], f: (A) -> F[T = B]) -> F[T = B]
    operation idF(fa: F[T = A]) -> F[T = A] = fa
  end

  operation optionPure[A](a: A) -> Option[T = A] = some(a)
  operation optionFlatMap[A, B](fa: Option[T = A], f: (A) -> Option[T = B]) -> Option[T = B] =
    match fa
      case some(x) -> f(x)
      case none() -> none

  fact CpsMonad[F = Option, pure = optionPure, flatMap = optionFlatMap]
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        errs.is_empty(),
        "a spec-defaulted op (idF) needs no instance-fact binding; fact should load clean: {errs:?}"
    );
}
