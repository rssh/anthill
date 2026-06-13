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

/// EVAL — op-valued bindings ARE the dictionary: a call to the spec op `combine` on
/// `Tag` values dispatches to the instance fact's bound `tagCombine`, even though
/// `Tag` owns no `combine` op of its own (`sort_ops_lookup(Tag, combine)` returns only
/// the inherited body-less spec op — no real impl — and the instance-fact binding is
/// the dictionary entry that backs it). First-order spec (no higher-kinded `F`), so
/// the typer binds `T := Tag` from the argument with no concrete-fill and leaves the
/// call for value-directed dispatch; the gap is purely the eval-side dispatch reading
/// the fact's op binding. Result `99` ⇒ `tagCombine` ran (not some other path).
#[test]
fn instance_fact_op_dispatches_at_eval() {
    let src = r#"namespace test.wi431.eval
  import anthill.prelude.Int64

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end
  operation tagCombine(x: Tag, y: Tag) -> Tag = tag(n: 99)
  fact Combiner[T = Tag, combine = tagCombine]

  operation runCombine() -> Int64 =
    match combine(tag(n: 1), tag(n: 2))
      case tag(v) -> v
end
"#;
    let mut interp = crate::common::interp_for(src);
    match interp.call("test.wi431.eval.runCombine", &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => assert_eq!(
            n, 99,
            "combine(tag, tag) must dispatch to the instance-fact-bound tagCombine (n = 99); got {n}"
        ),
        other => panic!(
            "combine(tag, tag) should dispatch via the instance fact to tagCombine; got {other:?}"
        ),
    }
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

/// COHERENCE (rule 2) ANCHOR — deferred. Two instance facts covering the same
/// (spec, carrier) with DIFFERENT op bindings must be a LOUD ambiguity error
/// (design §5.4 rule 2, keyed on the full canonical application / WI-419
/// identity). Today they load clean and eval dispatch picks the FIRST via
/// `provider_spec_view_bindings`' pre-existing first-provider-wins contract
/// (shared with WI-402/415..423 dispatch) — silent, not loud. `#[ignore]`'d
/// until the coherence increment lands; un-ignore it then.
#[test]
#[ignore = "WI-431 coherence (rule 2) not yet implemented — instance-fact ambiguity is silent"]
fn duplicate_instance_facts_are_a_loud_ambiguity() {
    let snippet = r#"namespace test.wi431.coherence
  import anthill.prelude.Int64

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end
  operation combineA(x: Tag, y: Tag) -> Tag = tag(n: 1)
  operation combineB(x: Tag, y: Tag) -> Tag = tag(n: 2)

  fact Combiner[T = Tag, combine = combineA]
  fact Combiner[T = Tag, combine = combineB]
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        errs.iter().any(|e| e.contains("ambigu") || e.contains("coheren")),
        "two instance facts for (Combiner, Tag) must be a loud ambiguity error; got: {errs:?}"
    );
}
