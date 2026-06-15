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
//! Increment 1 was the LOADER coverage half (rule 1); increment 2 added the
//! value-directed eval dispatch reading these op bindings; increment 3 added rule
//! 2 — COHERENCE: two DISTINCT instance facts for the same (spec, carrier) are a
//! loud ambiguity at load (`duplicate_instance_facts_are_a_loud_ambiguity`),
//! while identical facts stay idempotent; increment 4 (A2) adds the DICT-THREADED
//! dispatch path — a generic `requires Spec[T]` body dispatches a spec op via the
//! requirement dict built from the instance fact
//! (`instance_fact_op_dispatches_via_threaded_dict`), the only route when the
//! carrier is not in an argument. The op-binding signature validation and the
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

  sort CpsMonad[F[T]]
    operation pure[A](a: A) -> F[T = A]
    operation flatMap[A, B](fa: F[T = A], f: (A) -> F[T = B]) -> F[T = B]
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

  sort CpsMonad[F[T]]
    operation pure[A](a: A) -> F[T = A]
    operation flatMap[A, B](fa: F[T = A], f: (A) -> F[T = B]) -> F[T = B]
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
  import test.wi431.eval.Combiner.{combine}

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

/// EVAL — DICT-THREADED dispatch (increment 4 / A2): the spec op `zero() -> T`
/// carries the carrier `T` ONLY in its return type — no `T`-typed argument — so
/// value-directed dispatch (`resolve_spec_op_target_by_value`, increment 2)
/// CANNOT classify the carrier from a runtime value and the threaded dispatching
/// dict is the ONLY route. (A `combine(x: T, y: T)`-style op would be rescued by
/// value-directed dispatch reading `T` from an arg, masking this gap — see the
/// trace in WI-431 increment-4 notes.) A parameterized sort `Box` with
/// `requires HasZero[T]` calls `zero()` on its abstract `T`; at the call
/// `zeroLike(box(tag))` the receiver pins `T := Tag`, the `HasZero[T = Tag]` dict
/// is built by SLD against the instance fact's `SortProvidesInfo`
/// (`build_dep_projection` Strategy 3 ⇒ `construct_requirement(Tag, nil)`) and
/// threaded in; inside, `zero` dispatches via `dispatch_via_sort_ops_table`,
/// which must read the instance fact's `zero = tagZero` binding (Tag owns no real
/// `zero`). Without the increment-4 fallback this dies (the body-less spec op has
/// no impl and no value to re-derive from); result `42` ⇒ `tagZero` ran.
#[test]
fn instance_fact_op_dispatches_via_threaded_dict() {
    let src = r#"namespace test.wi431.threaded
  import anthill.prelude.Int64

  sort HasZero
    sort T = ?
    operation zero() -> T
  end

  sort Tag
    entity tag(n: Int64)
  end
  operation tagZero() -> Tag = tag(n: 42)
  fact HasZero[T = Tag, zero = tagZero]

  sort Box
    sort T = ?
    requires HasZero[T]
    entity box(content: T)
    operation zeroLike(b: Box) -> T =
      match b
        case box(_) -> zero()
  end

  operation runThreaded() -> Int64 =
    match box(content: tag(n: 1)).zeroLike()
      case tag(v) -> v
end
"#;
    let mut interp = crate::common::interp_for(src);
    match interp.call("test.wi431.threaded.runThreaded", &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => assert_eq!(
            n, 42,
            "zeroLike must thread a HasZero[T=Tag] dict from the instance fact and dispatch zero to tagZero (n = 42); got {n}"
        ),
        other => panic!(
            "zeroLike should dispatch zero via the threaded instance-fact dict to tagZero; got {other:?}"
        ),
    }
}

/// EVAL — DICT-THREADED dispatch when the spec ITSELF `requires` another spec
/// (regression guard): `HasZ requires MyEq` and is provided retroactively by
/// `fact HasZ[T = Tag, hzero = tagZero]` (with `fact MyEq[T = Tag]` satisfying the
/// provider-requires). The nullary `hzero() -> T` forces the threaded path (no
/// carrier arg ⇒ no value-directed rescue), and the target `tagZero` is a
/// namespace-level instance-fact op with no parent sort. An instance-fact-derived
/// dict is a LEAF (`construct_requirement(Tag, nil)`, arity 0) — it does NOT
/// bundle the spec's `MyEq` sub-requirement — so `expand_dispatching_dict`'s
/// arity check (`dict.arity()` vs the target's requires-chain) is `0 == 0` and
/// does not spuriously fire `EvalError::Internal`. Result `7` ⇒ `tagZero` ran.
#[test]
fn instance_fact_op_dispatches_when_spec_has_requires() {
    let src = r#"namespace test.wi431.subreq
  import anthill.prelude.{Int64, Bool}

  sort MyEq
    sort T = ?
    operation myeq(x: T, y: T) -> Bool
  end

  sort HasZ
    sort T = ?
    requires MyEq[T]
    operation hzero() -> T
  end

  sort Tag
    entity tag(n: Int64)
  end
  operation tagEq(x: Tag, y: Tag) -> Bool =
    match x
      case tag(a) ->
        match y
          case tag(b) -> eq(a, b)
  operation tagZero() -> Tag = tag(n: 7)
  fact MyEq[T = Tag, myeq = tagEq]
  fact HasZ[T = Tag, hzero = tagZero]

  sort Box
    sort T = ?
    requires HasZ[T]
    entity box(content: T)
    operation zeroLike(b: Box) -> T =
      match b
        case box(_) -> hzero()
  end

  operation run() -> Int64 =
    match box(content: tag(n: 1)).zeroLike()
      case tag(v) -> v
end
"#;
    let mut interp = crate::common::interp_for(src);
    match interp.call("test.wi431.subreq.run", &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => assert_eq!(
            n, 7,
            "hzero must dispatch via the threaded instance-fact dict to tagZero even though HasZ requires MyEq (n = 7); got {n}"
        ),
        other => panic!(
            "zeroLike should dispatch hzero via the threaded instance-fact dict (no spurious arity error); got {other:?}"
        ),
    }
}

/// EVAL — REALISTIC retroactive instance through a STDLIB collection op (the
/// actual use case for instance facts): `Color` gets `Eq` retroactively via
/// `fact Eq[T = Color, eq = colorEq]` — neither `Color` nor `Eq` is modified —
/// then `List.member` (which `requires Eq[T]` and calls `eq` internally) finds a
/// `Color` in a `List[Color]`. The `Eq[T = Color]` requirement dict is built from
/// the instance fact and threaded into `member`. (`eq` takes `T`-typed args, so
/// value-directed dispatch would also resolve this — this is end-to-end
/// integration coverage of an instance fact in a real stdlib collection, not the
/// strict A2 isolation that `instance_fact_op_dispatches_via_threaded_dict`
/// provides.) `member(color 2, [color 1, color 2]) = true ⇒ 1`; a miss ⇒ `0`.
#[test]
fn instance_fact_eq_powers_list_member() {
    let src = r#"namespace test.wi431.member
  import anthill.prelude.{List, Int64, Bool, Eq}
  import anthill.prelude.List.{member}

  sort Color
    entity color(code: Int64)
  end
  operation colorEq(x: Color, y: Color) -> Bool =
    match x
      case color(a) ->
        match y
          case color(b) -> eq(a, b)
  fact Eq[T = Color, eq = colorEq]

  operation hasMatch() -> Int64 =
    if member(color(code: 2), [color(code: 1), color(code: 2)]) then 1 else 0
  operation hasNoMatch() -> Int64 =
    if member(color(code: 9), [color(code: 1), color(code: 2)]) then 1 else 0
end
"#;
    let mut interp = crate::common::interp_for(src);
    let hit = match interp.call("test.wi431.member.hasMatch", &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => n,
        other => panic!("member(color 2, [color 1, color 2]) should eval via the instance-fact Eq; got {other:?}"),
    };
    assert_eq!(hit, 1, "member must find color 2 using the instance-fact-provided colorEq");
    let miss = match interp.call("test.wi431.member.hasNoMatch", &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => n,
        other => panic!("member(color 9, …) should eval via the instance-fact Eq; got {other:?}"),
    };
    assert_eq!(miss, 0, "member must not find an absent color (colorEq distinguishes codes)");
}

/// Rule 1 (default coexists): a spec op with a DEFAULT body (`idF`, a derived op
/// like §5.4's `flatten`) stays a spec default — it needs no instance-fact
/// binding. The fact binds only the primitives `pure`/`flatMap`; `idF` is
/// covered by its default.
#[test]
fn instance_fact_spec_default_op_needs_no_binding() {
    let snippet = r#"namespace test.wi431.cps_default
  import anthill.prelude.Option

  sort CpsMonad[F[T]]
    operation pure[A](a: A) -> F[T = A]
    operation flatMap[A, B](fa: F[T = A], f: (A) -> F[T = B]) -> F[T = B]
    operation idF[A](fa: F[T = A]) -> F[T = A] = fa
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

// ── (B) op-binding SIGNATURE validation ─────────────────────────────────────

/// (B) ACCEPT: a well-typed first-order binding — `combine = tagCombine` where
/// `tagCombine : (Tag, Tag) -> Tag` exactly matches `Combiner.combine` with
/// `T := Tag` — passes signature validation (loads clean).
#[test]
fn instance_fact_well_typed_binding_passes_signature_check() {
    let snippet = r#"namespace test.wi431.sig_ok
  import anthill.prelude.Int64

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end
  operation tagCombine(x: Tag, y: Tag) -> Tag = tag(n: 1)
  fact Combiner[T = Tag, combine = tagCombine]
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        !errs.iter().any(|e| e.contains("signature")),
        "a binding whose signature matches the spec op (with T:=Tag) must load clean: {errs:?}"
    );
}

/// (B) REJECT (arity): `combine` bound to a UNARY op — the spec op takes two
/// parameters — is a loud signature error at the fact.
#[test]
fn instance_fact_binding_wrong_arity_is_loud() {
    let snippet = r#"namespace test.wi431.sig_arity
  import anthill.prelude.Int64

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end
  operation badCombine(x: Tag) -> Tag = x
  fact Combiner[T = Tag, combine = badCombine]
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        errs.iter().any(|e| e.contains("signature-incompatible") && e.contains("parameter")),
        "binding combine to a unary op (spec takes 2) must be a loud arity error: {errs:?}"
    );
}

/// (B) REJECT (parameter type): `combine` bound to an op taking `Int64` params —
/// `T := Tag`, so the spec expects `Tag` params — is a loud signature error.
#[test]
fn instance_fact_binding_wrong_param_type_is_loud() {
    let snippet = r#"namespace test.wi431.sig_param
  import anthill.prelude.Int64

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end
  operation badParam(x: Int64, y: Int64) -> Tag = tag(n: 0)
  fact Combiner[T = Tag, combine = badParam]
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        errs.iter().any(|e| e.contains("signature-incompatible") && e.contains("parameter")),
        "binding combine to an op with Int64 params (spec expects Tag) must be loud: {errs:?}"
    );
}

/// (B) REJECT (return type): `combine` bound to an op returning `Int64` — `T :=
/// Tag`, so the spec returns `Tag` — is a loud signature error even though the
/// parameter types match (isolates the covariant return check).
#[test]
fn instance_fact_binding_wrong_return_type_is_loud() {
    let snippet = r#"namespace test.wi431.sig_return
  import anthill.prelude.Int64

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end
  operation badReturn(x: Tag, y: Tag) -> Int64 = 0
  fact Combiner[T = Tag, combine = badReturn]
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        errs.iter().any(|e| e.contains("signature-incompatible") && e.contains("return")),
        "binding combine to an op returning Int64 (spec returns Tag) must be loud: {errs:?}"
    );
}

/// (B) HIGHER-KINDED binding fails OPEN (deferred to WI-383): the §5.4 `CpsMonad`
/// instance binds `pure`/`flatMap`, whose types stay parametric after σ
/// (`F := Option` leaves `F[T = A]` ⇒ `Option[T = A]`, still containing the op's
/// own `A`). The ground gate skips them, so a well-formed HK instance loads clean
/// (no false signature error) — the HK signature check rides WI-383.
#[test]
fn instance_fact_higher_kinded_binding_signature_fails_open() {
    let snippet = r#"namespace test.wi431.sig_hk
  import anthill.prelude.Option

  sort CpsMonad[F[T]]
    operation pure[A](a: A) -> F[T = A]
    operation flatMap[A, B](fa: F[T = A], f: (A) -> F[T = B]) -> F[T = B]
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
        !errs.iter().any(|e| e.contains("signature")),
        "a well-formed higher-kinded instance binding must fail open (no signature error): {errs:?}"
    );
}

/// COHERENCE (rule 2): two instance facts covering the same (spec, carrier) with
/// DIFFERENT op bindings are a LOUD ambiguity error (design §5.4 rule 2, keyed on
/// the full canonical application / WI-419 identity). Each supplies a different
/// dictionary and there is no scoped/named instance selection yet, so before this
/// increment eval dispatch silently picked the FIRST via
/// `provider_spec_view_bindings`' first-provider-wins contract (shared with
/// WI-402/415..423 dispatch). Now `check_provider_operations` rejects it at load.
#[test]
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

/// COHERENCE (rule 2) — non-regression: the ambiguity is keyed on the full
/// canonical application, so two instance facts for the same (spec, carrier) that
/// bind the SAME op are IDENTICAL provisions (hash-consed to one `spec_view`) —
/// idempotent, not ambiguous. A crude "more than one fact for (spec, carrier)"
/// check would over-reject this; the real rule (distinct canonical applications)
/// must not.
#[test]
fn identical_instance_facts_are_idempotent_not_ambiguous() {
    let snippet = r#"namespace test.wi431.coherence_idem
  import anthill.prelude.Int64

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end
  operation tagCombine(x: Tag, y: Tag) -> Tag = tag(n: 7)

  fact Combiner[T = Tag, combine = tagCombine]
  fact Combiner[T = Tag, combine = tagCombine]
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        !errs.iter().any(|e| e.contains("ambigu") || e.contains("coheren")),
        "two IDENTICAL instance facts for (Combiner, Tag) are idempotent, not ambiguous: {errs:?}"
    );
}

/// COHERENCE (rule 2) — non-regression: the canonical-application identity must
/// be insensitive to WRITTEN FIELD ORDER. `fact Combiner[T = Tag, combine = c]`
/// and `fact Combiner[combine = c, T = Tag]` are the SAME instance — named args
/// canonicalize — so they must be idempotent, not a false ambiguity. (Guards the
/// spec_view-TermId dedup against an order-sensitive lowering.)
#[test]
fn identical_instance_facts_different_field_order_are_idempotent() {
    let snippet = r#"namespace test.wi431.coherence_order
  import anthill.prelude.Int64

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end
  operation tagCombine(x: Tag, y: Tag) -> Tag = tag(n: 7)

  fact Combiner[T = Tag, combine = tagCombine]
  fact Combiner[combine = tagCombine, T = Tag]
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        !errs.iter().any(|e| e.contains("ambigu") || e.contains("coheren")),
        "the same instance written in different field order is idempotent, not ambiguous: {errs:?}"
    );
}

/// COHERENCE (rule 2) — the ambiguity must be caught even when the two instance
/// facts live in DIFFERENT namespaces (third-party instance modules), where the
/// spec/carrier symbols are resolved in distinct import scopes and may be
/// interned under different `Symbol` copies. The grouping key canonicalizes
/// (matching the dispatch-side `provider_spec_view_bindings`), so the two still
/// collide.
#[test]
fn cross_namespace_distinct_instances_are_ambiguous() {
    let base = r#"namespace test.wi431.xbase
  import anthill.prelude.Int64
  export Combiner, Tag, combineA, combineB

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end
  operation combineA(x: Tag, y: Tag) -> Tag = tag(n: 1)
  operation combineB(x: Tag, y: Tag) -> Tag = tag(n: 2)
end
"#;
    let inst_a = r#"namespace test.wi431.xinstA
  import test.wi431.xbase.{Combiner, Tag, combineA}
  fact Combiner[T = Tag, combine = combineA]
end
"#;
    let inst_b = r#"namespace test.wi431.xinstB
  import test.wi431.xbase.{Combiner, Tag, combineB}
  fact Combiner[T = Tag, combine = combineB]
end
"#;
    let errs = load_errors(&[base, inst_a, inst_b]);
    assert!(
        errs.iter().any(|e| e.contains("ambigu") || e.contains("coheren")),
        "two instance facts for (Combiner, Tag) in different namespaces must still be a loud ambiguity: {errs:?}"
    );
}

/// COHERENCE (rule 2) — flip side of the cross-namespace case: two IDENTICAL
/// instance facts in different namespaces (same spec, carrier, and op) are the
/// same canonical application and must stay idempotent — the cross-scope
/// canonicalization must not turn copy-divergent-but-identical facts into a false
/// ambiguity.
#[test]
fn cross_namespace_identical_instances_are_idempotent() {
    let base = r#"namespace test.wi431.ybase
  import anthill.prelude.Int64
  export Combiner, Tag, tagCombine

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end
  operation tagCombine(x: Tag, y: Tag) -> Tag = tag(n: 7)
end
"#;
    let inst_a = r#"namespace test.wi431.yinstA
  import test.wi431.ybase.{Combiner, Tag, tagCombine}
  fact Combiner[T = Tag, combine = tagCombine]
end
"#;
    let inst_b = r#"namespace test.wi431.yinstB
  import test.wi431.ybase.{Combiner, Tag, tagCombine}
  fact Combiner[T = Tag, combine = tagCombine]
end
"#;
    let errs = load_errors(&[base, inst_a, inst_b]);
    assert!(
        !errs.iter().any(|e| e.contains("ambigu") || e.contains("coheren")),
        "identical instance facts in different namespaces are idempotent, not ambiguous: {errs:?}"
    );
}

/// COHERENCE (rule 2) — non-regression: distinct CARRIERS are independent
/// instances. `fact Combiner[T = Tag, …]` and `fact Combiner[T = Ring, …]` cover
/// different (spec, carrier) pairs, so neither collides — only same-carrier
/// op-binding conflicts are ambiguous.
#[test]
fn instance_facts_for_distinct_carriers_do_not_collide() {
    let snippet = r#"namespace test.wi431.coherence_carriers
  import anthill.prelude.Int64

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end
  sort Ring
    entity ring(n: Int64)
  end
  operation tagCombine(x: Tag, y: Tag) -> Tag = tag(n: 1)
  operation ringCombine(x: Ring, y: Ring) -> Ring = ring(n: 2)

  fact Combiner[T = Tag, combine = tagCombine]
  fact Combiner[T = Ring, combine = ringCombine]
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        !errs.iter().any(|e| e.contains("ambigu") || e.contains("coheren")),
        "instance facts for distinct carriers (Tag, Ring) must not collide: {errs:?}"
    );
}

// ── (E) carrier-derivation robustness ───────────────────────────────────────

/// (E) The carrier is derived from the spec's FIRST TYPE PARAMETER, matched by
/// NAME among the bindings — not `named_terms.first()`. Named args canonicalize by
/// SYMBOL INDEX (declaration order), and a POSITIONAL carrier is translated and
/// appended AFTER the named bindings, so in `fact Combiner[Tag, combine =
/// tagCombine]` (positional carrier `Tag`, named op `combine`) the first canonical
/// binding is `combine = tagCombine`. The pre-(E) `named_terms.first()` heuristic
/// then derived the carrier from the OP value `tagCombine` —
/// `fact_value_to_sort_sym` returns the symbol of a `Ref`/`Ident` WITHOUT checking
/// it is a Sort — filing the provision under `SortProvidesInfo(carrier =
/// tagCombine, …)` instead of `Tag`. A `combine(tag, tag)` call then value-directs
/// to carrier `Tag`, looks up `SortProvidesInfo(Tag, Combiner)`, finds nothing
/// (the provision is under `tagCombine`), and dies `UnknownOperation`. Deriving
/// the carrier from `Combiner`'s first type param `T` (matched by name) finds the
/// `Tag` binding regardless of order; result `99` ⇒ `tagCombine` ran.
#[test]
fn instance_fact_carrier_param_after_op_resolves_and_dispatches() {
    let src = r#"namespace test.wi431.carrier_order
  import anthill.prelude.Int64
  import test.wi431.carrier_order.Combiner.{combine}

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end
  operation tagCombine(x: Tag, y: Tag) -> Tag = tag(n: 99)
  fact Combiner[Tag, combine = tagCombine]

  operation runCombine() -> Int64 =
    match combine(tag(n: 1), tag(n: 2))
      case tag(v) -> v
end
"#;
    let mut interp = crate::common::interp_for(src);
    match interp.call("test.wi431.carrier_order.runCombine", &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => assert_eq!(
            n, 99,
            "combine must dispatch to the instance-fact-bound tagCombine even though the carrier \
             `Tag` was written POSITIONALLY (canonically ordered after the `combine` binding) \
             (n = 99); got {n}"
        ),
        other => panic!(
            "combine(tag, tag) should dispatch via the instance fact whose carrier binding is not \
             first in canonical order; got {other:?}"
        ),
    }
}

/// (E, LOUD) An op-bearing instance fact whose carrier cannot be derived — the
/// carrier type parameter `T` is simply not bound — is a LOUD load error, not a
/// silent drop. Pre-(E) the `named_terms.first()` heuristic picked the only
/// binding (`combine = tagCombine`, an Operation), `fact_value_to_sort_sym`
/// returned `None`, and the loader returned early WITHOUT emitting the provision
/// or any diagnostic — so a fact that forgot its carrier loaded clean and the
/// instance silently did not exist (coverage/coherence/signature never ran).
#[test]
fn instance_fact_unresolvable_carrier_is_loud() {
    let snippet = r#"namespace test.wi431.no_carrier
  import anthill.prelude.Int64

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end
  operation tagCombine(x: Tag, y: Tag) -> Tag = tag(n: 1)
  fact Combiner[combine = tagCombine]
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        errs.iter().any(|e| e.contains("carrier")),
        "an op-bearing instance fact whose carrier param is unbound must be a loud \
         carrier-derivation error, not a silent drop: {errs:?}"
    );
}

/// (E) non-regression: a TYPE-ONLY provider fact (no op binding) whose carrier
/// param is unbound keeps the lenient path — it is not an instance fact, so the
/// loud carrier check does not fire. (`fact BulkStore` / bare provider facts rely
/// on this; here a parametric type-only `fact Holder` with no binding must not
/// newly error.)
#[test]
fn type_only_fact_unbound_carrier_stays_lenient() {
    let snippet = r#"namespace test.wi431.type_only
  import anthill.prelude.Int64

  sort Holder
    sort T = ?
    operation hold(x: T) -> T = x
  end

  fact Holder
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        !errs.iter().any(|e| e.contains("carrier")),
        "a bare type-only provider fact (no op binding) must not trigger the loud carrier \
         check: {errs:?}"
    );
}
