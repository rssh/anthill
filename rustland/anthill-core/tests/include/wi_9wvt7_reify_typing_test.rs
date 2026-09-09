//! WI-20260908-9WVT7 / proposal 027.4 — the two typer fixes that let an effect-layer
//! `reify` be DECLARED and CALLED.
//!
//! 027.4 gives `Error` the operation `reify[Rho, X, T1](body: () -> X @ {Error[T1], Rho})
//! -> Result[E = T1, T = X] effects {Rho}` — 047 §3's reify at `M = Result`. Neither half
//! of that signature loaded before this ticket, for two unrelated reasons, and this file
//! drives both plus the controls that say the repairs are not vacuous.
//!
//! FIX (a) — DEEP-RESOLVE A CALLBACK ROW'S LABELS. `validate_callback_effect_row` compared
//! the declared and actual labels through `walk_value_to_resolved`, which chases a
//! TOP-LEVEL variable chain and does not descend into an `Fn`'s arguments. So a declared
//! `Error[T = ?P]` was compared UNRESOLVED against an actual `Error[T = Boom]` and reported
//! as "a closed row … does not admit", even though argument unification had already bound
//! `?P := Boom` (measured by instrumenting the comparison: the label's `T` child chased to
//! the actual's `Boom` TermId while the label itself did not). The repair walks both label
//! lists with `walk_type_deep_value`.
//!
//! FIX (b) — DO NOT DEMAND A `requires` FOR A SPEC PARAMETER NOTHING DISPATCHES ON. A sort
//! with an abstract type parameter is a SPEC sort, so WI-325 requires a covering `requires`
//! when a spec-op call leaves one of the sort's parameters abstract. That loop walked EVERY
//! parameter of the spec sort without asking whether the operation being called uses it.
//! `reify[Rho, X, T1]` names `Error.T` nowhere — not a parameter, not the return, not the
//! effect row — so nothing can dispatch on it and no witness could supply it, yet it was
//! flagged abstract. Whether the flag became a diagnostic was then decided by
//! `spec_warrants_abstract_check`'s NAMESPACE leg, so byte-identical source loaded under
//! `anthill.*` and was refused outside it. The repair skips a parameter the signature
//! neither mentions nor receives.
//!
//! WHAT FAILS UNDER WHICH BACK-OUT — MEASURED, each fix neutralised alone:
//!
//!   * back out (a) → `a_callback_row_label_resolves_its_type_argument` and
//!     `the_deep_resolve_is_not_error_specific` fail with
//!     "callback effects admitted by parameter `body` … (a closed row)";
//!     `an_unused_spec_parameter_demands_no_requires` still PASSES.
//!   * back out (b) → `an_unused_spec_parameter_demands_no_requires` and
//!     `a_callback_row_label_resolves_its_type_argument` fail with
//!     "missing `requires Err2[T = …]` on enclosing sort";
//!     `the_deep_resolve_is_not_error_specific` still passes.
//!
//! `a_callback_row_label_resolves_its_type_argument` therefore fails under EITHER back-out
//! — its program needs both repairs — so it does not separate them. The two that do are
//! `the_deep_resolve_is_not_error_specific` (fix (a) alone: a `Permission[C]` label with no
//! spec-member call in sight) and `an_unused_spec_parameter_demands_no_requires` (fix (b)
//! alone: a CONCRETE label `Err2[Boom]`, which needs no deep resolve, on an operation that
//! still never mentions `Err2.T`). Written that way deliberately — a suite where every row
//! reds under both changes cannot say which change it is measuring.
//!
//! PASS EITHER WAY BY DESIGN, and each is here because it is what makes its repair
//! non-vacuous rather than a blanket loosening:
//!
//!   * `an_abstract_carrier_param_still_demands_a_requires` (below) is the only row here
//!     that survives both back-outs.
//!   * `an_abstract_carrier_param_still_demands_a_requires` — (b)'s first attempt tested
//!     `occurs_in_view` on the parameter's alias VAR, which missed the SYMBOL spelling a
//!     declared parameter type uses (`Ref(MySpec.T)`); this row went RED under it, which is
//!     why the shipped predicate is `type_mentions_spec_param`.
//!
//! The third control for (b) is NOT duplicated here: a self-receiver spec carries its
//! sort's parameters even when the signature never writes them, and
//! `wi325_missing_requires_test::user_defined_self_receiver_spec_without_providers_errors_on_abstract_call`
//! already pins it. That row went RED under a version of (b) lacking the `!has_receiver`
//! conjunct — which is why the conjunct is there.

/// `common::try_load_kb_with` and NOT a hand-rolled parse/load recipe: it reads the
/// stdlib through the shared `STDLIB_PARSED` LazyLock, so these seven fixtures cost one
/// stdlib parse between them instead of one each.
#[track_caller]
fn expect_load(src: &str, what: &str) {
    if let Err(errs) = crate::common::try_load_kb_with(src) {
        panic!("expected {what} to load, got:\n{}", errs.join("\n"));
    }
}

#[track_caller]
fn expect_reject(src: &str, wants: &[&str], what: &str) {
    match crate::common::try_load_kb_with(src) {
        Ok(_) => panic!("expected {what} to be REJECTED, but it loaded"),
        Err(errs) => {
            let joined = errs.join("\n");
            for want in wants {
                assert!(
                    joined.contains(want),
                    "expected the rejection of {what} to mention {want:?}, got:\n{joined}"
                );
            }
        }
    }
}

/// The 027.4 shape, in a USER namespace — which is the point of fix (b): the same source
/// under `anthill.*` loaded before this ticket and outside it did not. `Err2` rather than
/// `Error` because the prelude's `Error` has no `reify` yet (that is 027.4's build-path
/// step 4); the typing question is identical and this file must not depend on the stdlib
/// growing the operation first.
fn reify_fixture(caller: &str) -> String {
    format!(
        r#"
namespace test.wi9wvt7
  import anthill.prelude.{{Int64, String, Nothing, Effect}}

  enum Result
    sort E = ?
    sort T = ?
    entity ok(value: T)
    entity err(error: E)
  end

  sort Boom
    entity boom(why: String)
  end

  sort Other
    entity other(k: Int64)
  end

  sort Err2
    import anthill.prelude.{{Nothing, Effect}}
    import test.wi9wvt7.{{Result}}
    sort T = ?
    operation raise(error: T) -> Nothing effects Err2[T]
    operation reify[Rho, X, T1](body: () -> X @ {{Err2[T1], Rho}}) -> Result[E = T1, T = X]
      effects {{Rho}}
    provides Effect[T = Err2]
  end

  operation may_fail(n: Int64) -> Int64 effects {{Err2[Boom]}} = 41

{caller}
end
"#
    )
}

// ── Fix (a): a callback row's label resolves its type ARGUMENT ────────────────────

/// THE ARM FOR (a). The declared label `Err2[T1]` and the actual `Err2[T = Boom]` conform
/// once `?T1` is resolved through σ — which is what the deep walk added. FAILS when (a) is
/// backed out, with the closed-row diagnostic.
#[test]
fn a_callback_row_label_resolves_its_type_argument() {
    expect_load(
        &reify_fixture(
            "  operation c(n: Int64) -> Result[E = Boom, T = Int64] =\n    \
             Err2.reify(lambda () -> may_fail(n))",
        ),
        "a reify whose callback row carries a type-parameter payload",
    );
}

/// NON-VACUITY CONTROL for (a), and it does NOT survive (a)'s back-out — measured, and
/// stated here because an earlier draft of this file claimed it did. Its assertion tokens
/// are produced by the RETURN-TYPE mismatch, which is only reached once (a) lets the
/// callback check pass; under back-out (a) the sole error is the closed-row diagnostic and
/// this row reds. What it still buys is the thing a back-out cannot show: that (a) is not
/// "stop comparing". A repair that merely dropped the check would make the arm above pass
/// too, and would make THIS row pass as a clean load — so the row separates "resolves the
/// label" from "ignores the label", which is the only way (a) could have been wrong in the
/// green direction.
#[test]
fn a_wrong_payload_annotation_is_still_refused() {
    expect_reject(
        &reify_fixture(
            "  operation c(n: Int64) -> Result[E = Other, T = Int64] =\n    \
             Err2.reify(lambda () -> may_fail(n))",
        ),
        &["E = Other", "E = Boom"],
        "a reify result annotated with a payload the body does not raise",
    );
}

/// The defect was never `Error`-specific: ANY parameterized effect label whose argument is
/// a call-site-bound type parameter was compared unresolved. `Permission` is the second
/// witness and the one that shows the repair is about row labels, not about `Error`.
/// FAILS when (a) is backed out.
#[test]
fn the_deep_resolve_is_not_error_specific() {
    expect_load(
        r#"
namespace test.wi9wvt7.perm
  import anthill.prelude.{Int64, Permission}

  sort Llm
  end

  operation acquires() -> Int64 effects {Permission[Llm]} = 1

  operation wrap[Rho, C](body: () -> Int64 @ {Permission[C], Rho}) -> Int64
    effects {Rho}

  operation caller() -> Int64 = wrap(lambda () -> acquires())
end
"#,
        "a callback row carrying `Permission[C]` at a type-parameter capability",
    );
}

// ── Fix (b): an unused spec parameter demands no `requires` ───────────────────────

/// THE ARM FOR (b), ISOLATED FROM (a). The callback row's label is CONCRETE
/// (`Err2[Boom]`), so no type argument needs resolving through σ and fix (a) is not on this
/// path — measured: with (a) neutralised this source still loads. What it does still need
/// is (b): `reifyConcrete` names `Err2.T` nowhere in its signature, so the enclosing sort's
/// parameter is not what any dispatch turns on and no `requires` could cover it. FAILS when
/// (b) is backed out, with "missing `requires Err2[T = …]` on enclosing sort".
///
/// The 027.4 signature proper (a type-parameter payload) needs BOTH repairs and is driven
/// by [`a_callback_row_label_resolves_its_type_argument`]; that test cannot separate them,
/// which is why this one exists beside it.
#[test]
fn an_unused_spec_parameter_demands_no_requires() {
    expect_load(
        r#"
namespace test.wi9wvt7.unused
  import anthill.prelude.{Int64, String, Nothing, Effect}

  enum Result
    sort E = ?
    sort T = ?
    entity ok(value: T)
    entity err(error: E)
  end

  sort Boom
    entity boom(why: String)
  end

  sort Err2
    import anthill.prelude.{Nothing, Effect}
    import test.wi9wvt7.unused.{Result, Boom}
    sort T = ?
    operation raise(error: T) -> Nothing effects Err2[T]
    operation reifyConcrete[Rho, X](body: () -> X @ {Err2[Boom], Rho}) -> Result[E = Boom, T = X]
      effects {Rho}
    provides Effect[T = Err2]
  end

  operation may_fail(n: Int64) -> Int64 effects {Err2[Boom]} = 41

  operation c(n: Int64) -> Result[E = Boom, T = Int64] =
    Err2.reifyConcrete(lambda () -> may_fail(n))
end
"#,
        "a spec-sort member whose signature never mentions the sort's type parameter",
    );
}

/// CONTROL for (b) — PASSES EITHER WAY BY DESIGN under the SHIPPED predicate, and that is
/// exactly why it is here: it went RED under (b)'s first attempt, which tested
/// `occurs_in_view` on the parameter's alias VAR. A declared parameter type names a spec
/// parameter by SYMBOL (`Ref(MySpec.T)`) as readily as by variable, so the var-only test
/// reported `same(a: T, b: T)` as not mentioning `T` and dropped WI-325's diagnostic on a
/// wholly-unimplemented spec. `type_mentions_spec_param` sees both spellings.
#[test]
fn an_abstract_carrier_param_still_demands_a_requires() {
    expect_reject(
        r#"
namespace test.wi9wvt7.spec
  import anthill.prelude.{Bool}

  sort MySpec
    import anthill.prelude.{Bool}
    sort T = ?
    operation same(a: T, b: T) -> Bool
  end

  operation use[A](x: A, y: A) -> Bool = MySpec.same(x, y)
end
"#,
        &["requires MySpec"],
        "a spec op called on an abstract carrier parameter",
    );
}

/// FIX (a) IS ONLY HALF DONE IF THE DENIED LABELS ARE LEFT UNRESOLVED. `e_absent` feeds the
/// SAME comparator as `e_present`, so resolving only the present lists would leave the
/// `-Label[Arg]` lacks-constraint reject dead exactly when the denial's argument resolves
/// through σ. MEASURED, this fixture with and without the `e_absent` walk:
///
/// | declared denial | `e_absent` resolved | not resolved |
/// |---|---|---|
/// | `-Err2[Boom]` (concrete) | lacks reject | lacks reject |
/// | `-Err2[T1]`, `T1 := Boom` via `cap` | lacks reject | NEVER REACHES THE CHECK |
///
/// In the unresolved case the label is not matched at all, so the row tail never takes its
/// residual and the call dies later on `expected a type for 'Eff'` — a denial that never
/// denied. This is WI-CBRSW's `-Permission[X]` shape (proposal 064): a denial written over
/// a capability TYPE PARAMETER is exactly what must refuse a body acquiring that capability,
/// and it is the reason the absent list is walked here rather than only the present ones.
#[test]
fn a_lacks_constraint_denies_through_a_type_parameter() {
    let fixture = |denied: &str| {
        format!(
            r#"
namespace test.wi9wvt7.lacks_{denied}
  import anthill.prelude.{{Int64, String, Effect}}

  sort Boom
    entity boom(why: String)
  end

  sort Err2
    import anthill.prelude.{{Effect}}
    sort T = ?
    provides Effect[T = Err2]
  end

  operation acquires() -> Int64 effects {{Err2[Boom]}} = 1

  operation wrap[T1, Eff](cap: T1, body: () -> Int64 @ {{Eff, -Err2[{denied}]}}) -> Int64
    effects {{Eff}}

  operation caller() -> Int64 effects {{Err2[Boom]}} =
    wrap(boom("x"), lambda () -> acquires())
end
"#
        )
    };
    // The CONTROL: a concrete denial, which fired before this ticket too.
    expect_reject(
        &fixture("Boom"),
        &["to lack `Err2[T = Boom]`"],
        "a body acquiring `Err2[Boom]` under a concrete `-Err2[Boom]` denial",
    );
    // THE ARM: the same denial written over a type parameter.
    expect_reject(
        &fixture("T1"),
        &["to lack `Err2[T = Boom]`"],
        "a body acquiring `Err2[Boom]` under a `-Err2[T1]` denial at `T1 := Boom`",
    );
}

/// WHAT FIX (b) IS FOR, asserted as the EQUIVALENCE rather than as one verdict: the same
/// program must load the same way wherever it is declared. `spec_warrants_abstract_check`
/// gates the WI-325 diagnostic on the declaring NAMESPACE (`anthill.*` versus anything
/// else) as a proxy for "is this spec host-implemented", there being no fact that
/// distinguishes a host-builtin spec with no providers from a user's unregistered one. So a
/// receiverless spec-op call on a parameter nothing dispatches on was refused outside
/// `anthill.*` and accepted inside it. MEASURED, both namespaces, before and after:
///
/// |               | user namespace | `anthill.*` |
/// |---|---|---|
/// | before (b)    | refused        | loads       |
/// | after (b)     | loads          | loads       |
///
/// The pre-existing `anthill.*` behaviour is the one this agrees with, so (b) removes an
/// inconsistency rather than opening a hole.
///
/// NOT A CLAIM THAT THE PROGRAM IS SOUND. `ping` is body-less with no provider, so it
/// cannot run: `anthill run` dies with "operation has no body". Detecting THAT is a
/// separate, missing check — and `missing requires MySpec[T = …]`, the message (b) removes
/// here, was never the right diagnostic for it: adding that clause to the enclosing sort
/// would not make `ping` runnable, because there is still no implementation. FAILS when (b)
/// is backed out — on the user-namespace half only.
#[test]
fn one_program_loads_the_same_in_both_namespaces() {
    let fixture = |ns: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Bool}}

  sort MySpec
    import anthill.prelude.{{Bool}}
    sort T = ?
    operation ping() -> Bool
  end

  operation drive() -> Bool = MySpec.ping()
end
"#
        )
    };
    expect_load(
        &fixture("test.wi9wvt7.ns_user"),
        "a receiverless spec-op call in a USER namespace",
    );
    expect_load(
        &fixture("anthill.wi9wvt7.ns_stdlib"),
        "the same call under the `anthill.*` prefix (unchanged by this ticket)",
    );
}
