//! WI-781 — `TranslationPolicy` facts actually drive lowering.
//!
//! `policy_for` had NO production caller before this: the facts parsed and
//! loaded, and `policy_test.rs` exercised the lookup, but nothing consulted it
//! at emission time — so a policy fact changed nothing, and the WI-772
//! bodied-policy refusal was unreachable outside unit tests. The prove driver's
//! `render_cited_lemmas` now routes every cite through
//! `render_cited_lemma_under_policy`. This closes proposal 030 §δ.4.
//!
//! NO z3 GUARD, deliberately. Every test here runs `--dry-run`, which prints the
//! emitted SMT and returns before the solver is invoked, and the cited lemma is
//! discharged `by trust` rather than by a solver — so the whole cite path is
//! reachable with no z3 on PATH. The sibling `prove_*` tests open with
//! `if !z3_available() { return; }`, which passes VACUOUSLY where z3 is absent;
//! a test whose subject is "the emitted document changed" must not be able to do
//! that.

mod common;
use common::{anthill, write_temp, Output};

/// The cited lemma is discharged `by trust` on purpose. The cite gate
/// (`cite_status`) refuses an undischarged cite before any policy is consulted,
/// and under `--dry-run` a `by z3` lemma returns `Skipped`, never Discharged —
/// so a solver-proved lemma would make every test here fail on the gate instead
/// of reaching the policy dispatch. Trust discharges without a solver and the
/// cite resolves as `Trusted`, which lifts.
fn fixture(extra_import: &str, policy_decl: &str) -> String {
    format!(
        r#"
namespace test.wi781.dispatch
  {extra_import}

  rule bound_d: gte(?x, 3.0)
    :- gte(?x, 5.0)

  rule target_violation: ⊥
    :- gte(?x, 5.0),
       lt(?x, 3.0)

  {policy_decl}

  proof bound_d
    by trust(reason: "WI-781 fixture: keeps the cite path solver-free")
  end

  proof target_violation
    using bound_d
    by z3(logic: "LRA")
  end
end
"#
    )
}

fn prove_dry_run(name: &str, src: &str) -> Output {
    let path = write_temp(&format!("{name}.anthill"), src);
    anthill(&["prove", path.to_str().unwrap(), "--dry-run", "--no-cache"])
}

/// The lifted hypothesis as it appears in the emitted document. Asserted as the
/// whole clause rather than on the word `forall`, so the test pins WHICH clause
/// is spliced — the lemma's premise ⇒ conclusion — not merely that some
/// quantifier survived.
const LIFTED_HYPOTHESIS: &str = "(assert (forall ((var_0 Real)) (=> (>= var_0 5.0) (>= var_0 3.0))))";

/// CONTROL. With no policy fact the cite defaults to `LiftedAxiom`, so the
/// document is exactly what it was before WI-781. Without this, the Inline test
/// below could pass against a build that had simply stopped emitting cites at
/// all.
#[test]
fn default_policy_still_splices_the_lifted_hypothesis() {
    let out = prove_dry_run("default", &fixture("", ""));
    assert!(
        out.stdout.contains(LIFTED_HYPOTHESIS),
        "a cite with no policy fact must lift as before; got:\n{}",
        out.stdout
    );
}

/// THE ACCEPTANCE: an explicit `TranslationPolicy` fact observably changes the
/// emitted SMT. Why `Inline` splices nothing, and why dropping a hypothesis is
/// the safe direction, is argued once on the arm itself
/// (`policy::render_cited_lemma_under_policy`).
#[test]
fn explicit_inline_policy_drops_the_hypothesis_from_the_document() {
    let out = prove_dry_run(
        "inline",
        &fixture(
            "import anthill.realization.policy.{TranslationPolicy, Inline}",
            r#"fact TranslationPolicy(
    predicate: "test.wi781.dispatch.bound_d",
    backend: "smt-z3",
    policy: Inline()
  )"#,
        ),
    );
    assert!(
        !out.stdout.contains(LIFTED_HYPOTHESIS),
        "an Inline policy must remove the lifted hypothesis; got:\n{}",
        out.stdout
    );
    // The proof still EMITS — Inline changes the document, it does not fail the
    // proof. Pinning this separates "policy applied" from "emission broke",
    // which a bare absence check cannot tell apart.
    assert!(
        out.stdout.contains("(assert (>= var_0 5.0))"),
        "the target's own body assertions must still be emitted; got:\n{}",
        out.stdout
    );
}

/// The backend field is matched, not ignored.
///
/// The ONLY test that can catch the `--solver` trap `SMT_Z3_BACKEND` documents:
/// it drives the real driver, so it sees which backend string the dispatch
/// actually passes. The smt-gen twin hands the constant in as an argument and so
/// cannot. Had the driver passed its `--solver` value (`z3`) instead, every
/// lookup would have silently missed and the feature would have shipped inert.
#[test]
fn a_policy_for_another_backend_does_not_apply() {
    let out = prove_dry_run(
        "other_backend",
        &fixture(
            "import anthill.realization.policy.{TranslationPolicy, Inline}",
            r#"fact TranslationPolicy(
    predicate: "test.wi781.dispatch.bound_d",
    backend: "lean",
    policy: Inline()
  )"#,
        ),
    );
    assert!(
        out.stdout.contains(LIFTED_HYPOTHESIS),
        "a `lean` policy must not steer the smt-z3 emitter; got:\n{}",
        out.stdout
    );
}

/// `DeclareFun` has no emitter. Refused loudly rather than falling back to the
/// lift, which would discharge the proof under a policy the author did not ask
/// for — a silent substitution in the one place the project's soundness story
/// says the policy is decided once and applied everywhere.
#[test]
fn an_unimplemented_policy_is_refused_loudly() {
    let out = prove_dry_run(
        "declare_fun",
        &fixture(
            "import anthill.realization.policy.{TranslationPolicy, DeclareFun}",
            r#"fact TranslationPolicy(
    predicate: "test.wi781.dispatch.bound_d",
    backend: "smt-z3",
    policy: DeclareFun()
  )"#,
        ),
    );
    assert!(
        out.has_diagnostic("error:", "DeclareFun"),
        "the refusal must name the policy it cannot lower; stderr:\n{}",
        out.stderr
    );
    assert!(
        out.has_diagnostic("error:", "does not implement yet"),
        "the refusal must say it is unimplemented, not that the proof is false; \
         stderr:\n{}",
        out.stderr
    );
    assert!(
        out.stdout.contains("1 failed"),
        "an unlowerable policy must FAIL the proof, not skip it; stdout:\n{}",
        out.stdout
    );
    assert_eq!(out.code, 1, "prove must exit nonzero when a proof fails");
}

/// THE SECOND ACCEPTANCE: the WI-772 bodied-policy refusal now reaches the CLI.
/// It was previously unreachable outside `policy_test.rs` — the reader it guards
/// had no production caller, so the guard could not fire in a real run no matter
/// what a project declared.
///
/// A guarded policy is refused because this reader head-matches facts and never
/// evaluates the body, so honouring it would silently apply the per-backend
/// DEFAULT while the source says the policy is conditional.
#[test]
fn a_bodied_policy_rule_is_refused_through_the_prove_error_channel() {
    let out = prove_dry_run(
        "bodied",
        &fixture(
            "import anthill.realization.policy.{TranslationPolicy, Inline}",
            r#"rule TranslationPolicy(
    predicate: "test.wi781.dispatch.bound_d",
    backend: "smt-z3",
    policy: Inline()
  ) :- enabled()"#,
        ),
    );
    assert!(
        out.has_diagnostic("error:", "bodied TranslationPolicy rule refused"),
        "the bodied refusal must surface as a prove error; stderr:\n{}",
        out.stderr
    );
    assert!(
        out.has_diagnostic("error:", "enabled"),
        "the refusal must name the offending rule's guard; stderr:\n{}",
        out.stderr
    );
    assert!(
        out.stdout.contains("1 failed"),
        "a bodied policy must FAIL the citing proof; stdout:\n{}",
        out.stdout
    );
    assert_eq!(out.code, 1, "prove must exit nonzero when a proof fails");
}
