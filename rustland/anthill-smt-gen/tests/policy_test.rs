//! Per-predicate translation policy — lookup and lowering dispatch
//! (proposal 030 phase δ).
//!
//! The `render_*` tests at the bottom cover WI-781's dispatch — the production
//! entry point that turns a resolved policy into emitted clauses. The lookup
//! tests above them predate it, and until WI-781 they were the ONLY thing
//! exercising this module: `policy_for` had no production caller, so the arms
//! resolved correctly and then nothing acted on them.

mod common;

use std::collections::BTreeSet;

use anthill_smt_gen::policy::{
    policy_for, render_cited_lemma_under_policy, PredicatePolicy, SMT_Z3_BACKEND,
};

#[test]
fn no_explicit_policy_no_cites_inlines() {
    let kb = common::load_kb_with(r#"
        namespace test.policy.inline
          rule foo(?x) :- gte(?x, 0)
        end
    "#);
    let cited: BTreeSet<String> = BTreeSet::new();
    assert_eq!(
        policy_for(&kb, "test.policy.inline.foo", SMT_Z3_BACKEND, &cited).expect("policy"),
        PredicatePolicy::Inline,
        "predicate with no explicit policy and no cite-side use must default to Inline"
    );
}

#[test]
fn no_explicit_policy_with_cite_lifts_axiom() {
    let kb = common::load_kb_with(r#"
        namespace test.policy.lifted
          rule foo(?x) :- gte(?x, 0)
        end
    "#);
    let cited: BTreeSet<String> = std::iter::once(
        "test.policy.lifted.foo".to_string()
    ).collect();
    assert_eq!(
        policy_for(&kb, "test.policy.lifted.foo", SMT_Z3_BACKEND, &cited).expect("policy"),
        PredicatePolicy::LiftedAxiom,
        "predicate cited via `using` must default to LiftedAxiom"
    );
}

#[test]
fn explicit_policy_overrides_default() {
    // A `fact TranslationPolicy(...)` declaration in source
    // overrides the inferred default.
    let kb = common::load_kb_with(r#"
        namespace test.policy.explicit
          import anthill.realization.policy.{TranslationPolicy, DeclareFun}

          rule bar(?x) :- gte(?x, 0)

          fact TranslationPolicy(
            predicate: "test.policy.explicit.bar",
            backend: "smt-z3",
            policy: DeclareFun
          )
        end
    "#);
    // Sanity: the schema symbol must resolve, and the source-
    // declared fact must actually land as a TranslationPolicy
    // entry in the KB.
    assert!(
        kb.try_resolve_symbol("anthill.realization.policy.TranslationPolicy").is_some(),
        "TranslationPolicy schema must be loaded from stdlib"
    );
    let cited: BTreeSet<String> = BTreeSet::new();
    assert_eq!(
        policy_for(&kb, "test.policy.explicit.bar", SMT_Z3_BACKEND, &cited).expect("policy"),
        PredicatePolicy::DeclareFun,
        "explicit TranslationPolicy fact must override the Inline default"
    );
}

/// WI-772(a): a BODIED TranslationPolicy rule must be refused loudly,
/// never silently skipped. The old reader `continue`d past non-facts,
/// so a guarded policy fell back to the per-backend default with no
/// diagnostic — the author had no hint their rule shape is unsupported.
#[test]
fn bodied_translation_policy_rule_is_refused() {
    let kb = common::load_kb_with(r#"
        namespace test.policy.bodied
          import anthill.realization.policy.{TranslationPolicy, DeclareFun}

          rule bar(?x) :- gte(?x, 0)

          rule TranslationPolicy(
            predicate: "test.policy.bodied.bar",
            backend: "smt-z3",
            policy: DeclareFun
          ) :- gte(1, 0)
        end
    "#);
    let cited: BTreeSet<String> = BTreeSet::new();
    let err = policy_for(&kb, "test.policy.bodied.bar", SMT_Z3_BACKEND, &cited)
        .expect_err("a bodied TranslationPolicy rule must be refused, not skipped");
    assert!(
        err.message.contains("bodied TranslationPolicy rule refused"),
        "refusal must state the unsupported shape, got: {}",
        err.message
    );
    assert!(
        err.message.contains(":-") && err.message.contains("gte"),
        "refusal must name the offending rule (head :- body), got: {}",
        err.message
    );
}

/// WI-772(a), order-independence: the refusal must fire even when a
/// MATCHING fact for the same (predicate, backend) key coexists with
/// the bodied rule and is asserted first. Candidates enumerate in
/// insertion (source) order, so a single-pass reader that
/// early-returns on the first matching fact would deterministically
/// never see a bodied rule written after the fact — this fixture's
/// exact shape — and the guarded policy would be silently dropped.
#[test]
fn bodied_policy_rule_is_refused_despite_matching_fact() {
    let kb = common::load_kb_with(r#"
        namespace test.policy.bodiedcoex
          import anthill.realization.policy.{TranslationPolicy, DeclareFun, Inline}

          rule bar(?x) :- gte(?x, 0)

          fact TranslationPolicy(
            predicate: "test.policy.bodiedcoex.bar",
            backend: "smt-z3",
            policy: DeclareFun
          )

          rule TranslationPolicy(
            predicate: "test.policy.bodiedcoex.bar",
            backend: "smt-z3",
            policy: Inline
          ) :- gte(1, 0)
        end
    "#);
    let cited: BTreeSet<String> = BTreeSet::new();
    let err = policy_for(&kb, "test.policy.bodiedcoex.bar", SMT_Z3_BACKEND, &cited)
        .expect_err(
            "the bodied TranslationPolicy rule must be refused even though a \
             matching fact exists — the fact winning by enumeration order \
             would silently drop the guarded policy",
        );
    assert!(
        err.message.contains("bodied TranslationPolicy rule refused"),
        "refusal must state the unsupported shape, got: {}",
        err.message
    );
}

// ── WI-781: the resolved policy drives emission ────────────────
//
// `render_cited_lemma_under_policy` is what the prove driver calls per cite.
// The CLI-level consequences (a policy fact changing the emitted document, the
// bodied refusal reaching the prove error channel) are pinned end-to-end in
// anthill-cli/tests/wi781_policy_dispatch_test.rs; these cover the arms
// directly, including the two the CLI fixture does not spell.

/// A citable lemma plus an optional policy declaration. The labeled head IS the
/// conclusion (`?x >= 5 ⇒ ?x >= 3`), which is what makes the rule citable — a
/// violation-shape rule with no conclusion is refused by the lift as uncitable,
/// and every assertion below would then be measuring the wrong refusal. Same
/// shape as `prove_using_test.rs`'s `bound_d`.
fn citable_kb(ns: &str, decl: &str) -> anthill_core::kb::KnowledgeBase {
    common::load_kb_with(&format!(
        r#"
        namespace {ns}
          import anthill.realization.policy.{{TranslationPolicy, Inline, DefineFun, DeclareFun, LiftedAxiom}}

          rule bound: gte(?x, 3.0)
            :- gte(?x, 5.0)

          {decl}
        end
    "#
    ))
}

/// The default for anything cited. Byte-identical to the pre-WI-781 path, which
/// is what makes the wiring a no-op until a policy fact says otherwise.
#[test]
fn lifted_axiom_renders_the_implication_clause() {
    let kb = citable_kb("test.render.lifted", "");
    let qn = "test.render.lifted.bound";
    let clauses =
        render_cited_lemma_under_policy(&kb, qn, SMT_Z3_BACKEND, false).expect("render");
    assert_eq!(clauses.len(), 1, "one head ⇒ one clause; got {clauses:?}");
    assert!(
        clauses[0].contains("(assert") && clauses[0].contains("=>"),
        "LiftedAxiom must render the premise ⇒ conclusion implication, got: {}",
        clauses[0]
    );
}

/// `Inline` contributes no hypothesis: the predicate symbol "disappears from the
/// emitted document" (schema), so a cite under it splices nothing. Empty is the
/// POLICY, not a skip — and it is the safe direction, since a missing hypothesis
/// can only make the goal harder to discharge.
#[test]
fn inline_renders_no_clause() {
    let kb = citable_kb(
        "test.render.inline",
        r#"fact TranslationPolicy(
            predicate: "test.render.inline.bound",
            backend: "smt-z3",
            policy: Inline
          )"#,
    );
    let qn = "test.render.inline.bound";
    let clauses =
        render_cited_lemma_under_policy(&kb, qn, SMT_Z3_BACKEND, false).expect("render");
    assert!(clauses.is_empty(), "Inline must splice nothing, got: {clauses:?}");
}

/// Neither unimplemented arm may fall back to the lift. Both are checked: a
/// dispatch that special-cased only the one its fixture used would satisfy a
/// single-arm test while leaving the other silently lifting. One KB carries
/// both policies — they key on different predicates, so they do not interact.
#[test]
fn unimplemented_arms_are_refused_not_lifted() {
    let kb = common::load_kb_with(
        r#"
        namespace test.render.unimpl
          import anthill.realization.policy.{TranslationPolicy, DefineFun, DeclareFun}

          rule defined: gte(?x, 3.0)
            :- gte(?x, 5.0)

          rule declared: gte(?x, 3.0)
            :- gte(?x, 5.0)

          fact TranslationPolicy(
            predicate: "test.render.unimpl.defined",
            backend: "smt-z3",
            policy: DefineFun
          )

          fact TranslationPolicy(
            predicate: "test.render.unimpl.declared",
            backend: "smt-z3",
            policy: DeclareFun
          )
        end
    "#,
    );
    for (rule, variant) in [("defined", "DefineFun"), ("declared", "DeclareFun")] {
        let qn = format!("test.render.unimpl.{rule}");
        let err = render_cited_lemma_under_policy(&kb, &qn, SMT_Z3_BACKEND, false)
            .expect_err(&format!("{variant} has no emitter and must be refused"));
        assert!(
            err.message.contains(variant),
            "refusal must name the policy it cannot lower, got: {}",
            err.message
        );
        assert!(
            err.message.contains("does not implement yet"),
            "refusal must read as unimplemented, not as a false proof, got: {}",
            err.message
        );
    }
}

/// `Inline` is only meaningful when the consumer actually inlines. Under
/// ABSTRACT emission the emitter short-circuits every rule call without
/// descending, so nothing is inlined anywhere and an `Inline` cite would
/// contribute nothing while looking honoured — the hypothesis simply vanishes.
///
/// This is the case the first cut of WI-781 got wrong: it returned no clause
/// unconditionally, justified by "the consumer's own emission inlines it",
/// which is false on exactly this path. Structured proofs dispatch their
/// `conclude` record with `abstract_body: true` BECAUSE they rely on the cited
/// lifts, so the silent version removed the premise those proofs rest on.
#[test]
fn inline_under_abstract_emission_is_refused() {
    let kb = citable_kb(
        "test.render.inlineabstract",
        r#"fact TranslationPolicy(
            predicate: "test.render.inlineabstract.bound",
            backend: "smt-z3",
            policy: Inline
          )"#,
    );
    let qn = "test.render.inlineabstract.bound";
    // Concrete consumer: legitimately empty.
    assert!(
        render_cited_lemma_under_policy(&kb, qn, SMT_Z3_BACKEND, false)
            .expect("concrete consumer renders")
            .is_empty(),
        "control: Inline splices nothing when the consumer can inline"
    );
    // Abstract consumer: nothing would inline it, so refuse.
    let err = render_cited_lemma_under_policy(&kb, qn, SMT_Z3_BACKEND, true)
        .expect_err("Inline under abstract emission drops the hypothesis silently");
    assert!(
        err.message.contains("emitted ABSTRACTLY"),
        "refusal must say why Inline cannot be honoured here, got: {}",
        err.message
    );
}

/// The backend is matched: a fact for another backend leaves the default in
/// place. Note this passes the constant in as an argument, so it pins the
/// MATCHING, not that the driver supplies the right string — only the CLI twin
/// (`wi781_policy_dispatch_test`) can catch that.
#[test]
fn a_policy_for_another_backend_is_not_applied() {
    let kb = citable_kb(
        "test.render.otherbackend",
        r#"fact TranslationPolicy(
            predicate: "test.render.otherbackend.bound",
            backend: "lean",
            policy: DeclareFun
          )"#,
    );
    let qn = "test.render.otherbackend.bound";
    // Would be a loud refusal if the `lean` fact applied.
    let clauses =
        render_cited_lemma_under_policy(&kb, qn, SMT_Z3_BACKEND, false).expect("render");
    assert_eq!(clauses.len(), 1, "a lean policy must not steer smt-z3; got {clauses:?}");
}

/// The constant the prove driver passes. Pinned as a literal because it is a
/// WIRE FORMAT: it must equal the `backend` string an author writes in a
/// `TranslationPolicy` fact, which the schema documents as `smt-z3`. Changing it
/// would not break a build — every lookup would just stop matching and the
/// feature would go inert, which is the state WI-781 found it in.
#[test]
fn the_z3_backend_name_is_the_documented_one() {
    assert_eq!(SMT_Z3_BACKEND, "smt-z3");
}
