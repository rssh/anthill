//! Per-predicate translation policy lookup (proposal 030 phase δ).

mod common;

use std::collections::BTreeSet;

use anthill_smt_gen::policy::{policy_for, PredicatePolicy};

#[test]
fn no_explicit_policy_no_cites_inlines() {
    let kb = common::load_kb_with(r#"
        namespace test.policy.inline
          rule foo(?x) :- gte(?x, 0)
        end
    "#);
    let cited: BTreeSet<String> = BTreeSet::new();
    assert_eq!(
        policy_for(&kb, "test.policy.inline.foo", "smt-z3", &cited).expect("policy"),
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
        policy_for(&kb, "test.policy.lifted.foo", "smt-z3", &cited).expect("policy"),
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
        policy_for(&kb, "test.policy.explicit.bar", "smt-z3", &cited).expect("policy"),
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
    let err = policy_for(&kb, "test.policy.bodied.bar", "smt-z3", &cited)
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
    let err = policy_for(&kb, "test.policy.bodiedcoex.bar", "smt-z3", &cited)
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
