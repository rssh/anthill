//! Per-predicate translation policy lookup (proposal 030 phase δ).

mod common;

use std::collections::BTreeSet;

use anthill_smt_gen::policy::{policy_for, PredicatePolicy};

#[test]
fn no_explicit_policy_no_cites_inlines() {
    let kb = common::load_kb_with(r#"
        namespace test.policy.inline
          export foo
          rule foo(?x) :- gte(?x, 0)
        end
    "#);
    let cited: BTreeSet<String> = BTreeSet::new();
    assert_eq!(
        policy_for(&kb, "test.policy.inline.foo", "smt-z3", &cited),
        PredicatePolicy::Inline,
        "predicate with no explicit policy and no cite-side use must default to Inline"
    );
}

#[test]
fn no_explicit_policy_with_cite_lifts_axiom() {
    let kb = common::load_kb_with(r#"
        namespace test.policy.lifted
          export foo
          rule foo(?x) :- gte(?x, 0) -: gte(?x, 0)
        end
    "#);
    let cited: BTreeSet<String> = std::iter::once(
        "test.policy.lifted.foo".to_string()
    ).collect();
    assert_eq!(
        policy_for(&kb, "test.policy.lifted.foo", "smt-z3", &cited),
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
          export bar

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
        policy_for(&kb, "test.policy.explicit.bar", "smt-z3", &cited),
        PredicatePolicy::DeclareFun,
        "explicit TranslationPolicy fact must override the Inline default"
    );
}
