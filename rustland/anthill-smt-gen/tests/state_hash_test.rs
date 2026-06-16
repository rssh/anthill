//! `state_hash` correctness tests (proposal 030 phase α.4).
//!
//! Pin: a change to ANY transitively-consulted rule body or referenced
//! fact MUST change the state hash. Mirrors `cache_key_test.rs` but
//! exercises only the kb-state-slice envelope — no SMT document, no
//! tactic, no solver-version. Two proofs over the same kb slice produce
//! the same state hash regardless of which tactic discharged them.

mod common;

use std::collections::BTreeSet;

use anthill_smt_gen::cache::state_hash;

fn hash_for(src: &str) -> String {
    let kb = common::load_kb_with(src);
    let visited: BTreeSet<String> = [
        "test.cache.proof_a",
        "test.cache.b",
        "test.cache.c",
        "test.cache.d",
        "test.cache.d_a",
        "test.cache.d_b",
    ].iter().map(|s| s.to_string()).collect();

    state_hash(&kb, &visited)
}

const BASE_SRC: &str = r#"
    namespace test.cache
      rule proof_a(?r) :- b(?r), c(?r), d(?r)
      rule b(?r)       :- eq(?r, 1)
      rule c(?r)       :- eq(?r, 2)
      rule d(?r)       :- d_a(?r), d_b(?r)
      rule d_a(?r)     :- eq(?r, 10)
      rule d_b(?r)     :- eq(?r, 20)
    end
"#;

#[test]
fn stable_under_no_change() {
    assert_eq!(hash_for(BASE_SRC), hash_for(BASE_SRC));
}

#[test]
fn changes_on_direct_dep_body_change() {
    let modified = BASE_SRC.replace(
        "rule b(?r)       :- eq(?r, 1)",
        "rule b(?r)       :- eq(?r, 99)",
    );
    assert_ne!(BASE_SRC, modified);
    assert_ne!(hash_for(BASE_SRC), hash_for(&modified));
}

#[test]
fn changes_on_transitive_dep_body_change() {
    // Headline: d_b is two hops from proof_a (proof_a → d → d_b).
    let modified = BASE_SRC.replace(
        "rule d_b(?r)     :- eq(?r, 20)",
        "rule d_b(?r)     :- eq(?r, 21)",
    );
    assert_ne!(BASE_SRC, modified);
    assert_ne!(hash_for(BASE_SRC), hash_for(&modified));
}

#[test]
fn changes_on_referenced_fact_change() {
    let with_fact = format!(
        "{BASE_SRC}\n    namespace test.cache_facts\n      \
         entity Cfg(scale: Int64)\n      fact Cfg(scale: 5)\n    end\n"
    );
    let modified = with_fact.replace("fact Cfg(scale: 5)", "fact Cfg(scale: 6)");

    let with_ref = with_fact.replace(
        "rule proof_a(?r) :- b(?r), c(?r), d(?r)",
        "rule proof_a(?r) :- b(?r), c(?r), d(?r), test.cache_facts.Cfg(scale: ?_s)",
    );
    let mod_with_ref = modified.replace(
        "rule proof_a(?r) :- b(?r), c(?r), d(?r)",
        "rule proof_a(?r) :- b(?r), c(?r), d(?r), test.cache_facts.Cfg(scale: ?_s)",
    );

    let kb1 = common::load_kb_with(&with_ref);
    let kb2 = common::load_kb_with(&mod_with_ref);
    let visited: BTreeSet<String> =
        std::iter::once("test.cache.proof_a".to_string()).collect();
    assert_ne!(state_hash(&kb1, &visited), state_hash(&kb2, &visited));
}

#[test]
fn ignores_smt_document_and_tactic() {
    // Different SMT documents and tactics must NOT affect the state
    // hash — that's its whole point vs build_key. Two discharges of
    // the same proof under different solver invocations should yield
    // the same state hash so the registry can recognise "same kb
    // state, different tactic" without re-discharging.
    let kb = common::load_kb_with(BASE_SRC);
    let visited: BTreeSet<String> =
        std::iter::once("test.cache.proof_a".to_string()).collect();
    let h = state_hash(&kb, &visited);
    // The hash is purely a function of (kb, visited) — re-call yields
    // the same digest, and the helper has no other inputs to depend on.
    assert_eq!(h, state_hash(&kb, &visited));
}
