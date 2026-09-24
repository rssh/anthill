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
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();

    state_hash(&kb, &visited)
}

const BASE_SRC: &str = r#"
    namespace test.cache
      import anthill.prelude.PartialEq.{eq}
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
    let visited: BTreeSet<String> = std::iter::once("test.cache.proof_a".to_string()).collect();
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
    let visited: BTreeSet<String> = std::iter::once("test.cache.proof_a".to_string()).collect();
    let h = state_hash(&kb, &visited);
    // The hash is purely a function of (kb, visited) — re-call yields
    // the same digest, and the helper has no other inputs to depend on.
    assert_eq!(h, state_hash(&kb, &visited));
}

/// A bodied operation, visited on its own — as the emitter records an operation
/// a proof called. No visited RULE here: a rule calling `f` would reference `eq`,
/// and `f`'s defining `eq` fact would then carry the body change into the hash by
/// itself, so the op-body test below would pass without the code it tests.
const OP_SRC: &str = r#"
    namespace test.cache.op
      operation f(x: Int64) -> Int64 = x + 1
    end
"#;

fn op_visited() -> BTreeSet<String> {
    std::iter::once("test.cache.op.f".to_string()).collect()
}

/// A visited operation's BODY is part of the slice: a proof that went through
/// `f` depends on what `f` computes. Fails without the `op_body_node` arm of
/// `walk_visited` — a loaded op has no clauses under its own functor, so the
/// two hashes were equal.
#[test]
fn changes_on_visited_operation_body_change() {
    let modified = OP_SRC.replace("= x + 1", "= x + 2");
    assert_ne!(OP_SRC, modified);
    let kb1 = common::load_kb_with(OP_SRC);
    let kb2 = common::load_kb_with(&modified);
    assert_ne!(
        state_hash(&kb1, &op_visited()),
        state_hash(&kb2, &op_visited())
    );
}

/// The hash covers the KB AS LOADED. `anthill prove` synthesizes a defining
/// rule under a bodied operation's own functor when a proof calls it
/// (WI-669/687), so a later record of the same run saw a clause under `f` that
/// the freshly loaded KB `anthill check` hashes does not have — every such
/// record read as stale (measured: 9 of lf1's 14 proofs). Fails without the
/// `is_loaded_rule` filter in `walk_visited`.
#[test]
fn ignores_a_defining_rule_synthesized_after_load() {
    let mut kb = common::load_kb_with(OP_SRC);
    let before = state_hash(&kb, &op_visited());

    let f = kb.try_resolve_symbol("test.cache.op.f").expect("f resolves");
    let rid = kb
        .synthesize_op_defining_rule(f)
        .expect("f's body yields a defining rule");
    assert!(
        kb.rules_by_functor(f).contains(&rid),
        "the synthesized rule sits under `f`, where the walk looks"
    );

    assert_eq!(before, state_hash(&kb, &op_visited()));
}

/// A LABELED rule's clause sits under its head's functor (`gte`), not under its
/// label — a cited `-:` lemma is the common case. Found the way `using` finds
/// it, label first. Fails when the walk looks up by functor only: the label
/// owns no clauses there, so the edit went unseen.
#[test]
fn changes_on_labeled_rule_body_change() {
    let src = r#"
        namespace test.cache.labeled
          import anthill.prelude.PartialOrd.{gte}
          rule lemma: gte(?x, 3.0) :- gte(?x, 5.0)
        end
    "#;
    let modified = src.replace("gte(?x, 5.0)", "gte(?x, 6.0)");
    assert_ne!(src, modified);
    let visited: BTreeSet<String> =
        std::iter::once("test.cache.labeled.lemma".to_string()).collect();
    assert_ne!(
        state_hash(&common::load_kb_with(src), &visited),
        state_hash(&common::load_kb_with(&modified), &visited)
    );
}
