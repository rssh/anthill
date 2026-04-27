//! Cache-key correctness tests (WI-096).
//!
//! Pin: a change to ANY transitively-consulted rule body or fact MUST
//! change the cache key. Canonical scenario from the design doc:
//! proof_a → {b, c, d} → {d_a, d_b}; editing d_b at depth 2 must
//! invalidate proof_a's key.

mod common;

use std::collections::BTreeSet;

use anthill_smt_gen::cache::{build_key, KeyInputs};

fn key_for(src: &str) -> String {
    let kb = common::load_kb_with(src);
    let visited: BTreeSet<String> = [
        "test.cache.proof_a",
        "test.cache.b",
        "test.cache.c",
        "test.cache.d",
        "test.cache.d_a",
        "test.cache.d_b",
    ].iter().map(|s| s.to_string()).collect();

    build_key(&kb, &KeyInputs {
        emitted_smt_lib: "(set-logic LRA)\n(check-sat)\n",
        tactic_canon: "smt(logic: \"LRA\")",
        hint_qns: &[],
        visited_rules: &visited,
        stdlib_version: "test-stdlib-v0",
        z3_version: "Z3 version 4.13.0",
    })
}

const BASE_SRC: &str = r#"
    namespace test.cache
      export proof_a, b, c, d, d_a, d_b
      rule proof_a(?r) :- b(?r), c(?r), d(?r)
      rule b(?r)       :- eq(?r, 1)
      rule c(?r)       :- eq(?r, 2)
      rule d(?r)       :- d_a(?r), d_b(?r)
      rule d_a(?r)     :- eq(?r, 10)
      rule d_b(?r)     :- eq(?r, 20)
    end
"#;

#[test]
fn key_stable_under_no_change() {
    assert_eq!(key_for(BASE_SRC), key_for(BASE_SRC));
}

#[test]
fn key_changes_on_direct_dep_body_change() {
    let modified = BASE_SRC.replace(
        "rule b(?r)       :- eq(?r, 1)",
        "rule b(?r)       :- eq(?r, 99)",
    );
    assert_ne!(BASE_SRC, modified);
    assert_ne!(key_for(BASE_SRC), key_for(&modified));
}

#[test]
fn key_changes_on_transitive_dep_body_change() {
    // Headline scenario: d_b is two hops from proof_a (proof_a → d → d_b).
    // Without content-hashed transitive walk, this would silently hit cache.
    let modified = BASE_SRC.replace(
        "rule d_b(?r)     :- eq(?r, 20)",
        "rule d_b(?r)     :- eq(?r, 21)",
    );
    assert_ne!(BASE_SRC, modified);
    assert_ne!(key_for(BASE_SRC), key_for(&modified));
}

#[test]
fn key_changes_on_referenced_fact_change() {
    let with_fact = format!(
        "{BASE_SRC}\n    namespace test.cache_facts\n      export Cfg\n      \
         entity Cfg(scale: Int)\n      fact Cfg(scale: 5)\n    end\n"
    );
    let modified = with_fact.replace("fact Cfg(scale: 5)", "fact Cfg(scale: 6)");

    // proof_a must reference Cfg for the fact to land in the dep set.
    let with_ref = with_fact.replace(
        "rule proof_a(?r) :- b(?r), c(?r), d(?r)",
        "rule proof_a(?r) :- b(?r), c(?r), d(?r), Cfg(scale: ?_s)",
    );
    let mod_with_ref = modified.replace(
        "rule proof_a(?r) :- b(?r), c(?r), d(?r)",
        "rule proof_a(?r) :- b(?r), c(?r), d(?r), Cfg(scale: ?_s)",
    );

    let kb1 = common::load_kb_with(&with_ref);
    let kb2 = common::load_kb_with(&mod_with_ref);
    let visited: BTreeSet<String> =
        std::iter::once("test.cache.proof_a".to_string()).collect();
    let inputs = KeyInputs {
        emitted_smt_lib: "(set-logic LRA)\n(check-sat)\n",
        tactic_canon: "smt(logic: \"LRA\")",
        hint_qns: &[],
        visited_rules: &visited,
        stdlib_version: "test-stdlib-v0",
        z3_version: "Z3 version 4.13.0",
    };
    assert_ne!(build_key(&kb1, &inputs), build_key(&kb2, &inputs));
}

#[test]
fn key_changes_on_smt_lib_change() {
    let kb = common::load_kb_with(BASE_SRC);
    let visited: BTreeSet<String> = std::iter::once("test.cache.proof_a".to_string()).collect();
    let mk = |smt: &str| {
        build_key(&kb, &KeyInputs {
            emitted_smt_lib: smt,
            tactic_canon: "smt(logic: \"LRA\")",
            hint_qns: &[],
            visited_rules: &visited,
            stdlib_version: "v0",
            z3_version: "Z3 version 4.13.0",
        })
    };
    assert_ne!(mk("(check-sat)\n"), mk("(check-sat)\n; comment\n"));
}

#[test]
fn key_changes_on_z3_version() {
    let kb = common::load_kb_with(BASE_SRC);
    let visited: BTreeSet<String> = std::iter::once("test.cache.proof_a".to_string()).collect();
    let mk = |v: &str| {
        build_key(&kb, &KeyInputs {
            emitted_smt_lib: "(check-sat)\n",
            tactic_canon: "smt",
            hint_qns: &[],
            visited_rules: &visited,
            stdlib_version: "v0",
            z3_version: v,
        })
    };
    assert_ne!(mk("Z3 version 4.13.0"), mk("Z3 version 4.14.0"));
}
