//! WI-320 — `EffectsRuntime` ↔ `effects_rows` bridge fact emission.
//!
//! Pins the idempotency contract on `emit_effects_runtime_bridge_fact`.
//! The bridge is asserted from Rust during `register_prelude` because the
//! surface grammar can't carry an `effects_rows(?)` entity-construction
//! term in type-argument position (proposal 045 §2.0.1). `register_prelude`
//! is called more than once on the same KB by the common test pattern
//! (manual call + `load_all`'s internal `register_prelude` at
//! `load.rs:1482`), and `assert_rule_debruijn` does NOT consult
//! `fact_dedup` — so without the in-function guard we'd duplicate the
//! bridge rule on every re-entry. Code-review finding #1.
//!
//! These tests pin both directions: the bridge IS installed after one
//! call (so consumers can rely on it), and it is NOT duplicated after N
//! calls (so a re-entry doesn't inflate the discrim tree).

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load;

fn effects_runtime_sym(kb: &KnowledgeBase) -> anthill_core::intern::Symbol {
    kb.try_resolve_symbol("anthill.prelude.EffectsRuntime")
        .expect("EffectsRuntime symbol pre-registered by register_prelude")
}

#[test]
fn bridge_fact_installed_after_register_prelude() {
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);

    let er_sym = effects_runtime_sym(&kb);
    let rules = kb.by_functor(er_sym);
    assert_eq!(
        rules.len(),
        1,
        "expected exactly one rule with EffectsRuntime functor after register_prelude, got {} — \
         the bridge fact (proposal 045 §2.0.1) should be installed during prelude bootstrap",
        rules.len()
    );
}

#[test]
fn bridge_fact_not_duplicated_on_second_register_prelude() {
    // Mirrors the op_requirements.rs:259-261 pattern: register_prelude
    // explicitly, then load_all → register_prelude again. The bridge must
    // remain a single rule, not pile up. With the by_functor guard at
    // load.rs's emit_effects_runtime_bridge_fact, the second call is a
    // no-op for the bridge.
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    load::register_prelude(&mut kb);

    let er_sym = effects_runtime_sym(&kb);
    let rules = kb.by_functor(er_sym);
    assert_eq!(
        rules.len(),
        1,
        "expected bridge fact to remain a single rule across two register_prelude calls, got \
         {} — duplicates would inflate by_functor / by_sort / discrim and surface duplicate \
         solutions for any query matching EffectsRuntime[Effects = ?]",
        rules.len()
    );
}

#[test]
fn bridge_fact_not_duplicated_on_many_register_prelude_calls() {
    // A stronger stress on the guard: five calls in a row. The first
    // installs the bridge; the rest must each short-circuit.
    let mut kb = KnowledgeBase::new();
    for _ in 0..5 {
        load::register_prelude(&mut kb);
    }

    let er_sym = effects_runtime_sym(&kb);
    let rules = kb.by_functor(er_sym);
    assert_eq!(rules.len(), 1, "expected 1 rule after 5 register_prelude calls, got {}", rules.len());
}
