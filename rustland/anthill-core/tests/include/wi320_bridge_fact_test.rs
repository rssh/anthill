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
use anthill_core::kb::term::Term;
use anthill_core::kb::typing::{sort_functor_of, type_display_name, types_compatible};
use smallvec::SmallVec;

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

// ─────────────────────────────────────────────────────────────────────
// Typing.rs `effects_rows` arms — code-review findings #2, #3, #5, #11.
//
// No typer flow currently produces an `effects_rows`-typed value (that
// is WI-307 work), so these tests construct the variant directly via
// the public `kb.alloc(Term::Fn { … })` API and exercise each
// `type_functor_name`-keyed dispatcher to confirm `effects_rows` no
// longer falls through to the generic catch-all.
// ─────────────────────────────────────────────────────────────────────

/// Build `effects_rows(effects_expr = <inner>)` directly. The arms under
/// test only inspect the wrapper's functor + the inner's TermId, so the
/// inner can be any well-formed term — `Type::nothing` keeps the test
/// self-contained (no stdlib load required, just `register_prelude`).
fn build_effects_rows_wrapping(kb: &mut KnowledgeBase, inner: anthill_core::kb::term::TermId)
    -> anthill_core::kb::term::TermId
{
    let effects_rows_sym = kb.try_resolve_symbol("anthill.prelude.Type.effects_rows")
        .expect("effects_rows entity symbol pre-registered");
    let effects_expr_sym = kb.intern("effects_expr");
    kb.alloc(Term::Fn {
        functor: effects_rows_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(effects_expr_sym, inner)]),
    })
}

fn build_nothing(kb: &mut KnowledgeBase) -> anthill_core::kb::term::TermId {
    let nothing_sym = kb.try_resolve_symbol("anthill.prelude.Type.nothing")
        .expect("nothing entity symbol pre-registered");
    kb.alloc(Term::Fn { functor: nothing_sym, pos_args: SmallVec::new(), named_args: SmallVec::new() })
}

#[test]
fn type_display_name_renders_effects_rows_with_row_braces() {
    // Code-review #11: prior to the dedicated arm, `effects_rows` fell
    // through to the generic Fn catch-all and rendered as
    // `effects_rows[effects_expr = nothing]`. The new arm renders the
    // wrapped expression in row braces.
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);

    let nothing = build_nothing(&mut kb);
    let er = build_effects_rows_wrapping(&mut kb, nothing);

    let display = type_display_name(&kb, er);
    assert_eq!(
        display, "{nothing}",
        "expected row-brace rendering of effects_rows(nothing), got {:?}",
        display
    );
}

#[test]
fn sort_functor_of_returns_none_for_effects_rows() {
    // Code-review #5: `effects_rows` is a structural Type variant with
    // no underlying sort head — `min_sort` should be undefined for
    // occurrences typed as an effect-row. The arm makes this explicit
    // (previously it fell to the `Term::Ref` catch-all, which also
    // returned None — same observable result, but now documented in
    // code as intentional rather than incidental).
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);

    let nothing = build_nothing(&mut kb);
    let er = build_effects_rows_wrapping(&mut kb, nothing);

    assert_eq!(sort_functor_of(&kb, er), None);
}

#[test]
fn types_compatible_recurses_into_effects_rows_inner() {
    // Code-review #2: prior to the dedicated arm, two `effects_rows`
    // wrappers with distinct TermIds fell to `_ => false` — even when
    // the wrapped inner Types were compatible. The new arm recurses
    // into the wrapped inner.
    //
    // We pick an inner pair where compatibility is asymmetric — `nothing`
    // is the bottom type (compatible with anything), so wrapping
    // `nothing` in `effects_rows` should be compatible with any other
    // `effects_rows`. Before the arm: `_ => false`; after: the recursive
    // call honors `nothing`'s bottom semantics.
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);

    let nothing = build_nothing(&mut kb);
    // A second, distinct-TermId inner: `type_var(?N)` — a fresh logical var.
    let type_var_sym = kb.try_resolve_symbol("anthill.prelude.Type.type_var")
        .expect("type_var entity symbol pre-registered");
    let name_field = kb.intern("name");
    let n_sym = kb.intern("N");
    let n_ref = kb.alloc(Term::Ref(n_sym));
    let type_var_term = kb.alloc(Term::Fn {
        functor: type_var_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(name_field, n_ref)]),
    });

    let er_nothing = build_effects_rows_wrapping(&mut kb, nothing);
    let er_var = build_effects_rows_wrapping(&mut kb, type_var_term);

    // Wrappers are distinct TermIds (different inners), so the
    // line-5049 `actual == expected` short-circuit does not fire — the
    // new arm is what's being exercised.
    assert_ne!(er_nothing, er_var);

    // `nothing` is bottom (compatible with anything) so the recursive
    // `types_compatible` call returns true. Before the arm this
    // returned false; after the arm it returns true.
    assert!(
        types_compatible(&mut kb, er_nothing, er_var),
        "expected effects_rows(nothing) compatible with effects_rows(type_var(?N)) via the new arm"
    );
}
