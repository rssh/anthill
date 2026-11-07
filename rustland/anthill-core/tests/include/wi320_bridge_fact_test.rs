//! WI-320 — the `EffectsRuntime` ↔ `effects_rows` typing arms.
//!
//! The bridge FACT this file first pinned (`EffectsRuntime[Effects = effects_rows(?)]`,
//! asserted at bootstrap so the goal held by an SLD match) was removed by WI-20261107-FDJ0E:
//! the goal is a type check now, which reads the anchor structurally. What stays is the
//! typer's reading of an `effects_rows` type.

use anthill_core::kb::load;
use anthill_core::kb::subst::Substitution;
use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::term_view::TermIdView;
use anthill_core::kb::typing::{
    sort_functor_of, type_display_name, types_compatible as raw_types_compatible,
};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

/// Test-private wrapper: see typing_test.rs::types_compatible for the
/// WI-335 fresh-subst convention.
fn types_compatible(kb: &mut KnowledgeBase, actual: TermId, expected: TermId) -> bool {
    let mut subst = Substitution::new();
    raw_types_compatible(kb, &mut subst, &TermIdView(actual), &TermIdView(expected))
}

fn effects_runtime_sym(kb: &KnowledgeBase) -> anthill_core::intern::Symbol {
    kb.try_resolve_symbol("anthill.prelude.EffectsRuntime")
        .expect("EffectsRuntime symbol pre-registered by register_prelude")
}

/// WI-20261107-FDJ0E — THE BRIDGE FACT IS GONE. It made the goal `EffectsRuntime[Effects =
/// <row>]` hold by an SLD match; the goal is now a type check, which reads the anchor as type
/// checking does — satisfied by an effect row (`wi_fdj0e_type_application_goal_test`'s query
/// row) — and no clause may be headed by a sort's type application. Bootstrap, run once or
/// five times, files none.
#[test]
fn no_clause_is_headed_by_the_anchor_after_register_prelude() {
    let mut kb = KnowledgeBase::new();
    for _ in 0..5 {
        load::register_prelude(&mut kb);
        let er_sym = effects_runtime_sym(&kb);
        assert!(kb.rules_by_functor(er_sym).is_empty(), "no clause is headed by `EffectsRuntime`");
    }
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
fn build_effects_rows_wrapping(
    kb: &mut KnowledgeBase,
    inner: anthill_core::kb::term::TermId,
) -> anthill_core::kb::term::TermId {
    let effects_rows_sym = kb
        .try_resolve_symbol("anthill.prelude.TypeExtractor.EffectsRows")
        .expect("EffectsRows entity symbol pre-registered");
    let effects_expr_sym = kb.intern("effects_expr");
    kb.alloc(Term::Fn {
        functor: effects_rows_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(effects_expr_sym, inner)]),
    })
}

fn build_nothing(kb: &mut KnowledgeBase) -> anthill_core::kb::term::TermId {
    kb.make_nothing_type()
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
fn types_compatible_routes_effects_rows_via_row_subtyping() {
    // WI-320 substrate originally added a dedicated (effects_rows,
    // effects_rows) arm in types_compatible so distinct-TermId wrappers
    // wouldn't fall to `_ => false`; the substrate did recursive
    // structural types_compatible on the inner.
    //
    // **WI-333 supersedes that recursive structural check** — the arm
    // now dispatches to `subtype_effect_rows`, which is row-aware
    // (open-tail subsumption, set semantics with element subtyping).
    // The substrate's "the arm exists and routes the inner pair" check
    // moves here, expressed in row-semantics terms: two structurally
    // distinct effects_rows wrappers with row-compatible payloads should
    // compare compatible.
    //
    // Use a valid EffectExpression pair: empty_row vs merge(present(X),
    // empty_row) — closed/closed where actual ⊆ expected. The wrappers
    // are distinct TermIds (different EffectExpression payloads), so the
    // hash-cons fast path doesn't fire — the arm dispatch is what's
    // being exercised.
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);

    let empty = kb.make_effect_expression_empty_row();
    let x_sym = kb.intern("X");
    let x_label = kb.make_sort_ref(x_sym);
    let present_x = kb.make_effect_expression_present(x_label);
    let one_label = kb.make_effect_expression_merge(present_x, empty);

    let er_empty = kb.make_effects_rows_type(empty);
    let er_one = kb.make_effects_rows_type(one_label);

    // Distinct TermIds — hash-cons short-circuit doesn't fire here.
    assert_ne!(er_empty, er_one);

    // Closed empty <: closed {X} — subset semantics under row sub.
    assert!(
        types_compatible(&mut kb, er_empty, er_one),
        "expected effects_rows(empty_row) <: effects_rows({{X}}) via row sub"
    );
    // Reverse direction: closed {X} NOT <: closed empty.
    assert!(
        !types_compatible(&mut kb, er_one, er_empty),
        "expected effects_rows({{X}}) NOT <: effects_rows(empty_row)"
    );
}
