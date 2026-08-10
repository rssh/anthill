//! WI-994 — §8.6's variant-exposure link belongs to the DECLARATION. A `sort`
//! that declares entity constructors exposes those names to its enclosing scope,
//! and *which registration of that name came first* decides nothing.
//!
//! `scan_items_pass1`'s `Item::SortWithBody` arm gated the link on `is_new`, and
//! `is_new` is false for two unrelated populations. WI-979 fixed the CATEGORY and
//! left the link gated for both, spinning this ticket out for the first alone —
//! the second it read as a population that "never had the link". That reading is
//! what this file refutes: it is the same defect, and the control is what shows it.
//!
//!   (a) DECLARATION-reuse — `namespace X` before `sort X { entity V }`.
//!       Pinned in `wi979_declaration_order_test`, where the pair is the subject.
//!   (b) BOOTSTRAP-reuse — `register_stdlib_scopes` pre-registers 7 stdlib sorts
//!       that source then re-declares WITH variants. This file.
//!
//! WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT — measured, by restoring the
//! `is_new &&` and re-running: `a_pre_registered_sorts_variants_are_exposed…` and
//! `one_variant_name_exposed_by_two_namespaces_is_ambiguous` (3 load errors where
//! 5 are expected). The other two PASS EITHER WAY, by design: they are the
//! controls that make those failures attributable to pre-registration rather than
//! to the wildcard import or to `guarded` itself. In
//! `wi979_declaration_order_test` the same backout fails
//! `variant_exposure_is_order_independent_wi994` alone.

use anthill_core::eval::{Interpreter, Value};

/// The entity a driven call built, by qualified functor name — which is what says
/// WHICH constructor a bare name reached. Local rather than lifted into `common`:
/// the shape is hand-rolled at nine other sites across five test files, so a lift
/// is a migration of its own (recorded in WI-994's feedback), not a step here.
fn assert_built(interp: &Interpreter, got: &Value, qualified: &str, why: &str) {
    match got {
        Value::Entity { functor, .. } => {
            assert_eq!(interp.kb().qualified_name_of(*functor), qualified, "{why}")
        }
        other => panic!("{why} — expected {qualified}, got {}", other.type_name()),
    }
}

/// The subject and its control are separate tests, not two rows of one: inside a
/// single fixture the subject's load error takes the control down with it, and a
/// control that cannot pass while the subject fails measures nothing.
#[test]
fn a_pre_registered_sorts_variants_are_exposed_to_its_namespace() {
    // `merge` / `empty_row` are variants of `enum anthill.prelude.EffectExpression`,
    // whose symbol the Rust bootstrap pre-registers.
    let mut interp = crate::common::interp_for(
        r#"
namespace wi994.boot
  import anthill.prelude.*
  operation row() -> EffectExpression = merge(left: empty_row(), right: empty_row())
end
"#,
    );
    // Back the un-gate out and this fails at LOAD — `type mismatch in merge.apply:
    // … got unknown functor`.
    let got = interp
        .call("wi994.boot.row", &[])
        .expect("row() must evaluate");
    assert_built(
        &interp,
        &got,
        "anthill.prelude.EffectExpression.merge",
        "bare `merge` must reach the enum's own constructor",
    );
}

/// CONTROL for the test above — passes either way, BY DESIGN. `pair` is a variant
/// of `enum anthill.prelude.Pair`, which nothing pre-registers, so its declaration
/// took the fresh arm and always had its exposure link.
#[test]
fn a_freshly_declared_prelude_sorts_variants_were_always_exposed() {
    let mut interp = crate::common::interp_for(
        r#"
namespace wi994.ctrl
  import anthill.prelude.*
  operation two() -> Bool = eq(pair(fst: 1, snd: 2), pair(fst: 1, snd: 2))
end
"#,
    );
    assert!(
        matches!(interp.call("wi994.ctrl.two", &[]), Ok(Value::Bool(true))),
        "CONTROL: bare `pair` resolves with or without this change",
    );
}

/// The ambiguity §8.6 requires — "two sorts exposing the same variant name make
/// that bare name **ambiguous** rather than letting one silently win".
///
/// This is the row WI-994 was filed asking to PREVENT, on the reading that the
/// pre-fix answer was a unique resolution worth keeping. Measured, it was not: the
/// fixture below spells `guarded(label:, guard:)` — unmistakably
/// `EffectExpression.guarded` — and the loader silently bound it to
/// `LogicalQuery.guarded`, then reported the fields it does not have. That is
/// "picking a referent the user never chose", which `anthill-cli`'s
/// `ambiguous-symbol.anthill` already pins as a refusal for two wildcard-imported
/// SORTS; this makes the two wildcard-imported NAMESPACES agree with it.
#[test]
fn one_variant_name_exposed_by_two_namespaces_is_ambiguous() {
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(
            r#"
namespace wi994.amb
  import anthill.prelude.*
  import anthill.reflect.*
  operation p(t: Type, g: List[T = Term]) -> EffectExpression
    = guarded(label: t, guard: g)
end
"#,
        ),
        &[
            // THE FINDING. Before the fix these two lines were absent and the
            // three below were the whole diagnosis — all three about the wrong
            // sort, and none of them saying a word about the choice.
            "ambiguous symbol 'guarded' in scope 'p': candidates \
             [\"anthill.prelude.EffectExpression.guarded\", \
             \"anthill.reflect.LogicalQuery.guarded\"]",
            // REPORTED TWICE, once per resolution of the one occurrence at 6:7 —
            // the operation's scope and its enclosing namespace's. `dedup_key` is
            // deliberately injective (WI-745) and the two renderings differ only
            // in the scope name, so nothing collapses them; WI-745's own duplicate
            // was eliminated at the PRODUCER, and this is a second producer doing
            // the same thing. Pinned rather than fixed — it is a defect in the
            // ambiguity-reporting path, not in the exposure link, and no fixture
            // reached it before this one. WI-1005, whose acceptance is this list
            // dropping to four. It is easy to miss: name the namespace and the
            // operation alike and the two renderings coincide and dedup, which is
            // what hid it from the probe this test was written from.
            "ambiguous symbol 'guarded' in scope 'amb': candidates \
             [\"anthill.prelude.EffectExpression.guarded\", \
             \"anthill.reflect.LogicalQuery.guarded\"]",
            // …and the cascade behind it, pinned so a later change to the
            // ambiguity's blast radius is visible rather than silent.
            "'guarded' has no field 'label' (declares: query, condition)",
            "'guarded' has no field 'guard' (declares: query, condition)",
            "type mismatch in guarded.apply: expected known operation or arrow-typed variable",
        ],
    );
}

/// CONTROL for the test above — passes either way. ONE wildcard import leaves
/// `guarded` with one candidate, so the exposure `anthill.prelude` gained must not
/// disturb it. Without this row the ambiguity test would be satisfied by any change
/// that broke `guarded` generally.
#[test]
fn one_wildcard_import_still_resolves_guarded_uniquely() {
    let mut interp = crate::common::interp_for(
        r#"
namespace wi994.uniq
  import anthill.reflect.*
  operation q0() -> LogicalQuery = empty_query()
  operation p(c: Term) -> LogicalQuery = guarded(query: q0(), condition: c)
end
"#,
    );
    let cond = Value::term(interp.kb_mut().make_name_term("wi994_condition"));
    let got = interp
        .call("wi994.uniq.p", &[cond])
        .expect("p() must evaluate");
    assert_built(
        &interp,
        &got,
        "anthill.reflect.LogicalQuery.guarded",
        "one wildcard import leaves exactly one `guarded` in scope",
    );
}
