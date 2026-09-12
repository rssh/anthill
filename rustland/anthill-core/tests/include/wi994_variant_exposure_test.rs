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
//! the ambiguity is expected; the count that row pins has since gone 5 → 2 → 1,
//! see its own doc). `…were_always_exposed` and `…resolves_guarded_uniquely` PASS
//! EITHER WAY, by design: they are what make those failures attributable to
//! pre-registration rather than to the wildcard import or to `guarded` itself. In
//! `wi979_declaration_order_test` the same backout fails
//! `variant_exposure_is_order_independent_wi994` alone.
//!
//! `two_distinct_references_…_report_twice` is NOT one of this ticket's controls —
//! it belongs to WI-1005, which WI-20260911-073GH delivered; both rows' numbers and
//! their separate back-out are at its own doc.

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
  import anthill.prelude.PartialEq.{eq}
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
            // THE FINDING. Before the fix this line was absent and three others —
            // two missing-field rows and a type mismatch — were the whole diagnosis,
            // all three about the wrong sort and none of them saying a word about
            // the choice.
            // WI-977: the scope is named QUALIFIED — as the candidate list beside it
            // always was. A bare `p` next to two fully-qualified candidates was the
            // one un-qualified name in the message.
            "ambiguous symbol 'guarded' in scope 'wi994.amb.p': candidates \
             [\"anthill.prelude.EffectExpression.guarded\", \
             \"anthill.reflect.LogicalQuery.guarded\"]",
            // THE CASCADE IS GONE, and this note is the "visible rather than silent"
            // the previous version of this comment asked for. It used to pin three more
            //   'guarded' has no field 'label' (declares: query, condition)
            //   'guarded' has no field 'guard' (declares: query, condition)
            //   type mismatch in guarded.apply: expected known operation or arrow-typed variable
            // — all three, as the note above says, ABOUT THE WRONG SORT. They existed
            // because `push_ambiguous_symbol` used to answer with `intern(name)`, a bare
            // symbol carrying no sort at all, so every later reader re-diagnosed the
            // reference it could not resolve. WI-980 made it answer with one of the real
            // candidates instead — it had to, because for a TOP-LEVEL candidate the bare
            // intern is a second symbol with the same qualified name, and storing a rule
            // head under it aborted the process on the WI-581 assert. A real candidate
            // has the fields, so the follow-on questions simply do not arise.
            //
            // WHICH candidate is arbitrary and the fix says so; what is NOT arbitrary is
            // that it is one of the two the user is being asked to choose between. The
            // count dropping from five to two was therefore the blast radius SHRINKING
            // to the errors that name the actual choice.
            //
            // AND THE SECOND OF THOSE TWO IS NOW GONE TOO — WI-1005, delivered by
            // WI-20260911-073GH rather than by a ticket of its own. The list used to
            // carry a duplicate of the row above differing ONLY in the scope name
            // (`in scope 'wi994.amb'`): the ONE occurrence at 6:7 was resolved twice,
            // once by `convert_expr_term` in the operation's scope and once by
            // `emit_operation_equation`, which lowered the same body again from the
            // tail of `load_operation` — after the enclosing scope had been restored.
            // `dedup_key` is deliberately INJECTIVE on the full rendering (WI-745), so
            // two spellings of one finding could not collapse, and WI-1005 refused to
            // widen it for the reason its doc gives.
            //
            // Nothing about the ambiguity path changed. The second resolution now runs
            // in the operation's own scope — it has to, so that an applied parameter is
            // the parameter and not a same-named constructor — so the two renderings
            // COINCIDE and the existing injective key collapses them, which is WI-1005's
            // "eliminate one producer rather than widen the key" reached from the other
            // side. Its other two acceptance rows are measured at
            // `two_distinct_references_to_one_ambiguous_name_still_report_twice` below
            // (4 → 2 on back-out, against this row's 2 → 1) and at
            // `run_cmd_test::ambiguous_symbol_blocks_the_run`'s count-is-1 assertion,
            // which is UNMOVED — its fixture's ambiguity is in a FACT head, not an
            // operation body, so no second lowering ever doubled it.
        ],
    );
}

/// WI-1005's CONTROL, and the row that says the collapse above is the DUPLICATE going
/// and not a SITE going.
///
/// `dedup_key` is injective on the full rendering, span included, precisely so that two
/// GENUINELY DISTINCT references to one bad name both survive — a short scope name is
/// not a unique identity (no-short-name-comparison), so collapsing on it would hide a
/// real second site. Two operations, two occurrences, two errors.
///
/// IT DOES NOT PASS EITHER WAY, and the first draft of this doc said it did. MEASURED by
/// backing the change out and re-running: **4** errors, not 2 — each occurrence doubled,
/// at 6:7 and 8:7, once `in scope 'wi994.amb2.<op>'` and once `in scope 'wi994.amb2'`.
/// So the row is a measurement, and a sharper one than intended: the count goes 4 → 2
/// PER OCCURRENCE, while the fixture above goes 2 → 1. A repair that merely stopped
/// reporting the second SITE would take this row to 1 and the one above to 1 as well,
/// and only this row can tell those two outcomes apart.
#[test]
fn two_distinct_references_to_one_ambiguous_name_still_report_twice() {
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(
            r#"
namespace wi994.amb2
  import anthill.prelude.*
  import anthill.reflect.*
  operation p(t: Type, g: List[T = Term]) -> EffectExpression
    = guarded(label: t, guard: g)
  operation q(t: Type, g: List[T = Term]) -> EffectExpression
    = guarded(label: t, guard: g)
end
"#,
        ),
        &[
            "ambiguous symbol 'guarded' in scope 'wi994.amb2.p': candidates \
             [\"anthill.prelude.EffectExpression.guarded\", \
             \"anthill.reflect.LogicalQuery.guarded\"]",
            "ambiguous symbol 'guarded' in scope 'wi994.amb2.q': candidates \
             [\"anthill.prelude.EffectExpression.guarded\", \
             \"anthill.reflect.LogicalQuery.guarded\"]",
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
