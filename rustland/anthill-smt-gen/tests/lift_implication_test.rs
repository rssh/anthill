//! WI-C1: `lift_rule_to_implication_clause` — converts a positive-
//! form rule (`R :- premises -: conclusion`) into a forall-quantified
//! implication clause for splicing as a cited-lemma assumption.
//!
//! Deterministic semantics: the `:-` clause is the premise set, the
//! `-:` clause is the conclusion. No heuristic.

use super::common::{load_kb_with, run_z3, z3_available};
use anthill_smt_gen::lift_rule_to_implication_clause;

fn build_simple_kb() -> anthill_core::kb::KnowledgeBase {
    // Trivial scalar lemma: `?x >= 5 ⇒ ?x >= 3`. Premise is on the
    // `:-` side, conclusion is on the `-:` side. The lift emits
    // `(forall ((var_x Real)) (=> (>= var_x 5.0) (>= var_x 3.0)))`.
    let source = r#"
        namespace test.lift.simple
          import anthill.prelude.{Float}
          import anthill.prelude.Ordered.{gte}

          export simple_lemma

          rule simple_lemma(?w)
            :- gte(?x, 5.0),
               ?w = ?x
            -: gte(?x, 3.0)
        end
    "#;
    load_kb_with(source)
}

#[test]
fn lift_emits_forall_implication_from_explicit_conclusion() {
    let kb = build_simple_kb();
    let clause = lift_rule_to_implication_clause(
        &kb, "test.lift.simple.simple_lemma").expect("lift");

    assert!(clause.starts_with("(forall ("),
        "expected forall-quantified clause, got:\n{clause}");
    // Premise `(>= var_x 5.0)` survives.
    assert!(clause.contains("(>= ") && clause.contains("5.0"),
        "expected the >= 5.0 premise to surface:\n{clause}");
    // Conclusion `(>= var_x 3.0)` is emitted directly (no inversion).
    assert!(clause.contains("3.0"),
        "expected conclusion to mention 3.0:\n{clause}");
    // Implication arrow.
    assert!(clause.contains("(=>"),
        "expected an implication form:\n{clause}");
}

#[test]
fn lifted_implication_is_a_z3_tautology() {
    if !z3_available() { return; }
    let kb = build_simple_kb();
    let clause = lift_rule_to_implication_clause(
        &kb, "test.lift.simple.simple_lemma").expect("lift");

    let smt = format!(
        "(set-logic LRA)\n(assert (not {clause}))\n(check-sat)\n"
    );
    let out = run_z3("lift_tautology", &smt);
    assert_eq!(out, "unsat",
        "lifted implication must be a tautology — got `{out}`. SMT was:\n{smt}");
}

#[test]
fn lift_refuses_rule_without_conclusion_clause() {
    // Violation-shape rule (no `-:`) — must NOT be liftable. The
    // citable-rule contract is opt-in via `-:`.
    let source = r#"
        namespace test.lift.no_conclusion
          import anthill.prelude.{Float}
          import anthill.prelude.Ordered.{gte, lt}

          export violation_only

          rule violation_only(?w)
            :- gte(?x, 5.0),
               lt(?x, 3.0),
               ?w = ?x
        end
    "#;
    let kb = load_kb_with(source);
    let result = lift_rule_to_implication_clause(
        &kb, "test.lift.no_conclusion.violation_only");
    let err = result.expect_err("lift must refuse rules without a `-:` clause");
    assert!(err.message.contains("not citable") || err.message.contains("`-:`"),
        "error message should mention the missing -: clause: `{}`", err.message);
}

fn build_band_kb() -> anthill_core::kb::KnowledgeBase {
    // Multi-clause: premises `?x >= 5 AND ?x <= 10` ⇒ conclusion
    // `?x >= 5 AND ?x <= 10` (still trivial, but exercises
    // multi-premise / multi-conclusion ANDing).
    let source = r#"
        namespace test.lift.band
          import anthill.prelude.{Float}
          import anthill.prelude.Ordered.{gte, lte}

          export band_lemma

          rule band_lemma(?w)
            :- gte(?x, 5.0),
               lte(?x, 10.0),
               ?w = ?x
            -: gte(?x, 5.0), lte(?x, 10.0)
        end
    "#;
    load_kb_with(source)
}

#[test]
fn lift_emits_multi_premise_and_multi_conclusion_with_and() {
    let kb = build_band_kb();
    let clause = lift_rule_to_implication_clause(
        &kb, "test.lift.band.band_lemma").expect("lift");
    // Multi-clause premises and conclusions both wrap in (and …).
    assert!(clause.matches("(and ").count() >= 2,
        "multi-clause premise + conclusion should produce two `(and …)` wrappers:\n{clause}");
    assert!(clause.contains("5.0") && clause.contains("10.0"),
        "expected both 5.0 and 10.0 literals to surface:\n{clause}");
}
