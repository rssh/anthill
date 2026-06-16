//! WI-C1: `lift_rule_to_implication_clause` — converts a positive-
//! form rule (per proposal 032: `label: head :- premises`, where the
//! head is the conclusion) into a forall-quantified implication
//! clause for splicing as a cited-lemma assumption.
//!
//! Deterministic semantics: the `:-` clause is the premise set, the
//! head (the rule's stated claim) is the conclusion. No heuristic.

use super::common::{load_kb_with, run_z3, z3_available};
use anthill_smt_gen::lift_rule_to_implication_clause;

fn build_simple_kb() -> anthill_core::kb::KnowledgeBase {
    // Trivial scalar lemma: `?x >= 5 ⇒ ?x >= 3`. The head is the
    // conclusion under proposal 032. The lift emits
    // `(forall ((var_x Real)) (=> (>= var_x 5.0) (>= var_x 3.0)))`.
    let source = r#"
        namespace test.lift.simple
          import anthill.prelude.{Float}
          import anthill.prelude.Ordered.{gte}


          rule simple_lemma: gte(?x, 3.0)
            :- gte(?x, 5.0)
        end
    "#;
    load_kb_with(source)
}

#[test]
fn lift_emits_forall_implication_from_explicit_conclusion() {
    let kb = build_simple_kb();
    let clauses = lift_rule_to_implication_clause(
        &kb, "test.lift.simple.simple_lemma").expect("lift");
    assert_eq!(clauses.len(), 1, "single-head rule lifts to one clause");
    let clause = &clauses[0];

    // The lift now wraps its result in a fully-formed `(assert ...)`
    // statement (WI-150 changed emit_assumptions to splice raw),
    // so the clause starts with `(assert (forall ...))` for ordinary
    // (non-shared) cited rules.
    assert!(clause.starts_with("(assert (forall ("),
        "expected `(assert (forall ...))` clause, got:\n{clause}");
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
    let clauses = lift_rule_to_implication_clause(
        &kb, "test.lift.simple.simple_lemma").expect("lift");
    let clause = &clauses[0];

    // Strip the `(assert ...)` wrapper since this test wants to
    // negate the implication directly. WI-150 changed the lift to
    // return `(assert <imp>)`; we recover `<imp>` for the negation.
    let inner = clause
        .strip_prefix("(assert ")
        .and_then(|s| s.strip_suffix(')'))
        .unwrap_or(clause);
    let smt = format!(
        "(set-logic LRA)\n(assert (not {inner}))\n(check-sat)\n"
    );
    let out = run_z3("lift_tautology", &smt);
    assert_eq!(out, "unsat",
        "lifted implication must be a tautology — got `{out}`. SMT was:\n{smt}");
}

#[test]
fn lift_refuses_rule_without_conclusion_clause() {
    // Violation-shape rule (denial: head=⊥) — must NOT be liftable.
    // The citable-rule contract is opt-in: only positive theorems
    // (head is a real claim) lift to forall implications.
    let source = r#"
        namespace test.lift.no_conclusion
          import anthill.prelude.{Float}
          import anthill.prelude.Ordered.{gte, lt}


          rule violation_only: ⊥
            :- gte(?x, 5.0),
               lt(?x, 3.0)
        end
    "#;
    let kb = load_kb_with(source);
    let result = lift_rule_to_implication_clause(
        &kb, "test.lift.no_conclusion.violation_only");
    let err = result.expect_err("lift must refuse denial-shape rules");
    assert!(err.message.contains("not citable") || err.message.contains("`-:`"),
        "error message should mention the missing conclusion: `{}`", err.message);
}

fn build_band_kb() -> anthill_core::kb::KnowledgeBase {
    // Multi-clause: premises `?x >= 5 AND ?x <= 10` ⇒ conclusion
    // `?x >= 5 AND ?x <= 10`. Under proposal 032 a labeled
    // multi-head rule desugars at load to N labeled rules sharing
    // the label; the lift fans out and returns one clause per head.
    let source = r#"
        namespace test.lift.band
          import anthill.prelude.{Float}
          import anthill.prelude.Ordered.{gte, lte}


          rule band_lemma: gte(?x, 5.0), lte(?x, 10.0)
            :- gte(?x, 5.0),
               lte(?x, 10.0)
        end
    "#;
    load_kb_with(source)
}

#[test]
fn lift_fans_out_one_clause_per_labeled_head() {
    let kb = build_band_kb();
    let clauses = lift_rule_to_implication_clause(
        &kb, "test.lift.band.band_lemma").expect("lift");
    assert_eq!(clauses.len(), 2,
        "two-head labeled rule fans out into two lifted clauses, got {}: {clauses:?}",
        clauses.len());
    let joined = clauses.join("\n");
    // Each clause has multi-premise (and ...) on the premise side.
    assert!(joined.matches("(and ").count() >= 2,
        "each clause's multi-premise side should wrap in (and …):\n{joined}");
    assert!(joined.contains("5.0") && joined.contains("10.0"),
        "expected both 5.0 and 10.0 literals to surface:\n{joined}");
    // Head H1 (>= 3) and H2 (<= 10) split across the two clauses;
    // the >= ... and <= ... conclusions both show up.
    assert!(joined.contains("(>="), "expected a >= conclusion:\n{joined}");
    assert!(joined.contains("(<="), "expected a <= conclusion:\n{joined}");
}
