//! `ProofConfig.assumptions` smoke test: pre-rendered SMT clauses
//! arrive as `(assert …)` blocks in the preamble for both upper-bound
//! and satisfiability modes. Smt-gen treats the strings opaquely —
//! it doesn't parse, it splices.
//!
//! Couples with the upcoming prove-driver `using` clause: the driver
//! collects cited-lemma clauses (rendered separately) and hands them
//! in here.

use super::common::load_kb_with;
use anthill_smt_gen::{emit_satisfiability_check_with, ProofConfig};

fn build_kb() -> anthill_core::kb::KnowledgeBase {
    let source = r#"
        namespace test.smt_gen.assumptions
          import anthill.prelude.{Float, Int64}
          import anthill.prelude.Ordered.{lt}

          export DistanceBounds, violation

          entity DistanceBounds(d_min: Float, d_max: Float)
          fact DistanceBounds(d_min: 1.0, d_max: 10.0)

          rule violation(?w)
            :- DistanceBounds(d_min: ?d_min, d_max: ?_),
               lt(?d, ?d_min),
               ?w = ?d
        end
    "#;
    load_kb_with(source)
}

#[test]
fn assumptions_appear_as_assert_in_preamble() {
    let kb = build_kb();
    // WI-150 changed `emit_assumptions` to splice raw, so callers
    // wrap each clause in `(assert ...)` themselves before stuffing
    // it into ProofConfig.assumptions.
    let cfg = ProofConfig {
        logic: Some("LRA".to_string()),
        assumptions: vec![
            "(assert (>= var_d 5.0))".to_string(),
            "(assert (<= var_d 7.0))".to_string(),
        ],
        ..Default::default()
    };
    let smt = emit_satisfiability_check_with(
        &kb, "test.smt_gen.assumptions.violation", &cfg)
        .expect("emit");
    assert!(smt.contains("(assert (>= var_d 5.0))"),
        "first assumption missing:\n{smt}");
    assert!(smt.contains("(assert (<= var_d 7.0))"),
        "second assumption missing:\n{smt}");
    // The marker comment helps debug-readability of generated SMT.
    assert!(smt.contains("Cited-lemma assumptions"),
        "expected the assumptions block comment:\n{smt}");
    // Must precede the violation goal so Z3 has the hypothesis when
    // deciding `lt(?d, d_min)`.
    let assume_idx = smt.find("(>= var_d 5.0)").unwrap();
    let goal_idx = smt.find("(< ").unwrap_or(usize::MAX);
    assert!(assume_idx < goal_idx,
        "assumption must come before goal:\n{smt}");
}

#[test]
fn empty_assumptions_emit_no_block() {
    let kb = build_kb();
    let cfg = ProofConfig {
        logic: Some("LRA".to_string()),
        assumptions: vec![],
        ..Default::default()
    };
    let smt = emit_satisfiability_check_with(
        &kb, "test.smt_gen.assumptions.violation", &cfg)
        .expect("emit");
    assert!(!smt.contains("Cited-lemma assumptions"),
        "no assumptions ⇒ no block comment:\n{smt}");
}
