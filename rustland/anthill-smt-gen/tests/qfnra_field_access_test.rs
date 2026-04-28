//! QF_NRA + entity field_access integration.
//!
//! Exercises the smt-gen path that lights up when a violation rule
//! reaches into a fact's entity term via `?p.position.x`-style dot
//! syntax. The body composes:
//!   - a multi-pos-arg rule call (`real_pose_at(0, Leader, ?lp)`)
//!     that fact-matches against a ground fact whose third arg is a
//!     `Pose(position: Vec3(x: ..., ...), ...)` constructor,
//!   - a sub-rule call (`distance_sq(?d_sq, ?lp, ?fp)`) whose body
//!     uses `?lp.position.x` — i.e. field_access on the entity
//!     binding propagated from the fact match,
//!   - a nonlinear equality `?d * ?d = ?d_sq` lifted as a free
//!     `(assert (= ...))` (LHS is not a bare DeBruijn var).
//!
//! Z3 should answer `unsat` when the violation asserts `?d < d_min`
//! against the concrete 4 m geometry and d_min = 1 m.
//!
//! No-Z3 fallback: if `z3` isn't on PATH, we still verify that
//! smt-gen emits a syntactically well-formed document with the
//! expected literals and `(set-logic QF_NRA)` line, so the test
//! catches regressions on machines without Z3.

use super::common::{load_kb_with, run_z3, z3_available};
use anthill_smt_gen::{emit_satisfiability_check_with, ProofConfig};

fn build_kb() -> anthill_core::kb::KnowledgeBase {
    let source = r#"
        namespace test.smt_gen.qfnra_field
          import anthill.prelude.{Float, Int, Bool}
          import anthill.prelude.Numeric.{add, sub, mul}
          import anthill.prelude.Ordered.{lt, gte}

          export Drone, Vec3, Pose, DistanceBounds
          export real_pose_at, distance_sq, violation

          enum Drone
            entity Leader
            entity Follower
          end

          entity Vec3(x: Float, y: Float, z: Float)
          entity Pose(position: Vec3)
          entity DistanceBounds(d_min: Float)

          fact DistanceBounds(d_min: 1.0)

          fact real_pose_at(0, Leader,
            Pose(position: Vec3(x: 0.0, y: 0.0, z: 12.0)))
          fact real_pose_at(0, Follower,
            Pose(position: Vec3(x: -4.0, y: 0.0, z: 12.0)))

          rule distance_sq(?d_sq, ?p1, ?p2)
            :- ?dx = ?p1.position.x - ?p2.position.x,
               ?dy = ?p1.position.y - ?p2.position.y,
               ?dz = ?p1.position.z - ?p2.position.z,
               ?d_sq = ?dx * ?dx + ?dy * ?dy + ?dz * ?dz

          rule violation(?w)
            :- real_pose_at(0, Leader, ?lp),
               real_pose_at(0, Follower, ?fp),
               distance_sq(?d_sq, ?lp, ?fp),
               ?d * ?d = ?d_sq,
               gte(?d, 0.0),
               DistanceBounds(d_min: ?d_min),
               lt(?d, ?d_min),
               ?w = ?d
        end
    "#;
    load_kb_with(source)
}

#[test]
fn qfnra_field_access_emits_well_formed_smtlib() {
    let kb = build_kb();
    let cfg = ProofConfig {
        logic: Some("QF_NRA".to_string()),
        ..Default::default()
    };
    let smt = emit_satisfiability_check_with(
        &kb, "test.smt_gen.qfnra_field.violation", &cfg)
        .expect("emit");
    assert!(smt.contains("(set-logic QF_NRA)"),
        "expected QF_NRA logic line, got:\n{smt}");
    // The leader/follower x-coords must reach the document as
    // literals — that is the whole point of fact-match + field_access.
    assert!(smt.contains("(- 4.0)") || smt.contains("-4.0"),
        "expected the follower's x = -4 to appear as a literal:\n{smt}");
    // Nonlinear equality is lifted as an assertion, not a binding —
    // the LHS is `(* ?d ?d)`, not a bare DeBruijn var.
    assert!(smt.contains("(assert (= (*"),
        "expected `?d * ?d = ?d_sq` to surface as an assertion:\n{smt}");
}

#[test]
fn qfnra_field_access_z3_says_unsat() {
    if !z3_available() { return; }
    let kb = build_kb();
    let cfg = ProofConfig {
        logic: Some("QF_NRA".to_string()),
        ..Default::default()
    };
    let smt = emit_satisfiability_check_with(
        &kb, "test.smt_gen.qfnra_field.violation", &cfg)
        .expect("emit");
    let out = run_z3("qfnra_field_access", &smt);
    assert_eq!(out, "unsat",
        "concrete |Δ| = 4 ≥ 1 = d_min — no violation. SMT was:\n{smt}");
}
