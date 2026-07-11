//! WI-681 — the lf1 GPS formation-geometry consumer of WI-669.
//!
//! A proof reads the follower's separation from the leader by calling the
//! `desired_position` controller op relationally; the SMT emitter inlines its
//! body-derived defining equation (WI-669 seam) instead of a hand-written
//! twin. `desired_position`'s body rotates a body-frame offset into the world
//! frame: `leader.pos + R(leader.yaw)·offset`. A 2-D rotation preserves norm,
//! so `|target − leader| = |offset| = 4` for ANY yaw — the ONLY nonlinear fact
//! needed is `cos²+sin²=1`. This exercises the three emitter pieces WI-681 adds:
//!   - an entity-constructor eq-RHS (`?target = Vec3(...)`) bound (frame-closed)
//!     for later field access, not translated as an arithmetic expression;
//!   - `cos`/`sin` lowered to uninterpreted functions + the Pythagorean identity;
//!   - the transitive seam reaching a bodied op called one inline-level down.

use super::common::{load_kb_with, run_z3, z3_available};
use anthill_core::kb::op_info::all_operation_params;
use anthill_core::kb::KnowledgeBase;
use anthill_smt_gen::{emit_satisfiability_check_with, ProofConfig};

/// A KB with `desired_position` (single-arm `Vec3` body over `cos`/`sin`), a
/// leader pose fact (at origin, yaw 0), a follower-offset fact (−4, 0, 0), and
/// two violation rules: `violation_direct` calls `desired_position` in its own
/// body; `violation_via_helper` reaches it one inline-level down through
/// `formation`.
fn build_kb() -> KnowledgeBase {
    let source = r#"
        namespace test.smt_gen.wi681
          import anthill.prelude.{Float, Int64, Bool}
          import anthill.prelude.Numeric.{add, sub, mul}
          import anthill.prelude.Ordered.{lt, gt, gte}
          import anthill.prelude.Float.{cos, sin}
          import anthill.geometry.{Vec3}

          enum Drone
            entity Leader
            entity Follower
          end

          entity Pose(position: Vec3, roll: Float, pitch: Float, yaw: Float)
          entity DistanceBounds(d_min: Float, d_max: Float)

          sort Geo
            operation desired_position(leader: Pose, offset: Vec3) -> Vec3 =
              Vec3(
                x: add(leader.position.x,
                       sub(mul(cos(leader.yaw), offset.x),
                           mul(sin(leader.yaw), offset.y))),
                y: add(leader.position.y,
                       add(mul(sin(leader.yaw), offset.x),
                           mul(cos(leader.yaw), offset.y))),
                z: add(leader.position.z, offset.z))
          end

          fact DistanceBounds(d_min: 1.0, d_max: 20.0)
          fact leader_pose(Pose(position: Vec3(x: 0.0, y: 0.0, z: 12.0),
                                roll: 0.0, pitch: 0.0, yaw: 0.0))
          fact follower_offset(Vec3(x: -4.0, y: 0.0, z: 0.0))

          rule distance_sq(?d_sq, ?p1, ?p2)
            :- ?dx = ?p1.position.x - ?p2.position.x,
               ?dy = ?p1.position.y - ?p2.position.y,
               ?dz = ?p1.position.z - ?p2.position.z,
               ?d_sq = ?dx * ?dx + ?dy * ?dy + ?dz * ?dz

          rule formation(?lp, ?fp)
            :- leader_pose(?lp),
               follower_offset(?off),
               Geo.desired_position(?lp, ?off, ?target),
               ?fp = Pose(position: ?target, roll: 0.0, pitch: 0.0, yaw: 0.0)

          rule violation_direct(?w)
            :- leader_pose(?lp),
               follower_offset(?off),
               Geo.desired_position(?lp, ?off, ?target),
               ?fp = Pose(position: ?target, roll: 0.0, pitch: 0.0, yaw: 0.0),
               distance_sq(?d_sq, ?lp, ?fp),
               ?d * ?d = ?d_sq,
               gte(?d, 0.0),
               DistanceBounds(d_min: ?d_min, d_max: ?_),
               lt(?d, ?d_min),
               ?w = ?d

          rule violation_via_helper(?w)
            :- formation(?lp, ?fp),
               distance_sq(?d_sq, ?lp, ?fp),
               ?d * ?d = ?d_sq,
               gte(?d, 0.0),
               DistanceBounds(d_min: ?d_min, d_max: ?_),
               lt(?d, ?d_min),
               ?w = ?d
        end
    "#;
    load_kb_with(source)
}

fn desired_position_sym(kb: &KnowledgeBase) -> anthill_core::intern::Symbol {
    all_operation_params(kb).into_iter().map(|(s, _)| s)
        .find(|s| kb.resolve_sym(*s).rsplit('.').next() == Some("desired_position"))
        .expect("desired_position op")
}

#[test]
fn body_derived_geometry_emits_uninterpreted_trig_and_identity() {
    let mut kb = build_kb();
    // The seam step: synthesize desired_position's defining rule.
    kb.synthesize_op_defining_rule(desired_position_sym(&kb))
        .expect("desired_position synthesizes a defining rule");
    let cfg = ProofConfig { logic: Some("QF_UFNRA".to_string()), ..Default::default() };
    let smt = emit_satisfiability_check_with(
        &kb, "test.smt_gen.wi681.violation_direct", &cfg).expect("emit");

    // cos/sin ride as uninterpreted functions...
    assert!(smt.contains("(declare-fun anthill_cos (Real) Real)"),
        "cos must be an uninterpreted function:\n{smt}");
    assert!(smt.contains("(declare-fun anthill_sin (Real) Real)"), "sin uninterpreted:\n{smt}");
    // ...constrained ONLY by the Pythagorean identity on the leader's yaw (0.0).
    assert!(smt.contains(
        "(assert (= (+ (* (anthill_cos 0.0) (anthill_cos 0.0)) \
         (* (anthill_sin 0.0) (anthill_sin 0.0))) 1.0))"),
        "the Pythagorean identity for the yaw arg must be asserted:\n{smt}");
    // The offset (−4) reaches the document from the body-derived Vec3, and there
    // is NO hand-written separation constant.
    assert!(smt.contains("(- 4.0)"), "the offset −4 flows through the body:\n{smt}");
}

#[test]
fn body_derived_geometry_z3_says_unsat() {
    if !z3_available() { return; }
    let mut kb = build_kb();
    kb.synthesize_op_defining_rule(desired_position_sym(&kb)).expect("synth");
    let cfg = ProofConfig { logic: Some("QF_UFNRA".to_string()), ..Default::default() };
    let smt = emit_satisfiability_check_with(
        &kb, "test.smt_gen.wi681.violation_direct", &cfg).expect("emit");
    assert_eq!(run_z3("wi681_direct", &smt), "unsat",
        "|target − leader| = |offset| = 4 ≥ 1 = d_min for every yaw. SMT:\n{smt}");
}

#[test]
fn transitive_seam_reaches_op_one_level_down() {
    if !z3_available() { return; }
    let mut kb = build_kb();
    // No manual synth: the transitive seam must reach `desired_position`
    // through the `formation` helper the obligation calls.
    kb.synthesize_body_derived_defrules("test.smt_gen.wi681.violation_via_helper");
    let cfg = ProofConfig { logic: Some("QF_UFNRA".to_string()), ..Default::default() };
    let smt = emit_satisfiability_check_with(
        &kb, "test.smt_gen.wi681.violation_via_helper", &cfg)
        .expect("emit: the transitive seam must have synthesized desired_position");
    assert_eq!(run_z3("wi681_helper", &smt), "unsat",
        "the body-derived geometry discharges through the helper rule. SMT:\n{smt}");
}
