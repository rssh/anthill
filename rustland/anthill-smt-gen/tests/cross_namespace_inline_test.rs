//! Cross-namespace rule inlining (WI-563).
//!
//! The lf1 safety proofs split a shared `position_distance` rule into a
//! `…common` namespace and consume it from `…gps` / `…transponder`. A
//! violation rule's body goal `position_distance(?d, ?l, ?f)` resolves to
//! the common-namespace rule ONLY when the consuming namespace imports it;
//! smt-gen then inlines the rule body (recursively, through
//! `position_distance_sq`) until it reaches the concrete `real_pose_at(0,…)`
//! geometry, pinning `?d` to the actual 4 m separation. The violation
//! `lt(?d, d_min=1)` is then `unsat`.
//!
//! This test guards both halves of the WI-563 fix:
//!   * `cross_namespace_import_inlines_to_unsat` — with the import present,
//!     the functor resolves and inlines all the way to the literal geometry.
//!   * `unresolved_functor_is_a_loud_error` — WITHOUT the import the functor
//!     stays unresolved and smt-gen returns a loud error rather than
//!     silently treating it as a free/uninterpreted relation (which would
//!     leave `?d` unconstrained and flip the verdict to a spurious `sat`).

use super::common::{load_kb_with, run_z3, z3_available};
use anthill_smt_gen::{emit_satisfiability_check_with, ProofConfig};

/// The shared `…common` namespace: the two-level `position_distance`
/// definition (mirroring safety_common.anthill) plus the concrete initial
/// geometry and a `reachable_real` rule over it.
const COMMON_NS: &str = r#"
    namespace test.smt_gen.common
      import anthill.prelude.{Float, Int64, Bool}
      import anthill.prelude.Numeric.{add, sub, mul}
      import anthill.prelude.Ordered.{gte}

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

      rule reachable_real(?leader_real, ?follower_real)
        :- real_pose_at(?k, Leader, ?leader_real),
           real_pose_at(?k, Follower, ?follower_real)

      rule position_distance_sq(?d_sq, ?p1, ?p2)
        :- ?dx = ?p1.position.x - ?p2.position.x,
           ?dy = ?p1.position.y - ?p2.position.y,
           ?dz = ?p1.position.z - ?p2.position.z,
           ?d_sq = ?dx * ?dx + ?dy * ?dy + ?dz * ?dz

      rule position_distance(?d, ?p1, ?p2)
        :- position_distance_sq(?d_sq, ?p1, ?p2),
           ?d * ?d = ?d_sq,
           gte(?d, 0.0)
    end
"#;

/// The consuming namespace WITH the `position_distance` import — the shape
/// of the fixed safety_gps.anthill.
fn source_with_import() -> String {
    format!(
        r#"{COMMON_NS}
        namespace test.smt_gen.gps
          import anthill.prelude.{{Float, Bool}}
          import anthill.prelude.Ordered.{{lt}}
          import test.smt_gen.common.{{
            reachable_real, position_distance, DistanceBounds
          }}

          rule safety_min_distance(?w)
            :- reachable_real(?leader_real, ?follower_real),
               position_distance(?d, ?leader_real, ?follower_real),
               DistanceBounds(d_min: ?d_min),
               lt(?d, ?d_min),
               ?w = ?d
        end
    "#
    )
}

/// Same consuming namespace but with `position_distance` OMITTED from the
/// import list — the bug shape that WI-563 surfaced.
fn source_without_import() -> String {
    format!(
        r#"{COMMON_NS}
        namespace test.smt_gen.gps
          import anthill.prelude.{{Float, Bool}}
          import anthill.prelude.Ordered.{{lt}}
          import test.smt_gen.common.{{ reachable_real, DistanceBounds }}

          rule safety_min_distance(?w)
            :- reachable_real(?leader_real, ?follower_real),
               position_distance(?d, ?leader_real, ?follower_real),
               DistanceBounds(d_min: ?d_min),
               lt(?d, ?d_min),
               ?w = ?d
        end
    "#
    )
}

fn qfnra_cfg() -> ProofConfig {
    ProofConfig {
        logic: Some("QF_NRA".to_string()),
        ..Default::default()
    }
}

#[test]
fn cross_namespace_import_inlines_to_concrete_geometry() {
    let kb = load_kb_with(&source_with_import());
    let smt = emit_satisfiability_check_with(
        &kb, "test.smt_gen.gps.safety_min_distance", &qfnra_cfg())
        .expect("emit should succeed once position_distance is imported");

    // Inlining must have chased position_distance -> position_distance_sq
    // -> the concrete `real_pose_at(0, …)` facts: the follower's x = -4
    // reaches the document as a literal.
    assert!(smt.contains("(- 4.0)") || smt.contains("-4.0"),
        "cross-namespace inline must reach the literal geometry:\n{smt}");
    // The nonlinear `?d * ?d = ?d_sq` clause from the inner rule must lift
    // as a free assertion (QF_NRA), not a binding.
    assert!(smt.contains("(assert (= (*"),
        "expected the nonlinear square clause as an assertion:\n{smt}");
}

#[test]
fn cross_namespace_import_z3_says_unsat() {
    if !z3_available() { return; }
    let kb = load_kb_with(&source_with_import());
    let smt = emit_satisfiability_check_with(
        &kb, "test.smt_gen.gps.safety_min_distance", &qfnra_cfg())
        .expect("emit");
    let out = run_z3("cross_namespace_inline", &smt);
    assert_eq!(out, "unsat",
        "concrete |Δ| = 4 ≥ 1 = d_min — no violation. SMT was:\n{smt}");
}

#[test]
fn unresolved_functor_is_a_loud_error() {
    // Without the import the `position_distance` functor never resolves to
    // the common-namespace rule. smt-gen must surface this loudly rather
    // than silently emitting an uninterpreted relation (which would leave
    // ?d free and the violation spuriously `sat`).
    let kb = load_kb_with(&source_without_import());
    let err = emit_satisfiability_check_with(
        &kb, "test.smt_gen.gps.safety_min_distance", &qfnra_cfg())
        .expect_err("an unresolved body-goal functor must be a loud error");
    let msg = err.message;
    assert!(msg.contains("position_distance"),
        "the error must name the offending functor, got: {msg}");
    assert!(msg.contains("unhandled body goal functor"),
        "expected the unhandled-functor diagnostic, got: {msg}");
}
