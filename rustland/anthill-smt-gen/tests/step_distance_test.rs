//! Discharge `step_distance_bound ≤ <bound>` for an lf1-shaped KB.
//! Exercises the recursive-rule-call path: `step_distance_bound`'s
//! body references `comm_delay_max(?tau)`, which is itself a derived
//! rule with its own body. The smt-gen has to chase that dependency
//! and inline it into the outer rule's translation.

use super::common::load_kb_with;

use anthill_smt_gen::{emit_obligation, Obligation};

fn lf1_with_step_bound_kb() -> anthill_core::kb::KnowledgeBase {
    // Concrete numbers chosen so the obligation is comfortably
    // discharged. With:
    //   v_L = v_F = 8 m/s, T_c = 0.032 s,
    //   epsilon = 1.5 m,
    //   comm_delay_max ≈ 0.032 + tiny ≈ 0.032 s
    // we get:
    //   delta = (8+8)*0.032 + 4*1.5 + 0.032*8
    //         = 0.512 + 6.0 + 0.256
    //         ≈ 6.77 m
    // The obligation `delta ≤ 7.0` should discharge; `delta ≤ 6.0`
    // should NOT (Z3 finds a counterexample).
    let source = r#"
        namespace test.smt_gen.step
          import anthill.prelude.{Float, Int64}
          import anthill.prelude.Numeric.{add, mul}
          import anthill.prelude.Float.{div}


          entity LinkParameters(
            range_max:    Float,
            signal_speed: Float,
            baud_rate:    Float,
            byte_size:    Int64,
            packet_size:  Int64
          )

          entity KinematicAssumptions(
            leader_speed_max:    Float,
            follower_speed_max:  Float,
            control_period:      Float,
            sensor_period:       Float
          )

          entity GpsErrorBound(epsilon: Float)

          rule comm_delay_max(?tau)
            :- LinkParameters(range_max: ?r,
                              signal_speed: ?c,
                              baud_rate: ?br,
                              byte_size: ?bs,
                              packet_size: ?ps),
               KinematicAssumptions(control_period: ?tc),
               ?prop  = div(?r, ?c),
               ?bits  = mul(?ps, ?bs),
               ?trans = div(?bits, ?br),
               ?sum1  = add(?prop, ?trans),
               ?tau   = add(?sum1, ?tc)

          rule step_distance_bound(?delta)
            :- KinematicAssumptions(leader_speed_max:    ?vL,
                                    follower_speed_max:  ?vF,
                                    control_period:      ?tc),
               GpsErrorBound(epsilon: ?eps),
               comm_delay_max(?tau),
               ?phys     = mul(add(?vL, ?vF), ?tc),
               ?gps_term = mul(4.0, ?eps),
               ?stale    = mul(?tau, ?vL),
               ?sum1     = add(?phys, ?gps_term),
               ?delta    = add(?sum1, ?stale)

          fact LinkParameters(
            range_max:    100.0,
            signal_speed: 300000000.0,
            baud_rate:    1000000.0,
            byte_size:    8,
            packet_size:  32
          )

          fact KinematicAssumptions(
            leader_speed_max:    8.0,
            follower_speed_max:  8.0,
            control_period:      0.032,
            sensor_period:       0.008
          )

          fact GpsErrorBound(epsilon: 1.5)
        end
    "#;
    load_kb_with(source)
}

#[test]
fn step_distance_bound_inlines_called_rule() {
    let kb = lf1_with_step_bound_kb();
    let smt = emit_obligation(&kb, &Obligation {
        rule_qn: "test.smt_gen.step.step_distance_bound".to_string(),
        upper_bound: 7.0,
    }).expect("emit");

    // The inlined comm_delay_max body should appear in the
    // step_distance_bound expression — concretely, the propagation
    // term `(/ range_max signal_speed)` from the called rule.
    assert!(
        smt.contains("(/ range_max signal_speed)"),
        "comm_delay_max body should be inlined into step bound:\n{smt}"
    );
    // And the GPS term `(* 4.0 epsilon)` should appear.
    assert!(
        smt.contains("(* 4.0 epsilon)"),
        "GPS noise term `(* 4.0 epsilon)` missing:\n{smt}"
    );
    // Three entities ⇒ three sets of consts.
    assert!(smt.contains("(define-fun epsilon () Real 1.5)"),
            "epsilon const missing:\n{smt}");
    assert!(smt.contains("(define-fun leader_speed_max () Real 8.0)"),
            "leader_speed_max const missing:\n{smt}");
    assert!(smt.contains("(define-fun range_max () Real 100.0)"),
            "range_max const missing:\n{smt}");
}

#[test]
fn step_distance_bound_z3_says_unsat_at_seven_meters() {
    if std::process::Command::new("z3").arg("--version").output()
        .map(|o| !o.status.success()).unwrap_or(true)
    {
        eprintln!("z3 not available — skipping");
        return;
    }
    let kb = lf1_with_step_bound_kb();
    let smt = emit_obligation(&kb, &Obligation {
        rule_qn: "test.smt_gen.step.step_distance_bound".to_string(),
        upper_bound: 7.0,
    }).expect("emit");
    let path = std::env::temp_dir().join("anthill_smt_gen_step_unsat.smt2");
    std::fs::write(&path, &smt).expect("write");
    let out = std::process::Command::new("z3").arg(&path).output().expect("z3");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.trim() == "unsat",
        "z3 should report `unsat` for delta ≤ 7.0 — got {stdout:?}\n{smt}"
    );
}

#[test]
fn step_distance_bound_z3_says_sat_at_six_meters() {
    // Sanity-check the discharge mechanism: with delta ≈ 6.77 m,
    // the bound `delta ≤ 6.0` is genuinely false, and Z3 should
    // produce `sat` (a counterexample exists). If both bounds gave
    // `unsat`, the obligation translation would be vacuous.
    if std::process::Command::new("z3").arg("--version").output()
        .map(|o| !o.status.success()).unwrap_or(true)
    {
        eprintln!("z3 not available — skipping");
        return;
    }
    let kb = lf1_with_step_bound_kb();
    let smt = emit_obligation(&kb, &Obligation {
        rule_qn: "test.smt_gen.step.step_distance_bound".to_string(),
        upper_bound: 6.0,
    }).expect("emit");
    let path = std::env::temp_dir().join("anthill_smt_gen_step_sat.smt2");
    std::fs::write(&path, &smt).expect("write");
    let out = std::process::Command::new("z3").arg(&path).output().expect("z3");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.trim() == "sat",
        "z3 should report `sat` (counterexample) for delta ≤ 6.0 — got {stdout:?}\n{smt}"
    );
}
