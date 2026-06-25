//! v0 obligation: discharge `comm_delay_max ≤ 0.1` for an lf1-shaped
//! KB. Five linear arithmetic operations over five user-asserted
//! constants. If this round-trips through emit_obligation, the SMT
//! foundation is solid.

use super::common::{load_kb_with, run_z3, z3_available};

use anthill_smt_gen::{emit_obligation, Obligation};

fn lf1_safety_kb() -> anthill_core::kb::KnowledgeBase {
    // Trimmed safety spec — enough for the comm_delay_max
    // obligation. Real lf1 spec adds GpsErrorBound, DistanceBounds,
    // step_distance_bound, etc.; smt-gen ignores facts outside the
    // rule's call graph.
    let source = r#"
        namespace test.smt_gen.lf1
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
        end
    "#;
    load_kb_with(source)
}

#[test]
fn comm_delay_max_emits_a_well_formed_smtlib_doc() {
    let kb = lf1_safety_kb();
    let smt = emit_obligation(&kb, &Obligation {
        rule_qn: "test.smt_gen.lf1.comm_delay_max".to_string(),
        upper_bound: 0.1,
    }).expect("emit");

    // Header
    assert!(smt.contains("(set-logic QF_LRA)"),
            "missing logic declaration:\n{smt}");
    // User-asserted constants resolved from the matching fact
    assert!(smt.contains("(define-fun range_max () Real 100.0)"),
            "range_max const missing:\n{smt}");
    assert!(smt.contains("(define-fun control_period () Real 0.032)"),
            "control_period const missing:\n{smt}");
    // Result variable bound to the rule body's RHS expression.
    // Loaded rules use de Bruijn indices, so the head's result is a
    // synthetic `var_<i>` rather than `tau` — Z3 doesn't care.
    assert!(smt.contains("(define-fun var_"),
            "result var define-fun missing:\n{smt}");
    // Obligation: assert NEGATION of the bound — Z3 should reply unsat.
    assert!(smt.contains("(assert (not (<= var_"),
            "obligation assertion missing:\n{smt}");
    assert!(smt.contains(" 0.1)))"),
            "upper bound 0.1 missing in obligation:\n{smt}");
    // Driver
    assert!(smt.contains("(check-sat)"),
            "missing (check-sat):\n{smt}");
}

/// First non-trivial check that we can actually verify and not just
/// emit syntactically-valid SMT: feed the emitted document to Z3 and
/// expect `unsat` (the obligation says comm_delay_max ≤ 0.1; the
/// computed tau is much smaller). Skipped when `z3` isn't on $PATH.
#[test]
fn comm_delay_max_z3_round_trip_unsat() {
    if !z3_available() { eprintln!("z3 not available — skipping discharge round-trip"); return; }
    let kb = lf1_safety_kb();
    let smt = emit_obligation(&kb, &Obligation {
        rule_qn: "test.smt_gen.lf1.comm_delay_max".to_string(),
        upper_bound: 0.1,
    }).expect("emit");
    let verdict = run_z3("smt_gen_comm_delay", &smt);
    assert!(
        verdict == "unsat",
        "z3 should report `unsat` for comm_delay_max ≤ 0.1 — got {verdict:?}\n{smt}"
    );
}

#[test]
fn config_overrides_logic_and_emits_timeout() {
    use anthill_smt_gen::{emit_obligation_with, ProofConfig};
    let kb = lf1_safety_kb();
    let mut config = ProofConfig::default();
    config.logic = Some("AUFLIRA".to_string());
    config.timeout_ms = Some(2500);
    let smt = emit_obligation_with(&kb, &Obligation {
        rule_qn: "test.smt_gen.lf1.comm_delay_max".to_string(),
        upper_bound: 0.1,
    }, &config).expect("emit");
    assert!(smt.contains("(set-logic AUFLIRA)"),
            "logic override not honoured:\n{smt}");
    assert!(smt.contains("(set-option :timeout 2500)"),
            "timeout option not emitted:\n{smt}");
    // Default logic must NOT appear.
    assert!(!smt.contains("(set-logic QF_LRA)"),
            "default logic leaked through override:\n{smt}");
}

#[test]
fn comm_delay_max_emits_arith_in_correct_smt_lib_order() {
    // Z3 wants prefix notation `(+ a b)`, not infix `(a + b)`.
    let kb = lf1_safety_kb();
    let smt = emit_obligation(&kb, &Obligation {
        rule_qn: "test.smt_gen.lf1.comm_delay_max".to_string(),
        upper_bound: 0.1,
    }).expect("emit");

    // The body should contain `(/ range_max signal_speed)` as the
    // propagation-delay sub-expression, NOT `(range_max / ...)`.
    assert!(
        smt.contains("(/ range_max signal_speed)"),
        "expected prefix-notation division of range_max / signal_speed:\n{smt}"
    );
    // And `(* packet_size byte_size)` for the bit count.
    assert!(
        smt.contains("(* packet_size byte_size)"),
        "expected (* packet_size byte_size) for the bit-count expression:\n{smt}"
    );
}
