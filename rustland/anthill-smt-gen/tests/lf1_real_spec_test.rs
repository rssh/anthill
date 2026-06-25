//! Discharge against the actual lf1 spec on disk — not a
//! test-scaffold inline source. Loads
//! `examples/webots-modelling/lf1/safety_*.anthill` (and their
//! dependencies) into a KB, runs smt-gen against the violation
//! rules, asserts Z3 reports `unsat` for both sides of the envelope.
//!
//! This is the proof-as-CI artifact: any edit to safety_gps.anthill /
//! safety_transponder.anthill that breaks the inductive step
//! (loosening the precondition, tightening the bounds, weakening
//! the sensor-error assumption) will surface here as `sat` with a
//! counterexample model.
//!
//! The transponder follower's d_max upper bound is *not* a per-step
//! inductive invariant (extremum-seeking yaw flips can transiently
//! drive the follower outward). That *bounded-excursion* obligation is
//! now discharged in-language by the ranking meta-tactic — see
//! `proof post_armed_excursion_bound by z3(tactic: ranking(...))` in
//! `examples/webots-modelling/lf1/safety_transponder.anthill`, run via
//! `discharge.sh`. The earlier hand-written
//! `lf1_transponder_excursion_ranking_function_manual` worked example
//! that lived here was obsoleted by that proof (proposal 025.1 Phase 5 /
//! WI-100) and removed in Phase 8 (WI-103).

use std::path::PathBuf;

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;
use anthill_core::parse::ir::ParsedFile;

use super::common::{self, collect_anthill_files};
use anthill_smt_gen::emit_satisfiability_check;

/// Build a KB with stdlib + the actual lf1 spec directory on disk.
fn lf1_kb() -> KnowledgeBase {
    let lf1_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/webots-modelling/lf1");
    let stdlib_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../stdlib/anthill");

    let mut all_files = collect_anthill_files(&stdlib_root);
    all_files.extend(collect_anthill_files(&lf1_root));

    let parsed: Vec<ParsedFile> = all_files.iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src)
                .unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    let refs: Vec<&ParsedFile> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let _ = load::load_all(&mut kb, &refs, &NullResolver);
    kb
}

#[test]
fn lf1_lower_violation_is_unsat() {
    if !common::z3_available() { eprintln!("z3 not available — skipping"); return; }
    let kb = lf1_kb();
    let smt = emit_satisfiability_check(
        &kb, "anthill.examples.lf1.safety.gps.lower_violation"
    ).expect("emit lower_violation");
    let verdict = common::run_z3("lf1_lower_violation", &smt);
    assert_eq!(
        verdict, "unsat",
        "lf1 lower_violation should be unsat (no underflow possible) \
         — got {verdict:?}\n\n{smt}"
    );
}

#[test]
fn lf1_upper_violation_is_unsat() {
    if !common::z3_available() { eprintln!("z3 not available — skipping"); return; }
    let kb = lf1_kb();
    let smt = emit_satisfiability_check(
        &kb, "anthill.examples.lf1.safety.gps.upper_violation"
    ).expect("emit upper_violation");
    let verdict = common::run_z3("lf1_upper_violation", &smt);
    assert_eq!(
        verdict, "unsat",
        "lf1 upper_violation should be unsat (no overflow possible) \
         — got {verdict:?}\n\n{smt}"
    );
}

#[test]
fn lf1_step_distance_bound_is_within_two_meters() {
    if !common::z3_available() { eprintln!("z3 not available — skipping"); return; }
    // With the lf1 facts (RTK-quality eps=0.1, v_max=8, T_c=0.032)
    // the step bound should compute to:
    //   delta = (8+8)*0.032 + 4*0.1 + tau*8 ≈ 0.512 + 0.4 + 0.256
    //         ≈ 1.17 m
    // Discharge against the loose bound 2.0 m. (Tighter bounds
    // make sat a counterexample: useful for the diagnostic but not
    // the safety claim.)
    use anthill_smt_gen::{emit_obligation, Obligation};
    let kb = lf1_kb();
    let smt = emit_obligation(&kb, &Obligation {
        rule_qn: "anthill.examples.lf1.safety.gps.step_distance_bound".to_string(),
        upper_bound: 2.0,
    }).expect("emit");
    let verdict = common::run_z3("lf1_step_bound", &smt);
    assert_eq!(
        verdict, "unsat",
        "step_distance_bound should fit under 2.0 m for lf1 — got {verdict:?}\n\n{smt}"
    );
}
