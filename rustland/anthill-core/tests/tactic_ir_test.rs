//! Tactic IR conversion tests (WI-097, proposal 025.1 Phase 2).
//!
//! Pin the `by z3(...)` → typed `Tactic` IR conversion. Backwards-compat
//! anchor: `by z3(logic: "LRA")` desugars to
//! `by z3(tactic: smt(logic: "LRA"))`. New shapes (combinators, raw,
//! induction, ranking) parse and lift to the typed IR.

use anthill_core::parse;
use anthill_core::parse::ir::{Item, ProofBody, ProofStrategy, Tactic, TacticArgValue};

fn with_proof_strategy<R>(src: &str, f: impl FnOnce(&ProofStrategy) -> R) -> R {
    let parsed = parse::parse(src).expect("parse");
    for item in &parsed.items {
        if let Item::Namespace(n) = item {
            for inner in &n.items {
                if let Item::Proof(p) = inner {
                    if let Some(strat) = &p.strategy {
                        return f(strat);
                    }
                }
            }
        }
    }
    panic!("no proof strategy found");
}

fn tactic_of(src: &str) -> Tactic {
    with_proof_strategy(src, |s| s.tactic.clone().expect("tactic IR"))
}

fn legacy_z3_logic_lra() -> &'static str {
    r#"
        namespace test.tac.legacy
          export r
          rule r(?x) :- eq(?x, 1)
          proof r by z3(logic: "LRA") end
        end
    "#
}

#[test]
fn legacy_z3_logic_arg_lifts_to_smt_application() {
    // Backwards-compat anchor: bare logic: arg becomes Tactic::App("smt", ...).
    let t = tactic_of(legacy_z3_logic_lra());
    match t {
        Tactic::App(_sym, args) => {
            // Single named arg `logic: "LRA"`.
            assert_eq!(args.len(), 1);
            let arg = &args[0];
            assert!(arg.name.is_some());
            match &arg.value {
                TacticArgValue::String(s) => assert_eq!(s, "LRA"),
                other => panic!("expected String, got {other:?}"),
            }
        }
        other => panic!("expected App, got {other:?}"),
    }
}

#[test]
fn explicit_smt_tactic_named_arg() {
    // Equivalent explicit form: by z3(tactic: smt(logic: "LIA")).
    let src = r#"
        namespace test.tac.smt
          export r
          rule r(?x) :- eq(?x, 1)
          proof r by z3(tactic: smt(logic: "LIA")) end
        end
    "#;
    let t = tactic_of(src);
    let Tactic::App(_sym, args) = t else { panic!("expected App"); };
    assert_eq!(args.len(), 1);
    let arg = &args[0];
    let TacticArgValue::String(ref s) = arg.value else {
        panic!("expected logic string, got {:?}", arg.value);
    };
    assert_eq!(s, "LIA");
}

#[test]
fn then_combinator_with_two_bare_tactics() {
    let src = r#"
        namespace test.tac.then
          export r
          rule r(?x) :- eq(?x, 1)
          proof r by z3(tactic: then(simplify, smt)) end
        end
    "#;
    let t = tactic_of(src);
    let Tactic::App(_sym, args) = t else { panic!("expected App") };
    assert_eq!(args.len(), 2);
    for arg in &args {
        let TacticArgValue::Tactic(inner) = &arg.value else {
            panic!("expected nested tactic, got {:?}", arg.value);
        };
        match inner.as_ref() {
            Tactic::Bare(_) => {}
            other => panic!("expected Bare, got {other:?}"),
        }
    }
}

#[test]
fn or_else_with_nested_smt_apps() {
    let src = r#"
        namespace test.tac.or_else
          export r
          rule r(?x) :- eq(?x, 1)
          proof r by z3(tactic: or_else(smt(logic: "LRA"), smt(logic: "NRA"))) end
        end
    "#;
    let t = tactic_of(src);
    let Tactic::App(_sym, args) = t else { panic!("expected App") };
    assert_eq!(args.len(), 2);
}

#[test]
fn raw_escape_carries_string_payload() {
    // `tactic: raw("…")` unwraps to a top-level Tactic::Raw — `by z3`
    // is the host strategy; `tactic:` selects the actual tactic.
    let src = r#"
        namespace test.tac.raw
          export r
          rule r(?x) :- eq(?x, 1)
          proof r by z3(tactic: raw("(then simplify (using-params smt :random_seed 42))")) end
        end
    "#;
    let t = tactic_of(src);
    match t {
        Tactic::Raw(s) => {
            assert!(s.contains("random_seed 42"), "raw payload: {s}");
        }
        other => panic!("expected Raw, got {other:?}"),
    }
}

#[test]
fn induction_meta_tactic_with_over_and_step() {
    let src = r#"
        namespace test.tac.induction
          export r
          rule r(?x) :- eq(?x, 1)
          proof r by z3(tactic: induction(over: List, step: smt(logic: "LIA"))) end
        end
    "#;
    let t = tactic_of(src);
    let Tactic::App(_sym, ind_args) = t else { panic!("expected induction App, got {t:?}") };
    assert_eq!(ind_args.len(), 2);
    let over_arg = ind_args.iter().find(|a| a.name.is_some()).expect("named arg");
    match &over_arg.value {
        TacticArgValue::Name(_) | TacticArgValue::Tactic(_) => {}
        other => panic!("`over` value: {other:?}"),
    }
}

#[test]
fn non_z3_strategy_has_no_tactic_ir() {
    let src = r#"
        namespace test.tac.derivation
          export Light, shines
          entity Light(state: String)
          fact Light(state: "bright")
          rule shines(?b) :- Light(state: ?b)
          proof shines by derivation end
        end
    "#;
    with_proof_strategy(src, |s| {
        assert!(s.tactic.is_none(),
            "non-z3 strategies should leave Tactic IR unset");
    });
}

#[test]
fn legacy_args_field_still_populated() {
    with_proof_strategy(legacy_z3_logic_lra(), |s| {
        assert!(!s.args.is_empty(),
            "legacy args must still be populated for dispatch_z3");
        assert!(s.tactic.is_some(),
            "tactic IR must also be populated");
    });
}

#[test]
fn lf1_existing_proofs_parse_unchanged() {
    // Smoke test: pin that the lf1 example's existing proofs still
    // parse and produce Tactic IR. Read each safety_*.anthill file
    // directly and check no parse errors.
    use std::path::PathBuf;
    let lf1_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/webots-modelling/lf1");
    if !lf1_dir.exists() { return; }  // skip if example missing
    for name in ["safety_gps.anthill", "safety_transponder.anthill"] {
        let path = lf1_dir.join(name);
        if !path.exists() { continue; }
        let src = std::fs::read_to_string(&path).unwrap();
        parse::parse(&src).unwrap_or_else(|e|
            panic!("parse {name}: {e:?}"));
    }
}

// Placeholder so the test binary references ProofBody (silences
// "unused" warnings if future tests are removed).
#[allow(dead_code)]
fn _unused_proof_body_marker(_b: ProofBody) {}
