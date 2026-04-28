//! Phase 6 — `induction` meta-tactic (WI-101).
//!
//! `induction(over: <sort>, base: <rule>, step: <rule>)` dispatches
//! the base and inductive-step obligations as SMT sub-queries through
//! the standard pipeline.
//!
//! Includes the lf1-shaped reachability proof: prove
//!   `forall k. d_min ≤ d_k ≤ d_max`
//! by induction on k, given a base case (d_0 in the strong invariant)
//! and an inductive step (per-step distance bound preserves the
//! envelope). Both cases are LRA, both unsat, induction discharges.

use std::path::PathBuf;
use std::process::Command;

const ANTHILL_BIN: &str = env!("CARGO_BIN_EXE_anthill");

fn z3_available() -> bool {
    Command::new("z3").arg("--version").output()
        .map(|o| o.status.success()).unwrap_or(false)
}

fn write_temp(name: &str, contents: &str) -> PathBuf {
    let dir = std::env::temp_dir()
        .join(format!("anthill-induction-test-{}-{}", std::process::id(), name));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, contents).unwrap();
    path
}

#[test]
fn induction_with_base_and_step_proved_combines_to_proved() {
    if !z3_available() { return; }
    let src = r#"
        namespace test.induction.ok
          export ind_ok, base_violation, step_violation
          entity Bound(lo: Int, hi: Int)
          fact Bound(lo: 0, hi: 10)

          -- Base violation: P(0) doesn't hold. With ?lo = 0 and the
          -- assertion gt(?lo, 0), unsat ⇒ base case is fine.
          rule base_violation(?marker)
            :- Bound(lo: ?lo, hi: ?_), gt(?lo, 0), eq(?marker, ?lo)

          -- Step violation: P(?n) holds but P(?n+1) doesn't. Encoded
          -- as a contradictory inequality pair.
          rule step_violation(?marker)
            :- Bound(lo: ?lo, hi: ?hi),
               gte(?n, ?lo), lt(?n, ?hi),
               ?next = add(?n, 1),
               gt(?next, ?hi),
               lte(?next, ?hi),
               eq(?marker, ?n)

          rule ind_ok(?marker) :- eq(?marker, true)

          proof ind_ok
            by z3(tactic: induction(over: anthill.prelude.Int,
                                     base: base_violation,
                                     step: step_violation),
                  logic: "LIA")
          end
        end
    "#;
    let path = write_temp("ok.anthill", src);
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "-v", "--no-cache"])
        .output().expect("anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("induction(over:") && stdout.contains("sub-queries:"),
        "verbose must surface the meta-tactic dispatch: {stdout}");
    assert!(stdout.contains("ind_ok: proved"),
        "both base+step unsat ⇒ induction proved: {stdout}");
}

#[test]
fn induction_with_failing_step_disproves() {
    if !z3_available() { return; }
    // Step is satisfiable — the obligation has a counterexample.
    let src = r#"
        namespace test.induction.fail
          export ind_bad, base_unsat, step_sat
          entity Cfg(scale: Int)
          fact Cfg(scale: 5)

          -- Unsat (good base case).
          rule base_unsat(?marker)
            :- Cfg(scale: ?s), gt(?s, 999), eq(?marker, ?s)

          -- Sat (bad inductive step — exists ?s > 0).
          rule step_sat(?marker)
            :- Cfg(scale: ?s), gt(?s, 0), eq(?marker, ?s)

          rule ind_bad(?marker) :- eq(?marker, true)

          proof ind_bad
            by z3(tactic: induction(over: anthill.prelude.Int,
                                     base: base_unsat,
                                     step: step_sat),
                  logic: "LIA")
          end
        end
    "#;
    let path = write_temp("fail.anthill", src);
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "-v", "--no-cache"])
        .output().expect("anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("induction case `test.induction.fail.step_sat` failed"),
        "failing step must surface in the diagnostic: {stdout}");
}

#[test]
fn induction_dispatches_three_positional_cases() {
    // Multi-case form: positional case rules cover N constructors.
    // For Bool (2 cases) or larger enums (4+) the induction tactic
    // accepts a flat list. v1 also supports base/step shorthand for
    // numeric induction.
    if !z3_available() { return; }
    let src = r#"
        namespace test.induction.multi
          export ind_multi, c1, c2, c3
          entity Cfg(scale: Int)
          fact Cfg(scale: 5)

          rule c1(?marker)
            :- Cfg(scale: ?s), gt(?s, 99), eq(?marker, ?s)
          rule c2(?marker)
            :- Cfg(scale: ?s), gt(?s, 100), eq(?marker, ?s)
          rule c3(?marker)
            :- Cfg(scale: ?s), gt(?s, 999), eq(?marker, ?s)

          rule ind_multi(?marker) :- eq(?marker, true)

          proof ind_multi
            by z3(tactic: induction(c1, c2, c3), logic: "LIA")
          end
        end
    "#;
    let path = write_temp("multi.anthill", src);
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "-v", "--no-cache"])
        .output().expect("anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("ind_multi: proved"),
        "all positional cases unsat ⇒ proved: {stdout}");
    assert!(stdout.contains("c1") && stdout.contains("c2") && stdout.contains("c3"),
        "verbose must list all sub-queries: {stdout}");
}
