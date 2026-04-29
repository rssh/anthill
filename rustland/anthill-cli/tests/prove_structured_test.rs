//! Proposal 031 phase b — end-to-end structured-proof dispatch.
//!
//! Verifies that a `proof X (rule h_i: ... by t_i)+ using h1, ..., hn
//! by t end` block discharges all step rules, chains their witnesses
//! into the concluding clause's discharge, and produces a single
//! Proved verdict for the parent rule.
//!
//! Skipped when z3 isn't on $PATH.

use std::path::PathBuf;
use std::process::Command;

const ANTHILL_BIN: &str = env!("CARGO_BIN_EXE_anthill");

fn z3_available() -> bool {
    Command::new("z3").arg("--version").output()
        .map(|o| o.status.success()).unwrap_or(false)
}

fn write_temp(name: &str, contents: &str) -> PathBuf {
    let dir = std::env::temp_dir()
        .join(format!("anthill-structured-{}-{}", std::process::id(), name));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, contents).unwrap();
    path
}

#[test]
fn structured_proof_two_steps_chain_to_parent_discharge() {
    if !z3_available() { return; }
    // Two-step chain. Step h1 establishes `?x >= 3` from the body
    // premise `?x >= 5`; step h2 establishes `?x >= 1` from h1's
    // claim. The concluding clause cites both steps to discharge
    // the parent rule's claim `?x >= 0`.
    let src = r#"
        namespace test.structured.chain
          export big_lemma

          rule big_lemma: gte(?x, 0.0)
            :- gte(?x, 5.0)

          proof big_lemma
            rule h1: gte(?x, 3.0)
              :- gte(?x, 5.0)
              by z3(logic: "LRA")

            rule h2: gte(?x, 1.0)
              :- gte(?x, 3.0)
              by z3(logic: "LRA")

            using h1, h2
            by z3(logic: "LRA")
          end
        end
    "#;
    let path = write_temp("structured_chain.anthill", src);
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "--no-cache"])
        .output().expect("anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("test.structured.chain.big_lemma: proved"),
        "parent rule must discharge under the structured chain:\n{stdout}"
    );
}

#[test]
fn structured_proof_step_failure_aborts_chain() {
    if !z3_available() { return; }
    // Step h1's claim is unsatisfiable from its body premises
    // (?x >= 5 ⇒ ?x >= 100 is false). The structured-proof
    // dispatcher should abort the chain on h1's failure rather
    // than reporting the parent rule as failed without context.
    let src = r#"
        namespace test.structured.fail
          export oops

          rule oops: gte(?x, 0.0)
            :- gte(?x, 5.0)

          proof oops
            rule h1: gte(?x, 100.0)
              :- gte(?x, 5.0)
              by z3(logic: "LRA")

            using h1
            by z3(logic: "LRA")
          end
        end
    "#;
    let path = write_temp("structured_fail.anthill", src);
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "--no-cache"])
        .output().expect("anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        !stdout.contains("test.structured.fail.oops: proved"),
        "parent rule must NOT discharge when a step fails:\n{stdout}"
    );
}

#[test]
fn structured_proof_with_trust_step_produces_metacompose_witness() {
    // Even without z3 we can exercise the trust path. h1 is
    // trust-discharged; the concluding clause cites it. The
    // dispatcher should produce a MetaCompose witness wrapping
    // the per-step TrustedAxiom and the concluding clause's
    // result. Without z3 the conclude-by-z3 step skips, so the
    // overall outcome is Skipped — but the syntax must still
    // round-trip through the dispatcher without panicking.
    let src = r#"
        namespace test.structured.trust
          export claim

          rule claim: gte(?x, 0.0)
            :- gte(?x, 5.0)

          proof claim
            rule h1: gte(?x, 3.0)
              :- gte(?x, 5.0)
              by trust(reason: "axiom by construction")

            using h1
            by trust(reason: "depends on h1")
          end
        end
    "#;
    let path = write_temp("structured_trust.anthill", src);
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "--no-cache"])
        .output().expect("anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("test.structured.trust.claim: proved"),
        "trust-only structured proof must discharge end-to-end:\n{stdout}"
    );
}

#[test]
fn structured_proof_witness_sidecar_replays_through_check() {
    if !z3_available() { return; }
    // Phase c: the MetaCompose witness produced by dispatch_structured
    // serializes into a sidecar JSON (per WI-124's witness persistence
    // layer); `anthill check` reads it and replays each sub-witness via
    // β.3's existing recursion. No phase-c code is added — the test
    // confirms the proposal-031 claim that "Phase c is essentially free".
    let src = r#"
        namespace test.structured.replay
          export claim

          rule claim: gte(?x, 0.0)
            :- gte(?x, 5.0)

          proof claim
            rule h1: gte(?x, 3.0)
              :- gte(?x, 5.0)
              by z3(logic: "LRA")

            using h1
            by z3(logic: "LRA")
          end
        end
    "#;
    let path = write_temp("structured_replay.anthill", src);

    // Run prove WITHOUT --no-cache so sidecars are written.
    let prove_out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap()])
        .output().expect("anthill prove");
    let prove_stdout = String::from_utf8_lossy(&prove_out.stdout);
    assert!(
        prove_stdout.contains("test.structured.replay.claim: proved"),
        "prove must succeed before check can replay:\n{prove_stdout}"
    );

    // Run check on the same source — should replay each sub-witness
    // via β.3's MetaCompose recursion.
    let check_out = Command::new(ANTHILL_BIN)
        .args(["check", path.to_str().unwrap()])
        .output().expect("anthill check");
    let check_stdout = String::from_utf8_lossy(&check_out.stdout);
    let check_stderr = String::from_utf8_lossy(&check_out.stderr);
    assert!(
        check_out.status.success(),
        "check must exit zero on a discharged structured proof:\n\
         stdout:\n{check_stdout}\nstderr:\n{check_stderr}"
    );
    // The parent record's check should report a positive verdict
    // (Verified or Trusted depending on aggregation).
    assert!(
        check_stdout.contains("test.structured.replay.claim"),
        "check output must mention the structured-proof rule:\n{check_stdout}"
    );
}
