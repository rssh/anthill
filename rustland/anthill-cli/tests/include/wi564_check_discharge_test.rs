//! WI-564 — `anthill check` chains the proof-discharge pass (local-proof.md
//! OQ-A/B). A green `check` now MEANS verified: it runs `load → type →
//! discharge-pending` in one invocation, reusing the same both-tier dispatch
//! `anthill prove` uses. When a relied-upon proof is not verified, `check`
//! completes but emits a loud warning (OQ-B degrade); the strict
//! `--require-proofs` flag escalates that to an error for airtight CI.
//!
//! These exercises use `by derivation` (the core SLD tier) so they need no z3 —
//! the gate behaviour they pin is solver-agnostic.

use std::path::PathBuf;
use std::process::Command;

const ANTHILL_BIN: &str = env!("CARGO_BIN_EXE_anthill");

fn write_temp(name: &str, contents: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("anthill-wi564-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, contents).unwrap();
    path
}

/// A provable `by derivation` obligation: `check` discharges it in-pass, reports
/// it proved, exits clean, and emits NO "unverified" warning.
#[test]
fn check_discharges_pending_derivation_proof() {
    let src = r#"
        namespace test.wi564.ok
          entity Light(state: String)
          fact Light(state: "bright")

          rule shines(?b) :- Light(state: ?b)
          proof shines by derivation end
        end
    "#;
    let path = write_temp("ok.anthill", src);

    let out = Command::new(ANTHILL_BIN)
        .args(["check", path.to_str().unwrap()])
        .output()
        .expect("run anthill check");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "check should succeed when every proof discharges:\nstdout:{stdout}\nstderr:{stderr}"
    );
    assert!(
        stdout.contains("shines") && stdout.contains("proved"),
        "check should discharge `shines` in-pass and report it proved; got:\n{stdout}"
    );
    assert!(
        !stderr.contains("unverified"),
        "no proof is unverified, so there must be no warning; got stderr:\n{stderr}"
    );
}

/// An unprovable obligation (`dark` has no derivation): by default `check`
/// COMPLETES (exit 0) but warns loudly — it never silently trusts.
#[test]
fn check_warns_but_completes_on_unverified_proof() {
    let src = r#"
        namespace test.wi564.warn
          entity Light(state: String)
          fact Light(state: "bright")

          rule dark(?x) :- Light(state: ?x), eq(?x, "off")
          proof dark by derivation end
        end
    "#;
    let path = write_temp("warn.anthill", src);

    let out = Command::new(ANTHILL_BIN)
        .args(["check", path.to_str().unwrap()])
        .output()
        .expect("run anthill check");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "check degrades (does NOT hard-block) on an unverified proof by default; \
         it should still exit 0:\nstdout:{stdout}\nstderr:{stderr}"
    );
    assert!(
        stderr.contains("unverified") && stderr.contains("not fully verified"),
        "an unverified relied-upon proof must surface a loud warning; got stderr:\n{stderr}"
    );
}

/// The same unprovable obligation under `--require-proofs`: the warning escalates
/// to a hard error (non-zero exit) for airtight CI.
#[test]
fn check_require_proofs_errors_on_unverified_proof() {
    let src = r#"
        namespace test.wi564.strict
          entity Light(state: String)
          fact Light(state: "bright")

          rule dark(?x) :- Light(state: ?x), eq(?x, "off")
          proof dark by derivation end
        end
    "#;
    let path = write_temp("strict.anthill", src);

    let out = Command::new(ANTHILL_BIN)
        .args(["check", "--require-proofs", path.to_str().unwrap()])
        .output()
        .expect("run anthill check --require-proofs");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !out.status.success(),
        "--require-proofs must escalate an unverified proof to a hard error:\n\
         stdout:{stdout}\nstderr:{stderr}"
    );
    assert!(
        stderr.contains("unverified") || stderr.contains("not verified"),
        "the error must explain the unverified-proof cause; got stderr:\n{stderr}"
    );
}
