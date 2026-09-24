//! A witness sidecar is evidence about the KB `anthill prove` ran against. Once
//! the rules or facts that proof consulted change, the sidecar no longer speaks
//! for the current KB, and its readers must say so:
//!
//!   * `anthill check` reports it STALE (`~ … STALE`), not `✓`. Replaying its SMT
//!     document cannot tell: it re-proves the OLD obligation, which stays unsat
//!     however the source changed. `--report-stale` lists it.
//!   * `anthill prove` refuses to discharge a `using` cite through it.
//!
//! Every test runs the CLI with its own cache (`ANTHILL_CACHE_DIR`) and working
//! directory — the witness directory is keyed by the working directory — so runs
//! neither share sidecars nor touch the user's cache.
//!
//! What fails when a piece is backed out (the pre-edit controls pass either way):
//!   * no staleness read — the first three tests, at their post-edit assertion;
//!   * no warning when a filtered `check` leaves a stale record unverified — the
//!     derivation test's `--filter` assertions;
//!   * no record of a lemma that failed in this run — the failed-cite test;
//!   * staleness judged under `--report-trust` — the trust-report test.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const ANTHILL_BIN: &str = env!("CARGO_BIN_EXE_anthill");

fn z3_available() -> bool {
    Command::new("z3")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// A fresh project directory holding `src` as `p.anthill`.
fn project(name: &str, src: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("anthill-stale-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("p.anthill"), src).unwrap();
    dir
}

fn edit(dir: &Path, from: &str, to: &str) {
    let path = dir.join("p.anthill");
    let src = std::fs::read_to_string(&path).unwrap();
    assert!(src.contains(from), "fixture must contain `{from}`");
    std::fs::write(&path, src.replace(from, to)).unwrap();
}

fn anthill(dir: &Path, args: &[&str]) -> Output {
    Command::new(ANTHILL_BIN)
        .args(args)
        .arg("p.anthill")
        .current_dir(dir)
        .env("ANTHILL_CACHE_DIR", dir.join("cache"))
        .output()
        .expect("run anthill")
}

fn stdout(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn both(o: &Output) -> String {
    format!(
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&o.stdout),
        String::from_utf8_lossy(&o.stderr)
    )
}

fn stale_line(qn: &str) -> String {
    format!("~ {qn}: STALE")
}

/// Solver-free: a `by derivation` sidecar goes stale when the fact it derived
/// from changes. The proof still holds after the edit — staleness is about the
/// evidence, not the claim — so this also pins that the full `check` re-proves
/// it and exits clean.
#[test]
fn check_reports_a_derivation_sidecar_stale_after_its_fact_changes() {
    let dir = project(
        "derivation",
        r#"
        namespace test.stale.derivation
          entity Light(state: String)
          fact Light(state: "bright")

          rule shines(?b) :- Light(state: ?b)
          proof shines by derivation end
        end
    "#,
    );
    let qn = "test.stale.derivation.shines";

    let proved = anthill(&dir, &["prove"]);
    assert!(proved.status.success(), "prove failed: {}", both(&proved));

    // Control: nothing changed, nothing stale.
    let fresh = anthill(&dir, &["check", "--report-stale"]);
    assert!(
        stdout(&fresh).contains("0 stale") && !stdout(&fresh).contains(&stale_line(qn)),
        "an unchanged KB must report no stale sidecar: {}",
        both(&fresh)
    );

    edit(&dir, r#"Light(state: "bright")"#, r#"Light(state: "dim")"#);

    let listed = anthill(&dir, &["check", "--report-stale"]);
    assert!(
        stdout(&listed).contains(&stale_line(qn)) && stdout(&listed).contains("1 stale"),
        "--report-stale must list the sidecar whose fact changed: {}",
        both(&listed)
    );

    // A filtered check skips the discharge pass, so nothing re-verifies the stale
    // record: it is an unverified proof — warned about, and an error under
    // `--require-proofs` (WI-564's OQ-B), never a silent exit 0.
    let filter = "test.stale.derivation.*";
    let filtered = anthill(&dir, &["check", "--filter", filter]);
    assert!(
        filtered.status.success()
            && String::from_utf8_lossy(&filtered.stderr).contains("stale proof(s) not re-verified"),
        "a filtered check must warn that the stale record went unverified: {}",
        both(&filtered)
    );
    let strict = anthill(&dir, &["check", "--filter", filter, "--require-proofs"]);
    assert!(
        !strict.status.success(),
        "--require-proofs must refuse a stale record nothing re-verified: {}",
        both(&strict)
    );

    // Stale is not a failure: the chained discharge re-proves `shines` against
    // the current KB (and rewrites the sidecar), so `check` exits 0.
    let checked = anthill(&dir, &["check"]);
    assert!(
        checked.status.success() && stdout(&checked).contains(&stale_line(qn)),
        "check must report the stale sidecar and still exit 0 once re-proved: {}",
        both(&checked)
    );
    let after = anthill(&dir, &["check", "--report-stale"]);
    assert!(
        stdout(&after).contains("0 stale"),
        "the re-proof must leave a fresh sidecar behind: {}",
        both(&after)
    );
}

/// The reported bug: after an edit that makes an SMT proof FALSE, the witness
/// replay printed `✓` — it re-ran the recorded document, which is still unsat.
#[test]
fn check_does_not_pass_an_smt_sidecar_the_kb_has_moved_on_from() {
    if !z3_available() {
        eprintln!("skipping: z3 not on $PATH");
        return;
    }
    let dir = project(
        "smt",
        r#"
        namespace test.stale.smt
          import anthill.prelude.PartialEq.{eq}
          import anthill.prelude.PartialOrd.{gt}
          entity Cfg(scale: Int64)
          fact Cfg(scale: 5)

          rule simple_unsat(?marker)
            :- Cfg(scale: ?s), gt(?s, 99), eq(?marker, ?s)

          proof simple_unsat by z3(logic: "LIA") end
        end
    "#,
    );
    let qn = "test.stale.smt.simple_unsat";
    let replay_pass = format!("✓ {qn}");

    let proved = anthill(&dir, &["prove"]);
    assert!(proved.status.success(), "prove failed: {}", both(&proved));

    // Control: the replay passes the fresh sidecar.
    let fresh = anthill(&dir, &["check"]);
    assert!(
        stdout(&fresh).lines().any(|l| l == replay_pass),
        "an unchanged KB must replay the sidecar to a pass: {}",
        both(&fresh)
    );

    edit(&dir, "fact Cfg(scale: 5)", "fact Cfg(scale: 500)");

    let checked = anthill(&dir, &["check"]);
    let out = stdout(&checked);
    assert!(
        !out.lines().any(|l| l == replay_pass),
        "a sidecar for a proof the edit made false must not replay to `✓`: {}",
        both(&checked)
    );
    assert!(
        out.contains(&stale_line(qn)),
        "it must be reported stale instead: {}",
        both(&checked)
    );
}

/// A `using` cite resolved through a sidecar is refused once the cited proof's
/// slice changed — `prove --rule` does not dispatch the cited rule, so the
/// sidecar is all it has.
#[test]
fn prove_refuses_a_cite_whose_sidecar_is_stale() {
    if !z3_available() {
        eprintln!("skipping: z3 not on $PATH");
        return;
    }
    let dir = project(
        "cite",
        r#"
        namespace test.stale.cite
          import anthill.prelude.PartialOrd.{gte, lt}

          rule bound_d: gte(?x, 3.0)
            :- gte(?x, 5.0)

          rule target_violation: ⊥
            :- gte(?x, 5.0),
               lt(?x, 3.0)

          proof bound_d
            by z3(logic: "LRA")
          end

          proof target_violation
            using bound_d
            by z3(logic: "LRA")
          end
        end
    "#,
    );
    let target = "test.stale.cite.target_violation";

    let proved = anthill(&dir, &["prove"]);
    assert!(proved.status.success(), "prove failed: {}", both(&proved));

    // Control: the cite resolves through the fresh sidecar.
    let fresh = anthill(&dir, &["prove", "--rule", target]);
    assert!(
        stdout(&fresh).contains(&format!("{target}: proved")),
        "an unchanged cited proof must still discharge the cite: {}",
        both(&fresh)
    );

    // Still provable — the cite is refused because its evidence is out of date,
    // not because the lemma became false.
    edit(&dir, ":- gte(?x, 5.0)\n", ":- gte(?x, 6.0)\n");

    let refused = anthill(&dir, &["prove", "--rule", target]);
    let text = both(&refused);
    assert!(
        text.contains("cite `test.stale.cite.bound_d`") && text.contains("is stale"),
        "a cite through a stale sidecar must be refused, naming the cite: {text}"
    );
    assert!(
        !stdout(&refused).contains(&format!("{target}: proved")),
        "the target must not discharge through the stale cite: {text}"
    );
}

/// A lemma whose proof FAILED earlier in this run is not citable, even though
/// its sidecar from an earlier run still hashes as fresh: the tactic is outside
/// the recorded slice, so changing it does not stale the sidecar.
#[test]
fn prove_refuses_a_cite_whose_lemma_failed_in_this_run() {
    if !z3_available() {
        eprintln!("skipping: z3 not on $PATH");
        return;
    }
    let dir = project(
        "failed-cite",
        r#"
        namespace test.stale.failed
          import anthill.prelude.PartialOrd.{gte, lt}

          rule bound_d: gte(?x, 3.0)
            :- gte(?x, 5.0)

          rule target_violation: ⊥
            :- gte(?x, 5.0),
               lt(?x, 3.0)

          proof bound_d
            by z3(logic: "LRA")
          end

          proof target_violation
            using bound_d
            by z3(logic: "LRA")
          end
        end
    "#,
    );
    let target = "test.stale.failed.target_violation";

    let proved = anthill(&dir, &["prove"]);
    assert!(proved.status.success(), "prove failed: {}", both(&proved));

    // `bound_d` over Reals under a bit-vector logic: z3 rejects the document.
    let path = dir.join("p.anthill");
    let src = std::fs::read_to_string(&path).unwrap();
    std::fs::write(
        &path,
        src.replacen(r#"by z3(logic: "LRA")"#, r#"by z3(logic: "QF_BV")"#, 1),
    )
    .unwrap();

    // Control: the sidecar is not stale — only the discharge is broken.
    let fresh = anthill(&dir, &["check", "--report-stale"]);
    assert!(
        stdout(&fresh).contains("0 stale"),
        "a tactic change is outside the recorded slice: {}",
        both(&fresh)
    );

    let run = anthill(&dir, &["prove"]);
    let text = both(&run);
    assert!(
        text.contains("cite `test.stale.failed.bound_d`") && text.contains("did not prove in this run"),
        "a cite of a lemma that just failed must be refused: {text}"
    );
    assert!(
        !stdout(&run).contains(&format!("{target}: proved")),
        "the target must not discharge through the failed lemma's old sidecar: {text}"
    );
}

/// `--report-trust` inventories what witness trees TRUST; a stale sidecar still
/// records that, so staleness must not drop it from the report.
#[test]
fn report_trust_still_lists_a_stale_trusted_proof() {
    if !z3_available() {
        eprintln!("skipping: z3 not on $PATH");
        return;
    }
    let dir = project(
        "trust",
        r#"
        namespace test.stale.trust
          import anthill.prelude.PartialOrd.{gte}

          rule big_lemma: gte(?x, 0.0)
            :- gte(?x, 5.0)

          proof big_lemma
            rule h1: gte(?x, 3.0)
              :- gte(?x, 5.0)
              by trust(reason: "test trust step")
            using h1
            by z3(logic: "LRA")
          end
        end
    "#,
    );
    let qn = "test.stale.trust.big_lemma";
    let trusted = format!("⚠ {qn}: trusted axiom (structured: [0] test trust step)");

    let proved = anthill(&dir, &["prove"]);
    assert!(proved.status.success(), "prove failed: {}", both(&proved));

    edit(&dir, "    :- gte(?x, 5.0)\n\n", "    :- gte(?x, 6.0)\n\n");
    let listed = anthill(&dir, &["check", "--report-stale"]);
    assert!(
        stdout(&listed).contains(&stale_line(qn)),
        "control: the edit must make the sidecar stale: {}",
        both(&listed)
    );

    let report = anthill(&dir, &["check", "--report-trust"]);
    assert!(
        stdout(&report).contains(&trusted),
        "the stale proof's trust dependency must still be reported: {}",
        both(&report)
    );
}
