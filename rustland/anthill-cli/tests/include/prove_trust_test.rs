//! Phase γ follow-up (proposal 030, WI-136): the `by trust("reason")`
//! tactic produces a TrustedAxiom-witnessed ProofRecord. Citing
//! such a rule via `using` succeeds with a trust warning that
//! surfaces the recorded reason.

use std::path::PathBuf;
use std::process::Command;

const ANTHILL_BIN: &str = env!("CARGO_BIN_EXE_anthill");

fn z3_available() -> bool {
    Command::new("z3").arg("--version").output()
        .map(|o| o.status.success()).unwrap_or(false)
}

fn write_temp(name: &str, contents: &str) -> PathBuf {
    let dir = std::env::temp_dir()
        .join(format!("anthill-trust-test-{}-{}", std::process::id(), name));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, contents).unwrap();
    path
}

#[test]
fn trust_tactic_discharges_with_reason() {
    let src = r#"
        namespace test.trust.basic

          rule geometric_law: gte(?x, 0.0)
            :- gte(?x, 0.0)

          proof geometric_law
            by trust(reason: "axiom by construction; identity claim")
          end
        end
    "#;
    let path = write_temp("trust_basic.anthill", src);
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "--no-cache"])
        .output().expect("anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("test.trust.basic.geometric_law: proved"),
        "trust tactic must discharge rule as Proved:\n{stdout}");
    assert!(out.status.success(), "prove must exit zero on a trust-discharged rule");
}

#[test]
fn citing_trusted_rule_warns_but_proceeds() {
    if !z3_available() { return; }
    // `axiom_lemma` is trust-discharged; `consumer` cites it via
    // `using` and runs through Z3. The cite-resolution should
    // resolve to Trusted (not NotFound / Pending), Z3 should still
    // get the lifted hypothesis, and the prove driver should print
    // a warning naming the trust reason.
    let src = r#"
        namespace test.trust.cite

          rule axiom_lemma: gte(?x, 3.0)
            :- gte(?x, 5.0)

          rule consumer: gte(?x, 3.0)
            :- gte(?x, 5.0)

          proof axiom_lemma
            by trust(reason: "load-bearing physical assumption")
          end

          proof consumer
            using axiom_lemma
            by z3(logic: "LRA")
          end
        end
    "#;
    let path = write_temp("trust_cite.anthill", src);
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "--no-cache"])
        .output().expect("anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stdout.contains("test.trust.cite.axiom_lemma: proved"),
        "trust-discharged lemma must be Proved:\n{stdout}");
    assert!(stdout.contains("test.trust.cite.consumer: proved"),
        "consumer must discharge under the trusted hypothesis:\n{stdout}");
    // The trust reason surfaces as a stderr warning at cite time.
    assert!(stderr.contains("TrustedAxiom") || stderr.contains("load-bearing"),
        "expected the trust warning to surface in stderr:\n{stderr}");
}
