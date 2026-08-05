//! WI-669 inc-1b — end-to-end: `anthill prove` discharges a property about a
//! BODIED operation with NO hand-written `<=>`/`ite` twin.
//!
//! The proof calls the bodied op relationally in its body (`Ops.clamp(?x, ?r)`).
//! The prove driver's WI-669 seam scans the obligation body, finds the rule-less
//! bodied `clamp`, and synthesizes a defining rule from the body-derived
//! equations (refolded to a nested `Expr::If`); the WI-680 smt-gen conditional
//! lowering then emits it as `(ite …)`. `grade` additionally exercises the
//! nested-`if` refold (`and`/`not` guards) through z3. Skipped without z3.

use std::path::PathBuf;
use std::process::Command;

const ANTHILL_BIN: &str = env!("CARGO_BIN_EXE_anthill");

fn z3_available() -> bool {
    Command::new("z3").arg("--version").output()
        .map(|o| o.status.success()).unwrap_or(false)
}

fn write_temp(name: &str, contents: &str) -> PathBuf {
    let dir = std::env::temp_dir()
        .join(format!("anthill-body-derived-{}-{}", std::process::id(), name));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, contents).unwrap();
    path
}

fn prove_stdout(name: &str, src: &str) -> String {
    let path = write_temp(name, src);
    let out = Command::new(ANTHILL_BIN)
        .arg("prove").arg("--no-cache").arg(&path)
        .output().expect("run anthill prove");
    format!(
        "{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    )
}

// Two bodied ops, NEITHER with a hand-written defining twin:
//   clamp(x) = if x >= 0 then x else 0            (single `if`)
//   grade(x) = if x>=0 then (if x>=5 then 2 else 1) else 0   (nested `if`)
const OPS: &str = r#"
  sort Ops
    operation clamp(x: Int64) -> Int64 = if gte(x, 0) then x else 0
    operation grade(x: Int64) -> Int64 =
      if gte(x, 0)
        then if gte(x, 5) then 2 else 1
        else 0
  end
"#;

fn src_with(rules: &str) -> String {
    format!(
        "namespace test.wi669b\n  import anthill.prelude.{{Int64}}\n  \
         import anthill.prelude.Ordered.{{gte, lt, lte}}\n{OPS}\n{rules}\nend\n"
    )
}

#[test]
fn bodied_op_properties_discharge_from_body_no_twin() {
    if !z3_available() { return; }
    // TRUE properties, both discharged from the body-derived defining rule:
    //   clamp(x) >= 0  (single if)   — violation clamp(x) < 0 is unsat
    //   grade(x) >= 0  (nested if)   — every branch is 0/1/2, unsat below 0
    let src = src_with(
        "  rule clamp_nonneg(?w) :- Ops.clamp(?x, ?r), lt(?r, 0), ?w = ?r\n\
         \x20 proof clamp_nonneg\n    by z3(logic: \"LRA\")\n  end\n\n\
         \x20 rule grade_nonneg(?w) :- Ops.grade(?x, ?r), lt(?r, 0), ?w = ?r\n\
         \x20 proof grade_nonneg\n    by z3(logic: \"LRA\")\n  end",
    );
    let out = prove_stdout("proved.anthill", &src);
    assert!(
        out.contains("test.wi669b.clamp_nonneg: proved"),
        "clamp(x) >= 0 must discharge from the body (single if), no twin — got:\n{out}"
    );
    assert!(
        out.contains("test.wi669b.grade_nonneg: proved"),
        "grade(x) >= 0 must discharge (nested if → and/not refold), no twin — got:\n{out}"
    );
}

#[test]
fn false_property_reports_counterexample() {
    if !z3_available() { return; }
    // FALSE property clamp(x) > 0: the violation clamp(x) <= 0 is sat (x<0 → 0),
    // so the body-derived discharge must FIND the counterexample, not vacuously
    // "prove" it.
    let src = src_with(
        "  rule clamp_nonpos(?w) :- Ops.clamp(?x, ?r), lte(?r, 0), ?w = ?r\n\
         \x20 proof clamp_nonpos\n    by z3(logic: \"LRA\")\n  end",
    );
    let out = prove_stdout("refuted.anthill", &src);
    assert!(
        out.contains("test.wi669b.clamp_nonpos: COUNTEREXAMPLE"),
        "clamp(x) > 0 is FALSE ⇒ z3 finds a counterexample from the body — got:\n{out}"
    );
}
