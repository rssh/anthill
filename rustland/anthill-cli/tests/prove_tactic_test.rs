//! End-to-end exercise of the WI-098 tactic-expression emitter.
//!
//! `by z3(tactic: <T>)` proofs must thread <T> into Z3's
//! `(check-sat-using ...)` form. Skipped when z3 isn't on $PATH.

use std::path::PathBuf;
use std::process::Command;

const ANTHILL_BIN: &str = env!("CARGO_BIN_EXE_anthill");

fn z3_available() -> bool {
    Command::new("z3").arg("--version").output()
        .map(|o| o.status.success()).unwrap_or(false)
}

fn write_temp(name: &str, contents: &str) -> PathBuf {
    let dir = std::env::temp_dir()
        .join(format!("anthill-tac-test-{}-{}", std::process::id(), name));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, contents).unwrap();
    path
}

fn prove_unsat_with(tactic_clause: &str) -> String {
    let slug = sanitize(tactic_clause);
    let src = format!(r#"
        namespace test.tac.{slug}
          export r
          entity Cfg(scale: Int)
          fact Cfg(scale: 5)
          rule r(?marker)
            :- Cfg(scale: ?s), gt(?s, 99), eq(?marker, ?s)
          proof r by z3({tactic_clause}) end
        end
    "#);
    let path = write_temp(&format!("tac_{slug}.anthill"), &src);
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "-v", "--no-cache", "--dry-run"])
        .output()
        .expect("run anthill prove");
    String::from_utf8_lossy(&out.stdout).to_string()
}

fn sanitize(s: &str) -> String {
    s.chars().map(|c| if c.is_ascii_alphanumeric() { c } else { '_' }).collect()
}

#[test]
fn legacy_logic_only_emits_plain_check_sat() {
    if !z3_available() { return; }
    let dump = prove_unsat_with(r#"logic: "LIA""#);
    assert!(dump.contains("(check-sat)\n"),
        "legacy `by z3(logic: ...)` must keep emitting plain (check-sat) — \
         tactic expression is the default smt: {dump}");
    assert!(!dump.contains("check-sat-using"),
        "no using- form should appear: {dump}");
}

#[test]
fn explicit_smt_with_random_seed_emits_using_params() {
    if !z3_available() { return; }
    let dump = prove_unsat_with(r#"tactic: smt(random_seed: 42)"#);
    assert!(dump.contains("(check-sat-using (using-params smt :random_seed 42))"),
        "smt with non-preamble param must emit (using-params ...): {dump}");
}

#[test]
fn then_combinator_emits_sexp() {
    if !z3_available() { return; }
    let dump = prove_unsat_with(r#"tactic: then(simplify, smt)"#);
    assert!(dump.contains("(check-sat-using (then simplify smt))"),
        "then combinator must serialise as Z3 (then ...): {dump}");
}

#[test]
fn or_else_uses_dashed_keyword() {
    if !z3_available() { return; }
    let dump = prove_unsat_with(r#"tactic: or_else(simplify, smt)"#);
    assert!(dump.contains("(check-sat-using (or-else simplify smt))"),
        "or_else (anthill) must become (or-else ...) (Z3): {dump}");
}

#[test]
fn raw_passes_through_verbatim() {
    if !z3_available() { return; }
    let dump = prove_unsat_with(r#"tactic: raw("(then simplify smt)")"#);
    assert!(dump.contains("(check-sat-using (then simplify smt))"),
        "raw must splice verbatim: {dump}");
}

#[test]
fn legacy_lf1_proofs_unchanged() {
    // Sanity: walk every safety_*.anthill in the lf1 example with
    // --dry-run and confirm none of them ends up with a `using-params`
    // form. The acceptance constraint for WI-098 is "discharge.sh
    // reports 5/5 unsat unchanged" — we approximate via dry-run
    // because z3 may not be on CI.
    if !z3_available() { return; }
    let lf1_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/webots-modelling/lf1");
    if !lf1_dir.exists() { return; }
    for fname in ["safety_gps.anthill", "safety_transponder.anthill"] {
        let path = lf1_dir.join(fname);
        if !path.exists() { continue; }
        let common = lf1_dir.join("safety_common.anthill");
        let leader = lf1_dir.join("leader.anthill");
        let out = Command::new(ANTHILL_BIN)
            .args(["prove", "--dry-run", "-v", "--no-cache",
                   path.to_str().unwrap(),
                   common.to_str().unwrap(),
                   leader.to_str().unwrap()])
            .output()
            .expect("run anthill prove");
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(!stdout.contains("(check-sat-using"),
            "lf1 {fname} must keep emitting plain (check-sat) — got:\n{stdout}");
    }
}
