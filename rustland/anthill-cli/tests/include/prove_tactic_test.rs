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
          entity Cfg(scale: Int64)
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
    // Sanity: dry-run every proof in the lf1 example and confirm none emits
    // a `using-params` / `check-sat-using` form — the lf1 proofs are all
    // `by z3(logic: ...)` or `ranking(...)`, which must keep emitting a plain
    // `(check-sat)`. The acceptance constraint for WI-098 is "discharge.sh
    // reports N/N unsat unchanged"; we approximate via --dry-run because z3
    // may not be on CI.
    //
    // Load the WHOLE directory, exactly as discharge.sh does. A hand-picked
    // file subset does NOT work: safety_transponder / safety_gps import their
    // controller specs (follower_transponder / follower_gps), so a subset
    // fails to resolve, `prove` errors, and nothing is emitted — the negative
    // assertion below would then pass vacuously (this is what happened between
    // WI-681 and WI-679: the subset silently stopped exercising the proofs).
    if !z3_available() { return; }
    let lf1_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/webots-modelling/lf1");
    if !lf1_dir.exists() { return; }
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", "--dry-run", "-v", "--no-cache", lf1_dir.to_str().unwrap()])
        .output()
        .expect("run anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout);
    // Non-vacuity: the directory must load cleanly and the proofs must emit —
    // otherwise the `check-sat-using` assertion proves nothing.
    assert!(out.status.success(),
        "anthill prove must load the lf1 directory cleanly — got:\nstdout:\n{stdout}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stderr));
    assert!(stdout.contains("(check-sat)"),
        "lf1 dry-run must emit at least one plain (check-sat) — got:\n{stdout}");
    assert!(!stdout.contains("(check-sat-using"),
        "lf1 proofs must keep emitting plain (check-sat), not a using-params form — got:\n{stdout}");
}
