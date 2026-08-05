//! Phase 4 outcome-layer end-to-end exercise (WI-099).
//!
//! Drives the full pipeline (CLI + Z3 + cache + outcome parser):
//! verifies that `model: true` populates the cache entry's model
//! and `cores: true` populates unsat_core. Skipped without z3.

use std::path::PathBuf;
use std::process::Command;

const ANTHILL_BIN: &str = env!("CARGO_BIN_EXE_anthill");

fn z3_available() -> bool {
    Command::new("z3").arg("--version").output()
        .map(|o| o.status.success()).unwrap_or(false)
}

fn write_temp(name: &str, contents: &str) -> PathBuf {
    let dir = std::env::temp_dir()
        .join(format!("anthill-outcome-test-{}-{}", std::process::id(), name));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, contents).unwrap();
    path
}

#[test]
fn sat_proof_with_model_flag_emits_get_model_in_smt() {
    if !z3_available() { return; }
    // A satisfiable rule body — gt(scale, 0) holds for scale=5.
    // We expect the verdict to come back as `sat` (counterexample),
    // i.e. `disproved`. With `model: true`, the SMT-LIB preamble
    // includes `(set-option :produce-models true)` and `(get-model)`.
    let src = r#"
        namespace test.outcome.sat
          entity Cfg(scale: Int64)
          fact Cfg(scale: 5)
          rule sat_witness(?marker)
            :- Cfg(scale: ?s), gt(?s, 0), eq(?marker, ?s)
          proof sat_witness by z3(logic: "LIA", model: true) end
        end
    "#;
    let path = write_temp("sat.anthill", src);
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "-v", "--no-cache", "--dry-run"])
        .output().expect("anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("(set-option :produce-models true)"),
        "model: true must wire :produce-models into preamble: {stdout}");
    assert!(stdout.contains("(get-model)"),
        "model: true must append (get-model) after check-sat: {stdout}");
}

#[test]
fn unsat_proof_with_cores_flag_emits_get_unsat_core() {
    if !z3_available() { return; }
    let src = r#"
        namespace test.outcome.cores
          entity Cfg(scale: Int64)
          fact Cfg(scale: 5)
          rule cores_witness(?marker)
            :- Cfg(scale: ?s), gt(?s, 99), eq(?marker, ?s)
          proof cores_witness by z3(logic: "LIA", cores: true) end
        end
    "#;
    let path = write_temp("cores.anthill", src);
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "-v", "--no-cache", "--dry-run"])
        .output().expect("anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("(set-option :produce-unsat-cores true)"),
        "cores: true must wire :produce-unsat-cores into preamble: {stdout}");
    assert!(stdout.contains("(get-unsat-core)"),
        "cores: true must append (get-unsat-core): {stdout}");
}

#[test]
fn no_outcome_flags_keeps_legacy_smt() {
    if !z3_available() { return; }
    let src = r#"
        namespace test.outcome.legacy
          entity Cfg(scale: Int64)
          fact Cfg(scale: 5)
          rule legacy(?marker)
            :- Cfg(scale: ?s), gt(?s, 99), eq(?marker, ?s)
          proof legacy by z3(logic: "LIA") end
        end
    "#;
    let path = write_temp("legacy.anthill", src);
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "-v", "--no-cache", "--dry-run"])
        .output().expect("anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(!stdout.contains("(set-option :produce-models"),
        "no model flag must not add :produce-models");
    assert!(!stdout.contains("(get-model)"),
        "no model flag must not add (get-model)");
    assert!(!stdout.contains("(get-unsat-core)"),
        "no cores flag must not add (get-unsat-core)");
}

#[test]
fn sat_verdict_with_model_populates_cli_output() {
    if !z3_available() { return; }
    let src = r#"
        namespace test.outcome.live
          entity Cfg(scale: Int64)
          fact Cfg(scale: 5)
          rule sat_live(?marker)
            :- Cfg(scale: ?s), gt(?s, 0), eq(?marker, ?s)
          proof sat_live by z3(logic: "LIA", model: true) end
        end
    "#;
    let path = write_temp("live.anthill", src);
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "-v", "--no-cache"])
        .output().expect("anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout);
    // Verdict: sat (counterexample) since gt(5, 0) holds.
    assert!(stdout.contains("COUNTEREXAMPLE") || stdout.contains("disproved"),
        "expected counterexample verdict, got:\n{stdout}");
    assert!(stdout.contains("model:") && stdout.contains("bindings"),
        "verbose must report model bindings on sat with model: true:\n{stdout}");
}

#[test]
fn cache_entry_carries_model_text() {
    if !z3_available() { return; }
    use std::fs;
    let src = r#"
        namespace test.outcome.cache
          entity Cfg(scale: Int64)
          fact Cfg(scale: 7)
          rule sat_for_cache(?marker)
            :- Cfg(scale: ?s), gt(?s, 0), eq(?marker, ?s)
          proof sat_for_cache by z3(logic: "LIA", model: true) end
        end
    "#;
    let path = write_temp("cache_outcome.anthill", src);
    let cache_dir = std::env::temp_dir()
        .join(format!("anthill-outcome-cache-{}", std::process::id()));
    let _ = fs::remove_dir_all(&cache_dir);

    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "-v", "--cache-dir"])
        .arg(&cache_dir)
        .output().expect("anthill prove");
    assert!(out.status.success() ||
        // sat verdicts return non-zero exit; that's fine for this
        // test — we just care the cache entry got written.
        String::from_utf8_lossy(&out.stdout).contains("COUNTEREXAMPLE"));

    // Find the single cache entry file under the project subtree.
    fn collect_jsons(dir: &std::path::Path, out: &mut Vec<PathBuf>) {
        if let Ok(rd) = fs::read_dir(dir) {
            for e in rd.flatten() {
                let p = e.path();
                if p.is_dir() { collect_jsons(&p, out); }
                else if p.extension().is_some_and(|e| e == "json") { out.push(p); }
            }
        }
    }
    let mut entries = Vec::new();
    collect_jsons(&cache_dir, &mut entries);
    assert!(!entries.is_empty(), "cache entry must have been written");

    let bytes = fs::read(&entries[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    let model_text = json.get("model_text").and_then(|v| v.as_str()).unwrap_or("");
    let assignments = json.get("variable_assignments")
        .and_then(|v| v.as_array()).cloned().unwrap_or_default();
    assert!(model_text.contains("define-fun") || !assignments.is_empty(),
        "cache entry must carry model_text or variable_assignments: \
         model_text={model_text:?}, assignments={assignments:?}");
}
