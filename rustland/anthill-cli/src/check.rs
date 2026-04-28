//! `anthill check` — kernel-side certificate checking
//! (proposal 030 phase β).
//!
//! Walks every Discharged ProofRecord in the loaded KB and verifies
//! its witness per the constructor's checking semantics. Read-only
//! over KB and cache; reports per-record pass/stale/fail/trust.
//!
//! Phase β.1 (this file) implements `SmtDischarge` checking via
//! audit-by-replay: load the recorded SMT-LIB document blob, re-run
//! the named backend, verify the verdict matches. Other constructors
//! (`SldDerivation`, `MetaCompose`, `ScopeAxiom`, `Specialization`,
//! `TrustedAxiom`) currently fall through to a "skipped — not yet
//! checked" outcome until later β sub-phases land them.

use std::path::{Path, PathBuf};
use std::process::Command;

use anthill_core::intern::Symbol;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::typing::get_named_arg;
use anthill_smt_gen::cache::{
    blob_subdir, hash_content, load_blob, resolve_cache_root,
};
use anthill_smt_gen::outcome::parse_z3_output;

/// One check report per ProofRecord.
#[allow(dead_code)] // fields surfaced by the CLI summary
pub struct CheckOutcome {
    pub rule_qn: String,
    pub status: CheckStatus,
}

#[allow(dead_code)] // variants surfaced by the CLI summary; phase β extends
pub enum CheckStatus {
    /// Witness verified successfully.
    Pass,
    /// Witness has no payload to check (Pending records, or
    /// constructors not yet implemented in this phase).
    Skipped(String),
    /// Witness verification failed — recorded verdict differs from
    /// observed, or supporting blob missing.
    Failed(String),
    /// Witness contains TrustedAxiom — surfaced for visibility.
    Trusted(String),
}

/// Top-level entry point for `anthill check <paths>`. Loads the KB,
/// walks Discharged ProofRecords, and prints a summary.
pub fn run_check(
    paths: &[PathBuf],
    kb: &KnowledgeBase,
    solver: &str,
    cache_dir_override: Option<&Path>,
) -> Result<Vec<CheckOutcome>, i32> {
    let _ = paths; // path tracking is the loader's job
    let cache_root = resolve_cache_root(cache_dir_override);
    let repo_root = std::env::current_dir().unwrap_or_else(|_| ".".into());
    let blob_dir = blob_subdir(&cache_root, &repo_root);

    let record_sym = match kb.try_resolve_symbol("anthill.realization.ProofRecord") {
        Some(s) => s,
        None => return Ok(Vec::new()),
    };

    let mut out = Vec::new();
    for rid in kb.by_functor(record_sym) {
        if !kb.rule_body(rid).is_empty() { continue; }
        let head = kb.rule_head(rid);
        let outcome = match check_one_record(kb, head, &blob_dir, solver) {
            Some(o) => o,
            None => continue,
        };
        out.push(outcome);
    }
    Ok(out)
}

fn check_one_record(
    kb: &KnowledgeBase,
    head: TermId,
    blob_dir: &Path,
    solver: &str,
) -> Option<CheckOutcome> {
    let named = match kb.get_term(head) {
        Term::Fn { named_args, .. } => named_args,
        _ => return None,
    };
    let rule_qn = match get_named_arg(kb, named, "rule")
        .and_then(|tid| match kb.get_term(tid) {
            Term::Const(Literal::String(s)) => Some(s.clone()),
            _ => None,
        }) {
        Some(s) => s,
        None => return None,
    };
    let witness_tid = get_named_arg(kb, named, "witness")?;
    // Don't gate on `result.status` — phase β verifies the witness
    // directly. ScopeAxiom records land at status = Pending in α.6/
    // α.7 (we avoid synthesizing a ProofResult at registration) but
    // their witness is checkable by definition. The witness check's
    // own outcome is the truth: Pass / Failed / Trusted / Skipped.
    let status = check_witness_term(kb, witness_tid, blob_dir, solver);
    Some(CheckOutcome { rule_qn, status })
}

fn check_witness_term(
    kb: &KnowledgeBase,
    witness: TermId,
    blob_dir: &Path,
    solver: &str,
) -> CheckStatus {
    let (functor, named) = match kb.get_term(witness) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        _ => return CheckStatus::Skipped("witness is not a structured term".into()),
    };
    let f_qn = kb.qualified_name_of(functor);
    let f_short = f_qn.rsplit('.').next().unwrap_or(f_qn);
    match f_short {
        "SmtDischarge" => check_smt_discharge_witness(kb, &named, blob_dir, solver),
        "ScopeAxiom" => check_scope_axiom_witness(kb, &named),
        "TrustedAxiom" => {
            let reason = read_string_field(kb, &named, "reason")
                .unwrap_or_else(|| "(no reason)".into());
            CheckStatus::Trusted(reason)
        }
        // Other constructors land in later β sub-phases.
        other => CheckStatus::Skipped(format!("witness `{other}` not yet checkable")),
    }
}

/// Phase β.4: re-read the named scope's declaration in the current
/// KB and verify the cited structural feature is still present.
/// Aspect-based dispatch:
///   - `requires.<SE-flat>`: walk SortRequiresInfo facts whose
///     sort_ref qn matches `scope_qn`; pass if any matches the
///     SE-flat encoding (using the same `flatten_spec` logic α.6
///     uses to register the witness).
///   - `induction`: walk SortInfo facts; pass if any matches
///     `scope_qn` and is inductive (`sort_info_is_inductive`).
///   - other: skip (forward-compat).
///
/// Failures are loud — declaration removed, clause edited, kind
/// changed away from enum — all surface as `Failed(...)` with a
/// message naming the cause.
fn check_scope_axiom_witness(
    kb: &KnowledgeBase,
    named: &smallvec::SmallVec<[(Symbol, TermId); 2]>,
) -> CheckStatus {
    use anthill_core::kb::load::{flatten_spec, qn_of_sort_ref, sort_info_is_inductive, sort_info_qn};

    let scope_qn = match read_string_field(kb, named, "scope_qn") {
        Some(s) => s,
        None => return CheckStatus::Failed("ScopeAxiom: missing scope_qn".into()),
    };
    let aspect = match read_string_field(kb, named, "aspect") {
        Some(s) => s,
        None => return CheckStatus::Failed("ScopeAxiom: missing aspect".into()),
    };

    if aspect == "induction" {
        let sort_info_sym = match kb.try_resolve_symbol("anthill.reflect.SortInfo") {
            Some(s) => s,
            None => return CheckStatus::Failed(
                "ScopeAxiom(induction): SortInfo schema not loaded".into()
            ),
        };
        for rid in kb.by_functor(sort_info_sym) {
            if !kb.rule_body(rid).is_empty() { continue; }
            let head = kb.rule_head(rid);
            let head_named = match kb.get_term(head) {
                Term::Fn { named_args, .. } => named_args.clone(),
                _ => continue,
            };
            let actual_qn = sort_info_qn(kb, &head_named);
            if actual_qn.as_deref() != Some(&scope_qn) { continue; }
            if sort_info_is_inductive(kb, &head_named) {
                return CheckStatus::Pass;
            } else {
                return CheckStatus::Failed(format!(
                    "ScopeAxiom(induction): sort `{scope_qn}` is no longer \
                     inductively defined (kind changed away from `enum`)"
                ));
            }
        }
        return CheckStatus::Failed(format!(
            "ScopeAxiom(induction): sort `{scope_qn}` not found in current KB"
        ));
    }

    if let Some(expected_se_flat) = aspect.strip_prefix("requires.") {
        let requires_sym = match kb.try_resolve_symbol(
            "anthill.reflect.SortRequiresInfo"
        ) {
            Some(s) => s,
            None => return CheckStatus::Failed(
                "ScopeAxiom(requires): SortRequiresInfo schema not loaded".into()
            ),
        };
        let mut scope_seen = false;
        for rid in kb.by_functor(requires_sym) {
            if !kb.rule_body(rid).is_empty() { continue; }
            let head = kb.rule_head(rid);
            let head_named = match kb.get_term(head) {
                Term::Fn { named_args, .. } => named_args.clone(),
                _ => continue,
            };
            let sort_ref_tid = match get_named_arg(kb, &head_named, "sort_ref") {
                Some(t) => t,
                None => continue,
            };
            let actual_qn = match qn_of_sort_ref(kb, sort_ref_tid) {
                Some(q) => q,
                None => continue,
            };
            if actual_qn != scope_qn { continue; }
            scope_seen = true;
            let spec_tid = match get_named_arg(kb, &head_named, "spec") {
                Some(t) => t,
                None => continue,
            };
            if let Some(actual_se) = flatten_spec(kb, spec_tid) {
                if actual_se == expected_se_flat {
                    return CheckStatus::Pass;
                }
            }
        }
        return CheckStatus::Failed(if scope_seen {
            format!(
                "ScopeAxiom(requires): scope `{scope_qn}` no longer has \
                 a requires clause matching `{expected_se_flat}`"
            )
        } else {
            format!(
                "ScopeAxiom(requires): scope `{scope_qn}` not found in \
                 current KB"
            )
        });
    }

    CheckStatus::Skipped(format!("ScopeAxiom: aspect `{aspect}` not recognised"))
}

fn check_smt_discharge_witness(
    kb: &KnowledgeBase,
    named: &smallvec::SmallVec<[(Symbol, TermId); 2]>,
    blob_dir: &Path,
    solver_path: &str,
) -> CheckStatus {
    let document_hash = match read_string_field(kb, named, "document_hash") {
        Some(h) if !h.is_empty() => h,
        _ => return CheckStatus::Skipped("witness document_hash empty".into()),
    };
    let recorded_verdict = match read_smt_verdict_label(kb, named) {
        Some(v) => v,
        None => return CheckStatus::Skipped("witness verdict unreadable".into()),
    };
    let document = match load_blob(blob_dir, &document_hash) {
        Some(s) => s,
        None => return CheckStatus::Failed(format!(
            "blob {document_hash} missing — re-run prove to repopulate"
        )),
    };
    if hash_content(&document) != document_hash {
        return CheckStatus::Failed(
            "blob content hash mismatch — store has been tampered with".into()
        );
    }
    let observed_verdict = match run_solver(solver_path, &document) {
        Ok(v) => v,
        Err(e) => return CheckStatus::Failed(format!("solver replay failed: {e}")),
    };
    if observed_verdict != recorded_verdict {
        return CheckStatus::Failed(format!(
            "verdict mismatch: recorded {recorded_verdict}, observed {observed_verdict}"
        ));
    }
    CheckStatus::Pass
}

fn run_solver(solver_path: &str, document: &str) -> Result<String, String> {
    let path = std::env::temp_dir().join(format!(
        "anthill_check_{}.smt2",
        rand_suffix()
    ));
    if let Err(e) = std::fs::write(&path, document) {
        return Err(format!("write smt2: {e}"));
    }
    let out = Command::new(solver_path).arg(&path).output()
        .map_err(|e| format!("invoke {solver_path}: {e}"))?;
    let _ = std::fs::remove_file(&path);
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    let outcome = parse_z3_output(&stdout);
    Ok(match outcome.verdict.as_str() {
        "unsat" => "Unsat".to_string(),
        "sat" => "Sat".to_string(),
        other => format!("Unknown:{other}"),
    })
}

fn read_smt_verdict_label(
    kb: &KnowledgeBase,
    named: &smallvec::SmallVec<[(Symbol, TermId); 2]>,
) -> Option<String> {
    let tid = get_named_arg(kb, named, "verdict")?;
    let functor = match kb.get_term(tid) {
        Term::Fn { functor, .. } => *functor,
        _ => return None,
    };
    let f_qn = kb.qualified_name_of(functor);
    Some(f_qn.rsplit('.').next().unwrap_or(f_qn).to_string())
}

fn read_string_field(
    kb: &KnowledgeBase,
    named: &smallvec::SmallVec<[(Symbol, TermId); 2]>,
    key: &str,
) -> Option<String> {
    let tid = get_named_arg(kb, named, key)?;
    if let Term::Const(Literal::String(s)) = kb.get_term(tid) {
        Some(s.clone())
    } else {
        None
    }
}

fn rand_suffix() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    let nanos = SystemTime::now().duration_since(UNIX_EPOCH)
        .map(|d| d.subsec_nanos()).unwrap_or(0);
    let pid = std::process::id();
    format!("{pid}_{nanos}")
}

/// Run the SmtDischarge replay path with explicit hash + verdict
/// inputs (no KB construction needed). Returns `CheckStatus::Pass`
/// when the blob loads, hash matches, and the solver replay yields
/// the recorded verdict; `Failed(...)` otherwise. Exposed for
/// targeted unit tests of the replay machinery.
#[cfg(test)]
fn check_smt_discharge_payload(
    blob_dir: &Path,
    document_hash: &str,
    recorded_verdict: &str,
    solver_path: &str,
) -> CheckStatus {
    let document = match load_blob(blob_dir, document_hash) {
        Some(s) => s,
        None => return CheckStatus::Failed(format!(
            "blob {document_hash} missing — re-run prove to repopulate"
        )),
    };
    if hash_content(&document) != document_hash {
        return CheckStatus::Failed(
            "blob content hash mismatch — store has been tampered with".into()
        );
    }
    let observed = match run_solver(solver_path, &document) {
        Ok(v) => v,
        Err(e) => return CheckStatus::Failed(format!("solver replay failed: {e}")),
    };
    if observed != recorded_verdict {
        return CheckStatus::Failed(format!(
            "verdict mismatch: recorded {recorded_verdict}, observed {observed}"
        ));
    }
    CheckStatus::Pass
}

#[cfg(test)]
mod tests {
    use super::*;
    use anthill_smt_gen::cache::store_blob;
    use tempfile::TempDir;

    fn z3_available() -> bool {
        Command::new("z3").arg("--version").output()
            .map(|o| o.status.success()).unwrap_or(false)
    }

    #[test]
    fn replay_unsat_passes() {
        if !z3_available() { eprintln!("skip: z3 not on PATH"); return; }
        let tmp = TempDir::new().unwrap();
        let smt = "(set-logic LRA)\n(declare-const x Real)\n\
                   (assert (and (> x 0) (< x 0)))\n(check-sat)\n";
        let hash = store_blob(tmp.path(), smt).unwrap();
        let result = check_smt_discharge_payload(tmp.path(), &hash, "Unsat", "z3");
        assert!(matches!(result, CheckStatus::Pass),
            "expected Pass for genuinely unsat document");
    }

    #[test]
    fn replay_verdict_mismatch_fails() {
        if !z3_available() { eprintln!("skip: z3 not on PATH"); return; }
        let tmp = TempDir::new().unwrap();
        // SAT document but witness claims Unsat — replay must reject.
        let smt = "(set-logic LRA)\n(declare-const x Real)\n\
                   (assert (> x 0))\n(check-sat)\n";
        let hash = store_blob(tmp.path(), smt).unwrap();
        let result = check_smt_discharge_payload(tmp.path(), &hash, "Unsat", "z3");
        assert!(matches!(result, CheckStatus::Failed(_)),
            "expected Failed when recorded verdict disagrees with replay");
    }

    #[test]
    fn missing_blob_fails() {
        let tmp = TempDir::new().unwrap();
        // No blob stored at this hash.
        let bogus_hash = "ab".repeat(32);
        let result = check_smt_discharge_payload(tmp.path(), &bogus_hash, "Unsat", "z3");
        assert!(matches!(result, CheckStatus::Failed(msg) if msg.contains("missing")),
            "expected Failed with 'missing' message when blob is absent");
    }
}

/// Pretty-print a check summary; returns the count of failed
/// outcomes (callers can return non-zero exit when > 0).
pub fn print_summary(outcomes: &[CheckOutcome]) -> usize {
    let mut pass = 0;
    let mut skipped = 0;
    let mut failed = 0;
    let mut trusted = 0;
    for o in outcomes {
        match &o.status {
            CheckStatus::Pass => {
                pass += 1;
                println!("✓ {}", o.rule_qn);
            }
            CheckStatus::Skipped(why) => {
                skipped += 1;
                println!("- {}: skipped ({why})", o.rule_qn);
            }
            CheckStatus::Failed(why) => {
                failed += 1;
                println!("✗ {}: FAILED ({why})", o.rule_qn);
            }
            CheckStatus::Trusted(reason) => {
                trusted += 1;
                println!("⚠ {}: trusted axiom ({reason})", o.rule_qn);
            }
        }
    }
    println!("\nsummary: {pass} pass, {failed} failed, {skipped} skipped, {trusted} trusted, {} total",
        outcomes.len());
    failed
}
