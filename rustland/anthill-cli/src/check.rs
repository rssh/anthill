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
    blob_subdir, hash_content, load_blob, load_witness, resolve_cache_root,
    witness_subdir, SmtVerdictDto, WitnessShape, WitnessSidecar,
};
use anthill_smt_gen::outcome::parse_z3_output;

/// One check report per ProofRecord.
pub struct CheckOutcome {
    pub rule_qn: String,
    pub status: CheckStatus,
}

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

/// Per-invocation options for `anthill check`. Mirrors the CLI
/// flags surface (proposal 030 phase ε §Lifecycle).
#[derive(Default, Clone, Debug)]
pub struct CheckOpts {
    /// Skip witness replay; only verify state-hash and structural
    /// integrity. Pending records still skip; ScopeAxiom records
    /// re-read declarations; SmtDischarge / MetaCompose records
    /// short-circuit to a "Pass (shallow)" outcome based on
    /// document_hash presence.
    pub shallow: bool,
    /// Report stale ProofRecords (state-hash mismatches current KB
    /// state) and skip everything else.
    pub report_stale_only: bool,
    /// Report only the records whose witness tree contains a
    /// TrustedAxiom; everything else is filtered out of the output.
    pub report_trust_only: bool,
    /// Glob-restrict the rule QNs that get checked. Empty = no
    /// restriction.
    pub filters: Vec<String>,
}


/// Like `run_check` but with explicit options for the ε CLI flags.
pub fn run_check_with(
    paths: &[PathBuf],
    kb: &KnowledgeBase,
    solver: &str,
    cache_dir_override: Option<&Path>,
    opts: &CheckOpts,
) -> Result<Vec<CheckOutcome>, i32> {
    let _ = paths;
    let cache_root = resolve_cache_root(cache_dir_override);
    let repo_root = std::env::current_dir().unwrap_or_else(|_| ".".into());
    let blob_dir = blob_subdir(&cache_root, &repo_root);
    let witness_dir = witness_subdir(&cache_root, &repo_root);

    let record_sym = match kb.try_resolve_symbol("anthill.realization.ProofRecord") {
        Some(s) => s,
        None => return Ok(Vec::new()),
    };

    let mut out = Vec::new();
    for rid in kb.rules_by_functor(record_sym) {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head(rid);
        let outcome = match check_one_record_with(
            kb, head, &blob_dir, &witness_dir, solver, opts
        ) {
            Some(o) => o,
            None => continue,
        };
        if !filter_keeps(&outcome, opts) { continue; }
        out.push(outcome);
    }
    Ok(out)
}

/// Filter pass: applies `--filter`, `--report-stale`, and
/// `--report-trust` selection to a check outcome.
fn filter_keeps(o: &CheckOutcome, opts: &CheckOpts) -> bool {
    if !opts.filters.is_empty() {
        let any_match = opts.filters.iter().any(|pat| glob_match(pat, &o.rule_qn));
        if !any_match { return false; }
    }
    if opts.report_trust_only {
        return matches!(o.status, CheckStatus::Trusted(_));
    }
    if opts.report_stale_only {
        return matches!(&o.status, CheckStatus::Failed(msg)
            if msg.contains("state-hash") || msg.contains("stale"));
    }
    true
}

/// Minimal glob matcher: `*` matches any sequence of characters
/// (including dots), no other special syntax. Sufficient for the
/// typical "anthill.examples.*" or "*.safety_*" patterns; richer
/// glob support is a follow-up if needed.
fn glob_match(pattern: &str, text: &str) -> bool {
    let parts: Vec<&str> = pattern.split('*').collect();
    if parts.len() == 1 {
        return pattern == text;
    }
    let mut cursor = 0usize;
    let first = parts[0];
    if !text[cursor..].starts_with(first) { return false; }
    cursor += first.len();
    for (i, part) in parts[1..].iter().enumerate() {
        if part.is_empty() {
            if i + 2 == parts.len() { return true; }
            continue;
        }
        match text[cursor..].find(part) {
            Some(pos) => cursor += pos + part.len(),
            None => return false,
        }
    }
    if let Some(last) = parts.last() {
        if !last.is_empty() && !text.ends_with(last) {
            return false;
        }
    }
    true
}

fn check_one_record_with(
    kb: &KnowledgeBase,
    head: TermId,
    blob_dir: &Path,
    witness_dir: &Path,
    solver: &str,
    opts: &CheckOpts,
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
    // Witness sidecar (WI-124) takes precedence over the in-source
    // placeholder when one exists for this rule QN — the sidecar
    // carries the discharged witness from the most recent prove
    // run. Falling back to the source witness preserves α.6/α.7
    // ScopeAxiom records (auto-registered, no sidecar needed).
    if let Some(sidecar) = load_witness(witness_dir, &rule_qn) {
        let status = if opts.shallow {
            check_witness_sidecar_shallow(&sidecar)
        } else {
            check_witness_sidecar(&sidecar, blob_dir, solver)
        };
        return Some(CheckOutcome { rule_qn, status });
    }
    let witness_tid = get_named_arg(kb, named, "witness")?;
    let status = if opts.shallow {
        check_witness_term_shallow(kb, witness_tid)
    } else {
        check_witness_term(kb, witness_tid, blob_dir, solver)
    };
    Some(CheckOutcome { rule_qn, status })
}

/// Shallow check: structural integrity only. ScopeAxiom records
/// still re-read the declaration (cheap, no solver). SmtDischarge,
/// SldDerivation, MetaCompose, Specialization records pass when
/// the witness is well-formed and the recorded hashes are non-
/// empty — no replay. TrustedAxiom records surface their reason.
fn check_witness_term_shallow(kb: &KnowledgeBase, witness: TermId) -> CheckStatus {
    let (functor, named) = match kb.get_term(witness) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        _ => return CheckStatus::Skipped("witness not a structured term".into()),
    };
    let f_short = kb.qualified_name_of(functor)
        .rsplit('.').next().unwrap_or("").to_string();
    match f_short.as_str() {
        "ScopeAxiom" => check_scope_axiom_witness(kb, &named),
        "TrustedAxiom" => {
            let reason = read_string_field(kb, &named, "reason")
                .unwrap_or_else(|| "(no reason)".into());
            CheckStatus::Trusted(reason)
        }
        "SmtDischarge" => {
            let dh = read_string_field(kb, &named, "document_hash")
                .unwrap_or_default();
            if dh.is_empty() {
                CheckStatus::Failed("SmtDischarge: document_hash empty (shallow)".into())
            } else {
                CheckStatus::Pass
            }
        }
        "Specialization" => check_specialization_witness(kb, &named),
        // Other shapes accepted as-is in shallow mode.
        _ => CheckStatus::Pass,
    }
}

fn check_witness_sidecar_shallow(sidecar: &WitnessSidecar) -> CheckStatus {
    match &sidecar.witness {
        WitnessShape::SmtDischarge { document_hash, .. } => {
            if document_hash.is_empty() {
                CheckStatus::Failed(
                    "sidecar SmtDischarge: document_hash empty (shallow)".into()
                )
            } else {
                CheckStatus::Pass
            }
        }
        WitnessShape::TrustedAxiom { reason } => CheckStatus::Trusted(reason.clone()),
        // Other shapes accepted as-is in shallow mode.
        _ => CheckStatus::Pass,
    }
}

/// Verify a witness loaded from a sidecar — same dispatch as
/// `check_witness_term` but operates on the serialized DTO so we
/// don't need to round-trip through KB term construction.
fn check_witness_sidecar(
    sidecar: &WitnessSidecar,
    blob_dir: &Path,
    solver: &str,
) -> CheckStatus {
    check_witness_shape(&sidecar.witness, blob_dir, solver)
}

fn check_witness_shape(
    shape: &WitnessShape,
    blob_dir: &Path,
    solver: &str,
) -> CheckStatus {
    match shape {
        WitnessShape::SmtDischarge { document_hash, verdict, .. } => {
            if document_hash.is_empty() {
                return CheckStatus::Skipped("sidecar has empty document_hash".into());
            }
            let recorded_verdict = match verdict {
                SmtVerdictDto::Unsat => "Unsat",
                SmtVerdictDto::Sat { .. } => "Sat",
                SmtVerdictDto::Unknown { .. } => return CheckStatus::Skipped(
                    "sidecar verdict is Unknown — nothing to replay".into()
                ),
            };
            check_smt_discharge_payload(blob_dir, document_hash, recorded_verdict, solver)
        }
        WitnessShape::MetaCompose { tactic_name, sub } => {
            // Phase β.3 + β.6 (sidecar path): recurse on each sub-
            // witness, aggregate via aggregate_meta_outcomes so trust
            // surfaces alongside other-pass outcomes (rather than
            // short-circuiting and masking later failures).
            let outcomes: Vec<CheckStatus> = sub.iter()
                .map(|s| check_witness_shape(s, blob_dir, solver))
                .collect();
            aggregate_meta_outcomes(tactic_name, &outcomes)
        }
        WitnessShape::TrustedAxiom { reason } => CheckStatus::Trusted(reason.clone()),
        // ScopeAxiom / Specialization sidecars happen when prove
        // discharged a record whose witness shape is one of those
        // (rare for user proofs in v0). Not yet replayable from the
        // sidecar alone — needs KB context. Skip with a note.
        other => CheckStatus::Skipped(format!(
            "sidecar witness `{}` not yet checkable from sidecar",
            shape_name(other)
        )),
    }
}

fn shape_name(s: &WitnessShape) -> &'static str {
    match s {
        WitnessShape::SmtDischarge { .. } => "SmtDischarge",
        WitnessShape::SldDerivation { .. } => "SldDerivation",
        WitnessShape::MetaCompose { .. } => "MetaCompose",
        WitnessShape::ScopeAxiom { .. } => "ScopeAxiom",
        WitnessShape::Specialization { .. } => "Specialization",
        WitnessShape::TrustedAxiom { .. } => "TrustedAxiom",
    }
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
        "Specialization" => check_specialization_witness(kb, &named),
        "MetaCompose" => check_meta_compose_witness(kb, &named, blob_dir, solver),
        "TrustedAxiom" => {
            let reason = read_string_field(kb, &named, "reason")
                .unwrap_or_else(|| "(no reason)".into());
            CheckStatus::Trusted(reason)
        }
        // Other constructors land in later β sub-phases.
        other => CheckStatus::Skipped(format!("witness `{other}` not yet checkable")),
    }
}

/// Phase β.3 (KB-side) + β.6 (trust propagation): recurse into each
/// sub-witness term in a MetaCompose, aggregating outcomes with
/// priority Failed > Skipped > Trusted > Pass. Mirrors the sidecar-
/// side recursion in `check_witness_shape::MetaCompose` so the two
/// paths stay in sync. Per-meta-tactic shape contracts (induction
/// expects base + step, ranking expects boundedness + decrease, …)
/// are deferred — they require a `MetaTacticContract` schema the
/// kernel doesn't yet have.
fn check_meta_compose_witness(
    kb: &KnowledgeBase,
    named: &smallvec::SmallVec<[(Symbol, TermId); 2]>,
    blob_dir: &Path,
    solver: &str,
) -> CheckStatus {
    let tactic_name = read_string_field(kb, named, "tactic_name")
        .unwrap_or_else(|| "compose".into());
    let sub_tid = match get_named_arg(kb, named, "sub") {
        Some(t) => t,
        None => return CheckStatus::Failed(
            "MetaCompose: missing `sub` field".into()
        ),
    };
    let sub_witnesses = read_witness_list(kb, sub_tid);
    let outcomes: Vec<CheckStatus> = sub_witnesses.iter()
        .map(|t| check_witness_term(kb, *t, blob_dir, solver))
        .collect();
    aggregate_meta_outcomes(&tactic_name, &outcomes)
}

/// Phase β.6: combine sub-witness outcomes into the MetaCompose's
/// own outcome with priority Failed > Skipped > Trusted > Pass.
/// Failed short-circuits to surface the breakage; Skipped surfaces
/// when no failures exist (incomplete checking is honest, not
/// silent); Trusted aggregates *all* trust reasons across the
/// subtree so the user sees every axiom dependency, not just the
/// first encountered. Pass only when every sub-witness passed.
///
/// Both the KB-term and sidecar paths route through this so trust
/// surfacing is uniform regardless of which path the witness
/// arrived from.
fn aggregate_meta_outcomes(tactic_name: &str, outcomes: &[CheckStatus]) -> CheckStatus {
    let mut trust_reasons: Vec<String> = Vec::new();
    let mut skipped_reasons: Vec<String> = Vec::new();
    for (i, status) in outcomes.iter().enumerate() {
        match status {
            CheckStatus::Pass => {}
            CheckStatus::Trusted(r) => trust_reasons.push(format!("[{i}] {r}")),
            CheckStatus::Skipped(r) => skipped_reasons.push(format!("[{i}] {r}")),
            CheckStatus::Failed(r) => return CheckStatus::Failed(format!(
                "{tactic_name}[{i}]: {r}"
            )),
        }
    }
    if !skipped_reasons.is_empty() {
        return CheckStatus::Skipped(format!(
            "{tactic_name}: {}",
            skipped_reasons.join("; ")
        ));
    }
    if !trust_reasons.is_empty() {
        return CheckStatus::Trusted(format!(
            "{tactic_name}: {}",
            trust_reasons.join("; ")
        ));
    }
    CheckStatus::Pass
}

/// Walk a `cons(head: <witness-term>, tail: ...)` list and collect
/// the head TermIds. Used to read MetaCompose's `sub` field.
fn read_witness_list(kb: &KnowledgeBase, mut tid: TermId) -> Vec<TermId> {
    let mut out = Vec::new();
    for _ in 0..1024 {
        let (functor, named) = match kb.get_term(tid) {
            Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
            _ => break,
        };
        let f_short = kb.qualified_name_of(functor)
            .rsplit('.').next().unwrap_or("").to_owned();
        if f_short != "cons" { break; }
        if let Some(h) = get_named_arg(kb, &named, "head") {
            out.push(h);
        }
        match get_named_arg(kb, &named, "tail") {
            Some(t) => tid = t,
            None => break,
        }
    }
    out
}

/// Phase β.5: validate a Specialization witness structurally.
///
/// Checks (per the proposal):
///   (a) parametric ProofRecord exists in the registry — without it
///       there's nothing to specialize.
///   (b) substitution is well-formed — no duplicate abstract_param
///       keys; concrete sorts are valid identifiers.
///   (c) v0: instances list is empty (per α.8 v0); pass when (a) and
///       (b) hold. Future refinement: when α.8 starts populating the
///       instances list, β.5 verifies each instance ProofRecord
///       covers a specific requires-law under the substitution.
///
/// Encoding: substitution is a cons-list of SortBinding entities;
/// instances is a cons-list of QN strings.
fn check_specialization_witness(
    kb: &KnowledgeBase,
    named: &smallvec::SmallVec<[(Symbol, TermId); 2]>,
) -> CheckStatus {
    let parametric_qn = match read_string_field(kb, named, "parametric") {
        Some(s) if !s.is_empty() => s,
        _ => return CheckStatus::Failed("Specialization: missing parametric QN".into()),
    };

    if !proof_record_exists(kb, &parametric_qn) {
        return CheckStatus::Failed(format!(
            "Specialization: parametric ProofRecord `{parametric_qn}` not found \
             in registry — was the spec's requires clause removed?"
        ));
    }

    let substitution = read_substitution(kb, named);
    let mut seen_keys: std::collections::HashSet<&str> = std::collections::HashSet::new();
    for (k, _) in &substitution {
        if !seen_keys.insert(k.as_str()) {
            return CheckStatus::Failed(format!(
                "Specialization: substitution has duplicate abstract_param `{k}`"
            ));
        }
    }

    CheckStatus::Pass
}

/// True iff a `ProofRecord` fact exists with `rule = qn`. The check
/// scans the rules_by_functor list for ProofRecord — small in practice
/// (proofs per project are bounded) and avoids needing a separate
/// index.
fn proof_record_exists(kb: &KnowledgeBase, qn: &str) -> bool {
    let record_sym = match kb.try_resolve_symbol("anthill.realization.ProofRecord") {
        Some(s) => s,
        None => return false,
    };
    for rid in kb.rules_by_functor(record_sym) {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head(rid);
        if let Term::Fn { named_args, .. } = kb.get_term(head) {
            if let Some(tid) = get_named_arg(kb, named_args, "rule") {
                if let Term::Const(Literal::String(s)) = kb.get_term(tid) {
                    if s == qn { return true; }
                }
            }
        }
    }
    false
}

/// Read a Specialization's `substitution` field — a cons-list of
/// SortBinding entities — into a `Vec<(abstract_param, concrete_sort)>`.
/// Returns an empty vec on a `nil` list or unrecognized shape; the
/// caller treats empty as a degenerate-but-valid substitution
/// (identity map).
fn read_substitution(
    kb: &KnowledgeBase,
    named: &smallvec::SmallVec<[(Symbol, TermId); 2]>,
) -> Vec<(String, String)> {
    let mut out = Vec::new();
    let mut tid = match get_named_arg(kb, named, "substitution") {
        Some(t) => t,
        None => return out,
    };
    for _ in 0..1024 {
        let (functor, named_inner) = match kb.get_term(tid) {
            Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
            _ => break,
        };
        let f_short = kb.qualified_name_of(functor)
            .rsplit('.').next().unwrap_or("").to_owned();
        if f_short != "cons" { break; }
        if let Some(h) = get_named_arg(kb, &named_inner, "head") {
            if let Term::Fn { named_args: bind_args, .. } = kb.get_term(h) {
                let k = read_string_field(kb, bind_args, "abstract_param");
                let v = read_string_field(kb, bind_args, "concrete_sort");
                if let (Some(k), Some(v)) = (k, v) {
                    out.push((k, v));
                }
            }
        }
        match get_named_arg(kb, &named_inner, "tail") {
            Some(t) => tid = t,
            None => break,
        }
    }
    out
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
        for rid in kb.rules_by_functor(sort_info_sym) {
            if !kb.is_fact(rid) { continue; }
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
        for rid in kb.rules_by_functor(requires_sym) {
            if !kb.is_fact(rid) { continue; }
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

pub(crate) fn rand_suffix() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    let nanos = SystemTime::now().duration_since(UNIX_EPOCH)
        .map(|d| d.subsec_nanos()).unwrap_or(0);
    let pid = std::process::id();
    format!("{pid}_{nanos}")
}

/// Run the SmtDischarge replay path with explicit hash + verdict
/// inputs (no KB construction needed). Returns `CheckStatus::Pass`
/// when the blob loads, hash matches, and the solver replay yields
/// the recorded verdict; `Failed(...)` otherwise. Used both from
/// the KB-side dispatch and from the sidecar-side dispatch (WI-124).
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

    /// Phase β.7 tampering: a sidecar that claims Unsat but points
    /// at a SAT document fails the replay. The attacker would have
    /// to either (a) forge a document that Z3 returns Unsat for —
    /// which means proving the property by content (no cheat) — or
    /// (b) tamper with Z3 itself, which is the documented trust
    /// boundary in §β.1.
    #[test]
    fn lying_sidecar_verdict_fails() {
        if !z3_available() { eprintln!("skip: z3 not on PATH"); return; }
        let tmp = TempDir::new().unwrap();
        // SAT-shaped document — Z3 will return sat.
        let sat_doc = "(set-logic LRA)\n(declare-const x Real)\n\
                       (assert (> x 0))\n(check-sat)\n";
        let hash = store_blob(tmp.path(), sat_doc).unwrap();
        // Sidecar lies and claims this discharge was Unsat.
        let result = check_smt_discharge_payload(tmp.path(), &hash, "Unsat", "z3");
        assert!(matches!(result, CheckStatus::Failed(_)),
            "lying sidecar must fail verification");
    }

    /// Phase β.7 tampering: a blob whose on-disk content has been
    /// edited to be different from its claimed hash is rejected by
    /// the content-hash re-check before solver replay even runs.
    #[test]
    fn tampered_blob_fails_content_hash_check() {
        let tmp = TempDir::new().unwrap();
        // Compute a hash for one document, then write a different
        // document at that hash's path — simulates manual edit.
        let original = "(check-sat)\n";
        let hash = hash_content(original);
        let tampered_path = anthill_smt_gen::cache::blob_path(tmp.path(), &hash);
        std::fs::create_dir_all(tampered_path.parent().unwrap()).unwrap();
        std::fs::write(&tampered_path, "(check-sat) ; tampered\n").unwrap();
        let result = check_smt_discharge_payload(tmp.path(), &hash, "Unsat", "z3");
        assert!(matches!(result, CheckStatus::Failed(msg) if msg.contains("hash mismatch")),
            "tampered blob must fail content-hash re-check");
    }

    #[test]
    fn aggregate_meta_priority_failed_beats_trusted() {
        // [Pass, Trusted, Failed] → Failed (with the failure's
        // reason surfaced; trust does NOT mask the failure).
        let outcomes = vec![
            CheckStatus::Pass,
            CheckStatus::Trusted("axiom_a".into()),
            CheckStatus::Failed("smt mismatch".into()),
        ];
        let r = aggregate_meta_outcomes("induction", &outcomes);
        assert!(matches!(r, CheckStatus::Failed(msg) if msg.contains("smt mismatch")),
            "Failed must take precedence over Trusted in aggregation");
    }

    #[test]
    fn aggregate_meta_trust_when_all_others_pass() {
        // [Pass, Trusted, Pass] → Trusted (trust surfaces when
        // there's nothing more severe to report).
        let outcomes = vec![
            CheckStatus::Pass,
            CheckStatus::Trusted("axiom_a".into()),
            CheckStatus::Pass,
        ];
        let r = aggregate_meta_outcomes("ranking", &outcomes);
        assert!(matches!(r, CheckStatus::Trusted(msg) if msg.contains("axiom_a")),
            "Trusted must surface when no Failed/Skipped outcomes exist");
    }

    #[test]
    fn aggregate_meta_skipped_beats_trusted() {
        // [Pass, Trusted, Skipped] → Skipped (incomplete checking
        // is honest, not silent — surface ahead of trust marker).
        let outcomes = vec![
            CheckStatus::Pass,
            CheckStatus::Trusted("axiom_a".into()),
            CheckStatus::Skipped("not yet impl".into()),
        ];
        let r = aggregate_meta_outcomes("induction", &outcomes);
        assert!(matches!(r, CheckStatus::Skipped(_)),
            "Skipped must take precedence over Trusted in aggregation");
    }

    #[test]
    fn aggregate_meta_all_pass_yields_pass() {
        let outcomes = vec![CheckStatus::Pass, CheckStatus::Pass, CheckStatus::Pass];
        assert!(matches!(
            aggregate_meta_outcomes("induction", &outcomes),
            CheckStatus::Pass
        ));
    }

    #[test]
    fn glob_match_basic_patterns() {
        // Exact match.
        assert!(glob_match("foo.bar", "foo.bar"));
        assert!(!glob_match("foo.bar", "foo.bar.baz"));
        // Suffix wildcard.
        assert!(glob_match("foo.*", "foo.bar"));
        assert!(glob_match("foo.*", "foo.bar.baz"));
        assert!(!glob_match("foo.*", "foox"));
        // Prefix wildcard.
        assert!(glob_match("*.bar", "foo.bar"));
        assert!(glob_match("*.bar", "a.b.c.bar"));
        // Substring wildcard.
        assert!(glob_match("*safety*", "anthill.examples.lf1.safety.gps.x"));
        assert!(!glob_match("*safety*", "anthill.examples.lf1.gps.x"));
    }

    #[test]
    fn aggregate_meta_collects_all_trust_reasons() {
        let outcomes = vec![
            CheckStatus::Trusted("axiom_a".into()),
            CheckStatus::Pass,
            CheckStatus::Trusted("axiom_b".into()),
        ];
        match aggregate_meta_outcomes("induction", &outcomes) {
            CheckStatus::Trusted(msg) => {
                assert!(msg.contains("axiom_a"), "trust reasons missing axiom_a: {msg}");
                assert!(msg.contains("axiom_b"), "trust reasons missing axiom_b: {msg}");
            }
            other => panic!("expected Trusted with both reasons, got {:?}",
                std::mem::discriminant(&other)),
        }
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
