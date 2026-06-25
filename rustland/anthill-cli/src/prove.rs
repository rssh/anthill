//! `anthill prove` — discharge proof obligations declared via
//! `proof <rule> by <strategy>` blocks (proposal 025).

use std::collections::BTreeSet;
use std::process::Command;

use smallvec::SmallVec;

use anthill_core::intern::Symbol;
use anthill_core::kb::{KnowledgeBase, RuleId};
use anthill_core::kb::proof_verify::{set_proof_result, VerdictWrite};
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::typing::get_named_arg;
use anthill_smt_gen::{
    emit_satisfiability_check_with_deps, lift_rule_to_implication_clause, ProofConfig,
};
use anthill_smt_gen::cache::{
    self, blob_subdir, build_key, hash_content, lookup, proof_subdir,
    resolve_cache_root, state_hash, store_blob, store_entry, store_witness,
    witness_subdir, CacheEntry, KeyInputs, Solver, WitnessSidecar,
};
use anthill_smt_gen::tactic_emit::emit_tactic_from_term;
use anthill_smt_gen::outcome::parse_z3_output;

use crate::{ProveArgs, load_kb_with_stdlib};
use crate::check::rand_suffix;
use crate::witness::{ProofWitness, SmtVerdict};

pub(crate) fn run_prove(args: &ProveArgs) -> Result<(), i32> {
    if args.show_cache {
        return run_show_cache(args);
    }
    if let Some(days) = args.gc_cache {
        return run_gc_cache(args, days);
    }

    let mut kb = load_kb_with_stdlib(&args.paths, args.verbose, true)?;

    let records = collect_proof_records(&kb);
    if records.is_empty() {
        eprintln!("no proof obligations found in loaded KB");
        return Ok(());
    }

    let mut total = 0usize;
    let mut discharged = 0usize;
    let mut skipped = 0usize;
    let mut failed = 0usize;
    let mut stats = CacheStats::default();
    // Phase γ.2: rules discharged earlier in this prove invocation.
    // Cite-resolution checks this set first so within-invocation
    // chains work even with --no-cache (which skips sidecar writes).
    // Phase γ.2: rules discharged earlier in this prove invocation,
    // mapped to the kind of discharge so cite_status can distinguish
    // a clean Discharged from a Trusted (TrustedAxiom-witnessed) one.
    let mut discharged_this_run: std::collections::HashMap<String, DischargeKind> =
        std::collections::HashMap::new();
    // WI-558: in-KB result write-backs (RuleId-exact), collected here and
    // applied after the dispatch loop so a retract/re-assert can't perturb
    // in-loop cite resolution (which reads other ProofRecord facts).
    let mut write_backs: Vec<(RuleId, VerdictWrite)> = Vec::new();

    for rec in &records {
        if let Some(filter) = &args.rule {
            if &rec.rule != filter {
                continue;
            }
        }
        total += 1;
        let outcome = dispatch(&mut kb, rec, args, &mut stats, &mut discharged_this_run);
        let witness = outcome.witness.clone();
        // WI-558: stash the in-KB result flip for this verdict, keyed on the
        // source record's RuleId (applied below). Encode the witness term now,
        // while `kb` is free between dispatches.
        if let (Some(rid), Some(vw)) =
            (rec.rid, verdict_write_for(&mut kb, &outcome.verdict, &witness, rec))
        {
            write_backs.push((rid, vw));
        }
        // Per-ProofRecord state hash (phase α.4): canonical hash of
        // the kb-state slice this discharge consulted. None for
        // early-exit Skipped / EmitError where no kb state was read.
        let record_state_hash: Option<String> = if outcome.visited_rules.is_empty() {
            None
        } else {
            Some(state_hash(&kb, &outcome.visited_rules))
        };
        // WI-124 — witness persistence: write a sidecar JSON for
        // every Proved outcome so `anthill check` can replay the
        // witness across CLI invocations. Discharges that didn't
        // produce a real witness (Skipped, EmitError) leave any
        // existing sidecar in place for staleness on the next run.
        if let (Verdict::Proved, Some(w)) = (&outcome.verdict, &witness) {
            persist_witness(args, &rec.rule, w, record_state_hash.as_deref());
            let kind = match w {
                ProofWitness::TrustedAxiom { reason } =>
                    DischargeKind::Trusted(reason.clone()),
                _ => DischargeKind::Sound,
            };
            discharged_this_run.insert(rec.rule.clone(), kind);
        }
        match outcome.verdict {
            Verdict::Proved => {
                println!("✓ {}: proved (z3: unsat)", rec.rule);
                discharged += 1;
            }
            Verdict::Disproved(model) => {
                println!("✗ {}: COUNTEREXAMPLE (z3: sat)", rec.rule);
                if args.verbose {
                    println!("{}", indent(&model, "  "));
                }
                failed += 1;
            }
            Verdict::Unknown(reason) => {
                println!("? {}: unknown ({reason})", rec.rule);
                failed += 1;
            }
            Verdict::Skipped(why) => {
                println!("- {}: skipped ({why})", rec.rule);
                skipped += 1;
            }
            Verdict::EmitError(msg) => {
                eprintln!("error: {}: {msg}", rec.rule);
                failed += 1;
            }
        }
    }

    // WI-558: flip each dispatched record's in-KB `result` (Pending →
    // Discharged | Failed) so the loaded KB reflects the prove verdicts for
    // every tier — not just the sidecar.
    for (rid, vw) in write_backs {
        set_proof_result(&mut kb, rid, vw);
    }

    if total == 0 {
        if let Some(rule) = &args.rule {
            eprintln!("error: no proof obligation found for rule `{rule}`");
            return Err(1);
        }
    }

    println!(
        "\nsummary: {discharged} proved, {failed} failed, {skipped} skipped, {total} total"
    );
    if args.stats {
        println!(
            "cache:   {} hit, {} miss, {} written, {} bypassed",
            stats.hits, stats.misses, stats.writes, stats.bypassed,
        );
    }
    if failed > 0 { Err(1) } else { Ok(()) }
}

#[derive(Default)]
struct CacheStats {
    hits: usize,
    misses: usize,
    writes: usize,
    bypassed: usize,
}

#[derive(Debug)]
struct ProofRec {
    /// The `RuleId` of the source `ProofRecord` fact this rec was read from,
    /// for the WI-558 in-KB result write-back. `None` for synthetic recs built
    /// during structured-proof dispatch (which are dispatched but never written
    /// back). Keyed on the exact RuleId — not the `rule` QN — so two
    /// `proof <same-rule>` decls each get their own verdict.
    rid: Option<RuleId>,
    rule: String,
    strategy: Strategy,
    /// Cited-lemma rule QNs from the source-level `using` clause.
    /// Each is dispatched separately to render its body as SMT,
    /// and the resulting clauses are spliced into this proof's
    /// SMT preamble as `(assert ...)` hypotheses (via
    /// `ProofConfig.assumptions`). Empty for proofs without a
    /// `using` clause.
    using: Vec<String>,
    /// True when the proof body is `ProofBodyStructured` (proposal
    /// 031). The dispatcher routes these through `dispatch_structured`
    /// rather than the standard tactic dispatch path. Phase b of the
    /// proposal (full structured-proof dispatch with transient
    /// step rules + hypothesis splicing) is filed as a follow-up
    /// work item; today the dispatcher emits a clear `Skipped`
    /// verdict so the syntax round-trips through parse/load/check
    /// without silently passing.
    structured: bool,
    /// Render the rule's body abstractly (don't chase rule calls
    /// into their defining bodies). Set to `true` for the conclude
    /// clause's parent-rule discharge in `dispatch_structured` so
    /// transitive nonlinear / fact-bound arithmetic doesn't pollute
    /// the LRA preamble — the cited step lifts already constrain
    /// the relevant variables.
    abstract_body: bool,
}

#[derive(Debug)]
enum Strategy {
    Open,
    Tool { name: String, args: Vec<NamedArg> },
}

#[derive(Debug)]
struct NamedArg {
    key: String,
    value: ArgValue,
}

#[derive(Debug)]
enum ArgValue {
    String(String),
    Int(i64),
    /// Parsed by `read_named_arg`; not yet consumed by any tactic-arg
    /// reader. Retained so float-valued args round-trip through the
    /// IR even though no current tactic looks at them.
    Float(#[allow(dead_code)] f64),
    Bool(bool),
    /// Non-primitive term value — preserved as a TermId so callers can
    /// re-walk it (e.g. tactic-term values for `tactic:` named args).
    Term(TermId),
    Other,
}

/// Pre-resolved symbols used during ProofRecord destructuring. Built
/// once per `collect_proof_records` call so the per-named-arg loops
/// can compare `Symbol` (a `u32`) instead of `qualified_name_of`'s
/// `String` clone.
struct ProofSyms {
    open: Option<Symbol>,
    cons: Option<Symbol>,
    named_arg: Option<Symbol>,
    scope_axiom: Option<Symbol>,
    specialization: Option<Symbol>,
}

impl ProofSyms {
    fn new(kb: &KnowledgeBase) -> Self {
        Self {
            open: kb.try_resolve_symbol("anthill.realization.ProofStrategyOpen"),
            cons: kb.try_resolve_symbol("anthill.prelude.List.cons"),
            named_arg: kb.try_resolve_symbol("named_arg"),
            scope_axiom: kb.try_resolve_symbol(
                "anthill.realization.witness.ProofWitness.ScopeAxiom"),
            specialization: kb.try_resolve_symbol(
                "anthill.realization.witness.ProofWitness.Specialization"),
        }
    }
}

fn collect_proof_records(kb: &KnowledgeBase) -> Vec<ProofRec> {
    let functor = match kb.try_resolve_symbol("anthill.realization.ProofRecord") {
        Some(s) => s,
        None => return Vec::new(),
    };
    let syms = ProofSyms::new(kb);
    let mut out = Vec::new();
    for rid in kb.rules_by_functor(functor) {
        let head = kb.rule_head(rid);
        if let Some(rec) = read_proof_record(kb, &syms, rid, head) {
            out.push(rec);
        }
    }
    // Phase γ.3: discharge in dependency order (cited before citer)
    // so γ.2's `discharged_this_run` has the prerequisite witnesses
    // ready by the time their consumer's cite-resolution fires.
    // Falls back to alphabetical when the topo sort can't terminate
    // (cycles surface via the warning path; offending records fall
    // to the end so the rest still get tried).
    topo_sort_by_using(out)
}

/// Kahn's algorithm over the `using` graph. Records with no
/// dependencies on other ProofRecords come first; ties broken
/// alphabetically. Cycles produce a stderr warning naming the
/// involved rules and the cycle members are appended to the end
/// of the order (their cites will then fail loudly via cite_status,
/// rather than crashing the whole prove run).
fn topo_sort_by_using(records: Vec<ProofRec>) -> Vec<ProofRec> {
    use std::collections::{BTreeSet, HashMap};
    let known: BTreeSet<String> = records.iter().map(|r| r.rule.clone()).collect();
    let mut indeg: HashMap<String, usize> = HashMap::new();
    let mut deps: HashMap<String, Vec<String>> = HashMap::new();
    for rec in &records {
        indeg.entry(rec.rule.clone()).or_insert(0);
        for cited in &rec.using {
            // Only edges to other records being dispatched count;
            // out-of-set cites resolve via sidecar/KB and don't
            // need ordering.
            if known.contains(cited) && cited != &rec.rule {
                *indeg.entry(rec.rule.clone()).or_insert(0) += 1;
                deps.entry(cited.clone()).or_default().push(rec.rule.clone());
            }
        }
    }
    let mut by_name: HashMap<String, ProofRec> = records
        .into_iter().map(|r| (r.rule.clone(), r)).collect();
    // Use a sorted ready-set so ties break alphabetically (stable
    // output order across runs).
    let mut ready: BTreeSet<String> = indeg.iter()
        .filter_map(|(k, v)| if *v == 0 { Some(k.clone()) } else { None })
        .collect();
    let mut out: Vec<ProofRec> = Vec::with_capacity(by_name.len());
    while let Some(qn) = ready.iter().next().cloned() {
        ready.remove(&qn);
        if let Some(rec) = by_name.remove(&qn) {
            out.push(rec);
        }
        if let Some(consumers) = deps.remove(&qn) {
            for c in consumers {
                if let Some(d) = indeg.get_mut(&c) {
                    *d = d.saturating_sub(1);
                    if *d == 0 { ready.insert(c); }
                }
            }
        }
    }
    if !by_name.is_empty() {
        let cycle: Vec<String> = by_name.keys().cloned().collect();
        eprintln!(
            "warning: cycle in `using` dependencies among proofs: {}; \
             these will discharge in arbitrary order and any cite-resolution \
             failures will surface per-record",
            cycle.join(", ")
        );
        let mut tail: Vec<ProofRec> = by_name.into_values().collect();
        tail.sort_by(|a, b| a.rule.cmp(&b.rule));
        out.extend(tail);
    }
    out
}

fn read_proof_record(
    kb: &KnowledgeBase,
    syms: &ProofSyms,
    rid: RuleId,
    term_id: TermId,
) -> Option<ProofRec> {
    let named = match kb.get_term(term_id) {
        Term::Fn { named_args, .. } => named_args,
        _ => return None,
    };
    // Auto-registered ScopeAxiom / Specialization records (proposal
    // 030 phase α.6+) are kernel-managed: they exist as ProofRecord
    // facts so phase β can verify them, but the user-facing prove
    // driver should not "discharge" them like ordinary proof blocks.
    if has_auto_registered_witness(kb, syms, named) {
        return None;
    }
    let rule = lookup_string(kb, named, "rule")?;
    let strategy = read_strategy(kb, syms, get_named_arg(kb, named, "strategy")?);
    let using = get_named_arg(kb, named, "using")
        .map(|tid| read_string_list(kb, syms, tid))
        .unwrap_or_default();
    let structured = get_named_arg(kb, named, "body")
        .map(|t| is_structured_body(kb, t))
        .unwrap_or(false);
    Some(ProofRec { rid: Some(rid), rule, strategy, using, structured, abstract_body: false })
}

/// True if `body_tid` is the `ProofBodyStructured` constructor (proposal 031).
fn is_structured_body(kb: &KnowledgeBase, body_tid: TermId) -> bool {
    let functor = match kb.get_term(body_tid) {
        Term::Fn { functor, .. } => *functor,
        _ => return false,
    };
    kb.qualified_name_of(functor) == "anthill.realization.ProofBodyStructured"
}

fn has_auto_registered_witness(
    kb: &KnowledgeBase,
    syms: &ProofSyms,
    named: &smallvec::SmallVec<[(Symbol, TermId); 2]>,
) -> bool {
    let witness_tid = match get_named_arg(kb, named, "witness") {
        Some(t) => t,
        None => return false,
    };
    let witness_functor = match kb.get_term(witness_tid) {
        Term::Fn { functor, .. } => *functor,
        _ => return false,
    };
    Some(witness_functor) == syms.scope_axiom
        || Some(witness_functor) == syms.specialization
}

/// Walk a `cons(head: <String const>, tail: ...)` list and collect
/// the head strings. Returns empty vec for a `nil`-only list. Used
/// to read the cited-lemma list from a ProofRecord's `using` field.
fn read_string_list(kb: &KnowledgeBase, syms: &ProofSyms, mut tid: TermId) -> Vec<String> {
    let mut out = Vec::new();
    for _ in 0..MAX_LIST_LEN {
        let (functor, named) = match kb.get_term(tid) {
            Term::Fn { functor, named_args, .. } => (*functor, named_args),
            _ => break,
        };
        if syms.cons != Some(functor) { break; }
        if let Some(h) = get_named_arg(kb, named, "head") {
            if let Term::Const(Literal::String(s)) = kb.get_term(h) {
                out.push(s.clone());
            }
        }
        match get_named_arg(kb, named, "tail") {
            Some(t) => tid = t,
            None => break,
        }
    }
    out
}

fn read_strategy(kb: &KnowledgeBase, syms: &ProofSyms, tid: TermId) -> Strategy {
    let (functor, named) = match kb.get_term(tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args),
        _ => return Strategy::Open,
    };
    if syms.open == Some(functor) {
        return Strategy::Open;
    }
    let tool = lookup_string(kb, named, "name").unwrap_or_default();
    let args = get_named_arg(kb, named, "args")
        .map(|tid| read_named_arg_list(kb, syms, tid))
        .unwrap_or_default();
    Strategy::Tool { name: tool, args }
}

const MAX_LIST_LEN: usize = 1024;

fn read_named_arg_list(kb: &KnowledgeBase, syms: &ProofSyms, mut tid: TermId) -> Vec<NamedArg> {
    let mut out = Vec::new();
    for _ in 0..MAX_LIST_LEN {
        let (functor, named) = match kb.get_term(tid) {
            Term::Fn { functor, named_args, .. } => (*functor, named_args),
            _ => break,
        };
        if syms.cons != Some(functor) { break; }
        if let Some(h) = get_named_arg(kb, named, "head") {
            if let Some(arg) = read_named_arg(kb, syms, h) {
                out.push(arg);
            }
        }
        match get_named_arg(kb, named, "tail") {
            Some(t) => tid = t,
            None => break,
        }
    }
    out
}

fn read_named_arg(kb: &KnowledgeBase, syms: &ProofSyms, tid: TermId) -> Option<NamedArg> {
    let (functor, named) = match kb.get_term(tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args),
        _ => return None,
    };
    // Symbol comparison falls through if the cached symbol isn't
    // populated (try_resolve_symbol("named_arg") may return None for
    // bare-interned symbols), so also accept by short-name match.
    let matches = syms.named_arg == Some(functor)
        || kb.qualified_name_of(functor).rsplit('.').next() == Some("named_arg");
    if !matches { return None; }
    let key = lookup_string(kb, named, "name")?;
    let val_tid = get_named_arg(kb, named, "value")?;
    let value = match kb.get_term(val_tid) {
        Term::Const(Literal::String(s)) => ArgValue::String(s.clone()),
        Term::Const(Literal::Int(n))    => ArgValue::Int(*n),
        Term::Const(Literal::Float(f))  => ArgValue::Float(f.into_inner()),
        Term::Const(Literal::Bool(b))   => ArgValue::Bool(*b),
        Term::Fn { .. } | Term::Ident(_) | Term::Ref(_) => ArgValue::Term(val_tid),
        _ => ArgValue::Other,
    };
    Some(NamedArg { key, value })
}

fn lookup_string(
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

enum Verdict {
    Proved,
    Disproved(String),
    Unknown(String),
    Skipped(String),
    EmitError(String),
}

/// Outcome of an SMT-discharge subquery: verdict for user-facing
/// reporting + an optional `ProofWitness` for the kernel registry
/// (proposal 030 phase α.3) + the visited-rule set the discharge
/// consulted (phase α.4 — drives the per-ProofRecord state hash).
/// The witness is populated when the backend produced a real
/// verdict (Proved / Disproved / Unknown); it's `None` for Skipped
/// (dry-run, solver missing) and EmitError outcomes. `visited_rules`
/// is populated whenever a discharge actually walked KB content —
/// empty for early-exit verdicts where no kb-state slice was
/// consulted.
struct DispatchOutcome {
    verdict: Verdict,
    witness: Option<ProofWitness>,
    visited_rules: BTreeSet<String>,
}

impl DispatchOutcome {
    fn no_witness(verdict: Verdict) -> Self {
        DispatchOutcome {
            verdict,
            witness: None,
            visited_rules: BTreeSet::new(),
        }
    }
}

fn dispatch(
    kb: &mut KnowledgeBase,
    rec: &ProofRec,
    args: &ProveArgs,
    stats: &mut CacheStats,
    discharged_this_run: &mut std::collections::HashMap<String, DischargeKind>,
) -> DispatchOutcome {
    if rec.structured {
        return dispatch_structured(kb, rec, args, stats, discharged_this_run);
    }
    let (tool, tool_args) = match &rec.strategy {
        Strategy::Open => return DispatchOutcome::no_witness(
            Verdict::Skipped("open obligation (no `by` clause)".into())),
        Strategy::Tool { name, args } => (name.as_str(), args.as_slice()),
    };
    match tool {
        "z3" => dispatch_z3(kb, &rec.rule, tool_args, &rec.using, rec.abstract_body, args, stats, discharged_this_run),
        "test" => DispatchOutcome::no_witness(
            Verdict::Skipped("`by test` not yet wired".into())),
        "derivation" => dispatch_derivation(kb, &rec.rule, tool_args),
        "trust" => dispatch_trust(tool_args),
        other => DispatchOutcome::no_witness(
            Verdict::Skipped(format!("unknown strategy `{other}`"))),
    }
}

// ── WI-558: in-KB result write-back ──────────────────────────────────
//
// After dispatch, flip each ProofRecord's `result` (Pending → Discharged |
// Failed) so the loaded KB reflects the prove verdicts for every tier — through
// the same `set_proof_result` helper the in-process `verify_proofs` pass uses,
// so the two paths stay in lockstep. The authoritative cross-invocation witness
// store is still the sidecar (proposal 030 OQ-D); this is the in-process
// consistency copy.
//
// Today the standalone `anthill prove` discards `kb` on return, so this flip is
// not yet CLI-observable on its own; it becomes load-bearing once the gate is
// chained into `anthill check` (deferred, local-proof.md OQ-A) and for any
// caller that drives `run_prove` over a KB it keeps. The flips are collected
// during the dispatch loop and applied *after* it, so a retract/re-assert never
// perturbs in-loop cite resolution.

/// Map a dispatch verdict to the core [`VerdictWrite`], encoding the witness
/// term inline (needs `&mut kb`). `Skipped` / `EmitError` reached no verdict,
/// so the record stays Pending (returns `None` — no write-back).
fn verdict_write_for(
    kb: &mut KnowledgeBase,
    verdict: &Verdict,
    witness: &Option<ProofWitness>,
    rec: &ProofRec,
) -> Option<VerdictWrite> {
    match verdict {
        Verdict::Proved => witness.as_ref().map(|w| VerdictWrite::Discharged {
            witness: witness_to_term(kb, w),
            solver: solver_name(rec),
        }),
        Verdict::Disproved(model) => Some(VerdictWrite::FailedDisproved {
            counterexample: model.clone(),
            solver: solver_name(rec),
        }),
        Verdict::Unknown(reason) => Some(VerdictWrite::FailedUnknown { reason: reason.clone() }),
        Verdict::Skipped(_) | Verdict::EmitError(_) => None,
    }
}

fn solver_name(rec: &ProofRec) -> String {
    match &rec.strategy {
        Strategy::Tool { name, .. } => name.clone(),
        Strategy::Open => "open".to_string(),
    }
}

fn str_const(kb: &mut KnowledgeBase, s: &str) -> TermId {
    kb.alloc(Term::Const(Literal::String(s.to_string())))
}

/// Encode a cli [`ProofWitness`] as a `ProofWitness` reflect term for the in-KB
/// `ProofRecord` fields. Covers the shapes a prove dispatch produces
/// (SmtDischarge / SldDerivation / TrustedAxiom / MetaCompose). The loader-only
/// ScopeAxiom / Specialization shapes are skipped by `read_proof_record`, so
/// reaching them here is a broken invariant — surfaced loudly (`debug_assert`)
/// while degrading to a descriptive marker in release rather than corrupting a
/// kernel-derived certificate into a panic mid-run.
fn witness_to_term(kb: &mut KnowledgeBase, w: &ProofWitness) -> TermId {
    match w {
        ProofWitness::SldDerivation { tree_hash } => {
            anthill_core::kb::proof_verify::make_sld_witness(kb, tree_hash)
        }
        ProofWitness::TrustedAxiom { reason } => trusted_axiom_term(kb, reason),
        ProofWitness::SmtDischarge { backend, logic, document_hash, verdict, core } => {
            let sym = kb.resolve_symbol("anthill.realization.witness.ProofWitness.SmtDischarge");
            let b = str_const(kb, backend);
            let l = str_const(kb, logic);
            let dh = str_const(kb, document_hash);
            let v = smt_verdict_to_term(kb, verdict);
            let c = option_string_to_term(kb, core.as_deref());
            let k_b = kb.intern("backend");
            let k_l = kb.intern("logic");
            let k_d = kb.intern("document_hash");
            let k_v = kb.intern("verdict");
            let k_c = kb.intern("core");
            kb.make_entity_term(
                sym,
                SmallVec::new(),
                SmallVec::from_slice(&[(k_b, b), (k_l, l), (k_d, dh), (k_v, v), (k_c, c)]),
            )
        }
        ProofWitness::MetaCompose { tactic_name, sub } => {
            let sym = kb.resolve_symbol("anthill.realization.witness.ProofWitness.MetaCompose");
            let tn = str_const(kb, tactic_name);
            let mut sub_terms = Vec::with_capacity(sub.len());
            for s in sub {
                sub_terms.push(witness_to_term(kb, s));
            }
            let sub_list = kb.build_list(&sub_terms);
            let k_t = kb.intern("tactic_name");
            let k_s = kb.intern("sub");
            kb.make_entity_term(
                sym,
                SmallVec::new(),
                SmallVec::from_slice(&[(k_t, tn), (k_s, sub_list)]),
            )
        }
        ProofWitness::ScopeAxiom { scope_kind, scope_qn, aspect } => {
            debug_assert!(false, "witness_to_term: kernel ScopeAxiom reached the prove write-back");
            trusted_axiom_term(kb, &format!("scope-axiom {scope_kind} {scope_qn} {aspect}"))
        }
        ProofWitness::Specialization { parametric, .. } => {
            debug_assert!(false, "witness_to_term: kernel Specialization reached the prove write-back");
            trusted_axiom_term(kb, &format!("specialization of {parametric}"))
        }
    }
}

fn trusted_axiom_term(kb: &mut KnowledgeBase, reason: &str) -> TermId {
    let sym = kb.resolve_symbol("anthill.realization.witness.ProofWitness.TrustedAxiom");
    let r = str_const(kb, reason);
    let k = kb.intern("reason");
    kb.make_entity_term(sym, SmallVec::new(), SmallVec::from_slice(&[(k, r)]))
}

fn smt_verdict_to_term(kb: &mut KnowledgeBase, v: &SmtVerdict) -> TermId {
    match v {
        SmtVerdict::Unsat => {
            let sym = kb.resolve_symbol("anthill.realization.witness.SmtVerdict.Unsat");
            kb.make_entity_term(sym, SmallVec::new(), SmallVec::new())
        }
        SmtVerdict::Sat { model_hash } => {
            let sym = kb.resolve_symbol("anthill.realization.witness.SmtVerdict.Sat");
            let m = str_const(kb, model_hash);
            let k = kb.intern("model_hash");
            kb.make_entity_term(sym, SmallVec::new(), SmallVec::from_slice(&[(k, m)]))
        }
        SmtVerdict::Unknown { reason } => {
            let sym = kb.resolve_symbol("anthill.realization.witness.SmtVerdict.Unknown");
            let r = str_const(kb, reason);
            let k = kb.intern("reason");
            kb.make_entity_term(sym, SmallVec::new(), SmallVec::from_slice(&[(k, r)]))
        }
    }
}

fn option_string_to_term(kb: &mut KnowledgeBase, s: Option<&str>) -> TermId {
    match s {
        None => {
            let sym = kb.resolve_symbol("anthill.prelude.Option.none");
            kb.make_entity_term(sym, SmallVec::new(), SmallVec::new())
        }
        Some(v) => {
            let sym = kb.resolve_symbol("anthill.prelude.Option.some");
            let val = str_const(kb, v);
            let k = kb.intern("value");
            kb.make_entity_term(sym, SmallVec::new(), SmallVec::from_slice(&[(k, val)]))
        }
    }
}

/// `proof X by trust(reason: "<reason>") end` — explicit user
/// trust: the rule's claim is asserted axiomatically with no
/// kernel check. Produces a `ProofWitness::TrustedAxiom { reason }`;
/// the witness flows through γ.2's `cite_status` (returns
/// `Trusted(reason)` to consumers) and β.6's aggregation
/// (surfaces the reason through containing MetaCompose witnesses).
///
/// Use cases:
///   - Geometric laws not derivable in QF_LRA / QF_NRA (triangle
///     inequality on Euclidean norm).
///   - Sensor / inner-loop specs treated as physical assumptions
///     (Mavic2Pro velocity envelope, GPS error bound).
///   - Bridge claims that decompose into hybrid-systems content
///     pending a richer backend (dReal, KeYmaera X).
///
/// `anthill check --report-trust` lists every rule whose witness
/// tree contains a TrustedAxiom, so the trust surface is auditable.
fn dispatch_trust(tool_args: &[NamedArg]) -> DispatchOutcome {
    let reason = tool_args.iter()
        .find(|a| a.key == "reason")
        .and_then(|a| match &a.value {
            ArgValue::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_else(|| "(no reason given)".to_string());
    DispatchOutcome {
        verdict: Verdict::Proved,
        witness: Some(ProofWitness::TrustedAxiom { reason }),
        // No KB state was consulted — the rule's claim is
        // axiomatic, not derived. visited_rules empty.
        visited_rules: BTreeSet::new(),
    }
}

// ── Structured proof dispatch (proposal 031 phase b) ─────────────

/// One decoded step from a `ProofBodyStructured` term — ready for
/// transient-rule synthesis and dispatch.
struct DecodedStep {
    /// Resolved qualified name `<parent_proof_qn>.<label>` — used as
    /// the synthesized KB rule's QN and as a discharged-this-run key.
    qn: String,
    head_term: TermId,
    body_terms: Vec<TermId>,
    using: Vec<String>,
    strategy: Strategy,
}

struct DecodedConclude {
    using: Vec<String>,
    strategy: Strategy,
}

/// Walk a cons-list of TermIds — siblings of `read_string_list` for
/// term-valued payloads. Returns the head TermId of each cons cell.
fn read_term_list(kb: &KnowledgeBase, syms: &ProofSyms, mut tid: TermId) -> Vec<TermId> {
    let mut out = Vec::new();
    for _ in 0..MAX_LIST_LEN {
        let (functor, named) = match kb.get_term(tid) {
            Term::Fn { functor, named_args, .. } => (*functor, named_args),
            _ => break,
        };
        if syms.cons != Some(functor) { break; }
        if let Some(h) = get_named_arg(kb, named, "head") {
            out.push(h);
        }
        match get_named_arg(kb, named, "tail") {
            Some(t) => tid = t,
            None => break,
        }
    }
    out
}

/// Decode a single `ProofStep` term. Returns None if the term isn't
/// a ProofStep (e.g. malformed body).
fn read_proof_step(
    kb: &KnowledgeBase,
    syms: &ProofSyms,
    parent_qn: &str,
    tid: TermId,
) -> Option<DecodedStep> {
    let named = match kb.get_term(tid) {
        Term::Fn { named_args, .. } => named_args,
        _ => return None,
    };
    let label = lookup_string(kb, named, "label").unwrap_or_default();
    let head_term = get_named_arg(kb, named, "head_term")?;
    let body_terms = get_named_arg(kb, named, "body_terms")
        .map(|t| read_term_list(kb, syms, t))
        .unwrap_or_default();
    let using = get_named_arg(kb, named, "using_names")
        .map(|t| read_string_list(kb, syms, t))
        .unwrap_or_default();
    let strategy = get_named_arg(kb, named, "tactic")
        .map(|t| read_strategy(kb, syms, t))
        .unwrap_or(Strategy::Open);
    let qn = if label.is_empty() {
        format!("{parent_qn}.<unnamed>")
    } else {
        format!("{parent_qn}.{label}")
    };
    Some(DecodedStep { qn, head_term, body_terms, using, strategy })
}

fn read_proof_conclude(
    kb: &KnowledgeBase,
    syms: &ProofSyms,
    tid: TermId,
) -> Option<DecodedConclude> {
    let named = match kb.get_term(tid) {
        Term::Fn { named_args, .. } => named_args,
        _ => return None,
    };
    let using = get_named_arg(kb, named, "using_names")
        .map(|t| read_string_list(kb, syms, t))
        .unwrap_or_default();
    let strategy = get_named_arg(kb, named, "tactic")
        .map(|t| read_strategy(kb, syms, t))
        .unwrap_or(Strategy::Open);
    Some(DecodedConclude { using, strategy })
}

/// Decode the structured body of a parent proof. The body term is
/// the `body` field of the parent's `ProofRecord` fact. Returns
/// (steps, conclude) where conclude is None when the parent body
/// has no concluding clause.
fn read_structured_body(
    kb: &KnowledgeBase,
    syms: &ProofSyms,
    parent_qn: &str,
    body_tid: TermId,
) -> Option<(Vec<DecodedStep>, Option<DecodedConclude>)> {
    let named = match kb.get_term(body_tid) {
        Term::Fn { named_args, .. } => named_args,
        _ => return None,
    };
    let steps_list = get_named_arg(kb, named, "steps")?;
    let step_tids = read_term_list(kb, syms, steps_list);
    let steps: Vec<DecodedStep> = step_tids.iter()
        .filter_map(|&t| read_proof_step(kb, syms, parent_qn, t))
        .collect();
    let conclude = get_named_arg(kb, named, "conclude")
        .and_then(|t| {
            // `Bottom` marks an absent conclude clause.
            if matches!(kb.get_term(t), Term::Bottom) { None }
            else { read_proof_conclude(kb, syms, t) }
        });
    Some((steps, conclude))
}

/// Synthesize a transient KB rule for a structured-proof step so
/// the standard cite-resolution path (lift_rule_to_implication_clause
/// in smt-gen) can pick it up via `using <step_qn>`. Head IS the
/// step's claim (proposal 032 unified encoding); the step is tagged
/// with `step_qn` as its label so `rule_id_by_qn` resolves it. The
/// rule is registered in the global scope; re-registration (same
/// step_qn) is idempotent.
///
/// When `parent_qn` resolves to an existing rule, the step is
/// asserted in that parent's variable frame so shared variable
/// names produce identical DeBruijn indices — the cited-step lift
/// then chains arithmetically with the parent's body in the
/// consumer's preamble.
fn synthesize_step_rule(
    kb: &mut KnowledgeBase,
    step_qn: &str,
    parent_qn: &str,
    body_terms: Vec<TermId>,
    head_term: TermId,
) {
    use anthill_core::intern::SymbolKind;
    let short_name = step_qn.rsplit('.').next().unwrap_or(step_qn);
    let global_scope = kb.make_name_term("_global");
    let label_sym = kb.define_symbol(short_name, step_qn, SymbolKind::Rule, global_scope.raw());
    if kb.rule_id_by_qn(step_qn).is_some() {
        return;
    }
    let rule_sort = kb.make_name_term("Rule");

    let parent_globals: Vec<_> = kb.rule_id_by_qn(parent_qn)
        .map(|rid| kb.rule_globals(rid).to_vec())
        .unwrap_or_default();

    let body_nodes = kb.term_body_to_nodes(&body_terms);
    let rid = kb.assert_rule_debruijn_with_nodes_in_frame(
        head_term,
        body_nodes,
        &parent_globals,
        rule_sort,
        global_scope,
        None,
    );
    kb.set_rule_label(rid, label_sym);
}

/// Phase-b dispatch for a structured proof body (proposal 031).
///
/// Algorithm:
///   1. Decode the body term to extract steps + optional conclude.
///   2. For each step: synthesize a transient KB rule under the
///      resolved step QN, build a synthetic `ProofRec`, dispatch
///      via the standard `dispatch()` path, record the resulting
///      witness in `discharged_this_run` so subsequent steps and
///      the concluding clause can cite it through the existing
///      `using` machinery.
///   3. Concluding clause: dispatch the parent rule with
///      `using = parent.using ∪ conclude.using ∪ {step QNs}`.
///   4. Wrap all sub-witnesses in
///      `MetaCompose { tactic_name: "structured", sub: [...] }`.
///
/// Failure mode: the first step that doesn't `Proved` aborts the
/// chain — its verdict surfaces directly so the user sees the
/// failing step, not an opaque "structured proof failed".
fn dispatch_structured(
    kb: &mut KnowledgeBase,
    rec: &ProofRec,
    args: &ProveArgs,
    stats: &mut CacheStats,
    discharged_this_run: &mut std::collections::HashMap<String, DischargeKind>,
) -> DispatchOutcome {
    let syms = ProofSyms::new(kb);
    // Re-fetch the parent ProofRecord's body term — `rec` doesn't
    // carry it, so we walk rules_by_functor for ProofRecord and find the
    // record for this rule QN.
    let body_tid = match find_proof_body_term(kb, &syms, &rec.rule) {
        Some(t) => t,
        None => return DispatchOutcome::no_witness(Verdict::EmitError(format!(
            "structured proof for `{}`: could not locate body term in KB", rec.rule
        ))),
    };
    let (steps, conclude) = match read_structured_body(kb, &syms, &rec.rule, body_tid) {
        Some(x) => x,
        None => return DispatchOutcome::no_witness(Verdict::EmitError(format!(
            "structured proof for `{}`: malformed ProofBodyStructured term", rec.rule
        ))),
    };
    if steps.is_empty() {
        return DispatchOutcome::no_witness(Verdict::EmitError(format!(
            "structured proof for `{}`: no steps", rec.rule
        )));
    }

    let mut sub_witnesses: Vec<ProofWitness> = Vec::new();
    let mut step_qns: Vec<String> = Vec::new();
    let mut visited_rules: BTreeSet<String> = BTreeSet::new();

    for step in &steps {
        synthesize_step_rule(kb, &step.qn, &rec.rule, step.body_terms.clone(), step.head_term);
        let step_rec = ProofRec {
            // Synthetic: a structured step has no source ProofRecord fact, so it
            // is dispatched but never result-written-back.
            rid: None,
            rule: step.qn.clone(),
            strategy: clone_strategy(&step.strategy),
            using: step.using.clone(),
            structured: false,
            abstract_body: false,
        };
        let outcome = dispatch(kb, &step_rec, args, stats, discharged_this_run);
        visited_rules.extend(outcome.visited_rules);
        match outcome.verdict {
            Verdict::Proved => {
                let kind = match &outcome.witness {
                    Some(ProofWitness::TrustedAxiom { reason }) =>
                        DischargeKind::Trusted(reason.clone()),
                    _ => DischargeKind::Sound,
                };
                discharged_this_run.insert(step.qn.clone(), kind);
                if let Some(w) = outcome.witness {
                    sub_witnesses.push(w);
                }
                step_qns.push(step.qn.clone());
            }
            other => return DispatchOutcome {
                verdict: other,
                witness: None,
                visited_rules,
            },
        }
    }

    let (conclude_strategy, mut conclude_using) = match conclude {
        Some(c) => (c.strategy, c.using),
        None => (Strategy::Open, Vec::new()),
    };
    for qn in &step_qns {
        if !conclude_using.contains(qn) {
            conclude_using.push(qn.clone());
        }
    }
    for u in &rec.using {
        if !conclude_using.contains(u) {
            conclude_using.push(u.clone());
        }
    }
    let parent_rec = ProofRec {
        // Synthetic re-dispatch of the parent rule (its verdict is folded into
        // the structured MetaCompose witness); the original `rec` carries the
        // RuleId that gets written back, not this one.
        rid: None,
        rule: rec.rule.clone(),
        strategy: conclude_strategy,
        using: conclude_using,
        structured: false,
        // Render the parent's body abstractly so transitive rule
        // calls (`distance_at_step` → `position_distance_sq` → ground
        // pose data) don't pollute the LRA preamble. Cited step
        // lifts already constrain the relevant variables.
        abstract_body: true,
    };
    let final_outcome = dispatch(kb, &parent_rec, args, stats, discharged_this_run);
    visited_rules.extend(final_outcome.visited_rules);
    match final_outcome.verdict {
        Verdict::Proved => {
            if let Some(w) = final_outcome.witness {
                sub_witnesses.push(w);
            }
            DispatchOutcome {
                verdict: Verdict::Proved,
                witness: Some(ProofWitness::MetaCompose {
                    tactic_name: "structured".to_string(),
                    sub: sub_witnesses,
                }),
                visited_rules,
            }
        }
        other => DispatchOutcome {
            verdict: other,
            witness: None,
            visited_rules,
        },
    }
}

/// Locate the `body` term of a parent ProofRecord by walking
/// the by-functor index for ProofRecord and matching the `rule`
/// field. None when no record exists for the given QN (which
/// shouldn't happen for a record that reached `dispatch`).
fn find_proof_body_term(
    kb: &KnowledgeBase,
    syms: &ProofSyms,
    rule_qn: &str,
) -> Option<TermId> {
    let functor = kb.try_resolve_symbol("anthill.realization.ProofRecord")?;
    for rid in kb.rules_by_functor(functor) {
        let head = kb.rule_head(rid);
        let named = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args,
            _ => continue,
        };
        if has_auto_registered_witness(kb, syms, named) {
            continue;
        }
        let rule = match lookup_string(kb, named, "rule") {
            Some(s) => s,
            None => continue,
        };
        if rule == rule_qn {
            return get_named_arg(kb, named, "body");
        }
    }
    None
}

/// Manual clone for `Strategy` — derive(Clone) would propagate to
/// every sub-type, so we spell it out for the structured-proof
/// dispatch path.
fn clone_strategy(s: &Strategy) -> Strategy {
    match s {
        Strategy::Open => Strategy::Open,
        Strategy::Tool { name, args } => Strategy::Tool {
            name: name.clone(),
            args: args.iter().map(|a| NamedArg {
                key: a.key.clone(),
                value: clone_arg_value(&a.value),
            }).collect(),
        },
    }
}

fn clone_arg_value(v: &ArgValue) -> ArgValue {
    match v {
        ArgValue::String(s) => ArgValue::String(s.clone()),
        ArgValue::Int(n) => ArgValue::Int(*n),
        ArgValue::Float(f) => ArgValue::Float(*f),
        ArgValue::Bool(b) => ArgValue::Bool(*b),
        ArgValue::Term(t) => ArgValue::Term(*t),
        ArgValue::Other => ArgValue::Other,
    }
}

fn dispatch_derivation(
    kb: &mut KnowledgeBase,
    rule_qn: &str,
    tool_args: &[NamedArg],
) -> DispatchOutcome {
    use anthill_core::kb::proof_verify::{discharge_by_derivation, DerivationOutcome};

    let mut max_depth: usize = anthill_core::kb::proof_verify::DEFAULT_DERIVATION_DEPTH;
    let mut max_solutions: usize = 1;
    for arg in tool_args {
        match (arg.key.as_str(), &arg.value) {
            ("max_depth", ArgValue::Int(n)) if *n > 0 => max_depth = *n as usize,
            ("max_solutions", ArgValue::Int(n)) if *n >= 0 => max_solutions = *n as usize,
            _ => {}
        }
    }

    // WI-558: the SLD discharge itself now lives in `anthill-core`
    // (`discharge_by_derivation`), so the cli `prove` driver and the in-process
    // `verify_proofs` pass never drift on what counts as a derivation. This
    // wrapper keeps the cli's verdict / witness / visited-rules surface.
    //
    // Phase α.3 witness: a placeholder `tree_hash` referencing the rule QN
    // (α.5 introduces full derivation-tree capture). Phase α.4: visited_rules
    // is the coarse `{rule_qn}` placeholder until the resolver surfaces its
    // visited-rule set.
    let visited: BTreeSet<String> = std::iter::once(rule_qn.to_string()).collect();
    match discharge_by_derivation(kb, rule_qn, max_depth, max_solutions) {
        DerivationOutcome::Proved { tree_hash } => DispatchOutcome {
            verdict: Verdict::Proved,
            witness: Some(ProofWitness::SldDerivation { tree_hash }),
            visited_rules: visited,
        },
        DerivationOutcome::NoDerivation => DispatchOutcome::no_witness(Verdict::Unknown(
            format!("no derivation found within depth {max_depth} for `{rule_qn}`"),
        )),
        DerivationOutcome::RuleNotFound => DispatchOutcome::no_witness(Verdict::EmitError(
            format!("rule `{rule_qn}` not in KB"),
        )),
        DerivationOutcome::NoRules => DispatchOutcome::no_witness(Verdict::EmitError(
            format!("no rules found for `{rule_qn}`"),
        )),
    }
}

fn dispatch_z3(
    kb: &mut KnowledgeBase,
    rule_qn: &str,
    tool_args: &[NamedArg],
    using: &[String],
    abstract_body: bool,
    cli: &ProveArgs,
    stats: &mut CacheStats,
    discharged_this_run: &std::collections::HashMap<String, DischargeKind>,
) -> DispatchOutcome {
    let mut config = ProofConfig::default();
    config.abstract_body = abstract_body;
    let mut canon_parts: Vec<String> = Vec::new();
    let mut tactic_term: Option<TermId> = None;
    // Render each cited lemma's body via smt-gen and stash the
    // resulting clauses as `(assert ...)` hypotheses for this proof.
    // We re-use `emit_satisfiability_check_with_deps` with a default
    // ProofConfig (no tactic, no outcome flags) — we only need the
    // body assertions, not the discharge envelope. The cited rule's
    // own body assertions become AND-ed conjuncts.
    // Phase γ.4: combine the user-stated `using` list with implicit
    // citations from the rule's enclosing scope chain. Each parent
    // scope contributes its auto-registered `<scope>.requires.<SE>`
    // ProofRecords (α.6). Explicit cites come first; implicit ones
    // appended in order, deduped against the explicit set.
    let implicit = implicit_cites_for(rule_qn, kb);
    let hints = hint_cites_for(rule_qn, kb);
    let mut effective: Vec<String> = using.iter().cloned().collect();
    for qn in implicit {
        if !effective.contains(&qn) {
            effective.push(qn);
        }
    }
    for qn in hints {
        if !effective.contains(&qn) {
            effective.push(qn);
        }
    }
    match render_cited_lemmas(kb, &effective, rule_qn, cli, discharged_this_run) {
        Ok(Some(clauses)) => {
            config.assumptions = clauses;
            canon_parts.push(format!("using={}", effective.join(",")));
        }
        Ok(None) => {}
        Err(msg) => {
            return DispatchOutcome::no_witness(Verdict::EmitError(msg));
        }
    }
    for arg in tool_args {
        match (arg.key.as_str(), &arg.value) {
            ("logic", ArgValue::String(s)) => {
                config.logic = Some(s.clone());
                canon_parts.push(format!("logic={s}"));
            }
            ("timeout", ArgValue::Int(n)) if *n >= 0 => {
                config.timeout_ms = Some(*n as u32);
                canon_parts.push(format!("timeout={n}"));
            }
            ("tactic", ArgValue::Term(t)) => tactic_term = Some(*t),
            ("model", ArgValue::Term(_)) | ("model", _) => {
                if let Some(b) = bool_of(&arg.value) {
                    config.produce_models = b;
                    canon_parts.push(format!("model={b}"));
                }
            }
            ("cores", _) => {
                if let Some(b) = bool_of(&arg.value) {
                    config.produce_unsat_cores = b;
                    canon_parts.push(format!("cores={b}"));
                }
            }
            ("interpolation", _) => {
                if let Some(b) = bool_of(&arg.value) {
                    config.produce_interpolants = b;
                    canon_parts.push(format!("interp={b}"));
                }
            }
            _ => {}
        }
    }
    // Meta-tactic dispatch: ranking expands to two sub-queries
    // (boundedness, decrease). Detected before the standard tactic-
    // expression path because it doesn't reduce to one Z3 call.
    if let Some(t) = tactic_term {
        if let Some((b_qn, d_qn)) = recognise_ranking_tactic(kb, t) {
            return dispatch_ranking(kb, rule_qn, &b_qn, &d_qn, &config, cli, stats);
        }
        if let Some(ind) = recognise_induction_tactic(kb, t) {
            return dispatch_induction(kb, rule_qn, &ind, &config, cli, stats);
        }
        config.tactic_expr = emit_tactic_from_term(kb, t);
        if let Some(expr) = &config.tactic_expr {
            canon_parts.push(format!("tactic={expr}"));
        }
    }
    let tactic_canon = format!("z3({})", canon_parts.join(","));
    run_smt_subquery(kb, rule_qn, &config, &tactic_canon, cli, stats)
}

/// Render each cited-lemma rule as a forall-quantified implication
/// clause via `lift_rule_to_implication_clause` — see WI-C1.
///
/// Phase γ.1 + γ.2 (proposal 030): every cite is gated on the
/// cited rule's ProofRecord being **discharged**. The check is:
///   1. Its witness shape must be ScopeAxiom or Specialization
///      (kernel-derived; discharged-by-construction); OR
///   2. A witness sidecar exists at the cited rule QN — proof that
///      a successful prove run persisted the witness; OR
///   3. The witness is TrustedAxiom — explicit user trust, allowed
///      but flagged.
/// Otherwise: hard error. This closes the silent-axiom-acceptance
/// hole that the previous text-only `lift_rule_to_implication_clause`
/// path left open.
///
/// Returns:
///   - `Ok(Some(clauses))` — list of forall-quantified implications
///     ready to splice into the consumer's `(assert …)` preamble.
///   - `Ok(None)` — empty cite list (or only self-citation).
///   - `Err(message)` — at least one cited rule is not discharged.
///     The consumer's discharge fails with this message instead of
///     proceeding under unverified assumptions.
fn render_cited_lemmas(
    kb: &KnowledgeBase,
    using: &[String],
    target_rule_qn: &str,
    cli: &ProveArgs,
    discharged_this_run: &std::collections::HashMap<String, DischargeKind>,
) -> Result<Option<Vec<String>>, String> {
    if using.is_empty() { return Ok(None); }
    let mut clauses = Vec::with_capacity(using.len());
    for cited in using {
        if cited == target_rule_qn { continue; }
        match cite_status(kb, cited, cli, discharged_this_run) {
            CiteStatus::Discharged => {}
            CiteStatus::Trusted(reason) => {
                eprintln!(
                    "warning: `using {cited}` (in proof `{target_rule_qn}`) \
                     depends on TrustedAxiom: {reason}"
                );
            }
            CiteStatus::NotFound => {
                return Err(format!(
                    "cite `{cited}` (in proof `{target_rule_qn}`) is unknown — \
                     no ProofRecord found for that rule. Did you misspell, or \
                     is the rule outside the loaded namespace?"
                ));
            }
            CiteStatus::Pending => {
                return Err(format!(
                    "cite `{cited}` (in proof `{target_rule_qn}`) is not \
                     discharged. Run `anthill prove` on `{cited}` first, or \
                     remove the `using` clause."
                ));
            }
        }
        match lift_rule_to_implication_clause(kb, cited) {
            Ok(lifted) => clauses.extend(lifted),
            Err(e) => {
                return Err(format!(
                    "cite `{cited}` (in proof `{target_rule_qn}`) could not be \
                     lifted to an implication clause: {}",
                    e.message
                ));
            }
        }
    }
    if clauses.is_empty() { Ok(None) } else { Ok(Some(clauses)) }
}

/// How a within-invocation discharge resolved — used to route
/// later cites of the same rule through the right `CiteStatus`
/// path so trust still surfaces even when cited within the same
/// prove run.
#[derive(Debug, Clone)]
enum DischargeKind {
    /// Solver / derivation / meta-tactic discharge with no
    /// transitively-trusted leaves.
    Sound,
    /// `by trust(reason: ...)` discharge — the reason propagates
    /// to consumers via `CiteStatus::Trusted`.
    Trusted(String),
}

/// The cite-resolution outcome for a single `using <Y>` reference.
enum CiteStatus {
    /// Y has a discharged proof — its witness is kernel-derived
    /// (ScopeAxiom / Specialization) or a sidecar exists.
    Discharged,
    /// Y's witness is TrustedAxiom — allowed but the trust flag
    /// surfaces in CLI output.
    Trusted(String),
    /// No ProofRecord found for Y.
    NotFound,
    /// Y's ProofRecord exists but is Pending or Failed (no sidecar
    /// to back it up).
    Pending,
}

/// Resolve a cite to a `CiteStatus`. Resolution order:
///   1. `discharged_this_run` set — rules proved earlier in this
///      same prove invocation (catches within-run chains even when
///      --no-cache disables sidecar persistence).
///   2. KB ProofRecord witness shape — kernel-derived (ScopeAxiom,
///      Specialization) records are discharged-by-construction;
///      TrustedAxiom (non-placeholder) is allowed but flagged.
///   3. Witness sidecar on disk — the witness was persisted by an
///      earlier `anthill prove` run.
fn cite_status(
    kb: &KnowledgeBase,
    cited_qn: &str,
    cli: &ProveArgs,
    discharged_this_run: &std::collections::HashMap<String, DischargeKind>,
) -> CiteStatus {
    if let Some(kind) = discharged_this_run.get(cited_qn) {
        return match kind {
            DischargeKind::Sound => CiteStatus::Discharged,
            DischargeKind::Trusted(reason) => CiteStatus::Trusted(reason.clone()),
        };
    }
    let record_sym = match kb.try_resolve_symbol("anthill.realization.ProofRecord") {
        Some(s) => s,
        None => return CiteStatus::NotFound,
    };
    let mut found_record = false;
    for rid in kb.rules_by_functor(record_sym) {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head(rid);
        let named = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args,
            _ => continue,
        };
        let qn_match = get_named_arg(kb, named, "rule")
            .and_then(|tid| match kb.get_term(tid) {
                Term::Const(Literal::String(s)) => Some(s.as_str() == cited_qn),
                _ => None,
            }).unwrap_or(false);
        if !qn_match { continue; }
        found_record = true;
        if let Some(witness_tid) = get_named_arg(kb, named, "witness") {
            let witness_short = match kb.get_term(witness_tid) {
                Term::Fn { functor, .. } => kb.qualified_name_of(*functor)
                    .rsplit('.').next().unwrap_or("").to_string(),
                _ => String::new(),
            };
            match witness_short.as_str() {
                "ScopeAxiom" | "Specialization" => return CiteStatus::Discharged,
                "TrustedAxiom" => {
                    let reason = get_named_arg(kb, witness_tid_named(kb, witness_tid).as_ref()
                        .unwrap_or(named), "reason")
                        .and_then(|t| match kb.get_term(t) {
                            Term::Const(Literal::String(s)) => Some(s.clone()),
                            _ => None,
                        })
                        .unwrap_or_else(|| "(no reason)".into());
                    // The pending-placeholder TrustedAxiom (loader
                    // default for un-discharged user proofs) is NOT
                    // a real trust statement — fall through to the
                    // sidecar lookup so a successful prove run can
                    // still satisfy the cite.
                    if !reason.starts_with("pending —") {
                        return CiteStatus::Trusted(reason);
                    }
                }
                _ => {}
            }
        }
        // SmtDischarge / SldDerivation / MetaCompose: defer to sidecar.
        break;
    }
    if !found_record { return CiteStatus::NotFound; }
    if sidecar_exists_for(cited_qn, cli) {
        CiteStatus::Discharged
    } else {
        CiteStatus::Pending
    }
}

/// Read a witness term's `named_args` so we can look up its `reason`
/// field. Tiny adapter for the closure-friendly ergonomics in
/// `cite_status`.
fn witness_tid_named<'a>(
    kb: &'a KnowledgeBase,
    witness_tid: TermId,
) -> Option<smallvec::SmallVec<[(Symbol, TermId); 2]>> {
    if let Term::Fn { named_args, .. } = kb.get_term(witness_tid) {
        Some(named_args.clone())
    } else {
        None
    }
}

/// Phase γ.4: walk a rule's enclosing-scope chain and collect every
/// auto-registered `<scope-qn>.requires.<SE>` ProofRecord as an
/// implicit citation. For rule `a.b.c.rule_name`, the parent scopes
/// `a.b.c`, `a.b`, `a` are each scanned. Records are returned in
/// outer-to-inner order (innermost scope's requires last).
/// WI-139 [hint] semantics: walk the KB for rules whose meta carries
/// the `hint` flag and whose head-functor QN sits in `rule_qn`'s
/// enclosing scope chain. Each such rule is implicitly cited so its
/// `-:` conclusion lifts as a forall hypothesis in the consumer's
/// preamble — the SMT-side analogue of `[simp]`'s SLD-side
/// auto-application.
///
/// v0 limitation: the rule's identity for cite purposes is its
/// head-functor QN (what `lift_rule_to_implication_clause` accepts).
/// For rules whose head-functor uniquely identifies them
/// (definitional unfolds with a unique top symbol, top-level rules
/// where label==head-functor), [hint] works directly. For
/// equational rules under shared `eq` functor, the lift picks the
/// first rule under the symbol — multiple equational [hint]s with
/// the same scope risk lifting the wrong one. Document; revisit
/// when a per-RuleId lift helper lands.
fn hint_cites_for(rule_qn: &str, kb: &mut KnowledgeBase) -> Vec<String> {
    let parts: Vec<&str> = rule_qn.split('.').collect();
    if parts.len() < 2 { return Vec::new(); }

    // Walk all rules in the KB. For each with `hint` meta, determine
    // its head-functor QN and check whether the QN is prefixed by
    // any of `rule_qn`'s parent scope segments.
    let rule_sort = kb.make_name_term("Rule");
    let mut out: Vec<String> = Vec::new();
    for rid in kb.by_sort(rule_sort) {
        let meta = kb.rule_meta(rid);
        if !anthill_core::kb::load::meta_has_flag(kb, meta, "hint") {
            continue;
        }
        let head = kb.rule_head(rid);
        let functor = match kb.get_term(head) {
            Term::Fn { functor, .. } => *functor,
            _ => continue,
        };
        let head_qn = kb.qualified_name_of(functor).to_string();
        // Scope filter: head_qn must start with one of rule_qn's
        // parent QN segments. This restricts hints to the proof's
        // own enclosing namespace chain.
        let mut in_scope = false;
        for end in 1..parts.len() {
            let scope = parts[..end].join(".");
            if head_qn.starts_with(&format!("{scope}.")) {
                in_scope = true;
                break;
            }
        }
        if in_scope && !out.contains(&head_qn) {
            out.push(head_qn);
        }
    }
    out
}

fn implicit_cites_for(rule_qn: &str, kb: &KnowledgeBase) -> Vec<String> {
    let record_sym = match kb.try_resolve_symbol("anthill.realization.ProofRecord") {
        Some(s) => s,
        None => return Vec::new(),
    };
    let parts: Vec<&str> = rule_qn.split('.').collect();
    if parts.len() < 2 { return Vec::new(); }

    // Snapshot all ProofRecord QNs once so the inner loop is cheap.
    let mut all_record_qns: Vec<String> = Vec::new();
    for rid in kb.rules_by_functor(record_sym) {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head(rid);
        let named = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args,
            _ => continue,
        };
        if let Some(tid) = get_named_arg(kb, named, "rule") {
            if let Term::Const(Literal::String(s)) = kb.get_term(tid) {
                all_record_qns.push(s.clone());
            }
        }
    }

    let mut out = Vec::new();
    // Walk outer-to-inner so the innermost scope's requires come
    // last in `effective_using` — matches the user's mental model
    // of "closest scope wins" if there's any duplication.
    for end in 1..parts.len() {
        let scope_qn = parts[..end].join(".");
        let prefix = format!("{scope_qn}.requires.");
        for qn in &all_record_qns {
            // Match exact-prefix-and-no-deeper-segment so we don't
            // pick up `a.b.requires.X.requires.Y` style records as
            // implicit cites for scope `a.b`.
            if let Some(rest) = qn.strip_prefix(&prefix) {
                if !rest.contains('.') {
                    out.push(qn.clone());
                }
            }
        }
    }
    out
}

/// True iff a witness sidecar JSON exists for the given rule QN at
/// the project's cache location. Used by cite_status as the
/// "discharged elsewhere" check for SmtDischarge / SldDerivation /
/// MetaCompose witnesses whose ProofRecord still says Pending in
/// source (because in-source persistence is deferred).
fn sidecar_exists_for(rule_qn: &str, cli: &ProveArgs) -> bool {
    if cli.no_cache { return false; }
    let cache_root = resolve_cache_root(cli.cache_dir.as_deref());
    let repo_root = std::env::current_dir().unwrap_or_else(|_| ".".into());
    let dir = anthill_smt_gen::cache::witness_subdir(&cache_root, &repo_root);
    anthill_smt_gen::cache::load_witness(&dir, rule_qn).is_some()
}

struct CacheCtx {
    subdir: std::path::PathBuf,
    blob_dir: std::path::PathBuf,
    key: String,
}

fn build_cache_context(
    cache_dir_override: &Option<std::path::PathBuf>,
    kb: &KnowledgeBase,
    smt: &str,
    tactic_canon: &str,
    visited: &BTreeSet<String>,
    z3_version: &str,
) -> CacheCtx {
    let cache_root = resolve_cache_root(cache_dir_override.as_deref());
    let repo_root = std::env::current_dir().unwrap_or_else(|_| ".".into());
    let subdir = proof_subdir(&cache_root, &repo_root, Solver::Z3);
    let blob_dir = blob_subdir(&cache_root, &repo_root);
    let key = build_key(kb, &KeyInputs {
        emitted_smt_lib: smt,
        tactic_canon,
        hint_qns: &[],
        visited_rules: visited,
        stdlib_version: env!("CARGO_PKG_VERSION"),
        z3_version,
    });
    CacheCtx { subdir, blob_dir, key }
}

/// Recognise `ranking(boundedness: <rule_qn>, decrease: <rule_qn>)`
/// as the tactic value of a `by z3(tactic: ...)` block. Returns the
/// two rule QNs the meta-tactic should dispatch as sub-queries.
/// WI-100.
fn recognise_ranking_tactic(
    kb: &KnowledgeBase,
    tactic_term: TermId,
) -> Option<(String, String)> {
    let (functor, named) = match kb.get_term(tactic_term) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        _ => return None,
    };
    let fn_name = kb.qualified_name_of(functor);
    if fn_name.rsplit('.').next() != Some("ranking") { return None; }

    let mut bnd: Option<String> = None;
    let mut dec: Option<String> = None;
    for (key_sym, val_tid) in &named {
        let key = kb.qualified_name_of(*key_sym);
        let key_short = key.rsplit('.').next().unwrap_or(key);
        let qn = qn_of(kb, *val_tid)?;
        match key_short {
            "boundedness" => bnd = Some(qn),
            "decrease" => dec = Some(qn),
            _ => {}
        }
    }
    Some((bnd?, dec?))
}

/// Parsed `induction(...)` tactic value. Slots are best-effort — at
/// least one of `base`/`step` is required to make a proof meaningful;
/// `cases` is reserved for non-binary inductions (multi-constructor
/// sorts). v1 only consumes `base` and `step`.
struct InductionSpec {
    over: Option<String>,
    base: Option<String>,
    step: Option<String>,
    cases: Vec<String>,
}

fn recognise_induction_tactic(
    kb: &KnowledgeBase,
    tactic_term: TermId,
) -> Option<InductionSpec> {
    let (functor, named, pos) = match kb.get_term(tactic_term) {
        Term::Fn { functor, named_args, pos_args } =>
            (*functor, named_args.clone(), pos_args.clone()),
        _ => return None,
    };
    let fn_name = kb.qualified_name_of(functor);
    if fn_name.rsplit('.').next() != Some("induction") { return None; }

    let mut spec = InductionSpec { over: None, base: None, step: None, cases: Vec::new() };
    for &p in &pos {
        if let Some(qn) = qn_of(kb, p) {
            spec.cases.push(qn);
        }
    }
    for (key_sym, val_tid) in &named {
        let key = kb.qualified_name_of(*key_sym);
        let key_short = key.rsplit('.').next().unwrap_or(key);
        match key_short {
            "over" => spec.over = qn_of(kb, *val_tid),
            "base" => spec.base = qn_of(kb, *val_tid),
            "step" => spec.step = qn_of(kb, *val_tid),
            _ => {}
        }
    }
    Some(spec)
}

/// Dispatch a structural / numeric induction proof as N+ SMT
/// sub-queries. v1: base + step (for `Int64.induction`-shaped proofs).
/// Multi-case form (positional `cases`) is handled when the user
/// supplies them; otherwise base+step is mandatory. WI-101.
fn dispatch_induction(
    kb: &mut KnowledgeBase,
    parent_qn: &str,
    spec: &InductionSpec,
    base_config: &ProofConfig,
    cli: &ProveArgs,
    stats: &mut CacheStats,
) -> DispatchOutcome {
    // Build the case list. For binary induction (Int / Bool /
    // single-recursive enums) use base + step. Otherwise consume the
    // positional `cases` list.
    let mut sub_qns: Vec<String> = Vec::new();
    if let Some(b) = &spec.base { sub_qns.push(b.clone()); }
    if let Some(s) = &spec.step { sub_qns.push(s.clone()); }
    sub_qns.extend(spec.cases.iter().cloned());
    if sub_qns.is_empty() {
        return DispatchOutcome::no_witness(Verdict::EmitError(format!(
            "induction tactic for `{parent_qn}` has no cases — \
             supply `base:` + `step:` or positional case rules"
        )));
    }

    if cli.verbose {
        let over = spec.over.as_deref().unwrap_or("(unspecified)");
        println!("  induction(over: {over}) sub-queries: {}", sub_qns.join(", "));
    }
    let outcome = dispatch_subqueries(
        kb, parent_qn, "induction case", &sub_qns, base_config, cli, stats);
    rewrap_meta_compose(outcome, "induction")
}

/// On a Proved meta-tactic outcome, replace the placeholder
/// `MetaCompose { tactic_name: "compose" }` produced by
/// `dispatch_subqueries` with one named after the actual meta-tactic
/// (`"induction"`, `"ranking"`, …). On non-Proved outcomes, returns
/// the outcome unchanged. Without this, callers would see anonymous
/// witnesses in the kernel registry.
fn rewrap_meta_compose(outcome: DispatchOutcome, tactic_name: &str) -> DispatchOutcome {
    if !matches!(outcome.verdict, Verdict::Proved) {
        return outcome;
    }
    let DispatchOutcome { verdict, witness, visited_rules } = outcome;
    let sub_witnesses = witness.into_iter().flat_map(|w| match w {
        ProofWitness::MetaCompose { sub, .. } => sub,
        other => vec![other],
    }).collect();
    DispatchOutcome {
        verdict,
        witness: Some(ProofWitness::MetaCompose {
            tactic_name: tactic_name.to_string(),
            sub: sub_witnesses,
        }),
        visited_rules,
    }
}

/// Shared meta-tactic dispatch: run each `sub_qns` rule as an SMT
/// satisfiability check; combine. All proved → Proved (with a
/// `MetaCompose` witness wrapping each sub-witness); first failure
/// surfaces with `label` ("ranking sub-query" / "induction case").
/// The returned witness on success is a `MetaCompose` placeholder;
/// the caller (`dispatch_ranking` / `dispatch_induction`) names the
/// meta-tactic by overwriting `tactic_name`.
fn dispatch_subqueries(
    kb: &mut KnowledgeBase,
    parent_qn: &str,
    label: &str,
    sub_qns: &[String],
    base_config: &ProofConfig,
    cli: &ProveArgs,
    stats: &mut CacheStats,
) -> DispatchOutcome {
    let sub_config = ProofConfig { tactic_expr: None, ..base_config.clone() };
    let mut sub_witnesses: Vec<ProofWitness> = Vec::new();
    let mut combined_visited: BTreeSet<String> = BTreeSet::new();
    for sub in sub_qns {
        let sub_canon = format!("z3-subquery({})",
            sub_config.logic.as_deref().unwrap_or("LRA"));
        let DispatchOutcome { verdict, witness, visited_rules } =
            run_smt_subquery(kb, sub, &sub_config, &sub_canon, cli, stats);
        combined_visited.extend(visited_rules);
        match verdict {
            Verdict::Proved => {
                if let Some(w) = witness {
                    sub_witnesses.push(w);
                }
                continue;
            }
            Verdict::Disproved(model) => return DispatchOutcome::no_witness(
                Verdict::Disproved(format!(
                    "{label} `{sub}` failed for `{parent_qn}`:\n{model}"))),
            Verdict::Unknown(why) => return DispatchOutcome::no_witness(
                Verdict::Unknown(format!(
                    "{label} `{sub}` for `{parent_qn}`: {why}"))),
            other => return DispatchOutcome::no_witness(other),
        }
    }
    DispatchOutcome {
        verdict: Verdict::Proved,
        witness: Some(ProofWitness::MetaCompose {
            tactic_name: "compose".to_string(), // overwritten by caller
            sub: sub_witnesses,
        }),
        visited_rules: combined_visited,
    }
}

fn qn_of(kb: &KnowledgeBase, term: TermId) -> Option<String> {
    match kb.get_term(term) {
        Term::Ref(s) | Term::Ident(s) => Some(kb.qualified_name_of(*s).to_string()),
        Term::Fn { functor, pos_args, named_args }
            if pos_args.is_empty() && named_args.is_empty() =>
            Some(kb.qualified_name_of(*functor).to_string()),
        _ => None,
    }
}

/// Run two sub-queries (boundedness, decrease) sequentially — the in-language
/// ranking meta-tactic. Exercised by the lf1 `post_armed_excursion_bound` proof
/// (`examples/webots-modelling/lf1/safety_transponder.anthill`), which obsoleted
/// and replaced the former hand-written `lf1_transponder_excursion_*_manual`
/// smt-gen test (removed in proposal 025.1 Phase 8 / WI-103).
fn dispatch_ranking(
    kb: &mut KnowledgeBase,
    parent_qn: &str,
    boundedness_qn: &str,
    decrease_qn: &str,
    base_config: &ProofConfig,
    cli: &ProveArgs,
    stats: &mut CacheStats,
) -> DispatchOutcome {
    let sub_qns = [boundedness_qn.to_string(), decrease_qn.to_string()];
    if cli.verbose {
        println!("  ranking sub-queries: {}", sub_qns.join(", "));
    }
    let outcome = dispatch_subqueries(
        kb, parent_qn, "ranking sub-query", &sub_qns, base_config, cli, stats);
    rewrap_meta_compose(outcome, "ranking")
}

/// Execute one obligation rule as an SMT-LIB satisfiability check.
/// The single canonical SMT-dispatch path: `dispatch_z3` calls this
/// directly for top-level proofs; meta-tactics (ranking, induction)
/// call it once per sub-case. `tactic_canon` is the cache-key
/// signature (e.g. `"z3(logic=LRA,tactic=...)"` for top-level,
/// `"z3-subquery(LRA)"` for meta-tactic children).
fn run_smt_subquery(
    kb: &mut KnowledgeBase,
    rule_qn: &str,
    config: &ProofConfig,
    tactic_canon: &str,
    cli: &ProveArgs,
    stats: &mut CacheStats,
) -> DispatchOutcome {
    let (smt, deps) = match emit_satisfiability_check_with_deps(kb, rule_qn, config) {
        Ok(p) => p,
        Err(e) => return DispatchOutcome::no_witness(Verdict::EmitError(e.message)),
    };
    if cli.verbose && !deps.is_empty() {
        println!("  deps: {}", deps.join(", "));
    }
    // Phase α.4: deps from emit_satisfiability_check_with_deps is the
    // visited-rule set for state-hash purposes. Cache hit AND miss
    // paths produce the same set since deps are computed before we
    // consult the cache.
    let visited: BTreeSet<String> = deps.into_iter().collect();
    if cli.dry_run {
        println!("--- {rule_qn} ---");
        print!("{smt}");
        println!("------");
        // Dry-run still consulted KB state (deps were computed); record
        // the visited set so callers can hash it even when no real
        // verdict is produced.
        return DispatchOutcome {
            verdict: Verdict::Skipped("dry-run (SMT printed to stdout)".into()),
            witness: None,
            visited_rules: visited,
        };
    }
    let z3_version = match Command::new(&cli.solver).arg("--version").output() {
        Ok(o) if o.status.success() =>
            String::from_utf8_lossy(&o.stdout).trim().to_string(),
        _ => return DispatchOutcome::no_witness(
            Verdict::Skipped(format!("solver `{}` not on $PATH", cli.solver))),
    };
    let cache_ctx = if cli.no_cache {
        stats.bypassed += 1;
        None
    } else {
        Some(build_cache_context(&cli.cache_dir, kb, &smt, tactic_canon, &visited, &z3_version))
    };
    if let Some(ctx) = &cache_ctx {
        if !cli.refresh_cache {
            if let Some(entry) = lookup(&ctx.subdir, &ctx.key) {
                stats.hits += 1;
                if cli.verbose {
                    println!("  cache hit: {} ({})", &ctx.key[..12], entry.verdict);
                }
                let cached_verdict = verdict_from_cache(&entry);
                let witness = build_smt_witness(
                    &cli.solver, config, &cached_verdict, &entry);
                return DispatchOutcome {
                    verdict: cached_verdict,
                    witness,
                    visited_rules: visited,
                };
            }
        }
        stats.misses += 1;
    }
    // Unique-suffix the path so concurrent `anthill prove` calls on the
    // same rule — across subprocesses (parallel test threads) and within
    // one process — don't trample each other's SMT2 file mid-z3.
    let path = std::env::temp_dir().join(format!(
        "anthill_prove_{}_{}.smt2",
        sanitize_filename(rule_qn),
        rand_suffix(),
    ));
    if let Err(e) = std::fs::write(&path, &smt) {
        return DispatchOutcome::no_witness(
            Verdict::EmitError(format!("write smt2: {e}")));
    }
    let started = std::time::Instant::now();
    let out = match Command::new(&cli.solver).arg(&path).output() {
        Ok(o) => o,
        Err(e) => {
            let _ = std::fs::remove_file(&path);
            return DispatchOutcome::no_witness(
                Verdict::EmitError(format!("invoke {}: {e}", cli.solver)));
        }
    };
    let elapsed = started.elapsed().as_secs_f64();
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    let outcome = parse_z3_output(&stdout);
    let (verdict, keep_smt2) = match outcome.verdict.as_str() {
        "unsat" => (Verdict::Proved, false),
        "sat" => (Verdict::Disproved(stdout.clone()), false),
        "unknown" => (Verdict::Unknown("z3: unknown".into()), false),
        // Keep the SMT2 dump on the wild-card branch so the path
        // referenced in the verdict message stays inspectable.
        other => (
            Verdict::Unknown(format!("z3 said `{other}` (path: {})", path.display())),
            true,
        ),
    };
    if !keep_smt2 {
        let _ = std::fs::remove_file(&path);
    }
    if cli.verbose {
        if !outcome.variable_assignments.is_empty() {
            println!("  model: {} bindings", outcome.variable_assignments.len());
        }
        if !outcome.unsat_core.is_empty() {
            println!("  unsat-core: {}", outcome.unsat_core.join(", "));
        }
    }
    // Phase α.5: real content-addressed hashes for the witness.
    // The SMT-LIB document is sha256'd; if a cache_ctx exists, the
    // document is also persisted as a blob so phase-β check can
    // replay the discharge. Same for the sat model.
    let document_hash = hash_content(&smt);
    let model_hash = if matches!(verdict, Verdict::Disproved(_))
        && !outcome.model_text.is_empty()
    {
        Some(hash_content(&outcome.model_text))
    } else {
        None
    };
    if let Some(ctx) = &cache_ctx {
        if let Err(e) = store_blob(&ctx.blob_dir, &smt) {
            if cli.verbose { eprintln!("  blob write failed (smt doc): {e}"); }
        }
        if model_hash.is_some() {
            if let Err(e) = store_blob(&ctx.blob_dir, &outcome.model_text) {
                if cli.verbose { eprintln!("  blob write failed (model): {e}"); }
            }
        }
    }
    let witness = Some(ProofWitness::SmtDischarge {
        backend: cli.solver.clone(),
        logic: config.logic.clone().unwrap_or_default(),
        document_hash: document_hash.clone(),
        verdict: smt_verdict_from_outcome(&outcome, model_hash.clone()),
        core: if outcome.unsat_core.is_empty() { None }
              else { Some(outcome.unsat_core.join("\n")) },
    });
    if let Some(ctx) = cache_ctx {
        let mut entry = CacheEntry::new(
            ctx.key,
            verdict_label(&verdict).to_string(),
            elapsed,
            z3_version,
            now_iso8601(),
            stdout,
        );
        entry.model_text = outcome.model_text;
        entry.variable_assignments = outcome.variable_assignments;
        entry.unsat_core = outcome.unsat_core;
        entry.document_hash = document_hash;
        entry.model_hash = model_hash.unwrap_or_default();
        match store_entry(&ctx.subdir, &entry) {
            Ok(_) => stats.writes += 1,
            Err(e) => if cli.verbose {
                eprintln!("  cache write failed: {e}");
            },
        }
    }
    DispatchOutcome { verdict, witness, visited_rules: visited }
}

/// Translate a parsed Z3 outcome into a `SmtVerdict` enum suitable
/// for the witness. Sat carries a content hash for the model text
/// (computed by the caller); unknown carries the reason.
fn smt_verdict_from_outcome(
    outcome: &anthill_smt_gen::outcome::OutcomeData,
    model_hash: Option<String>,
) -> SmtVerdict {
    match outcome.verdict.as_str() {
        "unsat" => SmtVerdict::Unsat,
        "sat" => SmtVerdict::Sat {
            model_hash: model_hash.unwrap_or_default(),
        },
        other => SmtVerdict::Unknown { reason: format!("z3: {other}") },
    }
}

/// Construct a witness for a cache-hit verdict from the stored
/// entry. The entry's `document_hash` and `model_hash` (added in
/// α.5) are content-addressed sha256 of the underlying blob text;
/// older entries written before α.5 have empty `document_hash`,
/// in which case the witness's hash defaults to empty too — a
/// signal to phase β that re-discharge is required to populate
/// payloads.
fn build_smt_witness(
    backend: &str,
    config: &ProofConfig,
    cached_verdict: &Verdict,
    entry: &CacheEntry,
) -> Option<ProofWitness> {
    let smt_verdict = match cached_verdict {
        Verdict::Proved => SmtVerdict::Unsat,
        Verdict::Disproved(_) => SmtVerdict::Sat {
            model_hash: entry.model_hash.clone(),
        },
        Verdict::Unknown(reason) => SmtVerdict::Unknown { reason: reason.clone() },
        _ => return None,
    };
    Some(ProofWitness::SmtDischarge {
        backend: backend.to_string(),
        logic: config.logic.clone().unwrap_or_default(),
        document_hash: entry.document_hash.clone(),
        verdict: smt_verdict,
        core: if entry.unsat_core.is_empty() { None }
              else { Some(entry.unsat_core.join("\n")) },
    })
}

fn bool_of(v: &ArgValue) -> Option<bool> {
    match v {
        ArgValue::Bool(b) => Some(*b),
        ArgValue::String(s) => match s.as_str() {
            "true" => Some(true),
            "false" => Some(false),
            _ => None,
        },
        ArgValue::Int(n) => Some(*n != 0),
        _ => None,
    }
}

fn verdict_label(v: &Verdict) -> &'static str {
    match v {
        Verdict::Proved => "proved",
        Verdict::Disproved(_) => "disproved",
        Verdict::Unknown(_) => "unknown",
        Verdict::Skipped(_) => "skipped",
        Verdict::EmitError(_) => "emit_error",
    }
}

fn verdict_from_cache(entry: &CacheEntry) -> Verdict {
    match entry.verdict.as_str() {
        "proved" => Verdict::Proved,
        "disproved" => Verdict::Disproved(entry.raw_output.clone()),
        "unknown" => Verdict::Unknown("z3: unknown (cached)".to_string()),
        other => Verdict::EmitError(format!("unrecognised cached verdict `{other}`")),
    }
}

/// Persist a successful discharge's witness as a JSON sidecar
/// (WI-124). The sidecar lives in the same per-project cache root
/// as proof entries and blobs; `anthill check` reads it back and
/// uses the stored witness in place of the in-source placeholder
/// (TrustedAxiom("pending …")) on Pending ProofRecords.
fn persist_witness(
    args: &ProveArgs,
    rule_qn: &str,
    witness: &ProofWitness,
    state_hash: Option<&str>,
) {
    if args.no_cache {
        // --no-cache means don't touch the cache; sidecars live in
        // the same store, so respect the same opt-out.
        return;
    }
    let cache_root = resolve_cache_root(args.cache_dir.as_deref());
    let repo_root = std::env::current_dir().unwrap_or_else(|_| ".".into());
    let dir = witness_subdir(&cache_root, &repo_root);
    let verdict_label = match witness {
        ProofWitness::SmtDischarge { verdict, .. } => match verdict {
            crate::witness::SmtVerdict::Unsat => "Proved",
            crate::witness::SmtVerdict::Sat { .. } => "Disproved",
            crate::witness::SmtVerdict::Unknown { .. } => "Unknown",
        },
        ProofWitness::SldDerivation { .. } => "Proved",
        ProofWitness::MetaCompose { .. } => "Proved",
        ProofWitness::ScopeAxiom { .. } => "Proved",
        ProofWitness::Specialization { .. } => "Proved",
        ProofWitness::TrustedAxiom { .. } => "Trusted",
    };
    let sidecar = WitnessSidecar {
        rule_qn: rule_qn.to_string(),
        verdict_label: verdict_label.to_string(),
        witness: witness.to_shape(),
        state_hash: state_hash.unwrap_or("").to_string(),
        written_at: now_iso8601(),
    };
    if let Err(e) = store_witness(&dir, &sidecar) {
        if args.verbose {
            eprintln!("  warning: witness sidecar write failed for `{rule_qn}`: {e}");
        }
    }
}

fn now_iso8601() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    let secs = SystemTime::now().duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs()).unwrap_or(0);
    format!("@{secs}")
}

fn run_show_cache(args: &ProveArgs) -> Result<(), i32> {
    let cache_root = resolve_cache_root(args.cache_dir.as_deref());
    let repo_root = std::env::current_dir().unwrap_or_else(|_| ".".into());
    let subdir = proof_subdir(&cache_root, &repo_root, Solver::Z3);
    if !subdir.exists() {
        println!("(no cached entries: {})", subdir.display());
        return Ok(());
    }
    let mut entries: Vec<CacheEntry> = walk_cache_entries(&subdir);
    entries.sort_by(|a, b| a.written_at.cmp(&b.written_at));
    println!("cache root: {}", subdir.display());
    println!("{:<14} {:<10} {:>9} {}", "key", "verdict", "secs", "written_at");
    for e in &entries {
        let key_short = if e.key.len() >= 12 { &e.key[..12] } else { &e.key };
        println!("{:<14} {:<10} {:>9.3} {}",
            key_short, e.verdict, e.solver_secs, e.written_at);
    }
    println!("\n{} entries", entries.len());
    Ok(())
}

fn run_gc_cache(args: &ProveArgs, days: u32) -> Result<(), i32> {
    use std::time::{SystemTime, UNIX_EPOCH};
    let cache_root = resolve_cache_root(args.cache_dir.as_deref());
    let repo_root = std::env::current_dir().unwrap_or_else(|_| ".".into());
    let subdir = proof_subdir(&cache_root, &repo_root, Solver::Z3);
    if !subdir.exists() {
        println!("(nothing to GC: {})", subdir.display());
        return Ok(());
    }
    let cutoff_secs = days as u64 * 86_400;
    let now = SystemTime::now().duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs()).unwrap_or(0);
    let mut deleted = 0usize;
    for entry in walk_cache_entries(&subdir) {
        let written = entry.written_at.strip_prefix('@')
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(0);
        if written == 0 || now.saturating_sub(written) >= cutoff_secs {
            cache::invalidate(&subdir, &entry.key);
            deleted += 1;
        }
    }
    println!("removed {deleted} entries older than {days} days from {}", subdir.display());
    Ok(())
}

fn walk_cache_entries(subdir: &std::path::Path) -> Vec<CacheEntry> {
    let mut out = Vec::new();
    fn recurse(dir: &std::path::Path, out: &mut Vec<CacheEntry>) {
        if let Ok(rd) = std::fs::read_dir(dir) {
            for entry in rd.flatten() {
                let p = entry.path();
                if p.is_dir() {
                    recurse(&p, out);
                } else if p.extension().is_some_and(|e| e == "json") {
                    if let Ok(bytes) = std::fs::read(&p) {
                        if let Ok(e) = serde_json::from_slice::<CacheEntry>(&bytes) {
                            out.push(e);
                        }
                    }
                }
            }
        }
    }
    recurse(subdir, &mut out);
    out
}

fn sanitize_filename(s: &str) -> String {
    s.chars().map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' }).collect()
}

fn indent(s: &str, prefix: &str) -> String {
    s.lines().map(|l| format!("{prefix}{l}")).collect::<Vec<_>>().join("\n")
}

// ── WI-558: prove write-back unit tests ──────────────────────────────
//
// `anthill-cli` is a binary crate (no lib target), so these in-process tests
// live beside the code they exercise: the new `witness_to_term` encoder (which
// resolves stdlib QNs — a typo would only otherwise surface under a live z3
// run) and the external (`by z3`) result write-back (`witness_to_term` +
// `set_proof_result` keyed on the source RuleId — the cli path the core
// `verify_proofs` tests don't cover).
#[cfg(test)]
mod wi558_tests {
    use super::*;
    use crate::witness::{ProofWitness, SmtVerdict};

    /// Load the embedded stdlib plus a single user source written to a temp
    /// file (`load_kb_with_stdlib` requires ≥1 user path).
    fn load_with_source(tag: &str, src: &str) -> KnowledgeBase {
        let dir = std::env::temp_dir()
            .join(format!("anthill-wi558-{}-{tag}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("src.anthill");
        std::fs::write(&path, src).unwrap();
        crate::load_kb_with_stdlib(&[path], false, true)
            .unwrap_or_else(|c| panic!("load failed with code {c}"))
    }

    const SRC: &str = r#"
        namespace t.w558
          entity Light(state: String)
          fact Light(state: "bright")
          rule shines(?b) :- Light(state: ?b)
          proof shines by z3 end
        end
    "#;

    /// Functor short name of the `field` term on the ProofRecord whose `rule`
    /// QN ends with `suffix`. Reads both `Fn` and the bare `Ref` a nullary
    /// constructor canonicalises to (WI-511).
    fn record_field_short(kb: &KnowledgeBase, suffix: &str, field: &str) -> Option<String> {
        let head = record_head(kb, suffix)?;
        let named = head_named(kb, head)?;
        let tid = get_named_arg(kb, &named, field)?;
        functor_short(kb, tid)
    }

    /// The `RuleId` of the live ProofRecord fact whose `rule` QN ends with
    /// `suffix` — the write-back key.
    fn record_rid(kb: &KnowledgeBase, suffix: &str) -> Option<RuleId> {
        let sym = kb.try_resolve_symbol("anthill.realization.ProofRecord")?;
        kb.rules_by_functor(sym).into_iter().find(|&rid| {
            kb.is_fact(rid)
                && head_named(kb, kb.rule_head(rid))
                    .and_then(|named| lookup_string(kb, &named, "rule"))
                    .is_some_and(|q| q.ends_with(suffix))
        })
    }

    fn record_head(kb: &KnowledgeBase, suffix: &str) -> Option<TermId> {
        let rid = record_rid(kb, suffix)?;
        Some(kb.rule_head(rid))
    }

    fn head_named(
        kb: &KnowledgeBase,
        head: TermId,
    ) -> Option<smallvec::SmallVec<[(Symbol, TermId); 2]>> {
        match kb.get_term(head) {
            Term::Fn { named_args, .. } => Some(named_args.clone()),
            _ => None,
        }
    }

    fn functor_short(kb: &KnowledgeBase, tid: TermId) -> Option<String> {
        let f = match kb.get_term(tid) {
            Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => *functor,
            _ => return None,
        };
        Some(kb.qualified_name_of(f).rsplit('.').next().unwrap_or("").to_string())
    }

    #[test]
    fn witness_to_term_encodes_smt_discharge() {
        let mut kb = load_with_source("enc", SRC);
        let w = ProofWitness::SmtDischarge {
            backend: "z3".into(),
            logic: "QF_LRA".into(),
            document_hash: "deadbeef".into(),
            verdict: SmtVerdict::Unsat,
            core: None,
        };
        let t = witness_to_term(&mut kb, &w);
        assert_eq!(functor_short(&kb, t).as_deref(), Some("SmtDischarge"));
        // Nested SmtVerdict.Unsat resolves (a wrong QN would have panicked).
        let named = head_named(&kb, t).expect("SmtDischarge named args");
        let verdict = get_named_arg(&kb, &named, "verdict").expect("verdict field");
        assert_eq!(functor_short(&kb, verdict).as_deref(), Some("Unsat"));
    }

    #[test]
    fn external_write_back_flips_record_to_discharged() {
        let mut kb = load_with_source("disc", SRC);
        assert_eq!(
            record_field_short(&kb, "shines", "result").as_deref(),
            Some("Pending"),
            "the `by z3` proof loads Pending"
        );
        let rid = record_rid(&kb, "shines").expect("record rid");
        let w = ProofWitness::SmtDischarge {
            backend: "z3".into(),
            logic: "QF_LRA".into(),
            document_hash: "deadbeef".into(),
            verdict: SmtVerdict::Unsat,
            core: None,
        };
        let witness = witness_to_term(&mut kb, &w);
        set_proof_result(&mut kb, rid, VerdictWrite::Discharged { witness, solver: "z3".into() });
        assert_eq!(
            record_field_short(&kb, "shines", "result").as_deref(),
            Some("Discharged"),
            "result flips to Discharged"
        );
        assert_eq!(
            record_field_short(&kb, "shines", "witness").as_deref(),
            Some("SmtDischarge"),
            "witness flips to the real SmtDischarge certificate"
        );
    }

    #[test]
    fn failed_unknown_write_back_flips_record_to_failed() {
        let mut kb = load_with_source("fail", SRC);
        let rid = record_rid(&kb, "shines").expect("record rid");
        set_proof_result(&mut kb, rid, VerdictWrite::FailedUnknown { reason: "z3 timeout".into() });
        assert_eq!(
            record_field_short(&kb, "shines", "result").as_deref(),
            Some("Failed"),
            "an unknown verdict flips the record to Failed, never Discharged"
        );
    }
}
