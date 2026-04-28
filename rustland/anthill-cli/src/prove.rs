//! `anthill prove` — discharge proof obligations declared via
//! `proof <rule> by <strategy>` blocks (proposal 025).

use std::collections::BTreeSet;
use std::process::Command;

use anthill_core::intern::Symbol;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::typing::get_named_arg;
use anthill_smt_gen::{
    emit_satisfiability_check_with_deps, lift_rule_to_implication_clause, ProofConfig,
};
use anthill_smt_gen::cache::{
    self, blob_subdir, build_key, entry_path, hash_content, lookup, proof_subdir,
    resolve_cache_root, state_hash, store_blob, store_entry, store_witness,
    witness_subdir, CacheEntry, KeyInputs, Solver, WitnessSidecar,
};
use anthill_smt_gen::tactic_emit::emit_tactic_from_term;
use anthill_smt_gen::outcome::parse_z3_output;

use crate::{ProveArgs, load_kb_with_stdlib};
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
    let mut discharged_this_run: std::collections::HashSet<String> =
        std::collections::HashSet::new();

    for rec in &records {
        if let Some(filter) = &args.rule {
            if &rec.rule != filter {
                continue;
            }
        }
        total += 1;
        let outcome = dispatch(&mut kb, rec, args, &mut stats, &discharged_this_run);
        let witness = outcome.witness.clone();
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
            discharged_this_run.insert(rec.rule.clone());
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
    rule: String,
    strategy: Strategy,
    /// Cited-lemma rule QNs from the source-level `using` clause.
    /// Each is dispatched separately to render its body as SMT,
    /// and the resulting clauses are spliced into this proof's
    /// SMT preamble as `(assert ...)` hypotheses (via
    /// `ProofConfig.assumptions`). Empty for proofs without a
    /// `using` clause.
    using: Vec<String>,
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
    #[allow(dead_code)]
    Float(f64),
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
    for rid in kb.by_functor(functor) {
        let head = kb.rule_head(rid);
        if let Some(rec) = read_proof_record(kb, &syms, head) {
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

fn read_proof_record(kb: &KnowledgeBase, syms: &ProofSyms, term_id: TermId) -> Option<ProofRec> {
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
    Some(ProofRec { rule, strategy, using })
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
/// consulted (phase α.4 — used to compute the per-ProofRecord state
/// hash). The witness is populated when the backend produced a real
/// verdict (Proved / Disproved / Unknown); it's `None` for Skipped
/// (dry-run, solver missing) and EmitError outcomes. `visited_rules`
/// is populated whenever a discharge actually walked KB content —
/// empty for early-exit verdicts where no kb-state slice was
/// consulted.
#[allow(dead_code)] // witness/state_hash consumed in α.5; kept now for plumbing
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
    discharged_this_run: &std::collections::HashSet<String>,
) -> DispatchOutcome {
    let (tool, tool_args) = match &rec.strategy {
        Strategy::Open => return DispatchOutcome::no_witness(
            Verdict::Skipped("open obligation (no `by` clause)".into())),
        Strategy::Tool { name, args } => (name.as_str(), args.as_slice()),
    };
    match tool {
        "z3" => dispatch_z3(kb, &rec.rule, tool_args, &rec.using, args, stats, discharged_this_run),
        "test" => DispatchOutcome::no_witness(
            Verdict::Skipped("`by test` not yet wired".into())),
        "derivation" => dispatch_derivation(kb, &rec.rule, tool_args),
        other => DispatchOutcome::no_witness(
            Verdict::Skipped(format!("unknown strategy `{other}`"))),
    }
}

fn dispatch_derivation(
    kb: &mut KnowledgeBase,
    rule_qn: &str,
    tool_args: &[NamedArg],
) -> DispatchOutcome {
    use anthill_core::kb::resolve::ResolveConfig;

    let mut max_depth: usize = 200;
    let mut max_solutions: usize = 1;
    for arg in tool_args {
        match (arg.key.as_str(), &arg.value) {
            ("max_depth", ArgValue::Int(n)) if *n > 0 => max_depth = *n as usize,
            ("max_solutions", ArgValue::Int(n)) if *n >= 0 => max_solutions = *n as usize,
            _ => {}
        }
    }

    let rule_sym = match kb.try_resolve_symbol(rule_qn) {
        Some(s) => s,
        None => return DispatchOutcome::no_witness(
            Verdict::EmitError(format!("rule `{rule_qn}` not in KB"))),
    };
    let rules = kb.by_functor(rule_sym);
    if rules.is_empty() {
        return DispatchOutcome::no_witness(
            Verdict::EmitError(format!("no rules found for `{rule_qn}`")));
    }
    let config = ResolveConfig {
        max_depth,
        max_solutions: max_solutions.max(1),
        simplify: true,
    };
    // SLD-derivation witness: phase α.3 produces a placeholder
    // tree_hash referencing the rule QN. Phase α.5 introduces
    // proper derivation-tree capture in the resolver and
    // content-addressed storage in the prove cache.
    let derivation_witness = ProofWitness::SldDerivation {
        tree_hash: format!("sld-derivation:{rule_qn}"),
    };
    // Phase α.4: visited_rules for derivation is currently a coarse
    // placeholder (rule_qn itself). The SLD resolver doesn't yet
    // surface its visited-rule set; α.5 introduces the derivation-
    // tree capture which will populate this precisely.
    let visited: BTreeSet<String> =
        std::iter::once(rule_qn.to_string()).collect();
    for rule_id in rules {
        if kb.rule_body(rule_id).is_empty() {
            return DispatchOutcome {
                verdict: Verdict::Proved,
                witness: Some(derivation_witness.clone()),
                visited_rules: visited.clone(),
            };
        }
        let empty_subst = anthill_core::kb::subst::Substitution::new();
        let (fresh_body, _links) = kb.with_fresh_vars(rule_id, &empty_subst);
        if !kb.resolve(&fresh_body, &config).is_empty() {
            return DispatchOutcome {
                verdict: Verdict::Proved,
                witness: Some(derivation_witness),
                visited_rules: visited,
            };
        }
    }
    DispatchOutcome::no_witness(Verdict::Unknown(format!(
        "no derivation found within depth {max_depth} for `{rule_qn}`"
    )))
}

fn dispatch_z3(
    kb: &mut KnowledgeBase,
    rule_qn: &str,
    tool_args: &[NamedArg],
    using: &[String],
    cli: &ProveArgs,
    stats: &mut CacheStats,
    discharged_this_run: &std::collections::HashSet<String>,
) -> DispatchOutcome {
    let mut config = ProofConfig::default();
    let mut canon_parts: Vec<String> = Vec::new();
    let mut tactic_term: Option<TermId> = None;
    // Render each cited lemma's body via smt-gen and stash the
    // resulting clauses as `(assert ...)` hypotheses for this proof.
    // We re-use `emit_satisfiability_check_with_deps` with a default
    // ProofConfig (no tactic, no outcome flags) — we only need the
    // body assertions, not the discharge envelope. The cited rule's
    // own body assertions become AND-ed conjuncts.
    match render_cited_lemmas(kb, using, rule_qn, cli, discharged_this_run) {
        Ok(Some(clauses)) => {
            config.assumptions = clauses;
            canon_parts.push(format!("using={}", using.join(",")));
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
    discharged_this_run: &std::collections::HashSet<String>,
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
            Ok(clause) => clauses.push(clause),
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
    discharged_this_run: &std::collections::HashSet<String>,
) -> CiteStatus {
    if discharged_this_run.contains(cited_qn) {
        return CiteStatus::Discharged;
    }
    let record_sym = match kb.try_resolve_symbol("anthill.realization.ProofRecord") {
        Some(s) => s,
        None => return CiteStatus::NotFound,
    };
    let mut found_record = false;
    for rid in kb.by_functor(record_sym) {
        if !kb.rule_body(rid).is_empty() { continue; }
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
/// sub-queries. v1: base + step (for `Int.induction`-shaped proofs).
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

/// Run two sub-queries (boundedness, decrease) sequentially. The
/// in-language analogue of `lf1_transponder_excursion_ranking_function_manual`.
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
    let path = std::env::temp_dir().join(format!(
        "anthill_prove_{}.smt2",
        sanitize_filename(rule_qn)
    ));
    if let Err(e) = std::fs::write(&path, &smt) {
        return DispatchOutcome::no_witness(
            Verdict::EmitError(format!("write smt2: {e}")));
    }
    let started = std::time::Instant::now();
    let out = match Command::new(&cli.solver).arg(&path).output() {
        Ok(o) => o,
        Err(e) => return DispatchOutcome::no_witness(
            Verdict::EmitError(format!("invoke {}: {e}", cli.solver))),
    };
    let elapsed = started.elapsed().as_secs_f64();
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    let outcome = parse_z3_output(&stdout);
    let verdict = match outcome.verdict.as_str() {
        "unsat" => Verdict::Proved,
        "sat" => Verdict::Disproved(stdout.clone()),
        "unknown" => Verdict::Unknown("z3: unknown".into()),
        other => Verdict::Unknown(format!("z3 said `{other}` (path: {})", path.display())),
    };
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

#[allow(dead_code)]
fn _cache_modules_in_use() {
    let _ = (cache::CACHE_FORMAT_VERSION, entry_path);
}

fn sanitize_filename(s: &str) -> String {
    s.chars().map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' }).collect()
}

fn indent(s: &str, prefix: &str) -> String {
    s.lines().map(|l| format!("{prefix}{l}")).collect::<Vec<_>>().join("\n")
}
