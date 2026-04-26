//! `anthill prove` — discharge proof obligations declared via
//! `proof <rule> by <strategy>` blocks (proposal 025).

use std::process::Command;

use anthill_core::intern::Symbol;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::typing::get_named_arg;
use anthill_smt_gen::{emit_satisfiability_check_with_deps, ProofConfig};

use crate::{ProveArgs, load_kb_with_stdlib};

pub(crate) fn run_prove(args: &ProveArgs) -> Result<(), i32> {
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

    for rec in &records {
        if let Some(filter) = &args.rule {
            if &rec.rule != filter {
                continue;
            }
        }
        total += 1;
        match dispatch(&mut kb, rec, args) {
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
    if failed > 0 { Err(1) } else { Ok(()) }
}

#[derive(Debug)]
struct ProofRec {
    rule: String,
    strategy: Strategy,
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
}

impl ProofSyms {
    fn new(kb: &KnowledgeBase) -> Self {
        Self {
            open: kb.try_resolve_symbol("anthill.realization.ProofStrategyOpen"),
            cons: kb.try_resolve_symbol("anthill.prelude.List.cons"),
            named_arg: kb.try_resolve_symbol("named_arg"),
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
    out.sort_by(|a, b| a.rule.cmp(&b.rule));
    out
}

fn read_proof_record(kb: &KnowledgeBase, syms: &ProofSyms, term_id: TermId) -> Option<ProofRec> {
    let named = match kb.get_term(term_id) {
        Term::Fn { named_args, .. } => named_args,
        _ => return None,
    };
    let rule = lookup_string(kb, named, "rule")?;
    let strategy = read_strategy(kb, syms, get_named_arg(kb, named, "strategy")?);
    Some(ProofRec { rule, strategy })
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
    if syms.named_arg != Some(functor) { return None; }
    let key = lookup_string(kb, named, "name")?;
    let val_tid = get_named_arg(kb, named, "value")?;
    let value = match kb.get_term(val_tid) {
        Term::Const(Literal::String(s)) => ArgValue::String(s.clone()),
        Term::Const(Literal::Int(n))    => ArgValue::Int(*n),
        Term::Const(Literal::Float(f))  => ArgValue::Float(f.into_inner()),
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

fn dispatch(kb: &mut KnowledgeBase, rec: &ProofRec, args: &ProveArgs) -> Verdict {
    let (tool, tool_args) = match &rec.strategy {
        Strategy::Open => return Verdict::Skipped("open obligation (no `by` clause)".into()),
        Strategy::Tool { name, args } => (name.as_str(), args.as_slice()),
    };
    match tool {
        "z3" => dispatch_z3(kb, &rec.rule, tool_args, args),
        "test" => Verdict::Skipped("`by test` not yet wired".into()),
        "derivation" => dispatch_derivation(kb, &rec.rule, tool_args),
        other => Verdict::Skipped(format!("unknown strategy `{other}`")),
    }
}

fn dispatch_derivation(
    kb: &mut KnowledgeBase,
    rule_qn: &str,
    tool_args: &[NamedArg],
) -> Verdict {
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
        None => return Verdict::EmitError(format!("rule `{rule_qn}` not in KB")),
    };
    let rules = kb.by_functor(rule_sym);
    if rules.is_empty() {
        return Verdict::EmitError(format!("no rules found for `{rule_qn}`"));
    }
    let config = ResolveConfig {
        max_depth,
        max_solutions: max_solutions.max(1),
        simplify: true,
    };
    for rule_id in rules {
        if kb.rule_body(rule_id).is_empty() {
            return Verdict::Proved;
        }
        let empty_subst = anthill_core::kb::subst::Substitution::new();
        let (fresh_body, _links) = kb.with_fresh_vars(rule_id, &empty_subst);
        if !kb.resolve(&fresh_body, &config).is_empty() {
            return Verdict::Proved;
        }
    }
    Verdict::Unknown(format!(
        "no derivation found within depth {max_depth} for `{rule_qn}`"
    ))
}

fn dispatch_z3(
    kb: &mut KnowledgeBase,
    rule_qn: &str,
    tool_args: &[NamedArg],
    cli: &ProveArgs,
) -> Verdict {
    let mut config = ProofConfig::default();
    for arg in tool_args {
        match (arg.key.as_str(), &arg.value) {
            ("logic", ArgValue::String(s)) => config.logic = Some(s.clone()),
            ("timeout", ArgValue::Int(n)) if *n >= 0 => config.timeout_ms = Some(*n as u32),
            _ => {}
        }
    }

    let (smt, deps) = match emit_satisfiability_check_with_deps(kb, rule_qn, &config) {
        Ok(p) => p,
        Err(e) => return Verdict::EmitError(e.message),
    };

    if cli.verbose && !deps.is_empty() {
        println!("  deps: {}", deps.join(", "));
    }

    if cli.dry_run {
        println!("--- {rule_qn} ---");
        print!("{smt}");
        println!("------");
        return Verdict::Skipped("dry-run (SMT printed to stdout)".into());
    }

    if Command::new(&cli.solver).arg("--version").output()
        .map(|o| !o.status.success()).unwrap_or(true)
    {
        return Verdict::Skipped(format!("solver `{}` not on $PATH", cli.solver));
    }

    let path = std::env::temp_dir().join(format!(
        "anthill_prove_{}.smt2",
        sanitize_filename(rule_qn)
    ));
    if let Err(e) = std::fs::write(&path, &smt) {
        return Verdict::EmitError(format!("write smt2: {e}"));
    }

    let out = match Command::new(&cli.solver).arg(&path).output() {
        Ok(o) => o,
        Err(e) => return Verdict::EmitError(format!("invoke {}: {e}", cli.solver)),
    };
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    match stdout.trim() {
        "unsat" => Verdict::Proved,
        "sat" => Verdict::Disproved(stdout),
        "unknown" => Verdict::Unknown("z3: unknown".into()),
        other => Verdict::Unknown(format!("z3 said `{other}` (path: {})", path.display())),
    }
}

fn sanitize_filename(s: &str) -> String {
    s.chars().map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' }).collect()
}

fn indent(s: &str, prefix: &str) -> String {
    s.lines().map(|l| format!("{prefix}{l}")).collect::<Vec<_>>().join("\n")
}
