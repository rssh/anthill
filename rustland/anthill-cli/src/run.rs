//! `anthill run` — execute an anthill program. Discovers entry points by
//! querying SortRequiresInfo facts that refine `anthill.cli.Main`, then
//! invokes the chosen sort's `main(args: List[String]) -> Int` with the
//! post-`--` CLI arguments. Proposal 028.

use std::fs;
use std::path::PathBuf;

use anthill_core::eval::{builtins, value::Value, Interpreter};
use anthill_core::intern::Symbol;
use anthill_core::kb::load::{self, FileSourceResolver};
use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use anthill_core::parse::ir::ParsedFile;
use clap::Parser;

use crate::stdlib_embedded;

// ── Exit codes ──────────────────────────────────────────────────────

/// Compilation failure — parse, load, typecheck errors, or no entry found.
const EXIT_COMPILE: i32 = 2;

/// Runtime failure — evaluator errored during `main`.
const EXIT_RUNTIME: i32 = 1;

/// Substituted for a `main` return value outside the 0..=255 range. Distinct
/// from EXIT_RUNTIME so an out-of-range exit can be distinguished from an
/// evaluator error.
const EXIT_OUT_OF_RANGE: i32 = 255;

// ── Args ────────────────────────────────────────────────────────────

#[derive(Parser)]
pub struct RunArgs {
    /// Qualified name of the sort providing `anthill.cli.Main` to run.
    /// Required when more than one sort provides Main.
    #[arg(long)]
    pub entry: Option<String>,

    /// User .anthill files or directories.
    #[arg(required = true)]
    pub paths: Vec<PathBuf>,

    /// Arguments passed to the program as `args: List[String]`.
    /// Place after `--`.
    #[arg(last = true)]
    pub args: Vec<String>,
}

// ── Entry discovery ─────────────────────────────────────────────────

/// Return the fully-qualified symbol of every sort whose
/// `SortRequiresInfo` spec names `anthill.cli.Main`. Deterministically
/// sorted by qualified name.
fn find_main_providers(kb: &mut KnowledgeBase) -> Vec<Symbol> {
    let main_sym = match kb.try_resolve_symbol("anthill.cli.Main") {
        Some(s) => s,
        None => return Vec::new(),
    };
    let requires_sym = match kb.try_resolve_symbol("anthill.reflect.SortRequiresInfo") {
        Some(s) => s,
        None => return Vec::new(),
    };
    let view_sym = match kb.try_resolve_symbol("anthill.reflect.SortView") {
        Some(s) => s,
        None => return Vec::new(),
    };

    let sort_ref_field = kb.intern("sort_ref");
    let spec_field = kb.intern("spec");

    let mut providers: Vec<Symbol> = Vec::new();
    for rid in kb.rules_by_functor(requires_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let head = kb.rule_head(rid);
        let Term::Fn { named_args, .. } = kb.get_term(head) else { continue };
        let sort_ref_tid = named_args.iter().find(|(s, _)| *s == sort_ref_field).map(|(_, t)| *t);
        let spec_tid = named_args.iter().find(|(s, _)| *s == spec_field).map(|(_, t)| *t);
        let (Some(sr), Some(sp)) = (sort_ref_tid, spec_tid) else { continue };

        // `spec` comes in three shapes depending on how the refining sort
        // wrote its `requires` clause (see proposal 028 §Entry-point
        // discovery). Ours is the unparameterized `Term::Fn` form.
        let spec_sym = match kb.get_term(sp) {
            Term::Ref(s) => Some(*s),
            Term::Fn { functor, pos_args, .. } if *functor == view_sym && !pos_args.is_empty() => {
                spec_sort_symbol(kb, pos_args[0])
            }
            Term::Fn { functor, .. } => Some(*functor),
            _ => None,
        };
        if spec_sym != Some(main_sym) { continue }

        if let Some(provider) = spec_sort_symbol(kb, sr) {
            providers.push(provider);
        }
    }

    providers.sort_by(|a, b| kb.qualified_name_of(*a).cmp(kb.qualified_name_of(*b)));
    providers.dedup();
    providers
}

/// Extract the head symbol of a Term that represents a sort reference
/// (either `Term::Ref(sym)` or `Term::Fn { functor: sym, .. }`).
fn spec_sort_symbol(kb: &KnowledgeBase, tid: TermId) -> Option<Symbol> {
    match kb.get_term(tid) {
        Term::Ref(s) => Some(*s),
        Term::Fn { functor, .. } => Some(*functor),
        _ => None,
    }
}

fn print_candidates(kb: &KnowledgeBase, providers: &[Symbol]) {
    eprintln!("candidates:");
    for p in providers {
        eprintln!("  {}", kb.qualified_name_of(*p));
    }
}

// ── Loading ─────────────────────────────────────────────────────────

/// Parse user files from `paths`. Returns (parsed files, errors).
fn parse_user_files(paths: &[PathBuf]) -> (Vec<ParsedFile>, Vec<String>) {
    let mut files = Vec::new();
    let mut errors = Vec::new();
    let collected = match crate::collect_anthill_files(paths) {
        Ok(f) => f,
        Err(errs) => return (files, errs),
    };
    for path in &collected {
        let source = match fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                errors.push(format!("{}: read error: {e}", path.display()));
                continue;
            }
        };
        match parse::parse(&source) {
            Ok(p) => files.push(p),
            Err(parse_errors) => {
                for pe in &parse_errors {
                    errors.push(format!("{}: {pe}", path.display()));
                }
            }
        }
    }
    (files, errors)
}

fn build_kb(paths: &[PathBuf]) -> Result<KnowledgeBase, i32> {
    let (stdlib_parsed, stdlib_errors) = stdlib_embedded::parse_embedded_stdlib();
    if !stdlib_errors.is_empty() {
        // Embedded stdlib failing to parse is a build-level regression, not a
        // user-facing recoverable warning.
        for e in &stdlib_errors {
            eprintln!("error: {e}");
        }
        return Err(EXIT_COMPILE);
    }

    let (user_parsed, user_errors) = parse_user_files(paths);
    if !user_errors.is_empty() {
        for e in &user_errors {
            eprintln!("error: {e}");
        }
        return Err(EXIT_COMPILE);
    }

    let mut kb = KnowledgeBase::new();
    let resolver = FileSourceResolver::new(base_dirs_for(paths));

    // Type errors are fatal — running an ill-typed program is unsound.
    // Other LoadErrors stay as warnings: some are recoverable (e.g.
    // ambiguous-symbol reports when stdlib `register_prelude` makes names
    // visible in parallel with explicit `import` clauses).
    let mut all_refs: Vec<&ParsedFile> = stdlib_parsed.iter().collect();
    all_refs.extend(user_parsed.iter());
    if let Err(errs) = load::load_all(&mut kb, &all_refs, &resolver) {
        let mut had_type_error = false;
        for e in &errs {
            if e.is_load_blocking() {
                had_type_error = true;
                eprintln!("error: {e}");
            } else {
                eprintln!("warning: {e}");
            }
        }
        if had_type_error {
            return Err(EXIT_COMPILE);
        }
    }

    Ok(kb)
}

fn base_dirs_for(paths: &[PathBuf]) -> Vec<PathBuf> {
    paths
        .iter()
        .filter_map(|p| {
            if p.is_dir() {
                p.parent().map(|pp| pp.to_path_buf())
            } else {
                p.parent().and_then(|pp| pp.parent()).map(|pp| pp.to_path_buf())
            }
        })
        .collect::<std::collections::HashSet<_>>()
        .into_iter()
        .collect()
}

// ── Run command ─────────────────────────────────────────────────────

/// Returns the process exit code. Error variants are still encoded as exit
/// codes (EXIT_COMPILE / EXIT_RUNTIME / EXIT_OUT_OF_RANGE); the caller just
/// forwards the number.
pub fn run(args: &RunArgs) -> i32 {
    match run_inner(args) {
        Ok(code) => code,
        Err(code) => code,
    }
}

fn run_inner(args: &RunArgs) -> Result<i32, i32> {
    let mut kb = build_kb(&args.paths)?;

    let providers = find_main_providers(&mut kb);
    let chosen = select_entry(&kb, &providers, args.entry.as_deref())?;
    let main_qname = format!("{}.main", kb.qualified_name_of(chosen));

    let mut interp = Interpreter::new(kb);
    builtins::register_standard_builtins(&mut interp)
        .map_err(|e| { eprintln!("error: registering builtins: {e}"); EXIT_RUNTIME })?;
    interp.register_standard_effect_handlers()
        .map_err(|e| { eprintln!("error: registering effect handlers: {e}"); EXIT_RUNTIME })?;

    let elements: Vec<Value> = args.args.iter().map(|s| Value::Str(s.clone())).collect();
    let args_value = interp.build_list_value(elements, &[])
        .map_err(|e| { eprintln!("error: {e}"); EXIT_RUNTIME })?;

    match interp.call(&main_qname, &[args_value]) {
        Ok(Value::Int(n)) => Ok(clamp_exit(n)),
        Ok(other) => {
            eprintln!("error: main returned non-Int value: {other:?}");
            Err(EXIT_RUNTIME)
        }
        Err(e) => {
            eprintln!("error: {e}");
            Err(EXIT_RUNTIME)
        }
    }
}

fn select_entry(
    kb: &KnowledgeBase,
    providers: &[Symbol],
    entry: Option<&str>,
) -> Result<Symbol, i32> {
    match providers.len() {
        0 => {
            eprintln!("error: no program entry found (expected `sort … requires anthill.cli.Main`)");
            Err(EXIT_COMPILE)
        }
        1 => {
            let only = providers[0];
            if let Some(req) = entry {
                if kb.qualified_name_of(only) != req {
                    eprintln!(
                        "error: --entry {req} does not match the sole program entry {}",
                        kb.qualified_name_of(only)
                    );
                    return Err(EXIT_COMPILE);
                }
            }
            Ok(only)
        }
        n => match entry {
            None => {
                eprintln!("error: ambiguous program entry — {n} sorts provide anthill.cli.Main");
                print_candidates(kb, providers);
                eprintln!("pass --entry <sort> to select one");
                Err(EXIT_COMPILE)
            }
            Some(req) => providers
                .iter()
                .find(|p| kb.qualified_name_of(**p) == req)
                .copied()
                .ok_or_else(|| {
                    eprintln!("error: --entry {req} is not among the program entries");
                    print_candidates(kb, providers);
                    EXIT_COMPILE
                }),
        },
    }
}

/// Coerce `main`'s return value to a process exit code. Values outside
/// 0..=255 clamp to EXIT_OUT_OF_RANGE (distinct from EXIT_RUNTIME so a
/// nonsense return can be distinguished from an evaluator error).
fn clamp_exit(n: i64) -> i32 {
    if (0..=255).contains(&n) { n as i32 } else { EXIT_OUT_OF_RANGE }
}
