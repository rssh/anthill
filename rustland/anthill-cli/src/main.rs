use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand, ValueEnum};

use anthill_core::codegen::generate_rust;
use anthill_core::kb::load::{self, FileSourceResolver};
use anthill_core::kb::resolve::{ResolveConfig, Solution};
use anthill_core::kb::subst::Substitution;
use anthill_core::kb::{KnowledgeBase, RuleId};
use anthill_core::parse;
use anthill_core::parse::ir::{Item, ParsedFile};
use anthill_core::persistence::print::TermPrinter;
use anthill_core::persistence::term_ser;

mod run;
mod stdlib_embedded;

// ── CLI types ───────────────────────────────────────────────────────

#[derive(Parser)]
#[command(name = "anthill", about = "Anthill language toolkit")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Generate host-language code from .anthill sources
    Codegen {
        #[command(subcommand)]
        target: CodegenTarget,
    },
    /// Load .anthill files into the knowledge base and report stats
    Load(LoadArgs),
    /// Query the knowledge base
    Query(QueryArgs),
    /// Check constraints (scaffold)
    Check(CheckArgs),
    /// Run an anthill program (entry via `requires anthill.cli.Main`)
    Run(run::RunArgs),
}

#[derive(Subcommand)]
enum CodegenTarget {
    /// Generate Rust skeleton code (traits, structs, enums)
    Rust(RustCodegenArgs),
}

#[derive(Parser)]
struct RustCodegenArgs {
    /// .anthill files or directories to process
    #[arg(required = true)]
    paths: Vec<PathBuf>,

    /// Output directory for generated .rs files
    #[arg(short, long, default_value = "./generated")]
    output_dir: PathBuf,

    /// Print what would be generated without writing files
    #[arg(long)]
    dry_run: bool,
}

#[derive(Parser)]
struct LoadArgs {
    /// .anthill files or directories to load
    #[arg(required = true)]
    paths: Vec<PathBuf>,

    /// Additional import names to load (e.g. anthill.prelude.List)
    #[arg(short = 'i', long = "import")]
    imports: Vec<String>,

    /// Print verbose output
    #[arg(long)]
    verbose: bool,

    /// Do not auto-include the embedded standard library. By default
    /// `anthill load` parses the stdlib alongside the requested paths
    /// so that prelude / reflect / realization references resolve.
    #[arg(long = "no-stdlib")]
    no_stdlib: bool,
}

#[derive(Parser)]
struct QueryArgs {
    /// Inline query pattern (e.g. 'EntityOf(?x, List)')
    pattern: Option<String>,

    /// Read queries from a .anthill file (imports + fact declarations)
    #[arg(long)]
    query_file: Option<PathBuf>,

    /// Import names into query scope (e.g. -i anthill.prelude.List)
    #[arg(short = 'i', long = "import")]
    imports: Vec<String>,

    /// .anthill files or directories to load into the KB
    #[arg(short = 'p', long = "path", required = true)]
    paths: Vec<PathBuf>,

    /// Query mode
    #[arg(long, default_value = "pattern")]
    mode: QueryMode,

    /// Maximum number of results (0 = unlimited)
    #[arg(long, default_value = "100")]
    max_results: usize,

    /// Use SLD resolution instead of pattern matching
    #[arg(long)]
    resolve: bool,

    /// Maximum resolution depth (for --resolve)
    #[arg(long, default_value = "100")]
    max_depth: usize,
}

#[derive(Clone, ValueEnum)]
enum QueryMode {
    /// Pattern matching against KB facts
    Pattern,
    /// List facts of a given sort
    Sort,
    /// List facts by functor name
    Functor,
    /// List facts in a domain
    Domain,
}

#[derive(Parser)]
struct CheckArgs {
    /// .anthill files or directories to check
    #[arg(required = true)]
    paths: Vec<PathBuf>,
}

// ── File collection ─────────────────────────────────────────────────

fn collect_anthill_files(paths: &[PathBuf]) -> Result<Vec<PathBuf>, Vec<String>> {
    let mut files = Vec::new();
    let mut errors = Vec::new();

    for path in paths {
        if !path.exists() {
            errors.push(format!("path does not exist: {}", path.display()));
            continue;
        }
        if path.is_dir() {
            collect_files_recursive(path, &mut files, &["anthill"]);
        } else if has_extension(path, &["anthill"]) {
            files.push(path.clone());
        } else {
            errors.push(format!("not an .anthill file: {}", path.display()));
        }
    }

    if !errors.is_empty() {
        return Err(errors);
    }

    files.sort();
    files.dedup();
    Ok(files)
}

/// Check if a file path has one of the given extensions.
fn has_extension(path: &Path, extensions: &[&str]) -> bool {
    path.extension()
        .and_then(|e| e.to_str())
        .map(|e| extensions.contains(&e))
        .unwrap_or(false)
}

/// Recursively collect files with matching extensions from a directory.
fn collect_files_recursive(dir: &Path, out: &mut Vec<PathBuf>, extensions: &[&str]) {
    let entries = match fs::read_dir(dir) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("warning: cannot read directory {}: {e}", dir.display());
            return;
        }
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_files_recursive(&path, out, extensions);
        } else if has_extension(&path, extensions) {
            out.push(path);
        }
    }
}

/// Collect `.toml` and `.json` data files from paths (directories or individual files).
fn collect_data_files(paths: &[PathBuf]) -> Vec<PathBuf> {
    let mut files = Vec::new();
    for path in paths {
        if !path.exists() {
            continue;
        }
        if path.is_dir() {
            collect_files_recursive(path, &mut files, &["toml", "json"]);
        } else if has_extension(path, &["toml", "json"]) {
            files.push(path.clone());
        }
    }
    files.sort();
    files.dedup();
    files
}

// ── Output naming ───────────────────────────────────────────────────

fn output_filename(input: &Path) -> String {
    let stem = input
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("out");
    format!("{stem}.rs")
}

// ── Shared KB loader ────────────────────────────────────────────────

fn load_kb(paths: &[PathBuf], verbose: bool) -> Result<KnowledgeBase, i32> {
    load_kb_with_stdlib(paths, verbose, false)
}

fn load_kb_with_stdlib(paths: &[PathBuf], verbose: bool, include_stdlib: bool)
    -> Result<KnowledgeBase, i32>
{
    let files = match collect_anthill_files(paths) {
        Ok(f) => f,
        Err(errs) => {
            for e in &errs {
                eprintln!("error: {e}");
            }
            return Err(1);
        }
    };

    if files.is_empty() {
        eprintln!("error: no .anthill files found");
        return Err(1);
    }

    // Parse all files
    let mut parsed_files = Vec::new();
    let mut errors = Vec::new();

    if include_stdlib {
        let (stdlib_files, stdlib_errors) = stdlib_embedded::parse_embedded_stdlib();
        if verbose {
            eprintln!("included {} embedded stdlib file(s)", stdlib_files.len());
        }
        parsed_files.extend(stdlib_files);
        for e in &stdlib_errors {
            errors.push(e.clone());
        }
    }

    for file in &files {
        let source = match fs::read_to_string(file) {
            Ok(s) => s,
            Err(e) => {
                errors.push(format!("{}: read error: {e}", file.display()));
                continue;
            }
        };
        match parse::parse(&source) {
            Ok(p) => parsed_files.push(p),
            Err(parse_errors) => {
                for pe in &parse_errors {
                    errors.push(format!("{}: {pe}", file.display()));
                }
            }
        }
    }

    if !errors.is_empty() {
        for e in &errors {
            eprintln!("error: {e}");
        }
        return Err(1);
    }

    if verbose {
        eprintln!("parsed {} file(s)", parsed_files.len());
    }

    // Build KB
    let mut kb = KnowledgeBase::new();

    // Build FileSourceResolver from parent dirs of input paths
    let base_dirs: Vec<PathBuf> = paths
        .iter()
        .filter_map(|p| {
            if p.is_dir() {
                // For a directory like stdlib/anthill/prelude/, we want the grandparent
                // (stdlib/) so that "anthill.prelude.List" resolves to
                // stdlib/anthill/prelude/List.anthill
                p.parent().map(|pp| pp.to_path_buf())
            } else {
                p.parent().and_then(|pp| pp.parent()).map(|pp| pp.to_path_buf())
            }
        })
        .collect::<std::collections::HashSet<_>>()
        .into_iter()
        .collect();
    let resolver = FileSourceResolver::new(base_dirs);

    let refs: Vec<&ParsedFile> = parsed_files.iter().collect();
    if let Err(load_errors) = load::load_all(&mut kb, &refs, &resolver) {
        // Print load errors as warnings — some unresolved names are expected
        // when loading without the full stdlib
        for e in &load_errors {
            eprintln!("warning: {e}");
        }
    }

    // Load .toml and .json data files (after entity definitions are available)
    let data_files = collect_data_files(paths);
    if !data_files.is_empty() {
        let domain = kb.make_name_term("_data");
        for file in &data_files {
            let source = match fs::read_to_string(file) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("warning: {}: read error: {e}", file.display());
                    continue;
                }
            };
            let ext = file.extension().and_then(|e| e.to_str()).unwrap_or("");
            let result = match ext {
                "toml" => term_ser::load_toml(&mut kb, &source, domain),
                "json" => term_ser::load_json(&mut kb, &source, domain),
                _ => continue,
            };
            match result {
                Ok(n) => {
                    if verbose {
                        eprintln!("loaded {} fact(s) from {}", n, file.display());
                    }
                }
                Err(errs) => {
                    for e in &errs {
                        eprintln!("warning: {}: {e}", file.display());
                    }
                }
            }
        }
    }

    Ok(kb)
}

// ── Codegen driver ──────────────────────────────────────────────────

fn run_codegen_rust(args: &RustCodegenArgs) -> Result<(), i32> {
    let files = match collect_anthill_files(&args.paths) {
        Ok(f) => f,
        Err(errs) => {
            for e in &errs {
                eprintln!("error: {e}");
            }
            return Err(1);
        }
    };

    if files.is_empty() {
        eprintln!("error: no .anthill files found");
        return Err(1);
    }

    if !args.dry_run {
        if let Err(e) = fs::create_dir_all(&args.output_dir) {
            eprintln!("error: cannot create output directory {}: {e}", args.output_dir.display());
            return Err(1);
        }
    }

    let mut errors: Vec<String> = Vec::new();
    let mut generated = 0u32;

    for file in &files {
        let source = match fs::read_to_string(file) {
            Ok(s) => s,
            Err(e) => {
                errors.push(format!("{}: read error: {e}", file.display()));
                continue;
            }
        };

        let parsed = match parse::parse(&source) {
            Ok(p) => p,
            Err(parse_errors) => {
                for pe in &parse_errors {
                    errors.push(format!("{}: {pe}", file.display()));
                }
                continue;
            }
        };

        let rust_code = match generate_rust(&parsed) {
            Ok(code) => code,
            Err(errs) => {
                for e in &errs {
                    errors.push(format!("{}: {e}", file.display()));
                }
                continue;
            }
        };
        let out_name = output_filename(file);
        let out_path = args.output_dir.join(&out_name);

        if args.dry_run {
            println!("[dry-run] {} -> {}", file.display(), out_path.display());
        } else {
            if let Err(e) = fs::write(&out_path, &rust_code) {
                errors.push(format!("{}: write error: {e}", out_path.display()));
                continue;
            }
            println!("{} -> {}", file.display(), out_path.display());
        }
        generated += 1;
    }

    if !errors.is_empty() {
        eprintln!();
        for e in &errors {
            eprintln!("error: {e}");
        }
        eprintln!();
    }

    let verb = if args.dry_run { "would generate" } else { "generated" };
    eprintln!("{verb} {generated} file(s), {} error(s)", errors.len());

    if errors.is_empty() {
        Ok(())
    } else {
        Err(1)
    }
}

// ── Load command ────────────────────────────────────────────────────

fn run_load(args: &LoadArgs) -> Result<(), i32> {
    let kb = load_kb_with_stdlib(&args.paths, args.verbose, !args.no_stdlib)?;
    println!("loaded: {} facts, {} rules", kb.fact_count(), kb.rule_count());
    Ok(())
}

// ── Query command ───────────────────────────────────────────────────

fn run_query(args: &QueryArgs) -> Result<(), i32> {
    if args.pattern.is_none() && args.query_file.is_none() {
        eprintln!("error: provide either a pattern argument or --query-file");
        return Err(1);
    }
    if args.pattern.is_some() && args.query_file.is_some() {
        eprintln!("error: provide either a pattern argument or --query-file, not both");
        return Err(1);
    }

    let mut kb = load_kb(&args.paths, false)?;

    // Dispatch on mode
    match args.mode {
        QueryMode::Sort => {
            let name = args.pattern.as_deref().ok_or_else(|| {
                eprintln!("error: --mode sort requires a pattern argument (sort name)");
                1
            })?;
            // Try both make_name_term (for kernel meta-sorts like Sort, Fact)
            // and resolve_qualified_name_term (for user-defined sorts)
            let sort_term = kb.make_name_term(name);
            let mut results = kb.by_sort(sort_term);
            if results.is_empty() {
                let alt = kb.resolve_qualified_name_term(name);
                results = kb.by_sort(alt);
            }
            print_rule_results(&kb, &results, args.max_results);
        }
        QueryMode::Functor => {
            let name = args.pattern.as_deref().ok_or_else(|| {
                eprintln!("error: --mode functor requires a pattern argument (functor name)");
                1
            })?;
            let sym = kb.try_resolve_symbol(name).unwrap_or_else(|| kb.intern(name));
            let results = kb.by_functor(sym);
            print_rule_results(&kb, &results, args.max_results);
        }
        QueryMode::Domain => {
            let name = args.pattern.as_deref().ok_or_else(|| {
                eprintln!("error: --mode domain requires a pattern argument (domain name)");
                1
            })?;
            let domain_term = kb.resolve_qualified_name_term(name);
            let results = kb.by_domain(domain_term);
            print_rule_results(&kb, &results, args.max_results);
        }
        QueryMode::Pattern => {
            let queries = collect_queries(args, &mut kb)?;
            let multi = queries.len() > 1;

            for (label, query_terms) in &queries {
                if multi {
                    println!("--- query: {} ---", label);
                }

                for &qt in query_terms {
                    if args.resolve {
                        let config = ResolveConfig {
                            max_depth: args.max_depth,
                            max_solutions: args.max_results,
                            simplify: false,
                        };
                        let solutions = kb.resolve(&[qt], &config);
                        print_solutions(&kb, &solutions, qt, args.max_results);
                    } else {
                        let results = kb.query(qt);
                        print_query_results(&kb, &results, args.max_results);
                    }
                }

                if multi {
                    println!();
                }
            }
        }
    }

    Ok(())
}

/// Collect query terms from either an inline pattern or a query file.
/// Returns (label, vec-of-term-ids) pairs.
fn collect_queries(
    args: &QueryArgs,
    kb: &mut KnowledgeBase,
) -> Result<Vec<(String, Vec<anthill_core::kb::term::TermId>)>, i32> {
    if let Some(ref pattern) = args.pattern {
        // Build source: import lines + fact pattern
        let mut source = String::new();
        for imp in &args.imports {
            source.push_str(&format!("import {imp}\n"));
        }
        source.push_str(&format!("fact {pattern}"));

        let parsed = match parse::parse(&source) {
            Ok(p) => p,
            Err(errs) => {
                for e in &errs {
                    eprintln!("parse error: {e}");
                }
                return Err(1);
            }
        };

        // Scan definitions for name resolution
        let scan_errors = load::scan_definitions(kb, &[&parsed]);
        for e in &scan_errors {
            eprintln!("warning: {e}");
        }

        // Extract the fact term and reintern into KB
        let global_raw = kb.make_name_term("_global").raw();
        let mut var_map = HashMap::new();
        let mut terms = Vec::new();
        for item in &parsed.items {
            if let Item::Fact(fact) = item {
                let tid = load::convert_query_term(
                    kb,
                    &parsed.terms,
                    &parsed.symbols,
                    fact.term,
                    global_raw,
                    &mut var_map,
                );
                terms.push(tid);
            }
        }
        if terms.is_empty() {
            eprintln!("error: no valid query pattern found");
            return Err(1);
        }
        Ok(vec![(pattern.clone(), terms)])
    } else if let Some(ref query_file) = args.query_file {
        let mut source = String::new();
        // Prepend --import flags
        for imp in &args.imports {
            source.push_str(&format!("import {imp}\n"));
        }
        let file_source = match fs::read_to_string(query_file) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("error: cannot read {}: {e}", query_file.display());
                return Err(1);
            }
        };
        source.push_str(&file_source);

        let parsed = match parse::parse(&source) {
            Ok(p) => p,
            Err(errs) => {
                for e in &errs {
                    eprintln!("parse error: {e}");
                }
                return Err(1);
            }
        };

        // Scan definitions for name resolution
        let scan_errors = load::scan_definitions(kb, &[&parsed]);
        for e in &scan_errors {
            eprintln!("warning: {e}");
        }

        // Extract all fact items as queries
        let global_raw = kb.make_name_term("_global").raw();
        let mut queries = Vec::new();
        let mut var_map = HashMap::new();
        for item in &parsed.items {
            if let Item::Fact(fact) = item {
                let tid = load::convert_query_term(
                    kb,
                    &parsed.terms,
                    &parsed.symbols,
                    fact.term,
                    global_raw,
                    &mut var_map,
                );
                let label = TermPrinter::new(kb).print_term(tid);
                queries.push((label, vec![tid]));
            }
        }
        if queries.is_empty() {
            eprintln!("error: no fact declarations found in {}", query_file.display());
            return Err(1);
        }
        Ok(queries)
    } else {
        unreachable!()
    }
}

// ── Check command ───────────────────────────────────────────────────

fn run_check(args: &CheckArgs) -> Result<(), i32> {
    let kb = load_kb(&args.paths, false)?;
    println!("loaded: {} facts, {} rules", kb.fact_count(), kb.rule_count());
    println!("note: constraint evaluation not yet implemented");
    Ok(())
}

// ── Display helpers ─────────────────────────────────────────────────

fn print_rule_results(kb: &KnowledgeBase, results: &[RuleId], max: usize) {
    let printer = TermPrinter::new(kb);
    let limit = if max == 0 { results.len() } else { max.min(results.len()) };

    for &rid in &results[..limit] {
        let head = kb.rule_head(rid);
        let body = kb.rule_body(rid);
        if body.is_empty() {
            println!("  {}", printer.print_term(head));
        } else {
            let body_strs: Vec<String> = body.iter().map(|&t| printer.print_term(t)).collect();
            println!("  {} :- {}", printer.print_term(head), body_strs.join(", "));
        }
    }

    let total = results.len();
    if max > 0 && total > max {
        println!("  ... ({} more, {} total)", total - max, total);
    } else {
        println!("{total} result(s)");
    }
}

fn print_query_results(
    kb: &KnowledgeBase,
    results: &[(RuleId, Substitution)],
    max: usize,
) {
    let printer = TermPrinter::new(kb);
    let limit = if max == 0 { results.len() } else { max.min(results.len()) };

    for (rid, subst) in &results[..limit] {
        let head = kb.rule_head(*rid);
        print!("  {}", printer.print_term(head));
        // Print bindings if any
        let bindings: Vec<String> = subst
            .iter()
            .map(|(vid, val)| {
                use anthill_core::eval::Value;
                let rendered = match val {
                    Value::Term(tid) => printer.print_term(*tid),
                    Value::Int(n) => n.to_string(),
                    Value::BigInt(n) => n.to_string(),
                    Value::Float(f) => f.to_string(),
                    Value::Bool(b) => b.to_string(),
                    Value::Str(s) => format!("{:?}", s),
                    other => format!("{:?}", other),
                };
                format!("?{} = {}", kb.resolve_sym(vid.name()), rendered)
            })
            .collect();
        if !bindings.is_empty() {
            print!("  [{}]", bindings.join(", "));
        }
        println!();
    }

    let total = results.len();
    if max > 0 && total > max {
        println!("  ... ({} more, {} total)", total - max, total);
    } else {
        println!("{total} result(s)");
    }
}

fn print_solutions(
    kb: &KnowledgeBase,
    solutions: &[Solution],
    query_term: anthill_core::kb::term::TermId,
    max: usize,
) {
    let printer = TermPrinter::new(kb);
    let limit = if max == 0 { solutions.len() } else { max.min(solutions.len()) };

    if solutions.is_empty() {
        println!("  no solutions");
        return;
    }

    // Collect vars from query for display
    let query_vars = kb.collect_vars(query_term);

    for sol in &solutions[..limit] {
        let bindings: Vec<String> = query_vars
            .iter()
            .filter_map(|vid| {
                sol.subst.resolve_with_term(*vid).map(|tid| {
                    format!("?{} = {}", kb.resolve_sym(vid.name()), printer.print_term(tid))
                })
            })
            .collect();
        if bindings.is_empty() {
            println!("  true");
        } else {
            println!("  {}", bindings.join(", "));
        }
        if !sol.residual.is_empty() {
            let residuals: Vec<String> = sol.residual.iter().map(|&t| printer.print_term(t)).collect();
            println!("    residual: {}", residuals.join(", "));
        }
    }

    let total = solutions.len();
    if max > 0 && total > max {
        println!("  ... ({} more, {} total)", total - max, total);
    } else {
        println!("{total} solution(s)");
    }
}

// ── Entry point ─────────────────────────────────────────────────────

fn main() -> ExitCode {
    let cli = Cli::parse();

    // `Run` carries its own exit code (the program's return value plus
    // distinct codes for compile vs runtime failure) and bypasses the
    // SUCCESS/FAILURE collapse used by the other commands.
    let result = match cli.command {
        Command::Codegen { target } => match target {
            CodegenTarget::Rust(ref args) => run_codegen_rust(args),
        },
        Command::Load(ref args) => run_load(args),
        Command::Query(ref args) => run_query(args),
        Command::Check(ref args) => run_check(args),
        Command::Run(ref args) => return ExitCode::from(run::run(args) as u8),
    };

    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(_) => ExitCode::FAILURE,
    }
}
