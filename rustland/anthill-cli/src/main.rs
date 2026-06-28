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

mod check;
mod prove;
mod run;
mod witness;

// ── CLI types ───────────────────────────────────────────────────────

#[derive(Parser)]
#[command(
    name = "anthill",
    about = "Anthill language toolkit",
    version = anthill_version::clap_version!()
)]
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
    /// Discharge proof obligations declared via `proof <rule> by ...` blocks
    Prove(ProveArgs),
}

#[derive(Subcommand)]
enum CodegenTarget {
    /// Generate Rust skeleton code (traits, structs, enums)
    Rust(RustCodegenArgs),
    /// Generate a C++17/20 namespace header from anthill specs
    Cpp(CppCodegenArgs),
    /// Scaffold a complete C++ controller project (Makefile + copies
    /// of hand-authored sources alongside generated headers)
    CppProject(CppProjectArgs),
    /// Bundle anthill sources into a Rust crate (`rust+anthill` profile).
    /// Emits a self-contained crate that embeds the spec and dispatches
    /// the named entry op via the interpreter at runtime.
    Bundle(BundleArgs),
}

#[derive(Parser)]
struct BundleArgs {
    /// .anthill source files / directories to bundle. Every `.anthill`
    /// file under the given paths is vendored into the output crate.
    #[arg(required = true)]
    paths: Vec<PathBuf>,

    /// Output directory for the generated crate. Created if absent;
    /// existing files in it are overwritten without warning.
    #[arg(short, long)]
    output_dir: PathBuf,

    /// Crate name (and binary name) for the generated project.
    #[arg(short = 'n', long = "name")]
    project_name: String,

    /// Operation qualified name to dispatch as `main(args: List[String]) -> Int`.
    /// Example: `my.app.main`.
    #[arg(short, long)]
    entry: String,

    /// One-line description for the generated `Cargo.toml`. Omitted from
    /// the emitted manifest when not set. Cargo (and `cargo publish`)
    /// reject empty quoted descriptions, so leave this off rather than
    /// passing an empty string.
    #[arg(long)]
    description: Option<String>,

    /// Reference anthill-core via a git URL instead of a local path. When
    /// set, the generated Cargo.toml uses `{ git = ..., rev = ... }`. The
    /// resulting bundle is portable across machines (build needs git +
    /// network, but no local checkout). Must be paired with `--git-rev`.
    #[arg(long = "git-url", requires = "git_rev")]
    git_url: Option<String>,

    /// Pin the git dependency to this commit / tag / branch ref. Must
    /// be paired with `--git-url`.
    #[arg(long = "git-rev", requires = "git_url")]
    git_rev: Option<String>,
}

#[derive(Parser)]
struct CppCodegenArgs {
    /// .anthill source files / directories to load (in addition to
    /// the embedded stdlib).
    #[arg(required = true)]
    paths: Vec<PathBuf>,

    /// Anthill namespace to emit. Produces `<short>.hpp` covering all
    /// entities, sum sorts, and traits classes declared directly
    /// under the namespace.
    #[arg(short = 'n', long = "namespace")]
    namespace: String,

    /// Output directory. Headers land here; `anthill_runtime.hpp` is
    /// copied alongside (and `anthill_geometry.hpp` if the namespace
    /// uses Vec3 / EulerAngles).
    #[arg(short, long, default_value = "./generated")]
    output_dir: PathBuf,

    /// Print emitted contents to stdout instead of writing files.
    #[arg(long)]
    dry_run: bool,
}

#[derive(Parser)]
struct CppProjectArgs {
    /// .anthill source files / directories to load.
    #[arg(required = true)]
    paths: Vec<PathBuf>,

    /// Anthill namespace whose traits classes become C++ controller
    /// targets. One controller is scaffolded per traits class found.
    #[arg(short = 'n', long = "namespace")]
    namespace: String,

    /// Directory holding hand-authored C++ sources to copy verbatim
    /// into each generated controller folder (e.g. `mavic_base.cpp`,
    /// `*_main.cpp`). Files are copied byte-for-byte; the generated
    /// Makefile compiles them alongside the generated header.
    #[arg(long = "cpp-sources", default_value = "./cpp")]
    cpp_sources: PathBuf,

    /// Directory holding `.wbt` world files (and any other Webots
    /// project assets) to copy into `<output>/worlds/` verbatim.
    /// Optional — when the directory doesn't exist, no worlds are
    /// copied and the user must drop a `.wbt` in by hand before
    /// launching Webots.
    #[arg(long = "worlds-dir", default_value = "./worlds")]
    worlds_dir: PathBuf,

    /// Output directory for the generated project. One subdirectory
    /// per controller, each self-contained (sources + Makefile + a
    /// copy of the runtime / geometry headers) so the result drops
    /// into a fresh Webots install without requiring any reference
    /// project.
    #[arg(short, long, default_value = "./generated")]
    output_dir: PathBuf,

    /// Print intended actions without writing files.
    #[arg(long)]
    dry_run: bool,
}

#[derive(Parser)]
struct ProveArgs {
    /// .anthill source files / directories to load (in addition to
    /// the embedded stdlib).
    #[arg(required = true)]
    paths: Vec<PathBuf>,

    /// Discharge only this proof (qualified rule name, e.g.
    /// `anthill.examples.lf1.safety.lower_violation`). When omitted,
    /// discharges every proof in the loaded KB.
    #[arg(long = "rule")]
    rule: Option<String>,

    /// External solver binary to invoke for `by z3` strategies.
    /// Default `z3`. Override for non-standard installs or alt-prover
    /// experiments.
    #[arg(long, default_value = "z3")]
    solver: String,

    /// Print emitted SMT-LIB to stdout instead of running the solver.
    /// Useful for debugging or when `z3` isn't on $PATH.
    #[arg(long)]
    dry_run: bool,

    /// Print extra progress info.
    #[arg(short, long)]
    verbose: bool,

    /// Bypass the proof cache for this run — every proof goes to the
    /// solver. (Cache reads AND writes are disabled.)
    #[arg(long = "no-cache")]
    no_cache: bool,

    /// Force re-run of every proof and overwrite cached entries.
    /// Useful after a solver upgrade or when debugging stale results.
    #[arg(long = "refresh-cache")]
    refresh_cache: bool,

    /// Print cached entries (key, verdict, age) for the loaded KB and
    /// exit. No proofs are dispatched.
    #[arg(long = "show-cache")]
    show_cache: bool,

    /// Override the cache root directory. Default: XDG cache (e.g.
    /// `~/.cache/anthill/` on Linux, `~/Library/Caches/anthill/` on
    /// macOS). Also honoured: `$ANTHILL_CACHE_DIR`.
    #[arg(long = "cache-dir")]
    cache_dir: Option<PathBuf>,

    /// Garbage-collect cache entries older than N days for the
    /// current project's subtree, then exit.
    #[arg(long = "gc-cache")]
    gc_cache: Option<u32>,

    /// After the run, print a summary of cache hits / misses / writes.
    #[arg(long = "stats")]
    stats: bool,
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

    /// Skip the witness-replay step; only verify state-hash and
    /// structural integrity. Faster but doesn't catch a Z3-says-
    /// different-now drift; mainly useful as a smoke-test in
    /// pre-commit hooks.
    #[arg(long, conflicts_with = "deep")]
    shallow: bool,

    /// Full witness replay (the default). Specified explicitly when
    /// pairing with `--report-stale` etc. — if neither --shallow
    /// nor --deep is set, --deep semantics apply.
    #[arg(long)]
    deep: bool,

    /// List stale ProofRecords (state-hash differs from current KB
    /// state) without re-running the witness check. Useful as the
    /// "what would change?" query before a `prove --refresh-cache`.
    #[arg(long)]
    report_stale: bool,

    /// List every ProofRecord whose witness tree contains a
    /// TrustedAxiom — surfaces the trust dependencies a project
    /// has accumulated.
    #[arg(long)]
    report_trust: bool,

    /// Restrict checking to ProofRecords whose rule QN matches the
    /// glob. Standard glob syntax (`*` matches any segment chars
    /// including `.`). Repeatable to combine multiple patterns.
    #[arg(long)]
    filter: Vec<String>,

    /// Solver binary used for SmtDischarge replay. Default `z3`.
    #[arg(long, default_value = "z3")]
    solver: String,

    /// WI-564: treat any relied-upon proof that is not verified — failed,
    /// refuted, or unconfirmable because the solver is unavailable / timed out —
    /// as a hard error rather than a warning. By default `check` chains the
    /// proof-discharge pass and degrades to a loud warning (so a z3-less dev/CI
    /// run still completes); this flag makes the gate airtight for CI.
    #[arg(long = "require-proofs")]
    require_proofs: bool,
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
        let (stdlib_files, stdlib_errors) = anthill::stdlib::parse_embedded();
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
    match load::load_all(&mut kb, &refs, &resolver) {
        Ok(result) => {
            // WI-346: surface advisory load warnings (e.g. requires-shadow).
            for w in &result.warnings {
                eprintln!("{w}");
            }
        }
        Err(load_errors) => {
            let mut had_type_error = false;
            for e in &load_errors {
                if e.is_load_blocking() {
                    had_type_error = true;
                    eprintln!("error: {e}");
                } else {
                    eprintln!("warning: {e}");
                }
            }
            if had_type_error {
                return Err(1);
            }
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

fn run_codegen_bundle(args: &BundleArgs) -> Result<(), i32> {
    let files = match collect_anthill_files(&args.paths) {
        Ok(f) => f,
        Err(errs) => {
            for e in &errs { eprintln!("error: {e}"); }
            return Err(1);
        }
    };
    if files.is_empty() {
        eprintln!("error: no .anthill files found");
        return Err(1);
    }

    // The generated crate vendors copies of each user source. For paths we
    // store inside the bundle, prefer the file name relative to the FIRST
    // ancestor that's a directory among `paths` so the layout stays sane;
    // fall back to the file's own basename when no parent dir is given.
    let mut user_sources: Vec<(String, String)> = Vec::with_capacity(files.len());
    for file in &files {
        let content = match fs::read_to_string(file) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("error: read {}: {e}", file.display());
                return Err(1);
            }
        };
        let rel = relative_under_paths(file, &args.paths)
            .unwrap_or_else(|| file.file_name().unwrap_or_default().to_string_lossy().into_owned());
        user_sources.push((rel, content));
    }

    // git mode: pairing is enforced by clap's `requires` (see BundleArgs).
    // path mode: auto-locate the workspace via env var or by walking up.
    let (stdlib_dir, anthill_core_dep) = match (&args.git_url, &args.git_rev) {
        (Some(url), Some(rev)) => {
            let stdlib_dir = match locate_stdlib_dir() {
                Some(d) => d,
                None => {
                    eprintln!("error: cannot locate stdlib relative to this binary");
                    return Err(1);
                }
            };
            (stdlib_dir, anthill_rust_gen::CoreDep::Git { url: url.clone(), rev: rev.clone() })
        }
        _ => {
            let (stdlib_dir, core_path) = match locate_workspace_paths() {
                Some(t) => t,
                None => {
                    eprintln!("error: cannot locate stdlib or anthill-core relative to this binary");
                    return Err(1);
                }
            };
            (stdlib_dir, anthill_rust_gen::CoreDep::Path(core_path))
        }
    };

    let opts = anthill_rust_gen::BundleOptions {
        project_name: args.project_name.clone(),
        description: args.description.clone(),
        entry_qname: args.entry.clone(),
        user_sources,
        stdlib_dir,
        anthill_core_dep,
    };

    if let Err(e) = anthill_rust_gen::generate_bundle(&opts, &args.output_dir) {
        eprintln!("error: {e}");
        return Err(1);
    }
    println!("bundle written to {}", args.output_dir.display());
    Ok(())
}

/// Compute the path to display inside the bundle for `file`. If `file`
/// lives under one of the user-supplied input directories in `paths`,
/// the returned name is relative to that directory; else None.
fn relative_under_paths(file: &Path, paths: &[PathBuf]) -> Option<String> {
    for p in paths {
        if p.is_dir() {
            if let Ok(stripped) = file.strip_prefix(p) {
                return Some(stripped.to_string_lossy().into_owned());
            }
        }
    }
    None
}

/// Locate the stdlib/anthill directory only (used by git-mode bundling,
/// where anthill-core is referenced via git rather than a local path).
fn locate_stdlib_dir() -> Option<PathBuf> {
    locate_workspace_paths().map(|(stdlib, _)| stdlib)
}

/// Locate the stdlib/anthill and anthill-core paths in the running workspace.
/// First tries env var ANTHILL_WORKSPACE_ROOT; else walks parents of the
/// running binary looking for a `stdlib/anthill` directory.
fn locate_workspace_paths() -> Option<(PathBuf, PathBuf)> {
    if let Ok(root) = std::env::var("ANTHILL_WORKSPACE_ROOT") {
        let root = PathBuf::from(root);
        let stdlib = root.join("stdlib/anthill");
        let core = root.join("rustland/anthill-core");
        if stdlib.is_dir() && core.is_dir() { return Some((stdlib, core)); }
    }
    let exe = std::env::current_exe().ok()?;
    let mut dir = exe.parent()?.to_path_buf();
    for _ in 0..6 {
        let stdlib = dir.join("stdlib/anthill");
        let core = dir.join("rustland/anthill-core");
        if stdlib.is_dir() && core.is_dir() {
            return Some((stdlib, core));
        }
        if !dir.pop() { break; }
    }
    None
}

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

// ── C++ codegen command ─────────────────────────────────────────────

/// WI-089(a): the compilation profile to emit `namespace` under, read from the
/// `Generated` facts at or under it (`source == namespace`, or — since a
/// controller's `source` is its fully-qualified sort name — any `source` under
/// `namespace.`). One emitted header carries one profile, so the cpp `Generated`
/// facts in scope are expected to agree; we take their single distinct profile.
/// `None` when nothing is declared (language base only). If facts genuinely
/// disagree we take the lexicographically-first profile deterministically rather
/// than guess by fact order — a multi-profile namespace is a project smell the
/// per-controller project-layout path handles instead.
fn profile_for_namespace(kb: &KnowledgeBase, namespace: &str) -> Option<String> {
    let ns_prefix = format!("{namespace}.");
    let mut profiles: Vec<String> = anthill_cpp_gen::generated_targets(kb)
        .into_iter()
        .filter(|t| t.language == "cpp")
        .filter(|t| t.source == namespace || t.source.starts_with(&ns_prefix))
        .filter_map(|t| t.profile)
        .collect();
    profiles.sort();
    profiles.dedup();
    profiles.into_iter().next()
}

fn run_codegen_cpp(args: &CppCodegenArgs) -> Result<(), i32> {
    let kb = load_kb_with_stdlib(&args.paths, false, true)?;

    // WI-089(a): the active compilation profile selects profile-keyed
    // TypeMapping / EffectMapping overlays. Read it from the namespace's
    // `Generated` fact (the spec-side declaration of what to emit); None when
    // nothing is declared, in which case only the language base applies.
    let profile = profile_for_namespace(&kb, &args.namespace);

    let header = anthill_cpp_gen::emit_namespace_header_with_profile(&kb, &args.namespace, profile.clone())
        .map_err(|e| {
            eprintln!("error: {}", e.message);
            1
        })?;

    let short = args.namespace.rsplit('.').next().unwrap_or(&args.namespace);
    let header_filename = format!("{short}.hpp");

    if args.dry_run {
        println!("[dry-run] {} -> {}/{}",
            args.namespace,
            args.output_dir.display(),
            header_filename);
        return Ok(());
    }

    if let Err(e) = fs::create_dir_all(&args.output_dir) {
        eprintln!("error: cannot create output dir {}: {e}", args.output_dir.display());
        return Err(1);
    }

    let header_path = args.output_dir.join(&header_filename);
    if let Err(e) = fs::write(&header_path, &header) {
        eprintln!("error: write {}: {e}", header_path.display());
        return Err(1);
    }
    println!("{} -> {}", args.namespace, header_path.display());

    let runtime_path = args.output_dir.join("anthill_runtime.hpp");
    if let Err(e) = fs::write(&runtime_path, anthill_cpp_gen::emit_runtime_header()) {
        eprintln!("error: write {}: {e}", runtime_path.display());
        return Err(1);
    }
    println!("anthill_runtime.hpp -> {}", runtime_path.display());

    // anthill::geometry only emits if the namespace declared anything
    // there; ignore the error when the namespace is empty (carrier-
    // only / unrelated namespace).
    if let Ok(geometry_header) = anthill_cpp_gen::emit_namespace_header_with_profile(&kb, "anthill.geometry", profile) {
        let geometry_path = args.output_dir.join("anthill_geometry.hpp");
        if let Err(e) = fs::write(&geometry_path, &geometry_header) {
            eprintln!("error: write {}: {e}", geometry_path.display());
            return Err(1);
        }
        println!("anthill.geometry -> {}", geometry_path.display());
    }

    Ok(())
}

// ── C++ project layout command ──────────────────────────────────────

fn run_codegen_cpp_project(args: &CppProjectArgs) -> Result<(), i32> {
    let kb = load_kb_with_stdlib(&args.paths, false, true)?;

    // Source of truth: `fact Generated(kind: "controller", language: "cpp", ...)`
    // entries scoped to the requested namespace. Each fact names one
    // controller binary and provides its profile / artifact path.
    // When no facts are declared, fall back to "every traits class
    // under the namespace becomes a controller" — keeps the existing
    // CLI flow working until projects opt into spec-declared
    // generation.
    let ns_prefix = format!("{}.", args.namespace);
    let declared: Vec<anthill_cpp_gen::GeneratedTarget> = anthill_cpp_gen::generated_targets(&kb)
        .into_iter()
        .filter(|t| t.language == "cpp")
        .filter(|t| t.kind == "controller")
        .filter(|t| t.source == args.namespace || t.source.starts_with(&ns_prefix))
        .collect();
    let controllers: Vec<String> = if declared.is_empty() {
        anthill_cpp_gen::traits_classes_in_namespace(&kb, &args.namespace)
    } else {
        declared.iter()
            .map(|t| t.source.rsplit('.').next().unwrap_or(&t.source).to_string())
            .collect()
    };
    if controllers.is_empty() {
        eprintln!(
            "error: namespace '{}' has no `fact Generated(kind: \"controller\")` \
             declarations and no traits classes to fall back on — \
             nothing to scaffold",
            args.namespace
        );
        return Err(1);
    }

    // WI-089(a): the profile that selects profile-keyed overlays — the single
    // distinct profile of the `Generated` facts at/under this namespace. Same
    // helper as `run_codegen_cpp` so both entry points agree. None on the
    // traits-class fallback (no Generated facts declared).
    let profile = profile_for_namespace(&kb, &args.namespace);
    let header = anthill_cpp_gen::emit_namespace_header_with_profile(&kb, &args.namespace, profile.clone())
        .map_err(|e| { eprintln!("error: {}", e.message); 1 })?;
    let geometry = anthill_cpp_gen::emit_namespace_header_with_profile(&kb, "anthill.geometry", profile).ok();
    let runtime = anthill_cpp_gen::emit_runtime_header();

    let cpp_files = match list_cpp_sources(&args.cpp_sources) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("error: scanning cpp sources at {}: {e}",
                args.cpp_sources.display());
            return Err(1);
        }
    };

    let ns_short = args.namespace.rsplit('.').next().unwrap_or(&args.namespace);
    let header_filename = format!("{ns_short}.hpp");

    for ctor_name in &controllers {
        let dir = args.output_dir.join("controllers").join(ctor_name);
        if args.dry_run {
            println!("[dry-run] would scaffold controller '{ctor_name}' under {}",
                dir.display());
            continue;
        }
        if let Err(e) = fs::create_dir_all(&dir) {
            eprintln!("error: mkdir {}: {e}", dir.display());
            return Err(1);
        }

        // Generated headers — same content per controller, copies are
        // intentional (Webots wants self-contained controller dirs).
        let mut wrote: Vec<String> = Vec::new();
        write_or_err(&dir.join(&header_filename), &header, &mut wrote)?;
        write_or_err(&dir.join("anthill_runtime.hpp"), runtime, &mut wrote)?;
        if let Some(g) = &geometry {
            write_or_err(&dir.join("anthill_geometry.hpp"), g, &mut wrote)?;
        }

        // Hand-authored sources copied verbatim. A file named
        // `<OtherCtor>.cpp`, `<OtherCtor>_main.cpp`, or `<OtherCtor>.hpp`
        // belongs to a different controller and is skipped — only
        // shared helpers (mavic_base.{cpp,hpp}, etc.) and this
        // controller's own `<ctor_name>{,_main}.{cpp,hpp}` are
        // copied. Filename-based, so renaming a source moves it to a
        // different bucket.
        for src in &cpp_files {
            let fname = match src.file_name().and_then(|s| s.to_str()) {
                Some(f) => f,
                None => continue,
            };
            if !file_belongs_to_controller(fname, ctor_name, &controllers) {
                continue;
            }
            let dst = dir.join(fname);
            if let Err(e) = fs::copy(src, &dst) {
                eprintln!("error: copy {} → {}: {e}", src.display(), dst.display());
                return Err(1);
            }
            wrote.push(fname.to_string());
        }

        // Per-controller Makefile. Compiles every .cpp in the dir
        // and links them against the Webots controller library.
        let makefile = render_controller_makefile(ctor_name);
        write_or_err(&dir.join("Makefile"), &makefile, &mut wrote)?;

        println!("scaffolded {} ({} files)", dir.display(), wrote.len());
    }

    // Copy world files (`.wbt` + any sibling textures / protos) into
    // `<output>/worlds/`. Webots opens the .wbt as the entry point,
    // so without this step the scaffolded project has nowhere to
    // launch the controllers from.
    if !args.dry_run && args.worlds_dir.exists() {
        let worlds_dst = args.output_dir.join("worlds");
        if let Err(e) = fs::create_dir_all(&worlds_dst) {
            eprintln!("error: mkdir {}: {e}", worlds_dst.display());
            return Err(1);
        }
        let world_files = match list_world_files(&args.worlds_dir) {
            Ok(v) => v,
            Err(e) => {
                eprintln!("error: scanning worlds at {}: {e}", args.worlds_dir.display());
                return Err(1);
            }
        };
        for src in &world_files {
            let Some(fname) = src.file_name() else { continue };
            let dst = worlds_dst.join(fname);
            if let Err(e) = fs::copy(src, &dst) {
                eprintln!("error: copy {} → {}: {e}", src.display(), dst.display());
                return Err(1);
            }
        }
        if !world_files.is_empty() {
            println!("copied {} world file(s) → {}",
                world_files.len(), worlds_dst.display());
        }
    }

    Ok(())
}

fn list_world_files(dir: &Path) -> Result<Vec<PathBuf>, std::io::Error> {
    let mut out = Vec::new();
    if !dir.exists() {
        return Ok(out);
    }
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if !path.is_file() { continue; }
        let ext = path.extension().and_then(|s| s.to_str()).unwrap_or("");
        if matches!(ext, "wbt" | "proto" | "wbproj") {
            out.push(path);
        }
    }
    out.sort();
    Ok(out)
}

/// Decide whether `fname` should be copied into `current_ctor`'s
/// folder. Files whose stem starts with a *different* controller's
/// name (e.g. `LeaderController_main.cpp` when current is
/// `FollowerController`) are filtered out. Everything else — shared
/// helpers, the current controller's own files — is kept.
fn file_belongs_to_controller(fname: &str, current_ctor: &str, controllers: &[String]) -> bool {
    let stem = fname.rsplit_once('.').map(|(s, _)| s).unwrap_or(fname);
    for other in controllers {
        if other == current_ctor { continue; }
        if stem == other.as_str() { return false; }
        if let Some(rest) = stem.strip_prefix(other.as_str()) {
            // Match `<other>_main`, `<other>_impl`, etc. Don't match
            // `LeaderController_helper` against `Leader` (require a
            // separator after the prefix).
            if rest.starts_with('_') || rest.is_empty() { return false; }
        }
    }
    true
}

fn list_cpp_sources(dir: &Path) -> Result<Vec<PathBuf>, std::io::Error> {
    let mut out = Vec::new();
    if !dir.exists() {
        return Ok(out);
    }
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if !path.is_file() { continue; }
        let ext = path.extension().and_then(|s| s.to_str()).unwrap_or("");
        if matches!(ext, "cpp" | "hpp" | "h" | "cc" | "cxx" | "hh") {
            out.push(path);
        }
    }
    out.sort();
    Ok(out)
}

fn write_or_err(path: &Path, contents: &str, wrote: &mut Vec<String>) -> Result<(), i32> {
    if let Err(e) = fs::write(path, contents) {
        eprintln!("error: write {}: {e}", path.display());
        return Err(1);
    }
    if let Some(name) = path.file_name() {
        wrote.push(name.to_string_lossy().to_string());
    }
    Ok(())
}

/// v0 Makefile for a Webots C++ controller. Mirrors the standard
/// `controllers/<name>/Makefile` shape Cyberbotics ships: pulls in
/// `$(WEBOTS_HOME)/resources/Makefile.include` which fills in
/// CFLAGS / LFLAGS / the libController link. We just declare the
/// target name + list every .cpp in the directory as a source.
fn render_controller_makefile(controller: &str) -> String {
    format!(
        r#"# Generated by anthill — controller scaffold.
# Compiles every .cpp in this directory against the Webots
# controller library. Re-run `anthill codegen cpp-project ...` to
# refresh generated headers when the .anthill specs change.
#
# Layout follows the Cyberbotics convention: include
# `Makefile.os.include` first, then declare sources, then include
# `Makefile.include`, *then* extend CFLAGS — `Makefile.include`
# resets CFLAGS, so std/warning flags must come after.

null :=
space := $(null) $(null)
WEBOTS_HOME_PATH ?= $(subst $(space),\ ,$(strip $(subst \,/,$(WEBOTS_HOME))))

ifndef WEBOTS_HOME
$(error set WEBOTS_HOME to your Webots install)
endif

include $(WEBOTS_HOME_PATH)/resources/Makefile.os.include

CXX_SOURCES = $(wildcard *.cpp)
TARGET = {controller}

include $(WEBOTS_HOME_PATH)/resources/Makefile.include

CFLAGS += -std=c++20 -Wall -Wextra
"#,
    )
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
            let results = kb.rules_by_functor(sym);
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
                            // Interactive query: keep residual solutions so
                            // `print_solutions` can DISPLAY the `residual:` line
                            // (floundered goals) rather than hide them (WI-519).
                            definite_only: false,
                            // `gamma` (WI-537 Γ overlay) defaults to None; `..Default`
                            // fills it without naming that crate-private type here.
                            ..Default::default()
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
    let mut kb = load_kb_with_stdlib(&args.paths, false, true)?;
    println!("loaded: {} facts, {} rules", kb.fact_count(), kb.rule_count());
    let opts = check::CheckOpts {
        shallow: args.shallow,
        report_stale_only: args.report_stale,
        report_trust_only: args.report_trust,
        filters: args.filter.clone(),
    };
    // Existing β.1 pass: replay recorded witnesses (drift / tamper detection).
    let outcomes = check::run_check_with(&args.paths, &kb, &args.solver, None, &opts)?;
    let failed = check::print_summary(&outcomes);

    // WI-564 — chain the discharge pass (local-proof.md OQ-A): `load → type`
    // already ran (`load_all`), so now `discharge-pending` flips every
    // `ProofRecord` to Discharged | Failed via the SAME both-tier dispatch
    // `anthill prove` uses. A green `check` then MEANS "verified", with no
    // separate prove step. Filters/report-only modes leave proofs alone — they
    // are inspection queries, not a full verification run.
    if !args.report_stale && !args.report_trust && args.filter.is_empty() {
        let prove_args = prove_args_for_check(args);
        let report = prove::discharge_loaded_kb(&mut kb, &prove_args, false);
        let unverified = report.unverified();
        if unverified > 0 {
            // OQ-B — degrade, don't silently trust: warn by default; the strict
            // `--require-proofs` flag escalates to an error for airtight CI.
            eprintln!(
                "warning: relied on {unverified} unverified proof(s); not fully verified \
                 (re-run with --require-proofs to make this an error)"
            );
            if args.require_proofs {
                eprintln!(
                    "error: --require-proofs: {unverified} proof obligation(s) not verified"
                );
                return Err(1);
            }
        }
    }

    if failed > 0 { Err(1) } else { Ok(()) }
}

/// WI-564: build the `prove` parameters for the discharge pass chained into
/// `check` — same source paths and solver, all-proofs (no `--rule` filter), and
/// the default cache behaviour (reuse the proof cache; the `Γ`-snapshot staleness
/// key keeps a chained discharge fast). The standalone `anthill prove` flags
/// (`--show-cache`, `--gc-cache`, `--stats`, `--dry-run`, …) do not apply here.
fn prove_args_for_check(args: &CheckArgs) -> ProveArgs {
    ProveArgs {
        paths: args.paths.clone(),
        rule: None,
        solver: args.solver.clone(),
        dry_run: false,
        verbose: false,
        no_cache: false,
        refresh_cache: false,
        show_cache: false,
        cache_dir: None,
        gc_cache: None,
        stats: false,
    }
}

// ── Display helpers ─────────────────────────────────────────────────

/// Render a carrier-agnostic `Value` for display (WI-348). A fact head or a
/// query binding may be a `Value::Term` (hash-consed), a `Value::Node`
/// (occurrence — e.g. a `denoted` effect on an `OperationInfo` value fact), or
/// a structural `Value::Entity`/`Tuple`. Reading it "as a term" (`rule_head`, or
/// narrowing a binding to `Value::Term`) panics on a value head and drops `Node`
/// bindings, so the query output reads the `Value` and renders each carrier here.
fn render_value(
    printer: &TermPrinter<'_, KnowledgeBase>,
    kb: &KnowledgeBase,
    v: &anthill_core::eval::Value,
) -> String {
    use anthill_core::eval::Value;
    match v {
        Value::Term { id: t, .. } => printer.print_term(*t),
        Value::Node(occ) => printer.print_occurrence(occ),
        Value::Int(n) => n.to_string(),
        Value::BigInt(n) => n.to_string(),
        Value::Float(f) => f.to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Str(s) => format!("{s:?}"),
        Value::Entity { functor, pos, named, .. } => {
            let mut parts: Vec<String> = pos.iter().map(|c| render_value(printer, kb, c)).collect();
            parts.extend(named.iter().map(|(s, c)| {
                format!("{}: {}", kb.resolve_sym(*s), render_value(printer, kb, c))
            }));
            format!("{}({})", kb.resolve_sym(*functor), parts.join(", "))
        }
        Value::Tuple { pos, named, .. } => {
            let mut parts: Vec<String> = pos.iter().map(|c| render_value(printer, kb, c)).collect();
            parts.extend(named.iter().map(|(s, c)| {
                format!("{}: {}", kb.resolve_sym(*s), render_value(printer, kb, c))
            }));
            format!("({})", parts.join(", "))
        }
        other => format!("{other:?}"),
    }
}

fn print_rule_results(kb: &KnowledgeBase, results: &[RuleId], max: usize) {
    let printer = TermPrinter::new(kb);
    let limit = if max == 0 { results.len() } else { max.min(results.len()) };

    for &rid in &results[..limit] {
        // WI-348: a head may be a value fact (Node-carrying); read it as a Value.
        let head = render_value(&printer, kb, kb.rule_head_value(rid));
        // Facts have no body; rule body atoms are occurrences (WI-246).
        let body = kb.rule_body_nodes(rid);
        if body.is_empty() {
            println!("  {head}");
        } else {
            let body_strs: Vec<String> =
                body.iter().map(|atom| printer.print_occurrence(atom)).collect();
            println!("  {} :- {}", head, body_strs.join(", "));
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
        // WI-348: read the head as a Value (may be a Node-carrying value fact).
        print!("  {}", render_value(&printer, kb, kb.rule_head_value(*rid)));
        // Print bindings if any — carrier-agnostic (a binding may be a Node).
        let bindings: Vec<String> = subst
            .iter()
            .map(|(vid, val)| {
                format!("?{} = {}", kb.resolve_sym(vid.name()), render_value(&printer, kb, val))
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
                // WI-348: read the binding as a Value — narrowing it to a term
                // would drop a `Value::Node` binding (e.g. a `denoted` effect label).
                sol.subst.resolve_as_value(*vid).map(|val| {
                    format!("?{} = {}", kb.resolve_sym(vid.name()), render_value(&printer, kb, val))
                })
            })
            .collect();
        if bindings.is_empty() {
            println!("  true");
        } else {
            println!("  {}", bindings.join(", "));
        }
        if !sol.residual.is_empty() {
            // WI-348: residual goals are carrier-agnostic `Value`s — render each
            // carrier (a delayed goal may mention a `Value::Node`).
            let residuals: Vec<String> =
                sol.residual.iter().map(|v| render_value(&printer, kb, v)).collect();
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
            CodegenTarget::Cpp(ref args) => run_codegen_cpp(args),
            CodegenTarget::CppProject(ref args) => run_codegen_cpp_project(args),
            CodegenTarget::Bundle(ref args) => run_codegen_bundle(args),
        },
        Command::Load(ref args) => run_load(args),
        Command::Query(ref args) => run_query(args),
        Command::Check(ref args) => run_check(args),
        Command::Run(ref args) => return ExitCode::from(run::run(args) as u8),
        Command::Prove(ref args) => prove::run_prove(args),
    };

    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(_) => ExitCode::FAILURE,
    }
}
