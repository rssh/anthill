use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand};

use anthill_core::kb::load::{self, FileSourceResolver};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId, Var};
use anthill_core::kb::{KnowledgeBase, RuleId};
use anthill_core::parse;
use anthill_core::parse::ir::ParsedFile;
use anthill_core::persistence::print::TermPrinter;
use anthill_core::persistence::term_ser;

use smallvec::SmallVec;

mod stdlib_embedded;
mod anthill_bundle;

static SKILL_MD: &str = r#"---
name: anthill-todo
description: Manage project work items (add, list, show, claim, deliver) using the anthill-todo CLI. Works in any project directory.
user-invocable: true
allowed-tools:
  - Bash
  - Read
  - Edit
---

# anthill-todo

Manage structured work items for any project using the `anthill-todo` CLI.

## Usage

Always pass `-d` with the current working directory so work items go to the correct project:

```bash
anthill-todo -d "$PWD" $ARGS
```

When invoked as `/anthill-todo`, run the CLI with the user's arguments. If no arguments, show the list.

If the project has no `anthill-todo/` directory yet, run `init` first.

## Commands

```bash
anthill-todo -d "$PWD" list                              # List all work items
anthill-todo -d "$PWD" add "description" [--depends WI-NNN]  # Add a new work item
anthill-todo -d "$PWD" show WI-NNN                       # Show details
anthill-todo -d "$PWD" next                              # Show next claimable item
anthill-todo -d "$PWD" --agent claude claim WI-NNN       # Claim a work item
anthill-todo -d "$PWD" --agent claude deliver WI-NNN     # Mark as delivered
anthill-todo -d "$PWD" feedback WI-NNN "feedback text"   # Add feedback
anthill-todo -d "$PWD" status                            # Show status counts
anthill-todo -d "$PWD" graph                             # Show dependency graph
anthill-todo -d "$PWD" init                              # Initialize anthill-todo/ in project
```
"#;

// ── CLI types ───────────────────────────────────────────────────

#[derive(Parser)]
#[command(name = "anthill-todo", about = "Structured work management powered by anthill")]
struct Cli {
    /// Project directory (default: look for anthill-todo/ in current dir, then current dir itself)
    #[arg(short = 'd', long = "dir")]
    project_dir: Option<PathBuf>,

    /// Use stdlib from disk instead of embedded (for development)
    #[arg(long = "stdlib")]
    stdlib_path: Option<PathBuf>,

    /// Agent name for claim/deliver/feedback
    #[arg(long, default_value = "user")]
    agent: String,

    #[command(subcommand)]
    command: TodoCommand,
}

#[derive(Subcommand)]
enum TodoCommand {
    /// Initialize a new anthill-todo project in the current directory
    Init {
        /// Project name (default: current directory name)
        #[arg(long)]
        name: Option<String>,
    },
    /// Add a new work item
    Add {
        /// Description of the work item
        description: String,
        /// Dependencies (other work item IDs)
        #[arg(long = "depends")]
        depends_on: Vec<String>,
        /// Acceptance criteria: tool names (e.g. cargo-test)
        #[arg(long = "acceptance")]
        acceptance: Vec<String>,
    },
    /// Show work item counts by status
    Status,
    /// List work items (hides delivered/verified by default)
    List {
        /// Filter by status (e.g. open, claimed, verified)
        #[arg(long)]
        status: Option<String>,
        /// Show all items including delivered/verified
        #[arg(long)]
        all: bool,
    },
    /// Show next claimable work item
    Next {
        /// Show all claimable items
        #[arg(long)]
        all: bool,
    },
    /// Show details of a work item
    Show {
        /// Work item ID
        id: String,
    },
    /// Claim a work item
    Claim {
        /// Work item ID
        id: String,
    },
    /// Mark a work item as delivered
    Deliver {
        /// Work item ID
        id: String,
    },
    /// Mark a delivered work item as verified
    Verify {
        /// Work item ID
        id: String,
    },
    /// Add feedback to a work item
    Feedback {
        /// Work item ID
        id: String,
        /// Feedback text
        text: String,
    },
    /// Delete a work item
    Delete {
        /// Work item ID
        id: String,
    },
    /// Update fields of a work item in place (preserves id, depends_on, status)
    Update {
        /// Work item ID
        id: String,
        /// New description
        #[arg(long)]
        description: Option<String>,
        /// Replace acceptance criteria with the given tool names (e.g. cargo-test).
        /// Pass `--acceptance` multiple times for multiple criteria.
        #[arg(long = "acceptance")]
        acceptance: Vec<String>,
    },
    /// Add a dependency to a work item
    AddDependency {
        /// Work item ID
        id: String,
        /// Dependency work item ID
        dependency: String,
    },
    /// Remove a dependency from a work item
    RemoveDependency {
        /// Work item ID
        id: String,
        /// Dependency work item ID to remove
        dependency: String,
    },
    /// Show dependency graph
    Graph,
    /// Print Claude Code skill definition to stdout
    Skill,
}

// ── File collection ─────────────────────────────────────────────

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
        } else if path.extension().and_then(|e| e.to_str()).map_or(false, |e| extensions.contains(&e)) {
            out.push(path);
        }
    }
}

fn collect_anthill_files(paths: &[PathBuf]) -> Vec<PathBuf> {
    let mut files = Vec::new();
    for path in paths {
        if !path.exists() { continue; }
        if path.is_dir() {
            collect_files_recursive(path, &mut files, &["anthill"]);
        } else if path.extension().and_then(|e| e.to_str()) == Some("anthill") {
            files.push(path.clone());
        }
    }
    files.sort();
    files.dedup();
    files
}

fn collect_data_files(paths: &[PathBuf]) -> Vec<PathBuf> {
    let mut files = Vec::new();
    for path in paths {
        if !path.exists() { continue; }
        if path.is_dir() {
            collect_files_recursive(path, &mut files, &["toml", "json"]);
        } else {
            let ext = path.extension().and_then(|e| e.to_str());
            if ext == Some("toml") || ext == Some("json") {
                files.push(path.clone());
            }
        }
    }
    files.sort();
    files.dedup();
    files
}

// ── Project directory discovery ──────────────────────────────────

/// Find the project directory. Checks:
/// 1. Explicit --dir flag
/// 2. `anthill-todo/` subdirectory of current dir
/// 3. Current directory itself (if it contains .anthill files)
fn find_project_dir(explicit: Option<&Path>) -> Result<PathBuf, String> {
    if let Some(dir) = explicit {
        if dir.is_dir() {
            return Ok(dir.to_path_buf());
        }
        return Err(format!("project directory does not exist: {}", dir.display()));
    }

    let cwd = std::env::current_dir()
        .map_err(|e| format!("cannot determine current directory: {e}"))?;

    let subdir = cwd.join("anthill-todo");
    if subdir.is_dir() {
        eprintln!("warning: no -d flag specified, using current directory: {}", cwd.display());
        return Ok(cwd);
    }

    // Maybe we're already inside an anthill-todo dir
    let has_anthill = cwd.read_dir()
        .map(|entries| entries.flatten().any(|e| {
            e.path().extension().map_or(false, |ext| ext == "anthill")
        }))
        .unwrap_or(false);
    if has_anthill {
        eprintln!("warning: no -d flag specified, using current directory: {}", cwd.display());
        return Ok(cwd);
    }

    Err("no anthill-todo/ directory found.\n  Run `anthill-todo init` or use -d <project-dir>.".into())
}

/// Determine the directory to scan for workitem files.
/// If the project dir has an anthill-todo/ subdirectory, scan only there.
/// Otherwise scan the project dir itself.
fn scan_dir(project_dir: &Path) -> PathBuf {
    let subdir = project_dir.join("anthill-todo");
    if subdir.is_dir() {
        subdir
    } else {
        project_dir.to_path_buf()
    }
}

// ── KB loading ──────────────────────────────────────────────────

/// Headerless project files — bare `fact …(…)` lists such as
/// `workitems.anthill` — parse with their items at the top level, which the
/// loader places in the `_global` scope where stage0 entity names like
/// `WorkItem` are not visible. The file store owns the knowledge that these
/// facts belong to the `anthill.stage0` domain, so it wraps such files in a
/// synthetic `namespace anthill.stage0` block. That reuses the scope the
/// project's `domain.anthill` set up (entity definitions + prelude imports),
/// so the bare functor and its constructor variants resolve lexically. Files
/// that already declare a namespace are left untouched.
fn assign_default_namespace(pf: &mut ParsedFile) {
    use anthill_core::parse::ir::{Item, Name, Namespace};
    use anthill_core::span::Span;

    if pf.items.is_empty() || pf.items.iter().any(|i| matches!(i, Item::Namespace(_))) {
        return;
    }
    let mut segments: SmallVec<[anthill_core::intern::Symbol; 2]> = SmallVec::new();
    segments.push(pf.symbols.intern("anthill"));
    segments.push(pf.symbols.intern("stage0"));
    let name = Name { segments, span: Span::default() };
    let items = std::mem::take(&mut pf.items);
    pf.items.push(Item::Namespace(Namespace {
        name,
        imports: Vec::new(),
        exports: Vec::new(),
        items,
        span: Span::default(),
    }));
}

fn load_kb(project_dir: &Path, stdlib_path: Option<&Path>) -> Result<KnowledgeBase, String> {
    // WI-233: phase timings, gated by ANTHILL_TODO_TIMING=1. Lets a
    // user see which phase of `load_kb` dominates the wall time.
    let timing = std::env::var("ANTHILL_TODO_TIMING").map(|v| v == "1").unwrap_or(false);
    let t_start = std::time::Instant::now();
    let mut t_phase = t_start;
    let mark = |label: &str, prev: &mut std::time::Instant| {
        if timing {
            let now = std::time::Instant::now();
            eprintln!("[timing] {label}: {:?}", now.duration_since(*prev));
            *prev = now;
        }
    };

    // Phase 1: Parse stdlib (embedded or from disk)
    let mut stdlib_parsed: Vec<ParsedFile> = Vec::new();

    if let Some(stdlib_dir) = stdlib_path {
        let stdlib_files = collect_anthill_files(&[stdlib_dir.to_path_buf()]);
        for file in &stdlib_files {
            let source = fs::read_to_string(file)
                .map_err(|e| format!("{}: {e}", file.display()))?;
            match parse::parse(&source) {
                Ok(p) => stdlib_parsed.push(p),
                Err(errs) => {
                    for e in &errs {
                        eprintln!("warning: {}: {e}", file.display());
                    }
                }
            }
        }
    } else {
        let (embedded, stdlib_errors) = stdlib_embedded::parse_embedded_stdlib();
        stdlib_parsed.extend(embedded);
        for e in &stdlib_errors {
            eprintln!("warning: {e}");
        }
    }
    mark(&format!("parse stdlib ({} files)", stdlib_parsed.len()), &mut t_phase);

    // Phase 2: Parse project files (only from anthill-todo/ subdir, not whole project)
    let scan = scan_dir(project_dir);
    let project_files = collect_anthill_files(&[scan.clone()]);
    let mut domain_parsed: Vec<ParsedFile> = Vec::new();
    for file in &project_files {
        let source = fs::read_to_string(file)
            .map_err(|e| format!("{}: {e}", file.display()))?;
        match parse::parse(&source) {
            Ok(mut p) => {
                assign_default_namespace(&mut p);
                domain_parsed.push(p);
            }
            Err(errs) => {
                for e in &errs {
                    eprintln!("warning: {}:{}", file.display(), e.format_with_source(&source));
                }
            }
        }
    }
    mark(&format!("parse project ({} files)", domain_parsed.len()), &mut t_phase);

    if stdlib_parsed.is_empty() && domain_parsed.is_empty() {
        return Err("no .anthill files found".into());
    }

    let mut kb = KnowledgeBase::new();

    let base_dirs: Vec<PathBuf> = project_dir.parent()
        .map(|p| vec![p.to_path_buf()])
        .unwrap_or_default();
    let resolver = FileSourceResolver::new(base_dirs);

    let stdlib_refs: Vec<&ParsedFile> = stdlib_parsed.iter().collect();
    if let Err(errs) = load::load_stdlib(&mut kb, &stdlib_refs, &resolver) {
        for e in &errs {
            eprintln!("warning: {e}");
        }
    }
    mark("load_stdlib (scan + load + typecheck + req_insertion)", &mut t_phase);

    let domain_refs: Vec<&ParsedFile> = domain_parsed.iter().collect();
    if let Err(errs) = load::load_incremental(&mut kb, &domain_refs, &resolver) {
        for e in &errs {
            eprintln!("warning: {e}");
        }
    }
    mark("load_incremental (project)", &mut t_phase);

    // Load .toml/.json data files (only from scan dir, not whole project)
    let data_files = collect_data_files(&[scan]);
    if !data_files.is_empty() {
        let domain = kb.make_name_term("_data");
        for file in &data_files {
            let source = match fs::read_to_string(file) {
                Ok(s) => s,
                Err(e) => { eprintln!("warning: {}: {e}", file.display()); continue; }
            };
            let ext = file.extension().and_then(|e| e.to_str()).unwrap_or("");
            let result = match ext {
                "toml" => term_ser::load_toml(&mut kb, &source, domain),
                "json" => term_ser::load_json(&mut kb, &source, domain),
                _ => continue,
            };
            if let Err(errs) = result {
                for e in &errs { eprintln!("warning: {}: {e}", file.display()); }
            }
        }
    }
    mark("load data files (toml/json)", &mut t_phase);
    if timing {
        eprintln!("[timing] TOTAL: {:?}", t_start.elapsed());
    }

    Ok(kb)
}

// ── Term helpers ────────────────────────────────────────────────

fn extract_named_arg(kb: &KnowledgeBase, term: TermId, field: &str) -> Option<TermId> {
    match kb.get_term(term) {
        Term::Fn { named_args, .. } => {
            named_args.iter()
                .find(|(s, _)| kb.resolve_sym(*s) == field)
                .map(|(_, id)| *id)
        }
        _ => None,
    }
}

fn extract_string(kb: &KnowledgeBase, term: TermId) -> Option<String> {
    match kb.get_term(term) {
        Term::Const(Literal::String(s)) => Some(s.clone()),
        _ => None,
    }
}

fn functor_name(kb: &KnowledgeBase, term: TermId) -> Option<String> {
    match kb.get_term(term) {
        Term::Fn { functor, .. } => Some(kb.resolve_sym(*functor).to_string()),
        Term::Ref(sym) => Some(kb.resolve_sym(*sym).to_string()),
        Term::Ident(sym) => Some(kb.resolve_sym(*sym).to_string()),
        _ => None,
    }
}

fn list_to_vec(kb: &KnowledgeBase, mut term: TermId) -> Vec<TermId> {
    let mut items = Vec::new();
    loop {
        match kb.get_term(term) {
            Term::Fn { functor, named_args, .. } => {
                let name = kb.resolve_sym(*functor);
                if name == "nil" { break; }
                if name == "cons" {
                    let named_args = named_args.clone();
                    if let Some((_, h)) = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "head") {
                        items.push(*h);
                    }
                    if let Some((_, t)) = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "tail") {
                        term = *t;
                    } else { break; }
                } else { break; }
            }
            _ => break,
        }
    }
    items
}

fn now_timestamp() -> String {
    chrono::Utc::now().format("%Y-%m-%dT%H:%M:%SZ").to_string()
}

// ── WorkItem accessors ──────────────────────────────────────────

struct WorkItemInfo {
    rule_id: RuleId,
    id: String,
    description: String,
    status: String,
    depends_on: Vec<String>,
}

fn collect_workitems(kb: &KnowledgeBase) -> Vec<WorkItemInfo> {
    let wi_sym = match kb.try_resolve_symbol("anthill.stage0.WorkItem") {
        Some(s) => s,
        None => return Vec::new(),
    };

    let mut items = Vec::new();
    for rid in kb.by_functor(wi_sym) {
        let head = kb.rule_head(rid);
        // Skip entity definition (has no string id)
        let id = match extract_named_arg(kb, head, "id").and_then(|t| extract_string(kb, t)) {
            Some(s) => s,
            None => continue,
        };
        let description = extract_named_arg(kb, head, "description")
            .and_then(|t| extract_string(kb, t))
            .unwrap_or_default();
        let status = extract_named_arg(kb, head, "status")
            .and_then(|t| functor_name(kb, t))
            .unwrap_or_else(|| "?".into());
        let deps = extract_named_arg(kb, head, "depends_on")
            .map(|t| list_to_vec(kb, t).iter()
                .filter_map(|&d| extract_string(kb, d))
                .collect())
            .unwrap_or_default();

        items.push(WorkItemInfo {
            rule_id: rid,
            id,
            description,
            status,
            depends_on: deps,
        });
    }
    items
}

/// Collect the set of work item IDs that have at least one Feedback fact.
fn items_with_feedback(kb: &KnowledgeBase) -> std::collections::HashSet<String> {
    let mut result = std::collections::HashSet::new();
    if let Some(fb_sym) = kb.try_resolve_symbol("anthill.stage0.Feedback") {
        for rid in kb.by_functor(fb_sym) {
            let fh = kb.rule_head(rid);
            if let Some(wi_id) = extract_named_arg(kb, fh, "workitem")
                .and_then(|t| extract_string(kb, t))
            {
                result.insert(wi_id);
            }
        }
    }
    result
}

// ── Command implementations ─────────────────────────────────────

fn run_status(kb: &KnowledgeBase) {
    let items = collect_workitems(kb);
    if items.is_empty() {
        println!("No work items found.");
        return;
    }

    let mut counts: HashMap<String, usize> = HashMap::new();
    for item in &items {
        *counts.entry(item.status.clone()).or_default() += 1;
    }

    let mut entries: Vec<_> = counts.into_iter().collect();
    entries.sort_by(|a, b| a.0.cmp(&b.0));

    println!("{} work item(s):", items.len());
    for (status, count) in entries {
        println!("  {status}: {count}");
    }
}

fn run_list(kb: &KnowledgeBase, status_filter: Option<&str>, show_all: bool) {
    let items = collect_workitems(kb);
    let closed = |s: &str| s == "Delivered" || s == "Verified";
    let filtered: Vec<_> = items.iter()
        .filter(|i| {
            if let Some(f) = status_filter {
                i.status.eq_ignore_ascii_case(f)
            } else if show_all {
                true
            } else {
                !closed(&i.status)
            }
        })
        .collect();

    if filtered.is_empty() {
        println!("No work items found.");
        return;
    }

    // Build dependents count: how many items depend on each item
    let mut dependents: HashMap<String, Vec<String>> = HashMap::new();
    for item in &items {
        for dep in &item.depends_on {
            dependents.entry(dep.clone()).or_default().push(item.id.clone());
        }
    }

    // Count transitive dependents (items transitively unblocked)
    fn count_transitive(id: &str, dependents: &HashMap<String, Vec<String>>, visited: &mut std::collections::HashSet<String>) -> usize {
        if !visited.insert(id.to_string()) { return 0; }
        let direct = dependents.get(id).cloned().unwrap_or_default();
        let mut count = direct.len();
        for dep in &direct {
            count += count_transitive(dep, dependents, visited);
        }
        count
    }

    // Partition: has unmet deps vs ready (no deps or all deps delivered/verified)
    let delivered = |status: &str| status == "Delivered" || status == "Verified";
    let status_map: HashMap<&str, &str> = items.iter().map(|i| (i.id.as_str(), i.status.as_str())).collect();

    let has_unmet_deps = |item: &WorkItemInfo| -> bool {
        item.depends_on.iter().any(|dep| {
            status_map.get(dep.as_str()).map_or(true, |s| !delivered(s))
        })
    };

    let mut ready: Vec<_> = filtered.iter().filter(|i| !has_unmet_deps(i)).collect();
    let mut blocked: Vec<_> = filtered.iter().filter(|i| has_unmet_deps(i)).collect();

    // Sort ready: most transitive dependents first
    ready.sort_by(|a, b| {
        let mut va = std::collections::HashSet::new();
        let mut vb = std::collections::HashSet::new();
        let ca = count_transitive(&a.id, &dependents, &mut va);
        let cb = count_transitive(&b.id, &dependents, &mut vb);
        cb.cmp(&ca).then(a.id.cmp(&b.id))
    });

    // Sort blocked by id
    blocked.sort_by(|a, b| a.id.cmp(&b.id));

    let fb_set = items_with_feedback(kb);

    if !ready.is_empty() {
        for item in &ready {
            let deps_info = if item.depends_on.is_empty() {
                String::new()
            } else {
                format!(" (depends: {})", item.depends_on.join(", "))
            };
            let unblocks = {
                let mut v = std::collections::HashSet::new();
                let c = count_transitive(&item.id, &dependents, &mut v);
                if c > 0 { format!(" [unblocks {c}]") } else { String::new() }
            };
            let fb = if fb_set.contains(&item.id) { " [has feedback]" } else { "" };
            println!("  {} [{}] {}{}{}{}", item.id, item.status, item.description, deps_info, unblocks, fb);
        }
    }

    if !blocked.is_empty() {
        if !ready.is_empty() { println!(); }
        println!("  -- blocked --");
        for item in &blocked {
            let deps = format!(" (depends: {})", item.depends_on.join(", "));
            let fb = if fb_set.contains(&item.id) { " [has feedback]" } else { "" };
            println!("  {} [{}] {}{}{}", item.id, item.status, item.description, deps, fb);
        }
    }

    println!("{} item(s)", filtered.len());
}

fn run_next(kb: &mut KnowledgeBase, show_all: bool) {
    let claimable_sym = match kb.try_resolve_symbol("anthill.stage0.workflow.claimable") {
        Some(s) => s,
        None => {
            eprintln!("error: workflow rules not loaded (missing anthill.stage0.workflow.claimable)");
            return;
        }
    };

    let id_var = { let s = kb.intern("id"); let v = kb.fresh_var(s); kb.alloc(Term::Var(Var::Global(v))) };
    let desc_var = { let s = kb.intern("desc"); let v = kb.fresh_var(s); kb.alloc(Term::Var(Var::Global(v))) };
    let query = kb.alloc(Term::Fn {
        functor: claimable_sym,
        pos_args: SmallVec::from_slice(&[id_var, desc_var]),
        named_args: SmallVec::new(),
    });

    let config = ResolveConfig { max_solutions: if show_all { 1000 } else { 1 }, ..ResolveConfig::default() };
    let solutions = kb.resolve(&[query], &config);

    if solutions.is_empty() {
        println!("No claimable items (all blocked or none open).");
        return;
    }

    let query_vars = kb.collect_vars(query);
    let mut seen = std::collections::HashSet::new();
    for sol in &solutions {
        let id = query_vars.iter()
            .find(|v| kb.resolve_sym(v.name()) == "id")
            .and_then(|v| sol.subst.resolve_with_term(*v))
            .and_then(|t| extract_string(kb, t))
            .unwrap_or_else(|| "?".into());
        if !seen.insert(id.clone()) { continue; }
        let desc = query_vars.iter()
            .find(|v| kb.resolve_sym(v.name()) == "desc")
            .and_then(|v| sol.subst.resolve_with_term(*v))
            .and_then(|t| extract_string(kb, t))
            .unwrap_or_default();
        println!("  {} — {}", id, desc);
    }
}

fn run_show(kb: &KnowledgeBase, id: &str) {
    let items = collect_workitems(kb);
    let item = items.iter().find(|i| i.id == id);
    match item {
        None => eprintln!("error: work item '{id}' not found"),
        Some(wi) => {
            println!("ID:          {}", wi.id);
            println!("Description: {}", wi.description);
            println!("Status:      {}", wi.status);
            if !wi.depends_on.is_empty() {
                println!("Depends on:  {}", wi.depends_on.join(", "));
            }

            // Show full term for detailed fields
            let head = kb.rule_head(wi.rule_id);
            let printer = TermPrinter::new(kb);

            if let Some(ctx) = extract_named_arg(kb, head, "context") {
                let ctx_items = list_to_vec(kb, ctx);
                if !ctx_items.is_empty() {
                    println!("Context:");
                    for c in &ctx_items {
                        println!("  - {}", printer.print_term(*c));
                    }
                }
            }

            if let Some(acc) = extract_named_arg(kb, head, "acceptance") {
                let acc_items = list_to_vec(kb, acc);
                if !acc_items.is_empty() {
                    println!("Acceptance:");
                    for a in &acc_items {
                        println!("  - {}", printer.print_term(*a));
                    }
                }
            }

            // Show feedback
            if let Some(fb_sym) = kb.try_resolve_symbol("anthill.stage0.Feedback") {
                for rid in kb.by_functor(fb_sym) {
                    let fh = kb.rule_head(rid);
                    let fb_wi = extract_named_arg(kb, fh, "workitem")
                        .and_then(|t| extract_string(kb, t));
                    if fb_wi.as_deref() == Some(id) {
                        let author = extract_named_arg(kb, fh, "author")
                            .and_then(|t| extract_string(kb, t))
                            .unwrap_or_else(|| "?".into());
                        let content = extract_named_arg(kb, fh, "content")
                            .and_then(|t| extract_string(kb, t))
                            .unwrap_or_default();
                        println!("Feedback ({author}): {content}");
                    }
                }
            }
        }
    }
}

fn run_claim(kb: &mut KnowledgeBase, id: &str, agent: &str, project_dir: &Path) {
    // Verify claimable
    let claimable_sym = match kb.try_resolve_symbol("anthill.stage0.workflow.claimable") {
        Some(s) => s,
        None => { eprintln!("error: workflow rules not loaded"); return; }
    };

    let id_term = kb.alloc(Term::Const(Literal::String(id.to_string())));
    let desc_var = { let s = kb.intern("desc"); let v = kb.fresh_var(s); kb.alloc(Term::Var(Var::Global(v))) };
    let query = kb.alloc(Term::Fn {
        functor: claimable_sym,
        pos_args: SmallVec::from_slice(&[id_term, desc_var]),
        named_args: SmallVec::new(),
    });
    let config = ResolveConfig { max_solutions: 1, ..ResolveConfig::default() };
    let solutions = kb.resolve(&[query], &config);
    if solutions.is_empty() {
        eprintln!("error: '{id}' is not claimable (not open or dependencies unverified)");
        return;
    }

    // Build Claimed(agent: "...", since: "...")
    let claimed_sym = kb.try_resolve_symbol("anthill.stage0.WorkStatus.Claimed")
        .unwrap_or_else(|| kb.intern("Claimed"));
    let agent_key = kb.intern("agent");
    let since_key = kb.intern("since");
    let agent_val = kb.alloc(Term::Const(Literal::String(agent.to_string())));
    let since_val = kb.alloc(Term::Const(Literal::String(now_timestamp())));
    let mut claimed_args: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> = SmallVec::new();
    claimed_args.push((agent_key, agent_val));
    claimed_args.push((since_key, since_val));
    claimed_args.sort_by_key(|(s, _)| s.index());
    let claimed_term = kb.alloc(Term::Fn {
        functor: claimed_sym,
        pos_args: SmallVec::new(),
        named_args: claimed_args,
    });

    // Find existing WorkItem and rebuild with new status
    let items = collect_workitems(kb);
    let item = match items.iter().find(|i| i.id == id) {
        Some(i) => i,
        None => { eprintln!("error: work item '{id}' not found"); return; }
    };

    let old_head = kb.rule_head(item.rule_id);
    let new_head = replace_named_arg(kb, old_head, "status", claimed_term);

    let sort = kb.rule_sort(item.rule_id);
    let domain = kb.rule_domain(item.rule_id);
    kb.assert_fact(new_head, sort, domain, None);

    let status_text = format!("Claimed(agent: \"{agent}\", since: \"{}\")", now_timestamp());
    match update_status_in_source(project_dir, id, &status_text) {
        Ok(()) => println!("claimed: {id} by {agent}"),
        Err(e) => {
            eprintln!("warning: source update for {id} failed: {e}");
            println!("claimed: {id} by {agent} (in-memory only)");
        }
    }
}

fn run_deliver(kb: &mut KnowledgeBase, id: &str, agent: &str, project_dir: &Path) {
    let items = collect_workitems(kb);
    let item = match items.iter().find(|i| i.id == id) {
        Some(i) => i,
        None => { eprintln!("error: work item '{id}' not found"); return; }
    };
    if item.status != "Claimed" {
        eprintln!("error: '{id}' is not Claimed (status: {})", item.status);
        return;
    }

    let delivered_sym = kb.try_resolve_symbol("anthill.stage0.WorkStatus.Delivered")
        .unwrap_or_else(|| kb.intern("Delivered"));
    let agent_key = kb.intern("agent");
    let at_key = kb.intern("at");
    let agent_val = kb.alloc(Term::Const(Literal::String(agent.to_string())));
    let at_val = kb.alloc(Term::Const(Literal::String(now_timestamp())));
    let mut del_args: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> = SmallVec::new();
    del_args.push((agent_key, agent_val));
    del_args.push((at_key, at_val));
    del_args.sort_by_key(|(s, _)| s.index());
    let del_term = kb.alloc(Term::Fn {
        functor: delivered_sym,
        pos_args: SmallVec::new(),
        named_args: del_args,
    });

    let old_head = kb.rule_head(item.rule_id);
    let new_head = replace_named_arg(kb, old_head, "status", del_term);

    let sort = kb.rule_sort(item.rule_id);
    let domain = kb.rule_domain(item.rule_id);
    kb.assert_fact(new_head, sort, domain, None);

    let status_text = format!("Delivered(agent: \"{agent}\", at: \"{}\")", now_timestamp());
    match update_status_in_source(project_dir, id, &status_text) {
        Ok(()) => println!("delivered: {id} by {agent}"),
        Err(e) => {
            eprintln!("warning: source update for {id} failed: {e}");
            println!("delivered: {id} by {agent} (in-memory only)");
        }
    }
}

fn run_verify(kb: &mut KnowledgeBase, id: &str, project_dir: &Path) {
    let items = collect_workitems(kb);
    let item = match items.iter().find(|i| i.id == id) {
        Some(i) => i,
        None => { eprintln!("error: work item '{id}' not found"); return; }
    };
    if item.status != "Delivered" {
        eprintln!("error: '{id}' is not Delivered (status: {})", item.status);
        return;
    }

    let verified_sym = kb.try_resolve_symbol("anthill.stage0.WorkStatus.Verified")
        .unwrap_or_else(|| kb.intern("Verified"));
    let at_key = kb.intern("at");
    let at_val = kb.alloc(Term::Const(Literal::String(now_timestamp())));
    let mut ver_args: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> = SmallVec::new();
    ver_args.push((at_key, at_val));
    let ver_term = kb.alloc(Term::Fn {
        functor: verified_sym,
        pos_args: SmallVec::new(),
        named_args: ver_args,
    });

    let old_head = kb.rule_head(item.rule_id);
    let new_head = replace_named_arg(kb, old_head, "status", ver_term);

    let sort = kb.rule_sort(item.rule_id);
    let domain = kb.rule_domain(item.rule_id);
    kb.assert_fact(new_head, sort, domain, None);

    let status_text = format!("Verified(at: \"{}\")", now_timestamp());
    match update_status_in_source(project_dir, id, &status_text) {
        Ok(()) => println!("verified: {id}"),
        Err(e) => {
            eprintln!("warning: source update for {id} failed: {e}");
            println!("verified: {id} (in-memory only)");
        }
    }
}

fn run_feedback(kb: &mut KnowledgeBase, id: &str, text: &str, agent: &str, project_dir: &Path) {
    let fb_sym = kb.try_resolve_symbol("anthill.stage0.Feedback")
        .unwrap_or_else(|| kb.intern("Feedback"));

    let wi_key = kb.intern("workitem");
    let author_key = kb.intern("author");
    let content_key = kb.intern("content");
    let at_key = kb.intern("at");

    let wi_val = kb.alloc(Term::Const(Literal::String(id.to_string())));
    let author_val = kb.alloc(Term::Const(Literal::String(agent.to_string())));
    let content_val = kb.alloc(Term::Const(Literal::String(text.to_string())));
    let at_val = kb.alloc(Term::Const(Literal::String(now_timestamp())));

    let mut args: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> = SmallVec::new();
    args.push((wi_key, wi_val));
    args.push((author_key, author_val));
    args.push((content_key, content_val));
    args.push((at_key, at_val));
    args.sort_by_key(|(s, _)| s.index());

    let term = kb.alloc(Term::Fn {
        functor: fb_sym,
        pos_args: SmallVec::new(),
        named_args: args,
    });

    let sort = kb.make_name_term("Fact");
    let domain = kb.make_name_term("anthill.stage0");
    kb.assert_fact(term, sort, domain, None);

    let fact_text = anthill_core::persistence::print::print_fact(kb, term, None);
    let workitems_file = scan_dir(project_dir).join("workitems.anthill");
    append_to_file(&workitems_file, &fact_text);

    println!("feedback on {id}: {text}");
}

fn run_graph(kb: &KnowledgeBase) {
    let items = collect_workitems(kb);
    if items.is_empty() {
        println!("No work items found.");
        return;
    }

    // Find roots (items with no dependencies)
    let roots: Vec<&WorkItemInfo> = items.iter()
        .filter(|i| i.depends_on.is_empty())
        .collect();

    // Build reverse index: id → items that depend on it
    let mut dependents: HashMap<&str, Vec<&str>> = HashMap::new();
    for item in &items {
        for dep in &item.depends_on {
            dependents.entry(dep.as_str()).or_default().push(&item.id);
        }
    }

    // Print tree from each root
    fn print_tree(
        id: &str,
        items: &[WorkItemInfo],
        dependents: &HashMap<&str, Vec<&str>>,
        prefix: &str,
        is_last: bool,
    ) {
        let item = items.iter().find(|i| i.id == id);
        let status = item.map(|i| i.status.as_str()).unwrap_or("?");
        let connector = if prefix.is_empty() { "" } else if is_last { "└─ " } else { "├─ " };
        println!("{prefix}{connector}{id} [{status}]");

        if let Some(deps) = dependents.get(id) {
            let child_prefix = if prefix.is_empty() && is_last {
                "   ".to_string()
            } else if is_last {
                format!("{prefix}   ")
            } else {
                format!("{prefix}│  ")
            };
            for (i, dep) in deps.iter().enumerate() {
                print_tree(dep, items, dependents, &child_prefix, i == deps.len() - 1);
            }
        }
    }

    for root in &roots {
        print_tree(&root.id, &items, &dependents, "", true);
    }
}

// ── Term manipulation helpers ───────────────────────────────────

fn replace_named_arg(kb: &mut KnowledgeBase, term: TermId, field: &str, new_value: TermId) -> TermId {
    match kb.get_term(term).clone() {
        Term::Fn { functor, pos_args, named_args } => {
            let new_named: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> = named_args.iter()
                .map(|&(sym, val)| {
                    if kb.resolve_sym(sym) == field { (sym, new_value) } else { (sym, val) }
                })
                .collect();
            kb.alloc(Term::Fn { functor, pos_args, named_args: new_named })
        }
        _ => term,
    }
}

/// Find the `fact ...()` block in source files whose body contains the given id.
/// Returns (file_path, source_text, block_start, block_end).
/// Byte index just past the closing `)` of the `fact ...(...)` block
/// starting at `fact_start`. The depth counter ignores `(` / `)` inside
/// string literals and `--` / `{- -}` comments, so an unbalanced paren
/// in a description doesn't desync the scan. Returns `None` if no
/// closing paren is reached — the caller must bail rather than retry
/// at the same offset.
fn fact_block_end(source: &str, fact_start: usize) -> Option<usize> {
    let mut depth: i32 = 0;
    let mut in_fact = false;
    let mut chars = source[fact_start..].char_indices();
    while let Some((i, ch)) = chars.next() {
        match ch {
            '"' => {
                // `\"` escapes the quote; `\\` escapes the backslash.
                while let Some((_, c)) = chars.next() {
                    if c == '\\' { chars.next(); continue; }
                    if c == '"' { break; }
                }
            }
            '-' if chars.clone().next().map(|(_, c)| c) == Some('-') => {
                while let Some((_, c)) = chars.next() {
                    if c == '\n' { break; }
                }
            }
            '{' if chars.clone().next().map(|(_, c)| c) == Some('-') => {
                chars.next();
                let mut prev_dash = false;
                while let Some((_, c)) = chars.next() {
                    if prev_dash && c == '}' { break; }
                    prev_dash = c == '-';
                }
            }
            '(' => { depth += 1; in_fact = true; }
            ')' => {
                depth -= 1;
                if in_fact && depth == 0 {
                    return Some(fact_start + i + 1);
                }
            }
            _ => {}
        }
    }
    None
}

fn find_fact_block(project_dir: &Path, id: &str) -> Option<(PathBuf, String, usize, usize)> {
    let files = collect_anthill_files(&[scan_dir(project_dir)]);
    let id_marker = format!("id: \"{id}\"");

    for file in &files {
        let source = match fs::read_to_string(&file) {
            Ok(s) => s,
            Err(_) => continue,
        };

        if !source.contains(&id_marker) {
            continue;
        }

        let mut pos = 0;
        while let Some(fact_start) = source[pos..].find("fact ") {
            let abs_start = pos + fact_start;
            let Some(abs_end) = fact_block_end(&source, abs_start) else { break };

            if source[abs_start..abs_end].contains(&id_marker) {
                return Some((file.clone(), source, abs_start, abs_end));
            }

            pos = abs_end;
        }
    }
    None
}

fn write_source(file: &Path, content: &str) -> Result<(), String> {
    fs::write(file, content).map_err(|e| format!("cannot write {}: {e}", file.display()))
}

fn update_status_in_source(project_dir: &Path, id: &str, new_status: &str) -> Result<(), String> {
    let (file, source, abs_start, abs_end) = find_fact_block(project_dir, id)
        .ok_or_else(|| format!("no fact block for {id}"))?;

    let fact_text = &source[abs_start..abs_end];
    // `status` is always written as the last field. rfind so the search
    // doesn't hit a literal `status: ` substring inside an earlier field's
    // string value (e.g. a description quoting `status: Open` as an example).
    let status_offset = fact_text.rfind("status: ").ok_or("no `status:` field")?;
    let status_abs = abs_start + status_offset;
    // status is always written as the last field, so its value runs to the closing `)`.
    let old_end = abs_end - 1;

    let mut result = String::new();
    result.push_str(&source[..status_abs]);
    result.push_str("status: ");
    result.push_str(new_status);
    result.push_str(&source[old_end..]);

    write_source(&file, &result)
}

fn update_depends_in_source(project_dir: &Path, id: &str, new_deps: &[String]) -> Result<(), String> {
    let (file, source, abs_start, abs_end) = find_fact_block(project_dir, id)
        .ok_or_else(|| format!("no fact block for {id}"))?;

    let fact_text = &source[abs_start..abs_end];
    let deps_offset = fact_text.find("depends_on: ").ok_or("no `depends_on:` field")?;
    let deps_abs = abs_start + deps_offset;
    let list_start = deps_abs + "depends_on: ".len();
    let list_end = scan_bracket_list_end(&source, list_start)
        .ok_or("malformed `depends_on:` list")?;

    let mut result = String::new();
    result.push_str(&source[..deps_abs]);
    result.push_str("depends_on: ");
    result.push_str(&format_string_list(new_deps));
    result.push_str(&source[list_end..]);

    write_source(&file, &result)
}

fn update_description_in_source(project_dir: &Path, id: &str, new_description: &str) -> Result<(), String> {
    let (file, source, abs_start, abs_end) = find_fact_block(project_dir, id)
        .ok_or_else(|| format!("no fact block for {id}"))?;

    let fact_text = &source[abs_start..abs_end];
    let key = "description: \"";
    let key_offset = fact_text.find(key).ok_or("no `description:` field")?;
    let value_start = abs_start + key_offset + key.len();

    let mut escaped = false;
    let mut value_end: Option<usize> = None;
    for (i, ch) in source[value_start..].char_indices() {
        if escaped { escaped = false; continue; }
        match ch {
            '\\' => escaped = true,
            '"' => { value_end = Some(value_start + i); break; }
            _ => {}
        }
    }
    let value_end = value_end.ok_or("unterminated description string")?;

    let mut result = String::new();
    result.push_str(&source[..value_start]);
    result.push_str(&escape_anthill_string(new_description));
    result.push_str(&source[value_end..]);

    write_source(&file, &result)
}

fn update_acceptance_in_source(project_dir: &Path, id: &str, new_tools: &[String]) -> Result<(), String> {
    let (file, source, abs_start, abs_end) = find_fact_block(project_dir, id)
        .ok_or_else(|| format!("no fact block for {id}"))?;

    let fact_text = &source[abs_start..abs_end];
    let key = "acceptance: ";
    let key_offset = fact_text.find(key).ok_or("no `acceptance:` field")?;
    let key_abs = abs_start + key_offset;
    let list_start = key_abs + key.len();
    let list_end = scan_bracket_list_end(&source, list_start)
        .ok_or("malformed `acceptance:` list")?;

    let mut result = String::new();
    result.push_str(&source[..key_abs]);
    result.push_str(key);
    result.push_str(&format_acceptance_list(new_tools));
    result.push_str(&source[list_end..]);

    write_source(&file, &result)
}

fn format_string_list(items: &[String]) -> String {
    if items.is_empty() {
        "[]".to_string()
    } else {
        let quoted: Vec<String> = items.iter().map(|s| format!("\"{s}\"")).collect();
        format!("[{}]", quoted.join(", "))
    }
}

fn format_acceptance_list(tools: &[String]) -> String {
    if tools.is_empty() {
        "[]".to_string()
    } else {
        let items: Vec<String> = tools.iter().map(|a| format!("ToolPasses(\"{a}\")")).collect();
        format!("[{}]", items.join(", "))
    }
}

fn escape_anthill_string(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

/// Scan from `list_start` (which must point at `[`) to the matching `]`.
/// Returns the absolute index just past the closing bracket, or None if unbalanced.
fn scan_bracket_list_end(source: &str, list_start: usize) -> Option<usize> {
    if !source[list_start..].starts_with('[') { return None; }
    let mut depth = 0;
    for (i, ch) in source[list_start..].char_indices() {
        match ch {
            '[' => depth += 1,
            ']' => {
                depth -= 1;
                if depth == 0 { return Some(list_start + i + 1); }
            }
            _ => {}
        }
    }
    None
}

fn append_to_file(path: &Path, text: &str) {
    use std::io::Write;
    if let Some(parent) = path.parent() {
        let _ = fs::create_dir_all(parent);
    }
    match fs::OpenOptions::new().create(true).append(true).open(path) {
        Ok(mut f) => { let _ = f.write_all(text.as_bytes()); }
        Err(e) => eprintln!("warning: cannot write to {}: {e}", path.display()),
    }
}

// ── Delete command ───────────────────────────────────────────────

fn run_delete(project_dir: &Path, id: &str) {
    let files = collect_anthill_files(&[scan_dir(project_dir)]);
    let id_marker = format!("id: \"{id}\"");

    for file in &files {
        let source = match fs::read_to_string(file) {
            Ok(s) => s,
            Err(_) => continue,
        };

        if !source.contains(&id_marker) {
            continue;
        }

        let mut found = false;
        let mut result = String::with_capacity(source.len());
        let mut pos = 0;
        while let Some(fact_offset) = source[pos..].find("fact ") {
            let abs_start = pos + fact_offset;
            let Some(abs_end) = fact_block_end(&source, abs_start) else { break };

            if source[abs_start..abs_end].contains(&id_marker) {
                result.push_str(&source[pos..abs_start]);
                let after = source[abs_end..]
                    .strip_prefix('\n')
                    .map_or(abs_end, |_| abs_end + 1);
                pos = after;
                found = true;
            } else {
                result.push_str(&source[pos..abs_end]);
                pos = abs_end;
            }
        }
        result.push_str(&source[pos..]);

        while result.ends_with("\n\n") {
            result.pop();
        }

        if found {
            if let Err(e) = fs::write(file, &result) {
                eprintln!("error: cannot write {}: {e}", file.display());
            } else {
                println!("deleted: {id} from {}", file.display());
            }
            return;
        }
    }

    eprintln!("error: work item '{id}' not found in source files");
}

// ── Dependency commands ─────────────────────────────────────────

/// Check if `from` transitively depends on `target` via the dependency graph.
/// Uses only the `id` and `depends_on` fields of WorkItemInfo.
fn has_transitive_dep(items: &[WorkItemInfo], from: &str, target: &str) -> bool {
    let mut visited = std::collections::HashSet::new();
    let mut stack = vec![from];
    while let Some(current) = stack.pop() {
        if !visited.insert(current) { continue; }
        if let Some(item) = items.iter().find(|i| i.id == current) {
            for dep in &item.depends_on {
                if dep == target { return true; }
                stack.push(dep);
            }
        }
    }
    false
}

fn run_add_dependency(kb: &KnowledgeBase, project_dir: &Path, id: &str, dep_id: &str) {
    let items = collect_workitems(kb);
    let item = match items.iter().find(|i| i.id == id) {
        Some(i) => i,
        None => { eprintln!("error: work item '{id}' not found"); return; }
    };

    if id == dep_id {
        eprintln!("error: work item cannot depend on itself");
        return;
    }

    if !items.iter().any(|i| i.id == dep_id) {
        eprintln!("error: dependency target '{dep_id}' not found");
        return;
    }

    if item.depends_on.iter().any(|d| d == dep_id) {
        eprintln!("error: '{id}' already depends on '{dep_id}'");
        return;
    }

    if has_transitive_dep(&items, dep_id, id) {
        eprintln!("error: adding {id} -> {dep_id} would create a cycle ({dep_id} already transitively depends on {id})");
        return;
    }

    let mut new_deps = item.depends_on.clone();
    new_deps.push(dep_id.to_string());

    match update_depends_in_source(project_dir, id, &new_deps) {
        Ok(()) => println!("added dependency: {id} -> {dep_id}"),
        Err(e) => eprintln!("error: source update for {id} failed: {e}"),
    }
}

fn run_remove_dependency(kb: &KnowledgeBase, project_dir: &Path, id: &str, dep_id: &str) {
    let items = collect_workitems(kb);
    let item = match items.iter().find(|i| i.id == id) {
        Some(i) => i,
        None => { eprintln!("error: work item '{id}' not found"); return; }
    };

    if !item.depends_on.iter().any(|d| d == dep_id) {
        eprintln!("error: '{id}' does not depend on '{dep_id}'");
        return;
    }

    let new_deps: Vec<String> = item.depends_on.iter()
        .filter(|d| d.as_str() != dep_id)
        .cloned()
        .collect();

    match update_depends_in_source(project_dir, id, &new_deps) {
        Ok(()) => println!("removed dependency: {id} -> {dep_id}"),
        Err(e) => eprintln!("error: source update for {id} failed: {e}"),
    }
}

// ── Update command ──────────────────────────────────────────────

fn run_update(
    kb: &KnowledgeBase,
    project_dir: &Path,
    id: &str,
    description: Option<&str>,
    acceptance: &[String],
) {
    let items = collect_workitems(kb);
    if !items.iter().any(|i| i.id == id) {
        eprintln!("error: work item '{id}' not found");
        return;
    }

    // clap gives an empty Vec when --acceptance is not passed; treat that as "no change".
    let update_acceptance = !acceptance.is_empty();

    if description.is_none() && !update_acceptance {
        eprintln!("error: nothing to update — pass --description and/or --acceptance");
        return;
    }

    let mut changed = Vec::new();

    if let Some(desc) = description {
        match update_description_in_source(project_dir, id, desc) {
            Ok(()) => changed.push("description"),
            Err(e) => { eprintln!("error: update description for {id}: {e}"); return; }
        }
    }

    if update_acceptance {
        match update_acceptance_in_source(project_dir, id, acceptance) {
            Ok(()) => changed.push("acceptance"),
            Err(e) => { eprintln!("error: update acceptance for {id}: {e}"); return; }
        }
    }

    println!("updated {id}: {}", changed.join(", "));
}

// ── Init command ────────────────────────────────────────────────

fn run_init(project_name: Option<&str>) {
    let cwd = std::env::current_dir().expect("cannot determine current directory");
    let dir = cwd.join("anthill-todo");

    if dir.exists() {
        eprintln!("error: anthill-todo/ already exists");
        return;
    }

    let name = project_name.unwrap_or_else(|| {
        cwd.file_name().and_then(|n| n.to_str()).unwrap_or("my-project")
    });

    fs::create_dir_all(&dir).expect("cannot create anthill-todo/");

    let domain = include_str!("../../../examples/github-todo/domain.anthill");
    fs::write(dir.join("domain.anthill"), domain).expect("write domain.anthill");

    let rules = include_str!("../../../examples/github-todo/rules.anthill");
    fs::write(dir.join("rules.anthill"), rules).expect("write rules.anthill");

    let project = format!(
        "-- Project configuration\n\nfact Project(\n  name: \"{name}\",\n  language: \"rust\",\n  build: \"cargo\",\n  tools: [\"cargo-test\"])\n"
    );
    fs::write(dir.join("project.anthill"), project).expect("write project.anthill");

    fs::write(dir.join("workitems.anthill"), "-- Work items\n\n").expect("write workitems.anthill");

    println!("created anthill-todo/ with:");
    println!("  domain.anthill    — entity type definitions");
    println!("  rules.anthill     — workflow rules (claimable, blocked, ...)");
    println!("  project.anthill   — project configuration");
    println!("  workitems.anthill — work items (empty)");
}

// ── Add command ─────────────────────────────────────────────────

fn next_workitem_id(kb: &KnowledgeBase, project_dir: &Path) -> Result<String, String> {
    if kb.try_resolve_symbol("anthill.stage0.WorkItem").is_none() {
        let domain_path = scan_dir(project_dir).join("domain.anthill");
        if !domain_path.is_file() {
            return Err(format!(
                "this directory is not an anthill-todo project (no {} found). \
                 Run `anthill-todo init` to scaffold one.",
                domain_path.display()
            ));
        }
        return Err(format!(
            "WorkItem sort not found in KB — {} may have parse errors \
             (any warnings would have printed to stderr above).",
            domain_path.display()
        ));
    }

    let items = collect_workitems(kb);
    let mut max_num: u32 = 0;

    for item in &items {
        if let Some(rest) = item.id.strip_prefix("WI-") {
            if let Ok(n) = rest.parse::<u32>() {
                max_num = max_num.max(n);
            }
        }
    }

    Ok(format!("WI-{:03}", max_num + 1))
}

fn run_add(kb: &KnowledgeBase, project_dir: &Path, description: &str, depends_on: &[String], acceptance: &[String]) {
    let id = match next_workitem_id(kb, project_dir) {
        Ok(id) => id,
        Err(e) => {
            eprintln!("error: {e}");
            return;
        }
    };
    let desc_escaped = escape_anthill_string(description);

    let deps = format_string_list(depends_on);

    let acc = if acceptance.is_empty() {
        format_acceptance_list(&["cargo-test".to_string()])
    } else {
        format_acceptance_list(acceptance)
    };

    let block = format!(
        "fact WorkItem(\n  id: \"{id}\",\n  description: \"{desc_escaped}\",\n  acceptance: {acc},\n  depends_on: {deps},\n  status: Open)\n\n"
    );

    let workitems_file = scan_dir(project_dir).join("workitems.anthill");
    append_to_file(&workitems_file, &block);

    println!("added: {id} — {description}");
}

// ── Entry point ─────────────────────────────────────────────────

fn main() -> ExitCode {
    // `--anthill` is hidden from clap's `--help` because the bundle is
    // still a partial port; route to the bundle pre-clap when present.
    let mut raw_args: Vec<String> = std::env::args().collect();
    if let Some(idx) = raw_args.iter().position(|a| a == "--anthill") {
        raw_args.remove(idx);
        raw_args.remove(0);
        return run_anthill_bundle(&raw_args);
    }

    let cli = Cli::parse();

    // These commands don't need project dir
    if let TodoCommand::Init { name } = &cli.command {
        run_init(name.as_deref());
        return ExitCode::SUCCESS;
    }

    if let TodoCommand::Skill = &cli.command {
        print!("{}", SKILL_MD);
        return ExitCode::SUCCESS;
    }

    let project_dir = match find_project_dir(cli.project_dir.as_deref()) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::FAILURE;
        }
    };

    // Delete operates on source files, doesn't need full KB
    if let TodoCommand::Delete { id } = &cli.command {
        run_delete(&project_dir, id);
        return ExitCode::SUCCESS;
    }

    let mut kb = match load_kb(&project_dir, cli.stdlib_path.as_deref()) {
        Ok(kb) => kb,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::FAILURE;
        }
    };

    match &cli.command {
        TodoCommand::Init { .. } | TodoCommand::Delete { .. } | TodoCommand::Skill => unreachable!(),
        TodoCommand::Add { description, depends_on, acceptance } => {
            run_add(&kb, &project_dir, description, depends_on, acceptance);
        }
        TodoCommand::Status => run_status(&kb),
        TodoCommand::List { status, all } => run_list(&kb, status.as_deref(), *all),
        TodoCommand::Next { all } => run_next(&mut kb, *all),
        TodoCommand::Show { id } => run_show(&kb, id),
        TodoCommand::Claim { id } => run_claim(&mut kb, id, &cli.agent, &project_dir),
        TodoCommand::Deliver { id } => run_deliver(&mut kb, id, &cli.agent, &project_dir),
        TodoCommand::Verify { id } => run_verify(&mut kb, id, &project_dir),
        TodoCommand::Feedback { id, text } => run_feedback(&mut kb, id, text, &cli.agent, &project_dir),
        TodoCommand::Update { id, description, acceptance } => {
            run_update(&kb, &project_dir, id, description.as_deref(), acceptance);
        }
        TodoCommand::AddDependency { id, dependency } => run_add_dependency(&kb, &project_dir, id, dependency),
        TodoCommand::RemoveDependency { id, dependency } => run_remove_dependency(&kb, &project_dir, id, dependency),
        TodoCommand::Graph => run_graph(&kb),
    }

    ExitCode::SUCCESS
}

// ── Anthill-bundle entry point ──────────────────────────────────

/// Compilation failure — parse, load, or build error.
const EXIT_COMPILE: u8 = 2;
/// Runtime failure — interpreter errored during `main`.
const EXIT_RUNTIME: u8 = 1;
/// Substituted for a `main` return value outside 0..=255 so an
/// out-of-range exit can be distinguished from a legitimate 255.
const EXIT_OUT_OF_RANGE: u8 = 255;

fn run_anthill_bundle(argv: &[String]) -> ExitCode {
    use anthill_core::eval::{builtins, Interpreter, Value};
    use anthill_core::kb::load::NullResolver;

    // `init` runs before any KB exists — it scaffolds the project's
    // anthill-todo/ directory. Reuse the legacy implementation; once
    // there's a project to load, the bundle takes over.
    if argv.first().map(|s| s.as_str()) == Some("init") {
        let name = argv.get(1).map(|s| s.as_str());
        run_init(name);
        return ExitCode::SUCCESS;
    }

    // Strip the global flags `-d <dir>` (`--dir`) and `--agent <name>` so
    // the bundle dispatch sees only its own subcommand args. The bundle's
    // parse_argv doesn't know about globals yet — once OperationSpec gains
    // a `globals` field this can move into anthill code.
    let mut bundle_argv: Vec<String> = Vec::with_capacity(argv.len());
    let mut explicit_dir: Option<PathBuf> = None;
    let mut agent: String = "user".to_string();
    let mut iter = argv.iter();
    while let Some(arg) = iter.next() {
        if arg == "-d" || arg == "--dir" {
            if let Some(dir) = iter.next() {
                explicit_dir = Some(PathBuf::from(dir));
            }
        } else if arg == "--agent" {
            if let Some(a) = iter.next() {
                agent = a.clone();
            }
        } else {
            bundle_argv.push(arg.clone());
        }
    }

    let (stdlib_parsed, stdlib_errors) = stdlib_embedded::parse_embedded_stdlib();
    let (bundle_parsed, bundle_errors) = anthill_bundle::parse_embedded_bundle();
    for e in stdlib_errors.iter().chain(bundle_errors.iter()) {
        eprintln!("error: {e}");
    }
    if !stdlib_errors.is_empty() || !bundle_errors.is_empty() {
        return ExitCode::from(EXIT_COMPILE);
    }

    // Bulk-pull the project's anthill-todo/ files: domain.anthill defines
    // WorkItem etc., rules.anthill provides workflow rules, workitems.anthill
    // carries the user-asserted facts. Without this the bundle's KB only
    // sees stdlib + the bundle itself, and `sort_query("WorkItem")` fails.
    let project_dir = match find_project_dir(explicit_dir.as_deref()) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::FAILURE;
        }
    };
    let scan = scan_dir(&project_dir);
    let project_files = collect_anthill_files(&[scan]);
    // Each project file pairs its on-disk path with the parsed IR so
    // the IndexedFileStore can later associate fact RuleIds with their
    // byte-range spans on disk.
    struct ProjectFile { path: PathBuf, parsed: ParsedFile }
    let mut project_items: Vec<ProjectFile> = Vec::new();
    for file in &project_files {
        let source = match fs::read_to_string(file) {
            Ok(s) => s,
            Err(e) => { eprintln!("warning: {}: {e}", file.display()); continue; }
        };
        match parse::parse(&source) {
            Ok(mut parsed) => {
                assign_default_namespace(&mut parsed);
                project_items.push(ProjectFile { path: file.clone(), parsed });
            }
            Err(errs) => {
                for err in &errs {
                    eprintln!("warning: {}:{}", file.display(), err.format_with_source(&source));
                }
            }
        }
    }

    let mut kb = KnowledgeBase::new();
    let all_refs: Vec<&ParsedFile> = stdlib_parsed.iter()
        .chain(bundle_parsed.iter())
        .chain(project_items.iter().map(|pf| &pf.parsed))
        .collect();
    let project_offset = stdlib_parsed.len() + bundle_parsed.len();
    let per_file_results = match load::load_all_per_file(&mut kb, &all_refs, &NullResolver) {
        Ok((_merged, per_file)) => per_file,
        Err(errs) => {
            let mut had_fatal = false;
            for e in &errs {
                if e.is_load_blocking() {
                    had_fatal = true;
                    eprintln!("error: {e}");
                } else {
                    eprintln!("warning: {e}");
                }
            }
            if had_fatal { return ExitCode::from(EXIT_COMPILE); }
            Vec::new()
        }
    };

    let mut interp = Interpreter::new(kb);
    if let Err(e) = builtins::register_standard_builtins(&mut interp) {
        eprintln!("error: registering builtins: {e}");
        return ExitCode::from(EXIT_RUNTIME);
    }
    if let Err(e) = interp.register_standard_effect_handlers() {
        eprintln!("error: registering effect handlers: {e}");
        return ExitCode::from(EXIT_RUNTIME);
    }

    // Build the FileStore handle the anthill side will receive. Mutating
    // commands (add / feedback / claim / ...) call `Store.persist` /
    // `Store.flush` on this entity; the registry routes the dispatch to
    // the matching FileStore instance backing the project's anthill-todo/
    // directory. `Flat` convention matches the legacy on-disk layout
    // (one workitems.anthill, no per-fact subfolders).
    let store_root = scan_dir(&project_dir);
    let store_root_str = store_root.to_string_lossy().to_string();
    let store_value = {
        use anthill_core::persistence::file_store::FileConvention;
        use anthill_core::persistence::indexed_file_store::IndexedFileStore;
        let fs_sym = interp.kb_mut().intern("FileStore");
        let flat_sym = interp.kb_mut().intern("Flat");
        let root_field = interp.kb_mut().intern("root");
        let conv_field = interp.kb_mut().intern("convention");
        let v = Value::Entity {
            functor: fs_sym,
            pos: vec![],
            named: vec![
                (root_field, Value::Str(store_root_str.clone())),
                (conv_field, Value::Entity {
                    functor: flat_sym,
                    pos: vec![],
                    named: vec![],
                }),
            ],
        };
        let key = match interp.store_canonical_key(&v) {
            Ok(k) => k,
            Err(e) => {
                eprintln!("error: computing store key: {e}");
                return ExitCode::from(EXIT_RUNTIME);
            }
        };

        // Seed the IndexedFileStore's source map: pair each project
        // file's fact RuleIds (in source order) with the byte ranges
        // of the corresponding parsed Item::Fact spans. Retract on
        // any source-loaded RuleId then knows exactly which file and
        // byte range to drop.
        let mut store = IndexedFileStore::new(store_root, FileConvention::Flat);
        for (file, result) in project_items.iter()
            .zip(per_file_results.iter().skip(project_offset))
        {
            let spans = file.parsed.fact_spans();
            for (rule_id, span) in result.fact_rule_ids.iter().zip(spans.iter()) {
                store.record_source(*rule_id, file.path.clone(), *span);
            }
        }

        interp.register_store(key, Box::new(store));
        v
    };

    let elements: Vec<Value> = bundle_argv.iter().map(|s| Value::Str(s.clone())).collect();
    let args_value = match interp.build_list_value(elements, &[]) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("error: building args list: {e}");
            return ExitCode::from(EXIT_RUNTIME);
        }
    };
    let agent_value = Value::Str(agent);

    // Seed Cell[V = WIS] from on-disk WI-NNN max so the next freshly
    // allocated id doesn't collide. Bundle command bodies still go
    // through `store: FileStore` until phase 3 wires them to spec ops.
    let wis_cell_value = {
        let kb_ref = interp.kb();
        let mut max_num: u32 = 0;
        for item in collect_workitems(kb_ref) {
            if let Some(rest) = item.id.strip_prefix("WI-") {
                if let Ok(n) = rest.parse::<u32>() {
                    max_num = max_num.max(n);
                }
            }
        }
        let id_counter = (max_num as i64) + 1;

        // Build the wis(backend, id_counter) entity. The `backend` field
        // is the same store_value used by the FileStore registry, so
        // anthill-side `persist`/`flush` calls through the cell route to
        // the same underlying IndexedFileStore.
        let wis_sym = interp.kb_mut().intern("anthill.todo.store.FileBasedWorkitemStore.wis");
        let backend_field = interp.kb_mut().intern("backend");
        let counter_field = interp.kb_mut().intern("id_counter");
        let wis_value = Value::Entity {
            functor: wis_sym,
            pos: vec![],
            named: vec![
                (backend_field, store_value.clone()),
                (counter_field, Value::Int(id_counter)),
            ],
        };
        let handle = interp.alloc_cell(wis_value);
        Value::Cell(handle)
    };

    // Build the chain_dicts for Main's flattened requires chain. Walk
    // the chain via the public requires_chain_flat API and allocate
    // a dictionary handle per entry — FileBasedWorkitemStore for the
    // WorkItemStore slot (so cmd_X dispatch lands on the impl), and
    // self-referential placeholders for every other slot. Walking
    // dynamically avoids hard-coding the chain length, which can grow
    // when Main gains more requires.
    let chain_dicts: smallvec::SmallVec<[_; 2]> = {
        let main_sym = interp.kb().try_resolve_symbol("anthill.todo.Main")
            .expect("anthill.todo.Main must be loaded");
        let workitemstore_sym = interp.kb()
            .try_resolve_symbol("anthill.todo.store.WorkItemStore");
        let filebased_sym = interp.kb_mut()
            .intern("anthill.todo.store.FileBasedWorkitemStore");
        let entries = anthill_core::kb::typing::requires_chain_flat(
            interp.kb(), main_sym,
        );
        let mut out: smallvec::SmallVec<[_; 2]> = smallvec::SmallVec::new();
        for entry in &entries {
            let impl_sym = if Some(entry.required_sort) == workitemstore_sym {
                filebased_sym
            } else {
                entry.required_sort
            };
            out.push(interp.alloc_requirement(impl_sym, smallvec::SmallVec::new()));
        }
        out
    };

    match interp.call_with_requirements("anthill.todo.Main.main",
                      &[args_value, store_value, wis_cell_value, agent_value],
                      chain_dicts) {
        Ok(Value::Int(n)) => {
            if (0..=255).contains(&n) {
                ExitCode::from(n as u8)
            } else {
                eprintln!("warning: main returned {n}, outside 0..=255 — clamped");
                ExitCode::from(EXIT_OUT_OF_RANGE)
            }
        }
        Ok(other) => {
            eprintln!("error: main returned non-Int value: {other:?}");
            ExitCode::from(EXIT_RUNTIME)
        }
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::from(EXIT_RUNTIME)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_item(id: &str, deps: &[&str]) -> WorkItemInfo {
        WorkItemInfo {
            rule_id: RuleId::from_raw(0),
            id: id.to_string(),
            description: String::new(),
            status: "Open".to_string(),
            depends_on: deps.iter().map(|s| s.to_string()).collect(),
        }
    }

    #[test]
    fn transitive_dep_direct() {
        let items = vec![
            make_item("A", &["B"]),
            make_item("B", &[]),
        ];
        assert!(has_transitive_dep(&items, "A", "B"));
        assert!(!has_transitive_dep(&items, "B", "A"));
    }

    #[test]
    fn transitive_dep_chain() {
        let items = vec![
            make_item("A", &["B"]),
            make_item("B", &["C"]),
            make_item("C", &[]),
        ];
        assert!(has_transitive_dep(&items, "A", "C"));
        assert!(!has_transitive_dep(&items, "C", "A"));
    }

    #[test]
    fn transitive_dep_diamond() {
        // A -> B -> D
        // A -> C -> D
        let items = vec![
            make_item("A", &["B", "C"]),
            make_item("B", &["D"]),
            make_item("C", &["D"]),
            make_item("D", &[]),
        ];
        assert!(has_transitive_dep(&items, "A", "D"));
        assert!(!has_transitive_dep(&items, "D", "A"));
        assert!(!has_transitive_dep(&items, "B", "C"));
    }

    #[test]
    fn transitive_dep_no_relation() {
        let items = vec![
            make_item("A", &[]),
            make_item("B", &[]),
        ];
        assert!(!has_transitive_dep(&items, "A", "B"));
        assert!(!has_transitive_dep(&items, "B", "A"));
    }

    #[test]
    fn transitive_dep_existing_cycle() {
        // Already-cyclic graph shouldn't infinite loop
        let items = vec![
            make_item("A", &["B"]),
            make_item("B", &["A"]),
        ];
        assert!(has_transitive_dep(&items, "A", "B"));
        assert!(has_transitive_dep(&items, "B", "A"));
    }

    #[test]
    fn transitive_dep_missing_target() {
        let items = vec![
            make_item("A", &["X"]),
        ];
        // X not in items — should not panic, just not found
        assert!(!has_transitive_dep(&items, "A", "Z"));
    }

    // ── update_status_in_source: regression for description-shadowing ──

    /// Regression: the original `update_status_in_source` used
    /// `fact_text.find("status: ")` and matched the first occurrence,
    /// including substrings inside the quoted description. Triggered when
    /// an item's description quoted `status: Open` as part of an example —
    /// the claim/deliver path would substitute *inside the description*,
    /// destroying the surrounding fact block. Fix: rfind so the actual
    /// `status:` field (always written last) wins.
    #[test]
    fn update_status_does_not_match_status_in_description() {
        let dir = tempfile::tempdir().expect("tempdir");
        let project = dir.path();
        let workitems = project.join("workitems.anthill");

        // A WorkItem whose description literally contains `status: Open`,
        // verifying the rfind anchor doesn't follow the description's example.
        let original = "fact WorkItem(\n  \
            id: \"WI-X\",\n  \
            description: \"asserts a WorkItem(id: \\\"X\\\", status: Open), retracts it\",\n  \
            acceptance: [ToolPasses(\"cargo-test\")],\n  \
            depends_on: [],\n  \
            status: Open)\n";
        std::fs::write(&workitems, original).unwrap();

        let new_status = r#"Claimed(agent: "claude", since: "2026-05-05T19:15:00Z")"#;
        update_status_in_source(project, "WI-X", new_status)
            .expect("update should succeed");

        let after = std::fs::read_to_string(&workitems).unwrap();

        // Description must be intact — no substitution into the quoted text.
        assert!(
            after.contains(r#"description: "asserts a WorkItem(id: \"X\", status: Open), retracts it""#),
            "description was mutated:\n{after}"
        );

        // The actual status field was updated to the new value.
        assert!(
            after.contains(&format!("status: {new_status}")),
            "status field not updated:\n{after}"
        );

        // Block is well-formed — closes with `)\n`.
        assert!(after.trim_end().ends_with(')'), "fact block not closed:\n{after}");

        // Round-trip: the resulting file must parse without errors.
        anthill_core::parse::parse(&after)
            .expect("rewritten fact must parse cleanly");
    }
}
