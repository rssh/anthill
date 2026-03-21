use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand};

use anthill_core::kb::load::{self, FileSourceResolver};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::{KnowledgeBase, RuleId};
use anthill_core::parse;
use anthill_core::parse::ir::ParsedFile;
use anthill_core::persistence::print::TermPrinter;
use anthill_core::persistence::term_ser;

use smallvec::SmallVec;

mod stdlib_embedded;

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
    /// List work items
    List {
        /// Filter by status (e.g. open, claimed, verified)
        #[arg(long)]
        status: Option<String>,
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
    /// Show dependency graph
    Graph,
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

    // Check for anthill-todo/ subdirectory
    let subdir = cwd.join("anthill-todo");
    if subdir.is_dir() {
        return Ok(subdir);
    }

    Err("no anthill-todo/ directory found.\n  Run `anthill-todo init` to create one.".into())
}

// ── KB loading ──────────────────────────────────────────────────

fn load_kb(project_dir: &Path, stdlib_path: Option<&Path>) -> Result<KnowledgeBase, String> {
    // Phase 1: Parse stdlib (embedded or from disk)
    let mut parsed_files: Vec<ParsedFile> = Vec::new();

    if let Some(stdlib_dir) = stdlib_path {
        let stdlib_files = collect_anthill_files(&[stdlib_dir.to_path_buf()]);
        for file in &stdlib_files {
            let source = fs::read_to_string(file)
                .map_err(|e| format!("{}: {e}", file.display()))?;
            match parse::parse(&source) {
                Ok(p) => parsed_files.push(p),
                Err(errs) => {
                    for e in &errs {
                        eprintln!("warning: {}: {e}", file.display());
                    }
                }
            }
        }
    } else {
        let (stdlib_parsed, stdlib_errors) = stdlib_embedded::parse_embedded_stdlib();
        parsed_files.extend(stdlib_parsed);
        for e in &stdlib_errors {
            eprintln!("warning: {e}");
        }
    }

    // Phase 2: Parse project files
    let project_files = collect_anthill_files(&[project_dir.to_path_buf()]);
    for file in &project_files {
        let source = fs::read_to_string(file)
            .map_err(|e| format!("{}: {e}", file.display()))?;
        match parse::parse(&source) {
            Ok(p) => parsed_files.push(p),
            Err(errs) => {
                for e in &errs {
                    eprintln!("warning: {}: {e}", file.display());
                }
            }
        }
    }

    if parsed_files.is_empty() {
        return Err("no .anthill files found".into());
    }

    let mut kb = KnowledgeBase::new();

    let paths = &[project_dir.to_path_buf()];
    let base_dirs: Vec<PathBuf> = paths.iter()
        .filter_map(|p| {
            if p.is_dir() { p.parent().map(|pp| pp.to_path_buf()) }
            else { p.parent().and_then(|pp| pp.parent()).map(|pp| pp.to_path_buf()) }
        })
        .collect::<std::collections::HashSet<_>>()
        .into_iter()
        .collect();
    let resolver = FileSourceResolver::new(base_dirs);

    let refs: Vec<&ParsedFile> = parsed_files.iter().collect();
    if let Err(errs) = load::load_all(&mut kb, &refs, &resolver) {
        for e in &errs {
            eprintln!("warning: {e}");
        }
    }

    // Load .toml/.json data files
    let data_files = collect_data_files(paths);
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

fn run_list(kb: &KnowledgeBase, status_filter: Option<&str>) {
    let items = collect_workitems(kb);
    let filtered: Vec<_> = items.iter()
        .filter(|i| status_filter.map_or(true, |f| i.status.eq_ignore_ascii_case(f)))
        .collect();

    if filtered.is_empty() {
        println!("No work items found.");
        return;
    }

    for item in &filtered {
        let deps = if item.depends_on.is_empty() {
            String::new()
        } else {
            format!(" (depends: {})", item.depends_on.join(", "))
        };
        println!("  {} [{}] {}{}", item.id, item.status, item.description, deps);
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

    let id_var = { let s = kb.intern("id"); let v = kb.fresh_var(s); kb.alloc(Term::Var(v)) };
    let desc_var = { let s = kb.intern("desc"); let v = kb.fresh_var(s); kb.alloc(Term::Var(v)) };
    let query = kb.alloc(Term::Fn {
        functor: claimable_sym,
        pos_args: SmallVec::from_slice(&[id_var, desc_var]),
        named_args: SmallVec::new(),
    });

    let config = ResolveConfig { max_solutions: if show_all { 100 } else { 1 }, ..ResolveConfig::default() };
    let solutions = kb.resolve(&[query], &config);

    if solutions.is_empty() {
        println!("No claimable items (all blocked or none open).");
        return;
    }

    let query_vars = kb.collect_vars(query);
    for sol in &solutions {
        let id = query_vars.iter()
            .find(|v| kb.resolve_sym(v.name()) == "id")
            .and_then(|v| sol.subst.resolve(*v))
            .and_then(|t| extract_string(kb, t))
            .unwrap_or_else(|| "?".into());
        let desc = query_vars.iter()
            .find(|v| kb.resolve_sym(v.name()) == "desc")
            .and_then(|v| sol.subst.resolve(*v))
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

fn run_claim(kb: &mut KnowledgeBase, id: &str, agent: &str, output: Option<&Path>) {
    // Verify claimable
    let claimable_sym = match kb.try_resolve_symbol("anthill.stage0.workflow.claimable") {
        Some(s) => s,
        None => { eprintln!("error: workflow rules not loaded"); return; }
    };

    let id_term = kb.alloc(Term::Const(Literal::String(id.to_string())));
    let desc_var = { let s = kb.intern("desc"); let v = kb.fresh_var(s); kb.alloc(Term::Var(v)) };
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

    println!("claimed: {id} by {agent}");

    if let Some(out) = output {
        let text = anthill_core::persistence::print::print_fact(kb, new_head, None);
        append_to_file(out, &text);
    }
}

fn run_deliver(kb: &mut KnowledgeBase, id: &str, agent: &str, output: Option<&Path>) {
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

    println!("delivered: {id} by {agent}");

    if let Some(out) = output {
        let text = anthill_core::persistence::print::print_fact(kb, new_head, None);
        append_to_file(out, &text);
    }
}

fn run_feedback(kb: &mut KnowledgeBase, id: &str, text: &str, agent: &str, output: Option<&Path>) {
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

    println!("feedback on {id}: {text}");

    if let Some(out) = output {
        let fact_text = anthill_core::persistence::print::print_fact(kb, term, None);
        append_to_file(out, &fact_text);
    }
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
    let files = collect_anthill_files(&[project_dir.to_path_buf()]);
    let id_marker = format!("id: \"{id}\"");

    for file in &files {
        let source = match fs::read_to_string(file) {
            Ok(s) => s,
            Err(_) => continue,
        };

        if !source.contains(&id_marker) {
            continue;
        }

        // Remove the fact block containing this ID.
        // Matches both single-line `fact WorkItem(...)` and multi-line `fact WorkItem(\n...\n)`
        let mut result = String::new();
        let mut skip = false;
        let mut paren_depth: i32 = 0;
        let mut found = false;

        for line in source.lines() {
            let trimmed = line.trim();

            // Detect start of a fact containing our ID
            if !skip && trimmed.starts_with("fact ") && source[result.len()..].contains(&id_marker) {
                // Check if this specific fact block contains the ID
                // by scanning ahead from current position
                let remaining = &source[result.len()..];
                let fact_start = remaining.find("fact ").unwrap();
                // Find the matching closing paren
                let mut depth: i32 = 0;
                let mut end_pos = fact_start;
                let mut in_fact = false;
                for (i, ch) in remaining[fact_start..].char_indices() {
                    match ch {
                        '(' => { depth += 1; in_fact = true; }
                        ')' => {
                            depth -= 1;
                            if in_fact && depth == 0 {
                                end_pos = fact_start + i + 1;
                                break;
                            }
                        }
                        _ => {}
                    }
                }
                let fact_text = &remaining[fact_start..end_pos];
                if fact_text.contains(&id_marker) {
                    skip = true;
                    paren_depth = 0;
                    found = true;
                    // Track paren depth for this line
                    for ch in trimmed.chars() {
                        match ch {
                            '(' => paren_depth += 1,
                            ')' => paren_depth -= 1,
                            _ => {}
                        }
                    }
                    if paren_depth <= 0 {
                        skip = false;
                    }
                    continue;
                }
            }

            if skip {
                for ch in trimmed.chars() {
                    match ch {
                        '(' => paren_depth += 1,
                        ')' => paren_depth -= 1,
                        _ => {}
                    }
                }
                if paren_depth <= 0 {
                    skip = false;
                }
                continue;
            }

            result.push_str(line);
            result.push('\n');
        }

        // Remove trailing blank lines
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

fn next_workitem_id(kb: &KnowledgeBase) -> String {
    let items = collect_workitems(kb);
    let mut max_num: u32 = 0;

    for item in &items {
        if let Some(rest) = item.id.strip_prefix("WI-") {
            if let Ok(n) = rest.parse::<u32>() {
                max_num = max_num.max(n);
            }
        }
    }

    format!("WI-{:03}", max_num + 1)
}

fn run_add(kb: &KnowledgeBase, project_dir: &Path, description: &str, depends_on: &[String], acceptance: &[String]) {
    let id = next_workitem_id(kb);
    let desc_escaped = description.replace('"', "\\\"");

    let deps = if depends_on.is_empty() {
        "[]".to_string()
    } else {
        let items: Vec<String> = depends_on.iter().map(|d| format!("\"{d}\"")).collect();
        format!("[{}]", items.join(", "))
    };

    let acc = if acceptance.is_empty() {
        "[ToolPasses(\"cargo-test\")]".to_string()
    } else {
        let items: Vec<String> = acceptance.iter().map(|a| format!("ToolPasses(\"{a}\")")).collect();
        format!("[{}]", items.join(", "))
    };

    let block = format!(
        "fact WorkItem(\n  id: \"{id}\",\n  description: \"{desc_escaped}\",\n  acceptance: {acc},\n  depends_on: {deps},\n  status: Open)\n\n"
    );

    let workitems_file = project_dir.join("workitems.anthill");
    append_to_file(&workitems_file, &block);

    println!("added: {id} — {description}");
}

// ── Entry point ─────────────────────────────────────────────────

fn main() -> ExitCode {
    let cli = Cli::parse();

    // Init doesn't need project dir
    if let TodoCommand::Init { name } = &cli.command {
        run_init(name.as_deref());
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

    let output_file = project_dir.join("transitions.anthill");

    match &cli.command {
        TodoCommand::Init { .. } | TodoCommand::Delete { .. } => unreachable!(),
        TodoCommand::Add { description, depends_on, acceptance } => {
            run_add(&kb, &project_dir, description, depends_on, acceptance);
        }
        TodoCommand::Status => run_status(&kb),
        TodoCommand::List { status } => run_list(&kb, status.as_deref()),
        TodoCommand::Next { all } => run_next(&mut kb, *all),
        TodoCommand::Show { id } => run_show(&kb, id),
        TodoCommand::Claim { id } => run_claim(&mut kb, id, &cli.agent, Some(&output_file)),
        TodoCommand::Deliver { id } => run_deliver(&mut kb, id, &cli.agent, Some(&output_file)),
        TodoCommand::Feedback { id, text } => run_feedback(&mut kb, id, text, &cli.agent, Some(&output_file)),
        TodoCommand::Graph => run_graph(&kb),
    }

    ExitCode::SUCCESS
}
