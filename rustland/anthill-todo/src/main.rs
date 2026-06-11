use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use anthill_core::kb::load;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use anthill_core::parse::ir::ParsedFile;

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
anthill-todo -d "$PWD" list --tag typing                 # Tag's items in dependency (sequence) order
anthill-todo -d "$PWD" add "description" [--depends WI-NNN] [--tag NAME]  # Add a new work item
anthill-todo -d "$PWD" insert "description" --before WI-NNN [--tag NAME]  # Insert a prerequisite before WI-NNN
anthill-todo -d "$PWD" show WI-NNN                       # Show details
anthill-todo -d "$PWD" next                              # Show next claimable item
anthill-todo -d "$PWD" --agent claude claim WI-NNN       # Claim a work item
anthill-todo -d "$PWD" --agent claude deliver WI-NNN     # Mark as delivered
anthill-todo -d "$PWD" feedback WI-NNN "feedback text"   # Add feedback
anthill-todo -d "$PWD" tag WI-NNN typing                 # Add a tag (named list)
anthill-todo -d "$PWD" untag WI-NNN typing               # Remove a tag
anthill-todo -d "$PWD" add-dependency WI-A WI-B          # Make WI-A depend on WI-B
anthill-todo -d "$PWD" remove-dependency WI-A WI-B       # Drop WI-A's dependency on WI-B
anthill-todo -d "$PWD" status                            # Show status counts
anthill-todo -d "$PWD" graph                             # Show dependency graph
anthill-todo -d "$PWD" init                              # Initialize anthill-todo/ in project
```

### Build-loop primitives (tags + ordered insert)

A *named list* (tag) plus `list --tag` gives a machine-readable, dependency-ordered
sequence: `list --tag typing` shows the tag's items topologically (a dependency
appears before its dependents) with status, marking the first undelivered item whose
dependencies are all satisfied with `<- next`. `insert "desc" --before WI-CUR --tag typing`
creates a new item, tags it, and makes WI-CUR depend on it — the "insert a blocking
prerequisite" step, in one command.
"#;


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

/// True if a parsed file declares a bundle-owned namespace (`anthill.todo` or
/// a child). The `--anthill` bundle embeds its own logic (`main.anthill` /
/// `store.anthill`); when the scanned directory is the crate dir itself those
/// sources appear as project files too, and loading them again defines every
/// bundle symbol twice. Skip them — a project supplies data, not bundle logic.
fn is_bundle_logic_file(pf: &ParsedFile) -> bool {
    // Bundle logic lives under `anthill.todo[.*]`; match the first two name
    // segments so a child namespace (e.g. `anthill.todo.store`) counts too.
    pf.items.iter().any(|item| match item {
        anthill_core::parse::ir::Item::Namespace(ns) => {
            let segs = &ns.name.segments;
            segs.len() >= 2
                && pf.symbols.name(segs[0]) == "anthill"
                && pf.symbols.name(segs[1]) == "todo"
        }
        _ => false,
    })
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

// ── WorkItem accessors ──────────────────────────────────────────

/// The slice of a WorkItem the HOST still reads: just the id, for the
/// fresh-id counter seeding. Everything else is bundle territory.
struct WorkItemInfo {
    id: String,
}

fn collect_workitems(kb: &KnowledgeBase) -> Vec<WorkItemInfo> {
    let wi_sym = match kb.try_resolve_symbol("anthill.stage0.WorkItem") {
        Some(s) => s,
        None => return Vec::new(),
    };

    let mut items = Vec::new();
    for rid in kb.rules_by_functor(wi_sym) {
        let head = kb.rule_head(rid);
        // Skip entity definition (has no string id)
        let id = match extract_named_arg(kb, head, "id").and_then(|t| extract_string(kb, t)) {
            Some(s) => s,
            None => continue,
        };
        items.push(WorkItemInfo { id });
    }
    items
}

/// All `(workitem, tag-name)` pairs from `anthill.stage0.Tag` facts.
/// Tag names attached to a work item (sorted, deduped).
/// Work item IDs carrying the given tag.
/// True if work item `id` already carries tag `name`.
/// The stage0 `Tag` entity must be defined in the project's domain for tag
/// facts to resolve on reload. Returns true if present; otherwise prints a
/// remediation error and returns false.
// ── Command implementations ─────────────────────────────────────

/// Topologically order a set of work item IDs by the dependency graph:
/// if item B (transitively) depends on item A, then A comes before B.
/// Independent items are ordered by id for a deterministic sequence.
/// Reachability is computed over the *full* graph, so two tagged items
/// are ordered correctly even when the dependency path between them runs
/// through untagged items.
/// `list --tag <name>`: the named-list sequence view. Items are shown in
/// dependency (topological) order with status; the first undelivered item
/// whose dependencies are all satisfied is marked `<- next` (the ticket the
/// build loop would pick), and items with unmet deps show `(blocked: …)`.
// ── Term manipulation helpers ───────────────────────────────────

/// Find the `fact ...()` block in source files whose body contains the given id.
/// Returns (file_path, source_text, block_start, block_end).
/// Byte index just past the closing `)` of the `fact ...(...)` block
/// starting at `fact_start`. The depth counter ignores `(` / `)` inside
/// string literals and `--` / `{- -}` comments, so an unbalanced paren
/// in a description doesn't desync the scan. Returns `None` if no
/// closing paren is reached — the caller must bail rather than retry
/// at the same offset.
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

/// A `Tag` fact attaching `name` to work item `id`. Field order is fixed
/// here for readable source; the loader resolves named args by field name.
/// Render the trailing " [tags: a, b]" note (empty when there are no tags).
/// Append a WorkItem block (plus a Tag fact per tag) for the given id.
/// Allocate the next id, append a new WorkItem (plus any tag facts), and return
/// its id. Returns None on error (already reported). Shared by `add` and `insert`.
// ── Tag / Insert commands ───────────────────────────────────────

/// Remove the first `fact Tag(...)` block matching both `workitem: "<id>"`
/// and `name: "<name>"`. Returns Ok(true) if one was removed.
/// `insert <description> --before <id>`: create a new work item, tag it,
/// and make `<id>` depend on it — placing the new item earlier in any
/// dependency-ordered sequence (the build loop's "insert prerequisite").
// ── Entry point ─────────────────────────────────────────────────

fn main() -> ExitCode {
    // WI-009 cutover: the anthill bundle IS the CLI. `--anthill` was the
    // opt-in flag while the port was partial — accepted and ignored for
    // back-compat with scripts that still pass it.
    let mut raw_args: Vec<String> = std::env::args().collect();
    if let Some(idx) = raw_args.iter().position(|a| a == "--anthill") {
        raw_args.remove(idx);
    }
    raw_args.remove(0);
    run_anthill_bundle(&raw_args)
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
    use anthill_core::eval::{builtins, EvalError, Interpreter, Value};
    use anthill_core::kb::load::NullResolver;

    // `init` runs before any KB exists — it scaffolds the project's
    // anthill-todo/ directory. Reuse the legacy implementation; once
    // there's a project to load, the bundle takes over.
    if argv.first().map(|s| s.as_str()) == Some("init") {
        // `init --name <name>` (the legacy clap flag) or `init <name>`.
        let name = match argv.get(1).map(|s| s.as_str()) {
            Some("--name") => argv.get(2).map(|s| s.as_str()),
            other => other,
        };
        run_init(name);
        return ExitCode::SUCCESS;
    }

    // `skill` is a static doc print — served host-side so the output stays
    // byte-identical to the legacy CLI (YAML frontmatter included; the
    // Claude Code skill installation parses it) and no KB load is paid.
    if argv.first().map(|s| s.as_str()) == Some("skill") {
        print!("{}", SKILL_MD);
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
                if is_bundle_logic_file(&parsed) { continue; }
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
    // directory. `SingleFile("workitems.anthill")` matches the legacy
    // on-disk layout: every runtime-persisted fact lands in the same
    // workitems.anthill the native CLI appends to (`Flat` would write a
    // separate facts.anthill — proposal 007's custom-persistence
    // conventions exist precisely so the store can target the project's
    // real file).
    let store_root = scan_dir(&project_dir);
    let store_root_str = store_root.to_string_lossy().to_string();
    let store_value = {
        use anthill_core::persistence::file_store::FileConvention;
        use anthill_core::persistence::indexed_file_store::IndexedFileStore;
        let fs_sym = interp.kb_mut().intern("FileStore");
        let single_file_sym = interp.kb_mut().intern("SingleFile");
        let root_field = interp.kb_mut().intern("root");
        let conv_field = interp.kb_mut().intern("convention");
        let file_field = interp.kb_mut().intern("file");
        let v = Value::Entity {
            functor: fs_sym,
            pos: vec![].into(),
            named: vec![
                (root_field, Value::Str(store_root_str.clone())),
                (conv_field, Value::Entity {
                    functor: single_file_sym,
                    pos: vec![].into(),
                    named: vec![(file_field, Value::Str("workitems.anthill".to_string()))].into(),
                }),
            ].into(),
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
        let mut store = IndexedFileStore::new(
            store_root,
            FileConvention::SingleFile("workitems.anthill".to_string()),
        );
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
            pos: vec![].into(),
            named: vec![
                (backend_field, store_value.clone()),
                (counter_field, Value::Int(id_counter)),
            ].into(),
        };
        let handle = interp.alloc_cell(wis_value);
        Value::Cell(handle)
    };

    // Build the chain_dicts for Main's DIRECT requires chain. Walk the
    // chain via the public direct_requires_chain API and allocate a
    // dictionary handle per entry — FileBasedWorkitemStore for the
    // WorkItemStore slot (so cmd_X dispatch lands on the impl), and
    // self-referential placeholders for every other slot. Walking
    // dynamically avoids hard-coding the chain length, which can grow
    // when Main gains more requires.
    //
    // WI-239: direct (not flat-transitive) so the count and order line
    // up with `synth_req_names(Main)` — `call_with_requirements` checks
    // `chain_dicts.len() == synth_req_names(Main).len()`, and both are
    // now the direct-require count. A transitive require is bundled
    // inside its direct parent's dict, not a top-level slot.
    let chain_dicts: smallvec::SmallVec<[_; 2]> = {
        let main_sym = interp.kb().try_resolve_symbol("anthill.todo.Main")
            .expect("anthill.todo.Main must be loaded");
        let workitemstore_sym = interp.kb()
            .try_resolve_symbol("anthill.todo.store.WorkItemStore");
        let filebased_sym = interp.kb_mut()
            .intern("anthill.todo.store.FileBasedWorkitemStore");
        let entries = anthill_core::kb::typing::direct_requires_chain(
            interp.kb_mut(), main_sym,
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
            eprintln!("error: main returned non-Int64 value: {other:?}");
            ExitCode::from(EXIT_RUNTIME)
        }
        // Top-level Error handler (WI-195): an anthill `Error` effect that
        // propagated out of Main (e.g. a `persist`/`flush` store I/O failure
        // raised through the Error effect) arrives here as `Raised`. Format
        // its payload as the canonical `error: ...` line and exit RUNTIME —
        // no Rust panic / backtrace. (Raised's own Display drops the payload,
        // so we render it here.)
        Err(EvalError::Raised { payload }) => {
            let msg = match &payload {
                Value::Str(s) => s.clone(),
                // v1: builtins raise String payloads; a user-raised entity
                // falls back to a debug rendering until a Value printer lands.
                other => format!("{other:?}"),
            };
            eprintln!("error: {msg}");
            ExitCode::from(EXIT_RUNTIME)
        }
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::from(EXIT_RUNTIME)
        }
    }
}
