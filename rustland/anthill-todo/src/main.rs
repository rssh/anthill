use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use anthill::{runner, stdlib};
use anthill_core::fs_util;
use anthill_core::kb::load;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use anthill_core::parse::error::ParseError;
use anthill_core::parse::ir::ParsedFile;

use smallvec::SmallVec;

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
anthill-todo -d "$PWD" list                              # List all work items (one line each: first line of the description)
anthill-todo -d "$PWD" list --long                       # Same listing with each item's full description text
anthill-todo -d "$PWD" list --unblocked                  # Only items whose dependencies are all satisfied
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
appears before its dependents) with status, marking the first Open item whose
dependencies are all satisfied with `<- next`. `insert "desc" --before WI-CUR --tag typing`
creates a new item, tags it, and makes WI-CUR depend on it — the "insert a blocking
prerequisite" step, in one command.
"#;

// ── File collection ─────────────────────────────────────────────
//
// WI-747: the recursive walk is `anthill_core::fs_util`; the POLICY below —
// which named paths are an error — stays here (it differs from anthill-cli's:
// this CLI has no `!path.exists()` skip, per the note below).

/// WI-744: `Err` when a named path cannot be read or is not something we can scan.
///
/// There is no `!path.exists() { continue; }` skip here, and the reason is worth
/// stating because an earlier draft of this function had one, justified by "a
/// fresh project has no `anthill-todo/` until `init`". That was fiction:
/// `scan_dir` returns `<project>/anthill-todo` only when `is_dir()` says so and
/// otherwise returns `<project>` itself, and `find_project_dir` hands it only
/// directories it has already proven exist (an explicit `-d` must `is_dir()`;
/// discovery needs a marker FILE inside). So the path always exists — and if that
/// invariant ever breaks, or a TOCTOU delete lands between the two, the honest
/// answer is a loud error, not a skip that makes `list` say "No work items found"
/// and exit 0.
fn collect_anthill_files(paths: &[PathBuf]) -> Result<Vec<PathBuf>, Vec<String>> {
    let mut files = Vec::new();
    let mut errors = Vec::new();
    for path in paths {
        if path.is_dir() {
            if let Err(e) = fs_util::collect_files_recursive(path, &["anthill"], &mut files) {
                errors.push(e);
            }
        } else if fs_util::has_extension(path, &["anthill"]) {
            files.push(path.clone());
        } else {
            errors.push(format!("not a project directory: {}", path.display()));
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    files.sort();
    files.dedup();
    Ok(files)
}

// ── Project directory discovery ──────────────────────────────────

/// The files that mark a directory as an anthill-todo PROJECT. `init` writes
/// `project.anthill`; every project accrues `workitems.anthill`. Either alone is
/// proof (a pre-versioning project predates `project.anthill`).
const PROJECT_MARKERS: [&str; 2] = ["project.anthill", "workitems.anthill"];

/// Does this directory HOLD a project, as opposed to merely being NAMED
/// `anthill-todo`?
///
/// WI-744: discovery used to accept any directory named `anthill-todo`, and any
/// directory holding some `.anthill` file. Both are too loose, and this repo is
/// the counterexample: `rustland/anthill-todo/` is this CLI's own CRATE (it holds
/// `Cargo.toml`, `src/`, and the bundle's `anthill/*.anthill` sources). Running
/// `anthill-todo list` from `rustland/` therefore resolved to the crate and
/// reported "No work items found", exit 0, while the real project sat one level
/// up with 98 of them — the long-standing "-d footgun", where a write could land
/// in the wrong tree. A warning naming the chosen directory used to be the only
/// hint; a marker test means there is nothing to hint AT, because the wrong
/// directory is no longer a candidate.
fn is_project_dir(dir: &Path) -> bool {
    PROJECT_MARKERS.iter().any(|m| dir.join(m).is_file())
}

/// Find the project directory. Checks:
/// 1. Explicit --dir flag
/// 2. `anthill-todo/` subdirectory of current dir
/// 3. Current directory itself (if it contains .anthill files)
fn find_project_dir(explicit: Option<&Path>) -> Result<PathBuf, String> {
    if let Some(dir) = explicit {
        if dir.is_dir() {
            return Ok(dir.to_path_buf());
        }
        return Err(format!(
            "project directory does not exist: {}",
            dir.display()
        ));
    }

    let cwd =
        std::env::current_dir().map_err(|e| format!("cannot determine current directory: {e}"))?;

    // Discovery is by MARKER, not by name or by "holds some .anthill file", so a
    // successful match needs no warning to caveat it (WI-744).
    let subdir = cwd.join("anthill-todo");
    if is_project_dir(&subdir) {
        return Ok(cwd);
    }
    // Already inside the project dir.
    if is_project_dir(&cwd) {
        return Ok(cwd);
    }

    Err(format!(
        "no anthill-todo project found in {cwd}.\n  \
         Looked for {cwd}/anthill-todo/{markers} and {cwd}/{markers}.\n  \
         Run `anthill-todo init`, or pass -d <project-dir>.",
        cwd = cwd.display(),
        markers = format!("{{{}}}", PROJECT_MARKERS.join(",")),
    ))
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
/// loader places in the `<global>` scope where stage0 entity names like
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
    let name = Name {
        segments,
        span: Span::default(),
    };
    let items = std::mem::take(&mut pf.items);
    pf.items.push(Item::Namespace(Namespace {
        name,
        // Synthetic ownership wrapper, not a source declaration: it has no written
        // description blocks of its own.
        descriptions: Vec::new(),
        imports: Vec::new(),
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
                && pf.symbols.local_name(segs[0]) == "anthill"
                && pf.symbols.local_name(segs[1]) == "todo"
        }
        _ => false,
    })
}

/// True if a parsed project file declares the bundle-owned `anthill.stage0`
/// domain (entity/enum defs) or the `anthill.stage0.workflow` rules. Since
/// WI-505 both ship in the binary bundle (anthill_bundle.rs), so re-loading a
/// project's own domain.anthill/rules.anthill would DOUBLE-define every
/// `anthill.stage0.WorkItem` / `claimable` etc. Skip such files — a project
/// supplies data (workitems, project config), not the standard domain/rules.
///
/// Matched on the ORIGINAL namespace, before `assign_default_namespace` wraps
/// headerless data files: a bare `workitems.anthill` / `project.anthill` has no
/// namespace item here (it only gets the synthetic `anthill.stage0` wrap
/// afterwards), so it is kept; only files that *explicitly* declare the domain
/// (`anthill.stage0`) or the workflow rules (`anthill.stage0.workflow`) match.
///
/// The skip keys on the presence of the bundle-owned *definitions* — a sort /
/// entity / enum for the domain, a `rule` for the workflow — not merely on the
/// namespace name. A file that only carries facts under an explicit
/// `namespace anthill.stage0` (unusual, but hand-authorable) defines nothing
/// that the bundle also defines, so it is kept and its data is not silently
/// dropped.
fn is_bundled_domain_or_rules(pf: &ParsedFile) -> bool {
    use anthill_core::parse::ir::Item;
    // Sort/entity/enum declarations — what a re-declared bundle domain would
    // double-define. Per parse/convert.rs: `sort`/`enum` → `Item::SortWithBody`,
    // an abstract `sort` (no body) → `Item::AbstractSort`, and the `entity`
    // sugar → `Item::Entity`. `rule` → `Item::Rule`.
    let defines_domain = |i: &Item| {
        matches!(
            i,
            Item::Entity(_) | Item::SortWithBody(_) | Item::AbstractSort(_)
        )
    };
    let defines_rule = |i: &Item| matches!(i, Item::Rule(_));
    pf.items.iter().any(|item| match item {
        Item::Namespace(ns) => {
            let segs = &ns.name.segments;
            let seg = |i: usize| pf.symbols.local_name(segs[i]);
            let is_domain_ns = segs.len() == 2 && seg(0) == "anthill" && seg(1) == "stage0";
            let is_workflow_ns = segs.len() == 3
                && seg(0) == "anthill"
                && seg(1) == "stage0"
                && seg(2) == "workflow";
            (is_domain_ns && ns.items.iter().any(defines_domain))
                || (is_workflow_ns && ns.items.iter().any(defines_rule))
        }
        _ => false,
    })
}

// ── Term helpers ────────────────────────────────────────────────

// The data-format version `init` stamps a new project's workitems.anthill with
// (`fact StoreFormat(version: N)`). MUST match the bundle's `current_store_format`
// (main.anthill), which the anthill-side version check compares stamps against;
// the `fresh init produces a clean project` test guards against divergence.
const CURRENT_STORE_FORMAT_VERSION: u32 = 1;

// WI-505: `init` no longer scaffolds a per-project domain.anthill/rules.anthill.
// The `anthill.stage0` domain and workflow rules ship bundled in the binary
// (anthill_bundle.rs), version-locked with the logic that imports them, so a
// fresh project carries no copy that could later drift out of sync with the
// grammar or domain. The data-format stamp is likewise bundle-owned and
// asserted from anthill via the store (WorkItemStore.stamp_format / `migrate`),
// never text-written here.

fn extract_named_arg(kb: &KnowledgeBase, term: TermId, field: &str) -> Option<TermId> {
    match kb.get_term(term) {
        Term::Fn { named_args, .. } => named_args
            .iter()
            .find(|(s, _)| kb.local_name_of(*s) == field)
            .map(|(_, id)| *id),
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

/// Collect WorkItem ids for the fresh-id counter. `Err` means the tracker is
/// malformed (unreadable) — a FATAL condition the caller aborts on rather than
/// silently seeding the counter from a partial read (which would mint a colliding
/// id).
fn collect_workitems(kb: &KnowledgeBase) -> Result<Vec<WorkItemInfo>, String> {
    use anthill_core::eval::Value;
    use anthill_core::kb::extent::BodiedRulePolicy;

    let wi_sym = match kb.try_resolve_symbol("anthill.stage0.WorkItem") {
        Some(s) => s,
        None => return Ok(Vec::new()),
    };

    // Read WorkItem FACTS through the kb accessor (WI-773), values-first: a bodied
    // WorkItem rule is a LOUD refusal, never a phantom item. The old
    // `rules_by_functor` + `rule_head` walk head-matched a bodied rule (listing it
    // as if it were a real work item) AND panicked outright on a value-fact head.
    // The refusal is fatal — propagate it rather than degrade the counter.
    let rows = kb
        .read_facts(wi_sym, &[], BodiedRulePolicy::Refuse)
        .map_err(|e| format!("reading work items: {e}"))?;

    let mut items = Vec::new();
    for row in rows {
        // A WorkItem fact head hash-conses to a term. A value-fact carrier
        // (Value::Node/Entity) is not expected for WorkItem and carries no readable
        // term id — surface it loudly (the old `rule_head` walk PANICKED here)
        // rather than drop it silently, but don't abort the whole read for one
        // anomalous row.
        let Value::Term { id: head, .. } = row else {
            eprintln!("warning: skipping a WorkItem fact with an unexpected non-term head");
            continue;
        };
        // A row without a string `id` is the entity-ctor definition (its `id` slot
        // is a type, not a literal); skip it, as the pre-migration walk did.
        let id = match extract_named_arg(kb, head, "id").and_then(|t| extract_string(kb, t)) {
            Some(s) => s,
            None => continue,
        };
        items.push(WorkItemInfo { id });
    }
    Ok(items)
}

/// All `(workitem, tag-name)` pairs from `anthill.stage0.Tag` facts.
/// Tag names attached to a work item (sorted, deduped).
/// Work item IDs carrying the given tag.
/// The stage0 `Tag` entity must be defined in the project's domain for tag
/// facts to resolve on reload. Returns true if present; otherwise prints a
/// remediation error and returns false.
/// Topologically order a set of work item IDs by the dependency graph:
/// if item B (transitively) depends on item A, then A comes before B.
/// Independent items are ordered by id for a deterministic sequence.
/// Reachability is computed over the *full* graph, so two tagged items
/// are ordered correctly even when the dependency path between them runs
/// through untagged items.
// ── The declared store (WI-830) ─────────────────────────────────

use anthill_core::eval::{value_functor, Interpreter, Value};
use anthill_core::persistence::file_store::FileConvention;
use anthill_core::persistence::indexed_file_store::IndexedFileStore;
use anthill_core::persistence::item_per_file_store::{ItemFields, ItemPerFileStore, LayoutFault};
use anthill_core::persistence::Store;

/// A project file paired with its parsed IR, so the store can associate each fact's
/// RuleId with its byte range on disk.
struct ProjectFile {
    path: PathBuf,
    parsed: ParsedFile,
}

/// A built backend, before it is handed to the mirror registry.
///
/// It exists as a named value rather than an immediate `Box<dyn Store>` because
/// `fsck` has business with the CONCRETE store — the layout checks and the
/// repair are `ItemPerFileStore`'s, and `Store` neither has them nor should.
/// Once the checks have run the box goes in and this value is gone.
enum BuiltStore {
    Indexed(IndexedFileStore),
    ItemPerFile(ItemPerFileStore),
}

impl BuiltStore {
    /// The disagreements between the on-disk layout and the facts (§10), for the
    /// STARTUP GATE. A backend whose layout means nothing has none to report —
    /// there is no directory claiming to be a status — so an empty answer here
    /// says "nothing to check", which is the right thing to say to a gate.
    fn layout_faults(&self) -> Vec<LayoutFault> {
        match self {
            BuiltStore::Indexed(_) => Vec::new(),
            BuiltStore::ItemPerFile(s) => s.layout_faults(),
        }
    }

    /// The same checks asked by `fsck`, where an empty answer would be a LIE.
    ///
    /// The gate above and this differ deliberately: silence is a correct answer
    /// to "is anything wrong?" and a wrong answer to "check this layout", which a
    /// shared-file store cannot do at all. Reporting `layout ok` there is the
    /// silent skip the repo's principles forbid — and it was inconsistent besides,
    /// since `--fix` on the same project refused (found in review).
    fn checked_layout(&self) -> Result<Vec<LayoutFault>, String> {
        match self {
            BuiltStore::Indexed(_) => Err(format!(
                "this project's store is `{INDEXED_FILE_STORE}`, which holds every row in \
                 one file — there is no directory-per-state layout for `fsck` to check or \
                 repair"
            )),
            BuiltStore::ItemPerFile(s) => Ok(s.layout_faults()),
        }
    }

    fn repair_paths(&mut self) -> Result<Vec<(PathBuf, PathBuf)>, String> {
        match self {
            BuiltStore::Indexed(_) => Err(format!(
                "this project's store is `{INDEXED_FILE_STORE}`, which holds every row in \
                 one file — there is no directory-per-state layout for `fsck` to check or \
                 repair"
            )),
            BuiltStore::ItemPerFile(s) => s.repair_paths().map_err(|e| e.to_string()),
        }
    }

    fn into_boxed(self) -> Box<dyn Store> {
        match self {
            BuiltStore::Indexed(s) => Box::new(s),
            BuiltStore::ItemPerFile(s) => Box::new(s),
        }
    }
}

/// A built store together with everything the registration still needs.
struct DeclaredStore {
    store: BuiltStore,
    /// The store VALUE the anthill side receives — the declared term with `root`
    /// resolved to the absolute path.
    value: Value,
    covers: Vec<String>,
}

/// Build the store the project's `ExtentBinding` declares.
///
/// THE HOST'S JOB IS THE FACTORY, AND ONLY THE FACTORY (proposal 057 §"Configuration &
/// bootstrap"). A backend is native code, so declarative configuration chooses AMONG the
/// backends compiled into this binary; it cannot introduce new ones. Everything else —
/// which functors are held, in which role, under which convention — comes from the
/// `.anthill` file.
///
/// A PROJECT THAT DECLARES NOTHING GETS THE DEFAULT, and the default is a BINDING, not a
/// second implementation. `PROJECT_MARKERS` accepts a directory holding nothing but
/// `workitems.anthill` — a zero-config tracker is a supported shape, and
/// `setup_domainless_project` tests it — so refusing an absent binding would delete a
/// documented capability, not tighten one. What matters is that there is one path from a
/// binding to a store: `default_binding` builds the same declaration `init` scaffolds, and
/// everything downstream cannot tell the two apart.
///
/// This is a default, not a fallback in the sense CLAUDE.md forbids: nothing failed and
/// nothing is being hidden. A binding that is PRESENT and wrong is still loud.
///
/// Carries out the store VALUE the anthill side receives — the declared term with its
/// `root` resolved to the absolute path. The registration key is computed from THAT
/// value, and the same value is what the bundle's `wis(backend:, …)` cell carries, so
/// both sides of the dispatch agree by construction.
///
/// BUILDING AND REGISTERING ARE SPLIT (WI-1114) because `fsck` sits between them: the
/// layout checks belong to the concrete backend, and once the store is boxed into the
/// mirror registry the host cannot ask it anything again.
fn build_declared_store(
    interp: &mut Interpreter,
    store_root: &Path,
    project_items: &[ProjectFile],
    project_results: &[load::LoadResult],
) -> Result<DeclaredStore, String> {
    use anthill_core::kb::extent::ExtentRole;

    let bindings = interp
        .kb()
        .extent_bindings()
        .map_err(|e| format!("reading the project's extent bindings: {e}"))?;

    let binding = match bindings.len() {
        1 => bindings.into_iter().next().expect("length checked"),
        0 => default_binding(interp)?,
        n => {
            return Err(format!(
                "this project declares {n} extent bindings; anthill-todo holds its work \
                 items in one store, so exactly one is expected"
            ))
        }
    };

    if binding.role != ExtentRole::Mirror {
        return Err(
            "this project declares its store as an extent OWNER. anthill-todo loads every \
             work item at startup and answers reads from the KB, so its store is a \
             durability mirror; an owner would have to serve reads from its own query \
             engine. Write `role: mirror()`."
                .to_string(),
        );
    }

    // The one native step: the declared store term names a backend this binary must
    // already have. Adding one is an arm HERE plus a `provides` block on the anthill
    // side — which is exactly the WI-437 shape, and exactly why the rest of this is no
    // longer hardcoded.
    let store_functor = value_functor(interp.kb(), &binding.store)
        .ok_or_else(|| "the declared store names no backend".to_string())?;
    // By resolved SYMBOL, never by name text. A `ends_with("IndexedFileStore")` test read
    // naturally and accepted `GitHubIndexedFileStore` — a functor defined nowhere — as the
    // local file store, so a project asking for a backend this build does not have got a
    // silent write into its own directory instead of the refusal. That is precisely the
    // WI-437 case this guard exists for (found in review, driven by
    // `a_lookalike_backend_name_is_refused`).
    let backend = resolve_backend(interp, store_functor)?;

    let store_root = declared_root(interp, &binding.store, store_root)?;
    let store = match backend {
        Backend::Indexed => {
            let convention = declared_convention(interp, &binding.store)?;
            let mut store = IndexedFileStore::new(store_root.clone(), convention);
            // Seed the source map: pair each project file's fact RuleIds (in source
            // order) with the byte ranges of the corresponding parsed `Item::Fact`
            // spans, so a retract of a source-loaded RuleId knows which file and which
            // bytes to drop.
            for (file, result) in project_items.iter().zip(project_results.iter()) {
                let spans = file.parsed.fact_spans();
                for (rule_id, span) in result.fact_rule_ids.iter().zip(spans.iter()) {
                    store.record_source(*rule_id, file.path.clone(), *span);
                }
            }
            BuiltStore::Indexed(store)
        }
        Backend::ItemPerFile => {
            // The SAME two inputs, associated differently: this backend addresses a row
            // by the file it lives in, so it takes each file's text and cuts it into
            // blocks, and keeps no byte offsets at all — a state change rewrites the
            // whole file at a new path, and an offset would not survive that.
            let mut store = ItemPerFileStore::new(store_root.clone(), declared_fields(interp, &binding.store)?);
            for (file, result) in project_items.iter().zip(project_results.iter()) {
                let source = fs::read_to_string(&file.path)
                    .map_err(|e| format!("{}: {e}", file.path.display()))?;
                let rows: Vec<_> = result
                    .fact_rule_ids
                    .iter()
                    .copied()
                    .zip(file.parsed.fact_spans())
                    .collect();
                store
                    .record_file(interp.kb(), file.path.clone(), &source, &rows)
                    .map_err(|e| format!("reading the project's layout: {e}"))?;
            }
            BuiltStore::ItemPerFile(store)
        }
    };

    // The runtime store value is the declared one with `root` made absolute: a config
    // file names a directory relative to itself, and the process needs the real path.
    let value = with_absolute_root(interp, &binding.store, store_functor, &store_root)?;
    let covers: Vec<String> = binding
        .covers
        .iter()
        .map(|s| interp.kb().qualified_name_of(*s).to_string())
        .collect();
    Ok(DeclaredStore {
        store,
        value,
        covers,
    })
}

/// Hand the built store to the mirror registry, and return the value the bundle sees.
fn register_declared_store(
    interp: &mut Interpreter,
    declared: DeclaredStore,
) -> Result<Value, String> {
    let key = interp
        .store_canonical_key(&declared.value)
        .map_err(|e| format!("computing the store key: {e}"))?;
    let covers_ref: Vec<&str> = declared.covers.iter().map(String::as_str).collect();
    interp
        .register_mirror(key, declared.store.into_boxed(), &covers_ref)
        .map_err(|e| format!("registering the declared store: {e}"))?;
    Ok(declared.value)
}

/// `anthill-todo fsck [--fix]` — check the on-disk layout against the facts, and
/// optionally move each misplaced file to the path its own fact names.
///
/// The directory is an index and the fact is the truth (design §4), so the repair
/// direction is settled: the FACT wins. What `--fix` will not do is choose between
/// two files claiming one id — that is a real disagreement about which is the item,
/// and only whoever interrupted the move knows.
fn run_fsck(store: &mut BuiltStore, args: &[String]) -> i32 {
    let mut fix = false;
    for arg in args {
        match arg.as_str() {
            "--fix" => fix = true,
            // `fsck` is in the bundle's command registry so `--help` finds it, so
            // asking it for its own help is a likely first move (found in review).
            "--help" | "-h" => {
                println!("{FSCK_USAGE}");
                return 0;
            }
            other => {
                eprintln!("error: unknown fsck option `{other}`");
                eprintln!("{FSCK_USAGE}");
                return runner::EXIT_COMPILE;
            }
        }
    }

    // Asked before anything is done, so that a backend with no layout to check
    // refuses BOTH the read-only and the repairing form, rather than answering
    // one with silence and the other with a refusal.
    if let Err(e) = store.checked_layout() {
        eprintln!("error: {e}");
        return runner::EXIT_RUNTIME;
    }

    if fix {
        match store.repair_paths() {
            Ok(moves) => {
                for (from, to) in &moves {
                    println!("moved {} -> {}", from.display(), to.display());
                }
                if moves.is_empty() {
                    println!("no misplaced files");
                }
            }
            Err(e) => {
                eprintln!("error: {e}");
                return runner::EXIT_RUNTIME;
            }
        }
    }

    // Re-asked after a repair, so what is reported is what is still true.
    let faults = match store.checked_layout() {
        Ok(faults) => faults,
        Err(e) => {
            eprintln!("error: {e}");
            return runner::EXIT_RUNTIME;
        }
    };
    if faults.is_empty() {
        println!("layout ok");
        return 0;
    }
    let mut blocking = 0usize;
    for fault in &faults {
        if fault.blocking() {
            blocking += 1;
            eprintln!("error: {fault}");
        } else {
            eprintln!("warning: {fault}");
        }
    }
    if blocking > 0 && !fix {
        eprintln!("run `anthill-todo fsck --fix` to repair what can be repaired mechanically");
    }
    if blocking > 0 {
        runner::EXIT_RUNTIME
    } else {
        0
    }
}

const FSCK_USAGE: &str = "\
usage: anthill-todo fsck [--fix]

Check the on-disk layout against the facts: that each item's file sits at the path
its own `id` and `status` name, that no id is held twice, and that every feedback
or tag row is in its item's file.

  --fix   move each misplaced file to the path its own fact names (the fact wins).
          It will not choose between two files claiming one id, split a file
          holding several items, or guess where an unreadable row belongs.";

/// The backends this build compiles in.
enum Backend {
    Indexed,
    ItemPerFile,
}

/// Which compiled-in backend a declared store functor names — the whole of the
/// host's remaining authority over storage, and a HARD REFUSAL when the answer is
/// none. Falling back to a local file store would silently write a project's rows
/// somewhere it did not ask for (design §3.1).
fn resolve_backend(
    interp: &Interpreter,
    store_functor: anthill_core::intern::Symbol,
) -> Result<Backend, String> {
    for (name, backend) in [
        (INDEXED_FILE_STORE, Backend::Indexed),
        (ITEM_PER_FILE_STORE, Backend::ItemPerFile),
    ] {
        let sym = interp
            .kb()
            .try_resolve_symbol(name)
            .ok_or_else(|| format!("the persistence substrate is not loaded: `{name}`"))?;
        if store_functor == sym {
            return Ok(backend);
        }
    }
    Err(format!(
        "anthill-todo has no backend for the declared store `{}`; this build provides \
         {INDEXED_FILE_STORE} and {ITEM_PER_FILE_STORE}",
        interp.kb().qualified_name_of(store_functor),
    ))
}

/// The three field names `ItemPerFileStore` routes on, read off the declaration.
///
/// `anthill-core`'s persistence layer is domain-neutral, so `status` / `id` /
/// `workitem` are not ITS knowledge — they are stage0's spelling, and they arrive
/// here from the project's own binding. A missing one is a refusal: there is no
/// default that could be right for a domain the store has never heard of.
fn declared_fields(interp: &Interpreter, store: &Value) -> Result<ItemFields, String> {
    let read = |field: &str| -> Result<String, String> {
        let value = interp
            .kb()
            .row_field(store, field)
            .ok_or_else(|| format!("the declared store has no `{field}` field"))?;
        string_field(interp, &value, field)
    };
    Ok(ItemFields::new(
        read("status_field")?,
        read("id_field")?,
        read("ref_field")?,
    ))
}

/// A `String`-valued field of a declared store, in either carrier a declaration can
/// arrive in: a host-built `Value::Str` or the hash-consed literal a source-written
/// fact carries.
fn string_field(interp: &Interpreter, value: &Value, field: &str) -> Result<String, String> {
    match value {
        Value::Str(s) => Ok(s.clone()),
        Value::Term { id, .. } => {
            use anthill_core::kb::term::TermSource;
            match interp.kb().term(*id) {
                Term::Const(Literal::String(s)) => Ok(s.clone()),
                other => Err(format!("`{field}` must be a string, got {other:?}")),
            }
        }
        other => Err(format!("`{field}` must be a string, got {other:?}")),
    }
}

/// The binding a project that declares none is treated as having: an `IndexedFileStore`
/// over `workitems.anthill` in the project directory, mirroring the four functors the
/// bundle persists. Written as a VALUE rather than as a separate construction path, so a
/// defaulted project and a declaring one differ in exactly one thing — where the binding
/// came from — and share every line after this.
///
/// Its text twin is [`EXAMPLE_BINDING`], which `init` scaffolds; the two must agree, and
/// `default_matches_the_scaffolded_binding` measures that they do.
fn default_binding(
    interp: &mut Interpreter,
) -> Result<anthill_core::kb::extent::ExtentBindingDecl, String> {
    use anthill_core::kb::extent::{ExtentBindingDecl, ExtentRole};

    let store_functor = interp
        .kb()
        .try_resolve_symbol("anthill.persistence.filesystem.IndexedFileStore")
        .ok_or_else(|| {
            "the persistence substrate is not loaded: \
             `anthill.persistence.filesystem.IndexedFileStore` does not resolve"
                .to_string()
        })?;
    let single_file = interp
        .kb()
        .try_resolve_symbol("anthill.persistence.filesystem.FileConvention.single_file")
        .ok_or_else(|| {
            "the persistence substrate is not loaded: `FileConvention.single_file` does \
             not resolve"
                .to_string()
        })?;
    let mut covers = Vec::with_capacity(DEFAULT_COVERAGE.len());
    for name in DEFAULT_COVERAGE {
        covers.push(
            interp
                .kb()
                .try_resolve_symbol(name)
                .ok_or_else(|| format!("the stage0 domain is not loaded: `{name}` does not resolve"))?,
        );
    }

    let root_field = interp.kb_mut().intern("root");
    let convention_field = interp.kb_mut().intern("convention");
    let file_field = interp.kb_mut().intern("file");
    // `root` is a placeholder: `with_absolute_root` replaces it with the real path, the
    // same as it does for a declared binding.
    let store = Value::Entity {
        functor: store_functor,
        pos: vec![].into(),
        named: vec![
            (root_field, Value::Str(".".to_string())),
            (
                convention_field,
                Value::Entity {
                    functor: single_file,
                    pos: vec![].into(),
                    named: vec![(file_field, Value::Str(DEFAULT_STORE_FILE.to_string()))].into(),
                },
            ),
        ]
        .into(),
    };
    Ok(ExtentBindingDecl {
        store,
        role: ExtentRole::Mirror,
        covers,
    })
}

/// The functors the bundle persists (`store.anthill`: commit / commit_feedback /
/// tag_item / stamp_format), and so the ones the default binding covers.
const DEFAULT_COVERAGE: [&str; 4] = [
    "anthill.stage0.WorkItem",
    "anthill.stage0.Feedback",
    "anthill.stage0.Tag",
    "anthill.stage0.StoreFormat",
];

/// The file the default store writes to — the same one the loader reads.
const DEFAULT_STORE_FILE: &str = "workitems.anthill";

/// The `ExtentBinding` `init` scaffolds. Text twin of [`default_binding`].
const EXAMPLE_BINDING: &str = "\
fact anthill.persistence.ExtentBinding(
  store: anthill.persistence.filesystem.IndexedFileStore(
    root: \".\",
    convention: anthill.persistence.filesystem.FileConvention.single_file(
      file: \"workitems.anthill\")),
  role: anthill.persistence.ExtentRole.mirror(),
  covers: [WorkItem, Feedback, Tag, StoreFormat])";

/// The qualified names of the backends this build provides.
const INDEXED_FILE_STORE: &str = "anthill.persistence.filesystem.IndexedFileStore";
const ITEM_PER_FILE_STORE: &str = "anthill.persistence.filesystem.ItemPerFileStore";

/// The directory the declared store writes to.
///
/// THE MIRROR MUST WRITE THE FILES THE LOADER READ. anthill-todo scans one directory, parses
/// what it finds, and seeds the store's source map with those files' byte ranges; a store
/// rooted anywhere else would retract by span against files nobody loaded and append rows
/// the next run never sees. So `root` has exactly one correct value here — the scanned
/// directory — and this refuses any other rather than accepting it and writing elsewhere.
///
/// It is checked rather than ignored because ignoring it is what the first cut did: the
/// field was decorative, `root: "elsewhere"` wrote to the project directory anyway, and
/// nothing said so (found in review). Honouring it properly is not open to this host —
/// the root would have to be known BEFORE the load that reads the file declaring it — so
/// the honest options were "refuse" and "silently ignore", and the repo picks refuse.
fn declared_root(
    interp: &Interpreter,
    store: &Value,
    scanned: &Path,
) -> Result<std::path::PathBuf, String> {
    let declared = interp
        .kb()
        .row_field(store, "root")
        .ok_or_else(|| "the declared store has no `root` field".to_string())?;
    let text = string_field(interp, &declared, "root")?;
    if text == "." {
        return Ok(scanned.to_path_buf());
    }
    Err(format!(
        "the declared store roots at `{text}`, but anthill-todo loads its work items from \
         {} and its store must write the same files it read. Write `root: \".\"`.",
        scanned.display()
    ))
}

/// Decode the declared `convention` field into the Rust `FileConvention` it names.
/// Matched by LOCAL name off a resolved functor rather than by qualified string, so the
/// two enums stay tied by their variant names (WI-830 reconciled them).
fn declared_convention(interp: &Interpreter, store: &Value) -> Result<FileConvention, String> {
    let conv = interp
        .kb()
        .row_field(store, "convention")
        .ok_or_else(|| "the declared store has no `convention` field".to_string())?;
    let functor = value_functor(interp.kb(), &conv)
        .ok_or_else(|| "the declared `convention` names no variant".to_string())?;
    match interp.kb().local_name_of(functor) {
        "flat" => Ok(FileConvention::Flat),
        "by_domain" => Ok(FileConvention::ByDomain),
        "single_file" => {
            let file = interp.kb().row_field(&conv, "file").ok_or_else(|| {
                "`single_file` needs its `file` field: single_file(file: \"…\")".to_string()
            })?;
            match file {
                Value::Str(s) => Ok(FileConvention::SingleFile(s)),
                // A source-written `single_file(file: "…")` carries its string as a
                // hash-consed literal, not a `Value::Str`.
                Value::Term { id, .. } => {
                    use anthill_core::kb::term::{Literal, Term, TermSource};
                    match interp.kb().term(id) {
                        Term::Const(Literal::String(s)) => {
                            Ok(FileConvention::SingleFile(s.clone()))
                        }
                        other => Err(format!(
                            "`single_file(file:)` must be a string, got {other:?}"
                        )),
                    }
                }
                other => Err(format!(
                    "`single_file(file:)` must be a string, got {other:?}"
                )),
            }
        }
        other => Err(format!(
            "unknown file convention `{other}`; this build implements flat, by_domain \
             and single_file"
        )),
    }
}

/// The runtime store value: the declared backend and convention, with `root` resolved to
/// the absolute path the process must actually use.
///
/// Rebuilt as a `Value::Entity` rather than edited in place, because the declared store is
/// a hash-consed `Value::Term` (a source-loaded fact) and a `Term` is immutable. That is
/// sound for the dispatch this value serves: the persist/flush registry keys on the
/// CANONICAL FORM of the value the host registers, and this same value is what the
/// bundle's `wis(backend:, …)` cell carries, so both sides render one string.
///
/// The rebuild carries EVERY declared field, replacing only `root` — which is total for
/// any backend rather than for the one that happened to be first. It used to name
/// `root` and `convention` and nothing else, on the reasoning that `IndexedFileStore`
/// declares exactly those two; `ItemPerFileStore` declares four, and the second backend
/// is precisely the moment a per-backend field list starts silently dropping
/// configuration (WI-1114).
fn with_absolute_root(
    interp: &mut Interpreter,
    store: &Value,
    store_functor: anthill_core::intern::Symbol,
    absolute: &Path,
) -> Result<Value, String> {
    let mut named: Vec<(anthill_core::intern::Symbol, Value)> = Vec::new();
    let mut saw_root = false;
    for (label, value) in declared_field_values(interp, store)? {
        // Field symbols are minted rather than taken from the term: canonicalization
        // renders named args by LOCAL name, so a freshly interned `root` and the
        // declared one are the same key. The FUNCTOR is the declared one, since that is
        // what the value is OF.
        let sym = interp.kb_mut().intern(&label);
        if label == "root" {
            saw_root = true;
            named.push((sym, Value::Str(absolute.to_string_lossy().to_string())));
        } else {
            named.push((sym, value));
        }
    }
    if !saw_root {
        return Err("the declared store has no `root` field".to_string());
    }
    Ok(Value::Entity {
        functor: store_functor,
        pos: vec![].into(),
        named: named.into(),
    })
}

/// Every named field of a declared store, by local name, in declaration order — in
/// either carrier a declaration arrives in (a source-loaded `Value::Term`, or the
/// `Value::Entity` [`default_binding`] builds).
fn declared_field_values(
    interp: &Interpreter,
    store: &Value,
) -> Result<Vec<(String, Value)>, String> {
    match store {
        Value::Entity { named, .. } => Ok(named
            .iter()
            .map(|(s, v)| (interp.kb().local_name_of(*s).to_string(), v.clone()))
            .collect()),
        Value::Term { id, .. } => {
            use anthill_core::kb::term::TermSource;
            let Term::Fn { named_args, .. } = interp.kb().term(*id) else {
                return Err("the declared store is not a store term".to_string());
            };
            Ok(named_args
                .iter()
                .map(|(label, value)| {
                    (
                        interp.kb().local_name_of(*label).to_string(),
                        Value::term(*value),
                    )
                })
                .collect())
        }
        other => Err(format!(
            "the declared store must be a store term, got {other:?}"
        )),
    }
}

// ── Init command ────────────────────────────────────────────────

/// Scaffold a fresh project's `anthill-todo/` directory.
///
/// `base_dir` is the explicit `-d <dir>` when given, else `None` (⇒ cwd). WI-748:
/// init used to hardcode the cwd and ignore `-d` entirely — the one subcommand
/// that decided WHERE by position instead of by the flag every other command
/// routes through `find_project_dir`. `-d X init` from any other directory then
/// dropped the scaffold wherever the user stood, and the success message named
/// no path to reveal it. Returns the process exit code (loud, non-zero, on the
/// refusal guards).
fn run_init(base_dir: Option<&Path>, project_name: Option<&str>) -> i32 {
    let cwd = std::env::current_dir().expect("cannot determine current directory");
    let base = base_dir.unwrap_or(cwd.as_path());

    // An explicit -d must name an existing directory — the same contract as
    // `find_project_dir`'s explicit-dir arm, so a typo'd `-d` errors rather than
    // conjuring a phantom tree (the write-side twin of the WI-744 discovery bug).
    if base_dir.is_some() && !base.is_dir() {
        eprintln!(
            "error: project directory does not exist: {}",
            base.display()
        );
        return runner::EXIT_RUNTIME;
    }

    // Resolve base to an absolute, symlink-free path — for a meaningful default
    // project name and, above all, an ABSOLUTE success message even when -d is
    // relative (`-d ../foo`). `base` is a directory we just proved exists, so a
    // canonicalize failure is a genuine I/O fault (a permission wall, a TOCTOU
    // delete). Surface it loudly rather than degrade to a non-normalized
    // `cwd.join(base)`: that fallback would silently break the absolute/
    // symlink-free guarantee AND feed the wrong directory to the is_project_dir
    // guard below (CLAUDE.md: avoid fallbacks, prefer a loud error over a silent
    // skip).
    let abs_base = match fs::canonicalize(base) {
        Ok(p) => p,
        Err(e) => {
            eprintln!(
                "error: cannot resolve project directory {}: {e}",
                base.display()
            );
            return runner::EXIT_RUNTIME;
        }
    };
    let dir = abs_base.join("anthill-todo");

    // Refuse to scaffold over an existing project rather than silently
    // re-scaffolding: either an `anthill-todo/` subdir is already here, or `base`
    // itself already carries the marker files (the flat "cwd IS the project"
    // layout `find_project_dir` also accepts).
    if dir.exists() {
        eprintln!("error: {} already exists", dir.display());
        return runner::EXIT_RUNTIME;
    }
    if is_project_dir(&abs_base) {
        eprintln!(
            "error: {} is already an anthill-todo project",
            abs_base.display()
        );
        return runner::EXIT_RUNTIME;
    }

    let name = project_name.map(str::to_string).unwrap_or_else(|| {
        abs_base
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("my-project")
            .to_string()
    });

    fs::create_dir_all(&dir).expect("cannot create anthill-todo/");

    // No domain.anthill / rules.anthill: the standard anthill.stage0 domain and
    // workflow rules ship bundled in the binary (WI-505), so a fresh project
    // has no per-project copy that could drift out of sync with the grammar.

    // The scaffold carries the store binding (WI-830) so a fresh project SHOWS its
    // configuration rather than inheriting an invisible one. It is not required — a
    // project without it gets `default_binding`, which this text must match — but a
    // scaffolded default that nobody can see is a default nobody edits.
    let project = format!(
        "-- Project configuration\n\nfact Project(\n  name: \"{name}\",\n  language: \"rust\",\n  build: \"cargo\",\n  tools: [\"cargo-test\"])\n\n\
         -- Which store holds these work items, and in which role (proposal 057).\n\
         -- `mirror`: every file here is loaded at startup and the KB answers reads, with\n\
         -- the store as the write-through durability leg. `root: \".\"` is this directory.\n\
         {EXAMPLE_BINDING}\n"
    );
    fs::write(dir.join("project.anthill"), project).expect("write project.anthill");

    let workitems =
        format!("-- Work items\n\nfact StoreFormat(version: {CURRENT_STORE_FORMAT_VERSION})\n\n");
    fs::write(dir.join("workitems.anthill"), workitems).expect("write workitems.anthill");

    // The absolute path, not a bare `anthill-todo/`: a wrong-place write must be
    // visible in the output even when -d is right. The old message named no path
    // and so could not have revealed WI-748 even to someone staring at it.
    println!("created {} with:", dir.display());
    println!("  project.anthill   — project configuration");
    println!("  workitems.anthill — work items (empty)");
    println!("(the anthill.stage0 domain + workflow rules ship bundled with anthill-todo)");
    0
}

// `migrate` is served by the anthill bundle (main.anthill `cmd_migrate`): it
// stamps workitems.anthill with a `StoreFormat` fact THROUGH the store, so the
// version-format logic stays in the bundle rather than host text-writing (WI-434).

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
    ExitCode::from(run_anthill_bundle(&raw_args) as u8)
}

// ── Anthill-bundle entry point ──────────────────────────────────

// Exit-code conventions (EXIT_COMPILE / EXIT_RUNTIME / EXIT_OUT_OF_RANGE), the
// builtins/effect-handler registration, and the `main`-result → exit-code
// mapping are shared with anthill-cli via `anthill::runner`. This entry point
// returns the raw `i32` exit code; `main` wraps it in `ExitCode` once.

fn run_anthill_bundle(argv: &[String]) -> i32 {
    use anthill_core::eval::{Interpreter, Value};
    use anthill_core::kb::load::NullResolver;

    // Strip the global flags FIRST (`-d <dir>` / `--dir`, `--agent <name>`,
    // `=`-joined forms included) so the host interceptions below and the
    // bundle dispatch both see only the subcommand argv — the documented
    // invocation form puts `-d "$PWD"` BEFORE the subcommand, so an
    // argv[0]-only check would miss `-d X init`/`-d X skill` entirely.
    // The bundle's parse_argv doesn't know about globals yet — once
    // OperationSpec gains a `globals` field this can move into anthill code.
    let mut bundle_argv: Vec<String> = Vec::with_capacity(argv.len());
    let mut explicit_dir: Option<PathBuf> = None;
    let mut agent: String = "user".to_string();
    // `--version` / `-V` is a global flag (WI-160) — recognised only ahead of
    // the subcommand (e.g. `anthill-todo --version`, `-d X --version`), i.e.
    // while no subcommand token has been pushed yet (`bundle_argv` empty).
    // Once a subcommand is seen, a literal `--version` / `-V` token is data
    // (e.g. a work-item description word) and passes through to the bundle —
    // otherwise a multi-word `add … --version …` would be hijacked. An exact
    // `version` subcommand token is handled after the loop.
    let mut want_version = false;
    let mut iter = argv.iter();
    while let Some(arg) = iter.next() {
        if (arg == "--version" || arg == "-V") && bundle_argv.is_empty() {
            want_version = true;
        } else if arg == "-d" || arg == "--dir" {
            match iter.next() {
                Some(dir) => explicit_dir = Some(PathBuf::from(dir)),
                None => {
                    eprintln!("error: {arg} requires a value");
                    return runner::EXIT_COMPILE;
                }
            }
        } else if let Some(dir) = arg
            .strip_prefix("-d=")
            .or_else(|| arg.strip_prefix("--dir="))
        {
            explicit_dir = Some(PathBuf::from(dir));
        } else if arg == "--agent" {
            match iter.next() {
                Some(a) => agent = a.clone(),
                None => {
                    eprintln!("error: --agent requires a value");
                    return runner::EXIT_COMPILE;
                }
            }
        } else if let Some(a) = arg.strip_prefix("--agent=") {
            agent = a.to_string();
        } else if arg == "--stdlib" || arg.starts_with("--stdlib=") {
            eprintln!(
                "error: the --stdlib flag was removed in the WI-009 cutover — \
                 the stdlib is embedded in the binary (rebuild to pick up stdlib edits)"
            );
            return runner::EXIT_COMPILE;
        } else {
            bundle_argv.push(arg.clone());
        }
    }

    // `--version` / `-V` (any position) and the `version` subcommand print
    // the build stamp and exit (WI-160). Served host-side like `init` /
    // `skill` — no KB load or project directory required, so the stamp is
    // available everywhere (the whole point is identifying a stale binary).
    if want_version || bundle_argv.first().map(|s| s.as_str()) == Some("version") {
        println!("{}", anthill_version::version_string!());
        return 0;
    }

    // A top-level help request (`--help` / `-h` / `help` in the subcommand
    // position, matching the bundle's own check) gets the build stamp
    // appended as a footer once the bundle prints its spec-driven command
    // list (WI-160).
    let help_mode = matches!(
        bundle_argv.first().map(|s| s.as_str()),
        Some("--help") | Some("-h") | Some("help")
    );

    // `init` runs before any KB exists — it scaffolds the project's
    // anthill-todo/ directory. Reuse the legacy implementation; once
    // there's a project to load, the bundle takes over.
    if bundle_argv.first().map(|s| s.as_str()) == Some("init") {
        // `init --name <name>` (the legacy clap flag) or `init <name>`.
        let name = match bundle_argv.get(1).map(|s| s.as_str()) {
            Some("--name") => bundle_argv.get(2).map(|s| s.as_str()),
            other => other,
        };
        // Honor the stripped `-d <dir>` — every other subcommand does, via
        // find_project_dir; init used to be the lone exception (WI-748).
        return run_init(explicit_dir.as_deref(), name);
    }

    // `skill` is a static doc print — served host-side so the output stays
    // byte-identical to the legacy CLI (YAML frontmatter included; the
    // Claude Code skill installation parses it) and no KB load is paid.
    // (The bundle has no skill dispatch arm — this is the one impl.)
    if bundle_argv.first().map(|s| s.as_str()) == Some("skill") {
        print!("{}", SKILL_MD);
        return 0;
    }

    let (stdlib_parsed, stdlib_errors) = stdlib::parse_embedded();
    let (bundle_parsed, bundle_errors) = anthill_bundle::parse_embedded_bundle();
    for e in stdlib_errors.iter().chain(bundle_errors.iter()) {
        eprintln!("error: {e}");
    }
    if !stdlib_errors.is_empty() || !bundle_errors.is_empty() {
        return runner::EXIT_COMPILE;
    }

    // Bulk-pull the project's anthill-todo/ files: domain.anthill defines
    // WorkItem etc., rules.anthill provides workflow rules, workitems.anthill
    // carries the user-asserted facts. Without this the bundle's KB only
    // sees stdlib + the bundle itself, and `sort_query(WorkItem)` fails.
    let project_dir = match find_project_dir(explicit_dir.as_deref()) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("error: {e}");
            return runner::EXIT_RUNTIME;
        }
    };
    let scan = scan_dir(&project_dir);
    let project_files = match collect_anthill_files(&[scan]) {
        Ok(f) => f,
        Err(errs) => {
            for e in &errs {
                eprintln!("error: {e}");
            }
            return runner::EXIT_COMPILE;
        }
    };
    // Each project file pairs its on-disk path with the parsed IR so
    // the IndexedFileStore can later associate fact RuleIds with their
    // byte-range spans on disk.
    let mut project_items: Vec<ProjectFile> = Vec::new();
    for file in &project_files {
        // WI-744: a project file we can SEE but cannot READ is an error. Skipping
        // it made `list` silently under-report — the work items are on disk, and
        // the user is told everything is fine.
        let source = match fs::read_to_string(file) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("error: {}: {e}", file.display());
                return runner::EXIT_COMPILE;
            }
        };
        match parse::parse(&source) {
            Ok(mut parsed) => {
                if is_bundle_logic_file(&parsed) {
                    continue;
                }
                // The standard domain/rules ship bundled (WI-505); a project's
                // own copy would double-define them, so skip it. Its presence
                // is a legacy scaffold, not an error — succeed against the
                // bundled definitions.
                if is_bundled_domain_or_rules(&parsed) {
                    continue;
                }
                assign_default_namespace(&mut parsed);
                // WI-745: stamp the path so a load error names the FILE
                // (`path:line:col`) — the todo CLI merges embedded stdlib +
                // bundle + N project files, so a bare byte offset identified none.
                let parsed = parsed.with_path(file.clone());
                project_items.push(ProjectFile {
                    path: file.clone(),
                    parsed,
                });
            }
            Err(errs) => {
                // A parse failure is always surfaced — a stale domain.anthill
                // that predates a grammar change (the WI-505 motivating case)
                // no longer cascades into a wall of unresolved-import errors,
                // because the bundled domain/rules already supply those names;
                // the honest parse diagnostic is all that remains, and a real
                // typo in any file must not be swallowed (loud over silent).
                // WI-852: through the shared owner, so this cannot drift from
                // the rendering every other parse-error and load-error printer
                // uses; batched so the file is indexed once.
                for located in ParseError::all_located(&errs, file, &source) {
                    eprintln!("warning: {located}");
                }
            }
        }
    }

    let mut kb = KnowledgeBase::new();
    let all_refs: Vec<&ParsedFile> = stdlib_parsed
        .iter()
        .chain(bundle_parsed.iter())
        .chain(project_items.iter().map(|pf| &pf.parsed))
        .collect();
    let project_offset = stdlib_parsed.len() + bundle_parsed.len();
    let per_file_results = match load::load_all_per_file(&mut kb, &all_refs, &NullResolver) {
        // `merged.warnings` is dropped deliberately: the stdlib and bundle are
        // EMBEDDED, so their advisories name files the user cannot act on. WI-745.
        Ok((_merged, per_file)) => per_file,
        // WI-744: every `LoadError` blocks (see `LoadError`'s doc), so there is no
        // fallback value here. The old fall-through returned an EMPTY per-file
        // result, and `record_source` zips `project_items` against it — so zero
        // fact→span mappings were recorded and `IndexedFileStore::retract` fell
        // back to a content-keyed retract. The demotion corrupted WRITES, it did
        // not merely mute a diagnostic.
        //
        // Deliberately asymmetric with the `parse::parse` arm below, which warns
        // and SKIPS. What lets that arm skip is not that it is per-file
        // attributable — the read arm above is too, and it BLOCKS — but WI-505:
        // the skipped file is a stale `domain.anthill` whose definitions the
        // bundle already supplies, so dropping it loses nothing. A load error has
        // no such redundancy guarantee, so it BLOCKS. WI-745 gave each error its
        // file identity (the `path:line:col` below now names the offending
        // project file among the merged embedded stdlib + bundle + N files), so
        // "skip just the offending file" is now *available* — but it stays
        // unimplemented on purpose: a load error is not the redundant duplicate
        // the parse arm skips, and WI-744 requires it to block.
        Err(errs) => {
            // Batched: one line index per file, not per error (WI-852 follow-up).
            for e in load::LoadError::render_all(&errs) {
                eprintln!("error: {e}");
            }
            return runner::EXIT_COMPILE;
        }
    };

    // The data-format version check runs inside the bundle's `main` (WI-434):
    // it is a query over the loaded StoreFormat facts, so it lives in anthill
    // rather than a host prescan.

    let mut interp = Interpreter::new(kb);
    if let Err(code) = runner::register_runtime(&mut interp) {
        return code;
    }

    // The store the anthill side will receive, built from the project's own DECLARED
    // extent binding (WI-830). Mutating commands (add / feedback / claim / ...) call
    // `Store.persist` / `Store.flush` on this entity, and the registry routes that
    // dispatch back to the instance built here.
    //
    // This used to be a fixed `IndexedFileStore` at a fixed path with a literal array of
    // functor names. None of it was a project's to change, which is what WI-437 (a
    // GitHub-backed tracker) was blocked on. It is now `fact ExtentBinding(...)` in
    // project.anthill, and the host's remaining job is the one part that must stay
    // native: mapping a declared store to one of its compiled-in backends.
    let store_root = scan_dir(&project_dir);
    let mut declared = match build_declared_store(
        &mut interp,
        &store_root,
        &project_items,
        &per_file_results[project_offset..],
    ) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("error: {e}");
            return runner::EXIT_RUNTIME;
        }
    };

    // `fsck` is the ONE command that wants the concrete backend rather than the store
    // algebra — the layout checks and the repair are a property of a directory-per-state
    // layout, not of storage. It is served here, between building the store and handing
    // it to the registry, because that is the only point at which the host still holds it.
    if bundle_argv.first().map(|s| s.as_str()) == Some("fsck") {
        return run_fsck(&mut declared.store, &bundle_argv[1..]);
    }

    // Otherwise the layout must agree with the facts before anything writes through it.
    // A blocking fault leaves the store's own routing ambiguous, so the next write would
    // have to guess; the remedy is named rather than guessed at.
    let faults = declared.store.layout_faults();
    let blocking = faults.iter().filter(|f| f.blocking()).count();
    for fault in &faults {
        if fault.blocking() {
            eprintln!("error: {fault}");
        } else {
            eprintln!("warning: {fault}");
        }
    }
    if blocking > 0 {
        eprintln!("error: run `anthill-todo fsck --fix` to move each file to the path its own fact names");
        return runner::EXIT_RUNTIME;
    }

    let store_value = match register_declared_store(&mut interp, declared) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("error: {e}");
            return runner::EXIT_RUNTIME;
        }
    };

    let args_value = match runner::build_args_value(&mut interp, &bundle_argv) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("error: building args list: {e}");
            return runner::EXIT_RUNTIME;
        }
    };
    let agent_value = Value::Str(agent);

    // Seed Cell[V = WIS] from on-disk WI-NNN max so the next freshly
    // allocated id doesn't collide. This cell is now the ONLY way the backend
    // reaches the bundle — every command body goes through the `WorkItemStore`
    // spec ops on it (WI-1113 removed the parallel `store: FileStore` path).
    //
    // Under a coordinated backend this seeding is exactly the id-collision bug
    // (design doc §1.2), and it disappears: `alloc_id` reads the forge registry
    // instead. Until then the host owns the scan, because the bundle has no
    // String -> Int64 to recover a counter from an id.
    let wis_cell_value = {
        let kb_ref = interp.kb();
        let items = match collect_workitems(kb_ref) {
            Ok(items) => items,
            Err(e) => {
                eprintln!("error: {e}");
                return runner::EXIT_RUNTIME;
            }
        };
        let mut max_num: u32 = 0;
        for item in items {
            if let Some(rest) = item.id.strip_prefix("WI-") {
                if let Ok(n) = rest.parse::<u32>() {
                    max_num = max_num.max(n);
                }
            }
        }
        let id_counter = (max_num as i64) + 1;

        // THE IMPL BUILDS ITS OWN STATE (WI-1114). This used to intern
        // `…FileBasedWorkitemStore.wis` and its `backend` / `id_counter` field names
        // and assemble the entity here — the host knowing one impl's INTERNALS, which
        // is a different thing from the one native step it legitimately owns (mapping a
        // declared store term to a compiled-in backend, above). The shape of the state
        // is the impl's business, and a second impl with a different state could not be
        // substituted while this line spelled the first one's.
        //
        // The impl is named because the host is the one that PICKS it — the same symbol
        // it pins into `chain_dicts` below, for the same reason. What it no longer knows
        // is what the impl keeps inside.
        //
        // `backend` is the same store value the mirror registry is keyed on, so
        // anthill-side `persist` / `flush` through the cell route to the instance built
        // above.
        let wis_value = match interp.call(
            "anthill.todo.store.FileBasedWorkitemStore.open",
            &[store_value.clone(), Value::Int(id_counter)],
        ) {
            Ok(v) => v,
            Err(e) => {
                eprintln!("error: building the store's initial state: {e}");
                return runner::EXIT_RUNTIME;
            }
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
        let main_sym = interp
            .kb()
            .try_resolve_symbol("anthill.todo.Main")
            .expect("anthill.todo.Main must be loaded");
        let workitemstore_sym = interp
            .kb()
            .try_resolve_symbol("anthill.todo.store.WorkItemStore");
        let filebased_sym = interp
            .kb_mut()
            .intern("anthill.todo.store.FileBasedWorkitemStore");
        let entries = anthill_core::kb::typing::direct_requires_chain(interp.kb_mut(), main_sym);
        let mut out: smallvec::SmallVec<[_; 2]> = smallvec::SmallVec::new();
        for entry in &entries {
            let impl_sym = if Some(entry.required_sort) == workitemstore_sym {
                filebased_sym
            } else {
                entry.required_sort
            };
            out.push(
                interp
                    .alloc_requirement(impl_sym, [])
                    .expect("the stdlib defines anthill.realization.runtime.Dictionary"),
            );
        }
        out
    };

    // The main-result → exit-code mapping (Int clamp, non-Int, top-level
    // `Raised` Error effect per WI-195, other evaluator errors) is shared with
    // anthill-cli's `run`.
    // NO `store_value` ARGUMENT. `main` used to take the concrete backend as a
    // `store: FileStore` parameter beside the cell, threaded through `dispatch` into
    // all twelve mutating `cmd_*` — and read by none of them. It is gone (WI-1113):
    // the backend reaches the bundle only inside the cell's `State`, through the
    // `WorkItemStore` spec ops, which is what lets a second backend be substituted at
    // all. `store_value` is still built above, because the cell's `wis(backend:, …)`
    // carries it and the mirror registry is keyed on it.
    let result = interp.call_with_requirements(
        "anthill.todo.Main.main",
        &[args_value, wis_cell_value, agent_value],
        chain_dicts,
    );
    let code = runner::exit_code_from_main(interp.kb(), result);

    // The bundle has just printed the spec-driven command list; surface the
    // build stamp as the `--help` footer (WI-160).
    if help_mode {
        println!();
        println!("{}", anthill_version::version_string!());
    }
    code
}
