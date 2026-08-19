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

### Referring to a work item

An item's id is MINTED FROM THE ITEM: `WI-<YYYYMMDD>-<5 characters>-<slug>`, e.g.
`WI-20260817-K7M2Q-item-per-file-store`. Nobody types that. Every command that
takes an id accepts any unambiguous FRAGMENT of one:

```bash
anthill-todo -d "$PWD" show WI-K7M2Q                  # the 5-character digest, or a prefix
anthill-todo -d "$PWD" show WI-20260817-K7M2Q         # date-digest — the stable handle
anthill-todo -d "$PWD" show WI-item-per-file          # the slug, or a prefix of it
```

A fragment matching several items is REPORTED with the candidates rather than
resolved by a rule — give more of one of them. Older `WI-NNN` ids still work
exactly as they always did, and are never renumbered.

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
/// The two shapes a project file can have (WI-1120): a plain `.anthill` file, and
/// an item DOCUMENT, `WI-NNN.anthill.md`.
///
/// A SUFFIX LIST, not an extension list, and it has to be: `Path::extension()`
/// answers `md` for the second, so `&["anthill"]` misses every item document
/// while `&["md"]` would sweep in every README in the tree.
const PROJECT_FILE_SUFFIXES: [&str; 2] = [ITEM_PLAIN_SUFFIX, ITEM_DOCUMENT_SUFFIX];

fn collect_anthill_files(paths: &[PathBuf]) -> Result<Vec<PathBuf>, Vec<String>> {
    let mut files = Vec::new();
    let mut errors = Vec::new();
    for path in paths {
        if path.is_dir() {
            if let Err(e) =
                fs_util::collect_files_by_suffix_recursive(path, &PROJECT_FILE_SUFFIXES, &mut files)
            {
                errors.push(e);
            }
        } else if fs_util::has_suffix(path, &PROJECT_FILE_SUFFIXES) {
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
// ── The declared fact↔markdown mapping (WI-1120) ─────────────────

/// Read `anthill.stage0.document`'s facts out of the BUNDLE'S PARSE IR.
///
/// WHY THE IR AND NOT THE KB, which is where every other declaration this host
/// reads comes from (`ExtentBinding`, the store's field names): the mapping is
/// needed to PARSE the project's own files, and the KB does not exist yet at
/// that point. A document's prose lives outside the fenced head, so reading one
/// means splicing each chapter back into the fact it fills BEFORE the loader
/// sees it — there is no later moment at which injecting it would not mean
/// rewriting rows the KB already holds.
///
/// The bundle is EMBEDDED, so this is not a second source of truth: it is the
/// same text, read one phase earlier. The same facts also load into the KB like
/// any other, which is what keeps them declarations rather than a private
/// side-channel.
fn document_mapping(bundle: &[ParsedFile]) -> Result<DocumentMapping, String> {
    let mut mapping = DocumentMapping::default();
    for pf in bundle {
        collect_mapping_facts(pf, &pf.items, &mut mapping)?;
    }
    if mapping.level == 0 {
        return Err("the bundled domain declares no `fact DocumentFormat(level:)`, so there is \
                    no structural level for a chapter heading to sit at"
            .to_string());
    }
    // A functor with two chapter fields would need the reader to decide which
    // chapter fills which, and nothing says. Refused rather than first-wins.
    for (i, c) in mapping.chapters.iter().enumerate() {
        if mapping.chapters[..i].iter().any(|o| o.functor == c.functor)
            || mapping.groups.iter().any(|g| g.functor == c.functor)
        {
            return Err(format!(
                "`{}` is given more than one chapter by the document mapping; a fact has one \
                 prose field here",
                c.functor
            ));
        }
    }
    Ok(mapping)
}

fn collect_mapping_facts(
    pf: &ParsedFile,
    items: &[anthill_core::parse::ir::Item],
    out: &mut DocumentMapping,
) -> Result<(), String> {
    use anthill_core::parse::ir::Item;
    for item in items {
        match item {
            Item::Namespace(ns) => collect_mapping_facts(pf, &ns.items, out)?,
            Item::Fact(f) => {
                let Term::Fn {
                    functor,
                    named_args,
                    ..
                } = pf.terms.get(f.term)
                else {
                    continue;
                };
                match pf.symbols.local_name(*functor) {
                    "DocumentFormat" => {
                        out.level = ir_int(pf, named_args, "level")
                            .ok_or("`fact DocumentFormat` carries no integer `level`")?
                            as usize;
                    }
                    "Chapter" => out.chapters.push(ChapterSpec {
                        functor: ir_name(pf, named_args, "functor")
                            .ok_or("`fact Chapter` carries no `functor`")?,
                        field: ir_string(pf, named_args, "field")
                            .ok_or("`fact Chapter` carries no `field`")?,
                        named: ir_string(pf, named_args, "named")
                            .ok_or("`fact Chapter` carries no `named`")?,
                    }),
                    "ChapterGroup" => out.groups.push(ChapterGroupSpec {
                        functor: ir_name(pf, named_args, "functor")
                            .ok_or("`fact ChapterGroup` carries no `functor`")?,
                        container: ir_string(pf, named_args, "container")
                            .ok_or("`fact ChapterGroup` carries no `container`")?,
                        field: ir_string(pf, named_args, "field")
                            .ok_or("`fact ChapterGroup` carries no `field`")?,
                        named_by: ir_string(pf, named_args, "named_by")
                            .ok_or("`fact ChapterGroup` carries no `named_by`")?,
                        decorate: ir_string_list(pf, named_args, "decorate"),
                    }),
                    _ => {}
                }
            }
            _ => {}
        }
    }
    Ok(())
}

type IrArgs = [(anthill_core::intern::Symbol, TermId)];

fn ir_arg(pf: &ParsedFile, args: &IrArgs, field: &str) -> Option<TermId> {
    args.iter()
        .find(|(s, _)| pf.symbols.local_name(*s) == field)
        .map(|(_, t)| *t)
}

fn ir_string(pf: &ParsedFile, args: &IrArgs, field: &str) -> Option<String> {
    match pf.terms.get(ir_arg(pf, args, field)?) {
        Term::Const(Literal::String(s)) => Some(s.clone()),
        _ => None,
    }
}

fn ir_int(pf: &ParsedFile, args: &IrArgs, field: &str) -> Option<i64> {
    match pf.terms.get(ir_arg(pf, args, field)?) {
        Term::Const(Literal::Int(n)) => Some(*n),
        _ => None,
    }
}

/// A field naming a FUNCTOR (`functor: WorkItem`) rather than holding a string.
/// It is written as a bare name, which parses to a `Ref`/`Ident`.
fn ir_name(pf: &ParsedFile, args: &IrArgs, field: &str) -> Option<String> {
    match pf.terms.get(ir_arg(pf, args, field)?) {
        Term::Ref(s) | Term::Ident(s) => Some(pf.symbols.local_name(*s).to_string()),
        Term::Fn { functor, .. } => Some(pf.symbols.local_name(*functor).to_string()),
        _ => None,
    }
}

/// `decorate: ["author"]` — a bracket literal, which parses to a flat
/// `ListLiteral` application (WI-1099). An absent field is an empty list rather
/// than an error: a group that decorates its headings with nothing is legal.
fn ir_string_list(pf: &ParsedFile, args: &IrArgs, field: &str) -> Vec<String> {
    let Some(t) = ir_arg(pf, args, field) else {
        return Vec::new();
    };
    let Term::Fn { pos_args, .. } = pf.terms.get(t) else {
        return Vec::new();
    };
    pos_args
        .iter()
        .filter_map(|a| match pf.terms.get(*a) {
            Term::Const(Literal::String(s)) => Some(s.clone()),
            _ => None,
        })
        .collect()
}

/// Splice each chapter's prose back into the fact whose field it holds, so that
/// what reaches the loader is the SAME parse IR a plain `fact` file would have
/// produced (WI-1120).
///
/// THAT EQUIVALENCE IS THE WHOLE DESIGN. Nothing downstream — not the loader,
/// not the typer, not a single reader in the bundle — learns that the text
/// arrived from a heading rather than from a string literal. It also settles
/// what a MISSING chapter means without a second rule: the field is simply left
/// off the fact, and the loader's existing omitted-field handling takes over, so
/// an `Option[T = String]` becomes `none()` exactly as §5.3's first row asks.
///
/// A FIELD chapter is matched by NAME and an ENTRY by POSITION, which is the
/// asymmetry §5.4 argues: a chapter name is fixed by the mapping, while an
/// entry's name comes from a field that is not injective (two `Feedback` rows on
/// this tracker share both `at` and `author`). The store checks the heading
/// against the fact when it seeds; here the binding is made.
fn inject_chapters(
    parsed: &mut ParsedFile,
    source: &str,
    doc: &Document,
    mapping: &DocumentMapping,
) -> Result<(), String> {
    let mut cursor: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
    let mut plan: Vec<(usize, String, String)> = Vec::new();
    let mut index = 0usize;
    collect_fact_injections(parsed, doc, mapping, source, &mut cursor, &mut plan, &mut index)?;
    apply_fact_injections(parsed, &plan);
    Ok(())
}

/// Walk the facts in DFS order and decide, per fact, which chapter's text fills
/// which of its fields. Collected first and applied second because deciding
/// borrows the IR and applying mutates it.
fn collect_fact_injections(
    parsed: &ParsedFile,
    doc: &Document,
    mapping: &DocumentMapping,
    source: &str,
    cursor: &mut std::collections::HashMap<String, usize>,
    plan: &mut Vec<(usize, String, String)>,
    index: &mut usize,
) -> Result<(), String> {
    use anthill_core::parse::ir::Item;
    fn walk(
        parsed: &ParsedFile,
        items: &[Item],
        doc: &Document,
        mapping: &DocumentMapping,
        source: &str,
        cursor: &mut std::collections::HashMap<String, usize>,
        plan: &mut Vec<(usize, String, String)>,
        index: &mut usize,
    ) -> Result<(), String> {
        for item in items {
            match item {
                Item::Namespace(ns) => {
                    walk(parsed, &ns.items, doc, mapping, source, cursor, plan, index)?
                }
                Item::Fact(f) => {
                    let position = *index;
                    *index += 1;
                    let Term::Fn { functor, .. } = parsed.terms.get(f.term) else {
                        continue;
                    };
                    let name = parsed.symbols.local_name(*functor).to_string();
                    if let Some(spec) = mapping.chapter_for(&name) {
                        if let Some(seg) = doc.segments.iter().find(|s| {
                            matches!(&s.kind, SegmentKind::Field { name } if *name == spec.named)
                        }) {
                            plan.push((
                                position,
                                spec.field.clone(),
                                source[seg.body.clone()].to_string(),
                            ));
                        }
                    } else if let Some(group) = mapping.group_for(&name) {
                        let nth = cursor.entry(group.container.clone()).or_insert(0);
                        let seg = doc
                            .segments
                            .iter()
                            .filter(|s| {
                                matches!(&s.kind, SegmentKind::Entry { container, .. }
                                         if *container == group.container)
                            })
                            .nth(*nth);
                        *nth += 1;
                        let seg = seg.ok_or_else(|| {
                            format!(
                                "the head declares more `{name}` rows than `## {}` has entries — \
                                 each row's prose is the entry at its own position, so the two \
                                 counts must agree",
                                group.container
                            )
                        })?;
                        plan.push((
                            position,
                            group.field.clone(),
                            source[seg.body.clone()].to_string(),
                        ));
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }
    walk(
        parsed,
        &parsed.items,
        doc,
        mapping,
        source,
        cursor,
        plan,
        index,
    )
}

/// Rebuild each planned fact's top-level term with the chapter's text added as a
/// named argument.
///
/// THE SPAN THE NEW LITERAL CARRIES IS ITS OWN — the fact's — rather than a
/// synthetic one: the text does not exist inside the head, so there is no
/// sub-range of the parsed region to point at, and pointing at the whole fact is
/// the closest true answer.
fn apply_fact_injections(parsed: &mut ParsedFile, plan: &[(usize, String, String)]) {
    use anthill_core::parse::ir::Item;
    // Collect (position, term, span) first — the mutation needs `&mut
    // parsed.terms` while the walk needs `&parsed.items`.
    let mut targets: Vec<(usize, TermId, anthill_core::span::Span)> = Vec::new();
    fn scan(
        items: &[Item],
        index: &mut usize,
        out: &mut Vec<(usize, TermId, anthill_core::span::Span)>,
    ) {
        for item in items {
            match item {
                Item::Namespace(ns) => scan(&ns.items, index, out),
                Item::Fact(f) => {
                    out.push((*index, f.term, f.span));
                    *index += 1;
                }
                _ => {}
            }
        }
    }
    let mut index = 0usize;
    scan(&parsed.items, &mut index, &mut targets);

    let mut rebuilt: std::collections::HashMap<usize, TermId> = std::collections::HashMap::new();
    for (position, field, value) in plan {
        let Some((_, term, span)) = targets.iter().find(|(p, _, _)| p == position) else {
            continue;
        };
        let term = rebuilt.get(position).copied().unwrap_or(*term);
        let Term::Fn {
            functor,
            pos_args,
            named_args,
        } = parsed.terms.get(term).clone()
        else {
            continue;
        };
        let field_sym = parsed.symbols.intern(field);
        let literal = parsed
            .terms
            .alloc(Term::Const(Literal::String(value.clone())), *span);
        let mut named: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> = named_args.clone();
        named.push((field_sym, literal));
        let new = parsed.terms.alloc(
            Term::Fn {
                functor,
                pos_args: pos_args.clone(),
                named_args: named,
            },
            *span,
        );
        rebuilt.insert(*position, new);
    }
    if rebuilt.is_empty() {
        return;
    }
    fn rewrite(
        items: &mut [Item],
        index: &mut usize,
        rebuilt: &std::collections::HashMap<usize, TermId>,
    ) {
        for item in items {
            match item {
                Item::Namespace(ns) => rewrite(&mut ns.items, index, rebuilt),
                Item::Fact(f) => {
                    if let Some(new) = rebuilt.get(index) {
                        f.term = *new;
                    }
                    *index += 1;
                }
                _ => {}
            }
        }
    }
    let mut index = 0usize;
    rewrite(&mut parsed.items, &mut index, &rebuilt);
}

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
use anthill_core::kb::typing::get_named_string_arg;
use anthill_core::persistence::file_store::FileConvention;
use anthill_core::persistence::indexed_file_store::IndexedFileStore;
use anthill_core::persistence::document::{
    self, ChapterGroupSpec, ChapterSpec, Document, DocumentMapping, SegmentKind,
};
use anthill_core::persistence::item_per_file_store::{
    ItemFields, ItemPerFileStore, LayoutFault, ITEM_DOCUMENT_SUFFIX, ITEM_PLAIN_SUFFIX,
};
use anthill_core::persistence::{print, Store};

/// A project file paired with its parsed IR, so the store can associate each fact's
/// RuleId with its byte range on disk.
struct ProjectFile {
    path: PathBuf,
    parsed: ParsedFile,
    /// The file's whole text, kept from the one read that produced `parsed`.
    /// The store cuts it into blocks, and re-reading it there would let the two
    /// disagree if anything touched the file in between.
    source: String,
    /// The document structure, for an item document (WI-1120). `None` for a
    /// plain `.anthill` file, whose whole text is the head.
    document: Option<Document>,
}

impl ProjectFile {
    /// The byte ranges of this file's facts, in the file's own coordinates.
    ///
    /// A DOCUMENT'S HEAD IS PARSED ALONE, so the parser's spans are relative to
    /// the head text and have to be shifted to address the file. That shift is
    /// the only place the two coordinate systems meet, and it is why the store is
    /// handed the whole source rather than the head: everything it renders — the
    /// preamble, the fences, the chapters — lives outside the parsed region.
    fn fact_spans_in_file(&self) -> Vec<anthill_core::span::Span> {
        let offset = self.document.as_ref().map(|d| d.head.start).unwrap_or(0) as u32;
        self.parsed
            .fact_spans()
            .into_iter()
            .map(|s| anthill_core::span::Span {
                start: s.start + offset,
                end: s.end + offset,
            })
            .collect()
    }
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

    /// WI-1120: the OTHER thing `--fix` repairs — a chapter heading that
    /// disagrees with the fact it projects. An empty answer from a shared-file
    /// store is honest here where it would be a lie in `checked_layout`: that
    /// store has no chapters, so there are none to be stale.
    fn repair_headings(&mut self) -> Result<Vec<(PathBuf, String)>, String> {
        match self {
            BuiltStore::Indexed(_) => Ok(Vec::new()),
            BuiltStore::ItemPerFile(s) => s.repair_headings().map_err(|e| e.to_string()),
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
    mapping: &DocumentMapping,
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

    check_covers_every_retracted_functor(interp, &binding.covers)?;

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
                // IN THE FILE'S COORDINATES, not the parsed region's (WI-1120). A
                // document's head is parsed alone, so `fact_spans()` counts from
                // the head rather than from byte 0 — and this store addresses a
                // row by its byte range in the FILE. The mismatch is silent and
                // destructive: a retract would splice at an offset short by the
                // preamble and fence, editing the wrong bytes instead of removing
                // the row. Reachable whenever a tree holds documents while its
                // binding still names this store — a `migrate` whose final binding
                // rewrite failed after the documents were written.
                let spans = file.fact_spans_in_file();
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
            // WI-1120: the document mapping makes every ITEM file a
            // `WI-NNN.anthill.md`. It is bundled with the domain, so it is not a
            // per-project choice — the encoding is a property of the schema.
            let mut store =
                ItemPerFileStore::new(store_root.clone(), declared_fields(interp, &binding.store)?)
                    .with_document_mapping(mapping.clone());
            for (file, result) in project_items.iter().zip(project_results.iter()) {
                let rows: Vec<_> = result
                    .fact_rule_ids
                    .iter()
                    .copied()
                    .zip(file.fact_spans_in_file())
                    .collect();
                let seeded = match &file.document {
                    Some(doc) => store.record_document(
                        interp.kb(),
                        file.path.clone(),
                        &file.source,
                        &rows,
                        doc,
                    ),
                    None => {
                        store.record_file(interp.kb(), file.path.clone(), &file.source, &rows)
                    }
                };
                seeded.map_err(|e| format!("reading the project's layout: {e}"))?;
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

/// Refuse a binding that omits a functor this tool retracts, at STARTUP and by name.
///
/// WHY IT EXISTS (WI-1123). `delete` used to retract only `WorkItem`, so a binding
/// naming `covers: [WorkItem, Tag]` looked like it worked — the omission cost the
/// project nothing until it hit the one command that needed it. Now that `delete`
/// takes an item's `Feedback` rows with it, that same binding dies mid-command with
/// `retract: FactRef does not belong to the supplied store` — true, loud, and
/// diagnosing nothing: the reader is looking at `delete`, and the fault is four
/// lines of `project.anthill`.
///
/// ONLY THE RETRACTED SET IS REQUIRED. A persist through the declared backend works
/// whether or not the binding names the functor; it is a RETRACT that needs the
/// row's reference to belong to the store being asked. So `StoreFormat`, which is
/// stamped and never removed, is not demanded — and `examples/github-todo`, whose
/// binding predates it, keeps loading.
///
/// IT BLOCKS EVERY COMMAND, INCLUDING `fsck` AND `migrate`, and that is deliberate
/// — not the same call as the orphan tolerance a few hundred lines down, which lets
/// `migrate` run over rows a project CANNOT un-write. This is four characters of
/// `project.anthill`, which the user owns and must edit whatever else they do:
/// `migrate` carries `covers` across verbatim (`rewrite_binding`), so migrating
/// would not repair it. Its two nearest neighbours already refuse every command on
/// the same grounds — `role: owner()`, and a backend this build does not provide.
/// What review found and this no longer does is send the reader in a circle: the
/// message must name the spelling that works, or blocking the repair commands has
/// no way out.
///
/// Not a fallback: the binding is the project's statement of what its store holds,
/// and a statement that omits rows the tool will ask that store to remove is wrong,
/// not merely incomplete.
fn check_covers_every_retracted_functor(
    interp: &Interpreter,
    covers: &[anthill_core::intern::Symbol],
) -> Result<(), String> {
    let declared: Vec<&str> = covers
        .iter()
        .map(|s| interp.kb().qualified_name_of(*s))
        .collect();
    let required: Vec<&str> = STORED_FUNCTORS
        .iter()
        .filter(|(_, r)| *r == Retracted::Yes)
        .map(|(name, _)| *name)
        .collect();
    let missing: Vec<&str> = required
        .iter()
        .copied()
        .filter(|want| !declared.contains(want))
        .collect();
    if missing.is_empty() {
        return Ok(());
    }
    // NAMED THE WAY THEY MUST BE WRITTEN, which is the SHORT name (found in
    // review). The comparison above is on the qualified name — that is what the
    // resolved symbol gives back, whatever the file said — but a `covers:` list is
    // read in a scope where `Feedback` resolves and `anthill.stage0.Feedback` does
    // not, so an error telling the reader to add the qualified name sends them to a
    // spelling that is refused again, identically. `rewrite_binding` writes short
    // names for exactly this reason; so does this.
    let spell = |names: &[&str]| -> String {
        names
            .iter()
            .map(|n| n.rsplit('.').next().unwrap_or(n))
            .collect::<Vec<_>>()
            .join(", ")
    };
    Err(format!(
        "this project's extent binding does not cover {}. anthill-todo RETRACTS rows of \
         {} — `delete` removes a work item together with its feedback and tags — and a \
         retract needs the row's reference to belong to the store being asked, so an \
         uncovered functor fails at that command rather than here. Add {} to the \
         binding's `covers:` list in project.anthill (short names: that is what \
         resolves there).",
        spell(&missing),
        spell(&required),
        spell(&missing),
    ))
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
fn run_fsck(interp: &mut Interpreter, store: &mut BuiltStore, args: &[String]) -> i32 {
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
        match repair_created(interp, store) {
            Ok(filled) => {
                for (id, stamp) in &filled {
                    println!("dated {id} from its file: {stamp}");
                }
            }
            Err(e) => {
                eprintln!("error: {e}");
                return runner::EXIT_RUNTIME;
            }
        }
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
        match store.repair_headings() {
            Ok(chapters) => {
                for (path, what) in &chapters {
                    println!("{}: {what}", path.display());
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

/// `anthill-todo migrate --to item-per-file` — the LAYOUT move (design §11).
///
/// Explodes the rows this project's store covers into one file per item under a
/// directory per state, and rewrites the project's `ExtentBinding` to name the
/// new layout. Steps 1 and 3 of §11; step 4 is deliberately absent and
/// [`MIGRATE_USAGE`] says why.
///
/// PURELY LOCAL, which is a change from what §11 was drafted as. Creating one
/// mirror entry per item was step 2 for as long as the forge ALLOCATED ids — an
/// unmirrored item had no permanent id, so mirroring and migrating were
/// inseparable. With ids minted locally that step is `export`, run separately and
/// only if the project wants a mirror at all. So there is no network here,
/// nothing paced under a rate limit, and nothing to resume across an API.
///
/// IT WRITES NOTHING UNTIL IT CAN WRITE EVERYTHING. Every row is buffered and one
/// `flush` lays down the whole tree. That flush routes and path-checks every row —
/// including [`ItemPerFileStore`]'s refusal of a file it never read — before it
/// writes the first byte, so a tree with debris in it aborts with the old layout
/// untouched.
fn run_migrate(
    interp: &mut Interpreter,
    declared: &DeclaredStore,
    store_root: &Path,
    project_items: &[ProjectFile],
    per_file: &[load::LoadResult],
    mapping: &DocumentMapping,
    args: &[String],
) -> i32 {
    let mut to: Option<&str> = None;
    let mut created_from: Option<String> = None;
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--help" | "-h" => {
                println!("{MIGRATE_USAGE}");
                return 0;
            }
            "--to" => match iter.next() {
                Some(v) => to = Some(v.as_str()),
                None => {
                    eprintln!("error: --to requires a value");
                    eprintln!("{MIGRATE_USAGE}");
                    return runner::EXIT_COMPILE;
                }
            },
            "--created-from" => match iter.next() {
                Some(v) => created_from = Some(v.clone()),
                None => {
                    eprintln!("error: --created-from requires a value");
                    eprintln!("{MIGRATE_USAGE}");
                    return runner::EXIT_COMPILE;
                }
            },
            other => match other
                .strip_prefix("--to=")
                .map(|v| (true, v))
                .or_else(|| other.strip_prefix("--created-from=").map(|v| (false, v)))
            {
                Some((true, v)) => to = Some(v),
                Some((false, v)) => created_from = Some(v.to_string()),
                None => {
                    eprintln!("error: unknown migrate option `{other}`");
                    eprintln!("{MIGRATE_USAGE}");
                    return runner::EXIT_COMPILE;
                }
            },
        }
    }
    if to == Some("document") {
        return run_migrate_to_document(
            interp,
            declared,
            store_root,
            project_items,
            per_file,
            mapping,
            created_from.as_deref(),
        );
    }
    match to {
        Some("item-per-file") => {}
        // The ticket and §11 were written when this move also created ~1110
        // GitHub issues, and named it after that. It no longer does anything with
        // a forge, so the old name is refused with the reason rather than
        // accepted as an alias — a user typing it is asking for the mirror, and
        // silently giving them a local rewrite would answer a different question.
        Some("github-coordinated") => {
            eprintln!(
                "error: `--to github-coordinated` no longer names this operation. Migration is \
                 a purely local rewrite of the on-disk layout (`--to item-per-file`); publishing \
                 the tracker to a forge is a separate `export`, run only if the project wants a \
                 mirror at all (design §11 step 2, §7)."
            );
            return runner::EXIT_COMPILE;
        }
        Some(other) => {
            eprintln!("error: `{other}` is not a layout this build can migrate to");
            eprintln!("{MIGRATE_USAGE}");
            return runner::EXIT_COMPILE;
        }
        // Not reachable through the dispatch, which routes here only on `--to`
        // or `--help` — and it stays because the two are 400 lines apart. If the
        // dispatch condition ever loosens, this says so instead of migrating a
        // project that asked for the schema stamp.
        None => {
            eprintln!("error: migrate requires `--to <layout>`");
            eprintln!("{MIGRATE_USAGE}");
            return runner::EXIT_COMPILE;
        }
    }

    // A PROJECT ALREADY ON THIS LAYOUT IS ANSWERED FROM THE STORE, NOT THE BINDING.
    //
    // The binding looked like the whole record of which layout a project is on, and
    // is not: a project whose config was switched over while its rows still sat in
    // one shared file answered "already migrated" and declined, while every other
    // command blocked on the resulting layout fault — a dead end out of the one
    // state `fsck` explicitly says is `migrate`'s to fix.
    //
    // The store is the thing that knows, and it already reports exactly this:
    // `SharedFile` is one file holding several primary rows, which is the
    // shared-file layout read by a store expecting one item per file.
    //
    // AND MIGRATING FROM HERE IS REFUSED RATHER THAN ATTEMPTED. Doing the move in
    // this state means deciding, per file, which are already the target shape and
    // which are not — which is the store's routing rule, re-derived out here. A
    // first cut did exactly that and review found four ways it was wrong: a
    // satellite-only file silently dropped, satellites of skipped files misfiled as
    // orphans, the orphan file truncated over rows a previous run had saved, and a
    // flush-failure note telling the user to delete the only copy of their data.
    // The honest move is one loud sentence naming the remedy: migration writes the
    // binding itself, so it must start from the layout the data is actually in.
    if matches!(declared.store, BuiltStore::ItemPerFile(_)) {
        let shared: Vec<PathBuf> = declared
            .store
            .layout_faults()
            .into_iter()
            .filter_map(|f| match f {
                LayoutFault::SharedFile { path, .. } => Some(path),
                _ => None,
            })
            .collect();
        if shared.is_empty() {
            println!("migrate: this project is already one file per item");
            return 0;
        }
        eprintln!(
            "error: this project declares {ITEM_PER_FILE_STORE}, but {} file(s) still hold \
             several work items each:",
            shared.len()
        );
        for path in &shared {
            eprintln!("  {}", path.display());
        }
        eprintln!(
            "Migration writes the binding itself, so it has to start from the layout the rows are \
             actually in. Set `store:` back to \
             `anthill.persistence.filesystem.IndexedFileStore(root: \".\", convention: \
             anthill.persistence.filesystem.FileConvention.single_file(file: \"<that file>\"))` \
             and run this again."
        );
        return runner::EXIT_RUNTIME;
    }

    let created = match created_from.as_deref() {
        Some(path) => match read_created_table(Path::new(path)) {
            Ok(t) => t,
            Err(e) => {
                eprintln!("error: {e}");
                return runner::EXIT_RUNTIME;
            }
        },
        None => std::collections::HashMap::new(),
    };

    let mut covered = Vec::with_capacity(declared.covers.len());
    for name in &declared.covers {
        match interp.kb().try_resolve_symbol(name) {
            Some(s) => covered.push(s),
            None => {
                eprintln!("error: this project's binding covers `{name}`, which resolves to nothing");
                return runner::EXIT_RUNTIME;
            }
        }
    }

    // WHICH FILES THIS MOVES, and it is a per-FILE decision. A file all of whose
    // facts the binding covers is a store file: its rows move and it goes. A file
    // with none is somebody else's (`project.anthill` holds `Project`, `Module`
    // and the binding itself) and is left alone.
    //
    // A file holding SOME of each is refused rather than split. Splitting means
    // rewriting a hand-written file around the rows removed from it, and the two
    // readings of what should survive — the prose above a moved fact, say — are
    // not something to guess at on a one-way rewrite of a tracker.
    let mut consumed: Vec<(&Path, Vec<anthill_core::kb::RuleId>)> = Vec::new();
    for (file, result) in project_items.iter().zip(per_file.iter()) {
        let mut mine = Vec::new();
        for &rule in &result.fact_rule_ids {
            let head = interp.kb().rule_head(rule);
            let Some(functor) = fact_functor(interp.kb(), head) else {
                eprintln!(
                    "error: {}: a fact whose head has no functor cannot be routed",
                    file.path.display()
                );
                return runner::EXIT_RUNTIME;
            };
            if covered.contains(&functor) {
                mine.push(rule);
            }
        }
        if mine.is_empty() {
            continue;
        }
        // AGAINST EVERY ITEM IN THE FILE, not against its facts. A file is
        // consumed — its rows moved, and the file itself REMOVED below — so the
        // question is whether it holds anything else at all, and `fact_rule_ids`
        // can only ever answer for facts. Counting facts passed a file whose rows
        // were all covered but which also held a `rule`, and then deleted it: an
        // unrecoverable loss on a one-way rewrite (found in review, driven by
        // `a_file_holding_a_rule_beside_its_rows_is_refused`).
        let (facts, others) = item_census(&file.parsed);
        if mine.len() != facts || others != 0 {
            eprintln!(
                "error: {} holds {} row(s) this store covers and {} item(s) it does not; \
                 migration moves a whole file or none of it, and it removes the files it moves. \
                 Move the covered rows into the store's own file first",
                file.path.display(),
                mine.len(),
                facts - mine.len() + others,
            );
            return runner::EXIT_RUNTIME;
        }
        consumed.push((file.path.as_path(), mine));
    }
    if consumed.is_empty() {
        eprintln!("error: this project has no rows to migrate — no file holds any of the functors its binding covers");
        return runner::EXIT_RUNTIME;
    }

    // ORPHANS ARE CARRIED ACROSS, NOT REFUSED AND NOT DROPPED. A satellite whose
    // item has no row names a file that will never exist, so it cannot go through
    // the store: `path_of` refuses it, deliberately and under test
    // (`a_satellite_naming_no_item_is_refused_at_flush`).
    //
    // THAT REFUSAL IS ABOUT CREATING ONE, AND THIS IS INHERITING ONE — the store
    // draws exactly that line, tolerating on READ (`LayoutFault::OrphanRow`, and
    // explicitly NOT blocking) what it refuses on write. And the read side has to
    // tolerate it, because orphans are not a defect a project can be asked to
    // clean up before migrating: until WI-1123 `Feedback` was `monotone`
    // (proposal 053) and could not be retracted at all, so every `delete` of an
    // item that had feedback stranded it. `delete` cascades now — but the
    // trackers arriving HERE are precisely the ones written by older builds, so
    // refusing to migrate over their orphans would lock out the projects that
    // most need migrating.
    //
    // So they are written where they will be read back, reported here, and
    // reported by `fsck` from then on — which is the state §10 already describes.
    let orphans = orphan_satellites(interp.kb(), &consumed);

    // The target carries the DOCUMENT MAPPING (WI-1120), so a project migrating
    // today lands directly in `WI-NNN.anthill.md` and never sees the plain-`fact`
    // shape WI-1118 shipped. `--to document` exists for the trackers that already
    // did.
    // THE SAME `created` PLAN AS `--to document`, and running it here is what
    // closes the dead end: this migration writes DOCUMENTS, so a tracker filed
    // before the field existed would otherwise land on disk holding
    // `created: ?created` and be refused by every later command — including the
    // conversion that would have filled it in.
    let plan = plan_created_stamps(interp, &consumed, &created);
    if let Err(code) = plan.report() {
        return code;
    }
    let stamped = plan.stamps;

    let mut target = ItemPerFileStore::new(
        store_root.to_path_buf(),
        ItemFields::new(STAGE0_STATUS_FIELD, STAGE0_ID_FIELD, STAGE0_REF_FIELD),
    )
    .with_document_mapping(mapping.clone());
    let mut rows = 0usize;
    for (path, rules) in &consumed {
        for &rule in rules {
            if orphans.iter().any(|(r, _, _)| *r == rule) {
                continue;
            }
            let head = match stamped.get(&rule) {
                Some(stamp) => match with_created(interp, rule, stamp) {
                    Ok(t) => t,
                    Err(e) => {
                        eprintln!("error: {}: {e}", path.display());
                        return runner::EXIT_RUNTIME;
                    }
                },
                None => interp.kb().rule_head(rule),
            };
            let kb = interp.kb();
            if let Err(e) = target.persist(
                kb,
                head,
                kb.rule_clause_kind(rule),
                kb.rule_domain(rule),
                kb.rule_meta(rule),
            ) {
                eprintln!("error: {}: {e}", path.display());
                return runner::EXIT_RUNTIME;
            }
            rows += 1;
        }
    }
    if let Err(e) = target.flush(interp.kb()) {
        eprintln!("error: writing the new layout: {e}");
        // NOT "nothing was written", which was the first version of this line and
        // was false: the flush routes everything before it writes anything, but it
        // then writes file by file, so an I/O failure part way through leaves the
        // files before it on disk (found in review). And the debris is not inert —
        // a re-run builds a store that never read those files and refuses them
        // with `refuse_unknown_occupant`'s message, which diagnoses a parse
        // failure that did not happen. So say what may be there and how to clear it.
        eprintln!(
            "note: the project still names its old layout and {} is untouched, but a partly \
             written tree may be on disk. Remove the state directories under {} before running \
             this again — a re-run will otherwise refuse them as files it never read",
            consumed
                .iter()
                .map(|(p, _)| p.display().to_string())
                .collect::<Vec<_>>()
                .join(", "),
            store_root.display()
        );
        return runner::EXIT_RUNTIME;
    }

    // The orphans, written with the same printer the store writes rows with, so
    // they reload exactly as they were.
    if !orphans.is_empty() {
        let path = store_root.join(ORPHAN_FILE);
        let mut text = String::from(ORPHAN_HEADER);
        for (rule, _, _) in &orphans {
            let kb = interp.kb();
            text.push_str(&print::print_fact(kb, kb.rule_head(*rule), kb.rule_meta(*rule)));
            text.push_str("\n\n");
        }
        if let Err(e) = write_atomic(&path, &text) {
            eprintln!("error: writing {ORPHAN_FILE}: {e}");
            return runner::EXIT_RUNTIME;
        }
    }

    // THE BINDING IS REWRITTEN BEFORE THE OLD FILES GO, and the order is the
    // crash story rather than a preference. Both files present is the dangerous
    // state — every row exists twice — and only the NEW binding makes it loud:
    // the item-per-file store reads the old file too, finds each id in two places
    // and reports `DuplicateId`, which blocks at startup. Under the old binding
    // the same tree just loads every row twice and answers `list` with doubles.
    // So the window between these two steps is the one that shouts.
    let binding_file = match rewrite_binding(interp, project_items, per_file, store_root, &covered) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("error: rewriting the extent binding: {e}");
            eprintln!(
                "note: the new layout is written but this project still names the old one. \
                 Delete the new state directories to abandon the migration, or fix the binding by hand"
            );
            return runner::EXIT_RUNTIME;
        }
    };
    for (path, _) in &consumed {
        if let Err(e) = fs::remove_file(path) {
            eprintln!("error: removing the migrated file {}: {e}", path.display());
            return runner::EXIT_RUNTIME;
        }
    }

    println!(
        "migrated {rows} row(s) from {} file(s) into {}",
        consumed.len(),
        store_root.display()
    );
    println!("binding rewritten in {}", binding_file.display());
    if !orphans.is_empty() {
        println!(
            "{} row(s) name a work item that has no row of its own; they are kept in {ORPHAN_FILE}:",
            orphans.len()
        );
        for (_, functor, item) in &orphans {
            println!("  {functor} names `{item}`");
        }
        println!("`fsck` reports these from now on — they do not block anything");
    }
    println!("run `anthill-todo fsck` to check the new layout against the facts");
    0
}

/// Where migration keeps rows naming an item that has none of its own.
/// Fill a missing `created` from the item file's own creation time, and write the
/// row back (WI-1121).
///
/// THE REPAIR FOR A HAND-ADDED FILE. Someone can write an item file by hand and
/// leave the field out — it is not the sort of thing a person remembers — and the
/// loader fills the omission with a fresh VAR, which the startup gate then
/// refuses because a var cannot be sorted or hashed. Refusing is right; refusing
/// with no way forward is not. The filesystem knows when that file was made, and
/// under a file-per-item layout that time IS the item's.
///
/// IT WRITES THROUGH THE STORE'S OWN `update`, so the row is re-printed by the
/// same printer every other write uses and the file's chapters ride along
/// untouched — the `created` fill is a head-only change, and the description
/// beside it is not re-serialized.
///
/// ONLY UNDER A LAYOUT WHERE A FILE IS AN ITEM. A shared-file store has one file
/// for every row, so its creation time says nothing about any particular item;
/// there the migration's `--created-from` table is the answer, and this reports
/// nothing rather than stamping them all alike.
fn repair_created(
    interp: &mut Interpreter,
    store: &mut BuiltStore,
) -> Result<Vec<(String, String)>, String> {
    let BuiltStore::ItemPerFile(inner) = store else {
        return Ok(Vec::new());
    };
    let mut filled = Vec::new();
    for (rule, path) in inner.primary_rows() {
        let head = interp.kb().rule_head(rule);
        if named_string(interp.kb(), head, "created").is_some() {
            continue;
        }
        let Some(id) = named_string(interp.kb(), head, STAGE0_ID_FIELD) else {
            continue;
        };
        let Some(stamp) = file_created_at(&path) else {
            return Err(format!(
                "{}: `{id}` carries no `created` and this file's creation time cannot be read",
                path.display()
            ));
        };
        let new = with_created(interp, rule, &stamp)?;
        let (kind, domain, meta) = {
            let kb = interp.kb();
            (kb.rule_clause_kind(rule), kb.rule_domain(rule), kb.rule_meta(rule))
        };
        inner
            .update(interp.kb(), rule, new, kind, domain, meta)
            .map_err(|e| format!("{}: {e}", path.display()))?;
        filled.push((id, stamp));
    }
    if !filled.is_empty() {
        inner
            .flush(interp.kb())
            .map_err(|e| format!("writing the dated rows: {e}"))?;
    }
    Ok(filled)
}

/// When a file was created, in `now()`'s spelling — the fallback source for a
/// `created` stamp (WI-1121).
///
/// THE FILESYSTEM KNOWS THIS, and for a hand-added item file it is the honest
/// answer: someone made that file at a time, and under the file-per-item layout
/// that time IS the item's. It is what turns a missing stamp from a refusal into
/// a repair.
///
/// BIRTH TIME, FALLING BACK TO MODIFICATION TIME, and the fallback is not a
/// silent degrade: `created()` is genuinely unsupported on some filesystems
/// (older ext4 without `crtime`), where `modified()` is the closest true thing —
/// an upper bound on when the file appeared, and never wrong by more than the
/// edits since. Both are approximations, which is exactly what `created` tolerates:
/// it is used for ORDERING and for the day partition an id is minted in, neither
/// of which needs better than a day (§6.5).
///
/// A SHARED FILE IS THE ONE PLACE THIS IS WEAK: every item in it gets the same
/// stamp, so the whole tracker lands in one day partition. That is why
/// `--created-from` stays the preferred source and this is the fallback — the
/// git-history table dates each id separately.
fn file_created_at(path: &Path) -> Option<String> {
    let meta = fs::metadata(path).ok()?;
    let at = meta.created().or_else(|_| meta.modified()).ok()?;
    let secs = at.duration_since(std::time::UNIX_EPOCH).ok()?.as_secs();
    let at = chrono::DateTime::from_timestamp(secs as i64, 0)?;
    Some(at.format("%Y-%m-%dT%H:%M:%SZ").to_string())
}

/// Which rows need a `created` stamp written into them, and from what (WI-1121).
///
/// SHARED BY BOTH MIGRATIONS, and that sharing is the fix for a real dead end:
/// `--to item-per-file` used to write documents without consulting the table at
/// all, so a tracker predating the field landed on disk carrying
/// `created: ?created` — an unbound variable — and was then unusable. The startup
/// gate refused every command including the `migrate` its own message named, and
/// `--to document` reported "already a document" and exited 0 without stamping.
/// Nothing could fill the field in.
///
/// TWO SOURCES, IN ORDER, AND IT NEVER REFUSES. `--created-from` first, because a
/// table derived from git history dates each id separately; the FILE'S OWN
/// creation time otherwise, because the filesystem knows when someone made that
/// file and under a per-item layout that is the item's own answer. Migration is
/// how a project adopts this version, and a migration that refuses over a field
/// it could have derived is a barrier rather than a check.
///
/// WHICH SOURCE EACH ITEM USED IS REPORTED, not silent — the two are not equally
/// good. A shared file gives every item in it one stamp, so the whole tracker
/// lands in one day partition, where §6.5's collision scope is the tracker at
/// once; the table does not. Saying which was used is what lets someone who cares
/// re-run with a table.
fn plan_created_stamps(
    interp: &Interpreter,
    consumed: &[(&Path, Vec<anthill_core::kb::RuleId>)],
    created: &std::collections::HashMap<String, String>,
) -> CreatedPlan {
    let mut plan = CreatedPlan::default();
    for (path, rules) in consumed {
        for &rule in rules {
            let head = interp.kb().rule_head(rule);
            let Some(id) = named_string(interp.kb(), head, STAGE0_ID_FIELD) else {
                continue; // a satellite: it carries no id and needs no stamp
            };
            if named_string(interp.kb(), head, "created").is_some() {
                continue;
            }
            match created.get(&id) {
                Some(stamp) => {
                    plan.stamps.insert(rule, stamp.clone());
                    plan.from_table += 1;
                }
                None => match file_created_at(path) {
                    Some(stamp) => {
                        plan.stamps.insert(rule, stamp);
                        plan.from_file += 1;
                    }
                    // Neither source answered: the file is gone from under us, or
                    // its metadata is unreadable. Loud rather than defaulted — a
                    // stamp invented here would be indistinguishable from a real
                    // one forever after.
                    None => plan.undatable.push(id),
                },
            }
        }
    }
    plan
}

/// Where each newly-stamped row's `created` came from, so the migration can say.
#[derive(Default)]
struct CreatedPlan {
    stamps: std::collections::HashMap<anthill_core::kb::RuleId, String>,
    from_table: usize,
    from_file: usize,
    undatable: Vec<String>,
}

impl CreatedPlan {
    /// Print what was derived and from where, and refuse only if something was
    /// genuinely underivable.
    fn report(&self) -> Result<(), i32> {
        if !self.undatable.is_empty() {
            let mut ids = self.undatable.clone();
            ids.sort();
            eprintln!(
                "error: {} work item(s) carry no `created` stamp, are not named by \
                 `--created-from`, and their files' creation time cannot be read: {}",
                ids.len(),
                ids.join(", ")
            );
            return Err(runner::EXIT_RUNTIME);
        }
        if self.from_table > 0 {
            println!("dated {} item(s) from the supplied table", self.from_table);
        }
        if self.from_file > 0 {
            println!(
                "dated {} item(s) from their file's creation time — pass `--created-from <file>` \
                 to date each id separately instead (see \
                 rustland/anthill-todo/scripts/created_from_git.py)",
                self.from_file
            );
        }
        Ok(())
    }
}

/// `migrate --to document` — the SECOND full-tree pass (WI-1120, design §11).
///
/// WI-1118 exploded this repo's tracker into one plain `.anthill` file per item
/// on the rule that migration is cheap to repeat now that it touches no forge.
/// This is the repeat: every `WI-NNN.anthill` becomes a `WI-NNN.anthill.md`
/// document, head plus chapters. It changes no data — the same rows, the same
/// fields, redistributed between the fenced head and the markdown below it — so
/// a before/after row count is a complete correctness check, and it is the same
/// writer every ordinary command uses, so it is a test of that writer rather
/// than a second implementation of it.
///
/// IT ALSO BACK-DATES `created` (WI-1121), because the two passes rewrite the
/// same 1115 files and doing them separately would put two whole-tree diffs in
/// history for one mechanical change. The stamp is not invented here: `created`
/// feeds the id mint and the listing's order, and stamping every legacy item
/// with the migration date would collapse the whole tracker into ONE day
/// partition — where §6.5's collision scope is the entire tracker at once. It
/// comes from `--created-from`, a `<id><TAB><timestamp>` table, and an item the
/// table does not name is a REFUSAL rather than a default.
///
/// NO STORE-FORMAT BUMP, and the reason is §11 step 4's own: there is one
/// `current_store_format()` for the binary, so bumping it makes every project
/// still on `IndexedFileStore` — a supported layout that has no chapters and
/// never will — warn on every command that it is out of date. What makes an
/// unconverted tracker loud instead is the `created` gate, which fires on
/// exactly the projects this converts and on no others.
#[allow(clippy::too_many_arguments)]
fn run_migrate_to_document(
    interp: &mut Interpreter,
    declared: &DeclaredStore,
    store_root: &Path,
    project_items: &[ProjectFile],
    per_file: &[load::LoadResult],
    mapping: &DocumentMapping,
    created_from: Option<&str>,
) -> i32 {
    if !matches!(declared.store, BuiltStore::ItemPerFile(_)) {
        eprintln!(
            "error: `--to document` converts an item-per-file tree into documents, and this \
             project is not on that layout yet. Run `anthill-todo migrate --to item-per-file` \
             first — it writes documents directly."
        );
        return runner::EXIT_RUNTIME;
    }

    let created = match created_from {
        Some(path) => match read_created_table(Path::new(path)) {
            Ok(t) => t,
            Err(e) => {
                eprintln!("error: {e}");
                return runner::EXIT_RUNTIME;
            }
        },
        None => std::collections::HashMap::new(),
    };

    let mut covered = Vec::with_capacity(declared.covers.len());
    for name in &declared.covers {
        match interp.kb().try_resolve_symbol(name) {
            Some(s) => covered.push(s),
            None => {
                eprintln!("error: this project's binding covers `{name}`, which resolves to nothing");
                return runner::EXIT_RUNTIME;
            }
        }
    }

    // ONLY THE PLAIN FILES ARE CONVERTED. A tree half-way through this — an
    // interrupted run, or a re-run — holds both shapes, and a document that is
    // already a document must be left exactly as it is rather than re-rendered:
    // re-rendering would reflow every chapter and lose the hand-added prose the
    // opacity invariant exists to protect.
    //
    // SO THIS IS NOT WHERE AN ALREADY-CONVERTED FILE GETS A MISSING `created`
    // FILLED IN — `fsck --fix` is, and it is the better home anyway: it rewrites
    // the row's head through the store's own `update`, leaving every chapter
    // beside it byte-identical, where a re-conversion would not.
    let mut consumed: Vec<(&Path, Vec<anthill_core::kb::RuleId>)> = Vec::new();
    for (file, result) in project_items.iter().zip(per_file.iter()) {
        if file.document.is_some() {
            continue;
        }
        let mut mine = Vec::new();
        for &rule in &result.fact_rule_ids {
            let head = interp.kb().rule_head(rule);
            let Some(functor) = fact_functor(interp.kb(), head) else {
                continue;
            };
            if covered.contains(&functor) {
                mine.push(rule);
            }
        }
        // ONLY ITEM FILES ARE CONVERTED. The document encoding is about an
        // item's PROSE, and a file holding no item holds none — the format stamp
        // at the tree's root is a `StoreFormat` row and stays exactly where and
        // as it is. Converting it would mean writing it through a store that
        // never read it, which is `refuse_unknown_occupant`'s refusal and,
        // correctly, its own answer to "should this file be rewritten": no.
        let holds_item = mine.iter().any(|&rule| {
            named_string(interp.kb(), interp.kb().rule_head(rule), STAGE0_ID_FIELD).is_some()
        });
        if mine.is_empty() || !holds_item {
            continue;
        }
        let (facts, others) = item_census(&file.parsed);
        if mine.len() != facts || others != 0 {
            eprintln!(
                "error: {} holds {} row(s) this store covers and {} item(s) it does not; \
                 conversion moves a whole file or none of it, and it removes the files it moves",
                file.path.display(),
                mine.len(),
                facts - mine.len() + others,
            );
            return runner::EXIT_RUNTIME;
        }
        consumed.push((file.path.as_path(), mine));
    }
    if consumed.is_empty() {
        println!("migrate: every item file is already a document");
        return 0;
    }

    let plan = plan_created_stamps(interp, &consumed, &created);
    if let Err(code) = plan.report() {
        return code;
    }
    let stamped = plan.stamps;

    let mut target = ItemPerFileStore::new(
        store_root.to_path_buf(),
        ItemFields::new(STAGE0_STATUS_FIELD, STAGE0_ID_FIELD, STAGE0_REF_FIELD),
    )
    .with_document_mapping(mapping.clone());
    let mut rows = 0usize;
    for (path, rules) in &consumed {
        for &rule in rules {
            let head = match stamped.get(&rule) {
                Some(stamp) => match with_created(interp, rule, stamp) {
                    Ok(t) => t,
                    Err(e) => {
                        eprintln!("error: {}: {e}", path.display());
                        return runner::EXIT_RUNTIME;
                    }
                },
                None => interp.kb().rule_head(rule),
            };
            let kb = interp.kb();
            if let Err(e) = target.persist(
                kb,
                head,
                kb.rule_clause_kind(rule),
                kb.rule_domain(rule),
                kb.rule_meta(rule),
            ) {
                eprintln!("error: {}: {e}", path.display());
                return runner::EXIT_RUNTIME;
            }
            rows += 1;
        }
    }
    if let Err(e) = target.flush(interp.kb()) {
        eprintln!("error: writing the documents: {e}");
        eprintln!(
            "note: the old files are untouched, but a partly written set of documents may be on \
             disk beside them. Remove the `*{ITEM_DOCUMENT_SUFFIX}` files under {} before running \
             this again",
            store_root.display()
        );
        return runner::EXIT_RUNTIME;
    }
    // The old files go LAST, so a crash leaves both encodings — which the next
    // load names as a `DuplicateId`, loud and repairable — rather than a hole.
    for (path, _) in &consumed {
        if let Err(e) = fs::remove_file(path) {
            eprintln!("error: removing the converted file {}: {e}", path.display());
            return runner::EXIT_RUNTIME;
        }
    }
    println!(
        "migrated {} file(s), {rows} row(s), to `*{ITEM_DOCUMENT_SUFFIX}` documents",
        consumed.len()
    );
    if !stamped.is_empty() {
        println!("back-dated `created` on {} item(s)", stamped.len());
    }
    0
}

/// A `<id><TAB><timestamp>` table. Blank lines and `#` comments are skipped; a
/// line that is neither is a REFUSAL, because a table half-read would silently
/// leave items undated and the refusal above would then name the wrong cause.
fn read_created_table(path: &Path) -> Result<std::collections::HashMap<String, String>, String> {
    let text =
        fs::read_to_string(path).map_err(|e| format!("reading {}: {e}", path.display()))?;
    let mut out = std::collections::HashMap::new();
    for (n, line) in text.lines().enumerate() {
        let line = line.trim_end();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let Some((id, stamp)) = line.split_once('\t') else {
            return Err(format!(
                "{}:{}: expected `<id><TAB><timestamp>`, got `{line}`",
                path.display(),
                n + 1
            ));
        };
        out.insert(id.trim().to_string(), stamp.trim().to_string());
    }
    Ok(out)
}

/// The row's head with `created` inserted right after `id`.
///
/// POSITION MATTERS ONLY TO A READER, and that is reason enough: the field is
/// identity-adjacent and belongs beside the id in every one of 1115 files, not
/// appended after `status` because that is where a push lands.
fn with_created(
    interp: &mut Interpreter,
    rule: anthill_core::kb::RuleId,
    stamp: &str,
) -> Result<TermId, String> {
    let head = interp.kb().rule_head(rule);
    let Term::Fn {
        functor,
        pos_args,
        named_args,
    } = interp.kb().get_term(head).clone()
    else {
        return Err("a work item whose head has no fields cannot be stamped".to_string());
    };
    let kb = interp.kb_mut();
    let created_sym = kb.intern("created");
    let value = kb.alloc(Term::Const(Literal::String(stamp.to_string())));
    let mut named = named_args.clone();
    // REPLACE, NOT INSERT, when the slot is already there. It usually IS: the
    // loader fills an omitted REQUIRED field with a fresh var, so every legacy
    // row reaches this carrying `created: ?created` — invisible in the source
    // file it came from and very visible in the one this writes. Pushing a
    // second `created:` beside it produced a duplicate named argument, which
    // the loader refuses; the whole rehearsed tree failed to reload.
    match named
        .iter()
        .position(|(s, _)| kb.local_name_of(*s) == "created")
    {
        Some(at) => named[at] = (created_sym, value),
        None => {
            let at = named
                .iter()
                .position(|(s, _)| kb.local_name_of(*s) == STAGE0_ID_FIELD)
                .map(|i| i + 1)
                .unwrap_or(0);
            named.insert(at, (created_sym, value));
        }
    }
    Ok(kb.alloc(Term::Fn {
        functor,
        pos_args,
        named_args: named,
    }))
}

/// A term's string-valued named argument.
fn named_string(kb: &KnowledgeBase, term: TermId, field: &str) -> Option<String> {
    let Term::Fn { named_args, .. } = kb.get_term(term) else {
        return None;
    };
    named_args
        .iter()
        .find(|(s, _)| kb.local_name_of(*s) == field)
        .and_then(|(_, t)| match kb.get_term(*t) {
            Term::Const(Literal::String(s)) => Some(s.clone()),
            _ => None,
        })
}

const ORPHAN_FILE: &str = "orphaned.anthill";

const ORPHAN_HEADER: &str = "\
-- Rows naming a work item that has no row of its own, kept here by
-- `anthill-todo migrate --to item-per-file`: the new layout files a row in its
-- item's file, and these have no item.
--
-- They are not damage. Until WI-1123 `Feedback` was `monotone` — it could not be
-- retracted — so deleting a work item left its feedback behind, and this is where
-- that feedback lives once every other row has moved into its item's file.
-- `delete` takes an item's feedback with it now, so nothing new lands here.
-- `fsck` reports each one as an orphan and does not block on it.
--
-- To retire one, delete it here. To give it a home again, restore the item it
-- names and move the row into that item's file.

";

const MIGRATE_USAGE: &str = "\
usage: anthill-todo migrate [--to item-per-file | --to document] [--created-from FILE]

  migrate                   stamp a pre-versioning project with the current data
                            format (the SCHEMA a row is written in).
  migrate --to item-per-file
                            move this project's work items from one shared file to
                            one file per item under a directory per state, and
                            rewrite its `ExtentBinding` to name the new layout.
                            Each item is written as a DOCUMENT (see below).
  migrate --to document     convert an item-per-file tree that still holds plain
                            `WI-NNN.anthill` files into `WI-NNN.anthill.md`
                            documents: an anthill head of facts, then the prose
                            fields as markdown chapters. Changes no data.
      --created-from FILE   a `<id><TAB><timestamp>` table supplying `created` for
                            items filed before the field existed. Applies to
                            EITHER `--to`, and is optional: an item the table does
                            not name is dated from its own file's creation time
                            instead, and the run says which source it used. Prefer
                            the table — it dates each id separately, where a
                            shared file dates every item in it alike.
                            `rustland/anthill-todo/scripts/created_from_git.py`
                            derives one from git history.

Two jobs under one name, and they do not overlap: the first versions how a row is
written, the second which file it lives in.

The layout move is purely local: no network, no forge. Publishing the tracker to a
forge is a separate operation.

THE DATA-FORMAT STAMP IS NOT TOUCHED. `StoreFormat` versions the SCHEMA a row is
written in, and this changes no schema — the same entities with the same fields,
redistributed across files. What changed is the layout, which `ExtentBinding`
already records and which the host already refuses loudly when a build has no
backend for it.";

/// The rows about to be migrated that name a work item no row defines, as
/// `(the row, its functor, the id it names)` in source order.
///
/// The same classification the store routes by — a row carrying the id field is
/// the item, a row carrying the reference field is a satellite of one — but asked
/// of the whole set at once, which is the question migration has and a per-write
/// store does not: the store is handed one row and cannot know whether the item
/// it names is somewhere later in the same flush.
fn orphan_satellites(
    kb: &KnowledgeBase,
    consumed: &[(&Path, Vec<anthill_core::kb::RuleId>)],
) -> Vec<(anthill_core::kb::RuleId, String, String)> {
    let mut items: Vec<String> = Vec::new();
    let mut refs: Vec<(anthill_core::kb::RuleId, String, String)> = Vec::new();
    for (_, rules) in consumed {
        for &rule in rules {
            let head = kb.rule_head(rule);
            let Term::Fn {
                functor, named_args, ..
            } = kb.get_term(head)
            else {
                continue;
            };
            // The store's own field reader, so "carries the id field" means here
            // exactly what it means when the store routes the same row.
            let arg = |field: &str| get_named_string_arg(kb, named_args, field);
            if let Some(id) = arg(STAGE0_ID_FIELD) {
                items.push(id);
            } else if let Some(item) = arg(STAGE0_REF_FIELD) {
                refs.push((rule, kb.local_name_of(*functor).to_string(), item));
            }
        }
    }
    refs.retain(|(_, _, item)| !items.contains(item));
    refs
}

/// What a parsed file holds, as `(facts, everything else)`.
///
/// "Everything else" counts an `import` and a namespace `{< … >}` description
/// block too: they are not `items` (a `Namespace` carries them as its own fields)
/// but they are content, and a file being consumed must have none of it.
///
/// Namespaces are descended rather than counted, and the synthetic one
/// [`assign_default_namespace`] wraps a bare fact file in is exactly why: counted,
/// every project file would look like it held one non-fact item.
fn item_census(parsed: &ParsedFile) -> (usize, usize) {
    use anthill_core::parse::ir::Item;

    fn walk(items: &[Item], facts: &mut usize, others: &mut usize) {
        for item in items {
            match item {
                Item::Fact(_) => *facts += 1,
                Item::Namespace(ns) => {
                    *others += ns.imports.len() + ns.descriptions.len();
                    walk(&ns.items, facts, others);
                }
                _ => *others += 1,
            }
        }
    }

    let (mut facts, mut others) = (0, 0);
    walk(&parsed.items, &mut facts, &mut others);
    (facts, others)
}

/// The functor a fact's head names, or `None` for a head that has none.
fn fact_functor(
    kb: &KnowledgeBase,
    term: TermId,
) -> Option<anthill_core::intern::Symbol> {
    match kb.get_term(term) {
        Term::Fn { functor, .. } => Some(*functor),
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        _ => None,
    }
}

/// Point the project's `ExtentBinding` at the item-per-file layout, and answer
/// which file was changed.
///
/// A SPLICE OVER THE FACT'S OWN SPAN, not a regenerated file. `project.anthill` is
/// hand-written and its comments explain the binding they sit above; rewriting the
/// whole file would deliver a correct binding and silently drop the prose that
/// says why it reads the way it does.
///
/// A project that declared NO binding was running on [`default_binding`], which is
/// a value with no text behind it — so there is no span to splice and the binding
/// is appended instead. That shape is supported (`PROJECT_MARKERS` accepts a
/// directory holding nothing but `workitems.anthill`), so it gets a written
/// binding here rather than a refusal.
fn rewrite_binding(
    interp: &Interpreter,
    project_items: &[ProjectFile],
    per_file: &[load::LoadResult],
    store_root: &Path,
    covered: &[anthill_core::intern::Symbol],
) -> Result<PathBuf, String> {
    let binding_sym = interp
        .kb()
        .try_resolve_symbol("anthill.persistence.ExtentBinding")
        .ok_or("`anthill.persistence.ExtentBinding` does not resolve")?;

    // `covers` is carried across verbatim rather than re-derived: it is the
    // project's statement of what this store holds, and migration changes where
    // rows live, not which ones are held. Short names, because that is what
    // resolves in the file being written.
    let covers: Vec<&str> = covered
        .iter()
        .map(|s| interp.kb().local_name_of(*s))
        .collect();
    let text = item_per_file_binding(&covers);

    for (file, result) in project_items.iter().zip(per_file.iter()) {
        // IN THE FILE'S COORDINATES (WI-1120): this splices the binding's text
        // into the file it was read from, so a head-relative span would cut at
        // the wrong offset. `project.anthill` is never a document, so today the
        // two agree — the shift is taken anyway rather than resting on that.
        let spans = file.fact_spans_in_file();
        if spans.len() != result.fact_rule_ids.len() {
            return Err(format!(
                "{}: {} fact span(s) against {} loaded fact(s)",
                file.path.display(),
                spans.len(),
                result.fact_rule_ids.len()
            ));
        }
        for (&rule, span) in result.fact_rule_ids.iter().zip(spans.iter()) {
            let head = interp.kb().rule_head(rule);
            if fact_functor(interp.kb(), head) != Some(binding_sym) {
                continue;
            }
            let source = fs::read_to_string(&file.path)
                .map_err(|e| format!("{}: {e}", file.path.display()))?;
            let (start, end) = (span.start as usize, span.end as usize);
            let (before, after) = (
                source
                    .get(..start)
                    .ok_or_else(|| format!("{}: {start} is not a character boundary", file.path.display()))?,
                source
                    .get(end..)
                    .ok_or_else(|| format!("{}: {end} is not a character boundary", file.path.display()))?,
            );
            write_atomic(&file.path, &format!("{before}{text}{after}"))?;
            return Ok(file.path.clone());
        }
    }

    let path = store_root.join("project.anthill");
    let mut source = match fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => String::new(),
        Err(e) => return Err(format!("{}: {e}", path.display())),
    };
    if !source.is_empty() && !source.ends_with('\n') {
        source.push('\n');
    }
    source.push_str("\n-- Written by `anthill-todo migrate --to item-per-file`.\n");
    source.push_str(&text);
    source.push('\n');
    write_atomic(&path, &source)?;
    Ok(path)
}

/// Write through a temp file and a rename, the way the stores do.
///
/// The binding rewrite is the step whose interruption the migration's ordering is
/// designed around (see [`run_migrate`]), and that reasoning assumes the file is
/// either the old binding or the new one. A truncating write can leave it neither.
fn write_atomic(path: &Path, content: &str) -> Result<(), String> {
    let temp = path.with_extension("anthill.tmp");
    fs::write(&temp, content).map_err(|e| format!("{}: {e}", temp.display()))?;
    fs::rename(&temp, path).map_err(|e| format!("{} → {}: {e}", temp.display(), path.display()))
}

/// The `ExtentBinding` text a migrated project carries. Twin of the
/// [`EXAMPLE_BINDING`] `init` scaffolds, for the other layout.
fn item_per_file_binding(covers: &[&str]) -> String {
    format!(
        "fact anthill.persistence.ExtentBinding(\n  \
           store: anthill.persistence.filesystem.ItemPerFileStore(\n    \
             root: \".\",\n    \
             status_field: \"{STAGE0_STATUS_FIELD}\",\n    \
             id_field: \"{STAGE0_ID_FIELD}\",\n    \
             ref_field: \"{STAGE0_REF_FIELD}\"),\n  \
           role: anthill.persistence.ExtentRole.mirror(),\n  \
           covers: [{}])",
        covers.join(", ")
    )
}

/// stage0's spelling of the three fields [`ItemPerFileStore`] routes on. They are
/// this CLI's knowledge, not the storage substrate's — which is why they travel in
/// the project's binding — and these constants are where the binding gets written
/// from and, through it, where `declared_fields` reads them back.
const STAGE0_STATUS_FIELD: &str = "status";
const STAGE0_ID_FIELD: &str = "id";
const STAGE0_REF_FIELD: &str = "workitem";

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
    let mut covers = Vec::with_capacity(STORED_FUNCTORS.len());
    for (name, _) in STORED_FUNCTORS {
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
/// tag_item / stamp_format), and so the ones the default binding covers — each
/// flagged with whether the bundle also RETRACTS its rows.
///
/// The flag is `store.anthill` §0's `non_monotone` set, read from the other side:
/// `WorkItem` (forget / replace), `Feedback` (forget, since WI-1123) and `Tag`
/// (forget / untag_item). `StoreFormat` is persisted and never retracted.
///
/// ONE LIST, TWO READERS, deliberately: `default_binding` takes every name, and
/// [`check_covers_every_retracted_functor`] takes the flagged ones. Kept apart they
/// drift, and the drift is silent in the direction that matters — a functor added
/// to the default while the guard still names three.
const STORED_FUNCTORS: [(&str, Retracted); 4] = [
    ("anthill.stage0.WorkItem", Retracted::Yes),
    ("anthill.stage0.Feedback", Retracted::Yes),
    ("anthill.stage0.Tag", Retracted::Yes),
    ("anthill.stage0.StoreFormat", Retracted::No),
];

/// Whether the bundle ever asks the store to remove a functor's rows.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Retracted {
    Yes,
    No,
}

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
    // The fact<->markdown mapping, read out of the bundle's own parse IR because
    // it is needed to READ the project's files (WI-1120) — see `document_mapping`
    // for why the KB is too late.
    let mapping = match document_mapping(&bundle_parsed) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("error: the bundled document mapping is malformed: {e}");
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
        // AN ITEM DOCUMENT IS PARSED AT ITS HEAD (WI-1120): the fenced block is
        // anthill and everything after it is markdown, so the parser is handed
        // the head alone and the chapters are spliced back into the facts they
        // fill before the loader sees them.
        //
        // The load-error rendering is the honest cost, and it is small: the head
        // is what `parsed.source` holds, so a `line:col` inside a document counts
        // from the head's first line rather than the file's — off by the one
        // fence line above it.
        let document = if fs_util::has_suffix(file, &[ITEM_DOCUMENT_SUFFIX]) {
            match document::read_document(&source, &mapping) {
                Ok(doc) => Some(doc),
                Err(e) => {
                    eprintln!("error: {}: {e}", file.display());
                    return runner::EXIT_COMPILE;
                }
            }
        } else {
            None
        };
        let head = match &document {
            Some(doc) => &source[doc.head.clone()],
            None => source.as_str(),
        };
        match parse::parse(head) {
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
                if let Some(doc) = &document {
                    if let Err(e) = inject_chapters(&mut parsed, &source, doc, &mapping) {
                        eprintln!("error: {}: {e}", file.display());
                        return runner::EXIT_COMPILE;
                    }
                }
                let parsed = parsed.with_path(file.clone());
                project_items.push(ProjectFile {
                    path: file.clone(),
                    parsed,
                    source,
                    document,
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
                for located in ParseError::all_located(&errs, file, head) {
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
        &mapping,
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
        return run_fsck(&mut interp, &mut declared.store, &bundle_argv[1..]);
    }

    // `migrate --to <layout>` is served here for the same reason and one more.
    // Like `fsck` it wants the concrete backend — to answer "already migrated" off
    // the binding rather than by guessing at the tree. Unlike `fsck` it also needs
    // the SECOND store, and the bundle cannot construct one: `open_store` is not
    // expressible against today's spec (design §8.2.1, WI-1113 measured), so the
    // anthill side has no way to write rows through a store other than the one it
    // was handed. The host holds both, so the layout move lives here.
    //
    // The bundle keeps its own `migrate`, which stamps a pre-versioning project
    // with the current data format (WI-434). The two do not overlap: that one is
    // about the SCHEMA a row is written in, this one about which file it lives in.
    //
    // `--to` is what selects THIS `migrate` over the bundle's, so a bare
    // `migrate` still reaches the schema stamp. `--help` is taken too, because
    // otherwise the one command that has options is the one whose usage text is
    // unreachable (found in review) — and the text covers both forms, since from
    // the outside they are one command's two jobs.
    if bundle_argv.first().map(|s| s.as_str()) == Some("migrate")
        && bundle_argv[1..]
            .iter()
            .any(|a| a == "--to" || a.starts_with("--to=") || a == "--help" || a == "-h")
    {
        return run_migrate(
            &mut interp,
            &declared,
            &store_root,
            &project_items,
            &per_file_results[project_offset..],
            &mapping,
            &bundle_argv[1..],
        );
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

    // The `Cell[V = WIS]` the bundle receives. It is the ONLY way the backend
    // reaches the bundle — every command body goes through the `WorkItemStore`
    // spec ops on it (WI-1113 removed the parallel `store: FileStore` path).
    //
    // THE COUNTER SEED IS GONE (WI-1121). This used to scan every loaded row for
    // the highest `WI-NNN` and hand the bundle `max + 1` to allocate from —
    // which IS the id-collision bug design §1.2 names, not a step towards fixing
    // it: two checkouts scan their own trees, reach the same number, and hand it
    // to two different items. `mint_id` derives an id from the item instead
    // (author, `created`, description), so there is no counter, nothing for the
    // host to scan, and no state to carry between commands. The one site that
    // parsed the digits out of an id is this one, and it is why grandfathered
    // `WI-NNN` ids can coexist with minted ones forever — nothing else reads an
    // id as anything but a string.
    let wis_cell_value = {
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
            &[store_value.clone()],
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
    // WI-239: NOT flat-transitive — a transitive require is bundled inside its direct
    // parent's dict, not given a top-level slot, so the count and order line up with
    // the frame's `__req_*` names rather than with a flattened walk.
    //
    // WI-867: and the list is `provider_dict_entries`, which is the one
    // `call_with_requirements` counts against — WI-869 widened THAT to a sort's direct
    // `requires` FOLLOWED BY its conditional provisions' `:- goals`, and this host was
    // still reading `direct_requires_chain`. The two agree only while `Main` declares
    // no conditional provision; the day it does, the old read hands over fewer
    // dictionaries than there are slots, and the host learns it as a count mismatch at
    // the entry rather than as a slot it forgot to fill.
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
        let entries: Vec<_> =
            anthill_core::kb::typing::provider_dict_entries(interp.kb_mut(), main_sym)
                .entries()
                .to_vec();
        let mut out: smallvec::SmallVec<[_; 2]> = smallvec::SmallVec::new();
        for entry in &entries {
            let impl_sym = if Some(entry.required_sort) == workitemstore_sym {
                filebased_sym
            } else {
                entry.required_sort
            };
            // WI-867: the SPEC beside the provider, and empty subs only because the
            // layout says so. Today both chains are empty, which is the accident that
            // made the pre-WI-867 blind call valid; when 058 phase 7 gives these specs
            // chains this refuses HERE, naming the spec, the provider and both halves,
            // instead of dying at a frame push inside `Main.main`.
            match interp.alloc_dictionary(entry.required_sort, impl_sym, []) {
                Ok(d) => out.push(d),
                // Reported, not panicked: this is a HOST bug — the dictionary this
                // binary hands `Main` is the wrong shape — and the refusal already
                // names the spec, the provider and both halves. A panic would bury
                // that under a backtrace in the one place it is addressed to.
                Err(e) => {
                    eprintln!("error: {e}");
                    return runner::EXIT_RUNTIME;
                }
            }
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
