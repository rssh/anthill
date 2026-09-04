use std::collections::{BTreeMap, BTreeSet};
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
mod forge;

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
/// `find_project_dir` hands it only directories it has already proven exist (an
/// explicit `-d` must `is_dir()`; discovery needs a marker FILE inside, which is
/// proof the directory holding it is there). So the path always exists — and if that
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
/// `project.anthill`; a project on the single-file layout accrues `workitems.anthill`.
/// Either alone is proof (a pre-versioning project predates `project.anthill`).
///
/// AN ITEM-PER-FILE PROJECT IS MARKED BY THE FIRST ALONE, and that is why `init` writes
/// `project.anthill` unconditionally: the item tree carries no file at a fixed name — its
/// contents are one directory per status, all of them absent until something is filed —
/// so a scaffold that leaned on the second marker would leave a fresh project
/// undiscoverable until its first `add`.
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
///
/// `Err` ON A STAT THAT FAILS FOR ANY REASON BUT "NOT THERE" — an unreadable
/// directory, a broken mount, a symlink loop. `Path::is_file()` answers `false`
/// for all of those exactly as it does for a missing file, and under the ancestor
/// walk (WI-20260828-C8SG5) that swallow stopped being harmless: "no marker here"
/// means KEEP WALKING, so an EACCES on the project the user is standing in would
/// hand the next command a DIFFERENT project further up and write into it. A
/// permission wall is not a fact about where the project is (CLAUDE.md: prefer a
/// loud error over a silent skip).
fn is_project_dir(dir: &Path) -> Result<bool, String> {
    for marker in PROJECT_MARKERS {
        let candidate = dir.join(marker);
        match fs::metadata(&candidate) {
            Ok(md) if md.is_file() => return Ok(true),
            Ok(_) => {}
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => {
                return Err(format!(
                    "cannot read {}: {e}\n  \
                     A marker that cannot be STATTED is not a marker that is absent, so \
                     project discovery stops here rather than resolve to some other \
                     project further up the tree.",
                    candidate.display()
                ))
            }
        }
    }
    Ok(false)
}

/// The directory to SCAN, if `dir` locates a project — either in its
/// `anthill-todo/` subdirectory (the normal layout) or in itself (the flat
/// layout). `Ok(None)` when it locates neither.
///
/// THE MARKER TEST AND THE SCAN TARGET ARE ONE DECISION, and that is the whole
/// point of this function. They used to be two: `find_project_dir` proved a
/// project by MARKER and returned the directory ABOVE it, and a separate
/// `scan_dir` then re-derived the scan root by NAME (`<dir>/anthill-todo`, if
/// `is_dir()`). The two could disagree, and this repo's own shape is the
/// counterexample again — a flat project at `<d>/workitems.anthill` beside a
/// MARKER-LESS `<d>/anthill-todo/` (a crate, a scratch directory) resolved on the
/// flat marker and then scanned the marker-less directory: `list` said "No work
/// items found", exit 0, and `add` opened a SECOND store inside it, orphaning the
/// rows discovery had just matched on. Returning the scanned directory itself
/// makes that disagreement unrepresentable (found by /code-review).
fn scan_root_at(dir: &Path) -> Result<Option<PathBuf>, String> {
    let subdir = dir.join("anthill-todo");
    if is_project_dir(&subdir)? {
        // A HALF-MIGRATED PROJECT KEEPS BOTH, and the subdirectory wins. Say which
        // file is being ignored: its rows are not in the listing, and `add` mints
        // ids without seeing the ids in it.
        if is_project_dir(dir)? {
            for marker in PROJECT_MARKERS {
                let stray = dir.join(marker);
                if stray.is_file() {
                    eprintln!(
                        "warning: ignoring {} — {} holds a project and takes precedence",
                        stray.display(),
                        subdir.display()
                    );
                }
            }
        }
        return Ok(Some(subdir));
    }
    if is_project_dir(dir)? {
        return Ok(Some(dir.to_path_buf()));
    }
    Ok(None)
}

/// Find the directory to SCAN for the project's files. Checks, in order:
/// 1. An explicit `--dir` flag, resolved through the same two arms (so `-d` cannot
///    route to a marker-less `anthill-todo/` either); a directory locating no
///    project at all is still accepted, and reports itself empty downstream.
/// 2. Cwd AND EVERY ANCESTOR, NEAREST FIRST, each tried the same two ways.
///
/// WI-20260828-C8SG5: THE ANCESTOR WALK IS NOT A RETURN OF THE WI-744 FOOTGUN — it
/// is the MARKER test, not the search depth, that rejects `rustland/anthill-todo/`
/// (this CLI's own crate, which holds no `project.anthill`). Walking up from
/// `rustland/` now reaches the repo's real tracker one level further up, which is
/// the project WI-744 wanted found there; the crate is not a candidate at any depth.
///
/// It became necessary when the item-per-file layout (WI-1118) gave a project
/// SUBDIRECTORIES: `<proj>/anthill-todo/claimed/` is where a user stands while
/// editing a `WI-….anthill.md`, and a bare `list` from there used to exit 1 —
/// advising `init`, which would have nested a SECOND project inside the tracker
/// (`run_init` now refuses that outright).
///
/// THE WALK IS UNBOUNDED — no `.git`, no `$HOME`, no filesystem-boundary stop — so
/// the answer can be far from the cwd, and a MUTATING command would then write
/// there. Every match above the cwd itself therefore NAMES the directory it chose,
/// on stderr. WI-744 deleted a warning on the AT-cwd path because it annotated
/// every normal invocation and distinguished nothing; this one fires only where
/// the project is somewhere the cwd does not show, which is exactly the case that
/// warning could not cover.
fn find_project_dir(explicit: Option<&Path>) -> Result<PathBuf, String> {
    if let Some(dir) = explicit {
        if dir.is_dir() {
            return Ok(scan_root_at(dir)?.unwrap_or_else(|| dir.to_path_buf()));
        }
        return Err(format!(
            "project directory does not exist: {}",
            dir.display()
        ));
    }

    let cwd =
        std::env::current_dir().map_err(|e| format!("cannot determine current directory: {e}"))?;

    // Discovery is by MARKER, not by name or by "holds some .anthill file", so a
    // successful match needs no warning to caveat it (WI-744) — only a match the
    // cwd does not show does, and that is the `depth > 0` note below.
    for (depth, dir) in cwd.ancestors().enumerate() {
        if let Some(root) = scan_root_at(dir)? {
            if depth > 0 {
                eprintln!(
                    "note: using the anthill-todo project at {} (found by searching upward \
                     from {})",
                    root.display(),
                    cwd.display()
                );
            }
            return Ok(root);
        }
    }

    Err(format!(
        "no anthill-todo project found in {cwd} or any parent directory.\n  \
         Looked for <dir>/anthill-todo/{markers} and <dir>/{markers} at every level \
         from {cwd} up to the filesystem root.\n  \
         Run `anthill-todo init`, or pass -d <project-dir>.",
        cwd = cwd.display(),
        markers = format!("{{{}}}", PROJECT_MARKERS.join(",")),
    ))
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
    // WI-909 — THE WRAPPER CARRIES THE CONSTRUCTOR IMPORTS, and it must, because imports
    // are FILE-LOCAL (WI-995 / WI-1074). The doc above says this wrapper "reuses the scope
    // the project's `domain.anthill` set up (entity definitions + prelude imports)"; the
    // first half is true and the second never was. A scope carries DECLARATIONS across
    // files, not imports -- so `domain.anthill`'s `import anthill.prelude.Option.{some}`
    // has never been visible here, and a document's `some(value: "x")` resolved solely
    // through `kb::load`'s implicit tier.
    //
    // WI-909 emptied that tier, which made this the ON-DISK FORMAT'S problem rather than
    // a test's: the printer emits `some(value: …)` into every stored item document, and a
    // synthesized wrapper with no imports could no longer resolve it. MEASURED -- the
    // delete / tag / document-format suites failed with
    // `match_failed(occurrence: Node, scrutinee: Term)`, a RUNTIME failure, because a
    // document's facts load clean and only misbehave when matched against.
    //
    // Supplied here rather than at the tier because this is exactly what a file-local
    // import is for, and because the store is the component that knows these facts are
    // `anthill.stage0` ones. The names are the four the printer can emit: `Option`'s pair
    // for a wrapped optional, `List`'s for a `depends_on` chain.
    let mut imports = Vec::new();
    for (owner, members) in SYNTHETIC_WRAPPER_IMPORTS {
        let mut path: SmallVec<[anthill_core::intern::Symbol; 2]> = SmallVec::new();
        path.push(pf.symbols.intern("anthill"));
        path.push(pf.symbols.intern("prelude"));
        path.push(pf.symbols.intern(owner));
        let selected = members
            .iter()
            .map(|m| {
                let mut segs: SmallVec<[anthill_core::intern::Symbol; 2]> = SmallVec::new();
                segs.push(pf.symbols.intern(m));
                Name {
                    segments: segs,
                    span: Span::default(),
                }
            })
            .collect();
        imports.push(anthill_core::parse::ir::Import {
            path: Name {
                segments: path,
                span: Span::default(),
            },
            kind: anthill_core::parse::ir::ImportKind::Selective(selected),
        });
    }

    let items = std::mem::take(&mut pf.items);
    pf.items.push(Item::Namespace(Namespace {
        name,
        // Synthetic ownership wrapper, not a source declaration: it has no written
        // description blocks of its own.
        descriptions: Vec::new(),
        imports,
        items,
        span: Span::default(),
    }));
}

// ── The declared document format (WI-K63ZV) ──────────────────────

/// Read `anthill.stage0.document`'s facts, and the domain's own entity
/// declarations, out of the BUNDLE'S PARSE IR.
///
/// WHY THE IR AND NOT THE KB, which is where every other declaration this host
/// reads comes from: the mapping is needed to READ the project's own files, and
/// the KB does not exist yet at that point. A document holds its item's fact as
/// DATA, so reading one means turning an attributes chapter into the facts a
/// plain `fact` file would have declared BEFORE the loader sees it.
///
/// The bundle is EMBEDDED, so this is not a second source of truth: it is the
/// same text, read one phase earlier. The same facts also load into the KB like
/// any other, which keeps them declarations rather than a private side-channel.
///
/// THE SCHEMA COMES WITH IT, and that is the real departure from WI-1120's
/// encoding: a value's spelling follows its DECLARED TYPE (§3.2), so the reader
/// needs the types. It reads them from the same bundle, so there is still only
/// one place either is written.
fn document_mapping(bundle: &[ParsedFile]) -> Result<DocumentMapping, String> {
    let mut mapping = DocumentMapping::default();
    for pf in bundle {
        collect_schema(pf, &pf.items, &mut mapping.schema);
    }
    for pf in bundle {
        collect_mapping_facts(pf, &pf.items, &mut mapping)?;
    }
    // §5.1 — a mapping that loads wrong silently produces documents that lose
    // data, so it is checked once, here, against the schema it was read beside.
    mapping.check()?;
    Ok(mapping)
}

/// Every entity declaration in one file, plus every enum and its variants.
///
/// A nested entity is collected too — an enum's variants ARE entities, and
/// `ToolPasses(tool:, params:)` is one — because a `ScalarForm` names a
/// constructor and the reader has to know its fields.
fn collect_schema(
    pf: &ParsedFile,
    items: &[anthill_core::parse::ir::Item],
    out: &mut document::DomainSchema,
) {
    use anthill_core::parse::ir::Item;
    for item in items {
        match item {
            Item::Namespace(ns) => collect_schema(pf, &ns.items, out),
            Item::Entity(e) => {
                let name = pf.symbols.local_name(*e.name.segments.last().unwrap());
                out.functors.push(document::FunctorSchema {
                    name: name.to_string(),
                    fields: e
                        .fields
                        .iter()
                        .map(|f| document::FieldSchema {
                            name: pf.symbols.local_name(f.name).to_string(),
                            ty: schema_type(pf, &f.ty),
                        })
                        .collect(),
                });
            }
            Item::SortWithBody(s) => {
                let name = pf.symbols.local_name(*s.name.segments.last().unwrap());
                let variants: Vec<(String, bool)> = s
                    .items
                    .iter()
                    .filter_map(|i| match i {
                        Item::Entity(e) => Some((
                            pf.symbols
                                .local_name(*e.name.segments.last().unwrap())
                                .to_string(),
                            !e.fields.is_empty(),
                        )),
                        _ => None,
                    })
                    .collect();
                if !variants.is_empty() {
                    out.enums.push((name.to_string(), variants));
                }
                collect_schema(pf, &s.items, out);
            }
            _ => {}
        }
    }
}

/// A declared type, as the document format reads it.
///
/// Everything it cannot spell as data is `Opaque`, which is not a refusal: an
/// opaque value takes the backticked term spelling, which is total. So an
/// unfamiliar type costs a pair of backticks, never a lost field.
fn schema_type(pf: &ParsedFile, ty: &anthill_core::parse::ir::TypeExpr) -> document::FieldType {
    use anthill_core::parse::ir::TypeExpr;
    let local = |n: &anthill_core::parse::ir::Name| {
        pf.symbols.local_name(*n.segments.last().unwrap()).to_string()
    };
    match ty {
        TypeExpr::Simple(name) => match local(name).as_str() {
            "String" => document::FieldType::Text,
            "Int64" | "Int" => document::FieldType::Int,
            "Bool" => document::FieldType::Bool,
            other => document::FieldType::Named(other.to_string()),
        },
        TypeExpr::Parameterized { name, bindings } => {
            let inner = || {
                bindings
                    .first()
                    .map(|b| schema_type(pf, &b.bound))
                    .unwrap_or(document::FieldType::Opaque)
            };
            match local(name).as_str() {
                "Option" => document::FieldType::Option(Box::new(inner())),
                "List" => document::FieldType::List(Box::new(inner())),
                _ => document::FieldType::Opaque,
            }
        }
        _ => document::FieldType::Opaque,
    }
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
                let field = |name: &str, what: &str| -> Result<String, String> {
                    ir_string(pf, named_args, name)
                        .ok_or_else(|| format!("`fact {what}` carries no `{name}`"))
                };
                let functor_of = |name: &str, what: &str| -> Result<String, String> {
                    ir_name(pf, named_args, name)
                        .ok_or_else(|| format!("`fact {what}` carries no `{name}`"))
                };
                match pf.symbols.local_name(*functor) {
                    "DocumentFormat" => {
                        out.level = ir_int(pf, named_args, "level")
                            .ok_or("`fact DocumentFormat` carries no integer `level`")?
                            as usize;
                        out.attributes = field("attributes", "DocumentFormat")?;
                    }
                    "FieldGroup" => out.field_groups.push(document::FieldGroupSpec {
                        functor: functor_of("functor", "FieldGroup")?,
                        fields: ir_string_list(pf, named_args, "fields"),
                    }),
                    "ScalarForm" => out.scalar_forms.push(document::ScalarFormSpec {
                        sort: functor_of("sort", "ScalarForm")?,
                        constructor: functor_of("constructor", "ScalarForm")?,
                        slot: field("slot", "ScalarForm")?,
                    }),
                    "FlatRecord" => out.flat_records.push(document::FlatRecordSpec {
                        functor: functor_of("functor", "FlatRecord")?,
                        field: field("field", "FlatRecord")?,
                        prefix: field("prefix", "FlatRecord")?,
                    }),
                    "Chapter" => out.chapters.push(ChapterSpec {
                        functor: functor_of("functor", "Chapter")?,
                        field: field("field", "Chapter")?,
                        named: field("named", "Chapter")?,
                    }),
                    "ChapterGroup" => out.groups.push(ChapterGroupSpec {
                        functor: functor_of("functor", "ChapterGroup")?,
                        container: field("container", "ChapterGroup")?,
                        kind: field("kind", "ChapterGroup")?,
                        key: field("key", "ChapterGroup")?,
                        heading: ir_string_list(pf, named_args, "heading"),
                        field: field("field", "ChapterGroup")?,
                    }),
                    "SatelliteList" => out.lists.push(document::SatelliteListSpec {
                        functor: functor_of("functor", "SatelliteList")?,
                        named: field("named", "SatelliteList")?,
                        fields: ir_string_list(pf, named_args, "fields"),
                        key: field("key", "SatelliteList")?,
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

/// `heading: ["at", "author"]` — a bracket literal, which parses to a flat
/// `ListLiteral` application (WI-1099). An absent field is an empty list rather
/// than an error; the mapping's own check decides whether that is legal.
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

/// Turn one item document into the parse IR a plain `fact` file would have
/// produced.
///
/// TWO STEPS, and the split is what keeps the prose exact. The attributes
/// chapter is rendered to anthill SOURCE and parsed, so the loader, the typer
/// and every reader downstream see ordinary facts and none of them learns that
/// the text arrived from a markdown file. The PROSE is then spliced in as the
/// string literal it already is, rather than escaped into that source and
/// unescaped by the parser — a round trip through two escaping layers is exactly
/// what this encoding exists to remove.
fn parse_document(
    source: &str,
    doc: &Document,
    mapping: &DocumentMapping,
) -> Result<(ParsedFile, Vec<document::DocumentFault>), String> {
    let facts = document::document_facts(doc, mapping, STAGE0_ID_FIELD)
        .map_err(|e| e.to_string())?;
    let mut parsed = parse::parse(&facts.source).map_err(|errs| {
        // The source was generated here, so a parse error is this reader's bug
        // or a value the spelling let through — either way it names the text it
        // produced, because nothing in the file looks like it.
        format!(
            "the attributes chapter denotes `{}`, which does not parse: {}",
            facts.source.trim(),
            errs.iter()
                .map(|e| format!("{e:?}"))
                .collect::<Vec<_>>()
                .join("; ")
        )
    })?;
    inject_prose(&mut parsed, source, doc, &facts);
    Ok((parsed, facts.faults))
}

/// Splice each chapter's prose into the field it fills.
///
/// A field inside a FLATTENED record is reached through its path, so the
/// injection rebuilds the record's constructor call rather than adding a named
/// argument to the fact. That is the one place flattening reaches outside
/// `document.rs`, and it is here rather than there because only this side holds
/// the parse IR.
fn inject_prose(
    parsed: &mut ParsedFile,
    source: &str,
    doc: &Document,
    facts: &document::DocumentFacts,
) {
    use anthill_core::parse::ir::Item;
    // The facts in emission order, which is the order they were written and so
    // the order they parse in.
    let mut targets: Vec<(TermId, anthill_core::span::Span)> = Vec::new();
    fn scan(items: &[Item], out: &mut Vec<(TermId, anthill_core::span::Span)>) {
        for item in items {
            match item {
                Item::Namespace(ns) => scan(&ns.items, out),
                Item::Fact(f) => out.push((f.term, f.span)),
                _ => {}
            }
        }
    }
    scan(&parsed.items, &mut targets);

    let mut rebuilt: std::collections::HashMap<usize, TermId> =
        std::collections::HashMap::new();
    for binding in &facts.prose {
        let Some((term, span)) = targets.get(binding.fact).copied() else {
            continue;
        };
        let Some(seg) = doc.segments.get(binding.segment) else {
            continue;
        };
        let text = source[seg.body.clone()].to_string();
        let term = rebuilt.get(&binding.fact).copied().unwrap_or(term);
        let literal = parsed
            .terms
            .alloc(Term::Const(Literal::String(text)), span);
        let new = match binding.path.as_slice() {
            [field] => with_named_arg(parsed, term, field, literal, span),
            [outer, inner] => {
                let record = binding.record.clone().unwrap_or_default();
                let held = named_arg_of(parsed, term, outer).unwrap_or_else(|| {
                    parsed.terms.alloc(
                        Term::Fn {
                            functor: parsed.symbols.intern(&record),
                            pos_args: SmallVec::new(),
                            named_args: SmallVec::new(),
                        },
                        span,
                    )
                });
                let filled = with_named_arg(parsed, held, inner, literal, span);
                with_named_arg(parsed, term, outer, filled, span)
            }
            _ => continue,
        };
        rebuilt.insert(binding.fact, new);
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

/// One application with `field` set — replacing it if it is already there, so
/// that filling a record twice does not write the argument twice.
///
/// THE SPAN THE NEW TERM CARRIES IS THE FACT'S rather than a synthetic one: the
/// text does not exist inside the parsed source, so there is no sub-range to
/// point at, and pointing at the whole fact is the closest true answer.
fn with_named_arg(
    parsed: &mut ParsedFile,
    term: TermId,
    field: &str,
    value: TermId,
    span: anthill_core::span::Span,
) -> TermId {
    let Term::Fn {
        functor,
        pos_args,
        named_args,
    } = parsed.terms.get(term).clone()
    else {
        return term;
    };
    let sym = parsed.symbols.intern(field);
    let mut named: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> = named_args;
    match named.iter_mut().find(|(s, _)| *s == sym) {
        Some(slot) => slot.1 = value,
        None => named.push((sym, value)),
    }
    parsed.terms.alloc(
        Term::Fn {
            functor,
            pos_args,
            named_args: named,
        },
        span,
    )
}

fn named_arg_of(parsed: &ParsedFile, term: TermId, field: &str) -> Option<TermId> {
    let Term::Fn { named_args, .. } = parsed.terms.get(term) else {
        return None;
    };
    named_args
        .iter()
        .find(|(s, _)| parsed.symbols.local_name(*s) == field)
        .map(|(_, t)| *t)
}

/// True if a parsed file declares a bundle-owned namespace (`anthill.todo` or a
/// child). The `--anthill` bundle embeds its own logic (`main.anthill` /
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

// The data-format version `init` stamps a new project with (`fact StoreFormat(version:
// N)`), written to `store_format.anthill` — the root file `ItemPerFileStore` files a
// store-level row in. MUST match the bundle's `current_store_format` (main.anthill),
// which the anthill-side version check compares stamps against; `fresh_init_project_loads_clean`
// (cmd_version_stamp_test) guards against divergence — a fresh project reads as stale the
// moment the two integers part.
const CURRENT_STORE_FORMAT_VERSION: u32 = 1;

// WI-505: `init` no longer scaffolds a per-project domain.anthill/rules.anthill.
// The `anthill.stage0` domain and workflow rules ship bundled in the binary
// (anthill_bundle.rs), version-locked with the logic that imports them, so a
// fresh project carries no copy that could later drift out of sync with the
// grammar or domain. The data-format stamp is bundle-owned wherever there is a KB to
// flush through the store (WorkItemStore.stamp_format / `migrate`); `init` is the one
// place that text-writes it, because it runs before any project exists to load.

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
    self, ChapterGroupSpec, ChapterSpec, Document, DocumentMapping,
};
use anthill_core::persistence::item_per_file_store::{
    identity_prefix, ItemFields, ItemPerFileStore, LayoutFault, ITEM_DOCUMENT_SUFFIX,
    ITEM_PLAIN_SUFFIX,
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
    /// The document structure, for an item document. `None` for a plain
    /// `.anthill` file, whose whole text is anthill source.
    document: Option<Document>,
}

/// The first ITEM file among the project's loaded files — the signal that this directory
/// is on the item-per-file layout, whatever it declares.
///
/// A DOCUMENT IS CONCLUSIVE ANYWHERE; a plain `WI-NNN.anthill` counts only BELOW the
/// root. The root is where every non-item file lives — `workitems.anthill`,
/// `project.anthill`, `store_format.anthill`, `orphaned.anthill` — and all of them carry
/// the plain suffix, so a root-level test would read a zero-config tracker as an item
/// tree and refuse the very shape the default exists to serve. An item lives in a
/// directory named for its status, so "below the root" is exactly the question.
fn first_item_file<'a>(project_items: &'a [ProjectFile], store_root: &Path) -> Option<&'a Path> {
    project_items.iter().map(|f| f.path.as_path()).find(|path| {
        if fs_util::has_suffix(path, &[ITEM_DOCUMENT_SUFFIX]) {
            return true;
        }
        path.parent().is_some_and(|parent| parent != store_root)
            && fs_util::has_suffix(path, &PROJECT_FILE_SUFFIXES)
    })
}

impl ProjectFile {
    /// The byte ranges of this file's facts, in the file's own coordinates.
    ///
    /// A DOCUMENT HAS NONE, and returns an empty list rather than a wrong one.
    /// Its facts were not cut out of the file at all — the attributes chapter was
    /// rendered to anthill source and parsed, so the parser's spans address text
    /// that exists nowhere on disk. The store does not want them either: it
    /// re-renders a document's attributes from the facts, so there is no byte
    /// range for it to preserve.
    fn fact_spans_in_file(&self) -> Vec<anthill_core::span::Span> {
        if self.document.is_some() {
            return Vec::new();
        }
        self.parsed.fact_spans()
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

    /// The layout half of `--fix` (WI-K63ZV): a `FieldGroup` written apart, or a
    /// heading value encoded when it need not be. Both are RENDERINGS of data the
    /// file already holds correctly, so the repair is a re-render. A shared-file
    /// store has no attributes chapter, so it has none of these to fix.
    fn repair_layout(&mut self) -> Result<Vec<PathBuf>, String> {
        match self {
            BuiltStore::Indexed(_) => Ok(Vec::new()),
            BuiltStore::ItemPerFile(s) => s.repair_layout().map_err(|e| e.to_string()),
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
/// binding to a store: `default_binding` builds a declaration of exactly the kind a
/// project can write by hand, and everything downstream cannot tell the two apart.
///
/// IT IS NOT WHAT `init` SCAFFOLDS. A new project is item-per-file; the default describes
/// the single shared file, because what it must keep matching is the trackers already
/// written that way — see the note in [`run_init`].
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
        0 => {
            // AN ITEM TREE WITH NO BINDING IS A BROKEN PROJECT, NOT A ZERO-CONFIG ONE
            // (found in review). `init` scaffolds the item-per-file binding while
            // `default_binding` describes the single shared file, so the two no longer
            // agree — and a project whose `ExtentBinding` is lost (a hand edit, a merge
            // that drops it) would otherwise default to the single file and write a
            // SECOND store beside the item tree it already has. MEASURED before this
            // guard: `add` exited 0 and created `workitems.anthill` next to
            // `open/WI-….anthill.md`, leaving the tracker split across two layouts with
            // nothing said. That is the silent skip the asymmetry would have bought.
            //
            // The zero-config shape this defaults FOR is a directory of plain
            // `workitems.anthill`, which holds no item files and so never trips this.
            if let Some(item) = first_item_file(project_items, store_root) {
                return Err(format!(
                    "{} is an item file, so this project is on the item-per-file layout, \
                     but it declares no `anthill.persistence.ExtentBinding`. Restore the \
                     binding in project.anthill — `ItemPerFileStore`, as `anthill-todo \
                     init` scaffolds it. Defaulting would write a second store into \
                     workitems.anthill beside the items already here.",
                    item.display()
                ));
            }
            default_binding(interp)?
        }
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
                let seeded = match &file.document {
                    // A DOCUMENT HAS NO SPANS: its facts were rendered from the
                    // attributes chapter rather than cut out of the file, so the
                    // store is handed the rows in the order they were emitted and
                    // re-derives everything else.
                    Some(doc) => store.record_document(
                        interp.kb(),
                        file.path.clone(),
                        &file.source,
                        &result.fact_rule_ids,
                        doc,
                    ),
                    None => {
                        let rows: Vec<_> = result
                            .fact_rule_ids
                            .iter()
                            .copied()
                            .zip(file.fact_spans_in_file())
                            .collect();
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
    let mirrored = project_is_mirrored(interp);
    let required: Vec<&str> = STORED_FUNCTORS
        .iter()
        .filter(|(_, r)| match r {
            Retracted::Yes => true,
            Retracted::No => false,
            Retracted::WhenMirrored => mirrored,
        })
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
        names.iter().copied().map(short_name).collect::<Vec<_>>().join(", ")
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

/// `anthill-todo fsck [--fix] [--renumber [<id>]]` — check the on-disk layout
/// against the facts, and optionally repair it.
///
/// TWO REPAIRS, TWO VERBS, because they differ in what they change and therefore
/// in what can be looking at it. `--fix` moves a file to the path its own fact
/// names: the directory is an index and the fact is the truth (design §4), so the
/// direction is settled and nothing outside that file cared where it sat.
/// `--renumber` changes an IDENTITY (§6.6) — every `depends_on` in the tree and
/// every commit message outside it may be naming the id it retires.
///
/// What NEITHER will do is choose between two files claiming ONE id: that is a
/// real disagreement about which file is the item, and only whoever interrupted
/// the move knows. Two files whose ids merely COLLIDE are the opposite case —
/// two real items — and that one `--renumber` can decide alone, because §6.6's
/// order is computed from the rows rather than negotiated.
fn run_fsck(
    interp: &mut Interpreter,
    store: &mut BuiltStore,
    store_root: &Path,
    args: &[String],
) -> i32 {
    let mut fix = false;
    let mut renumber = false;
    let mut forced_loser: Option<String> = None;
    let mut rest = args.iter().peekable();
    while let Some(arg) = rest.next() {
        match arg.as_str() {
            "--fix" => fix = true,
            "--renumber" => {
                renumber = true;
                // THE ID IS OPTIONAL: bare, this repairs every collision by
                // §6.6's order; with an id, that id is the side that loses. It is
                // read positionally because the bare form is the common one and
                // `--renumber=<id>` would read as the only form there is.
                if rest.peek().is_some_and(|next| !next.starts_with('-')) {
                    forced_loser = rest.next().cloned();
                }
            }
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

    // `--fix` FIRST, and the order is load-bearing when both are asked for: a
    // re-mint reads the item's `created`, and filling a missing one is `--fix`'s
    // job. The stamps it wrote are handed across because they are not in the KB —
    // that repair goes through the store, and `fsck` never reloads.
    let mut filled_created = std::collections::HashMap::new();
    if fix {
        match repair_created(interp, store) {
            Ok(filled) => {
                for (rule, id, stamp) in filled {
                    println!("dated {id} from its file: {stamp}");
                    filled_created.insert(rule, stamp);
                }
            }
            Err(e) => {
                eprintln!("error: {e}");
                return runner::EXIT_RUNTIME;
            }
        }
        match store.repair_layout() {
            Ok(files) => {
                for path in &files {
                    println!("re-rendered {}", path.display());
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
    }

    if renumber {
        match repair_ids(
            interp,
            store,
            store_root,
            forced_loser.as_deref(),
            &filled_created,
        ) {
            Ok(report) => report.print(),
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
    if blocking > 0 {
        // NAMED PER FAULT, not as one line about `--fix`. A collision is repaired
        // by the OTHER verb, and telling its reader to run `--fix` sends them to a
        // command that leaves the tree exactly as it found it and then reports the
        // same error — the circle WI-1123's covers check was written not to draw.
        //
        // AND ONLY THE VERBS THIS RUN DID NOT TRY. Suggesting the command that has
        // just run and left the fault standing is the same circle, one turn later.
        let untried: Vec<&str> = remedies_for(&faults)
            .into_iter()
            .filter(|v| !(fix && *v == FSCK_FIX) && !(renumber && *v == FSCK_RENUMBER))
            .collect();
        if !untried.is_empty() {
            eprintln!(
                "run {} to repair what can be repaired mechanically",
                untried.join(" and then ")
            );
        }
    }
    if blocking > 0 {
        runner::EXIT_RUNTIME
    } else {
        0
    }
}

const FSCK_USAGE: &str = "\
usage: anthill-todo fsck [--fix] [--renumber [<id>]]

Check the on-disk layout against the facts: that each item's file sits at the path
its own `id` and `status` name, that no id is held twice, that no two items were
minted into one identity, and that every feedback or tag row is in its item's file.

  --fix   move each misplaced file to the path its own fact names (the fact wins),
          and date an item whose `created` was left out from its file. It will not
          choose between two files claiming one id, split a file holding several
          items, or guess where an unreadable row belongs.

  --renumber [<id>]
          re-mint one side of every collision between two items whose ids share a
          `<time>-<hash>` identity. Which side loses is decided from the rows —
          later `created`, then author, then description — so two checkouts
          repairing the same collision without talking produce the same tree.
          Give an <id> to force THAT one to be the side that is renumbered.
          It rewrites the id, the item's satellite rows and every `depends_on`
          entry in the tree; mentions in PROSE are reported and left alone.";

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
    legacy_documents: &[(PathBuf, String)],
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
            legacy_documents,
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
) -> Result<Vec<(anthill_core::kb::RuleId, String, String)>, String> {
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
        filled.push((rule, id, stamp));
    }
    if !filled.is_empty() {
        inner
            .flush(interp.kb())
            .map_err(|e| format!("writing the dated rows: {e}"))?;
    }
    Ok(filled)
}


// ── fsck --renumber: the repair half of §6.6 (WI-VDXAM) ────────

/// One item as the renumber reads it: the four values the deterministic order
/// and the re-mint are computed from, and nothing else.
///
/// READ ONCE, BEFORE ANYTHING IS WRITTEN. Every decision below is taken over
/// these values; nothing consults the filesystem, the clock, or the order the
/// files happened to be walked in. That is what makes two checkouts resolving
/// the same collision independently produce byte-identical trees — the property
/// §6.6 calls load-bearing, because a repair that two sides disagree about turns
/// one collision into a second and worse divergence.
struct ItemRow {
    rule: anthill_core::kb::RuleId,
    path: PathBuf,
    id: String,
    created: String,
    author: String,
    description: String,
}

impl ItemRow {
    /// The total order §6.6 states: LATER `created` LOSES, ties broken on
    /// author, then on the full description.
    ///
    /// THE ID IS THE LAST TIE-BREAK, and it is what makes the order TOTAL rather
    /// than merely usually-total. The three fields above cannot all agree between
    /// two items in a collision — equal `created` and equal description with an
    /// equal author would digest identically, which is one item under a different
    /// name (`DuplicateId`, whose remedy is the opposite one) — but that argument
    /// rests on both ids having been MINTED, and a hand-written id shaped like a
    /// minted one is exactly what a tracker of two id shapes can hold. The ids
    /// differ by construction here, so appending one closes the case.
    fn order_key(&self) -> (&str, &str, &str, &str) {
        (&self.created, &self.author, &self.description, &self.id)
    }
}

/// What a renumber did, so `fsck` can say it.
#[derive(Default)]
struct Renumbering {
    /// Per repaired item: the id it lost, the id it gained, and the two paths its
    /// file moved between. The DESTINATION is read back out of the store after the
    /// flush rather than computed here — the path is the store's rule (an id and a
    /// status directory), and a second copy of that rule in the reporting code
    /// would be free to disagree with the bytes on disk.
    minted: Vec<(String, String, PathBuf, PathBuf)>,
    satellites: usize,
    dependents: usize,
    /// Places the old id still appears, after every field this rewrites has been
    /// rewritten — prose, and anything else the repair deliberately leaves alone.
    mentions: Vec<(PathBuf, usize, String)>,
}

impl Renumbering {
    /// Say what was done, and — just as loudly — what was deliberately not.
    ///
    /// A REPAIR THAT PRINTS NOTHING IS INDISTINGUISHABLE FROM ONE THAT DID NOT
    /// RUN, which is the same argument `fsck`'s `layout ok` line already makes.
    fn print(&self) {
        if self.minted.is_empty() {
            println!("no id collisions");
            return;
        }
        for (old, new, from, to) in &self.minted {
            println!("renumbered {old} -> {new}");
            println!("  moved {} -> {}", from.display(), to.display());
        }
        println!(
            "re-pointed {} satellite row(s) and rewrote `depends_on` in {} item(s)",
            self.satellites, self.dependents
        );
        if self.mentions.is_empty() {
            return;
        }
        // NOT AN ERROR AND NOT A WARNING. Every one of these may correctly name
        // the item that KEPT the id — the two were minted into one day partition
        // and a reader wrote about one of them — so the honest report is the
        // locations and the reason, not a verdict this cannot reach.
        println!(
            "{} prose mention(s) of a renumbered id remain, and were NOT rewritten — a \
             `WI-…` in feedback text may legitimately mean the item that kept the id:",
            self.mentions.len()
        );
        for (path, line, text) in &self.mentions {
            let text: String = text.chars().take(100).collect();
            println!("  {}:{line}: {text}", path.display());
        }
        println!("note: references outside this tree — commit messages, branch names — are not \
                  visible here and were not checked");
    }
}

/// The commands that repair what these faults are, spelled the way they must be
/// typed, in the order they have to run.
///
/// PER FAULT, BECAUSE THE VERBS ARE NOT INTERCHANGEABLE (WI-VDXAM). `--fix` moves
/// a file, `--renumber` changes an identity, and `migrate` converts an encoding;
/// naming one of them at a tree that needs another sends the reader to a command
/// that reports the same error again, having done nothing. Faults with no
/// mechanical repair — a duplicate id, an unroutable row — contribute nothing, and
/// an EMPTY answer is the honest one there: only whoever left the tree in that
/// state can say what it should be.
///
/// `--fix` FIRST when both are named, which is the order `fsck` itself runs them
/// in and for the same reason: a re-mint reads a `created` that `--fix` fills.
fn remedies_for(faults: &[LayoutFault]) -> Vec<&'static str> {
    let mut verbs: Vec<&'static str> = Vec::new();
    for fault in faults.iter().filter(|f| f.blocking()) {
        let verb = match fault {
            LayoutFault::PathDisagreement { .. } => FSCK_FIX,
            LayoutFault::IdCollision { .. } => FSCK_RENUMBER,
            LayoutFault::PlainItemFile { .. } => "`anthill-todo migrate --to document`",
            LayoutFault::SharedFile { .. } => "`anthill-todo migrate --to item-per-file`",
            // A BLOCKING `DocumentFault` NAMES NO VERB, and `--fix` in particular is
            // the wrong one: `repair_layout` SKIPS a blocking document fault by
            // design, because re-rendering a file the reader had to drop a field
            // from would make the loss permanent. Sending its reader to `--fix`
            // produced `no misplaced files` and then the identical error.
            LayoutFault::DocumentFault { .. } => continue,
            LayoutFault::DuplicateId { .. } | LayoutFault::UnroutableRow { .. } => continue,
            LayoutFault::OrphanRow { .. } | LayoutFault::MisfiledRow { .. } => continue,
        };
        if !verbs.contains(&verb) {
            verbs.push(verb);
        }
    }
    verbs.sort_by_key(|v| *v != FSCK_FIX);
    verbs
}

const FSCK_FIX: &str = "`anthill-todo fsck --fix`";
const FSCK_RENUMBER: &str = "`anthill-todo fsck --renumber`";

/// `anthill-todo fsck --renumber [<id>]` — resolve every `<time>-<hash>` identity
/// collision by re-minting one side (design §6.6).
///
/// SEPARATE FROM `--fix`, AND NOT AS A MATTER OF TASTE. `--fix` moves a file to
/// the path its own fact names: the fact is authoritative, the direction is
/// settled, and nothing outside that file can be looking at the old path. This
/// changes an IDENTITY, which every `depends_on` in the tree and every commit
/// message outside it may be naming. Different blast radius, different verb.
///
/// WHAT IT REWRITES: the loser's `id:` field (which carries its filename with it,
/// since the path is a function of the row), its satellites' `workitem:` fields,
/// and every `depends_on` entry in the tree. WHAT IT REFUSES TO REWRITE: prose. A
/// `WI-…` in a feedback entry may legitimately mean the winner — the two items
/// are neighbours in one day's partition and a reader wrote about one of them —
/// so those are REPORTED with locations and left exactly as they are.
///
/// `forced_loser` overrides which side loses, for when one id has already escaped
/// into commit messages and branch names. It names the id that must be renumbered.
fn repair_ids(
    interp: &mut Interpreter,
    store: &mut BuiltStore,
    store_root: &Path,
    forced_loser: Option<&str>,
    filled_created: &std::collections::HashMap<anthill_core::kb::RuleId, String>,
) -> Result<Renumbering, String> {
    let BuiltStore::ItemPerFile(inner) = store else {
        return Err(format!(
            "this project's store is `{INDEXED_FILE_STORE}`, which holds every row in one \
             file — `--renumber` repairs a collision between two item FILES, and there are \
             none to repair"
        ));
    };

    // THE COLLISION MUST BE THE ONLY THING WRONG, checked before a byte moves.
    //
    // ONE RULE RATHER THAN A LIST, because every other blocking fault breaks this
    // repair in its own way and the shared reason is enough: a renumber rewrites
    // whole FILES through the store, so it needs the store's picture of the tree to
    // be right everywhere it writes. A duplicate id is the sharp case — two rows
    // carrying one id would be re-minted to two different ids under one key, and
    // whichever landed second would take the other's file. But a misplaced file
    // would be silently moved as a side effect and its fault left standing in the
    // report; an unplaceable row has no destination at all; a plain file would be
    // renamed to a document's name; and a file the document reader had to drop a
    // field from would be re-rendered without it.
    //
    // IT IS NOT A DEADLOCK, and that is what the check costs. `fsck --fix` repairs
    // every one of these that is mechanically repairable, and it runs on a colliding
    // tree — the collision blocks nothing there, because two colliding ids name two
    // different destinations (see `repair_paths`). So `fsck --fix` then
    // `fsck --renumber`, which is the order the combined form already runs in.
    if let Some(blocker) = inner
        .layout_faults()
        .into_iter()
        .find(|f| f.blocking() && !matches!(f, LayoutFault::IdCollision { .. }))
    {
        return Err(format!(
            "{blocker}. Resolve that first — `anthill-todo fsck --fix` repairs what is \
             mechanical: renumbering rewrites whole files, and it needs every other \
             disagreement between this tree and its facts already settled"
        ));
    }

    // Every primary row, read once. `primary_rows` comes back sorted by path,
    // and that order is used for nothing but iteration.
    let mut rows: Vec<ItemRow> = Vec::new();
    for (rule, path) in inner.primary_rows() {
        let head = interp.kb().rule_head(rule);
        let Some(id) = named_string(interp.kb(), head, STAGE0_ID_FIELD) else {
            continue;
        };
        rows.push(ItemRow {
            rule,
            path,
            // A stamp `--fix` has just written in this same run is not in the KB
            // — that repair goes through the store, and `fsck` never reloads —
            // so the two sources are merged here rather than in the KB. Without
            // it `fsck --fix --renumber` would refuse over a field its own first
            // half had already filled.
            created: filled_created
                .get(&rule)
                .cloned()
                .or_else(|| named_string(interp.kb(), head, "created"))
                .unwrap_or_default(),
            author: prose_string(interp.kb(), head, STAGE0_AGENT_FIELD).unwrap_or_default(),
            description: prose_string(interp.kb(), head, "description").unwrap_or_default(),
            id,
        });
    }

    // The groups: every identity prefix two or more rows share. Folded before it
    // is compared, because minting checks occupancy that way (§6.5) and a repair
    // that disagreed with the mint would renumber into a prefix the mint calls
    // taken.
    let mut groups: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for (i, row) in rows.iter().enumerate() {
        if let Some(prefix) = identity_prefix(&row.id) {
            groups.entry(prefix.to_lowercase()).or_default().push(i);
        }
    }
    groups.retain(|_, g| g.len() > 1);

    // AN UNDATED ITEM CANNOT BE ORDERED, SO IT IS REFUSED RATHER THAN PLACED.
    // `created` is a required field the loader fills with a fresh var when it is
    // omitted, so an item that never got one reads back as no string at all — and
    // the empty string sorts BEFORE every real timestamp, which would silently make
    // the undated item the WINNER of a rule that says the earlier one wins. It is
    // also the input a re-mint needs. Both halves want the same answer, and the
    // answer is that this item is not datable from here.
    for group in groups.values() {
        for &i in group {
            if rows[i].created.is_empty() {
                return Err(format!(
                    "{}: `{}` is one side of an id collision and carries no `created`, so \
                     neither side can be ordered against it — later `created` is what \
                     decides which one is renumbered. Run `anthill-todo fsck --fix` first: \
                     it dates an undated item from its own file",
                    rows[i].path.display(),
                    rows[i].id
                ));
            }
        }
    }

    if let Some(forced) = forced_loser {
        let in_a_group = groups
            .values()
            .flatten()
            .any(|&i| rows[i].id.eq_ignore_ascii_case(forced));
        if !in_a_group {
            return Err(format!(
                "`{forced}` is not one side of an id collision, so there is nothing to \
                 renumber it away from. `--renumber` without an id repairs every collision \
                 there is; run `anthill-todo fsck` to see them"
            ));
        }
    }

    // Which prefixes are spoken for. Seeded with EVERY id in the tree, including
    // both sides of every collision: the loser is moving away from the shared
    // prefix, and the winner is staying on it.
    let mut taken: BTreeSet<String> = rows
        .iter()
        .filter_map(|row| identity_prefix(&row.id))
        .map(|p| p.to_lowercase())
        .collect();

    // Decide, for every group, before rewriting anything.
    let mut renames: BTreeMap<String, String> = BTreeMap::new();
    let mut report = Renumbering::default();
    for group in groups.values() {
        let mut ordered = group.clone();
        ordered.sort_by(|&a, &b| rows[a].order_key().cmp(&rows[b].order_key()));
        // The winner is the first under the order — unless it is the id the
        // caller named, in which case the next one keeps the prefix and every
        // other side of the group is renumbered exactly as it would have been.
        let winner = match forced_loser {
            Some(forced) if rows[ordered[0]].id.eq_ignore_ascii_case(forced) => ordered[1],
            _ => ordered[0],
        };
        for &i in &ordered {
            if i == winner {
                continue;
            }
            let new_id = remint(interp, &rows[i], &mut taken)?;
            report.minted.push((
                rows[i].id.clone(),
                new_id.clone(),
                rows[i].path.clone(),
                PathBuf::new(),
            ));
            renames.insert(rows[i].id.clone(), new_id);
        }
    }
    if renames.is_empty() {
        return Ok(report);
    }

    // ── The rewrite ─────────────────────────────────────────────
    //
    // ONE `update` PER ROW, and that is a requirement rather than tidiness: the
    // store pairs a write with the retract it replaces, and a row retracted twice
    // in one flush has two writes claiming it. So every change a row needs — its
    // own id, and every `depends_on` entry naming a renumbered item — is applied
    // to one term and written once.
    for row in &rows {
        let head = interp.kb().rule_head(row.rule);
        let mut new = head;
        if let Some(minted) = renames.get(&row.id) {
            let one = std::iter::once((row.id.clone(), minted.clone())).collect();
            new = rewrite_field_strings(interp.kb_mut(), new, STAGE0_ID_FIELD, &one).ok_or_else(
                || {
                    format!(
                        "{}: `{}` carries no `{STAGE0_ID_FIELD}` field to renumber",
                        row.path.display(),
                        row.id
                    )
                },
            )?;
        }
        if let Some(rewritten) = rewrite_field_strings(interp.kb_mut(), new, "depends_on", &renames)
        {
            new = rewritten;
            report.dependents += 1;
        }
        if new == head {
            continue;
        }
        write_through(interp, inner, row.rule, new, &row.path)?;
    }

    // The satellites, by ROUTE rather than by file: a feedback row that is
    // misfiled or orphaned still names the item, and leaving it pointing at an id
    // no row carries would turn a repaired collision into an orphan.
    for (old, new) in &renames {
        let one: BTreeMap<String, String> =
            std::iter::once((old.clone(), new.clone())).collect();
        for (rule, path) in inner.satellite_rows_of(old) {
            let head = interp.kb().rule_head(rule);
            let Some(rewritten) =
                rewrite_field_strings(interp.kb_mut(), head, STAGE0_REF_FIELD, &one)
            else {
                return Err(format!(
                    "{}: a row routed as a satellite of `{old}` carries no \
                     `{STAGE0_REF_FIELD}` field to re-point",
                    path.display()
                ));
            };
            write_through(interp, inner, rule, rewritten, &path)?;
            report.satellites += 1;
        }
    }

    inner
        .flush(interp.kb())
        .map_err(|e| format!("writing the renumbered items: {e}"))?;

    for (_, new_id, _, landed) in &mut report.minted {
        *landed = inner
            .item_location(new_id)
            .ok_or_else(|| {
                format!("`{new_id}` was written and this store holds no file for it")
            })?
            .to_path_buf();
    }
    report.mentions = remaining_mentions(store_root, &renames)?;
    Ok(report)
}

/// Stage the replacement of one row through the store, carrying its clause kind,
/// domain and metadata across unchanged.
fn write_through(
    interp: &mut Interpreter,
    store: &mut ItemPerFileStore,
    rule: anthill_core::kb::RuleId,
    new: TermId,
    path: &Path,
) -> Result<(), String> {
    let (kind, domain, meta) = {
        let kb = interp.kb();
        (
            kb.rule_clause_kind(rule),
            kb.rule_domain(rule),
            kb.rule_meta(rule),
        )
    };
    store
        .update(interp.kb(), rule, new, kind, domain, meta)
        .map_err(|e| format!("{}: {e}", path.display()))?;
    Ok(())
}

/// The most attempts a re-mint will make before refusing. Nowhere near reachable
/// — §6.5 measures a re-hash at roughly zero on this tracker, and each attempt
/// draws from 33.5 million values in one day's partition — so reaching it means
/// the digest is not spreading, which is a defect to report rather than a load to
/// absorb.
const REMINT_ATTEMPTS: i64 = 64;

/// Re-mint one item's id, by §6.5's rule and its attempt counter.
///
/// STARTS AT 1, NEVER 0. Attempt 0 is what produced the id this is replacing, so
/// re-deriving it would answer with the colliding id — and, worse, would look
/// like it had worked.
///
/// THE AUTHOR IS THE ONE THE ROW RECORDS. §6.5 mints from the FILING author, and
/// §6.7 settles that a work item does not record who filed it; what it records is
/// the agent of its last status change, which for an item still `Open` is the one
/// who filed it and after a `claim` is the one who claimed it. That is a weaker
/// input than the mint's, and it does not matter: what a re-mint owes its caller
/// is a free prefix reached by a rule two checkouts compute identically, and a
/// value read out of the row is exactly that. It is used for the tie-break above
/// for the same reason, so there is one reading of "author" here rather than two.
fn remint(
    interp: &mut Interpreter,
    row: &ItemRow,
    taken: &mut BTreeSet<String>,
) -> Result<String, String> {
    let day = day_partition(&row.created).ok_or_else(|| {
        format!(
            "{}: `{}` cannot be re-minted — its `created` is {:?}, and the day it names is \
             the first segment of every minted id. Run `anthill-todo fsck --fix` to date it \
             from its file",
            row.path.display(),
            row.id,
            row.created
        )
    })?;
    for attempt in 1..=REMINT_ATTEMPTS {
        // The digest's input, spelled exactly as `FileBasedWorkitemStore.digest_input`
        // spells it — the two must agree or `add` and this would mint into
        // different spaces.
        let input = format!(
            "{}\n{}\n{}\n{}",
            row.author, row.created, row.description, attempt
        );
        let digest = string_op(interp, "anthill.prelude.String.digestBase32", &input, 5)?;
        let prefix = format!("WI-{day}-{digest}");
        if !taken.insert(prefix.to_lowercase()) {
            continue;
        }
        let slug = string_op(interp, "anthill.prelude.String.slug", &row.description, 30)?;
        return Ok(if slug.is_empty() {
            prefix
        } else {
            format!("{prefix}-{slug}")
        });
    }
    Err(format!(
        "`{}` could not be re-minted: {REMINT_ATTEMPTS} attempts all landed on an identity \
         prefix this tracker already holds",
        row.id
    ))
}

/// One of the two minting primitives, through the interpreter.
///
/// NOT RE-IMPLEMENTED HERE, and that is the point (§6.7). `slug` and
/// `digestBase32` MINT AN IDENTITY from content, so a second implementation that
/// disagreed by one character would hand one item two ids — which is the very
/// collision this command exists to repair, arriving by the one route no
/// coordination could catch. The repair calls what `mint_id` calls.
fn string_op(
    interp: &mut Interpreter,
    op: &str,
    text: &str,
    width: i64,
) -> Result<String, String> {
    match interp.call(op, &[Value::Str(text.to_string()), Value::Int(width)]) {
        Ok(Value::Str(out)) => Ok(out),
        Ok(other) => Err(format!("`{op}` answered {other:?}, which is not a string")),
        Err(e) => Err(format!("`{op}`: {e}")),
    }
}

/// `2026-08-17T10:22:03Z` -> `20260817`, the day partition a minted id opens with.
///
/// THE SAME THREE CUTS `FileBasedWorkitemStore.day_of` MAKES, and cuts rather
/// than a separator strip for the reason stated there: dropping every `-` would
/// swallow one out of a garbled stamp and yield a shorter partition that still
/// looks like one. `None` where that sort names no day, so the caller can refuse
/// instead of minting into a partition it invented.
fn day_partition(created: &str) -> Option<String> {
    let digits = |s: &str| s.chars().all(|c| c.is_ascii_digit());
    if !created.is_ascii() || created.len() < 10 {
        return None;
    }
    let (y, m, d) = (&created[0..4], &created[5..7], &created[8..10]);
    (digits(y) && digits(m) && digits(d)).then(|| format!("{y}{m}{d}"))
}

/// Every place a renumbered id still appears, once every field this repair
/// rewrites has been rewritten (§6.6).
///
/// REPORTED, NEVER REWRITTEN, and the limit is honest rather than lazy. The two
/// sides of a collision were minted in the same day partition, so a feedback
/// entry or a description that names `WI-<day>-<hash>…` may perfectly well mean
/// the side that KEPT the id — and prose is the one place nothing distinguishes
/// the two readings. §6.4 states the same limit for provisional ids; this is that
/// limit on a rare path instead of on every offline `add`.
///
/// It sees the tracker's own files and nothing else. A commit message, a branch
/// name and a conversation are all outside this tree, and saying so is why the
/// report exists at all.
fn remaining_mentions(
    root: &Path,
    renames: &BTreeMap<String, String>,
) -> Result<Vec<(PathBuf, usize, String)>, String> {
    let mut files = Vec::new();
    fs_util::collect_files_by_suffix_recursive(root, &PROJECT_FILE_SUFFIXES, &mut files)?;
    files.sort();
    let mut out = Vec::new();
    for path in files {
        let text = fs::read_to_string(&path)
            .map_err(|e| format!("re-reading {} for stale references: {e}", path.display()))?;
        for (n, line) in text.lines().enumerate() {
            if renames.keys().any(|old| line.contains(old.as_str())) {
                out.push((path.clone(), n + 1, line.trim().to_string()));
            }
        }
    }
    Ok(out)
}

/// Rewrite every `String` literal `renames` names, inside the value of ONE named
/// field of a fact — and nowhere else.
///
/// THE FIELD RESTRICTION IS THE WHOLE SAFETY ARGUMENT. A renumber must reach
/// `depends_on`'s elements, wherever a list encoding happens to put them, and
/// must not reach the description sitting two fields away — which is the same
/// string appearing in two places meaning two different things. Walking the whole
/// term and matching on the literal would rewrite both; walking one field's
/// subterm cannot touch the other, whatever shape either has.
///
/// `None` when nothing under the field changed, so a caller can tell a rewrite
/// from a no-op and write only what moved.
fn rewrite_field_strings(
    kb: &mut KnowledgeBase,
    term: TermId,
    field: &str,
    renames: &BTreeMap<String, String>,
) -> Option<TermId> {
    let Term::Fn {
        functor,
        pos_args,
        named_args,
    } = kb.get_term(term).clone()
    else {
        return None;
    };
    let at = named_args
        .iter()
        .position(|(s, _)| kb.local_name_of(*s) == field)?;
    let replaced = substitute_strings(kb, named_args[at].1, renames)?;
    let mut named = named_args;
    named[at].1 = replaced;
    Some(kb.alloc(Term::Fn {
        functor,
        pos_args,
        named_args: named,
    }))
}

/// The recursive half: every `String` literal under `t` that `renames` names,
/// replaced. `None` when nothing under `t` changed.
///
/// SHAPE-BLIND BY DESIGN. `depends_on` is `Option[T = List[T = String]]`, which
/// reaches a store as an `Option` wrapper around a cons chain, a `ListLiteral`, or
/// a bare list depending on how the row was written and which desugaring ran; a
/// walk that knew any of those spellings would silently miss the others.
fn substitute_strings(
    kb: &mut KnowledgeBase,
    t: TermId,
    renames: &BTreeMap<String, String>,
) -> Option<TermId> {
    match kb.get_term(t).clone() {
        Term::Const(Literal::String(s)) => renames
            .get(&s)
            .map(|to| kb.alloc(Term::Const(Literal::String(to.clone())))),
        Term::Fn {
            functor,
            mut pos_args,
            mut named_args,
        } => {
            let mut changed = false;
            for arg in pos_args.iter_mut() {
                if let Some(new) = substitute_strings(kb, *arg, renames) {
                    *arg = new;
                    changed = true;
                }
            }
            for (_, arg) in named_args.iter_mut() {
                if let Some(new) = substitute_strings(kb, *arg, renames) {
                    *arg = new;
                    changed = true;
                }
            }
            changed.then(|| {
                kb.alloc(Term::Fn {
                    functor,
                    pos_args,
                    named_args,
                })
            })
        }
        _ => None,
    }
}

/// A field written either bare (`"x"`) or wrapped (`some(value: "x")`), reached
/// through a dotted PATH so a flattened record's member is one argument away.
///
/// BOTH SPELLINGS REACH THE STORE and neither is a deviation — the field is
/// declared `Option[T = String]`, the loader accepts a bare literal for it and the
/// printer emits the wrapped form, so one tracker holds both. Comparing the
/// wrapped form against a bare value is how WI-1121's idempotence check silently
/// failed its first time out; the bundle's own `prose_field_of` is this function,
/// and the two have to keep agreeing.
fn prose_string(kb: &KnowledgeBase, term: TermId, path: &str) -> Option<String> {
    let segments: Vec<String> = path.split('.').map(|s| s.to_string()).collect();
    let value = document::value_at(kb, term, &segments)?;
    match kb.get_term(value) {
        Term::Const(Literal::String(s)) => Some(s.clone()),
        Term::Fn { named_args, .. } => named_args
            .iter()
            .find(|(s, _)| kb.local_name_of(*s) == "value")
            .and_then(|(_, inner)| match kb.get_term(*inner) {
                Term::Const(Literal::String(s)) => Some(s.clone()),
                _ => None,
            }),
        _ => None,
    }
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

/// `migrate --to document` — convert every item still in the WI-1120 encoding.
///
/// THE THIRD FULL-TREE PASS, after WI-1118's and WI-1120's, and §11 accepted
/// that arithmetic: a migration is cheap to repeat now that it touches no forge.
/// Every `WI-….anthill.md` holding a fenced `anthill` head becomes one holding
/// an `## Attributes` chapter, at the same path.
///
/// IT IS NOT A PURE REFORMAT, and the claim that a before/after row count is a
/// complete correctness check is FALSE here: the count is identical while every
/// status value changes shape and each rejection reason moves into a chapter.
/// Two data changes ride with it, both decided rather than measured —
///
///   * `status: Claimed(agent: a, since: t)` becomes
///     `last_status_change: StatusChange(status: Claimed, agent: some(a), at: some(t))`.
///     The old payloads were irregular (`since` on two variants, `at` on four,
///     `agent` on two, `Verified` carrying neither), so this is a normalisation
///     as well as a move. NOTHING IS SYNTHESIZED: a variant that recorded no
///     agent yields `none`, because 985 of 1127 items had already lost who
///     claimed them and inventing one is worse than a gap.
///   * `depends_on: some(value: nil)` becomes ABSENT, and reads back as `none`.
///     692 items write the former. `some([])` and `none` are different values,
///     so this is a data change and no round-trip test can see it — both sides
///     read as "no dependencies".
///
/// IT GOES THROUGH THE ORDINARY WRITER. The converted rows are loaded into the
/// live KB and persisted through an `ItemPerFileStore` carrying the same mapping
/// every command uses, so the spec's checks — prose demotion, heading encoding,
/// the blank-line rule — cannot be skipped by a bespoke rendering path.
#[allow(clippy::too_many_arguments)]
fn run_migrate_to_document(
    interp: &mut Interpreter,
    declared: &DeclaredStore,
    store_root: &Path,
    project_items: &[ProjectFile],
    per_file: &[load::LoadResult],
    mapping: &DocumentMapping,
    legacy: &[(PathBuf, String)],
    created_from: Option<&str>,
) -> i32 {
    if !matches!(declared.store, BuiltStore::ItemPerFile(_)) {
        eprintln!(
            "error: `--to document` converts an item-per-file tree, and this project is not on \
             that layout yet. Run `anthill-todo migrate --to item-per-file` first."
        );
        return runner::EXIT_RUNTIME;
    }
    // TWO SOURCES, ONE DESTINATION. A tracker reaches this command from either
    // of the two shapes that are not an attribute document: a per-item PLAIN
    // `.anthill` file (a project that never ran WI-1120's conversion), and a
    // legacy DOCUMENT (one that ran it before this format existed). Both convert
    // the same way from here on — the difference is only in how they were read.
    let plain: Vec<(&Path, Vec<anthill_core::kb::RuleId>)> =
        match plain_item_files(interp, declared, project_items, per_file) {
            Ok(found) => found,
            Err(code) => return code,
        };
    if legacy.is_empty() && plain.is_empty() {
        println!("migrate: every item file is already an attribute document");
        return 0;
    }

    // ── read and convert, all of it, before anything is written
    let mut converted: Vec<ParsedFile> = Vec::with_capacity(legacy.len());
    for (path, source) in legacy {
        match convert_legacy_document(path, source, mapping) {
            Ok(parsed) => converted.push(parsed),
            Err(e) => {
                eprintln!("error: {}: {e}", path.display());
                return runner::EXIT_RUNTIME;
            }
        }
    }

    // ── load them, so the writer is handed facts rather than text
    let refs: Vec<&ParsedFile> = converted.iter().collect();
    let per_file_converted = match load::load_all_per_file(
        interp.kb_mut(),
        &refs,
        &anthill_core::kb::load::NullResolver,
    ) {
        Ok((_merged, per_file)) => per_file,
        Err(errs) => {
            for e in load::LoadError::render_all(&errs) {
                eprintln!("error: {e}");
            }
            eprintln!(
                "error: the converted rows do not load, so nothing was written. The old files \
                 are untouched"
            );
            return runner::EXIT_COMPILE;
        }
    };

    let mut target = ItemPerFileStore::new(
        store_root.to_path_buf(),
        ItemFields::new(STAGE0_STATUS_FIELD, STAGE0_ID_FIELD, STAGE0_REF_FIELD),
    )
    .with_document_mapping(mapping.clone());
    // Every path this writes it has already READ — that is what makes
    // overwriting them safe, and it is the one thing `refuse_unknown_occupant`
    // cannot see for itself, because the reading happened in another store.
    target.adopt(legacy.iter().map(|(p, _)| p.clone()));

    // A PLAIN file's rows need `created` before they can be written: an id is
    // minted from it and `list` orders by it, so an undated item has no place in
    // either. It comes from `--created-from`, or from the file's own creation
    // time, and which source was used is REPORTED — a file time dates every item
    // in a shared file alike, which is a weaker answer than a table.
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
    let plan = plan_created_stamps(interp, &plain, &created);
    if let Err(code) = plan.report() {
        return code;
    }
    let stamped = plan.stamps;

    let mut rows = 0usize;
    let legacy_rules: Vec<(&Path, Vec<anthill_core::kb::RuleId>)> = legacy
        .iter()
        .zip(per_file_converted.iter())
        .map(|((p, _), r)| (p.as_path(), r.fact_rule_ids.clone()))
        .collect();
    for (path, rules) in legacy_rules.iter().chain(plain.iter()) {
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
            "note: a partly converted tree may be on disk. Every file keeps its own name, so \
             re-running this converts whatever is still in the old encoding"
        );
        return runner::EXIT_RUNTIME;
    }
    // The sources go LAST. A crash before this point leaves both encodings —
    // which the next load names as a `DuplicateId`, loud and repairable —
    // rather than a hole.
    //
    // A LEGACY DOCUMENT IS USUALLY REWRITTEN AT ITS OWN PATH, and then there is
    // nothing to remove. USUALLY is not ALWAYS: the directory is the item's
    // status, so a source tree whose directory already disagreed with its status
    // converts to a DIFFERENT path, and leaving the source behind puts the item
    // in two files. Asked of the store rather than assumed, because the store is
    // what decided where the row went.
    let mut sources: Vec<PathBuf> = plain.iter().map(|(p, _)| p.to_path_buf()).collect();
    for ((path, _), parsed) in legacy.iter().zip(converted.iter()) {
        let Some(id) = first_item_id(parsed) else {
            continue;
        };
        match target.item_location(&id) {
            Some(written) if written == path.as_path() => {}
            _ => sources.push(path.clone()),
        }
    }
    for path in &sources {
        if let Err(e) = fs::remove_file(path) {
            eprintln!("error: removing the converted file {}: {e}", path.display());
            return runner::EXIT_RUNTIME;
        }
    }
    // THE BINDING NAMES A FIELD THIS CONVERSION JUST MOVED, and leaving it is
    // what turns a successful migration into an unusable tracker: the store
    // routes a row by `status_field`, stage0's status now lives inside
    // `last_status_change`, and every command afterwards fails with "carries
    // `id` but no `status` field" — on data that converted perfectly.
    //
    // It is not caught by the conversion itself, which builds its own target
    // store from this CLI's constants rather than from the declaration. So the
    // declaration has to be brought along, here, by the one command that knows
    // the field moved.
    match rewrite_status_field(project_items) {
        Ok(Some(path)) => println!("updated the store binding in {}", path.display()),
        Ok(None) => {}
        Err(e) => {
            eprintln!("error: the documents are converted, but {e}");
            eprintln!(
                "note: set `status_field: \"{STAGE0_STATUS_FIELD}\"` in the project's \
                 `ExtentBinding` by hand — until it names the field an item's status \
                 actually lives in, every command will refuse to route a row"
            );
            return runner::EXIT_RUNTIME;
        }
    }
    println!(
        "migrated {} file(s), {rows} row(s), to attribute documents",
        legacy.len() + plain.len()
    );
    if !stamped.is_empty() {
        println!("back-dated `created` on {} item(s)", stamped.len());
    }
    0
}

/// The PLAIN per-item files a `--to document` run would convert.
///
/// ONLY ITEM FILES, and only plain ones. A file already in either document shape
/// is left alone — a legacy one is converted through its own path, and an
/// attribute document must not be re-rendered, because re-rendering reflows
/// every chapter and would lose the hand-added prose the opacity invariant
/// exists to protect. A file holding no item is left alone too: the format stamp
/// at the tree's root is a `StoreFormat` row and has no prose for a chapter to
/// hold.
fn plain_item_files<'a>(
    interp: &Interpreter,
    declared: &DeclaredStore,
    project_items: &'a [ProjectFile],
    per_file: &[load::LoadResult],
) -> Result<Vec<(&'a Path, Vec<anthill_core::kb::RuleId>)>, i32> {
    let mut covered = Vec::with_capacity(declared.covers.len());
    for name in &declared.covers {
        match interp.kb().try_resolve_symbol(name) {
            Some(s) => covered.push(s),
            None => {
                eprintln!(
                    "error: this project's binding covers `{name}`, which resolves to nothing"
                );
                return Err(runner::EXIT_RUNTIME);
            }
        }
    }
    let mut out: Vec<(&Path, Vec<anthill_core::kb::RuleId>)> = Vec::new();
    for (file, result) in project_items.iter().zip(per_file.iter()) {
        if file.document.is_some()
            || fs_util::has_suffix(&file.path, &[ITEM_DOCUMENT_SUFFIX])
        {
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
            return Err(runner::EXIT_RUNTIME);
        }
        out.push((file.path.as_path(), mine));
    }
    Ok(out)
}

/// Point the project's `ExtentBinding` at the field an item's status now lives
/// in, and answer which file was rewritten.
///
/// NARROW ON PURPOSE. It rewrites exactly the pre-flattening stage0 spelling
/// (`"status"`), because that is the one this conversion moved. A binding naming
/// anything else belongs to a domain this command did not change, and a blanket
/// rewrite would repoint it at a field its own rows do not have — the store is
/// domain-neutral, and this is the one place that must not forget it.
fn rewrite_status_field(project_items: &[ProjectFile]) -> Result<Option<PathBuf>, String> {
    const WAS: &str = "status_field: \"status\"";
    let now = format!("status_field: \"{STAGE0_STATUS_FIELD}\"");
    for file in project_items {
        if file.source.contains(&now) {
            return Ok(None);
        }
    }
    let mut found: Option<&ProjectFile> = None;
    for file in project_items {
        if !file.source.contains(WAS) {
            continue;
        }
        if found.is_some() {
            return Err(format!(
                "two project files declare `{WAS}`; which one binds this store is a guess"
            ));
        }
        found = Some(file);
    }
    let Some(file) = found else {
        // Either there is no binding to update, or it names a field this
        // conversion did not move. Both are silence rather than a refusal.
        return Ok(None);
    };
    let text = file.source.replacen(WAS, &now, 1);
    fs::write(&file.path, text)
        .map_err(|e| format!("writing {}: {e}", file.path.display()))?;
    Ok(Some(file.path.clone()))
}

/// The `id` of the item a converted file declares, read off the parse IR.
fn first_item_id(parsed: &ParsedFile) -> Option<String> {
    use anthill_core::parse::ir::Item;
    fn walk(pf: &ParsedFile, items: &[Item]) -> Option<String> {
        for item in items {
            match item {
                Item::Namespace(ns) => {
                    if let Some(found) = walk(pf, &ns.items) {
                        return Some(found);
                    }
                }
                Item::Fact(f) => {
                    let Term::Fn { named_args, .. } = pf.terms.get(f.term) else {
                        continue;
                    };
                    if let Some(id) = ir_string(pf, named_args, STAGE0_ID_FIELD) {
                        return Some(id);
                    }
                }
                _ => {}
            }
        }
        None
    }
    walk(parsed, &parsed.items)
}

/// One legacy document, as the parse IR the new encoding would have produced.
///
/// THE STATUS NORMALISATION LIVES HERE, in the todo CLI, because it is stage0
/// knowledge: `anthill-core`'s reader is domain-neutral and must not learn that
/// `Claimed` used to carry `agent` and `since`. It is also the only place that
/// knowledge is needed — after this pass no file holds the old shape.
fn convert_legacy_document(
    path: &Path,
    source: &str,
    mapping: &DocumentMapping,
) -> Result<ParsedFile, String> {
    let doc = document::legacy::read(source)
        .ok_or("this file has no ```anthill head, so it is neither encoding")?;
    let head = &source[doc.head.clone()];
    let mut parsed = parse::parse(head).map_err(|errs| {
        format!(
            "the head does not parse: {}",
            errs.iter()
                .map(|e| format!("{e:?}"))
                .collect::<Vec<_>>()
                .join("; ")
        )
    })?;

    // The chapters, in the shapes the old mapping gave them: one `description`
    // field chapter, and the entries of one `Feedback` container.
    let mut description: Option<String> = None;
    let mut entries: Vec<String> = Vec::new();
    let mut in_container = false;
    for chapter in &doc.chapters {
        let body = source[chapter.body.clone()].to_string();
        match chapter.level {
            2 if chapter.heading.eq_ignore_ascii_case("description") => {
                in_container = false;
                description = Some(body);
            }
            2 if chapter.heading.eq_ignore_ascii_case("feedback") => in_container = true,
            2 => {
                return Err(format!(
                    "`## {}` is a chapter the previous encoding did not declare, so its text \
                     belongs to no field",
                    chapter.heading
                ))
            }
            3 if in_container => entries.push(body),
            _ => {}
        }
    }

    let mut feedback = 0usize;
    let mut plan: Vec<(usize, Rewrite)> = Vec::new();
    let mut index = 0usize;
    collect_legacy_rewrites(
        &parsed,
        &parsed.items.iter().collect::<Vec<_>>(),
        &mut index,
        &mut plan,
        &mut feedback,
        &description,
        &entries,
        path,
    )?;
    if feedback != entries.len() {
        return Err(format!(
            "the head declares {feedback} `Feedback` row(s) against {} entries below it",
            entries.len()
        ));
    }
    apply_legacy_rewrites(&mut parsed, &plan, mapping);
    assign_default_namespace(&mut parsed);
    Ok(parsed.with_path(path.to_path_buf()))
}

/// What one legacy fact needs done to it.
enum Rewrite {
    /// A `WorkItem`: hoist its `status` payload into a `StatusChange`, and fill
    /// the description chapter.
    Item { description: Option<String> },
    /// A `Feedback`: fill the content chapter.
    Feedback { content: String },
}

#[allow(clippy::too_many_arguments)]
fn collect_legacy_rewrites(
    parsed: &ParsedFile,
    items: &[&anthill_core::parse::ir::Item],
    index: &mut usize,
    plan: &mut Vec<(usize, Rewrite)>,
    feedback: &mut usize,
    description: &Option<String>,
    entries: &[String],
    path: &Path,
) -> Result<(), String> {
    use anthill_core::parse::ir::Item;
    for item in items {
        match item {
            Item::Namespace(ns) => collect_legacy_rewrites(
                parsed,
                &ns.items.iter().collect::<Vec<_>>(),
                index,
                plan,
                feedback,
                description,
                entries,
                path,
            )?,
            Item::Fact(f) => {
                let position = *index;
                *index += 1;
                let Term::Fn { functor, .. } = parsed.terms.get(f.term) else {
                    continue;
                };
                match parsed.symbols.local_name(*functor) {
                    "WorkItem" => plan.push((
                        position,
                        Rewrite::Item {
                            description: description.clone(),
                        },
                    )),
                    "Feedback" => {
                        let content = entries.get(*feedback).cloned().ok_or_else(|| {
                            format!(
                                "{}: more `Feedback` rows than entries below them",
                                path.display()
                            )
                        })?;
                        *feedback += 1;
                        plan.push((position, Rewrite::Feedback { content }));
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn apply_legacy_rewrites(
    parsed: &mut ParsedFile,
    plan: &[(usize, Rewrite)],
    mapping: &DocumentMapping,
) {
    use anthill_core::parse::ir::Item;
    let mut targets: Vec<(TermId, anthill_core::span::Span)> = Vec::new();
    fn scan(items: &[Item], out: &mut Vec<(TermId, anthill_core::span::Span)>) {
        for item in items {
            match item {
                Item::Namespace(ns) => scan(&ns.items, out),
                Item::Fact(f) => out.push((f.term, f.span)),
                _ => {}
            }
        }
    }
    scan(&parsed.items, &mut targets);

    let mut rebuilt: std::collections::HashMap<usize, TermId> = std::collections::HashMap::new();
    for (position, rewrite) in plan {
        let Some((term, span)) = targets.get(*position).copied() else {
            continue;
        };
        let new = match rewrite {
            Rewrite::Feedback { content } => {
                let literal = parsed
                    .terms
                    .alloc(Term::Const(Literal::String(content.clone())), span);
                with_named_arg(parsed, term, "content", literal, span)
            }
            Rewrite::Item { description } => {
                let mut term = hoist_status(parsed, term, span, mapping);
                if let Some(text) = description {
                    let literal = parsed
                        .terms
                        .alloc(Term::Const(Literal::String(text.clone())), span);
                    term = with_named_arg(parsed, term, "description", literal, span);
                }
                term
            }
        };
        rebuilt.insert(*position, new);
    }
    let mut index = 0usize;
    fn rewrite_items(
        items: &mut [Item],
        index: &mut usize,
        rebuilt: &std::collections::HashMap<usize, TermId>,
    ) {
        for item in items {
            match item {
                Item::Namespace(ns) => rewrite_items(&mut ns.items, index, rebuilt),
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
    rewrite_items(&mut parsed.items, &mut index, &rebuilt);
}

/// `status: Claimed(agent: a, since: t)` → `last_status_change: StatusChange(…)`.
///
/// THE OLD PAYLOADS WERE IRREGULAR, and that irregularity is the whole reason
/// this is a table of two field names rather than a rename: the time was called
/// `since` on `Claimed` and `Stale` and `at` on the other four, `agent` appeared
/// on two variants, and `Verified` carried neither. Whatever is not there
/// becomes `none` — nothing is invented, because the information is gone.
fn hoist_status(
    parsed: &mut ParsedFile,
    term: TermId,
    span: anthill_core::span::Span,
    mapping: &DocumentMapping,
) -> TermId {
    let Some(status) = named_arg_of(parsed, term, "status") else {
        return term;
    };
    let (variant, payload): (String, Vec<(String, TermId)>) = match parsed.terms.get(status).clone()
    {
        Term::Ref(s) | Term::Ident(s) => (parsed.symbols.local_name(s).to_string(), Vec::new()),
        Term::Fn {
            functor,
            named_args,
            ..
        } => (
            parsed.symbols.local_name(functor).to_string(),
            named_args
                .iter()
                .map(|(s, t)| (parsed.symbols.local_name(*s).to_string(), *t))
                .collect(),
        ),
        _ => return term,
    };
    let field = |name: &str| payload.iter().find(|(n, _)| n == name).map(|(_, t)| *t);
    let agent = field("agent");
    let at = field("at").or_else(|| field("since"));
    let reason = field("reason");

    let bare = parsed.terms.alloc(
        Term::Fn {
            functor: parsed.symbols.intern(&variant),
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        },
        span,
    );
    let mut named: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> = SmallVec::new();
    named.push((parsed.symbols.intern("status"), bare));
    for (name, held) in [("agent", agent), ("at", at), ("reason", reason)] {
        let value = match held {
            Some(v) => some_of(parsed, v, span),
            None => none_of(parsed, span),
        };
        named.push((parsed.symbols.intern(name), value));
    }
    let record = parsed.terms.alloc(
        Term::Fn {
            functor: parsed.symbols.intern("StatusChange"),
            pos_args: SmallVec::new(),
            named_args: named,
        },
        span,
    );
    let field_name = mapping
        .flat_records
        .first()
        .map(|r| r.field.clone())
        .unwrap_or_else(|| "last_status_change".to_string());
    let term = without_named_arg(parsed, term, "status", span);
    with_named_arg(parsed, term, &field_name, record, span)
}

/// WI-909 — THE FUNCTOR IS AN ADDRESS, not the short name. This is a HOST-SIDE MINT: it
/// builds an `Option` node straight into a `ParsedFile`, and the loader then resolves that
/// functor through the ordinary name ladder. While `some` sat on `kb::load`'s implicit
/// tier the short spelling resolved from anywhere; the tier is empty now, so a short name
/// here reaches nothing and the synthesized node silently stops matching.
///
/// MEASURED: with the tier rows removed and every `.anthill` import in place,
/// `anthill-todo`'s delete/tag/document suites failed with
/// `match_failed(occurrence: Node, scrutinee: Term)` -- a RUNTIME failure, not a load
/// error, because a synthesized node names nothing to fail about at load. Restoring the
/// rows made them pass, which is what identified this site.
///
/// Same rule as `parse::desugar_target` and `parse::pratt`: a functor a PROGRAM never
/// wrote must carry its target outright. `..` is unspellable by any identifier, so it
/// cannot be captured by a user declaration either.
fn some_of(parsed: &mut ParsedFile, value: TermId, span: anthill_core::span::Span) -> TermId {
    let mut named: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> = SmallVec::new();
    named.push((parsed.symbols.intern("value"), value));
    parsed.terms.alloc(
        Term::Fn {
            functor: parsed.symbols.intern("..anthill.prelude.Option.some"),
            pos_args: SmallVec::new(),
            named_args: named,
        },
        span,
    )
}

fn none_of(parsed: &mut ParsedFile, span: anthill_core::span::Span) -> TermId {
    parsed.terms.alloc(
        Term::Fn {
            functor: parsed.symbols.intern("..anthill.prelude.Option.none"),
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        },
        span,
    )
}

fn without_named_arg(
    parsed: &mut ParsedFile,
    term: TermId,
    field: &str,
    span: anthill_core::span::Span,
) -> TermId {
    let Term::Fn {
        functor,
        pos_args,
        named_args,
    } = parsed.terms.get(term).clone()
    else {
        return term;
    };
    let sym = parsed.symbols.intern(field);
    let named: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> =
        named_args.into_iter().filter(|(s, _)| *s != sym).collect();
    parsed.terms.alloc(
        Term::Fn {
            functor,
            pos_args,
            named_args: named,
        },
        span,
    )
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
  migrate --to document     make every item file an ATTRIBUTE DOCUMENT — an
                            `## Attributes` chapter of one line per field, then
                            the prose fields as chapters. Converts both shapes
                            that are not one already: a plain `WI-NNN.anthill`
                            file, and a file still holding a fenced `anthill`
                            head. NOT a pure reformat — every status value is
                            rewritten into the flat form, and an `Option` holding
                            an EMPTY list becomes absent.
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
/// Is `ns` the wrapper [`assign_default_namespace`] builds, rather than a namespace the
/// source wrote?
///
/// EVERY FIELD IT SETS IS CHECKED, which is what makes this a shape match rather than a
/// provenance guess: the name it mints, the default span it stamps, the absence of
/// descriptions, and the exact prelude-constructor imports it supplies. A file that
/// genuinely writes `namespace anthill.stage0` carries a real span and fails the second
/// clause; one that writes different imports fails the last.
fn is_synthetic_wrapper(ns: &anthill_core::parse::ir::Namespace) -> bool {
    use anthill_core::span::Span;
    if ns.span != Span::default() || !ns.descriptions.is_empty() {
        return false;
    }
    ns.imports.len() == SYNTHETIC_WRAPPER_IMPORTS.len()
}

/// The imports [`assign_default_namespace`] supplies, as `(owner, members)`. One source
/// of truth for the wrapper and for [`is_synthetic_wrapper`], so the two cannot drift.
const SYNTHETIC_WRAPPER_IMPORTS: [(&str, [&str; 2]); 2] =
    [("Option", ["some", "none"]), ("List", ["cons", "nil"])];

fn item_census(parsed: &ParsedFile) -> (usize, usize) {
    use anthill_core::parse::ir::Item;
    use anthill_core::span::Span;

    fn walk(items: &[Item], facts: &mut usize, others: &mut usize) {
        for item in items {
            match item {
                Item::Fact(_) => *facts += 1,
                Item::Namespace(ns) => {
                    // WI-909 — THE SYNTHETIC WRAPPER'S IMPORTS ARE NOT CONTENT. Since
                    // `assign_default_namespace` began supplying the prelude constructor
                    // imports its facts need, a bare fact file carries imports it did not
                    // write, and counting them here made every such file look like it held
                    // non-fact content -- which is exactly what `migrate` refuses to
                    // consume. Driven: seven `wi1118_migrate_test` rows failed on
                    // `migrate(&proj).status.success()` with no other symptom.
                    //
                    // MATCHED ON THE WRAPPER'S EXACT SHAPE, not on a sentinel span. A bare
                    // `ns.span == Span::default()` test would be a provenance guess on a
                    // one-way rewrite that DELETES files: any future producer of a
                    // zero-span namespace would silently stop `migrate` counting written
                    // imports and let it consume a file it must refuse. `is_synthetic_
                    // wrapper` instead asserts everything `assign_default_namespace`
                    // constructs -- the `anthill.stage0` name, the default span, no
                    // descriptions, and exactly the import set it supplies -- so a
                    // namespace that is not that wrapper cannot be mistaken for it.
                    // Raised by `/code-review`, which also caught the comment here citing
                    // import spans: `parse::ir::Import` has no span field.
                    if !is_synthetic_wrapper(ns) {
                        *others += ns.imports.len();
                    }
                    *others += ns.descriptions.len();
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

/// The `ExtentBinding` text an item-per-file project carries — written by `init` for a
/// new project and by `migrate --to item-per-file` for a converted one, so the two land
/// on the same declaration rather than on two spellings of it.
///
/// `covers` is a parameter because the two callers know different things: `init` names
/// every functor the bundle persists, while a migration carries across whatever the
/// project already declared.
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
///
/// A DOTTED PATH for the status (WI-K63ZV): an item's state is the last change
/// made to it, so the value the directory mirrors sits inside that record. The
/// store follows the path and learns nothing else about the shape.
const STAGE0_STATUS_FIELD: &str = "last_status_change.status";
const STAGE0_ID_FIELD: &str = "id";
const STAGE0_REF_FIELD: &str = "workitem";
/// The author a work item DOES record (WI-VDXAM). §6.7 settles that it records no
/// FILER; what it holds is the agent of its last status change, which is the one
/// who filed it while the item is still `Open`. It is stage0's own path rather
/// than a configured one — the binding names the id, status and reference fields
/// because the store routes on them, and this is read by the renumber alone.
const STAGE0_AGENT_FIELD: &str = "last_status_change.agent";

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
/// over `workitems.anthill` in the project directory, mirroring the functors the bundle
/// persists. Written as a VALUE rather than as a separate construction path, so a
/// defaulted project and a declaring one differ in exactly one thing — where the binding
/// came from — and share every line after this.
///
/// THIS IS NOT WHAT `init` SCAFFOLDS, and has not been since init moved to item-per-file.
/// It is the layout a project that declares NOTHING is read as, so it is pinned by the
/// trackers already written that way rather than by what a new one gets — see the note in
/// [`run_init`] for why the two must not be unified.
/// `default_matches_the_declared_single_file_binding` measures it against the spelled-out
/// text of the same configuration.
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
/// `WorkItem` (forget / replace), `Feedback` (forget, since WI-1123), `Tag`
/// (forget / untag_item) and `MirrorEntry` (forget, since WI-1117 — but only a
/// project with a mirror can hold one, so its coverage is required only there).
/// `StoreFormat` is persisted and never retracted.
///
/// ONE LIST, THREE READERS, deliberately: `default_binding` takes every name,
/// [`check_covers_every_retracted_functor`] takes the flagged ones, and [`run_init`]
/// takes every name SHORTENED, for the `covers:` list it scaffolds. Kept apart they
/// drift, and the drift is silent in the direction that matters — a functor added
/// to the default while the guard still names three, or while the scaffold does.
const STORED_FUNCTORS: [(&str, Retracted); 5] = [
    ("anthill.stage0.WorkItem", Retracted::Yes),
    ("anthill.stage0.Feedback", Retracted::Yes),
    ("anthill.stage0.Tag", Retracted::Yes),
    // WI-1117: `export` persists the link, and `forget` retracts it with the item
    // it names — the same cascade, and for the same reason, as the two above.
    ("anthill.stage0.MirrorEntry", Retracted::WhenMirrored),
    ("anthill.stage0.StoreFormat", Retracted::No),
];

/// The name a `covers:` list spells for a qualified functor: its last segment.
///
/// ONE RULE, THREE CALLERS. A `covers:` entry is read in a scope where `Feedback`
/// resolves and `anthill.stage0.Feedback` does not, so every writer of such a list owes
/// the same shortening — [`run_init`] scaffolds one, [`check_covers_every_retracted_functor`]
/// names the missing entries in its error, and `rewrite_binding` carries a project's own
/// list across a migration (via `local_name_of`, since it starts from resolved symbols
/// rather than text). Held apart, the three drifted silently: a wrong short name still
/// parses, and only fails later at symbol resolution.
///
/// AN UNQUALIFIED NAME ANSWERS ITSELF, and that is the right answer rather than a missing
/// guard: `covers:` wants the last segment, and a name with no dot already is one. What
/// catches a malformed [`STORED_FUNCTORS`] entry is `default_binding`, which resolves the
/// QUALIFIED form and fails loudly when it does not exist.
fn short_name(qualified: &str) -> &str {
    qualified.rsplit('.').next().unwrap_or(qualified)
}

/// Whether the bundle ever asks the store to remove a functor's rows — and, for
/// one of them, whether that can happen in THIS project at all.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Retracted {
    Yes,
    No,
    /// Retracted, but only a project WITH A MIRROR can hold such a row: `export`
    /// is the only thing that writes one (WI-1117). Requiring coverage
    /// unconditionally would refuse, at startup, every existing project that has
    /// no mirror and cannot reach the failure the requirement exists to prevent
    /// — a false alarm on a tracker where nothing is wrong, which is not what
    /// "loud over silent" asks for.
    WhenMirrored,
}

/// Whether this project can hold `MirrorEntry` rows: it declares a mirror to
/// publish to, or it already carries links from one.
///
/// BOTH HALVES, because either alone is reachable. A project that adds a `Mirror`
/// fact has not exported yet and holds no rows; a project whose mirror was
/// removed from the config still holds every link the last `export` wrote, and
/// `delete` would still be asked to retract one.
///
/// A read failure answers TRUE. The question is "must coverage be declared", and
/// the safe answer when it cannot be decided is the one that asks for the
/// declaration rather than the one that quietly drops the requirement.
fn project_is_mirrored(interp: &Interpreter) -> bool {
    use anthill_core::kb::extent::BodiedRulePolicy;
    ["anthill.stage0.Mirror", "anthill.stage0.MirrorEntry"]
        .iter()
        .any(|name| match interp.kb().try_resolve_symbol(name) {
            None => false,
            Some(sym) => match interp.kb().read_facts(sym, &[], BodiedRulePolicy::Refuse) {
                Ok(rows) => !rows.is_empty(),
                Err(_) => true,
            },
        })
}

/// The file the default store writes to — the same one the loader reads.
const DEFAULT_STORE_FILE: &str = "workitems.anthill";

/// The per-checkout override of the project's `Mirror.access` (WI-1117).
const MIRROR_ACCESS_ENV: &str = "ANTHILL_TODO_MIRROR";

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
    match is_project_dir(&abs_base) {
        Ok(true) => {
            eprintln!(
                "error: {} is already an anthill-todo project",
                abs_base.display()
            );
            return runner::EXIT_RUNTIME;
        }
        Ok(false) => {}
        Err(e) => {
            eprintln!("error: {e}");
            return runner::EXIT_RUNTIME;
        }
    }

    // REFUSE TO NEST A PROJECT INSIDE ANOTHER PROJECT'S TRACKER. Scaffolding into
    // `<proj>/anthill-todo/open/` is not merely redundant, it CORRUPTS THE OUTER
    // PROJECT: `collect_anthill_files` walks `<proj>/anthill-todo` recursively, so
    // the nested `project.anthill` becomes a second `Project` fact and a second
    // `ExtentBinding` in the outer project's own KB — measured, `add` at `<proj>`
    // then dies with "default acceptance found multiple Project facts", naming
    // neither file. Discovery is nearest-first, so the nested tracker also shadows
    // the real one for everything beneath it (found by /code-review).
    //
    // THE TEST IS "INSIDE A TRACKER", NOT "BENEATH A PROJECT", and the difference
    // is the false positive it avoids: someone whose home directory holds a
    // personal `~/anthill-todo/` must still be able to `init` at `~/code/newthing`,
    // which is below that project but outside its tracker.
    for ancestor in abs_base.ancestors().skip(1) {
        let tracker = ancestor.join("anthill-todo");
        match is_project_dir(&tracker) {
            Ok(true) if abs_base.starts_with(&tracker) => {
                eprintln!(
                    "error: {} is inside the anthill-todo project at {} — a project nested \
                     in another project's tracker is read as part of it, and breaks it.\n  \
                     Work items go in that project (`anthill-todo add`), or pass -d <dir> \
                     naming a directory outside it.",
                    abs_base.display(),
                    tracker.display()
                );
                return runner::EXIT_RUNTIME;
            }
            Ok(_) => {}
            Err(e) => {
                eprintln!("error: {e}");
                return runner::EXIT_RUNTIME;
            }
        }
    }

    let name = project_name.map(str::to_string).unwrap_or_else(|| {
        abs_base
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("my-project")
            .to_string()
    });

    // THE NAME GOES INTO A STRING LITERAL, and a project file that does not parse is only
    // a WARNING — so a name carrying `"` or `\` would write a `project.anthill` whose
    // `ExtentBinding` is silently dropped, and the project would run on the single-file
    // default instead of the layout it was just scaffolded for (found in review; before
    // the scaffold carried the layout this was cosmetic). Refused rather than escaped:
    // the default name is a DIRECTORY BASENAME nobody chose for this purpose, so the
    // honest answer is to say so and let the user name the project themselves.
    if name.contains('"') || name.contains('\\') {
        eprintln!(
            "error: project name {name:?} cannot be written to project.anthill — a name \
             carrying `\"` or `\\` would not parse, and the store binding under it would be \
             silently dropped. Name the project explicitly: `anthill-todo init <name>`"
        );
        return runner::EXIT_RUNTIME;
    }

    fs::create_dir_all(&dir).expect("cannot create anthill-todo/");

    // No domain.anthill / rules.anthill: the standard anthill.stage0 domain and
    // workflow rules ship bundled in the binary (WI-505), so a fresh project
    // has no per-project copy that could drift out of sync with the grammar.

    // The scaffold carries the store binding (WI-830) so a fresh project SHOWS its
    // configuration rather than inheriting an invisible one — and here it MUST, because
    // it deliberately no longer agrees with [`default_binding`]. A project created today
    // is ITEM-PER-FILE; a project that declares nothing is still read as the one shared
    // file it was written in.
    //
    // THE DEFAULT DOES NOT FOLLOW THE SCAFFOLD, and that asymmetry is deliberate.
    // `default_binding` answers for the zero-config trackers already on disk, every one
    // of which holds its rows in `workitems.anthill`. Moving it in step with this would
    // not silently misread them — MEASURED: the item-per-file store refuses a shared file
    // it finds, exits 1, and names `migrate --to item-per-file`. It would break all of
    // them at once instead, forcing a migration nobody asked for. So the scaffold moves
    // and the default stays. `default_matches_the_declared_single_file_binding` measures
    // the half that must not move; `init_scaffolds_the_item_per_file_layout` measures
    // this one.
    //
    // THE COST OF THE ASYMMETRY IS PAID IN `build_declared_store`: with the two no longer
    // equal, a project that LOSES its binding would default to the single file and write
    // a second store beside its item tree. That is guarded there, not here.
    //
    // `covers` NAMES `MirrorEntry` AND THIS REPO'S OWN `project.anthill` DOES NOT, which
    // is a deliberate asymmetry rather than drift. A `covers` entry is resolved at
    // startup, so naming a functor a given BINARY does not define is a hard refusal —
    // which is why the declaration must never get ahead of the backend (design §14.1).
    // A scaffold satisfies that BY CONSTRUCTION: the file is written by the same binary
    // that has the functor. A checked-in `project.anthill` does not — it is pulled by
    // checkouts whose `anthill-todo` is older, and every one of them stops working the
    // moment it lands. MEASURED, on this repo: adding the entry to a tracker with no
    // mirror bought nothing and broke every un-rebuilt binary.
    let covers: Vec<&str> = STORED_FUNCTORS
        .iter()
        .map(|(name, _)| short_name(name))
        .collect();
    let project = format!(
        "-- Project configuration\n\nfact Project(\n  name: \"{name}\",\n  language: \"rust\",\n  build: \"cargo\",\n  tools: [\"cargo-test\"])\n\n\
         -- Which store holds these work items, and in which role (proposal 057).\n\
         -- `mirror`: every file here is loaded at startup and the KB answers reads, with\n\
         -- the store as the write-through durability leg. `root: \".\"` is this directory.\n\
         -- One file per item, under a directory named for the item's status.\n\
         {binding}\n",
        binding = item_per_file_binding(&covers)
    );
    // `StoreFormat` carries neither an id nor an item reference, so `ItemPerFileStore`
    // files it at the root under its own snake_cased functor (`Route::StoreLevel`). This
    // writes that same path directly: `init` has no loaded KB to flush through the store.
    //
    // THE STAMP FIRST AND THE MARKER LAST. `project.anthill` is a `PROJECT_MARKERS` entry
    // and `store_format.anthill` is not, so this order makes an interrupted scaffold a
    // directory that is not yet a project. The other order leaves a DISCOVERABLE project
    // with no stamp: every later command warns "pre-versioning", while `init` refuses to
    // run again over the directory it half-made (found in review).
    let store_format = format!("fact StoreFormat(version: {CURRENT_STORE_FORMAT_VERSION})\n");
    for (leaf, body) in [
        ("store_format.anthill", store_format),
        ("project.anthill", project),
    ] {
        // Loud, not a panic: the rest of this crate answers an I/O fault with
        // `EXIT_RUNTIME`, and a half-written scaffold is exactly the state a user needs
        // told about rather than shown a backtrace for.
        if let Err(e) = fs::write(dir.join(leaf), body) {
            eprintln!("error: cannot write {}: {e}", dir.join(leaf).display());
            return runner::EXIT_RUNTIME;
        }
    }

    // The absolute path, not a bare `anthill-todo/`: a wrong-place write must be
    // visible in the output even when -d is right. The old message named no path
    // and so could not have revealed WI-748 even to someone staring at it.
    println!("created {} with:", dir.display());
    println!("  project.anthill      — project configuration");
    println!("  store_format.anthill — the data format its items are written in");
    println!("(each item lands in its own file, under a directory named for its status)");
    println!("(the anthill.stage0 domain + workflow rules ship bundled with anthill-todo)");
    0
}

// `migrate` is served by the anthill bundle (main.anthill `cmd_migrate`): it stamps the
// project with a `StoreFormat` fact THROUGH the store — so the file it lands in is
// whichever one the declared store files a store-level row in (`workitems.anthill` on the
// single-file layout, `store_format.anthill` on the item-per-file one) — keeping the
// version-format logic in the bundle rather than host text-writing (WI-434).

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

    // `ANTHILL_TODO_MIRROR=on|off` REACHES THE BUNDLE AS `--mirror <value>`
    // (WI-1117, design §3.2). The environment is where a PER-CHECKOUT override
    // of a project-wide default belongs — a CI test job, an air-gapped machine,
    // a fork with no write token — and the host is the only side that can see
    // it, so the translation happens here rather than in anthill.
    //
    // ONLY FOR THE TWO COMMANDS THAT DECLARE THE FLAG: `--mirror` on any other
    // subcommand is an unknown argument, so injecting it unconditionally would
    // make `ANTHILL_TODO_MIRROR` break every command in the tool.
    //
    // AN EXPLICIT FLAG WINS. Someone who typed `--offline` or `--mirror` on the
    // command line has answered the question for this run, and a second answer
    // arriving from the environment would silently overrule the one they can see.
    if matches!(bundle_argv.first().map(String::as_str), Some("export") | Some("import"))
        && !bundle_argv
            .iter()
            .any(|a| a == "--mirror" || a.starts_with("--mirror=") || a == "--offline")
    {
        // SET-BUT-EMPTY IS ABSENT. `std::env::var` answers `Ok("")` for
        // `ANTHILL_TODO_MIRROR=`, which is how a CI system writes a variable it
        // has no value for — and injecting `--mirror ""` would hard-fail both
        // commands with "`--mirror ` is neither `on` nor `off`" on a job that
        // configured nothing.
        match std::env::var(MIRROR_ACCESS_ENV) {
            Ok(value) if !value.trim().is_empty() => {
                // The BUNDLE decides whether the value is legal, and says so
                // naming the flag. Refusing here would need a second copy of that
                // rule and a second message that could disagree with it.
                bundle_argv.push("--mirror".to_string());
                bundle_argv.push(value);
            }
            _ => {}
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
    let scan = project_dir.clone();
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
    // Files still in the WI-1120 encoding: not loaded, converted by `migrate`.
    let mut legacy_documents: Vec<(PathBuf, String)> = Vec::new();
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
        // AN ITEM DOCUMENT IS DATA, NOT SOURCE (WI-K63ZV): its attributes
        // chapter is turned into the facts a plain `fact` file would have
        // declared, and its prose is spliced into them. So there is nothing here
        // for the parser to be handed — `parse_document` produces the IR
        // directly.
        if fs_util::has_suffix(file, &[ITEM_DOCUMENT_SUFFIX]) {
            // A file still in the PREVIOUS encoding is not read at all. It is
            // recorded so that `migrate --to document` can convert it and every
            // other command can refuse loudly; parsing it against today's domain
            // would produce a wall of type errors naming a shape nobody wrote.
            if document::legacy::is_legacy(&source) {
                legacy_documents.push((file.clone(), source));
                continue;
            }
            let doc = match document::read_document(&source, &mapping) {
                Ok(doc) => doc,
                Err(e) => {
                    eprintln!("error: {}: {e}", file.display());
                    return runner::EXIT_COMPILE;
                }
            };
            match parse_document(&source, &doc, &mapping) {
                Ok((parsed, faults)) => {
                    let mut parsed = parsed;
                    assign_default_namespace(&mut parsed);
                    project_items.push(ProjectFile {
                        path: file.clone(),
                        parsed: parsed.with_path(file.clone()),
                        source,
                        document: Some(Document { faults: doc.faults.into_iter().chain(faults).collect(), ..doc }),
                    });
                }
                Err(e) => {
                    eprintln!("error: {}: {e}", file.display());
                    return runner::EXIT_COMPILE;
                }
            }
            continue;
        }
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
                    source,
                    document: None,
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
    // THE FORGE HOST FUNCTIONS, AND THEY GO IN BEFORE THE LOAD (WI-1117/WI-1122).
    // `coordination.anthill`'s binding block names five functions this crate owns
    // — anthill-core's `HOST_FNS` is a closed slice that knows nothing about
    // forges — and the seam seals its registry when the loader builds its mapping
    // cache, so registering after `load_all` is refused. It has to be here even
    // for a project with no mirror at all: the mapping is in the BUNDLE, and an
    // unknown key stops every interpreter built for the program, including the
    // scratch one each bridged evaluation makes.
    if let Err(e) = forge::register(&mut kb, &project_dir) {
        eprintln!("error: {e}");
        return runner::EXIT_COMPILE;
    }
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
    let store_root = project_dir.clone();
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
        return run_fsck(
            &mut interp,
            &mut declared.store,
            &store_root,
            &bundle_argv[1..],
        );
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
            &legacy_documents,
            &bundle_argv[1..],
        );
    }

    // A FILE IN THE PREVIOUS ENCODING IS A LOUD REFUSAL, not an item that
    // quietly is not there. It was not parsed, so its rows are in no KB and no
    // store; every command would run against a tracker missing that item and
    // report success. `migrate --to document` is served above, which is why the
    // gate sits below it.
    if !legacy_documents.is_empty() {
        for (path, _) in legacy_documents.iter().take(5) {
            eprintln!(
                "error: {}: still written as a fenced `anthill` head plus chapters",
                path.display()
            );
        }
        if legacy_documents.len() > 5 {
            eprintln!("error: …and {} more", legacy_documents.len() - 5);
        }
        eprintln!(
            "error: {} item file(s) are in the previous encoding and were NOT read. Run \
             `anthill-todo migrate --to document` to convert them",
            legacy_documents.len()
        );
        return runner::EXIT_RUNTIME;
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
        match remedies_for(&faults).join(" and then ") {
            remedy if remedy.is_empty() => eprintln!(
                "error: no command repairs this — the fault above needs a hand: either it \
                 is a disagreement only you can settle, or repairing it mechanically \
                 would lose what it is reporting"
            ),
            remedy => eprintln!("error: run {remedy} to repair this"),
        }
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
