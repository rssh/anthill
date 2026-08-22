//! WI-995 — MEASUREMENT: what does making imports file-local COST on the corpus?
//!
//! The ticket's rule is that an import resolves ONLY in the file where it is listed.
//! Today an import is written into a table keyed by the ADDRESS (`ScopeId`), and two
//! files can write one address (`namespace demo` in each), so one file's import
//! changes how a bare name resolves in another. Before that behaviour changes, the
//! ticket requires the corpus cost be MEASURED — "the count decides whether this
//! lands as a refusal, a warning, or a migration".
//!
//! HOW IT IS MEASURED — a counterfactual, not a proxy. `SymbolTable::resolve_in_scope`
//! answers every name TWICE while the audit runs: once as today, and once under
//! `ImportVisibility::OwnFileOnly`, where an import alias or import-contributed parent
//! link written by a file OTHER than the asking one is not there at all. A name whose
//! two answers DISAGREE is a name that would stop resolving (or resolve elsewhere)
//! under the rule — that, and only that, is the cost. Counting import statements, or
//! shared addresses, would measure exposure instead: neither says whether any name
//! actually reaches across.
//!
//! WHAT IS EXEMPT, stated because it is a judgement and not a fact of the code:
//!   - `ImportOrigin::Builtin` — the prelude / kernel-vocab aliases the loader writes
//!     into `<global>` itself. They are written in no file, so they are local to none;
//!     under any reading of the rule they stay visible.
//!   - `requires`, enclosing-body and variant-exposure parent links. They come from a
//!     DECLARATION at the address, not from one file's import list, so the rule does
//!     not touch them. Only `Plain` / `Wildcard` import links are file-scoped here.
//!
//! THE THIRD BUCKET is the ticket's open question made visible: resolutions with NO
//! asking file (`asking: None`) — the typer's type-param lookup and the query path run
//! after the per-file loop, where no one file is asking. The rule has no answer for
//! them yet, so they are reported SEPARATELY rather than folded into the cost.

use anthill_core::intern::ImportOrigin;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use std::path::PathBuf;

/// Load one corpus group with the audit running, and render the report.
/// Returns `(report text, cross-file site count, unattributed site count)`.
fn audit_corpus(label: &str, files: &[PathBuf]) -> (String, usize, usize) {
    let parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src =
                std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src)
                .unwrap_or_else(|errs| panic!("parse {}: {errs:?}", p.display()))
                .with_path(p.clone())
        })
        .collect();
    let refs: Vec<&parse::ir::ParsedFile> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    kb.begin_import_audit();
    // WI-966: READ the verdict. A group that will not load measures nothing, and a
    // discarded `Err` would let this report a confident zero over a KB that stopped
    // loading at its first file.
    let verdict = load::load_all(&mut kb, &refs, &NullResolver);
    let load_errors: Vec<String> = match verdict {
        Ok(_) => Vec::new(),
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    };
    let audit = kb.take_import_audit().expect("audit was begun");

    let name_of = |idx: Option<anthill_core::span::SourceId>| -> String {
        match idx {
            None => "<no asking file — typer / query>".to_string(),
            Some(i) => files
                .get(i.index())
                .map(|p| {
                    p.file_name()
                        .unwrap_or(p.as_os_str())
                        .to_string_lossy()
                        .to_string()
                })
                .unwrap_or_else(|| format!("<source #{}>", i.raw())),
        }
    };

    let mut uses: Vec<_> = audit.uses.values().collect();
    // `SourceId` is not `Ord`; sort on its raw, which is the registration order.
    uses.sort_by_key(|u| (u.asking.map(|s| s.raw()), u.name.clone()));
    let cross_file = uses.iter().filter(|u| u.asking.is_some()).count();
    let unattributed = uses.len() - cross_file;

    let (alias_entries, parent_edges) = kb.import_record_counts();
    let mut out = String::new();
    out.push_str(&format!(
        "\n══ {label} — {} files, {} name resolutions audited\n   \
         instrument recorded {alias_entries} import alias entries, \
         {parent_edges} import parent edges\n",
        files.len(),
        audit.resolutions
    ));
    // A zero cost is only evidence if the instrument had something to suppress.
    //
    // WI-1089 narrowed which half that is on a CORPUS. An import parent edge is now
    // written by the wildcard form alone — a plain `import a.b.C` binds the name and
    // links nothing — and the corpus writes no wildcard imports, so `parent_edges` is
    // legitimately 0 here. The alias half is what these groups exercise, and the
    // parent-edge half keeps its own control in `the_instrument_is_not_vacuous`
    // below, which writes `import lib.*` precisely so the second predicate is driven.
    assert!(
        alias_entries > 0,
        "{label}: the alias origin table is empty — the instrument suppressed nothing, \
         so its verdict measures nothing"
    );
    if !load_errors.is_empty() {
        out.push_str(&format!(
            "   NB this group does not load clean today ({} errors, first: {})\n",
            load_errors.len(),
            load_errors[0]
        ));
    }
    out.push_str(&format!(
        "   cross-file import dependencies: {cross_file} site(s)   \
         unattributed (typer/query): {unattributed} site(s)\n"
    ));
    for u in &uses {
        out.push_str(&format!(
            "     [{}] `{}` in scope `{}`  ×{}\n        pre-WI-995 (shared): {}\n        now (file-local): {}\n",
            name_of(u.asking),
            u.name,
            kb.qualified_name_of(u.scope.owner()),
            u.hits,
            render(&kb, &u.shared_imports),
            render(&kb, &u.file_local),
        ));
    }

    let contested = kb.contested_import_entries();
    out.push_str(&format!(
        "   import entries written by more than one origin: {}\n",
        contested.len()
    ));
    for (scope, name, writes) in contested.iter().take(40) {
        let w: Vec<String> = writes
            .iter()
            .map(|(o, target)| match o {
                ImportOrigin::Builtin => format!("builtin→{target}"),
                ImportOrigin::Declaration => format!("declaration→{target}"),
                ImportOrigin::Invocation => format!("invocation→{target}"),
                ImportOrigin::File(f) => format!("{}→{target}", name_of(Some(*f))),
                // WI-M460D — this is the import-ALIAS channel; only `add_import`
                // writes it, and it files Builtin/File/Invocation. An `Exposure`
                // here would mean a parent-edge origin had leaked into the alias
                // table, so it is rendered loudly rather than given a plausible
                // spelling that would read as expected output in the report.
                ImportOrigin::Exposure => format!("BUG:exposure-origin-in-alias→{target}"),
            })
            .collect();
        out.push_str(&format!("     `{name}` in `{scope}`: {}\n", w.join(", ")));
    }
    (out, cross_file, unattributed)
}

fn render(kb: &KnowledgeBase, r: &anthill_core::intern::ResolveResult) -> String {
    use anthill_core::intern::ResolveResult::*;
    match r {
        Found(s) => format!("Found({})", kb.qualified_name_of(*s)),
        Ambiguous(c) => format!("Ambiguous({:?})", kb.candidate_names(c)),
        NotFound => "NotFound".to_string(),
    }
}

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn files_under(rel: &str) -> Vec<PathBuf> {
    let mut v = crate::common::collect_anthill_files(&root().join(rel));
    v.sort();
    v
}

/// THE CONTROL for the corpus measurement above, and it is the half that makes the
/// measured number mean anything: a zero cost is indistinguishable from an instrument
/// that never fires, and this repo has been wrong in exactly that way before.
///
/// These are the ticket's own fixtures. Two files write ONE address (`namespace demo`);
/// only the second carries the import, and the first reads the bare name. Under today's
/// rule the name resolves through the OTHER file's import — which is precisely what the
/// audit must report.
///
/// A CONTROL fixture rides along where the import is written in the SAME file that
/// reads it: it must stay silent, or the instrument is reporting every import rather
/// than the cross-file ones.
///
/// WHICH TEST FAILS WHEN THE INSTRUMENT IS BACKED OUT: this one — `cross_file` drops to
/// 0. `wi995_measure_import_file_locality_cost` passes either way by design; it reports
/// a corpus number and asserts only that the instrument ran.
#[test]
fn wi995_control_a_foreign_files_import_is_detected() {
    // The name has to be one the import is LOAD-BEARING for. A prelude name
    // (`Int64`) is reachable with no import at all — the implicit-prelude tier — so
    // suppressing an import of it changes no answer, and a fixture built on one
    // reports zero however broken the instrument is. Measured: it did.
    let lib = r#"
namespace lib
  sort Thing
    entity Thing(v: Int64)
  end
end
"#;
    // Reader and import in the SAME file — must NOT be reported.
    let same_file = r#"
namespace demo
  import lib.{Thing}
  sort Holder
    entity Holder(t: Thing)
  end
end
"#;
    // The SAME text, with the import moved to a second file writing the SAME address.
    let reader_only = r#"
namespace demo
  sort Holder
    entity Holder(t: Thing)
  end
end
"#;
    let importer_only = r#"
namespace demo
  import lib.{Thing}
end
"#;

    let audit_of = |sources: &[&str]| -> (usize, u64) {
        let parsed: Vec<_> = sources
            .iter()
            .map(|s| parse::parse(s).expect("fixture parses"))
            .collect();
        let stdlib = crate::common::collect_anthill_files(&root().join("stdlib/anthill"));
        let stdlib_parsed: Vec<_> = stdlib
            .iter()
            .map(|p| {
                let src = std::fs::read_to_string(p).expect("read stdlib file");
                parse::parse(&src)
                    .expect("stdlib parses")
                    .with_path(p.clone())
            })
            .collect();
        let mut refs: Vec<&parse::ir::ParsedFile> = stdlib_parsed.iter().collect();
        refs.extend(parsed.iter());
        let mut kb = KnowledgeBase::new();
        kb.begin_import_audit();
        // The fixtures are about RESOLUTION, not about loading clean; read the verdict
        // anyway so a fixture that stops loading cannot masquerade as a quiet result.
        let load_errors = match load::load_all(&mut kb, &refs, &NullResolver) {
            Ok(_) => Vec::new(),
            Err(e) => e.iter().map(|e| e.to_string()).collect(),
        };
        let audit = kb.take_import_audit().expect("audit was begun");
        let cross = audit.uses.values().filter(|u| u.asking.is_some()).count();
        // The split fixtures are SUPPOSED to stop loading — that is the rule working —
        // so the caller decides; both counts come back and each assertion below says
        // which it means.
        (cross, load_errors.len() as u64)
    };

    // THE TICKET'S ACCEPTANCE. The same-file fixture keeps working; the split one — an
    // import written in one file and the name read in another at the SAME address —
    // refuses. This is the ticket's fixture D, and it is the whole point.
    let (same_cross, same_errs) = audit_of(&[lib, same_file]);
    assert_eq!(
        same_errs, 0,
        "an import read in its OWN file must keep working"
    );
    assert_eq!(
        same_cross, 0,
        "and it is not a cross-file dependency, so the audit must not report it",
    );

    let (split_cross, split_errs) = audit_of(&[lib, reader_only, importer_only]);
    assert!(
        split_errs > 0,
        "fixture D must refuse: `Thing` is imported in one file and read in another",
    );
    assert!(
        split_cross > 0,
        "and the audit must name it as a resolution that USED to reach across files; \
         got {split_cross}. With no report the corpus zero would measure nothing.",
    );

    // THE SECOND PRODUCER — a WILDCARD import reaches through the PARENT-LINK path, not
    // the alias path, and the two are suppressed by different predicates
    // (`import_entry_visible` / `import_parent_visible`). A control exercising only the
    // alias would leave half the instrument unproven.
    let importer_wildcard = "\nnamespace demo\n  import lib.*\nend\n";
    let (wild_cross, wild_errs) = audit_of(&[lib, reader_only, importer_wildcard]);
    assert!(
        wild_errs > 0 && wild_cross > 0,
        "a WILDCARD import in another file must refuse too and be reported; got \
         {wild_errs} errors / {wild_cross} sites",
    );
}

/// THE HOLE THE RULE IS ABOUT, at its sharpest: two files import DIFFERENT symbols
/// under ONE name into ONE address. Each file must read its own.
///
/// This is the case a NAME-keyed rule silently passes. `Scope.imports` is a `HashMap`,
/// so the later file's write wins it outright; a check that only asks "did some visible
/// origin write an entry under this name" answers yes for the EARLIER file too and then
/// hands back the winner's symbol — so file A's `Thing` becomes file B's `Thing`,
/// decided by load order. The rule has to carry the visible write's OWN symbol.
///
/// DRIVEN THROUGH A CLOSED LABEL, so no type introspection is needed: the two `Thing`s
/// have DIFFERENT field names, and an entity's labels are closed (WI-851). If either
/// file's `Thing` resolved to the other's, its field name would be unknown there and the
/// load would fail — so a clean load IS the assertion that each file read its own.
///
/// WHICH TEST FAILS WHEN THE SYMBOL-KEYING IS BACKED OUT: this one, and only this one.
/// Fixture D in the control above passes either way — its foreign import is the ONLY
/// write of that name, so name-keying and symbol-keying agree there. That is exactly why
/// it did not catch this.
#[test]
fn wi995_two_files_importing_one_name_each_read_their_own() {
    let libs = "\
namespace liba
  sort Thing
    entity Thing(only_a: Int64)
  end
end

namespace libb
  sort Thing
    entity Thing(only_b: Int64)
  end
end
";
    // Both write `namespace demo` — ONE address — and each imports a DIFFERENT `Thing`.
    let reads_a = "\
namespace demo
  import liba.{Thing}
  fact holds_a(t: Thing(only_a: 1))
end
";
    let reads_b = "\
namespace demo
  import libb.{Thing}
  fact holds_b(t: Thing(only_b: 2))
end
";

    // CONTROL: each file alone loads, so the labels and the imports are well-formed and
    // a failure below is about the two COEXISTING, not about either fixture.
    crate::common::try_load_kb_with_files(&[libs, reads_a]).expect("file A alone must load");
    crate::common::try_load_kb_with_files(&[libs, reads_b]).expect("file B alone must load");

    // THE CLAIM, in both orders — the defect is load-order dependent, so one order alone
    // would pass on the winner's side and prove nothing.
    crate::common::try_load_kb_with_files(&[libs, reads_a, reads_b]).unwrap_or_else(|e| {
        panic!("A then B: each file must read the `Thing` IT imported; got {e:?}")
    });
    crate::common::try_load_kb_with_files(&[libs, reads_b, reads_a]).unwrap_or_else(|e| {
        panic!("B then A: each file must read the `Thing` IT imported; got {e:?}")
    });
}

/// The whole measurement, as one test so the groups share one report.
#[test]
fn wi995_measure_import_file_locality_cost() {
    let stdlib = files_under("stdlib/anthill");
    let stl = files_under("rustland/anthill-stl/anthill");
    let base: Vec<PathBuf> = stdlib.iter().chain(stl.iter()).cloned().collect();

    let with =
        |extra: &str| -> Vec<PathBuf> { base.iter().cloned().chain(files_under(extra)).collect() };

    let groups: Vec<(&str, Vec<PathBuf>)> = vec![
        ("stdlib alone", stdlib.clone()),
        (
            "stdlib + rust host bindings (the suite's baseline)",
            base.clone(),
        ),
        (
            "baseline + examples/github-todo",
            with("examples/github-todo"),
        ),
        (
            "baseline + anthill-todo (this project's tracker)",
            with("anthill-todo"),
        ),
        (
            "baseline + examples/webots-modelling",
            with("examples/webots-modelling"),
        ),
        ("baseline + anthill-testcases", with("anthill-testcases")),
    ];

    let mut report = String::new();
    let mut totals = Vec::new();
    for (label, files) in &groups {
        let (text, cross, unattributed) = audit_corpus(label, files);
        report.push_str(&text);
        totals.push((label.to_string(), cross, unattributed));
    }

    report.push_str("\n══ SUMMARY (cross-file / unattributed sites)\n");
    for (label, cross, un) in &totals {
        report.push_str(&format!("   {cross:>5} / {un:<5}  {label}\n"));
    }
    eprintln!("{report}");
    std::fs::write(
        std::env::temp_dir().join("wi995-import-locality-report.txt"),
        &report,
    )
    .ok();

    // The assertion is deliberately only that the audit RAN and saw the corpus —
    // the numbers themselves are the deliverable and are pinned by the caller that
    // reads this report, not here. A zero denominator would mean the instrument
    // measured nothing, which is the one outcome that must never read as "no cost".
    assert!(
        totals.iter().all(|(_, _, _)| true) && !totals.is_empty(),
        "no corpus groups were audited"
    );
}
