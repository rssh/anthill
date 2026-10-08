//! WI-20261008-RAH0Z — every test's stdlib load goes through the one recipe
//! (`tests/common`), except in the files listed here BY NAME.
//!
//! This is a mechanical guard, and it exists because the shape it forbids was in 174
//! files: a test that takes the stdlib's files and calls `load_all` itself. Such a load
//!
//! * is outside `ANTHILL_TEST_TWO_STEP_LOAD` — counted on 2026-10-07, 1 028 of the 9 591
//!   stdlib loads the integration binaries execute ran one-shot whatever the switch
//!   said, so "green under two-step" said nothing about the tests that made them;
//! * will be outside a stdlib loaded once per test binary (WI-059), for the same reason:
//!   neither reaches a test except through the recipe;
//! * re-read and re-parsed the 87 stdlib files at every call, where the recipe parses
//!   them once per binary.
//!
//! Most of the copies were the recipe verbatim. About thirty existed because `common`
//! did not hand out what they wanted — the loader's `LoadError` values, a clean load's
//! warnings, the KB a refused load left, a file read from disk. It does now
//! (`common::LoadOutcome`, `common::UserFile`), so the reason is gone and the rule can be
//! "through the recipe, or named here".
//!
//! WHAT THE GUARD SEES: a file under `anthill-core/tests`, outside `common/`, that names
//! a way OUT of the recipe on a line that is not a comment —
//!
//! * the stdlib's files, to load by hand: `stdlib_parsed(`, `stdlib_dir(`,
//!   `rust_stl_dir(`;
//! * a recipe NAMED instead of read from the switch: `LoadRecipe::OneShot`,
//!   `LoadRecipe::TwoStep`;
//! * a `common` helper that names one for its caller: `present_all_again(` (the stdlib
//!   and the test's files in ONE call, into a KB that holds them),
//!   `load_stdlib_kb_with_source(` and `load_stdlib_kb_untyped(` (the stdlib, then the
//!   test's file in a call of its own).
//!
//! A later load made by hand into a KB that was loaded some other way
//! (`load_in_a_later_call`, a bare `load_all(&mut kb, &[&file], ..)`) is not on the
//! list: it is one more load, not the load of the stdlib with the test's files.
//!
//! Each such file is in [`PINNED`] with its reason and with HOW MANY lines of it name
//! one, so a second way out added to a file that is already listed is seen too — the
//! count is part of the entry. An entry whose file no longer names one fails as well, so
//! the list stays the list.
//!
//! WHAT IT DOES NOT SEE, and says so. It reads text, so it does not see a spelling it
//! was not given: a recipe variant reached through a glob import, a function passed by
//! name. And it does not see a load that takes the stdlib's files without `common`:
//!
//! * `wi995_import_file_locality_test::audit_corpus` spells the stdlib's PATH — its
//!   corpus groups are lists of paths loaded in one call each — and says why at its site;
//! * `wi925_entity_desugaring_test` and `wi926_eponymous_entity_test` hand the loader ONE
//!   file and a `FileSourceResolver` over `stdlib/`, which reads what that file imports.
//!   That is the loader's other entry to the stdlib, not a copy of the recipe's corpus.
//!
//! The collector the 174 copies were built on, `collect_stdlib_and_rust_bindings`, is
//! private to `common` now, which the compiler enforces.
//!
//! CONTROL — `every_way_out_of_the_recipe_is_pinned_by_name` is the test that fails when
//! a copy comes back. Every other test in the suite passes with a copy restored, by
//! design: a copy loads the same files. MEASURED, each by making the change and running
//! this file: a `crate::common::stdlib_parsed()` call added to a file that is not listed
//! (`cut_test.rs`) — it FAILS naming the file; the `wi718…` entry deleted — it FAILS
//! naming that file as unlisted; an entry added for a file that names nothing — it FAILS
//! naming the entry as stale; a second `stdlib_parsed()` call added to a listed file
//! (`wi718…`) — it FAILS naming the file and both counts.
//!
//! AND THE ENTRIES THE COPIES MOVED TO FOLLOW THE SWITCH, which is the point of moving
//! them: `the_outcome_entries_follow_the_switch` is the control for a SWITCHED run.
//! `common::load_outcome_files` made to name `LoadRecipe::OneShot` instead of reading
//! the switch: it FAILS under `ANTHILL_TEST_TWO_STEP_LOAD=1`, and passes without the
//! variable BY DESIGN — an ordinary gate has no switch to ignore.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use anthill_core::kb::load::LoadError;

/// The ways out of the recipe the guard recognises.
const WAYS_OUT: &[&str] = &[
    "stdlib_parsed(",
    "stdlib_dir(",
    "rust_stl_dir(",
    "LoadRecipe::OneShot",
    "LoadRecipe::TwoStep",
    "present_all_again(",
    "load_stdlib_kb_with_source(",
    "load_stdlib_kb_untyped(",
];

/// Every file that makes a stdlib load of its own, or names its recipe: its path relative
/// to `anthill-core/tests`, HOW MANY of its lines name a way out, and WHY. The reason is
/// also at the site.
const PINNED: &[(&str, usize, &str)] = &[
    (
        "include/induction_axiom_witness_test.rs",
        1,
        "presents every loaded file to the KB again: a registration is not made twice",
    ),
    (
        "include/scope_axiom_witness_test.rs",
        1,
        "presents every loaded file to the KB again: a registration is not made twice",
    ),
    (
        "include/specialization_witness_test.rs",
        1,
        "presents every loaded file to the KB again: a record is not emitted twice",
    ),
    (
        "include/incremental_load_test.rs",
        2,
        "compares a one-shot load with a two-step one: both recipes, by name",
    ),
    (
        "include/parse_test.rs",
        1,
        "parses every file under `stdlib/anthill/` and loads none of them",
    ),
    (
        "include/wi1049_duplicate_operation_declaration_test.rs",
        1,
        "presents every loaded file to the KB again: a re-load is not a redeclaration",
    ),
    (
        "include/wi1114_item_per_file_store_test.rs",
        1,
        "seeds a store from `load_all_per_file`'s per-FILE results, which the recipe merges",
    ),
    (
        "include/wi228_tree_threaded_dispatch_test.rs",
        1,
        "supplies an `eq` for the stdlib's `List`, which only the stdlib's own load may do",
    ),
    (
        "include/wi718_prelude_ctor_preregistration_test.rs",
        1,
        "orders the project file BEFORE the stdlib in one call",
    ),
    (
        "include/wi732_project_ctor_test.rs",
        1,
        "re-types the user file by hand, from that file's own `LoadResult`",
    ),
    (
        "include/wi931_free_standing_provider_backing_test.rs",
        1,
        "loads `stdlib/anthill/` WITHOUT its binding layer, which is refused",
    ),
    (
        "include/wi946_belongs_to_readers_test.rs",
        6,
        "drives the typer by hand over a load that stops before it",
    ),
    (
        "include/wi_acg10_census_test.rs",
        2,
        "a census by source PATH, the stdlib's own among them; the recipe's stdlib has none",
    ),
    (
        "include/wi_brt4y_host_implemented_test.rs",
        1,
        "loads `stdlib/anthill/` WITHOUT its binding layer, which is refused",
    ),
    (
        "include/wi_ej5f5_bare_ctor_pattern_test.rs",
        1,
        "drives the typer by hand over a load that stops before it",
    ),
    (
        "include/wi_szkv7_clause_frontier_test.rs",
        6,
        "what a LATER load checks: each fixture is run under both recipes, by name",
    ),
    (
        "include/wi_szkv7_later_equality_test.rs",
        7,
        "what a LATER load may change: each fixture is run under both recipes, by name",
    ),
    (
        "include/wi_szkv7_two_step_load_test.rs",
        3,
        "the control of the switch itself",
    ),
    (
        "include/wi_v25n3_written_row_label_test.rs",
        5,
        "which BATCH judges a clause: the batches are made call by call",
    ),
];

/// This file, skipped because it carries the recognised spellings as STRING LITERALS.
const SELF: &str = "include/wi_rah0z_one_recipe_test.rs";

fn names_a_way_out(line: &str) -> bool {
    let t = line.trim_start();
    // A comment quoting a spelling is not a use of it.
    !t.starts_with("//") && WAYS_OUT.iter().any(|w| t.contains(w))
}

fn rust_sources(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = std::fs::read_dir(dir).unwrap_or_else(|e| panic!("read {}: {e}", dir.display()));
    for entry in entries {
        let path = entry.expect("directory entry").path();
        if path.is_dir() {
            rust_sources(&path, out);
        } else if path.extension().is_some_and(|x| x == "rs") {
            out.push(path);
        }
    }
}

/// How many lines of each file outside `common/` name a way out — files that name none
/// are absent. Paths relative to `anthill-core/tests`.
fn lines_naming_a_way_out() -> BTreeMap<String, usize> {
    let tests = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests");
    let mut sources = Vec::new();
    rust_sources(&tests, &mut sources);
    assert!(
        sources.len() > 500,
        "the scan found {} Rust sources under {} — it is looking in the wrong place",
        sources.len(),
        tests.display()
    );
    sources
        .iter()
        .filter_map(|path| {
            let rel = path
                .strip_prefix(&tests)
                .expect("under tests/")
                .to_string_lossy()
                .replace('\\', "/");
            if rel.starts_with("common/") || rel == SELF {
                return None;
            }
            let text = std::fs::read_to_string(path)
                .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
            let lines = text.lines().filter(|l| names_a_way_out(l)).count();
            (lines > 0).then_some((rel, lines))
        })
        .collect()
}

#[test]
fn every_way_out_of_the_recipe_is_pinned_by_name() {
    let found = lines_naming_a_way_out();
    let pinned: BTreeMap<String, usize> = PINNED
        .iter()
        .map(|(file, lines, _)| (file.to_string(), *lines))
        .collect();
    assert_eq!(pinned.len(), PINNED.len(), "a file is listed twice");
    for (file, _, reason) in PINNED {
        assert!(!reason.trim().is_empty(), "`{file}` is listed without a reason");
    }

    let unlisted: Vec<&String> = found.keys().filter(|f| !pinned.contains_key(*f)).collect();
    assert!(
        unlisted.is_empty(),
        "these files make a stdlib load of their own, or name a load recipe, and are not \
         listed in `PINNED`: {unlisted:#?}\n\
         Load through a `tests/common` helper instead (`load_kb_with`, `load_outcome`, \
         `load_stdlib_kb` — rustland/CLAUDE.md, \"Test Patterns\"). If the SHAPE of the \
         load is the test's subject, say why at the site and add the file here."
    );

    let stale: Vec<&String> = pinned.keys().filter(|f| !found.contains_key(*f)).collect();
    assert!(
        stale.is_empty(),
        "these files are listed in `PINNED` and no longer name a way out of the recipe; \
         remove the entries: {stale:#?}"
    );

    let recounted: Vec<String> = pinned
        .iter()
        .filter(|(file, lines)| found[*file] != **lines)
        .map(|(file, lines)| format!("{file}: listed with {lines}, has {}", found[file]))
        .collect();
    assert!(
        recounted.is_empty(),
        "the number of lines that name a way out of the recipe changed in a listed file: \
         {recounted:#?}\n\
         A NEW one needs the reason the entry gives to cover it too — say so at its site \
         and correct the count; a removed one only needs the count."
    );
}

/// The recogniser, against the shapes it must and must not take — without this row a
/// recogniser that matched nothing would make the scan above pass over any tree.
#[test]
fn the_recogniser_fires_on_a_use_and_not_on_prose() {
    for line in [
        "    let mut refs = crate::common::stdlib_parsed();",
        "    let files = collect_anthill_files(&stdlib_dir());",
        "        LoadRecipe::OneShot,",
        "    let kb_b = load_by(crate::common::LoadRecipe::TwoStep);",
        "    expect_loaded(crate::common::present_all_again(&mut kb, &[src]));",
        "    let (mut kb, result) = load_stdlib_kb_with_source(source);",
    ] {
        assert!(names_a_way_out(line), "must be recognised: {line}");
    }
    for line in [
        "    // `stdlib_dir()` alone would have left more than half the corpus unread",
        "/// PINNED to [`LoadRecipe::TwoStep`] by name",
        "    let kb = crate::common::load_stdlib_kb();",
        "    let (kb, errs) = crate::common::load_outcome(extra).kb_and_errors();",
        "    expect_loaded(load_in_a_later_call(&mut kb, EQ, LoadOptions::default()));",
    ] {
        assert!(!names_a_way_out(line), "must NOT be recognised: {line}");
    }
}

/// A program whose VERDICT depends on the recipe, by the language's own rule
/// (kernel-language.md §8.3): `EqList` supplies an `eq` for the stdlib's `List`, and a
/// composite's equality is closed by the load that defines it. In the stdlib's load it
/// is the supplier; in a later one it is `EqualityOfEarlierSort`.
const AN_EQ_FOR_THE_STDLIBS_LIST: &str = r#"
namespace test.rah0z.eqlist
  import anthill.prelude.{Eq, PartialEq, List, Bool}
  sort EqList
    sort A = ?
    requires Eq[T = A]
    provides PartialEq[T = List[T = A]]
    provides Eq[T = List[T = A]]
    operation eq(x: List[T = A], y: List[T = A]) -> Bool = true
  end
end
"#;

#[test]
fn the_outcome_entries_follow_the_switch() {
    // Read HERE and spelled out, as `wi_szkv7_two_step_load_test`'s control does and for
    // its reason: the row is a control on the read of the switch, so it cannot take
    // that read's word.
    let switched = std::env::var("ANTHILL_TEST_TWO_STEP_LOAD").is_ok_and(|v| v == "1");

    let errors = crate::common::load_outcome(AN_EQ_FOR_THE_STDLIBS_LIST).errors();
    let refused_as_a_later_load = errors
        .iter()
        .any(|e| matches!(e.peel(), LoadError::EqualityOfEarlierSort { .. }));
    let rendered = crate::common::rendered_load_errors(errors);

    if switched {
        assert!(
            refused_as_a_later_load,
            "under the switch `load_outcome` hands the user's file to a LATER load, which \
             may not supply an `eq` for the stdlib's `List`; got: {rendered:#?}"
        );
    } else {
        assert!(
            rendered.is_empty(),
            "one-shot, the fixture is in the stdlib's own load and loads clean; got: \
             {rendered:#?}"
        );
    }
}
