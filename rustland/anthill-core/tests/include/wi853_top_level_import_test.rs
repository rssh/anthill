//! WI-853 — `import` is admitted at a file's TOP LEVEL, not only inside a
//! `namespace` / `sort` body.
//!
//! A file's top level IS a scope: `_declaration` (grammar.js) admits `sort`,
//! `fact`, `rule`, `operation` … outside any namespace, and the loader defines
//! every one of them in `_global`. `import` is how names enter a scope, so
//! admitting the declarations while refusing the import that feeds them was an
//! asymmetry with no rule behind it — a top-level `sort S` could be written but
//! nothing it referenced could be brought into view except by writing every name
//! out in full.
//!
//! It is what made `anthill query -i <name>` work (its own tests live in
//! `anthill-cli/tests/wi853_query_import_test.rs`): the flag has no namespace to
//! sit in, and the scope its import must enter is `_global`, the one the query
//! pattern is resolved in.
//!
//! SCOPE OF THE IMPORT, stated because it is not the file-local import other
//! languages have and the difference is observable: a top-level import enters
//! `_global`, so it is visible from every scope that chains up to `_global` — in
//! any file of the same load, not only the one that wrote it
//! (`a_top_level_import_enters_the_shared_global_scope` drives exactly that).
//! That is the SAME rule top-level DEFINITIONS already follow: a top-level `sort
//! S` is equally visible KB-wide. The language has no per-file scope to attach a
//! narrower one to; `_global` is the top.

use crate::common::try_load_kb_with_files;

/// A namespace to import FROM. `S` is reachable by its short name only through
/// an import — `use_s` below names it bare.
const LIB: &str = "\
namespace wi853.lib
  sort S
    entity mk(x: Int64)
  end
end
";

fn assert_loads(sources: &[&str], why: &str) {
    if let Err(errs) = try_load_kb_with_files(sources) {
        panic!("{why}; load failed with: {errs:?}");
    }
}

fn assert_unresolved(sources: &[&str], name: &str, why: &str) {
    match try_load_kb_with_files(sources) {
        Ok(_) => panic!("must NOT load: {why}"),
        Err(errs) => assert!(
            errs.iter()
                .any(|e| e.contains(&format!("unresolved name '{name}'"))),
            "{why}; expected `{name}` to be unresolved, got: {errs:?}",
        ),
    }
}

/// The claim, with its control. `S` is written bare in a top-level operation
/// signature: it resolves with the import above it and does not without, so the
/// import is what carries it — not some other route to the name.
#[test]
fn a_top_level_import_brings_a_name_into_the_top_level_scope() {
    assert_unresolved(
        &[LIB, "operation use_s(s: S) -> Int64\n"],
        "S",
        "the control: without an import, a bare `S` at the top level names nothing",
    );
    assert_loads(
        &[LIB, "import wi853.lib\n\noperation use_s(s: S) -> Int64\n"],
        "a top-level import must make `wi853.lib`'s contents resolvable at the top level",
    );
}

/// All three import forms reach the top level, because it is the SAME
/// `import_clause` a namespace body takes — one grammar rule, admitted in one
/// more place, not a second spelling that could accept a different language.
#[test]
fn every_import_form_is_admitted_at_the_top_level() {
    for form in [
        "import wi853.lib\n",
        "import wi853.lib.{S}\n",
        "import wi853.lib.*\n",
    ] {
        assert_loads(
            &[LIB, &format!("{form}\noperation use_s(s: S) -> Int64\n")],
            &format!("`{}` must be admitted at the top level", form.trim()),
        );
    }
}

/// The scope semantics, driven rather than asserted in prose: the import is
/// written in one file and the name is used inside a NAMESPACE in another. It
/// resolves — `_global` is a shared scope and every namespace chains up to it.
///
/// Pinned deliberately. It is the one way a top-level import differs from the
/// file-local import of most languages, and a reader who assumed file locality
/// would write code that only works by accident.
#[test]
fn a_top_level_import_enters_the_shared_global_scope() {
    let other = "\
namespace wi853.other
  operation use_s(s: S) -> Int64
end
";
    assert_unresolved(
        &[LIB, other],
        "S",
        "the control: `S` is not in scope inside `wi853.other` on its own",
    );
    assert_loads(
        &[LIB, "import wi853.lib\n", other],
        "an import into `_global` must be visible from a namespace in another file, \
         the same way a top-level DEFINITION is",
    );
}

/// A top-level import lands in `ParsedFile::imports`, NOT in `items`.
///
/// The distinction is load-bearing rather than cosmetic: `scan_definitions`
/// takes a scope's imports as a separate list (`process_imports`), and every
/// consumer that walks `items` — the loader's four passes, codegen, the fact-span
/// collector — matches on `Item` variants. An import smuggled in as an `Item`
/// variant would be silently dropped by all of them.
#[test]
fn a_top_level_import_is_not_an_item() {
    let parsed = anthill_core::parse::parse("import wi853.lib\n\nfact mk(x: 1)\n")
        .expect("a top-level import must parse");
    assert_eq!(
        parsed.imports.len(),
        1,
        "the import must be collected as an import"
    );
    assert_eq!(
        parsed.items.len(),
        1,
        "only the fact is an item; got {:?}",
        parsed.items
    );
}
