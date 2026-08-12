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
//! SCOPE OF THE IMPORT — REVISED BY WI-995, and stated at length because this file
//! used to teach the opposite. A top-level import enters `_global`, but it is spent in
//! the FILE that lists it: another file's text does not see it
//! (`a_top_level_import_does_not_escape_the_file_that_wrote_it` drives exactly that).
//!
//! WI-853 originally reasoned that a top-level import must follow the same rule as a
//! top-level DEFINITION — visible KB-wide — because "the language has no per-file scope
//! to attach a narrower one to; `_global` is the top". WI-995 supplied the missing
//! scope: every import records the file that wrote it, so "local to its file" is now
//! expressible at any address, `_global` included. The two halves have parted company
//! deliberately: a top-level `sort S` is still KB-wide, an `import` is not, because a
//! definition ADDS a name to the program while an import only chooses what one file's
//! text may call it.
//!
//! `anthill query -i <name>` is unaffected: a flag belongs to the INVOCATION, not to any
//! file (`load::ImportAttribution::Invocation`), so it reaches the query it was passed
//! for. That is the channel a file-less asker uses.

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
        &[LIB, "import wi853.lib.S\n\noperation use_s(s: S) -> Int64\n"],
        "a top-level import must bind its name at the top level",
    );
}

/// WI-1089, and the reason the test above imports `wi853.lib.S` rather than
/// `wi853.lib`: an import binds THE NAME IT WRITES. `import wi853.lib` puts `lib`
/// in scope, not `lib`'s contents — the same line means the same thing in Scala,
/// Java and Rust, and §8.6's own lead sentence says so ("does not by itself add a
/// sort's contents"). The two ways to reach inside are both driven below.
#[test]
fn importing_a_namespace_binds_the_namespace_name_not_its_contents() {
    assert_unresolved(
        &[LIB, "import wi853.lib\n\noperation use_s(s: S) -> Int64\n"],
        "S",
        "`import wi853.lib` binds `lib`; a bare `S` is not in scope through it",
    );
    assert_loads(
        &[LIB, "import wi853.lib.*\n\noperation use_s(s: S) -> Int64\n"],
        "the wildcard form is how a scope's contents come in",
    );
    assert_loads(
        &[LIB, "import wi853.lib\n\noperation use_s(s: lib.S) -> Int64\n"],
        "and the bound name qualifies the path to what it contains",
    );
}

/// All three import forms reach the top level, because it is the SAME
/// `import_clause` a namespace body takes — one grammar rule, admitted in one
/// more place, not a second spelling that could accept a different language.
#[test]
fn every_import_form_is_admitted_at_the_top_level() {
    // WI-1089: each form spelled so that it BINDS `S`, since that is what `use_s`
    // reads — the plain form binds the name it writes, so here it writes `S`.
    for form in [
        "import wi853.lib.S\n",
        "import wi853.lib.{S}\n",
        "import wi853.lib.*\n",
    ] {
        assert_loads(
            &[LIB, &format!("{form}\noperation use_s(s: S) -> Int64\n")],
            &format!("`{}` must be admitted at the top level", form.trim()),
        );
    }
}

/// The scope semantics, driven rather than asserted in prose — and INVERTED by WI-995.
///
/// The import is written in one file and the name used inside a namespace in ANOTHER.
/// It does not resolve: an import is spent in the file that lists it. `_global` is still
/// a shared scope for DEFINITIONS — a top-level `sort S` in one file is visible KB-wide,
/// as the second half here drives — but an import is not a definition, and sharing it
/// was the whole-program non-locality WI-995 removed: a file could silently change what
/// a bare name meant in a file it had never seen.
///
/// This test used to assert the opposite, and this suite's header used to teach it as a
/// deliberate difference from "the file-local import of most languages". Both were
/// rewritten with the rule rather than deleted, because the SHAPE they pin is what
/// changed and a reader arriving from WI-853 needs to see which way it went.
#[test]
fn a_top_level_import_does_not_escape_the_file_that_wrote_it() {
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
    assert_unresolved(
        &[LIB, "import wi853.lib\n", other],
        "S",
        "and a THIRD file's top-level import does not put it in scope either — an \
         import resolves only in the file that lists it (WI-995)",
    );
    // The half that did NOT change: a top-level DEFINITION is still KB-wide, so the
    // refusal above is about imports specifically and not about `_global` going private.
    assert_loads(
        &[
            "sort SGlobal853\n  entity mk(x: Int64)\nend\n",
            "namespace wi853.def_user\n  operation use_g(s: SGlobal853) -> Int64\nend\n",
        ],
        "a top-level DEFINITION is still visible from another file's namespace",
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
