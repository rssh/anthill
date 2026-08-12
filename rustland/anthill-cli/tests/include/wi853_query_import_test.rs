//! WI-853 — `anthill query -i/--import <name>` supplies a name to the query's scope.
//!
//! The flag was NON-FUNCTIONAL by construction: it synthesized a `import <name>`
//! line and prepended it to the query text, but `import` was admitted only inside
//! a `namespace` / `sort` body, so the source could never parse and EVERY `-i` run
//! failed. It went unnoticed because the resulting diagnostic named neither the
//! flag nor the file and read as a fault in the user's pattern.
//!
//! Fixed in the GRAMMAR, not the CLI: a file's top level IS a scope — the
//! `_global` one every top-level `sort` / `fact` / `rule` is defined in — and
//! `import` is how names enter a scope, so admitting the declarations but not the
//! import that feeds them was an asymmetry with no rule behind it. The flag then
//! needs no wrapper: it is one ordinary top-level import, parsed as its own
//! source and scanned into `_global`, which is exactly the scope
//! `convert_query_term` resolves the pattern in.
//!
//! Every test here pins a BEHAVIOUR the flag was supposed to have, against a
//! control that fails without the flag — a non-zero solution count alone would
//! pass on a query that resolves for unrelated reasons.

use crate::common::{anthill, fixtures_dir, Output};
use std::path::PathBuf;

fn fixture(name: &str) -> PathBuf {
    fixtures_dir("wi853").join(name)
}

fn query(args: &[&str]) -> Output {
    let kb = fixture("kb.anthill");
    let mut all = vec!["query", "--path", kb.to_str().unwrap()];
    all.extend_from_slice(args);
    anthill(&all)
}

/// THE acceptance case. `mk` lives in `wi853.kb`, so the pattern resolves ONLY
/// because the flag brings it into scope: the same query without the flag is the
/// control, and it does not resolve.
#[test]
fn an_import_flag_puts_the_name_in_query_scope() {
    // Without the import, `mk` resolves to no known functor at `_global`. Since
    // WI-754 that is REFUSED loudly rather than answered as a silent empty set —
    // a stronger control than the old "no solutions" (exit 0): the import is what
    // makes the name exist at all in the query's scope, so its absence is a fault,
    // not an empty answer.
    let without = query(&["mk(x: ?v)"]);
    assert_eq!(
        without.code, 1,
        "control: with no import `mk` resolves nowhere and must be refused; \
         stdout:\n{}\nstderr:\n{}",
        without.stdout, without.stderr
    );
    assert!(
        without.has_diagnostic("error:", "'mk'"),
        "the refusal must name the unresolvable functor; stderr:\n{}",
        without.stderr
    );
    assert!(
        !without.stdout.contains("no solutions"),
        "a refused query must not also print an empty answer; stdout:\n{}",
        without.stdout
    );

    // WI-1089: the WILDCARD form. `-i wi853.kb` binds the namespace name
    // `kb` — an invocation import reads exactly as the same line in source — and
    // what this test needs in scope is a name the namespace CONTAINS.
    let with = query(&["-i", "wi853.kb.*", "mk(x: ?v)"]);
    assert_eq!(
        with.code, 0,
        "the query must succeed; stderr:\n{}",
        with.stderr
    );
    assert!(
        with.has_stdout_line("?v = 7"),
        "expected the imported `mk` to match the KB's fact; stdout:\n{}\nstderr:\n{}",
        with.stdout,
        with.stderr
    );
    assert!(
        with.has_stdout_line("1 solution(s)"),
        "stdout:\n{}",
        with.stdout
    );
}

/// The other input path: a `--query-file` reads its patterns from a file, and the
/// flag has to reach them too. It is the path where the old join did the most
/// damage — the file's text was the second half of a source that could not parse.
#[test]
fn an_import_flag_reaches_a_query_file() {
    let q = fixture("query.anthill");
    let with = query(&["-i", "wi853.kb.*", "--query-file", q.to_str().unwrap()]);
    assert_eq!(
        with.code, 0,
        "the query must succeed; stderr:\n{}",
        with.stderr
    );
    assert!(
        with.has_stdout_line("?v = 7"),
        "expected the imported `mk` to match; stdout:\n{}\nstderr:\n{}",
        with.stdout,
        with.stderr
    );
}

/// A name that resolves nowhere is a blocking fault of the FLAG, and the
/// diagnostic says so — the flag is the whole of its origin, so it is named.
#[test]
fn an_unresolvable_import_flag_blocks() {
    let out = query(&["-i", "nosuch.ns", "mk(x: ?v)"]);
    assert_eq!(
        out.code, 1,
        "an import that resolves nowhere must block; stdout:\n{}",
        out.stdout
    );
    assert!(
        out.diagnostics("error:")
            .any(|l| l.starts_with("error: --import `nosuch.ns`: ")
                && l.contains("unresolved import 'nosuch.ns'")),
        "expected the fault blamed on the flag it came from; stderr:\n{}",
        out.stderr
    );
}

/// Each flag is parsed as its OWN source, so a fault in one can never be
/// attributed to another. Under the old join tree-sitter's recovery merged
/// several `import` lines into a single ERROR node, and WI-852 had to name a
/// RANGE of flags ("one of `a`, `b`") because the span could not tell them apart.
/// One source per flag makes the range unnecessary: the good flag is not blamed.
#[test]
fn a_malformed_flag_names_only_itself() {
    let out = query(&["-i", "wi853.kb", "-i", "not a name!!", "mk(x: ?v)"]);
    assert_eq!(
        out.code, 1,
        "a malformed flag must block; stdout:\n{}",
        out.stdout
    );

    let errs: Vec<&str> = out.diagnostics("error:").collect();
    assert!(
        !errs.is_empty(),
        "expected a diagnostic; stderr:\n{}",
        out.stderr
    );
    assert!(
        errs.iter()
            .all(|l| l.starts_with("error: --import `not a name!!`: ")),
        "every diagnostic must name the flag at fault, and only it; stderr:\n{}",
        out.stderr
    );
}

/// Flags are independent arguments, so a fault in one does not suppress the
/// report on the next — fixing typos one CLI run at a time is what stopping at
/// the first would cost.
#[test]
fn every_malformed_flag_is_reported() {
    let out = query(&["-i", "not a name!!", "-i", "nosuch.ns", "mk(x: ?v)"]);
    assert_eq!(
        out.code, 1,
        "a malformed flag must block; stdout:\n{}",
        out.stdout
    );

    let errs: Vec<&str> = out.diagnostics("error:").collect();
    assert!(
        errs.iter()
            .any(|l| l.starts_with("error: --import `not a name!!`: ")),
        "the first flag's fault must be reported; stderr:\n{}",
        out.stderr
    );
    assert!(
        errs.iter()
            .any(|l| l.starts_with("error: --import `nosuch.ns`: ")),
        "the second flag's fault must be reported too; stderr:\n{}",
        out.stderr
    );
}

// DELETED (WI-921): `an_import_flag_is_refused_where_it_cannot_apply`. It drove the
// rule on `--mode sort`, whose argument was a raw clause-kind tag no import could bear
// on; the mode is gone, so the assertion cannot fail — and an assertion that cannot
// fail is not a pin. The rule itself still has pins, on the flags that DO have inert
// positions (`--match` / `--resolve` / `--max-depth` under a listing mode, wi767).
//
// NOT vacuous in general, and the diff that removed this test first claimed it was:
// `--mode domain _global` still reads its argument as a raw intern rather than through
// the ladder, so `-i` is inert for that one spelling — and, unlike `--mode sort`, it is
// silently ACCEPTED there rather than refused. WI-923 owns it.

/// WI-853's first fallout. The query file's `ParsedFile` is now stamped with the
/// path it was read from, which the old join made impossible: with the `-i` lines
/// sharing the file's source, a path stamp would have attributed a FLAG's fault to
/// the file, so the two load printers here named no file at all. The source now IS
/// the file, so the stamp is correct unconditionally — with flags or without.
#[test]
fn a_query_file_load_error_names_the_file() {
    let q = fixture("bad-import-query.anthill");
    for flags in [vec![], vec!["-i", "wi853.kb"]] {
        let mut args = flags.clone();
        args.extend_from_slice(&["--query-file", q.to_str().unwrap()]);
        let out = query(&args);

        assert_eq!(
            out.code, 1,
            "the unresolved import must block; stderr:\n{}",
            out.stderr
        );
        // Line 3, column 8: `nosuch.ns` in `import nosuch.ns`, after two comment
        // lines — the same position with `-i` as without, since nothing is
        // prepended to the file any more.
        let expected = format!("error: {}:3:8: ", q.display());
        assert!(
            out.diagnostics("error:")
                .any(|l| l.starts_with(&expected) && l.contains("unresolved import 'nosuch.ns'")),
            "a load error from the query file must name the file and where in it \
             (flags: {flags:?}); stderr:\n{}",
            out.stderr
        );
    }
}
