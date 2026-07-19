//! WI-744 — `anthill query` blocks on a load error in the query source.
//!
//! `collect_queries` scans the query snippet with `load::scan_definitions` (which
//! returns `Vec<LoadError>`) and used to print every one as `warning:` and run the
//! query regardless. That is a DISTINCT demotion from the `is_load_blocking`
//! allowlist — it printed all of them unconditionally, not via the allowlist — so
//! it is its own behavior change and earns its own test.
//!
//! It matters because an unresolved import leaves the pattern's short names to
//! resolve by accidental scope walk or not at all: the user gets a confident
//! wrong answer, or a silent `no solutions`, in place of a diagnostic.

mod common;

use common::{anthill, fixtures_dir};

fn q(args: &[&str]) -> common::Output {
    let dir = fixtures_dir("query");
    let facts = dir.join("facts.anthill");
    let mut full = vec!["query", "-p", facts.to_str().unwrap()];
    full.extend_from_slice(args);
    anthill(&full)
}

/// The control: a well-formed query file scans clean and answers. Pins that the
/// block is attributable to the bad import and not to the query path itself —
/// and that `scan_definitions` reports nothing for a legitimate snippet, which is
/// the false-positive risk of making it blocking.
#[test]
fn a_well_formed_query_file_answers() {
    let dir = fixtures_dir("query");
    let path = dir.join("good-query.anthill");
    let out = q(&["--query-file", path.to_str().unwrap()]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert!(out.has_stdout_line("2 solution(s)"),
            "expected both facts; got stdout:\n{}", out.stdout);
}

/// A bare `--pattern` has no imports at all: it must scan clean and answer. The
/// query snippet is scanned as a standalone source against a KB whose names it
/// never imports, so this is where a blocking `scan_definitions` would
/// false-positive if it ever reported a benign diagnostic.
#[test]
fn a_bare_pattern_answers() {
    let out = q(&["probe.db.Person.mk(name: ?n, age: ?a)"]);
    assert_eq!(out.code, 0, "a plain pattern must not trip the scan; stderr:\n{}", out.stderr);
    assert!(out.has_stdout_line("2 solution(s)"),
            "expected both facts; got stdout:\n{}", out.stdout);
}

/// An unresolved import in the query source must BLOCK. Before WI-744 this
/// printed `warning: unresolved import 'no.such.module.Nope'` and then answered
/// anyway, exit 0.
#[test]
fn unresolved_import_in_a_query_blocks() {
    let dir = fixtures_dir("query");
    let path = dir.join("bad-import-query.anthill");
    let out = q(&["--query-file", path.to_str().unwrap()]);
    assert_eq!(out.code, 1, "a load error in the query must block; stderr:\n{}", out.stderr);
    // "no solutions" included: the resolve path's EMPTY answer has no count
    // line, so a blocked-but-ran query would slip past the count checks alone.
    assert!(!out.stdout.contains("solution(s)") && !out.stdout.contains("result(s)")
                && !out.stdout.contains("no solutions"),
            "the query must not answer; got stdout:\n{}", out.stdout);
    assert!(out.has_diagnostic("error:", "no.such.module.Nope"),
            "expected a loud `error:` naming the import; got stderr:\n{}", out.stderr);
    assert!(!out.has_diagnostic("warning:", "no.such.module.Nope"),
            "the import must not be demoted to a warning:\n{}", out.stderr);
}
