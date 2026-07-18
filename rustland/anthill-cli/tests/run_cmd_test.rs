//! Acceptance tests for `anthill run` (WI-051, proposal 028).
//! Invokes the built binary against fixture programs and asserts on
//! stdout, stderr, and exit code.

mod common;

use common::{anthill, Output};

fn fixtures_dir() -> std::path::PathBuf {
    common::fixtures_dir("run")
}

fn run_with(args: &[&str]) -> Output {
    let mut full = vec!["run"];
    full.extend_from_slice(args);
    anthill(&full)
}

#[test]
fn hello_program_prints_and_exits_zero() {
    let path = fixtures_dir().join("hello.anthill");
    let out = run_with(&[path.to_str().unwrap()]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert_eq!(out.stdout, "hello, world\n");
}

#[test]
fn no_main_fails_with_exit_2() {
    let path = fixtures_dir().join("no-main.anthill");
    let out = run_with(&[path.to_str().unwrap()]);
    assert_eq!(out.code, 2);
    assert!(out.stderr.contains("no program entry found"),
            "stderr did not mention missing entry:\n{}", out.stderr);
}

#[test]
fn ambiguous_entries_list_candidates_and_exit_2() {
    let path = fixtures_dir().join("two-mains.anthill");
    let out = run_with(&[path.to_str().unwrap()]);
    assert_eq!(out.code, 2);
    assert!(out.stderr.contains("ambiguous program entry"),
            "stderr missing ambiguity banner:\n{}", out.stderr);
    assert!(out.stderr.contains("my.two.One"),
            "stderr missing `my.two.One` candidate:\n{}", out.stderr);
    assert!(out.stderr.contains("my.two.Two"),
            "stderr missing `my.two.Two` candidate:\n{}", out.stderr);
}

#[test]
fn entry_flag_disambiguates() {
    let path = fixtures_dir().join("two-mains.anthill");
    let out = run_with(&["--entry", "my.two.Two", path.to_str().unwrap()]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert_eq!(out.stdout, "two\n");
}

#[test]
fn args_passed_after_double_dash() {
    let path = fixtures_dir().join("args.anthill");
    let out = run_with(&[path.to_str().unwrap(), "--", "first", "second", "third"]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert_eq!(out.stdout, "first\nsecond\nthird\n");
}

#[test]
fn main_return_value_is_exit_code() {
    let path = fixtures_dir().join("exit7.anthill");
    let out = run_with(&[path.to_str().unwrap()]);
    assert_eq!(out.code, 7, "stderr:\n{}", out.stderr);
    assert_eq!(out.stdout, "");
}

#[test]
fn eprintln_writes_to_stderr_not_stdout() {
    let path = fixtures_dir().join("eprintln.anthill");
    let out = run_with(&[path.to_str().unwrap()]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert_eq!(out.stdout, "stdout-line\n");
    assert!(out.stderr.contains("stderr-line\n"),
            "expected `stderr-line` on stderr; got:\n{}", out.stderr);
    assert!(!out.stdout.contains("stderr-line"),
            "stderr-line leaked to stdout:\n{}", out.stdout);
}

// ── WI-744: every LoadError blocks the run ──────────────────────────────

/// A load error must BLOCK — `UnresolvedName` was absent from the old
/// `is_load_blocking` allowlist, so this program printed `RAN` and exited 0 with
/// its unresolved name demoted to `warning:`.
#[test]
fn unresolved_name_blocks_the_run() {
    let path = fixtures_dir().join("unresolved-name.anthill");
    let out = run_with(&[path.to_str().unwrap()]);
    assert_eq!(out.code, 2, "an unresolved name must block the run; stderr:\n{}", out.stderr);
    assert_eq!(out.stdout, "", "the program must NOT run; it printed to stdout");
    assert!(out.stderr.contains("error:") && out.stderr.contains("unresolved name 'NoSuchSortXyz'"),
            "expected a loud `error:` for the unresolved name; got:\n{}", out.stderr);
    // WI-745: the diagnostic names the FILE and a line:col (`path:line:col: …`),
    // not a raw byte offset that identifies nothing once files merge into one KB.
    assert!(out.stderr.contains("unresolved-name.anthill:"),
            "the error must name the source file with a line:col; got:\n{}", out.stderr);
    assert!(!out.stderr.contains(" at "),
            "the raw byte-offset Display (`… at N..M`) must be retired; got:\n{}", out.stderr);
    assert!(!out.stderr.contains("warning: unresolved name"),
            "the error must not be demoted to a warning:\n{}", out.stderr);
}

/// The same for the catch-all `LoadError::Other` — the variant most
/// deliberately-loud guards raise, and the one whose demotion made the
/// allowlist's default for a NEW guard "advisory".
#[test]
fn catch_all_load_error_blocks_the_run() {
    let path = fixtures_dir().join("load-error-other.anthill");
    let out = run_with(&[path.to_str().unwrap()]);
    assert_eq!(out.code, 2, "a LoadError::Other must block the run; stderr:\n{}", out.stderr);
    assert_eq!(out.stdout, "", "the program must NOT run; it printed to stdout");
    assert!(out.stderr.lines().any(|l| l.starts_with("error:") && l.contains("operation 'my.app.Lib.f'")),
            "expected a loud `error:` naming the guard; got:\n{}", out.stderr);
    // WI-745: even a span-less `Other` names its FILE now (`path: message`), so
    // the user knows which of the merged sources raised the guard.
    assert!(out.stderr.contains("load-error-other.anthill:"),
            "the error must name the source file; got:\n{}", out.stderr);
    // The negative is line-wise and names the guard, so it cannot be satisfied
    // by the incidental absence of unrelated advisories on this stderr.
    assert!(!out.stderr.lines().any(|l| l.starts_with("warning:") && l.contains("my.app.Lib.f")),
            "the guard must not be demoted to a warning:\n{}", out.stderr);
}

/// The third promoted variant. An ambiguous name used to demote to `warning:`
/// and run — silently picking a referent the user never chose.
///
/// WI-745 closed the gap this test used to document: the span was `0..0`
/// (`remap_symbol_strict` pushed `Span::default()`) AND the error printed twice
/// (the fact functor is resolved once for owner-tracking and again for the term
/// build). It now names the FILE at a real line:col and prints exactly once.
#[test]
fn ambiguous_symbol_blocks_the_run() {
    let path = fixtures_dir().join("ambiguous-symbol.anthill");
    let out = run_with(&[path.to_str().unwrap()]);
    assert_eq!(out.code, 2, "an ambiguous symbol must block the run; stderr:\n{}", out.stderr);
    assert_eq!(out.stdout, "", "the program must NOT run; it printed to stdout");
    assert!(out.stderr.contains("error:") && out.stderr.contains("ambiguous symbol 'widget'"),
            "expected a loud `error:` for the ambiguous symbol; got:\n{}", out.stderr);
    assert!(out.stderr.contains("lib.one.Thing.widget")
            && out.stderr.contains("lib.two.Gadget.widget"),
            "the diagnostic must name both candidates; got:\n{}", out.stderr);
    // WI-745 defect 2: a real span, not `0..0` (`remap_symbol_strict` now takes one).
    assert!(out.stderr.contains("ambiguous-symbol.anthill:") && !out.stderr.contains("0..0"),
            "the error must name the file at a real line:col, not `0..0`; got:\n{}", out.stderr);
    // WI-745 defect 3: printed exactly once (the double-resolution is deduped).
    assert_eq!(out.stderr.matches("ambiguous symbol 'widget'").count(), 1,
            "the ambiguous symbol must be reported once, not per resolution; got:\n{}", out.stderr);
    assert!(!out.stderr.contains("warning: ambiguous"),
            "the error must not be demoted to a warning:\n{}", out.stderr);
}

/// The OTHER half: making every `LoadError` block must not collapse the advisory
/// channel. A genuine advisory (`LoadWarning`, the WI-346 requires-shadow) rides
/// `LoadResult.warnings` on the `Ok` path — it prints as a `warning:` and the
/// program still RUNS.
///
/// The fixture triggers its OWN advisory, so this does not depend on the
/// stdlib's incidental shadow warnings — those are a wart whose message invites
/// its own removal, and anchoring here would fail the day someone removes it.
#[test]
fn advisory_warnings_print_but_do_not_block() {
    let path = fixtures_dir().join("advisory-warning.anthill");
    let out = run_with(&[path.to_str().unwrap()]);
    assert_eq!(out.code, 0, "an advisory must not block; stderr:\n{}", out.stderr);
    assert_eq!(out.stdout, "advisory-fixture-ran\n", "the program must still run");
    assert!(out.stderr.contains("warning: operation `ping` in `my.advisory.Shadower`"),
            "expected the fixture's own advisory on stderr; got:\n{}", out.stderr);
    assert!(!out.stderr.contains("error:"),
            "an advisory must not be reported as an error:\n{}", out.stderr);
}

// ── WI-746: `anthill run` sees the project's conventional data files ──

/// `anthill run <dir>` must load `<dir>/anthill.toml`, exactly as `anthill load`
/// and `anthill query` do.
///
/// It did not. `run` assembles its own KB in `run::build_kb` rather than going
/// through `load_kb_with_stdlib`, so it never reached the data path: the same
/// project directory answered one way under `anthill query` and another under
/// `anthill run`, and a program could not see facts its own project declared.
/// Both now call the shared `load_conventional_data`.
///
/// Broken data is the probe because it is decisive about the WIRING: if `run`
/// stops reading data files, this fixture is ignored and the program runs to
/// completion, exit 0. What the facts DO once loaded is pinned once, against the
/// shared helper, by `load_cmd_test::declared_data_reaches_the_kb` — no reason to
/// rebuild `pattern_query` machinery here to re-test the same function.
#[test]
fn broken_data_blocks_the_run() {
    let path = fixtures_dir().join("with-broken-data");
    let out = run_with(&[path.to_str().unwrap()]);
    assert_eq!(out.code, 2, "broken declared data must block the run; stderr:\n{}", out.stderr);
    assert!(out.stdout.is_empty(),
            "the program must not run; got stdout:\n{}", out.stdout);
    assert!(out.has_diagnostic("error:", "anthill.toml")
            && out.stderr.contains("unknown entity"),
            "expected a loud `error:` naming the data file and the fault; got:\n{}", out.stderr);
}

/// The control, and the guard against the opposite regression: wiring data into
/// `run` must not break runs that HAVE valid data. Without this, deleting the
/// data load entirely would still pass `broken_data_blocks_the_run`'s sibling
/// only by accident.
#[test]
fn valid_data_does_not_disturb_the_run() {
    let path = fixtures_dir().join("with-data");
    let out = run_with(&[path.to_str().unwrap()]);
    assert_eq!(out.code, 0, "valid data must not block the run; stderr:\n{}", out.stderr);
    assert_eq!(out.stdout, "ran\n");
    assert!(!out.has_diagnostic("error:", "anthill.toml"),
            "valid data must not produce an error:\n{}", out.stderr);
}
