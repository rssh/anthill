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
    assert!(out.stderr.contains("error: unresolved name 'NoSuchSortXyz'"),
            "expected a loud `error:`; got:\n{}", out.stderr);
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
    assert!(out.stderr.contains("error: operation 'my.app.Lib.f'"),
            "expected a loud `error:` naming the guard; got:\n{}", out.stderr);
    // The positive assert is anchored on the CLI's own `error: ` prefix, not a
    // bare `contains("error:")`: `Other` used to render its message as "load
    // error: …", so a substring test matched its own text and passed even under
    // `warning:` — vacuous against the very regression this pins.
    //
    // The negative is line-wise and names the guard, so it cannot be satisfied
    // by the incidental absence of unrelated advisories on this stderr.
    assert!(!out.stderr.lines().any(|l| l.starts_with("warning:") && l.contains("my.app.Lib.f")),
            "the guard must not be demoted to a warning:\n{}", out.stderr);
}

/// The third promoted variant. An ambiguous name used to demote to `warning:`
/// and run — silently picking a referent the user never chose.
///
/// Known gap (pre-existing, surfaced by the promotion): the span reads `0..0`
/// because two of the three producers push `Span::default()`
/// (`remap_name_str_inner`, `remap_symbol_strict` — neither takes a span). The
/// candidate list is what makes it locatable today, so that is what this pins.
#[test]
fn ambiguous_symbol_blocks_the_run() {
    let path = fixtures_dir().join("ambiguous-symbol.anthill");
    let out = run_with(&[path.to_str().unwrap()]);
    assert_eq!(out.code, 2, "an ambiguous symbol must block the run; stderr:\n{}", out.stderr);
    assert_eq!(out.stdout, "", "the program must NOT run; it printed to stdout");
    assert!(out.stderr.contains("error: ambiguous symbol 'widget'"),
            "expected a loud `error:`; got:\n{}", out.stderr);
    assert!(out.stderr.contains("lib.one.Thing.widget")
            && out.stderr.contains("lib.two.Gadget.widget"),
            "the diagnostic must name both candidates; got:\n{}", out.stderr);
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
