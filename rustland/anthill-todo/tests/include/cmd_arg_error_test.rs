//! The four SUBCOMMAND-LEVEL argument errors, driven end to end through the real
//! binary.
//!
//! Until this change all four `ParseError` variants below collapsed into a single
//! `case parse_err(_) -> eprintln("anthill-todo: argument error")` arm in
//! `anthill/main.anthill`. That line named neither the offending token nor the
//! command it was given to, so `list -unblocked` — one dash, which
//! `anthill.cli.parse.parse_args` never treats as a flag at all and hands to
//! `consume_positional`, which refuses it because `list` declares no positionals —
//! read exactly like a missing `-d`. Meanwhile every `ParamSpec` in the registry
//! carried a `description:` string that nothing ever printed.
//!
//! CONTROL. Restore that collapsed arm and EVERY assertion in the first five tests
//! fails: the stderr is then the fixed string `anthill-todo: argument error`, which
//! contains no token, no command name, and no `--flag`. Narrower back-outs, each of
//! which fails exactly one test and leaves the others green:
//!   * drop the `spec` field from `unknown_flag`/`unexpected_argument` (stdlib
//!     `cli/parse.anthill`) — nothing can render a usage block, so the `--status`
//!     description assertions go;
//!   * make `single_dash_flag` return `some(name)` for any `-`-prefixed token
//!     instead of consulting `find_param` — `single_dash_token_that_names_nothing_
//!     gets_no_suggestion` fails while `single_dash_flag_is_named_with_its_two_dash_
//!     form` still passes, which is why both are here;
//!   * make `dashed_param_named` skip the `dash_spelled` test and answer for any
//!     declared name — `a_single_dash_token_naming_a_positional_is_not_advised_to_
//!     grow_a_dash` fails ALONE, the other two arms of that predicate staying green.
//!     The three tests are one fixture per `ParamKind` outcome for that reason: a
//!     fixture of flags alone cannot tell the two questions apart.
//! `happy_path_flags_still_parse` passes either way BY DESIGN: it is the witness
//! that the diagnostics were not bought by breaking the parse they report on.

use std::process::Command;

use crate::common::setup_project;

const ANTHILL_TODO_BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

const SINGLE_OPEN_WI: &str = "\
fact WorkItem(
  id: \"WI-001\",
  created: \"2026-01-01T00:00:00Z\",
  description: \"test item\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  last_status_change: StatusChange(status: Open()))
";

/// Run the binary against a throwaway project and return `(success, stderr, stdout)`.
/// The tempdir lives to the end of the call, which is all any assertion here needs.
fn run(args: &[&str]) -> (bool, String, String) {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, SINGLE_OPEN_WI);
    let mut argv = vec!["--anthill", "-d", proj.to_str().unwrap()];
    argv.extend_from_slice(args);
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(&argv)
        .output()
        .expect("run anthill-todo");
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
        String::from_utf8_lossy(&out.stdout).into_owned(),
    )
}

/// Every argument diagnostic names the command and prints that command's own
/// accepted flags, rendered from the `ParamSpec` list `specs()` declares — so
/// asserting the descriptions asserts the registry is the source, not prose.
fn assert_names_list_and_its_flags(stderr: &str) {
    assert!(
        stderr.contains("anthill-todo: list:"),
        "diagnostic must name the command it refused; got:\n{stderr}"
    );
    assert!(
        stderr.contains("usage: list [--status VALUE]"),
        "diagnostic must print the command's usage line; got:\n{stderr}"
    );
    for flag in ["--status", "--all", "--tag", "--unblocked", "--long"] {
        assert!(
            stderr.contains(flag),
            "usage block must list {flag}; got:\n{stderr}"
        );
    }
    assert!(
        stderr.contains("Show only unblocked items (all dependencies satisfied)"),
        "usage block must carry each ParamSpec's own description; got:\n{stderr}"
    );
}

#[test]
fn single_dash_flag_is_named_with_its_two_dash_form() {
    let (ok, stderr, _) = run(&["list", "-unblocked"]);
    assert!(!ok, "a one-dash flag must still be refused");
    assert!(
        stderr.contains("unexpected argument '-unblocked'"),
        "the offending token must appear verbatim; got:\n{stderr}"
    );
    assert!(
        stderr.contains("a flag takes two dashes: '--unblocked'"),
        "the spec knows `unblocked` is a flag, so the fix must be spelled out; got:\n{stderr}"
    );
    assert_names_list_and_its_flags(&stderr);
}

#[test]
fn single_dash_token_that_names_nothing_gets_no_suggestion() {
    // The pair to the test above: the two-dash advice is keyed on `find_param`
    // over the command's OWN params, not on the leading dash. A token the spec
    // does not contain must get the plain refusal — inventing `--zzz` would name
    // a flag that does not exist.
    let (ok, stderr, _) = run(&["list", "-zzz"]);
    assert!(!ok, "an unknown one-dash token must be refused");
    assert!(
        stderr.contains("unexpected argument '-zzz'"),
        "the offending token must appear verbatim; got:\n{stderr}"
    );
    assert!(
        !stderr.contains("--zzz"),
        "must not invent a two-dash flag the spec never declared; got:\n{stderr}"
    );
    assert!(
        !stderr.contains("a flag takes two dashes"),
        "the suggestion must not fire for a token that names no param; got:\n{stderr}"
    );
    assert_names_list_and_its_flags(&stderr);
}

#[test]
fn a_single_dash_token_naming_a_positional_is_not_advised_to_grow_a_dash() {
    // The THIRD arm of the same predicate, and the one a fixture of flags alone
    // cannot judge: `id` IS a parameter of `show`, so `find_param` finds it — but
    // it is a POSITIONAL, spelled `<id>` in the usage line printed directly below.
    // Advising `--id` there would contradict that line, which is the exact drift
    // between advice and spec this reporter exists to remove. The fix for a
    // positional is to drop the dash, not to add one, so no advice is offered.
    let (ok, stderr, _) = run(&["show", "WI-001", "-id"]);
    assert!(!ok, "a stray one-dash token must be refused");
    assert!(
        stderr.contains("unexpected argument '-id'"),
        "the offending token must appear verbatim; got:\n{stderr}"
    );
    assert!(
        !stderr.contains("--id"),
        "a positional must not be advised as a flag; got:\n{stderr}"
    );
    assert!(
        stderr.contains("usage: show <id>"),
        "and the usage line it would have contradicted is right there; got:\n{stderr}"
    );
}

#[test]
fn unknown_flag_lists_the_flags_the_command_does_accept() {
    let (ok, stderr, _) = run(&["list", "--stat", "Open"]);
    assert!(!ok, "an unknown flag must be refused");
    assert!(
        stderr.contains("unknown flag '--stat'"),
        "the offending flag must appear verbatim; got:\n{stderr}"
    );
    assert_names_list_and_its_flags(&stderr);
}

#[test]
fn a_value_flag_given_no_value_names_that_flag() {
    let (ok, stderr, _) = run(&["list", "--status"]);
    assert!(!ok, "a value flag with no value must be refused");
    assert!(
        stderr.contains("flag '--status' expects a value"),
        "the diagnostic must name which flag went hungry; got:\n{stderr}"
    );
    assert_names_list_and_its_flags(&stderr);
}

#[test]
fn missing_required_positional_names_the_parameter_and_its_usage() {
    let (ok, stderr, _) = run(&["show"]);
    assert!(!ok, "a missing required positional must be refused");
    assert!(
        stderr.contains("anthill-todo: show: missing required argument <id>"),
        "the diagnostic must name the command and the parameter; got:\n{stderr}"
    );
    assert!(
        stderr.contains("usage: show <id>"),
        "a positional must render as <id>, not as a flag; got:\n{stderr}"
    );
    assert!(
        stderr.contains("Work item id"),
        "the ARGS block must carry the ParamSpec's own description; got:\n{stderr}"
    );
}

#[test]
fn happy_path_flags_still_parse() {
    // Passes with and without the change, BY DESIGN: the control that says the
    // five diagnostics above were not bought by making the parser refuse more.
    let (ok, stderr, stdout) = run(&["list", "--status", "Open", "--unblocked"]);
    assert!(
        ok,
        "a well-formed invocation must still succeed; stderr:\n{stderr}"
    );
    assert!(
        stdout.contains("WI-001"),
        "the open, unblocked fixture item must be listed; got:\n{stdout}"
    );
}
