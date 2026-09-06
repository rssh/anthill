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
//! CONTROLS, every one of them RUN rather than reasoned about. Restore the
//! collapsed arm and the five original diagnostic tests all fail: the stderr is
//! then the fixed string `anthill-todo: argument error`, which contains no token,
//! no command name and no `--flag`. Narrower back-outs, with the rows each one
//! actually failed:
//!
//!   * make `single_dash_flag` answer `some(name)` for any `-`-prefixed token
//!     instead of looking the name up — ONE fails,
//!     `single_dash_token_that_names_nothing_gets_no_suggestion`, while
//!     `single_dash_flag_is_named_with_its_two_dash_form` stays green. Both are
//!     here for that reason.
//!   * make `find_dashed_param` (stdlib `cli/parse.anthill`) match on the name
//!     alone, dropping `dash_spelled` — TWO fail:
//!     `a_positional_is_not_reachable_as_a_flag` and
//!     `a_single_dash_token_naming_a_positional_is_not_advised_to_grow_a_dash`.
//!     I first wrote "fails alone" here and measured otherwise. Two is CORRECT and
//!     is the fix working: the parser's flag lookup and the reporter's suggestion
//!     are now literally the same call, so the suggestion cannot name a spelling
//!     the parser would refuse. When they had separate copies, only the second
//!     row moved.
//!   * spell `missing_required` as `<name>` again (bypass `required_spelling`) —
//!     ONE fails, `a_missing_required_flag_is_spelled_the_way_the_parser_accepts_it`.
//!   * restore the prior `usage_token` body (positional unbracketed, everything
//!     else always bracketed, `repeated`'s `...` outside) — THREE fail:
//!     `a_required_param_is_unbracketed_in_the_usage_line`,
//!     `a_repeatable_param_renders_as_repeatable`, and the `missing_required`
//!     one again. Also not the "one" I first wrote, and also the point: the
//!     message and the usage line read the SAME `param_token`, so they move
//!     together or not at all. (Mutating `param_token` to ignore `required`
//!     instead fails FIVE, because that also brackets positionals — which the old
//!     code never did. It is not a back-out of anything; the row above is.)
//!   * put the seven registry params back to `kind: flag()` — ONE fails,
//!     `a_repeatable_param_renders_as_repeatable`.
//!
//! `happy_path_flags_still_parse` passes under every one of them BY DESIGN: it is
//! the witness that the diagnostics were not bought by breaking the parse they
//! report on.

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

// ─── /code-review high, 2026-09-06: four ways the new block contradicted itself ──
//
// Each of these printed a message and, one line under it, a usage block DENYING
// what the message said. The collapsed `anthill-todo: argument error` line said
// nothing and so misled nobody; asserting a spelling makes the assertion
// falsifiable, which is the point of the change and also its new failure mode.
// Their back-outs and the rows each one fails are in the header — they are not one
// test each, because the fixes deliberately COLLAPSED duplicated definitions.

#[test]
fn a_missing_required_flag_is_spelled_the_way_the_parser_accepts_it() {
    // `insert`'s `before` is `kind: flag(), required: true` — the registry's only
    // required non-positional, and the row that makes this measurable at all.
    let (ok, stderr, _) = run(&["insert", "a new item"]);
    assert!(!ok, "a missing required flag must be refused");
    assert!(
        stderr.contains("missing required argument --before VALUE"),
        "a required FLAG must be named as a flag; got:\n{stderr}"
    );
    assert!(
        !stderr.contains("<before>"),
        "the positional spelling is refused when followed, so it must not be advised; got:\n{stderr}"
    );
}

#[test]
fn a_required_param_is_unbracketed_in_the_usage_line() {
    // The other half of the same message: `missing required argument --before VALUE`
    // printed over `[--before VALUE]` would call the missing param optional.
    let (ok, stderr, _) = run(&["insert", "a new item"]);
    assert!(!ok, "a missing required flag must be refused");
    assert!(
        stderr.contains("usage: insert <description> --before VALUE ["),
        "a required flag must render without optionality brackets; got:\n{stderr}"
    );
    assert!(
        !stderr.contains("[--before VALUE]"),
        "…and must not also appear bracketed; got:\n{stderr}"
    );
}

#[test]
fn a_positional_is_not_reachable_as_a_flag() {
    // `show --id` used to reach `flag_expects_value` and print
    // `flag '--id' expects a value` directly above `usage: show <id>`, a block
    // that denies `--id` exists. `consume_flag` now asks the same dash-spelled
    // question every renderer asks, so `--id` is simply unknown.
    let (ok, stderr, _) = run(&["show", "--id"]);
    assert!(!ok, "a positional's name is not a flag");
    assert!(
        stderr.contains("unknown flag '--id'"),
        "expected the unknown-flag refusal; got:\n{stderr}"
    );
    assert!(
        !stderr.contains("expects a value"),
        "must not offer to accept a flag the usage block omits; got:\n{stderr}"
    );
    assert!(
        stderr.contains("usage: show <id>"),
        "and the block it agrees with is right there; got:\n{stderr}"
    );
}

#[test]
fn a_repeatable_param_renders_as_repeatable() {
    // Seven registry params carried "(repeatable)" in their description while
    // declared `kind: flag()`, so `usage_token`'s `repeated()` arm was dead and
    // the usage line said `[--depends VALUE]` above "Dependency work item id
    // (repeatable)". Nothing printed either string before this change.
    let (ok, stderr, _) = run(&["add", "--nosuch"]);
    assert!(!ok, "an unknown flag must be refused");
    assert!(
        stderr.contains("[--depends VALUE...]"),
        "a repeatable param must render its ellipsis; got:\n{stderr}"
    );
    assert!(
        stderr.contains("Dependency work item id (repeatable)"),
        "…beside the description that says so; got:\n{stderr}"
    );
    assert!(
        stderr.contains("[--created VALUE]"),
        "and a non-repeatable flag must NOT grow one; got:\n{stderr}"
    );
}
