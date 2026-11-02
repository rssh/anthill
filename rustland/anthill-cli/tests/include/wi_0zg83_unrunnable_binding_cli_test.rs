//! WI-20260828-0ZG83 — `anthill query` and `anthill run` over a program whose binding names
//! a host function the CLI does not provide: an embedder's, as `examples/guardians/lib`'s
//! keys are the guardians test harness's.
//!
//! Before: every query over such a program whose goal bridged any operation panicked
//! (`bridged_value: internal evaluator error … broken binding block …`), and `anthill run`
//! refused every entry ("error: registering builtins: …"). Now the binding is reported at
//! the call it backs.
//!
//! WITH THE CHANGE BACKED OUT (measured with the pre-change binary on these fixtures):
//! `the_guardians_library_does_not_stop_a_query_that_never_reaches_it` fails at its test
//! half (exit 101, the panic) and passes its control half;
//! `an_unrelated_goal_is_answered_and_the_reaching_goal_reported` and
//! `run_reports_the_binding_at_the_call_and_runs_an_entry_that_avoids_it` fail.

use crate::common::{anthill, fixtures_dir};

fn fixture(name: &str) -> String {
    fixtures_dir("wi_0zg83")
        .join(name)
        .to_str()
        .unwrap()
        .to_string()
}

fn guardians_lib() -> String {
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/guardians/lib")
        .to_str()
        .unwrap()
        .to_string()
}

/// THE ACCEPTANCE: the same query, the same goal, with and without the guardians library
/// on the load path. The goal bridges `anthill.reflect.as_term`, a host operation of the
/// standard library, and never reaches a guardians binding.
#[test]
fn the_guardians_library_does_not_stop_a_query_that_never_reaches_it() {
    let ctl = fixture("ctl");
    let control = anthill(&["query", "-p", &ctl, "ctl.read(1)"]);
    assert_eq!(
        control.code, 0,
        "control: the goal bridges a host operation and holds; stderr:\n{}",
        control.stderr
    );
    assert!(
        control.has_stdout_line("1 solution(s)"),
        "{}",
        control.stdout
    );

    let lib = guardians_lib();
    let test = anthill(&["query", "-p", &ctl, "-p", &lib, "ctl.read(1)"]);
    assert_eq!(
        test.code, 0,
        "the guardians library's bindings do not stop the query; stderr:\n{}",
        test.stderr
    );
    assert!(test.has_stdout_line("1 solution(s)"), "{}", test.stdout);
    assert!(!test.stderr.contains("panicked"), "{}", test.stderr);
}

/// A goal that reaches no binding is answered; one that reaches the unrunnable binding is
/// reported naming the operation and the key, and its search marked incomplete.
#[test]
fn an_unrelated_goal_is_answered_and_the_reaching_goal_reported() {
    let p = fixture("embedder");
    let other = anthill(&["query", "-p", &p, "p.other(?r)"]);
    assert_eq!(other.code, 0, "stderr:\n{}", other.stderr);
    assert!(other.stdout.contains("?r = 2"), "{}", other.stdout);

    let uses = anthill(&["query", "-p", &p, "p.uses(?r)"]);
    assert_eq!(uses.code, 0, "stderr:\n{}", uses.stderr);
    assert!(
        uses.has_diagnostic(
            "warning:",
            "`p.W.squish` could not be evaluated by the resolver: its `language rust` \
             binding (`operation_map`) names host function \"embedder_squish\", which this \
             runtime does not provide"
        ),
        "stderr:\n{}",
        uses.stderr
    );
    assert!(uses.stdout.contains("INCOMPLETE"), "{}", uses.stdout);
}

/// `anthill run`: an entry that reaches the binding fails naming it; an entry of the same
/// program that does not reach it runs to its answer.
#[test]
fn run_reports_the_binding_at_the_call_and_runs_an_entry_that_avoids_it() {
    let p = fixture("embedder");
    let reaches = anthill(&["run", "--entry", "p.Reaches", &p]);
    assert_eq!(reaches.code, 1, "stderr:\n{}", reaches.stderr);
    assert!(
        reaches.has_diagnostic("error:", "`p.W.squish` cannot run here"),
        "stderr:\n{}",
        reaches.stderr
    );

    let avoids = anthill(&["run", "--entry", "p.Avoids", &p]);
    assert_eq!(
        avoids.code, 2,
        "`main` answers `plain(1)`, the exit code; stderr:\n{}",
        avoids.stderr
    );
}
