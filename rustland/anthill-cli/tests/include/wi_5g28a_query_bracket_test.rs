//! WI-20260911-5G28A (L3 review) — a type BRACKET in a query pattern is refused by name,
//! not crashed on. `convert_query_term` reads neither parse-only bracket channel and its
//! `Term::ParseAux` arm is `unreachable!`, so the applied `Wrap[T = C].holds()` and the
//! call-site `Wrap.holds[T = C]()` PANICKED the CLI on every tree, and L3 — which lowers
//! the paren-less `Wrap[T = C].holds` to the applied term — made it the third spelling
//! to (it used to answer a silent `no solutions`). The query scan now refuses all three
//! (`load::query_bracket_errors`).
//!
//! BACK-OUT: drop the `SourceRole::Query` call of `query_bracket_errors` in
//! `scan_definitions_with_sources` and the three refusal rows panic (exit 101). The
//! control passes either way, by design.

use crate::common::{anthill, fixtures_dir};

fn query(goal: &str) -> crate::common::Output {
    let kb = fixtures_dir("wi_5g28a").join("wrap.anthill");
    anthill(&["query", "-p", kb.to_str().unwrap(), goal])
}

#[track_caller]
fn assert_refused(goal: &str, needle: &str) {
    let out = query(goal);
    assert!(
        out.code == 1 && out.has_diagnostic("error:", needle) && !out.stderr.contains("panicked"),
        "`{goal}` must be refused naming `{needle}`, not crash or answer; code {}\n\
         stdout:\n{}\nstderr:\n{}",
        out.code,
        out.stdout,
        out.stderr
    );
}

#[test]
fn a_paren_less_receiver_bracket_is_refused() {
    assert_refused(
        "q5g28a.Wrap[T = q5g28a.Colour].holds",
        "type bracket is not read in a query pattern",
    );
}

#[test]
fn an_applied_receiver_bracket_is_refused() {
    assert_refused(
        "q5g28a.Wrap[T = q5g28a.Colour].holds()",
        "type bracket is not read in a query pattern",
    );
}

#[test]
fn a_call_site_bracket_is_refused() {
    assert_refused(
        "q5g28a.Wrap.holds[T = q5g28a.Colour]()",
        "call-site type arguments `q5g28a.Wrap.holds[…](…)` are not supported here",
    );
}

#[test]
fn the_unbracketed_goal_answers() {
    // CONTROL — passes with the change backed out, by design: the fixture and the goal
    // are sound, so each refusal above is about its bracket alone.
    let out = query("q5g28a.Wrap.holds");
    assert!(
        out.code == 0 && out.has_stdout_line("true"),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}
