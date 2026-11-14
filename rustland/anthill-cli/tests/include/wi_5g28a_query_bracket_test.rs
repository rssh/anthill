//! WI-20260911-5G28A (L3 review) — a type BRACKET in a query pattern is refused by name,
//! not crashed on. `convert_query_term` reads neither parse-only bracket channel and its
//! `Term::ParseAux` arm is `unreachable!`, so the applied `Wrap[T = C].holds()` and the
//! call-site `Wrap.holds[T = C]()` PANICKED the CLI on every tree, and L3 — which lowers
//! the paren-less `Wrap[T = C].holds` to the applied term — made it the third spelling
//! to (it used to answer a silent `no solutions`). The query scan now refuses all three
//! (`load::query_bracket_errors`) — the call-site one, on a relation's goal, where its routing
//! finds nothing the relation declares for it to bind, as on a rule-body goal (a query is
//! typed where it is read, proposal 073 §6.2).
//!
//! BACK-OUT: drop the `SourceRole::Query` call of `query_bracket_errors` in
//! `scan_definitions_with_sources` and the three refusal rows panic (exit 101). The
//! control passes either way, by design.
//!
//! WI-20260824-PAPX0 pairs the paren-less spelling with the dot `(Wrap[…]).holds`, which
//! holds a second copy of the bracket. A query does not read it, and the sweep skips it:
//! with the skip backed out a tuple type entry is refused a second time, as an entry, on
//! the paren-less spelling only (`a_structural_entry_is_refused_once_in_either_spelling`
//! fails; measured on 8c96c440's binary).

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
        "a callee with no type-parameter list",
    );
}

#[test]
fn a_structural_entry_is_refused_once_in_either_spelling() {
    for goal in [
        "q5g28a.Wrap[T = (q5g28a.Colour, q5g28a.Colour)].holds",
        "q5g28a.Wrap[T = (q5g28a.Colour, q5g28a.Colour)].holds()",
    ] {
        assert_refused(goal, "type bracket is not read in a query pattern");
        let out = query(goal);
        let errors = out.stderr.lines().filter(|l| l.starts_with("error:")).count();
        assert_eq!(errors, 1, "`{goal}` must be refused once\nstderr:\n{}", out.stderr);
    }
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
