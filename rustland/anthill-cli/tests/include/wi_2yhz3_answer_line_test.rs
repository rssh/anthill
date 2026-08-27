//! WI-20260827-2YHZ3 — `anthill query` prints the answer it PROVED.
//!
//! The visible half of the reader defect. `rule builtin_bound(?x) :- ?x <=> 6`
//! answered `?x = ?_` — a head variable bound by a rule-body BUILTIN sits behind
//! an answer link σ never path-compressed, and the answer line read one hop and
//! stopped on the link. Nothing about resolution was wrong: `builtin_bound(6)`
//! answered `true` and `builtin_bound(7)` answered nothing, in the same build
//! that printed `?_`.
//!
//! This is where the defect was actually costly. A `?_` in an answer line is how
//! an author learns "your rule computed nothing" — so it read as a LANGUAGE
//! limitation ("a rule body cannot bind an operation's result") rather than as a
//! printing bug, and was filed as one.
//!
//! WHAT FAILS ON A BACK-OUT: `builtin_bound_head_var_prints_its_value` and
//! `nested_binding_prints_all_the_way_down`.
//! WHAT PASSES EITHER WAY, BY DESIGN: `fact_bound_head_var_was_never_truncated`
//! (the compressed path), `ground_queries_decided_correctly_throughout`
//! (resolution was never the problem), and `an_honestly_unbound_answer_still_prints_underscore`
//! — the one that keeps the fix from becoming a lie in the other direction.

use crate::common::{anthill, fixtures_dir};

fn fixture() -> std::path::PathBuf {
    fixtures_dir("query").join("builtin-bound-head.anthill")
}

fn query(goal: &str) -> crate::common::Output {
    let fx = fixture();
    let out = anthill(&["query", "-p", fx.to_str().unwrap(), goal]);
    assert_eq!(out.code, 0, "`{goal}` must run; stderr:\n{}", out.stderr);
    out
}

/// THE HEADLINE.
#[test]
fn builtin_bound_head_var_prints_its_value() {
    let out = query("probe.wi2yhz3.builtin_bound(?x)");
    assert!(
        out.stdout.contains("?x = 6"),
        "a head var bound by a rule-body builtin must PRINT its value; got stdout:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("?x = ?_"),
        "and must not print as unbound; got stdout:\n{}",
        out.stdout
    );
    assert!(
        out.has_stdout_line("1 solution(s)"),
        "exactly one answer; got stdout:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("residual"),
        "nothing flounders here — the answer is definite; got stdout:\n{}",
        out.stdout
    );
}

/// DEEP, NOT A CHASE. A top-level var chase prints `B(v: ?_)` here and passes
/// every other test in this file.
#[test]
fn nested_binding_prints_all_the_way_down() {
    let out = query("probe.wi2yhz3.nested(?x)");
    assert!(
        out.stdout.contains("?x = B(v: 6)"),
        "the nested var must resolve too; got stdout:\n{}",
        out.stdout
    );
}

/// CONTROL — passes either way BY DESIGN. The fact path binds through
/// `bind_compressed`, so one hop always landed on the value here. This agreement
/// is why the other path's truncation went unnoticed.
#[test]
fn fact_bound_head_var_was_never_truncated() {
    let out = query("probe.wi2yhz3.fact_bound(?x)");
    assert!(
        out.stdout.contains("?x = 6"),
        "the compressed path was always readable; got stdout:\n{}",
        out.stdout
    );
}

/// CONTROL — passes either way BY DESIGN. A ground query has no answer var to
/// project, so it decided correctly throughout. This is the measurement that
/// separated "the resolver cannot bind" from "the printer cannot read it".
#[test]
fn ground_queries_decided_correctly_throughout() {
    let yes = query("probe.wi2yhz3.builtin_bound(6)");
    assert!(
        yes.has_stdout_line("true") && yes.has_stdout_line("1 solution(s)"),
        "`builtin_bound(6)` is provable; got stdout:\n{}",
        yes.stdout
    );
    let no = query("probe.wi2yhz3.builtin_bound(7)");
    assert!(
        no.has_stdout_line("no solutions"),
        "`builtin_bound(7)` is refuted; got stdout:\n{}",
        no.stdout
    );
}

/// THE OTHER DIRECTION, and the reason this control is not optional: the fix
/// must not make `?_` disappear where `?_` is the honest answer. `=` is
/// `PartialEq.eq`, a TEST that never binds (§8.3), so `?x = 6` on a free `?x`
/// SUSPENDS — and a suspension must keep printing as an unbound var WITH its
/// residual, not be laundered into a definite-looking answer.
#[test]
fn an_honestly_unbound_answer_still_prints_underscore() {
    let out = query("probe.wi2yhz3.tested(?x)");
    assert!(
        out.stdout.contains("?x = ?_"),
        "an answer that genuinely binds nothing still shows an unbound var; got stdout:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("residual"),
        "and it says WHY — the undischarged goal is named; got stdout:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("conditional"),
        "and the summary calls it conditional, not a definite answer; got stdout:\n{}",
        out.stdout
    );
}
