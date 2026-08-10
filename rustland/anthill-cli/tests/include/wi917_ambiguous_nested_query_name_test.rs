//! WI-917 — an AMBIGUOUS query name is refused WHEREVER it is written, and a DOTTED path
//! whose head is contested is refused as an ambiguity rather than as an absence.
//!
//! WI-907 made a contested name reach the ambiguity message (`wi907_ambiguous_query_name_test`
//! pins that). It reached it only for a SHORT name, and only at the pattern's HEAD or
//! inside a `not` — the positions WI-863's committed-position walk visits. Both limits
//! were DRIVEN through this binary before the fix, on the fixture beside this file:
//!
//!  * `Widget917.w917a(v: ?x)` reported "does not resolve to a known functor — no rule,
//!    fact, or declaration is in scope for it": the very message WI-907 removed for a
//!    short name, back one dot away, because both dotted rungs stand down under a
//!    contested head and the path then fell to the WI-476 bare intern.
//!
//!  * `push_choice(never917(), contested917(?v))` and `box917(inner: load917(n: ?n))`
//!    printed `no solutions`, exit 0, no diagnostic — while EITHER import alone answered
//!    one row. That is the measurement the second half turns on: WI-863 tolerates an
//!    unresolvable name in a bare disjunction branch and never walks a data slot at all,
//!    because an ABSENT name there has no solutions to lose; a contested one does, and
//!    loses them silently.
//!
//! Every contested name in the fixture ANSWERS under either reading, which is what makes
//! those two measurements possible — WI-907's fixture cannot show it, since its contested
//! `SortInfo` is a sort with no clauses.

use crate::common::{anthill, fixtures_dir};

fn query(args: &[&str]) -> crate::common::Output {
    let kb = fixtures_dir("wi917").join("kb.anthill");
    let mut all = vec!["query", "-p", kb.to_str().unwrap()];
    all.extend_from_slice(args);
    anthill(&all)
}

/// Both namespaces in scope, so every short name they share is ambiguous at `_global`.
fn query_both(args: &[&str]) -> crate::common::Output {
    let mut all = vec!["-i", "wi917.alpha.*", "-i", "wi917.beta.*"];
    all.extend_from_slice(args);
    query(&all)
}

/// ONE namespace in scope — the control side of every measurement here: the same pattern,
/// the same declarations, a name that now denotes one thing.
fn query_alpha(args: &[&str]) -> crate::common::Output {
    let mut all = vec!["-i", "wi917.alpha.*"];
    all.extend_from_slice(args);
    query(&all)
}

fn assert_refused_as_ambiguous(out: &crate::common::Output, name: &str, candidates: &[&str]) {
    assert_eq!(
        out.code, 1,
        "a contested pattern must be refused; stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.has_diagnostic("error:", &format!("'{name}' in query pattern is ambiguous")),
        "the refusal must name the AMBIGUITY, not an absence; stderr:\n{}",
        out.stderr
    );
    for c in candidates {
        assert!(
            out.has_diagnostic("error:", c),
            "it must name the candidate `{c}` it could not choose between; stderr:\n{}",
            out.stderr
        );
    }
    assert!(
        !out.has_diagnostic("error:", "does not resolve to a known functor"),
        "and must NOT claim the name resolves to nothing — two declarations do; \
         stderr:\n{}",
        out.stderr
    );
    assert!(
        !out.stdout.contains("solution"),
        "a refused query must not also print an answer; stdout:\n{}",
        out.stdout
    );
}

fn assert_answered(out: &crate::common::Output, line: &str) {
    assert_eq!(
        out.code, 0,
        "stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    assert_eq!(
        out.diagnostics("error:").count(),
        0,
        "stderr:\n{}",
        out.stderr
    );
    assert!(out.has_stdout_line(line), "stdout:\n{}", out.stdout);
}

// ── The dotted head ─────────────────────────────────────────────────

/// THE DOTTED CASE. The candidates named are the HEAD's, because the head is the only
/// segment the ladder resolves — the tail is appended to whatever it denotes, never
/// looked up on its own.
#[test]
fn a_contested_dotted_head_is_refused_as_ambiguous() {
    let out = query_both(&["Widget917.w917a(v: ?x)"]);
    assert_refused_as_ambiguous(
        &out,
        "Widget917.w917a",
        &["wi917.alpha.Widget917", "wi917.beta.Widget917"],
    );
}

/// CONTROL, green on both sides: with one import the head names one sort and the
/// IDENTICAL path answers. A refusal above is therefore the ambiguity, not the
/// head-qualification rung having stopped working.
#[test]
fn a_single_import_still_answers_the_identical_dotted_path() {
    assert_answered(&query_alpha(&["Widget917.w917a(v: ?x)"]), "?x = 1");
}

/// CONTROL, green on both sides, and the one that makes the message's ADVICE true:
/// "qualify the name" has somewhere to go.
#[test]
fn qualifying_the_contested_head_resolves_the_same_path() {
    assert_answered(
        &query_both(&["wi917.alpha.Widget917.w917a(v: ?x)"]),
        "?x = 1",
    );
}

// ── The positions WI-863 tolerates ──────────────────────────────────

/// A BARE DISJUNCTION BRANCH — left to resolution by WI-863, and pre-fix therefore silent:
/// `no solutions`, exit 0, though the branch answers under either reading (next test).
#[test]
fn a_contested_name_in_a_bare_disjunction_branch_is_refused() {
    let out = query_both(&["push_choice(never917(), contested917(?v))"]);
    assert_refused_as_ambiguous(
        &out,
        "contested917",
        &["wi917.alpha.contested917", "wi917.beta.contested917"],
    );
}

/// THE MEASUREMENT THE REFUSAL IS FOR. One import, same pattern: the branch answers. So
/// the second import did not make the query meaningless — it made a name contested, and
/// tolerating that silently DROPPED the row.
#[test]
fn a_single_import_still_answers_the_same_disjunction() {
    assert_answered(
        &query_alpha(&["push_choice(never917(), contested917(?v))"]),
        "?v = 1",
    );
}

/// A DATA SLOT — never a goal, and never walked by the undefined-functor pass at all.
/// This is where the two diagnoses diverge most: an ABSENT data name's bare intern is
/// what the FACT's loader produced too, so pattern and fact match; a contested one's
/// matches neither reading, which is why the fact below stops being found.
#[test]
fn a_contested_name_in_a_data_slot_is_refused() {
    let out = query_both(&["box917(inner: load917(n: ?n))"]);
    assert_refused_as_ambiguous(
        &out,
        "load917",
        &[
            "wi917.alpha.Payload917.load917",
            "wi917.beta.Payload917.load917",
        ],
    );
}

/// THE MEASUREMENT for the data slot: `fact box917(inner: load917(n: 7))` is written
/// inside `wi917.alpha`, where the name resolves, so one import finds it and two lose it.
#[test]
fn a_single_import_still_matches_the_same_data_slot() {
    assert_answered(&query_alpha(&["box917(inner: load917(n: ?n))"]), "?n = 7");
}

/// CONTROL — WI-863's tolerance itself must survive. An ABSENT name in the SAME bare
/// branch still answers: its reason (that branch has no solutions to lose) holds for an
/// absence and only for one, so widening the descent must not widen WHAT is refused.
#[test]
fn an_absent_name_in_a_bare_disjunction_branch_is_still_tolerated() {
    assert_answered(
        &query_both(&["push_choice(w917a(v: ?x), no_such_thing917(?z))"]),
        "?x = 1",
    );
}
