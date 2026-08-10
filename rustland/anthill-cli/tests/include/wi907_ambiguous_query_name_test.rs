//! WI-907 — an AMBIGUOUS query name is refused AS AMBIGUOUS.
//!
//! WI-754 made a query name that resolves to nothing a loud refusal instead of `no
//! solutions`. WI-907 is the other half of that message's job: since the name ladder now
//! STOPS at an ambiguity rather than descending past it, an ambiguous name reaches the
//! same reporter as an absent one — and telling an author "no rule, fact, or declaration
//! is in scope for it" when TWO are sends them to declare a third.
//!
//! The `-i` flags are the whole experiment, and the measurement behind it is in
//! `anthill-core`'s `wi907_ambiguous_name_ladder_test`, which also pins which symbol
//! each case binds.

use crate::common::{anthill, fixtures_dir};

fn query(args: &[&str]) -> crate::common::Output {
    let kb = fixtures_dir("wi907").join("kb.anthill");
    let mut all = vec!["query", "-p", kb.to_str().unwrap()];
    all.extend_from_slice(args);
    anthill(&all)
}

/// Both namespaces in scope, so `name` is ambiguous at `_global`.
fn query_both(args: &[&str]) -> crate::common::Output {
    let mut all = vec!["-i", "wi907.alpha.*", "-i", "wi907.beta.*"];
    all.extend_from_slice(args);
    query(&all)
}

fn assert_refused_as_ambiguous(out: &crate::common::Output, name: &str, candidates: &[&str]) {
    assert_eq!(
        out.code, 1,
        "an ambiguous pattern must be refused; stdout:\n{}\nstderr:\n{}",
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

/// THE acceptance case, on the name that used to ANSWER. `SortInfo` is ambiguous between
/// the two imported sorts AND is an implicit-tier spelling — the combination that made
/// the fall-through produce rows rather than silence.
#[test]
fn an_ambiguous_name_colliding_with_the_implicit_tier_is_refused() {
    let out = query_both(&["SortInfo(name: ?n)"]);
    assert_refused_as_ambiguous(
        &out,
        "SortInfo",
        &["wi907.alpha.SortInfo", "wi907.beta.SortInfo"],
    );
}

/// The same refusal for an ordinary user name with no tier twin, which pre-fix bound the
/// bare symbol and reported the (false) unknown-functor message. One rule, not a
/// special case for the names the tier happens to list.
#[test]
fn an_ambiguous_user_name_is_refused_with_its_candidates() {
    let out = query_both(&["Widget907(v: ?x)"]);
    assert_refused_as_ambiguous(
        &out,
        "Widget907",
        &["wi907.alpha.Widget907", "wi907.beta.Widget907"],
    );
}

/// CONTROL — ONE import: the name resolves, so the query runs and answers. Without this
/// the refusals above would also pass if `-i` had simply stopped working.
#[test]
fn a_single_import_still_answers() {
    let out = query(&["-i", "wi907.alpha.*", "w907a(v: ?x)"]);
    assert_eq!(
        out.code, 0,
        "stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    assert!(out.has_stdout_line("?x = 1"), "stdout:\n{}", out.stdout);
}

/// CONTROL — WI-754's own case must keep its own message: a name nothing declares is
/// still reported as absent, not as ambiguous. The two diagnostics are the two answers
/// the ladder can give, and conflating them in either direction is the defect.
#[test]
fn an_absent_name_is_still_reported_as_absent() {
    let out = query_both(&["NoSuchThing907(?x)"]);
    assert_eq!(
        out.code, 1,
        "stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.has_diagnostic("error:", "does not resolve to a known functor"),
        "stderr:\n{}",
        out.stderr
    );
    assert!(
        !out.has_diagnostic("error:", "ambiguous"),
        "nothing declares this name, so there is no conflict to report; stderr:\n{}",
        out.stderr
    );
}
