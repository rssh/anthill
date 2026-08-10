//! WI-863(A) — the WI-754 unknown-functor refusal is HEAD-ONLY, so a functor
//! nested in a GOAL position escaped it. The worst case is `not(<absent>(42))`:
//! the undefined inner goal resolves to a complete-empty search, and NAF flips
//! that to a confident `true` — a query asserts a negation for a predicate that
//! does not exist. The fix walks the query's goal positions, but only refuses an
//! undefined functor in a position COMMITTED to its truth: the top-level goal, or
//! anywhere inside a `not` (directly, or a connective deep — `not(p | absent)`).
//!
//! A BARE (un-negated) disjunction or quantifier is left to resolution: an `or` /
//! `push_choice` branch may fail while its sibling succeeds, and a quantifier body
//! over a possibly-empty collection may never run — so an undefined name there
//! does not corrupt the (correct) answer, and refusing it would reject a valid
//! query. `not` is the one goal context where an undefined functor NECESSARILY
//! falsifies its negand. Each nested case is pinned alongside the legitimate NAF
//! it must be told apart from.

use crate::common::{anthill, fixtures_dir};

/// Queried against `props.anthill` — top-level `base(1)`/`base(2)` facts, the
/// `holds`/`never` propositions, and NO `nonesuch`, so a nested `nonesuch` is a
/// genuinely undefined goal functor.
fn query_props(args: &[&str]) -> crate::common::Output {
    let kb = fixtures_dir("wi754").join("props.anthill");
    let mut all = vec!["query", "-p", kb.to_str().unwrap()];
    all.extend_from_slice(args);
    anthill(&all)
}

fn is_refused(out: &crate::common::Output, name: &str) -> bool {
    out.code == 1
        && out.has_diagnostic("error:", &format!("'{name}'"))
        && out.has_diagnostic("error:", "does not resolve to a known functor")
}

/// A query that ran to an answer without any refusal — the shape every
/// "must-not-over-refuse" control checks.
fn answered(out: &crate::common::Output) -> bool {
    out.code == 0 && out.diagnostics("error:").count() == 0
}

// ── The nested-under-`not` refusal (THE acceptance case) ────────────

/// `not(nonesuch(42))` must NOT silently answer `true`. Before, the undefined
/// inner goal resolved to a complete-empty search and NAF read that as "the
/// negand is false, so `not` holds" — a confident `true` for a name that does not
/// exist. Now the nested functor is named and the query refused.
#[test]
fn not_over_an_unknown_functor_is_refused_not_confident_true() {
    let out = query_props(&["not(nonesuch(42))"]);
    assert!(
        is_refused(&out, "nonesuch"),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    // THE pin: the old bug printed a positive answer. A refusal must not.
    assert!(
        !out.stdout.contains("true") && !out.stdout.contains("solution(s)"),
        "a refused negation must not also assert an answer; stdout:\n{}",
        out.stdout
    );
}

/// Recursion: a doubly-nested `not(not(nonesuch(1)))` is refused too — the walk
/// descends through every goal position inside the negation, not just one level.
#[test]
fn a_doubly_nested_unknown_under_not_is_refused() {
    let out = query_props(&["not(not(nonesuch(1)))"]);
    assert!(
        is_refused(&out, "nonesuch"),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}

/// A connective deep: `not(nonesuch(1) | base(999))`. The surface `|` lowers to
/// the `or` RULE (not a builtin), so a head-only or `not`-negand-only check would
/// miss `nonesuch` and NAF would launder the empty disjunction into `true`. Once
/// inside the `not`, the walk follows `or`'s branches and catches it.
#[test]
fn an_unknown_disjunct_under_not_is_refused() {
    let out = query_props(&["not(nonesuch(1) | base(999))"]);
    assert!(
        is_refused(&out, "nonesuch"),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}

/// A bounded-quantifier body is a goal too, and under a `not` it is followed:
/// `not(forall ?x in [1,2]: nonesuch(?x))` catches the undefined body predicate.
#[test]
fn an_unknown_in_a_quantifier_body_under_not_is_refused() {
    let out = query_props(&["not((forall ?x in [1, 2]: nonesuch(?x)))"]);
    assert!(
        is_refused(&out, "nonesuch"),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}

// ── What legitimate NAF must NOT be refused ─────────────────────────

/// THE over-fire guard for negation: `base` IS defined but has no `base(999)`, so
/// `not(base(999))` is a genuine negation-as-failure that SUCCEEDS. It must answer
/// `true`, exit 0 — never be mistaken for an unknown functor.
#[test]
fn not_over_a_known_empty_predicate_still_succeeds() {
    let out = query_props(&["not(base(999))"]);
    assert!(
        answered(&out),
        "genuine NAF over a known-empty predicate must run; stderr:\n{}",
        out.stderr
    );
    assert!(out.stdout.contains("true"), "stdout:\n{}", out.stdout);
}

/// The other half: `not` over a TRUE fact fails (the fact holds, so its negation
/// does not). `base(1)` is a fact, so `not(base(1))` answers `no solutions`, exit
/// 0 — a genuine negation, not a refusal.
#[test]
fn not_over_a_true_fact_answers_empty() {
    let out = query_props(&["not(base(1))"]);
    assert!(
        answered(&out),
        "genuine negation must run; stderr:\n{}",
        out.stderr
    );
    assert!(
        out.has_stdout_line("no solutions"),
        "stdout:\n{}",
        out.stdout
    );
}

// ── Bare (un-negated) disjunction / quantifier are NOT refused ──────

/// THE boundary that keeps the walk from over-refusing: a `push_choice` branch may
/// fail while its sibling succeeds, so an undefined name in a BARE disjunction does
/// not corrupt the answer. `push_choice(base(1), nonesuch(5))` answers `true` via
/// the live left branch and must NOT be refused (it is not inside a `not`).
#[test]
fn a_bare_disjunction_with_an_unknown_branch_is_not_refused() {
    let out = query_props(&["push_choice(base(1), nonesuch(5))"]);
    assert!(
        answered(&out),
        "a live disjunction must answer, not be refused; stderr:\n{}",
        out.stderr
    );
    assert!(out.stdout.contains("true"), "stdout:\n{}", out.stdout);
}

/// A quantifier over an EMPTY collection never runs its body, so an undefined body
/// predicate is irrelevant and the quantifier is vacuously `true`. A bare (not
/// negated) `forall ?x in []: nonesuch(?x)` must answer, not be refused.
#[test]
fn a_vacuous_bare_quantifier_over_an_unknown_body_is_not_refused() {
    let out = query_props(&["(forall ?x in []: nonesuch(?x))"]);
    assert!(
        answered(&out),
        "a vacuous quantifier must answer, not be refused; stderr:\n{}",
        out.stderr
    );
    assert!(out.stdout.contains("true"), "stdout:\n{}", out.stdout);
}

/// The over-fire guard's positive control: a DEFINED body predicate resolves.
/// `forall ?x in [1,2]: base(?x)` answers `true` — the walk never touches a bare
/// quantifier body, defined or not.
#[test]
fn a_defined_quantifier_body_is_not_refused() {
    let out = query_props(&["(forall ?x in [1, 2]: base(?x))"]);
    assert!(
        answered(&out),
        "a defined body predicate must resolve; stderr:\n{}",
        out.stderr
    );
    assert!(out.stdout.contains("true"), "stdout:\n{}", out.stdout);
}

// ── The scope boundary: DATA positions are not walked ───────────────

/// An undefined functor in a DATA slot — a constructor argument, not a goal — is
/// NOT flagged: `base(nonesuch(1))` walks `base` (defined) but not into its data
/// argument. The query simply matches no fact and answers `no solutions`, exit 0.
/// Refusing here would reject legitimate data; unknown data constructors are a
/// separate concern from an undefined GOAL functor (WI-863 scope).
#[test]
fn an_unknown_functor_in_a_data_position_is_not_refused() {
    let out = query_props(&["base(nonesuch(1))"]);
    assert!(
        answered(&out),
        "a data-position functor must not be refused; stderr:\n{}",
        out.stderr
    );
    assert!(
        out.has_stdout_line("no solutions"),
        "stdout:\n{}",
        out.stdout
    );
}
