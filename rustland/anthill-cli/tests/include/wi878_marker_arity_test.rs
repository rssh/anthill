//! WI-878 (Case C of WI-863) — the undefined-functor guard exempted a resolver
//! SCOPING MARKER by its SHORT NAME alone. The four marker names — `forall_in` /
//! `some_in` / `forall_impl` (3-ary) and `__pop_assumption` (1-ary) — are
//! skolemised / expanded by the resolver in place, so they carry no rule / fact /
//! declaration and must be exempted from the "undefined functor" report; without
//! the exemption a legitimate `(forall …)` query would be mis-refused (WI-027).
//!
//! But the exemption was name-only, so a marker NAME carried at a NON-marker
//! arity — a user typo like `some_in(x)` — was exempted too and escaped the
//! report: it resolved to nothing and printed a silent `no solutions`, the exact
//! silent-skip the WI-754 / WI-863 guard exists to eliminate. The fix makes the
//! shared `is_scoping_marker` predicate arity-aware and routes BOTH the CLI
//! exemption and the resolver's marker dispatch through it (lockstep), so a
//! mis-arity marker name is no longer a marker anywhere: the resolver treats it as
//! an ordinary (undefined) functor and the CLI reports it loudly, while a
//! well-formed marker at its canonical arity still resolves unchanged.


use crate::common::{anthill, fixtures_dir};

/// Queried against `wi754/props.anthill` — top-level `base(1)`/`base(2)` facts and
/// NO marker names declared anywhere, so a bare `some_in` / `forall_in` /
/// `forall_impl` / `__pop_assumption` is a genuinely undefined functor.
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

/// A query that ran to an answer without any refusal.
fn answered(out: &crate::common::Output) -> bool {
    out.code == 0 && out.diagnostics("error:").count() == 0
}

// ── A marker NAME at a non-marker arity is refused, not silent ──────

/// THE acceptance case: `some_in` is the resolver's 3-ary existential quantifier,
/// but `some_in(x)` is a 1-ary application — a typo, not a quantifier. Before, the
/// name-only exemption swallowed it and the query printed a silent `no solutions`;
/// now the arity gate declines the exemption and the undefined functor is named.
#[test]
fn some_in_at_wrong_arity_is_refused_not_silent() {
    let out = query_props(&["some_in(x)"]);
    assert!(is_refused(&out, "some_in"), "stdout:\n{}\nstderr:\n{}", out.stdout, out.stderr);
    // THE pin: the old bug printed a silent, confident `no solutions` for a name
    // that resolves to nothing. A refusal must not also report an empty answer.
    assert!(
        !out.has_stdout_line("no solutions"),
        "a refused marker-typo must not also print `no solutions`; stdout:\n{}",
        out.stdout
    );
}

/// The 3-ary universal quantifier at the wrong arity is refused the same way.
#[test]
fn forall_in_at_wrong_arity_is_refused() {
    let out = query_props(&["forall_in(x)"]);
    assert!(is_refused(&out, "forall_in"), "stdout:\n{}\nstderr:\n{}", out.stdout, out.stderr);
}

/// The 3-ary hereditary-Harrop marker (WI-108) at the wrong arity is refused too.
#[test]
fn forall_impl_at_wrong_arity_is_refused() {
    let out = query_props(&["forall_impl(x)"]);
    assert!(is_refused(&out, "forall_impl"), "stdout:\n{}\nstderr:\n{}", out.stdout, out.stderr);
}

/// The OTHER arity class: `__pop_assumption` is the 1-ary scope-discharge marker,
/// so a 2-ary `__pop_assumption(1, 2)` is off-arity and refused — exercising the
/// `pos_arity == 1` branch of the shared predicate, not just the 3-ary one.
#[test]
fn pop_assumption_at_wrong_arity_is_refused() {
    let out = query_props(&["__pop_assumption(1, 2)"]);
    assert!(
        is_refused(&out, "__pop_assumption"),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}

// ── A well-formed marker at its canonical arity still resolves ──────

/// THE regression: a well-formed universal quantifier desugars to a 3-ary
/// `forall_in(?x, xs, tuple(body))`, which the arity gate STILL exempts (and the
/// resolver still expands). `forall ?x in [1,2]: base(?x)` holds — both facts
/// exist — and must answer `true`, never be refused as an unknown `forall_in`.
#[test]
fn a_well_formed_forall_still_resolves() {
    let out = query_props(&["(forall ?x in [1, 2]: base(?x))"]);
    assert!(answered(&out), "a well-formed forall must resolve, not be refused; stderr:\n{}", out.stderr);
    assert!(out.stdout.contains("true"), "stdout:\n{}", out.stdout);
}

/// The existential twin: `some ?x in [1,2]: base(?x)` desugars to a 3-ary
/// `some_in`, exempted and expanded unchanged — `base(1)` satisfies it, so it
/// answers. This is the direct counterpart to the refused `some_in(x)` typo: same
/// name, canonical arity, opposite outcome.
#[test]
fn a_well_formed_some_still_resolves() {
    let out = query_props(&["(some ?x in [1, 2]: base(?x))"]);
    assert!(answered(&out), "a well-formed some must resolve, not be refused; stderr:\n{}", out.stderr);
    assert!(out.stdout.contains("true"), "stdout:\n{}", out.stdout);
}
