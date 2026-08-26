//! WI-754 — an UNRESOLVABLE functor in a query pattern is refused LOUDLY, not
//! answered as a silent empty set.
//!
//! The resolver answers an undefined predicate the same way it answers a defined
//! one with no matching facts: an empty solution set, printed `no solutions`,
//! exit 0. For a program that is correct SLD semantics (and negation-as-failure
//! over an undefined predicate depends on it), but at the CLI a human who typed a
//! name that resolves to nothing reads `no solutions` as "no such fact" when the
//! truth is "that name could not resolve". So the query command resolves each
//! pattern FIRST and, only when the answer is empty, refuses a head that names no
//! known functor — the same altitude WI-744 blocks an unresolved import at.
//!
//! Resolving first (rather than a pre-resolution head check) is what keeps the
//! refusal from over-firing on things that DO answer: a bounded quantifier
//! (`forall_in` / `some_in`, a resolver special form with no rule/fact), an
//! arity-0 proposition reachable only through a rule body, a builtin. The tests
//! below pin each of those alongside the genuinely-unknown case they must be told
//! apart from — conflating the two in either direction is the whole defect.

use crate::common::{anthill, fixtures_dir};

fn query(args: &[&str]) -> crate::common::Output {
    let kb = fixtures_dir("wi754").join("kb.anthill");
    let mut all = vec!["query", "-p", kb.to_str().unwrap()];
    all.extend_from_slice(args);
    anthill(&all)
}

/// The top-level (un-namespaced) fixture: propositions and a predicate to
/// quantify over, for cases the head-only check cannot classify without resolving.
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

// ── The unknown-functor refusal ─────────────────────────────────────

/// THE acceptance case. `nope` is declared nowhere, so the pattern resolves to
/// nothing — and that is now a loud fault naming the functor, not `no solutions`.
#[test]
fn an_unknown_functor_is_refused_not_silently_empty() {
    let out = query(&["nope(row: ?x)"]);
    assert!(
        is_refused(&out, "nope"),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    assert!(
        !out.stdout.contains("no solutions") && !out.stdout.contains("solution(s)"),
        "a refused query must not also print an answer; stdout:\n{}",
        out.stdout
    );
}

/// The qualified spelling refuses too, and the diagnostic echoes the whole dotted
/// name the user wrote — the sort segment (`app.util.Q.nope`) included, since an
/// entity's qualified name carries the sort it was declared in.
#[test]
fn an_unknown_qualified_functor_is_refused() {
    let out = query(&["app.util.Q.nope(row: ?x)"]);
    assert!(
        is_refused(&out, "app.util.Q.nope"),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}

/// A namespaced name queried by its BARE leaf does not resolve at the query's
/// `<global>` scope, so it is refused — and the message guides to the fix (qualify
/// or `-i`) rather than falsely claiming nothing defines it. The control shows the
/// SAME predicate answers under its qualified name, so the refusal is about scope,
/// not existence.
#[test]
fn a_namespaced_name_queried_bare_is_refused_but_qualified_answers() {
    let bare = query(&["q(row: ?x)"]);
    assert!(
        is_refused(&bare, "q"),
        "stdout:\n{}\nstderr:\n{}",
        bare.stdout,
        bare.stderr
    );
    assert!(
        bare.has_diagnostic("error:", "-i") || bare.has_diagnostic("error:", "Qualify"),
        "the refusal must guide the user to qualify or import; stderr:\n{}",
        bare.stderr
    );

    let qualified = query(&["app.util.Q.q(row: ?x)"]);
    assert_eq!(
        qualified.code, 0,
        "the qualified name must answer; stderr:\n{}",
        qualified.stderr
    );
    assert!(
        qualified.stdout.contains("?x = 7"),
        "stdout:\n{}",
        qualified.stdout
    );
}

// ── What must NOT be refused ────────────────────────────────────────

/// THE over-fire guard, and the reason the check keys on definedness rather than
/// on an empty result: `app.util.Q.q` IS defined but has no `row: 999`, so it
/// legitimately answers the empty set — `no solutions`, exit 0 — and must NOT be
/// mistaken for an unknown name.
#[test]
fn a_known_functor_with_no_match_answers_empty() {
    let out = query(&["app.util.Q.q(row: 999)"]);
    assert_eq!(
        out.code, 0,
        "a known-but-nonmatching query must run; stderr:\n{}",
        out.stderr
    );
    assert!(
        out.has_stdout_line("no solutions"),
        "stdout:\n{}",
        out.stdout
    );
    assert_eq!(
        out.diagnostics("error:").count(),
        0,
        "a defined functor must not be refused; stderr:\n{}",
        out.stderr
    );
}

/// The other half of the control: a defined functor with a matching fact answers
/// as before. Pins that the guard adds a refusal path without disturbing the
/// resolution one.
#[test]
fn a_known_functor_with_a_match_answers() {
    let out = query(&["app.util.Q.q(row: ?x)"]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert!(out.stdout.contains("?x = 7"), "stdout:\n{}", out.stdout);
    assert!(
        out.has_stdout_line("1 solution(s)"),
        "stdout:\n{}",
        out.stdout
    );
}

/// A head with no functor — a bare variable — has no name to resolve, so it is
/// exempt and enumerates the KB the way it always did. This is the boundary the
/// ticket asked to settle: an anonymous / variable head is NOT an unknown name.
#[test]
fn a_variable_head_is_exempt() {
    let out = query(&["?x"]);
    assert_eq!(
        out.code, 0,
        "a variable head must not be refused; stderr:\n{}",
        out.stderr
    );
    assert_eq!(
        out.diagnostics("error:").count(),
        0,
        "stderr:\n{}",
        out.stderr
    );
    assert!(
        out.stdout.contains("solution(s)"),
        "it enumerates; stdout:\n{}",
        out.stdout
    );
}

/// A builtin (`eq`) is a `Resolved` operation, so it is defined and must not be
/// refused — even though it has no `rules_by_functor` entry.
#[test]
fn a_builtin_functor_is_exempt() {
    // WI-20260825-KD9SW — `-i` for the WRITTEN `eq`. A minted `=` names
    // `..anthill.prelude.PartialEq.eq` outright and needs nothing; the implicit tier that
    // used to answer a written `eq` in query scope is gone, and a query has no file to
    // hold an import. This is the repair the refusal's own message prescribes.
    let out = query(&["-i", "anthill.prelude.PartialEq.{eq}", "eq(1, 1)"]);
    assert_eq!(
        out.code, 0,
        "a builtin must resolve, not block; stderr:\n{}",
        out.stderr
    );
    assert_eq!(
        out.diagnostics("error:").count(),
        0,
        "stderr:\n{}",
        out.stderr
    );
    assert!(
        out.has_stdout_line("1 solution(s)"),
        "stdout:\n{}",
        out.stdout
    );
}

/// A bounded quantifier is a resolver special form (`forall_in` / `some_in`) with
/// no rule or fact, recognised by short name. It must resolve, not be refused —
/// and a quantifier that is FALSE answers `no solutions` (its own empty result),
/// never "unknown functor". (WI-027 is a documented query form.)
#[test]
fn a_bounded_quantifier_is_not_refused() {
    let t = query_props(&["(forall ?x in [1, 2]: base(?x))"]);
    assert_eq!(
        t.code, 0,
        "a true quantifier must resolve; stderr:\n{}",
        t.stderr
    );
    assert!(t.stdout.contains("true"), "stdout:\n{}", t.stdout);

    let f = query_props(&["(some ?x in [999]: base(?x))"]);
    assert_eq!(
        f.code, 0,
        "a false quantifier answers empty, not refused; stderr:\n{}",
        f.stderr
    );
    assert!(f.has_stdout_line("no solutions"), "stdout:\n{}", f.stdout);
    assert_eq!(f.diagnostics("error:").count(), 0, "stderr:\n{}", f.stderr);
}

/// An arity-0 proposition (a bodied rule with no head arguments) resolves through
/// its rule body, sitting in no functor-enumeration table. Resolving FIRST is what
/// answers a TRUE one; the discrim-index backstop is what keeps a FALSE one at
/// `no solutions` instead of refusing a declared predicate as unknown.
#[test]
fn an_arity_0_proposition_is_not_refused() {
    let t = query_props(&["holds"]);
    assert_eq!(
        t.code, 0,
        "a true proposition must resolve; stderr:\n{}",
        t.stderr
    );
    assert!(t.stdout.contains("true"), "stdout:\n{}", t.stdout);

    let f = query_props(&["never"]);
    assert_eq!(
        f.code, 0,
        "a declared-but-false proposition answers empty, not refused; stderr:\n{}",
        f.stderr
    );
    assert!(f.has_stdout_line("no solutions"), "stdout:\n{}", f.stdout);
    assert_eq!(
        f.diagnostics("error:").count(),
        0,
        "a declared proposition must not be refused as unknown; stderr:\n{}",
        f.stderr
    );

    // The control: a genuinely absent proposition IS refused.
    let absent = query_props(&["absent_prop"]);
    assert!(
        is_refused(&absent, "absent_prop"),
        "stderr:\n{}",
        absent.stderr
    );
}

// ── --match mode ────────────────────────────────────────────────────

/// The guard binds `--match` too: browsing for a functor that heads no clause is
/// the same silent zero. Refused identically; the control browses the known one.
#[test]
fn an_unknown_functor_is_refused_under_match() {
    let out = query(&["--match", "nope(row: ?x)"]);
    assert!(
        is_refused(&out, "nope"),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    assert!(
        !out.stdout.contains("result(s)"),
        "no browse output on a refusal; stdout:\n{}",
        out.stdout
    );

    let ok = query(&["--match", "app.util.Q.q(row: ?x)"]);
    assert_eq!(
        ok.code, 0,
        "the browse itself must work; stderr:\n{}",
        ok.stderr
    );
    assert!(ok.has_stdout_line("1 result(s)"), "stdout:\n{}", ok.stdout);
}

// ── multi-query files ───────────────────────────────────────────────

/// An unknown functor in the MIDDLE of a `--query-file` must not abort the run:
/// each pattern is independent, so the pattern AFTER it still runs. The refusal
/// is reported as it is met and the process exits non-zero once all have run —
/// refusing by returning out of the loop would silently drop the tail, the very
/// silent-skip this ticket is about.
#[test]
fn an_unknown_functor_mid_file_does_not_drop_later_queries() {
    let kb = fixtures_dir("wi754").join("props.anthill");
    let qf = fixtures_dir("wi754").join("multi-query.anthill");
    let out = anthill(&[
        "query",
        "-p",
        kb.to_str().unwrap(),
        "--query-file",
        qf.to_str().unwrap(),
    ]);

    assert_eq!(
        out.code, 1,
        "one unknown pattern must make the run fail; stderr:\n{}",
        out.stderr
    );
    assert!(
        out.has_diagnostic("error:", "'nonesuch'"),
        "the unknown middle pattern must be reported; stderr:\n{}",
        out.stderr
    );
    // THE pin: `holds` comes AFTER `nonesuch` in the file, so its presence proves
    // the loop did not abort at the unknown one. (Its header prints only if the
    // loop reached it; the old `?` return would have stopped at `nonesuch`.)
    assert!(
        out.stdout.contains("holds"),
        "the query after the unknown one must still run; stdout:\n{}",
        out.stdout
    );
    // And the one BEFORE it ran too — every pattern is attempted.
    assert!(out.stdout.contains("base(1)"), "stdout:\n{}", out.stdout);
}
