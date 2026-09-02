//! WI-914 — a LISTING MODE's argument is read by THE SAME LADDER as a query pattern.
//!
//! `--mode functor` / `--mode domain` looked their user-supplied argument up by ABSOLUTE
//! name only, while `--mode pattern` resolved the same text at `<global>`. So one CLI
//! answered two ways about what a name denotes — the WI-752 headline divergence a layer
//! up — and the losing side reported it as `0 result(s)`: an EMPTY LISTING where the
//! truth was an unreadable name. `-i` was refused outright for every listing mode
//! (WI-853), so the two readings could not even be compared on the same name.
//!
//! `--mode sort` was the DEVIATION — its argument was the kernel's CLAUSE-KIND TAG
//! (`Fact`/`Rule`/`Sort`/…), raw-interned by the loader site that files each clause, so
//! the ladder answered `NotFound` for every one. WI-921 DELETED the mode rather than
//! exempt or rename it, so every MODE `query` still has reads its argument through the
//! ladder. Not every ARGUMENT: `--mode domain <global>` is still a raw intern (WI-923).
//!
//! The fixture is `wi907`'s: two namespaces declaring the same short names, so one name
//! is unambiguous under one `-i` and contested under two — the only shape that can tell
//! "resolved at `<global>`" apart from "looked up absolutely".

use crate::common::{anthill, fixtures_dir};

fn query(args: &[&str]) -> crate::common::Output {
    let kb = fixtures_dir("wi907").join("kb.anthill");
    let mut all = vec!["query", "-p", kb.to_str().unwrap()];
    all.extend_from_slice(args);
    anthill(&all)
}

/// One import, so `w907a` / `Widget907` resolve to `wi907.alpha`'s.
fn query_alpha(args: &[&str]) -> crate::common::Output {
    let mut all = vec!["-i", "wi907.alpha.*"];
    all.extend_from_slice(args);
    query(&all)
}

/// Both, so the short names are contested at `<global>`.
fn query_both(args: &[&str]) -> crate::common::Output {
    let mut all = vec!["-i", "wi907.alpha.*", "-i", "wi907.beta.*"];
    all.extend_from_slice(args);
    query(&all)
}

fn assert_lists(out: &crate::common::Output, line: &str) {
    assert_eq!(
        out.code, 0,
        "stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.lines().any(|l| l.trim() == line),
        "expected the listing to contain `{line}`; stdout:\n{}",
        out.stdout
    );
}

// ── THE ACCEPTANCE: the two modes agree on what a name denotes ──────────────────

/// The headline. `--mode functor w907a` under `-i` names what `--mode pattern
/// 'w907a(v: ?x)'` names under the same `-i` — the same fact, off the same symbol. Before
/// WI-914 the first was unaskable (`-i` refused) and, asked without the flag, answered
/// `0 result(s)`.
#[test]
fn a_short_functor_name_denotes_what_the_same_text_denotes_in_a_pattern() {
    let listing = query_alpha(&["--mode", "functor", "w907a"]);
    assert_lists(&listing, "w907a(v: 1)");

    let pattern = query_alpha(&["w907a(v: ?x)"]);
    assert_eq!(pattern.code, 0, "stderr:\n{}", pattern.stderr);
    assert!(
        pattern.has_stdout_line("?x = 1"),
        "the control: the pattern resolves the same text to the same fact; stdout:\n{}",
        pattern.stdout
    );
}

/// The absolute spelling keeps working — the ladder's dotted rungs answer it. Without
/// this the test above would also pass if `--mode functor` had simply started resolving
/// short names and lost paths.
#[test]
fn the_absolute_spelling_still_denotes_the_same_functor() {
    let out = query(&["--mode", "functor", "wi907.alpha.Widget907.w907a"]);
    assert_lists(&out, "w907a(v: 1)");
}

/// A domain is a declared symbol (a namespace, or a sort), so it reads the same way:
/// `Widget907` under one import is `wi907.alpha`'s sort-domain.
#[test]
fn a_short_domain_name_resolves_at_global_too() {
    let short = query_alpha(&["--mode", "domain", "Widget907"]);
    let absolute = query(&["--mode", "domain", "wi907.alpha.Widget907"]);
    assert_eq!(short.code, 0, "stderr:\n{}", short.stderr);
    assert_eq!(
        short.stdout, absolute.stdout,
        "the short name under `-i` and the path must list the SAME domain"
    );
}

// ── Both non-`Found` answers are refusals, not empty listings ───────────────────

/// A name nothing declares was reported as `0 result(s)` — an empty listing, which is
/// what a KNOWN functor with no clauses says. The two are different answers and now read
/// differently.
#[test]
fn an_absent_functor_name_is_refused_not_reported_as_an_empty_listing() {
    let out = query(&["--mode", "functor", "NoSuch907"]);
    assert_eq!(
        out.code, 1,
        "stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.has_diagnostic("error:", "'NoSuch907' in --mode functor does not resolve"),
        "stderr:\n{}",
        out.stderr
    );
    assert!(
        !out.stdout.contains("result(s)"),
        "a refused listing must not also print a count; stdout:\n{}",
        out.stdout
    );
}

/// Same for a domain, and the noun follows the position: an author who asked for a domain
/// is not told their name is not a known FUNCTOR.
#[test]
fn an_absent_domain_name_is_refused_as_a_domain() {
    let out = query(&["--mode", "domain", "nosuch.ns907"]);
    assert_eq!(
        out.code, 1,
        "stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.has_diagnostic(
            "error:",
            "'nosuch.ns907' in --mode domain does not resolve to a known domain"
        ),
        "stderr:\n{}",
        out.stderr
    );
}

/// An AMBIGUITY ends the ladder here as everywhere (§8.6, WI-907): the same name that
/// listed under one import is refused under two, naming both candidates. Silently picking
/// one would decide in the author's favour a conflict they have to see — and the pre-fix
/// absolute lookup could not even represent the question.
#[test]
fn a_contested_listing_name_is_refused_with_its_candidates() {
    for mode in ["functor", "domain"] {
        let out = query_both(&["--mode", mode, "Widget907"]);
        assert_eq!(
            out.code, 1,
            "mode {mode}; stdout:\n{}\nstderr:\n{}",
            out.stdout, out.stderr
        );
        assert!(
            out.has_diagnostic(
                "error:",
                &format!("'Widget907' in --mode {mode} is ambiguous")
            ),
            "mode {mode}; stderr:\n{}",
            out.stderr
        );
        for c in ["wi907.alpha.Widget907", "wi907.beta.Widget907"] {
            assert!(
                out.has_diagnostic("error:", c),
                "mode {mode} must name candidate `{c}`; stderr:\n{}",
                out.stderr
            );
        }
    }
}

// ── `--mode sort` is gone (WI-921) ──────────────────────────────────────────────

/// The deletion, pinned where the deviation used to be pinned. `sort` is refused by
/// ARGUMENT PARSING — exit 2, not the 1 a command that ran and failed returns — so a
/// script still passing it stops instead of silently listing something else. The
/// refusal must also enumerate what remains: a user who wanted the mode's tag listing
/// has no replacement, and one who wanted a declared sort's clauses never had the mode
/// they thought they had.
#[test]
fn the_sort_mode_no_longer_exists() {
    let out = query(&["--mode", "sort", "Fact"]);
    assert_eq!(
        out.code, 2,
        "stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.has_diagnostic("error:", "invalid value 'sort'"),
        "the refusal must name the rejected value; stderr:\n{}",
        out.stderr
    );
    // Not `has_diagnostic`: clap prints `[possible values: …]` on its own
    // continuation line, which carries no `error:` prefix to key on.
    assert!(
        out.stderr.contains("pattern")
            && out.stderr.contains("functor")
            && out.stderr.contains("domain"),
        "and enumerate the modes that survive; stderr:\n{}",
        out.stderr
    );
    assert!(
        !out.stdout.contains("result(s)"),
        "a refused mode must not print a listing; stdout:\n{}",
        out.stdout
    );
}

/// What the deleted mode was reached for is still reachable, by the dimensions that do
/// exist — the control that the deletion removed a NAME, not a capability. "A declared
/// sort's clauses" is `head functor ∈ constructors(S)`, a family in the FUNCTOR
/// dimension, so it is two steps: discover the constructors, then list off one.
///
/// The discovery step runs WITHOUT `-i`, and WI-909 changed the reason — this paragraph
/// said the fixture "declares its own `SortInfo` in both namespaces … Unimported, the
/// head resolves to the implicit tier's", and both halves are now false. The fixture
/// declares `cons`, not `SortInfo` (WI-907's tier-collision subject moved with the tier
/// itself), and the pattern below is written FULLY QUALIFIED, so it names
/// `anthill.reflect.SortInfo` outright and never reaches a rung at all. No `-i` is
/// needed because nothing is being brought into scope; the qualified spelling is also
/// what keeps a user sort of the same name from answering in its place, which is the
/// property the old reasoning was reaching for. Found by `/code-review`.
/// WI-1047 — `--max-results 0` (unlimited) since `query` began loading the stdlib. The
/// reflection listing now answers with the stdlib's own `SortInfo` rows as well as this
/// fixture's, and at the default cap of 100 the fixture's row fell off the end. The
/// assertion is a `contains`, so the cap was the only thing in its way; raising it keeps
/// what this test measures (the row is REACHABLE) rather than what the cap happens to
/// admit.
#[test]
fn a_declared_sorts_clauses_are_reachable_without_the_mode() {
    let sorts = query(&[
        "--max-results",
        "0",
        "--match",
        // WI-909: qualified, because the eight reflection result sorts left the
        // implicit tier and a bare `SortInfo` in a query pattern now resolves to
        // nothing. `-i anthill.reflect.*` would do as well; the qualified spelling is
        // chosen because it needs no flag plumbing and says which sort is meant.
        "anthill.reflect.SortInfo(name: ?s, constructors: ?c)",
    ]);
    assert_eq!(sorts.code, 0, "stderr:\n{}", sorts.stderr);
    assert!(
        sorts.stdout.contains("[w907a]"),
        "the reflection listing must expose `Widget907`'s constructor list; stdout:\n{}",
        sorts.stdout
    );

    // And then the clauses, off that constructor.
    let listing = query_alpha(&["--mode", "functor", "w907a"]);
    assert_lists(&listing, "w907a(v: 1)");
}

/// `-i` is accepted by EVERY listing mode — previously this asserted the refusal for
/// `--mode sort` and kept these as its control; the control is now the whole claim.
/// Pattern mode's half is pinned harder by the headline test above (`?x = 1`, not just
/// exit 0), so it is not re-run here.
#[test]
fn an_import_flag_applies_to_every_mode() {
    for mode in ["functor", "domain"] {
        let ok = query_alpha(&["--mode", mode, "Widget907"]);
        assert_eq!(
            ok.code, 0,
            "`-i` must be accepted by --mode {mode}; stdout:\n{}\nstderr:\n{}",
            ok.stdout, ok.stderr
        );
    }
}
