//! WI-914 — a LISTING MODE's argument is read by THE SAME LADDER as a query pattern.
//!
//! `--mode functor` / `--mode domain` looked their user-supplied argument up by ABSOLUTE
//! name only, while `--mode pattern` resolved the same text at `_global`. So one CLI
//! answered two ways about what a name denotes — the WI-752 headline divergence a layer
//! up — and the losing side reported it as `0 result(s)`: an EMPTY LISTING where the
//! truth was an unreadable name. `-i` was refused outright for every listing mode
//! (WI-853), so the two readings could not even be compared on the same name.
//!
//! `--mode sort` is the DEVIATION, and it is measured here rather than asserted: its
//! argument is the kernel's CLAUSE-KIND TAG (`Sort`/`Fact`/`Rule`/…), interned as raw
//! text by the loader site that files each clause. The ladder answers `NotFound` for
//! every tag, so routing it would not unify the modes — it would break the mode. Pinned
//! from BOTH sides: the tag still lists, and a declared sort name does NOT.
//!
//! The fixture is `wi907`'s: two namespaces declaring the same short names, so one name
//! is unambiguous under one `-i` and contested under two — the only shape that can tell
//! "resolved at `_global`" apart from "looked up absolutely".

mod common;

use common::{anthill, fixtures_dir};

fn query(args: &[&str]) -> common::Output {
    let kb = fixtures_dir("wi907").join("kb.anthill");
    let mut all = vec!["query", "-p", kb.to_str().unwrap()];
    all.extend_from_slice(args);
    anthill(&all)
}

/// One import, so `w907a` / `Widget907` resolve to `wi907.alpha`'s.
fn query_alpha(args: &[&str]) -> common::Output {
    let mut all = vec!["-i", "wi907.alpha.*"];
    all.extend_from_slice(args);
    query(&all)
}

/// Both, so the short names are contested at `_global`.
fn query_both(args: &[&str]) -> common::Output {
    let mut all = vec!["-i", "wi907.alpha.*", "-i", "wi907.beta.*"];
    all.extend_from_slice(args);
    query(&all)
}

fn assert_lists(out: &common::Output, line: &str) {
    assert_eq!(out.code, 0, "stdout:\n{}\nstderr:\n{}", out.stdout, out.stderr);
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
    assert_eq!(out.code, 1, "stdout:\n{}\nstderr:\n{}", out.stdout, out.stderr);
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
    assert_eq!(out.code, 1, "stdout:\n{}\nstderr:\n{}", out.stdout, out.stderr);
    assert!(
        out.has_diagnostic("error:", "'nosuch.ns907' in --mode domain does not resolve to a known domain"),
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
        assert_eq!(out.code, 1, "mode {mode}; stdout:\n{}\nstderr:\n{}", out.stdout, out.stderr);
        assert!(
            out.has_diagnostic("error:", &format!("'Widget907' in --mode {mode} is ambiguous")),
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

// ── `--mode sort`: the deviation, pinned from both sides ────────────────────────

/// The tag still lists. This is the half that a ladder would have broken: `Fact` is
/// declared by nothing and lives in no scope, so `resolve_name_in_global` answers
/// `NotFound` for it.
#[test]
fn a_clause_kind_tag_still_lists() {
    let out = query(&["--mode", "sort", "Fact"]);
    assert_lists(&out, "w907a(v: 1)");
}

/// The other half — and the reason the deviation is stated rather than assumed. A
/// DECLARED SORT is not a clause-kind tag, and asking for one printed `0 result(s)`: the
/// tool answering "this sort has no facts" about a sort that has one. Both spellings,
/// because the pre-fix mode reached them by two different lookups and only a rule that
/// covers both is a rule.
#[test]
fn a_declared_sort_name_is_not_a_clause_kind_tag() {
    for name in ["Widget907", "wi907.alpha.Widget907"] {
        let out = query(&["--mode", "sort", name]);
        assert_eq!(out.code, 1, "{name}; stdout:\n{}\nstderr:\n{}", out.stdout, out.stderr);
        assert!(
            out.has_diagnostic("error:", &format!("'{name}' names no clause")),
            "{name}; stderr:\n{}",
            out.stderr
        );
        assert!(
            out.has_diagnostic("error:", "not a way to list a declared sort's facts"),
            "the refusal must say what the mode DOES list; stderr:\n{}",
            out.stderr
        );
        assert!(
            !out.stdout.contains("0 result(s)"),
            "the old silent empty is exactly what must not survive; stdout:\n{}",
            out.stdout
        );
    }

    // The control the refusal exists for: `--mode pattern` DOES reach that sort's facts.
    let pattern = query_alpha(&["w907a(v: ?x)"]);
    assert!(pattern.has_stdout_line("?x = 1"), "stdout:\n{}", pattern.stdout);
}

/// `-i` stays refused for `--mode sort` alone — its argument is not resolved in any
/// scope, so an import cannot bear on it, and WI-853's rule is that an inert flag is
/// refused rather than ignored. The refusal now says WHY, and no longer claims the rule
/// for the two modes where the flag is live.
#[test]
fn an_import_flag_is_refused_for_the_tag_mode_only() {
    let refused = query_alpha(&["--mode", "sort", "Fact"]);
    assert_eq!(refused.code, 1, "stdout:\n{}", refused.stdout);
    assert!(
        refused.has_diagnostic("error:", "--import does not apply to --mode sort"),
        "stderr:\n{}",
        refused.stderr
    );

    // The control: the same flag on the two modes that DO name into `_global`.
    for mode in ["functor", "domain"] {
        let ok = query_alpha(&["--mode", mode, "Widget907"]);
        assert_eq!(
            ok.code, 0,
            "`-i` must be accepted by --mode {mode}; stdout:\n{}\nstderr:\n{}",
            ok.stdout, ok.stderr
        );
    }
}
