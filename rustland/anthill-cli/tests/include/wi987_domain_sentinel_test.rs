//! WI-987 — the CLI half: `--mode domain`'s ONE reserved argument no longer collides
//! with a name a user may declare.
//!
//! `run_query`'s Domain arm matches the reserved spelling BEFORE consulting the ladder
//! (a fallback would re-admit every unresolvable name — see that arm). While the
//! spelling was `_global`, that made a legal `namespace _global` unreachable through the
//! only name it has: the arm answered with the loader's tag instead, and the ladder was
//! never asked. Now the tag is `<global>`, which no declaration can take, so the two
//! questions are separate ones.
//!
//! CONTROL, MEASURED — put `intern::GLOBAL_SCOPE_NAME` back to `"_global"` and ALL
//! THREE fail, each on its own half of the collision:
//!   - `a_declared_global_namespace_is_listable_by_its_own_name`: the arm captures the
//!     argument again, so the listing is the TOP LEVEL's and the declared namespace's
//!     clause is absent — the defect itself, driven.
//!   - `the_reserved_spelling_lists_the_top_level_clauses`: `<global>` is then no
//!     reserved spelling, so it falls to the ladder and is refused (exit 1). This case
//!     exists to assert the hint's advice WORKS rather than merely prints, and it turns
//!     out to discriminate too.
//!   - `an_unresolvable_domain_is_told_how_to_name_the_top_level`: the hint still
//!     prints, naming `'_global'` — advice for a spelling a user's own declaration can
//!     take, which is the thing that could not be said correctly before.

use crate::common::{anthill, fixtures_dir};

/// `--no-stdlib` because this file asserts WHICH OF TWO SCOPES a clause is filed under,
/// and the stdlib files hundreds of its own metadata facts under the top-level one — with
/// it loaded, the `<global>` listing is the stdlib's and the fixture's row falls off the
/// end of the default result cap (measured: that is how this test first failed). The
/// fixture needs nothing from the prelude, so dropping it costs no coverage and makes
/// each listing exactly the clauses under test.
fn query(args: &[&str]) -> crate::common::Output {
    let kb = fixtures_dir("wi987").join("kb.anthill");
    let mut all = vec!["query", "--no-stdlib", "-p", kb.to_str().unwrap()];
    all.extend_from_slice(args);
    anthill(&all)
}

/// THE WI-987 acceptance for this position: the declared namespace answers for its own
/// name, with ITS clause — not the top level's.
#[test]
fn a_declared_global_namespace_is_listable_by_its_own_name() {
    let out = query(&["--mode", "domain", "_global"]);
    assert_eq!(
        out.code, 0,
        "`namespace _global` is an ordinary domain; stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.has_stdout_line("inside987(v: 2)"),
        "the DECLARED `_global`'s clause must be listed; stdout:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("outside987"),
        "the top-level clause belongs to the OTHER scope; stdout:\n{}",
        out.stdout
    );
}

/// The reserved argument still reaches the clauses no namespace owns.
#[test]
fn the_reserved_spelling_lists_the_top_level_clauses() {
    let out = query(&["--mode", "domain", "<global>"]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert!(
        out.has_stdout_line("outside987(v: 1)"),
        "the top-level clause must be listed; stdout:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("inside987"),
        "the declared namespace's clause belongs to the OTHER scope; stdout:\n{}",
        out.stdout
    );
}

/// A name the ladder cannot bind gets the reserved spelling NAMED. Without it the
/// absence message offers only qualify/import, neither of which can reach a scope no
/// declaration owns — and the user has no other way to learn the spelling, or that it
/// needs quoting.
#[test]
fn an_unresolvable_domain_is_told_how_to_name_the_top_level() {
    let out = query(&["--mode", "domain", "nosuch987"]);
    assert_eq!(out.code, 1, "stdout:\n{}", out.stdout);
    assert!(
        out.has_diagnostic("error:", "--mode domain '<global>'"),
        "the refusal must name the reserved spelling, quoted; stderr:\n{}",
        out.stderr
    );
}
