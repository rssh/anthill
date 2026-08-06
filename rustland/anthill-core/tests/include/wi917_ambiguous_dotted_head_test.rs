//! WI-917 — AN AMBIGUOUS HEAD SEGMENT OF A DOTTED PATH IS AN AMBIGUITY, and an ambiguity
//! is refused wherever it is written.
//!
//! WI-907 made a contested WHOLE name terminal and reported it — as a load error at a
//! reference, as a candidate-naming refusal at a query head. Neither half reached the two
//! places this suite covers, and both were DRIVEN through the shipped CLI before the fix:
//!
//!  1. THE DOTTED HEAD. `resolve_dotted_in_kb`'s two rungs BOTH stand down under a
//!     contested head — rung 1 needs one head symbol, rung 2 must not re-root a name the
//!     loader cannot read — and while `Option<Symbol>` was the ladder's answer that was
//!     indistinguishable from a plain miss. So the path fell to the WI-476 bare intern:
//!     `rule r(?x) :- Widget917.w917a(v: ?x)` with two `Widget917`s in scope LOADED CLEAN,
//!     on a position that has an error channel, and `anthill query 'Widget917.w917a(v:
//!     ?x)'` reported "does not resolve to a known functor — no rule, fact, or
//!     declaration is in scope for it": the exact false message WI-907 removed for the
//!     short name, one dot away.
//!
//!  2. THE TOLERATED QUERY POSITIONS. WI-863 deliberately does not descend into a bare
//!     disjunction branch, a quantifier body or a data slot, because "an undefined name
//!     there does not corrupt the correct answer". That argument is about ABSENCE. A
//!     CONTESTED name in those positions silently DROPS solutions instead — measured
//!     through the CLI on a contested name that ANSWERS under either reading: one row
//!     under either import alone, `no solutions` and exit 0 under both
//!     (`wi917_ambiguous_nested_query_name_test`, whose fixture is built for it).
//!
//! WHAT EACH TEST IS FOR. The reference and query tests pin the two reports. The
//! `a_single_import_*` tests are CONTROLS that pass on BOTH sides of the fix: they pin
//! that the head-qualification rung still resolves the identical path once the head names
//! one thing, so a refusal above cannot be the ladder simply having stopped working.
//!
//! STDLIB LOADS: one per `#[test]`.

use anthill_core::intern::ResolveResult;
use anthill_core::kb::extent::ExtentRegError;
use anthill_core::kb::{load, KnowledgeBase};

use crate::common::{
    load_kb_with, mount_extent, query_pattern_term, try_load_kb_with,
};

/// Two namespaces declaring the SAME sort names, so a scope seeing both resolves each
/// HEAD ambiguously. `SortInfo` doubles as an implicit-tier spelling (WI-907's subject),
/// which is what lets the tolerated-position test show a fall-through that ANSWERS rather
/// than one that is merely silent.
const DECLS: &str = r#"
namespace wi917.alpha
  sort Widget917
    entity w917a(v: anthill.prelude.Int64)
  end
  sort SortInfo
    entity si917a(v: anthill.prelude.Int64)
  end
  fact w917a(v: 1)
end

namespace wi917.beta
  sort Widget917
    entity w917b(v: anthill.prelude.Int64)
  end
  sort SortInfo
    entity si917b(v: anthill.prelude.Int64)
  end
end
"#;

/// `DECLS` plus a namespace whose body cites the dotted path — the REFERENCE position,
/// which has a load-error channel. `namespaces` are wildcard-imported into that body, so
/// one import leaves the head unambiguous and two contest it.
fn source_citing_dotted(namespaces: &[&str]) -> String {
    let mut src = DECLS.to_owned();
    src.push_str("namespace wi917.use\n");
    for ns in namespaces {
        src.push_str(&format!("  import {ns}.*\n"));
    }
    src.push_str("  rule r917(?x) :- Widget917.w917a(v: ?x)\nend\n");
    src
}

/// `DECLS` plus TOP-LEVEL wildcard imports — the one way `_global`, the scope a query
/// pattern and a host name are read in, gains a name it does not declare (WI-853).
/// Nothing here REFERENCES a contested name, so the program loads clean and the conflict
/// is live but unreported until a query or a mount names it.
fn kb_importing(namespaces: &[&str]) -> KnowledgeBase {
    let mut src = DECLS.to_owned();
    for ns in namespaces {
        src.push_str(&format!("import {ns}.*\n"));
    }
    load_kb_with(&src)
}

fn global_scope(kb: &mut KnowledgeBase) -> anthill_core::intern::ScopeId {
    kb.global_scope()
}

/// THE DEFECT AT A REFERENCE. Two `Widget917`s in scope, and the citation loaded CLEAN —
/// no diagnostic at all, on the one position that has a channel for one.
#[test]
fn an_ambiguous_dotted_head_at_a_reference_refuses_the_load() {
    let errs = try_load_kb_with(&source_citing_dotted(&["wi917.alpha", "wi917.beta"]))
        .err()
        .expect("`Widget917` names two sorts, so `Widget917.w917a` denotes no one thing");

    let joined = errs.join("\n");
    assert!(
        joined.contains("ambiguous symbol 'Widget917.w917a'"),
        "the refusal must be the AMBIGUITY, named against the path as written; got:\n{joined}",
    );
    for candidate in ["wi917.alpha.Widget917", "wi917.beta.Widget917"] {
        assert!(
            joined.contains(candidate),
            "and it must name `{candidate}`, one of the readings of the contested HEAD — \
             the only segment the ladder resolves, since the tail is appended to whatever \
             the head denotes; got:\n{joined}",
        );
    }
}

/// CONTROL, green on both sides: ONE import leaves the head naming one sort, and the
/// identical path resolves through head-qualification. Without this the test above would
/// also pass if the dotted rung had simply started refusing every path.
#[test]
fn a_single_import_still_resolves_the_identical_dotted_path() {
    let kb = load_kb_with(&source_citing_dotted(&["wi917.alpha"]));

    assert!(
        kb.rules_by_functor_iter(kb.resolve_symbol("wi917.use.r917")).next().is_some(),
        "the citing rule must have loaded, which is what proves the path resolved",
    );
}

/// THE DEFECT AT A QUERY PATTERN, at the verdict the CLI reporter reads
/// (`report_unknown_functor_name` re-reads this ladder to tell an ambiguity from an
/// absence). Pre-fix this answered `NotFound`, and the author of a contested path was
/// told nothing declares the name when two things do.
#[test]
fn an_ambiguous_dotted_head_at_a_query_pattern_reads_as_ambiguous() {
    let mut kb = kb_importing(&["wi917.alpha", "wi917.beta"]);
    let scope = global_scope(&mut kb);

    let verdict = load::resolve_name_in_kb(&kb, "SortInfo.si917a", scope);

    let ResolveResult::Ambiguous(candidates) = verdict else {
        panic!("the ladder must answer AMBIGUOUS, not {verdict:?} — the CLI reports what \
                this returns, and `NotFound` is the false 'nothing is in scope for it'");
    };
    assert_eq!(
        kb.candidate_names(&candidates),
        &["wi917.alpha.SortInfo".to_owned(), "wi917.beta.SortInfo".to_owned()],
    );
}

/// THE HOST-NAME POSITION (WI-908 routed it through the same ladder). A mount takes
/// OWNERSHIP of a functor, so the precision matters more here than anywhere: telling a
/// host that nothing declares its name when two things do sends it to declare a third.
#[test]
fn an_ambiguous_dotted_host_name_is_refused_as_ambiguous_not_absent() {
    let mut kb = kb_importing(&["wi917.alpha", "wi917.beta"]);

    let err = mount_extent(&mut kb, "Widget917.w917a").expect_err(
        "a contested host path denotes no single functor, so there is nothing to mount",
    );

    let ExtentRegError::AmbiguousName { candidates, .. } = &err else {
        panic!("the refusal must be the AMBIGUITY, named; got {err:?}");
    };
    assert_eq!(
        candidates,
        &["wi917.alpha.Widget917".to_owned(), "wi917.beta.Widget917".to_owned()],
    );
}

/// THE TOLERATED POSITIONS (gap 2). WI-863 leaves a bare disjunction branch, a quantifier
/// body and a data slot to resolution because an ABSENT name there costs nothing. A
/// CONTESTED one costs the branch's solutions, silently — so `ambiguous_query_names`
/// walks every node, and each of these is refused.
///
/// Unlike the tests above, this one cannot be run against the pre-fix tree: the walk it
/// asks is NEW, and what existed before was the absence of any caller. The pre-fix
/// measurement is therefore the CLI's, in `wi917_ambiguous_nested_query_name_test`, where
/// these same three patterns exited 0 with no diagnostic.
#[test]
fn a_contested_name_is_found_in_every_position_wi863_tolerates() {
    let mut kb = kb_importing(&["wi917.alpha", "wi917.beta"]);
    let scope = global_scope(&mut kb);
    let contested = kb.resolve_symbol("wi917.alpha.SortInfo");

    for pattern in [
        "push_choice(w917a(v: ?x), SortInfo(name: ?n))", // bare disjunction branch
        "forall_in(?s, nil, tuple(SortInfo(name: ?s)))", // quantifier body
        "w917a(v: SortInfo(name: ?n))",                  // DATA slot, never a goal
    ] {
        let qt = query_pattern_term(&mut kb, pattern);
        let found = kb.ambiguous_query_names(qt, scope);
        assert_eq!(
            found.len(),
            1,
            "`{pattern}` names a contested `SortInfo`, which must be reported wherever it \
             is written; got {:?}",
            found.iter().map(|&s| kb.local_name_of(s).to_owned()).collect::<Vec<_>>(),
        );
        assert_ne!(
            found[0], contested,
            "and the reported symbol is the WI-476 bare intern the pattern actually bound \
             — not one of the candidates, which would be deciding the conflict",
        );
        assert_eq!(kb.local_name_of(found[0]), "SortInfo");
    }
}

/// CONTROL, green on both sides, and the one that keeps WI-863's tolerance intact: an
/// ABSENT name in the same tolerated positions is still NOT reported by this walk. The
/// two diagnoses are the two answers the ladder can give, and widening the descent must
/// not widen WHAT is refused.
#[test]
fn an_absent_name_in_a_tolerated_position_is_still_tolerated() {
    let mut kb = kb_importing(&["wi917.alpha", "wi917.beta"]);
    let scope = global_scope(&mut kb);

    for pattern in [
        "push_choice(w917a(v: ?x), no_such_thing917(?z))",
        "w917a(v: no_such_thing917(?z))",
    ] {
        let qt = query_pattern_term(&mut kb, pattern);
        assert!(
            kb.ambiguous_query_names(qt, scope).is_empty(),
            "`{pattern}` names nothing at all, and WI-863's reason for tolerating that \
             there — the branch has no solutions to lose — still holds",
        );
    }
}
