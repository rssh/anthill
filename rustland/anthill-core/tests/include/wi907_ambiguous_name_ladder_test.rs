//! WI-907 — AN AMBIGUITY ENDS THE NAME LADDER.
//!
//! The lower rungs (`resolve_dotted_in_kb`, then the implicit tier) exist for a name that
//! means NOTHING at this scope. A name that means SEVERAL things has an answer already,
//! and `load::resolve_name_in_kb` used to descend past it — so the positions with no
//! load-error channel (a QUERY pattern, a HOST-supplied mount name) silently took a
//! symbol that was not even among the candidates.
//!
//! MEASURED before the fix, through the shipped `anthill query`: two wildcard-imported
//! user sorts named `SortInfo` made the bare name ambiguous at `_global`, and
//! `SortInfo(name: ?n)` answered FOUR rows out of `anthill.reflect.SortInfo` — the
//! implicit tier those very declarations had already shadowed. Adding the SECOND import,
//! which makes the name strictly more contested, is what brought the shadowed reading
//! back; with one import the query was correctly empty.
//!
//! WHAT EACH TEST IS FOR. The first pins the stop. The next two are CONTROLS that pass on
//! BOTH sides of the fix: they pin the two answers the stop must not disturb — a single
//! import still shadows the tier, and an unshadowed tier name still resolves. The last
//! carries the rule to the host-name position, where the wrong symbol was not merely
//! queried but MOUNTED.
//!
//! The user-visible half — that the CLI now names the candidates instead of reporting
//! "no rule, fact, or declaration is in scope for it" — is `anthill-cli`'s
//! `wi907_ambiguous_query_name_test`.
//!
//! STDLIB LOADS: four, one per `#[test]`. The implicit tier answers only when its target
//! is LOADED (WI-900), so no claim here can be made in a bare KB.

use anthill_core::kb::extent::ExtentRegError;
use anthill_core::kb::KnowledgeBase;

use crate::common::{load_kb_with, mount_extent, query_pattern_functor};

/// Two namespaces declaring the SAME two short names, so a scope that sees both resolves
/// each one ambiguously. `SortInfo` and `SortView` are both implicit-tier spellings
/// (`load::PRELUDE_QUALIFIED`'s reflection result sorts) — the tier is what the ladder
/// used to fall through TO, so a collision with it is the sharpest subject.
///
/// The two are not interchangeable, and the difference is a mount detail: reflect's
/// `SortInfo` carries resident facts, so mounting it is refused as a `ResidentCollision`
/// before the ladder question is reached (WI-908 measured this). `SortView` carries none.
/// So the query tests use `SortInfo` (whose tier target ANSWERS, making the fall-through
/// visible as solutions) and the mount test uses `SortView`.
const DECLS: &str = r#"
namespace wi907.alpha
  sort SortInfo
    entity si907a(v: anthill.prelude.Int64)
  end
  sort SortView
    entity sv907a(v: anthill.prelude.Int64)
  end
end

namespace wi907.beta
  sort SortInfo
    entity si907b(v: anthill.prelude.Int64)
  end
  sort SortView
    entity sv907b(v: anthill.prelude.Int64)
  end
end
"#;

/// A wildcard import is the one way `_global` — the scope a query pattern and a host
/// name are read in — gains a name it does not declare itself. Two of them is what makes
/// a name ambiguous THERE.
///
/// WI-995 — supplied through the INVOCATION (`-i <ns>.*`, the CLI spelling this fixture
/// has always been modelling) rather than written as a top-level import in the program
/// source. Since imports became file-local, a program file's import is local to that
/// file and does not reach a query pattern or a host name, which have no file; the `-i`
/// channel is the one that does. The subject is unchanged — two wildcard imports still
/// make the short name ambiguous at `_global` — only the channel is named honestly.
fn kb_importing(namespaces: &[&str]) -> KnowledgeBase {
    // Panics on a load error, which is half the fixture's claim: nothing here REFERENCES
    // the contested name, so the program loads clean and the ambiguity is live but
    // unreported. That is why the query position had to decide it at all.
    let mut kb = load_kb_with(DECLS);
    let specs: Vec<String> = namespaces.iter().map(|ns| format!("{ns}.*")).collect();
    let refs: Vec<&str> = specs.iter().map(String::as_str).collect();
    crate::common::supply_invocation_imports(&mut kb, &refs);
    kb
}

/// THE DEFECT. `SortInfo` names two user sorts at `_global` and the implicit tier's
/// `anthill.reflect.SortInfo`; the loader is on record as unable to choose between the
/// first two, so the one thing the query must not do is answer as the third.
#[test]
fn an_ambiguous_query_name_does_not_fall_through_to_the_implicit_tier() {
    let mut kb = kb_importing(&["wi907.alpha", "wi907.beta"]);
    let tier = kb.resolve_symbol("anthill.reflect.SortInfo");
    assert!(
        kb.rules_by_functor_iter(tier).next().is_some(),
        "control: the tier target must carry clauses, or binding it would be inert and \
         this test would pass for the wrong reason — pre-fix this query ANSWERED",
    );

    let bound = query_pattern_functor(&mut kb, "SortInfo(name: ?n)");

    assert_ne!(
        bound, tier,
        "the ladder must STOP at the ambiguity: `anthill.reflect.SortInfo` is not even \
         among the candidates the name is ambiguous between",
    );
    assert!(
        kb.kind_of(bound).is_none(),
        "and what is left must be the WI-476 bare intern — a symbol that DECLARES \
         nothing, which also rules out picking one of the two candidates (deciding the \
         conflict in the author's favour is the same fault with a nearer symbol). It \
         heads no clause, so the query matches nothing and the CLI's reporter gets its \
         chance to name the candidates",
    );
}

/// CONTROL, green on both sides: ONE import leaves the name unambiguous, and a user
/// declaration in scope still shadows the implicit tier. Without this the test above
/// would also pass if the fix had simply broken the tier for every short name.
#[test]
fn a_single_import_still_shadows_the_implicit_tier() {
    let mut kb = kb_importing(&["wi907.alpha"]);

    let bound = query_pattern_functor(&mut kb, "SortInfo(name: ?n)");

    assert_eq!(
        bound,
        kb.resolve_symbol("wi907.alpha.SortInfo"),
        "one import resolves the name outright, and a name in scope outranks the tier",
    );
}

/// CONTROL, green on both sides: with NOTHING shadowing it the tier still answers. This
/// is the rung the fix stops descending TO, and it must keep working for the names it is
/// for — a bare `SortInfo` / `cons` / `eq` in a reflection query (WI-040 / WI-521).
#[test]
fn an_unshadowed_implicit_tier_name_still_binds_its_target() {
    let mut kb = kb_importing(&[]);

    let bound = query_pattern_functor(&mut kb, "SortInfo(name: ?n)");

    assert_eq!(
        bound,
        kb.resolve_symbol("anthill.reflect.SortInfo"),
        "no user declaration is in scope at `_global`, so the tier is the answer",
    );
}

/// THE HOST-NAME POSITION, where the fall-through did not merely answer a query but took
/// OWNERSHIP of a functor: `register_extent_owner` mounted the tier's
/// `anthill.reflect.SortView` for a host that named a contested `SortView`.
///
/// The refusal must be AMBIGUOUS, not `UnresolvableName`: they are opposite faults, and
/// telling an author that nothing declares the name when two things do sends them to
/// declare a third. (The `internal` half of this precision is WI-911's.)
#[test]
fn an_ambiguous_host_name_is_refused_as_ambiguous_not_absent() {
    let mut kb = kb_importing(&["wi907.alpha", "wi907.beta"]);

    let err = mount_extent(&mut kb, "SortView").expect_err(
        "a contested host name denotes no single functor, so there is nothing to mount \
         — pre-fix this mounted the tier's `anthill.reflect.SortView`",
    );

    let ExtentRegError::AmbiguousName { candidates, .. } = &err else {
        panic!("the refusal must be the AMBIGUITY, named; got {err:?}");
    };
    assert_eq!(
        candidates,
        &[
            "wi907.alpha.SortView".to_owned(),
            "wi907.beta.SortView".to_owned()
        ],
        "and it must name what it could not choose between",
    );
}
