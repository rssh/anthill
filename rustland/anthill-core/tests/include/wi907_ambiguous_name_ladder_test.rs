//! WI-907 — AN AMBIGUITY ENDS THE NAME LADDER.
//!
//! The lower rungs (`resolve_dotted_in_kb`, then the implicit tier) exist for a name that
//! means NOTHING at this scope. A name that means SEVERAL things has an answer already,
//! and `load::resolve_name_in_kb` used to descend past it — so the positions with no
//! load-error channel (a QUERY pattern, a HOST-supplied mount name) silently took a
//! symbol that was not even among the candidates.
//!
//! MEASURED before the fix, through the shipped `anthill query`: two wildcard-imported
//! user sorts named `SortInfo` made the bare name ambiguous at `<global>`, and
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
/// each one ambiguously. Both are implicit-tier spellings (`load::PRELUDE_QUALIFIED`) —
/// the tier is what the ladder used to fall through TO, so a collision with it is the
/// sharpest subject, and a name NOT on the tier would make every row here vacuous.
///
/// `cons` / `nil` SINCE WI-909, which emptied the tier of everything but the four
/// constructors. This fixture declared `SortInfo` / `SortView`, chosen when the eight
/// reflection result sorts were tier entries; with those gone the collision they modelled
/// could not happen, and — worse — the central row below would have gone on PASSING,
/// because a ladder with no rung to fall to cannot fall through. Repointed rather than
/// deleted: the RULE (an ambiguity ends the ladder) is unchanged and still needs an
/// instrument.
///
/// ONE PROPERTY OF THE OLD PAIR IS GONE, said here rather than quietly dropped. `SortInfo`
/// carried resident facts and `SortView` did not, which is why the query rows used one and
/// the mount row the other (mounting a resident-fact target is refused as a
/// `ResidentCollision` before the ladder question is reached — WI-908 measured that). No
/// remaining tier name carries clauses at all, so the two are interchangeable now and the
/// split is kept only so each row keeps a name of its own. The resident-fact half belongs
/// to WI-908's own rows.
const DECLS: &str = r#"
namespace wi907.alpha
  sort cons
    entity si907a(v: anthill.prelude.Int64)
  end
  sort nil
    entity sv907a(v: anthill.prelude.Int64)
  end
end

namespace wi907.beta
  sort cons
    entity si907b(v: anthill.prelude.Int64)
  end
  sort nil
    entity sv907b(v: anthill.prelude.Int64)
  end
end
"#;

/// A wildcard import is the one way `<global>` — the scope a query pattern and a host
/// name are read in — gains a name it does not declare itself. Two of them is what makes
/// a name ambiguous THERE.
///
/// WI-995 — supplied through the INVOCATION (`-i <ns>.*`, the CLI spelling this fixture
/// has always been modelling) rather than written as a top-level import in the program
/// source. Since imports became file-local, a program file's import is local to that
/// file and does not reach a query pattern or a host name, which have no file; the `-i`
/// channel is the one that does. The subject is unchanged — two wildcard imports still
/// make the short name ambiguous at `<global>` — only the channel is named honestly.
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

/// THE DEFECT. The contested name denotes two user sorts at `<global>` AND the implicit
/// tier's target; the loader is on record as unable to choose between the first two, so
/// the one thing the query must not do is answer as the third. (Measured on `SortInfo`
/// when that was a tier spelling; `cons` since WI-909 — see [`DECLS`].)
#[test]
fn an_ambiguous_query_name_does_not_fall_through_to_the_implicit_tier() {
    let mut kb = kb_importing(&["wi907.alpha", "wi907.beta"]);
    // THE TIER-SPECIFIC HALF OF THIS ROW IS GONE (WI-909's third pass emptied
    // `PRELUDE_QUALIFIED`), and it is removed rather than reworded. It used to assert
    // `bound != tier` -- that the ladder did not DESCEND past the ambiguity into the
    // implicit rung -- guarded by a control showing the rung would otherwise have
    // answered. With no rung there is nothing to descend to, so both the assertion and
    // its control now hold by construction. Keeping them would be exactly the vacuous
    // control this file exists to warn about.
    //
    // WHAT SURVIVES IS THE HARDER HALF, and it is untouched by the removal: the ladder
    // must bind NEITHER CANDIDATE. Picking one would decide the conflict in the author's
    // favour -- "the same fault with a nearer symbol" -- and that is still reachable,
    // still wrong, and still what the assertion below measures.
    let bound = query_pattern_functor(&mut kb, "cons(?h, ?t)");

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

    let bound = query_pattern_functor(&mut kb, "cons(?h, ?t)");

    assert_eq!(
        bound,
        kb.resolve_symbol("wi907.alpha.cons"),
        "one import resolves the name outright, and a name in scope outranks the tier",
    );
}

/// INVERTED IN WI-909's THIRD PASS. This was the file's CONTROL -- green on both sides of
/// WI-907, pinning that the rung the fix stopped descending TO still answered for the
/// names it was for. `PRELUDE_QUALIFIED` is empty now, so there is no such rung and no
/// such name: an unshadowed bare short name at `<global>` binds NOTHING.
///
/// It is kept, inverted, because it is the counterpart of the row above and the two must
/// be read together: that row says an AMBIGUOUS name binds neither candidate, this one
/// says an UNCONTESTED one binds nothing either. Together they say the query position
/// has no fallback left, which is the whole of WI-909.
#[test]
fn an_unshadowed_short_name_now_binds_nothing() {
    let mut kb = kb_importing(&[]);

    let bound = query_pattern_functor(&mut kb, "cons(?h, ?t)");

    assert!(
        kb.kind_of(bound).is_none(),
        "with the tier empty a bare `cons` reaches no declaration, so the pattern gets \
         the WI-476 bare intern -- a symbol that declares nothing and heads no clause",
    );
    assert_eq!(
        crate::common::query_pattern_functor_qn(&mut kb, "anthill.prelude.List.cons(?h, ?t)"),
        "anthill.prelude.List.cons",
        "control: the ladder is intact -- the QUALIFIED name still binds, so the row \
         above measures the missing rung and not a broken query position",
    );
}

/// THE HOST-NAME POSITION, where the fall-through did not merely answer a query but took
/// OWNERSHIP of a functor: `register_extent_owner` mounted the tier's target for a host
/// that named a contested short name. (Measured on `SortView` when that was a tier
/// spelling; the name here is `nil` since WI-909 — see [`DECLS`].)
///
/// The refusal must be AMBIGUOUS, not `UnresolvableName`: they are opposite faults, and
/// telling an author that nothing declares the name when two things do sends them to
/// declare a third. (The `internal` half of this precision is WI-911's.)
#[test]
fn an_ambiguous_host_name_is_refused_as_ambiguous_not_absent() {
    let mut kb = kb_importing(&["wi907.alpha", "wi907.beta"]);

    let err = mount_extent(&mut kb, "nil").expect_err(
        "a contested host name denotes no single functor, so there is nothing to mount \
         — pre-fix this mounted the tier's target for it",
    );

    let ExtentRegError::AmbiguousName { candidates, .. } = &err else {
        panic!("the refusal must be the AMBIGUITY, named; got {err:?}");
    };
    assert_eq!(
        candidates,
        &[
            "wi907.alpha.nil".to_owned(),
            "wi907.beta.nil".to_owned()
        ],
        "and it must name what it could not choose between",
    );
}
