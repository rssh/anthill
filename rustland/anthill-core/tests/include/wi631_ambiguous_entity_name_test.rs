//! WI-631: unique-or-loud short-name entity resolution.
//!
//! `KnowledgeBase::resolve_entity_functor` resolves a short entity name ONLY
//! when it is unique across the field-types registry; a short name declared
//! by several sorts' constructors comes back
//! [`ResolveResult::Ambiguous`] with the candidates in qualified-name
//! order, so every consumer surface fails loudly (naming the candidates and
//! asking for a qualified name) instead of silently answering with an
//! arbitrary sort's schema — the WI-515 tie-break this replaces picked the
//! minimal qualified name. Exact qualified-name resolution is unaffected.

use anthill_core::intern::ResolveResult;

use crate::common::load_kb_with;

/// Two sorts each declare a constructor named `dup` — a genuinely ambiguous
/// short name (the stdlib analog is `guarded` in `anthill.prelude` vs
/// `anthill.reflect.LogicalQuery`).
const DUP: &str = r#"
namespace test.wi631
  sort Alpha
    entity dup(x: Int64)
  end
  sort Beta
    entity dup(y: String)
  end
end
"#;

#[test]
fn ambiguous_short_name_is_reported_not_picked() {
    let kb = load_kb_with(DUP);
    match kb.resolve_entity_functor("dup") {
        ResolveResult::Ambiguous(candidates) => {
            let names: Vec<&str> = candidates
                .iter()
                .map(|&s| kb.qualified_name_of(s))
                .collect();
            assert_eq!(
                names,
                vec!["test.wi631.Alpha.dup", "test.wi631.Beta.dup"],
                "both candidates, in qualified-name order"
            );
            let msg = kb.ambiguous_entity_message("dup", &candidates);
            assert!(
                msg.contains("test.wi631.Alpha.dup") && msg.contains("test.wi631.Beta.dup"),
                "the diagnostic names every candidate: {msg}"
            );
        }
        other => panic!("a short name declared by two sorts must be Ambiguous, got {other:?}"),
    }
}

#[test]
fn qualified_name_resolves_despite_short_name_ambiguity() {
    let kb = load_kb_with(DUP);
    match kb.resolve_entity_functor("test.wi631.Beta.dup") {
        ResolveResult::Found(sym) => {
            assert_eq!(kb.qualified_name_of(sym), "test.wi631.Beta.dup");
        }
        other => panic!("an exact qualified name must stay Found, got {other:?}"),
    }
}

#[test]
fn unique_short_name_still_resolves() {
    let kb = load_kb_with(
        r#"
namespace test.wi631u
  sort Solo
    entity only_here(v: Int64)
  end
end
"#,
    );
    match kb.resolve_entity_functor("only_here") {
        ResolveResult::Found(sym) => {
            assert_eq!(kb.qualified_name_of(sym), "test.wi631u.Solo.only_here");
        }
        other => panic!("a unique short name must resolve, got {other:?}"),
    }
    assert_eq!(
        kb.resolve_entity_functor("nowhere"),
        ResolveResult::NotFound,
        "an unregistered name is NotFound"
    );
}
