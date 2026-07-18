//! WI-458: an error's SOURCE SPAN for a fact/rule head must key on the head
//! OCCURRENCE (its `RuleId`), not the hash-consed head `TermId`.
//!
//! The head span side-table (`term_spans`) keys on the interned head `TermId`
//! with first-write-wins. Two facts written in DIFFERENT namespaces whose heads
//! intern to the SAME `TermId` — a bare ad-hoc predicate short-name-interns
//! identically, and identical literal args hash-cons — but carry DIFFERENT
//! domains are NOT deduped (`assert_fact`'s key is `(term, sort, domain)`), so
//! they get distinct `RuleId`s while sharing one `term_spans` entry. A head
//! error about the SECOND fact would then print the FIRST file's location.
//!
//! The fix records each head's span keyed by its `RuleId` (`rule_head_span`),
//! which is unique per stored fact/rule and so cannot cross-file-alias.

use anthill_core::parse;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};

/// Two files, two namespaces, byte-identical fact HEAD (`enabled(feature: "x")`).
/// `enabled` is an undeclared ad-hoc predicate, so it short-name-interns to the
/// same functor symbol in both files; the `"x"` literal hash-conses; hence one
/// shared head `TermId`. The namespaces differ, so the domains differ and the
/// two facts are stored as distinct rules.
const FILE_A: &str = r#"
namespace wi458a
  fact enabled(feature: "x")
end
"#;

const FILE_B: &str = r#"
namespace wi458b
  fact enabled(feature: "x")
end
"#;

fn load_kb(sources: &[&str]) -> KnowledgeBase {
    let parsed: Vec<_> = sources.iter()
        .map(|s| parse::parse(s).expect("parse source"))
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver)
        .unwrap_or_else(|errs| {
            for e in &errs { eprintln!("Load error: {e}"); }
            panic!("load failed with {} errors", errs.len());
        });
    kb
}

#[test]
fn head_span_keys_on_occurrence_not_hashconsed_termid() {
    let mut kb = load_kb(&[FILE_A, FILE_B]);

    let enabled = kb.intern("enabled");
    let rids = kb.rules_by_functor(enabled);
    assert_eq!(
        rids.len(), 2,
        "expected exactly two `enabled` facts (one per namespace), got {}: \
         the two facts must NOT dedup — they differ by domain",
        rids.len(),
    );
    let (rid_a, rid_b) = (rids[0], rids[1]);

    // Precondition of the bug: both facts share ONE hash-consed head TermId, so
    // the TermId-keyed `term_span` cannot tell them apart.
    let head_a = kb.fact_head_term(rid_a).expect("fact A has a term head");
    let head_b = kb.fact_head_term(rid_b).expect("fact B has a term head");
    assert_eq!(
        head_a, head_b,
        "the two fact heads must intern to the SAME TermId for this test to \
         exercise the hash-cons collision",
    );
    // `term_span` collapses them onto whichever file registered the head first.
    assert_eq!(
        kb.term_span(head_a).map(|s| s.source),
        kb.term_span(head_b).map(|s| s.source),
        "term_span keys on the shared TermId, so both resolve to one source — \
         this is exactly the WI-458 collision",
    );

    // The fix: the per-occurrence head span keys on the RuleId, so each fact
    // resolves to its OWN source file.
    let src_a = kb.rule_head_span(rid_a).expect("fact A recorded a head span").source;
    let src_b = kb.rule_head_span(rid_b).expect("fact B recorded a head span").source;
    assert_ne!(
        src_a, src_b,
        "WI-458: the two facts share a head TermId but live in different files; \
         their per-occurrence head spans must resolve to distinct sources \
         (got {} for both)",
        kb.source_name(src_a),
    );
}
