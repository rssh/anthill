//! Named type applications already lower correctly when their names are in scope.
//! The remaining defect was silent absence when the sort or a binding was missing.
use crate::common::{load_kb_with, query_pattern_term, supply_invocation_imports};
use anthill_core::{
    kb::{load, resolve::ResolveConfig, KnowledgeBase},
    parse,
};

fn kb() -> KnowledgeBase {
    let mut kb = load_kb_with(include_str!("../fixtures/wi7fp1m/words.anthill"));
    supply_invocation_imports(&mut kb, &["wi7fp1m.*", "anthill.prelude.List.*"]);
    kb
}

fn count(kb: &mut KnowledgeBase, pattern: &str, cap: usize) -> usize {
    let query = query_pattern_term(kb, pattern);
    let rows = kb.resolve(
        &[query],
        &ResolveConfig {
            max_solutions: cap,
            ..Default::default()
        },
    );
    assert!(rows.iter().all(|row| row.is_definite()), "{pattern}");
    rows.len()
}

#[test]
fn wi7fp1m_imported_type_and_wrapper_answer_identically() {
    // Controls: all these counts pass with the diagnostic fix backed out.
    let mut kb = kb();
    supply_invocation_imports(&mut kb, &["anthill.prelude.List"]);
    assert_eq!(count(&mut kb, "domain(nil(), List[T = Letter])", 0), 1);
    assert_eq!(count(&mut kb, "domain(?w, List[T = Letter])", 8), 8);
    assert_eq!(count(&mut kb, "any_word(?w)", 8), 8);
    assert_eq!(count(&mut kb, "domain(?x, Letter)", 0), 3);
    for word in ["nil()", "[a()]", "[b()]", "[c()]"] {
        assert_eq!(
            count(&mut kb, &format!("domain({word}, List[T = Letter])"), 0),
            1
        );
    }
}

#[test]
fn wi7fp1m_missing_type_names_are_located_errors() {
    // Regression: each scan incorrectly succeeds with query_type_name_errors removed.
    let mut kb = kb();
    for (pattern, missing) in [
        ("domain(nil(), List[T = Letter])", "List"),
        (
            "domain(nil(), anthill.prelude.List[T = MissingLetter])",
            "MissingLetter",
        ),
        (
            "domain(nil(), anthill.prelude.List[T = anthill.prelude.List[T = MissingNested]])",
            "MissingNested",
        ),
    ] {
        let parsed = parse::parse(&format!("fact {pattern}")).unwrap();
        let errors = load::scan_query_definitions(&mut kb, &[&parsed]);
        let messages = load::LoadError::render_all(&errors)
            .collect::<Vec<_>>()
            .join("\n");
        assert!(messages.contains(missing), "{pattern}: {messages}");
        assert!(!errors.is_empty(), "{pattern} must be refused");
        let span = errors[0].user_span().expect("located missing name");
        assert!(parsed.source[span.start as usize..span.end as usize].contains(missing));
    }
}

#[test]
fn wi7fp1m_query_file_import_is_visible_to_validation() {
    // Control for file-local (rather than invocation) imports.
    let mut kb = kb();
    let parsed =
        parse::parse("import anthill.prelude.List\nfact domain(nil(), List[T = Letter])").unwrap();
    assert!(load::scan_query_definitions(&mut kb, &[&parsed]).is_empty());
    let parse::ir::Item::Fact(fact) = &parsed.items[0] else {
        panic!("query file must contain a fact pattern");
    };
    let scope = kb.global_scope();
    let query = load::convert_query_term(
        &mut kb,
        &parsed.terms,
        &parsed.symbols,
        fact.term,
        scope,
        &mut Default::default(),
    );
    let rows = kb.resolve(&[query], &ResolveConfig::default());
    assert_eq!(rows.len(), 1);
    assert!(rows[0].is_definite());
}
