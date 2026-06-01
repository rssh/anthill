/// Tests for incremental-loading primitives.
///
/// Verifies (1) resolve_instantiations is idempotent, (2) load_stdlib +
/// load_incremental produces a semantically equivalent KB to a one-shot
/// load_all.


use std::collections::BTreeSet;

use anthill_core::parse;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver, resolve_instantiations};
use anthill_core::persistence::print::TermPrinter;

fn parse_files(paths: &[std::path::PathBuf]) -> Vec<anthill_core::parse::ir::ParsedFile> {
    paths.iter()
        .map(|p| {
            let src = std::fs::read_to_string(p).expect("read");
            parse::parse(&src).expect("parse")
        })
        .collect()
}

fn load_stdlib_kb() -> KnowledgeBase {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    assert!(!files.is_empty(), "no stdlib files found");

    let parsed = parse_files(&files);
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_stdlib(&mut kb, &refs, &NullResolver).expect("stdlib load");
    kb
}

/// Canonical text form of every SortRequiresInfo fact in the KB, sorted.
fn canonical_requires_facts(kb: &KnowledgeBase) -> BTreeSet<String> {
    let sym = kb.try_resolve_symbol("anthill.reflect.SortRequiresInfo")
        .expect("SortRequiresInfo");
    let printer = TermPrinter::new(kb);
    kb.rules_by_functor(sym).iter()
        .map(|rid| printer.print_term(kb.rule_head(*rid)))
        .collect()
}

#[test]
fn resolve_instantiations_is_idempotent() {
    let mut kb = load_stdlib_kb();

    let requires_sym = kb.try_resolve_symbol("anthill.reflect.SortRequiresInfo")
        .expect("SortRequiresInfo symbol");

    // Snapshot the set of finalized SortRequiresInfo rule IDs + their heads.
    let before: Vec<_> = kb.rules_by_functor(requires_sym).iter()
        .map(|rid| (*rid, kb.rule_head(*rid)))
        .collect();
    assert!(!before.is_empty(), "stdlib should define SortRequiresInfo facts");

    // Second call must be a no-op: no retract, no reassert.
    resolve_instantiations(&mut kb);

    let after: Vec<_> = kb.rules_by_functor(requires_sym).iter()
        .map(|rid| (*rid, kb.rule_head(*rid)))
        .collect();

    assert_eq!(before, after,
        "resolve_instantiations should be idempotent (same RuleIds + heads)");
}

const USER_SOURCE: &str = r#"
namespace test.increment
  import anthill.prelude.{Eq, Ordered}

  sort MyThing
    sort T = ?
    requires Eq[T]
    requires Ordered[T]
  end
end
"#;

#[test]
fn load_incremental_equivalent_to_load_all() {
    // Build KB-A via one-shot load_all.
    let stdlib = crate::common::collect_anthill_files(&crate::common::stdlib_dir());
    let stdlib_parsed = parse_files(&stdlib);
    let user_parsed = parse::parse(USER_SOURCE).expect("parse user");

    let mut all_refs: Vec<&_> = stdlib_parsed.iter().collect();
    all_refs.push(&user_parsed);

    let mut kb_a = KnowledgeBase::new();
    load::register_prelude(&mut kb_a);
    kb_a.register_standard_builtins();
    load::load_all(&mut kb_a, &all_refs, &NullResolver).expect("one-shot load");

    // Build KB-B via load_stdlib then load_incremental.
    let mut kb_b = KnowledgeBase::new();
    load::register_prelude(&mut kb_b);
    kb_b.register_standard_builtins();
    let stdlib_refs: Vec<&_> = stdlib_parsed.iter().collect();
    load::load_stdlib(&mut kb_b, &stdlib_refs, &NullResolver).expect("stdlib load");
    load::load_incremental(&mut kb_b, &[&user_parsed], &NullResolver)
        .expect("incremental load");

    // Compare canonical SortRequiresInfo fact sets.
    let a = canonical_requires_facts(&kb_a);
    let b = canonical_requires_facts(&kb_b);
    assert_eq!(a, b,
        "SortRequiresInfo facts must match between one-shot and incremental loads");

    // MyThing contributes exactly two requires facts (Eq[T] + Ordered[T]).
    let my_count = a.iter().filter(|s| s.contains("MyThing")).count();
    assert_eq!(my_count, 2,
        "expected two MyThing-rooted requires facts; got:\n{:#?}",
        a.iter().filter(|s| s.contains("MyThing")).collect::<Vec<_>>());
}

#[test]
fn load_incremental_does_not_touch_stdlib_facts() {
    // Snapshot stdlib facts, then run load_incremental with a user file,
    // then check every originally-resolved RuleId is still live and still
    // marked resolved.
    let mut kb = load_stdlib_kb();

    let requires_sym = kb.try_resolve_symbol("anthill.reflect.SortRequiresInfo")
        .expect("SortRequiresInfo");
    let pre: Vec<_> = kb.rules_by_functor(requires_sym).iter()
        .filter(|rid| kb.is_requires_resolved(**rid))
        .map(|rid| (*rid, kb.rule_head(*rid)))
        .collect();
    assert!(!pre.is_empty(), "stdlib should have finalized SortRequiresInfo facts");

    let user = parse::parse(USER_SOURCE).expect("parse user");
    load::load_incremental(&mut kb, &[&user], &NullResolver).expect("incremental");

    for (rid, head) in &pre {
        assert!(kb.is_requires_resolved(*rid),
            "stdlib RuleId {rid:?} should remain marked resolved");
        assert_eq!(kb.rule_head(*rid), *head,
            "stdlib fact head must not be mutated by load_incremental");
    }
}

#[test]
fn at_least_one_requires_fact_marked_resolved() {
    // Facts whose spec is a SortView with positional args go through the
    // retract+reassert finalization path and get marked. Simpler specs
    // (e.g. bare Ref) are left untouched — not every RuleId needs to be
    // marked, only those that were actually rewritten.
    let kb = load_stdlib_kb();

    let requires_sym = kb.try_resolve_symbol("anthill.reflect.SortRequiresInfo")
        .expect("SortRequiresInfo symbol");

    let any_marked = kb.rules_by_functor(requires_sym).iter()
        .any(|rid| kb.is_requires_resolved(*rid));
    assert!(any_marked,
        "stdlib has SortView-shaped requires, at least one should be marked");
}
