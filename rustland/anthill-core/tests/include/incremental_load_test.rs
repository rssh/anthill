/// Tests for incremental-loading primitives.
///
/// Verifies (1) `resolve_instantiations` is idempotent, (2) a STAGED load — the stdlib
/// through `load_all`, then the user file through a second `load_all` into that same live
/// KB — produces a semantically equivalent KB to a one-shot `load_all` over both.
///
/// WI-20260901-Q68AK retired the `load_stdlib` / `load_incremental` spellings these tests
/// were named for; both were one-line delegations to `load_all` by then, so every call
/// below is a `load_all` and the test NAMES are the only place the old distinction
/// survives.
use std::collections::BTreeSet;

use anthill_core::kb::load::{self, resolve_instantiations, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use anthill_core::persistence::print::TermPrinter;

fn parse_files(paths: &[std::path::PathBuf]) -> Vec<anthill_core::parse::ir::ParsedFile> {
    paths
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p).expect("read");
            parse::parse(&src).expect("parse")
        })
        .collect()
}

/// Phase 1 over the FULL closure — `stdlib/anthill/` **plus** `anthill-stl/anthill/`.
///
/// WI-1103 moved these fixtures off the stdlib-ALONE corpus, which is why the whole
/// file was green through a defect that made every two-phase load impossible. Without
/// the host bindings there is no `fact Eq[Int64]` and no `fact NonEq[Float]`, so
/// `eq_derive` has no lawful-`Eq` leaf to propagate from and no partial leaf to
/// propagate — almost nothing classifies, no `NonEq` is derived, and the derived rows
/// whose re-check broke phase 2 never exist here. This file is the only fixture in the
/// suite that loads two phases at all; loading less than the shipped closure in it
/// left the path effectively untested (WI-979's shape).
///
/// CONTROL — MEASURED by backing the WI-1103 change out (the
/// `is_unbacked_derived_provision` skip in `check_provider_operations`): the two
/// callers of this helper that go on to `load_all` into a live KB
/// (`load_incremental_does_not_touch_stdlib_facts`, and the sibling closure in
/// `load_incremental_equivalent_to_load_all`) FAIL with five
/// `UnbackedProviderOperation`s. `resolve_instantiations_is_idempotent` and
/// `at_least_one_requires_fact_marked_resolved` pass either way BY DESIGN — they stop
/// at phase 1, which never re-walks a derived row.
fn load_stdlib_kb() -> KnowledgeBase {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    assert!(!files.is_empty(), "no stdlib files found");

    let parsed = parse_files(&files);
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::load_all(&mut kb, &refs, &NullResolver).expect("stdlib load");
    kb
}

/// Canonical text form of every SortRequiresInfo fact in the KB, sorted.
fn canonical_requires_facts(kb: &KnowledgeBase) -> BTreeSet<String> {
    let sym = kb
        .try_resolve_symbol("anthill.reflect.SortRequiresInfo")
        .expect("SortRequiresInfo");
    let printer = TermPrinter::new(kb);
    kb.rules_by_functor(sym)
        .iter()
        .map(|rid| printer.print_term(kb.rule_head(*rid)))
        .collect()
}

#[test]
fn resolve_instantiations_is_idempotent() {
    let mut kb = load_stdlib_kb();

    let requires_sym = kb
        .try_resolve_symbol("anthill.reflect.SortRequiresInfo")
        .expect("SortRequiresInfo symbol");

    // Snapshot the set of finalized SortRequiresInfo rule IDs + their heads.
    let before: Vec<_> = kb
        .rules_by_functor(requires_sym)
        .iter()
        .map(|rid| (*rid, kb.rule_head(*rid)))
        .collect();
    assert!(
        !before.is_empty(),
        "stdlib should define SortRequiresInfo facts"
    );

    // Second call must be a no-op: no retract, no reassert.
    resolve_instantiations(&mut kb);

    let after: Vec<_> = kb
        .rules_by_functor(requires_sym)
        .iter()
        .map(|rid| (*rid, kb.rule_head(*rid)))
        .collect();

    assert_eq!(
        before, after,
        "resolve_instantiations should be idempotent (same RuleIds + heads)"
    );
}

const USER_SOURCE: &str = r#"
namespace test.increment
  import anthill.prelude.{Eq, Ord}

  sort MyThing
    sort T = ?
    requires Eq[T]
    requires Ord[T]
  end
end
"#;

/// WI-967 — a `load_all` into a live KB bootstraps like every other load entry point.
///
/// It used to be the ONE entry point that skipped `register_prelude`, on the
/// assumption that it is only ever reached second. Nothing enforced that, and
/// reaching it FIRST silently produced a KB whose kernel vocabulary did not
/// resolve. This drives the fixed behaviour on a genuinely fresh KB: no stdlib,
/// no prior load, no caller-side registration.
///
/// CONTROL — RE-STATED, BECAUSE THE ISOLATING BACK-OUT WENT WITH THE SECOND ENTRY POINT
/// (WI-20260901-Q8NH5, measured). While `load_incremental` was its own function, removing
/// ITS `register_prelude` reddened this row alone: every other row here calls
/// `load_stdlib` first and bootstrapped through the OTHER function. There is ONE bootstrap
/// site now — `load_all_with`'s `register_prelude(kb)` — and removing it takes all FIVE
/// rows in this file red, `load_stdlib_kb` included, so no back-out isolates this one any
/// more. What it still holds alone is the SHAPE: it is the only row whose KB never sees a
/// stdlib file, so it is the only one asserting that the kernel vocabulary and the builtin
/// TAGS come from the LOAD and not from something the stdlib happened to bring. The WI-967
/// deletion of the redundant caller-side `register_prelude` / builtin-tag lines is still a
/// refactor over an idempotent function, green either way, here and across the suite.
#[test]
fn load_incremental_bootstraps_a_fresh_kb() {
    let user = parse::parse(
        r#"
namespace test.wi967
  sort Boxed
    entity Boxed(n: Int64)
  end

  fact Boxed(n: 42)
end
"#,
    )
    .expect("parse");

    let mut kb = KnowledgeBase::new();
    // FIRST call into the KB — no register_prelude, no load_stdlib, nothing.
    load::load_all(&mut kb, &[&user], &NullResolver)
        .expect("a first load_all must bootstrap a fresh KB, not leave kernel names unresolved");

    // Both halves of bootstrap must have run.
    // (1) the kernel meta-sorts / stdlib scope hierarchy — `Int64` above resolved.
    assert!(
        kb.try_resolve_symbol("Int64").is_some(),
        "register_prelude's KERNEL_META_SORTS did not run"
    );
    // (2) the builtin TAGS — `register_builtin_tags`, which only
    // `register_prelude` calls (WI-967).
    let eq = kb
        .try_resolve_symbol("anthill.prelude.PartialEq.eq")
        .expect("PartialEq.eq symbol must exist after bootstrap");
    assert!(
        kb.is_builtin(eq),
        "register_builtin_tags did not run: PartialEq.eq carries no builtin tag"
    );

    // DRIVE the loaded content, so this is not a `loads clean` assertion:
    // the fact must be queryable through the bootstrapped KB.
    let boxed = kb
        .try_resolve_symbol("test.wi967.Boxed")
        .expect("Boxed symbol");
    assert_eq!(
        kb.rules_by_functor(boxed).len(),
        1,
        "the `fact Boxed(n: 42)` should be indexed under its head functor"
    );
}

/// WI-1103 — also over the FULL closure (see [`load_stdlib_kb`] for why, and for the
/// measured back-out). One of this file's two CONTROLs for that change: it FAILS at
/// the SECOND `load_all` line below without it, because `check_provider_operations`
/// re-walks phase 1's derived `NonEq` rows and refuses all five.
#[test]
fn load_incremental_equivalent_to_load_all() {
    // Build KB-A via one-shot load_all.
    let stdlib = crate::common::collect_stdlib_and_rust_bindings();
    let stdlib_parsed = parse_files(&stdlib);
    let user_parsed = parse::parse(USER_SOURCE).expect("parse user");

    let mut all_refs: Vec<&_> = stdlib_parsed.iter().collect();
    all_refs.push(&user_parsed);

    let mut kb_a = KnowledgeBase::new();
    load::load_all(&mut kb_a, &all_refs, &NullResolver).expect("one-shot load");

    // Build KB-B in two batches: the stdlib, then the user file into that live KB.
    let mut kb_b = KnowledgeBase::new();
    let stdlib_refs: Vec<&_> = stdlib_parsed.iter().collect();
    load::load_all(&mut kb_b, &stdlib_refs, &NullResolver).expect("stdlib load");
    load::load_all(&mut kb_b, &[&user_parsed], &NullResolver).expect("incremental load");

    // Compare canonical SortRequiresInfo fact sets.
    let a = canonical_requires_facts(&kb_a);
    let b = canonical_requires_facts(&kb_b);
    assert_eq!(
        a, b,
        "SortRequiresInfo facts must match between one-shot and incremental loads"
    );

    // MyThing contributes exactly two requires facts (Eq[T] + Ord[T]).
    let my_count = a.iter().filter(|s| s.contains("MyThing")).count();
    assert_eq!(
        my_count,
        2,
        "expected two MyThing-rooted requires facts; got:\n{:#?}",
        a.iter()
            .filter(|s| s.contains("MyThing"))
            .collect::<Vec<_>>()
    );
}

#[test]
fn load_incremental_does_not_touch_stdlib_facts() {
    // Snapshot stdlib facts, then load a user file into the live KB,
    // then check every originally-resolved RuleId is still live and still
    // marked resolved.
    let mut kb = load_stdlib_kb();

    let requires_sym = kb
        .try_resolve_symbol("anthill.reflect.SortRequiresInfo")
        .expect("SortRequiresInfo");
    let pre: Vec<_> = kb
        .rules_by_functor(requires_sym)
        .iter()
        .filter(|rid| kb.is_requires_resolved(**rid))
        .map(|rid| (*rid, kb.rule_head(*rid)))
        .collect();
    assert!(
        !pre.is_empty(),
        "stdlib should have finalized SortRequiresInfo facts"
    );

    let user = parse::parse(USER_SOURCE).expect("parse user");
    load::load_all(&mut kb, &[&user], &NullResolver).expect("incremental");

    for (rid, head) in &pre {
        assert!(
            kb.is_requires_resolved(*rid),
            "stdlib RuleId {rid:?} should remain marked resolved"
        );
        assert_eq!(
            kb.rule_head(*rid),
            *head,
            "stdlib fact head must not be mutated by the second load"
        );
    }
}

#[test]
fn at_least_one_requires_fact_marked_resolved() {
    // Facts whose spec is a SortView with positional args go through the
    // retract+reassert finalization path and get marked. Simpler specs
    // (e.g. bare Ref) are left untouched — not every RuleId needs to be
    // marked, only those that were actually rewritten.
    let kb = load_stdlib_kb();

    let requires_sym = kb
        .try_resolve_symbol("anthill.reflect.SortRequiresInfo")
        .expect("SortRequiresInfo symbol");

    let any_marked = kb
        .rules_by_functor(requires_sym)
        .iter()
        .any(|rid| kb.is_requires_resolved(*rid));
    assert!(
        any_marked,
        "stdlib has SortView-shaped requires, at least one should be marked"
    );
}
