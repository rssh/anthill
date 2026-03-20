/// Integration tests for the persistence module.
///
/// Tests: term printer round-trips, FileStore pull/persist/flush, full KB round-trip.

use std::path::PathBuf;

use anthill_core::kb::term::{Literal, Term};
use anthill_core::kb::{KnowledgeBase, RuleId};
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::persistence::print::{self, TermPrinter};
use anthill_core::persistence::file_store::{FileConvention, FileStore};
use anthill_core::persistence::{BulkStore, Store};
use anthill_core::parse;

use ordered_float::OrderedFloat;
use smallvec::SmallVec;

// ── Term printer tests ─────────────────────────────────────────

#[test]
fn printer_round_trip_simple_fact() {
    // Build: fact Eq(T: Int)
    let mut kb = KnowledgeBase::new();
    let eq_sym = kb.intern("Eq");
    let t_sym = kb.intern("T");
    let int_term = kb.make_name_term("Int");
    let eq_term = kb.alloc(Term::Fn {
        functor: eq_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(t_sym, int_term)]),
    });

    let text = print::print_fact(&kb, eq_term, None);
    assert_eq!(text, "fact Eq(T: Int)\n");

    // Parse it back
    let parsed = parse::parse(&text).expect("re-parse should succeed");
    assert_eq!(parsed.items.len(), 1);
}

#[test]
fn printer_round_trip_string_literal() {
    let mut kb = KnowledgeBase::new();
    let f = kb.intern("greet");
    let s = kb.alloc(Term::Const(Literal::String("hello \"world\"".into())));
    let t = kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::from_slice(&[s]),
        named_args: SmallVec::new(),
    });

    let text = print::print_fact(&kb, t, None);
    // Parse back — should succeed
    let parsed = parse::parse(&text).expect("re-parse of string literal fact");
    assert_eq!(parsed.items.len(), 1);
}

#[test]
fn printer_round_trip_numeric_literals() {
    let mut kb = KnowledgeBase::new();
    let f = kb.intern("nums");
    let int_val = kb.alloc(Term::Const(Literal::Int(42)));
    let float_val = kb.alloc(Term::Const(Literal::Float(OrderedFloat(3.14))));
    let t = kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::from_slice(&[int_val, float_val]),
        named_args: SmallVec::new(),
    });

    let text = print::print_fact(&kb, t, None);
    let parsed = parse::parse(&text).expect("re-parse of numeric fact");
    assert_eq!(parsed.items.len(), 1);
}

#[test]
fn printer_nested_fn() {
    let mut kb = KnowledgeBase::new();
    let inner_sym = kb.intern("inner");
    let outer_sym = kb.intern("outer");
    let val = kb.alloc(Term::Const(Literal::Int(1)));
    let inner = kb.alloc(Term::Fn {
        functor: inner_sym,
        pos_args: SmallVec::from_slice(&[val]),
        named_args: SmallVec::new(),
    });
    let outer = kb.alloc(Term::Fn {
        functor: outer_sym,
        pos_args: SmallVec::from_slice(&[inner]),
        named_args: SmallVec::new(),
    });

    let printer = TermPrinter::new(&kb);
    assert_eq!(printer.print_term(outer), "outer(inner(1))");
}

// ── FileStore pull tests ───────────────────────────────────────

#[test]
fn pull_reads_anthill_files() {
    let dir = tempfile::tempdir().expect("create temp dir");
    let root = dir.path();

    // Write some .anthill files
    std::fs::write(root.join("a.anthill"), "fact Foo\n").unwrap();
    std::fs::write(root.join("b.anthill"), "fact Bar\nfact Baz\n").unwrap();

    let store = FileStore::new(root.to_path_buf(), FileConvention::Flat);
    let files = store.pull().expect("pull should succeed");
    assert_eq!(files.len(), 2);

    // Count total facts across parsed files
    let total_facts: usize = files
        .iter()
        .map(|f| {
            f.items
                .iter()
                .filter(|i| matches!(i, anthill_core::parse::ir::Item::Fact(_)))
                .count()
        })
        .sum();
    assert_eq!(total_facts, 3);
}

#[test]
fn pull_empty_dir() {
    let dir = tempfile::tempdir().expect("create temp dir");
    let store = FileStore::new(dir.path().to_path_buf(), FileConvention::Flat);
    let files = store.pull().expect("pull empty dir");
    assert!(files.is_empty());
}

#[test]
fn pull_nonexistent_dir() {
    let store = FileStore::new(PathBuf::from("/nonexistent/path"), FileConvention::Flat);
    let files = store.pull().expect("pull nonexistent dir returns empty");
    assert!(files.is_empty());
}

#[test]
fn pull_nested_dirs() {
    let dir = tempfile::tempdir().expect("create temp dir");
    let sub = dir.path().join("sub");
    std::fs::create_dir(&sub).unwrap();
    std::fs::write(dir.path().join("top.anthill"), "fact A\n").unwrap();
    std::fs::write(sub.join("nested.anthill"), "fact B\n").unwrap();

    let store = FileStore::new(dir.path().to_path_buf(), FileConvention::Flat);
    let files = store.pull().expect("pull nested");
    assert_eq!(files.len(), 2);
}

// ── FileStore persist + flush tests ────────────────────────────

#[test]
fn persist_and_flush_flat() {
    let dir = tempfile::tempdir().expect("create temp dir");
    let mut store = FileStore::new(dir.path().to_path_buf(), FileConvention::Flat);

    let mut kb = KnowledgeBase::new();
    let sort = kb.make_name_term("Fact");
    let domain = kb.make_name_term("test");

    // Create a simple fact term: Foo
    let foo = kb.make_name_term("Foo");
    store.persist(&kb, foo, sort, domain, None).unwrap();

    // Create another fact: Bar(x: 42)
    let bar_sym = kb.intern("Bar");
    let x_sym = kb.intern("x");
    let val = kb.alloc(Term::Const(Literal::Int(42)));
    let bar = kb.alloc(Term::Fn {
        functor: bar_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(x_sym, val)]),
    });
    store.persist(&kb, bar, sort, domain, None).unwrap();

    // Flush
    store.flush(&kb).unwrap();

    // Verify the file was written
    let content = std::fs::read_to_string(dir.path().join("facts.anthill")).unwrap();
    assert!(content.contains("fact Foo"));
    assert!(content.contains("fact Bar(x: 42)"));
}

#[test]
fn persist_flush_appends() {
    let dir = tempfile::tempdir().expect("create temp dir");

    // Pre-existing file
    std::fs::write(dir.path().join("facts.anthill"), "fact Existing\n").unwrap();

    let mut store = FileStore::new(dir.path().to_path_buf(), FileConvention::Flat);
    let mut kb = KnowledgeBase::new();
    let sort = kb.make_name_term("Fact");
    let domain = kb.make_name_term("test");
    let new_term = kb.make_name_term("NewFact");

    store.persist(&kb, new_term, sort, domain, None).unwrap();
    store.flush(&kb).unwrap();

    let content = std::fs::read_to_string(dir.path().join("facts.anthill")).unwrap();
    assert!(content.contains("fact Existing"));
    assert!(content.contains("fact NewFact"));
}

#[test]
fn persist_by_domain() {
    let dir = tempfile::tempdir().expect("create temp dir");
    let mut store = FileStore::new(dir.path().to_path_buf(), FileConvention::ByDomain);

    let mut kb = KnowledgeBase::new();
    let sort = kb.make_name_term("Fact");
    let domain_a = kb.make_name_term("banking");
    let domain_b = kb.make_name_term("trading");

    let foo = kb.make_name_term("Foo");
    let bar = kb.make_name_term("Bar");

    store.persist(&kb, foo, sort, domain_a, None).unwrap();
    store.persist(&kb, bar, sort, domain_b, None).unwrap();
    store.flush(&kb).unwrap();

    // Should produce separate files per domain
    assert!(dir.path().join("banking.anthill").exists());
    assert!(dir.path().join("trading.anthill").exists());
}

// ── Full round-trip: KB → FileStore → disk → FileStore → KB ───

#[test]
fn full_round_trip() {
    let dir = tempfile::tempdir().expect("create temp dir");

    // Step 1: Build a KB with some facts
    let mut kb1 = KnowledgeBase::new();
    let fact_sort = kb1.make_name_term("Fact");
    let domain = kb1.make_name_term("test");

    // fact Eq(T: Int)
    let eq_sym = kb1.intern("Eq");
    let t_sym = kb1.intern("T");
    let int_term = kb1.make_name_term("Int");
    let eq_fact = kb1.alloc(Term::Fn {
        functor: eq_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(t_sym, int_term)]),
    });
    let fid1 = kb1.assert_fact(eq_fact, fact_sort, domain, None);

    // fact parent("alice", "bob")
    let parent_sym = kb1.intern("parent");
    let alice = kb1.alloc(Term::Const(Literal::String("alice".into())));
    let bob = kb1.alloc(Term::Const(Literal::String("bob".into())));
    let parent_fact = kb1.alloc(Term::Fn {
        functor: parent_sym,
        pos_args: SmallVec::from_slice(&[alice, bob]),
        named_args: SmallVec::new(),
    });
    let fid2 = kb1.assert_fact(parent_fact, fact_sort, domain, None);

    // Step 2: Persist facts to FileStore
    let mut store = FileStore::new(dir.path().to_path_buf(), FileConvention::Flat);
    store
        .persist(
            &kb1,
            kb1.fact_term(fid1),
            kb1.fact_sort(fid1),
            kb1.fact_domain(fid1),
            kb1.fact_meta(fid1),
        )
        .unwrap();
    store
        .persist(
            &kb1,
            kb1.fact_term(fid2),
            kb1.fact_sort(fid2),
            kb1.fact_domain(fid2),
            kb1.fact_meta(fid2),
        )
        .unwrap();
    store.flush(&kb1).unwrap();

    // Step 3: Pull back into a new KB
    let store2 = FileStore::new(dir.path().to_path_buf(), FileConvention::Flat);
    let parsed_files = store2.pull().expect("pull should succeed");
    assert_eq!(parsed_files.len(), 1);

    let mut kb2 = KnowledgeBase::new();
    for pf in &parsed_files {
        load::load(&mut kb2, pf, &NullResolver).expect("load should succeed");
    }

    // Step 4: Verify facts in the new KB
    let fact_sort2 = kb2.make_name_term("Fact");
    let facts = kb2.by_sort(fact_sort2);
    assert_eq!(facts.len(), 2, "should have 2 facts after round-trip");

    // Verify we can find the Eq fact by functor
    // After round-trip, "Eq" may resolve to the qualified anthill.prelude.Eq symbol
    let eq_sym2 = kb2.try_resolve_symbol("Eq")
        .or_else(|| kb2.try_resolve_symbol("anthill.prelude.Eq"))
        .unwrap_or_else(|| kb2.intern("Eq"));
    let eq_results = kb2.by_functor(eq_sym2);
    assert_eq!(eq_results.len(), 1, "should find 1 Eq fact");

    // Verify we can find the parent fact by functor
    let parent_sym2 = kb2.intern("parent");
    let parent_results = kb2.by_functor(parent_sym2);
    assert_eq!(parent_results.len(), 1, "should find 1 parent fact");
}

// ── Retract (stage 0: recorded only) ──────────────────────────

#[test]
fn retract_is_recorded() {
    let dir = tempfile::tempdir().expect("create temp dir");
    let mut store = FileStore::new(dir.path().to_path_buf(), FileConvention::Flat);

    // Retract returns Ok(true) in stage 0
    let result = store.retract(RuleId::from_index(0));
    assert!(result.is_ok());
    assert!(result.unwrap());
}
