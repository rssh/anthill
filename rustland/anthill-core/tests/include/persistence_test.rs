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
fn round_trip_escapes_preserve_content() {
    // Regression: printer escapes \" and \\, parser must decode them so the
    // resulting Literal::String matches the original. Previously the grammar's
    // string regex `/"[^"]*"/` rejected any backslash, breaking round-trip on
    // every string containing a quote or backslash. (See WI-085 history.)
    //
    // Strategy: print(fact) -> parse -> load into fresh KB -> printer again ->
    // assert second print equals first. If escapes are preserved end to end,
    // both prints come out identical.
    let cases = [
        r#"plain ascii"#,
        r#"quotes "inside" string"#,
        r#"backslash \ alone"#,
        r#"both \ and " together"#,
        r#"em-dash — and "quotes" in same string"#,  // WI-082 trigger
        "newline\nand\ttab",
    ];
    for original in cases {
        let mut kb1 = KnowledgeBase::new();
        let functor = kb1.intern("s");
        let lit = kb1.alloc(Term::Const(Literal::String(original.to_string())));
        let fact = kb1.alloc(Term::Fn {
            functor,
            pos_args: SmallVec::from_slice(&[lit]),
            named_args: SmallVec::new(),
        });
        let printed1 = print::print_fact(&kb1, fact, None);

        // Round-trip: parse and load into a fresh KB.
        let parsed = parse::parse(&printed1)
            .unwrap_or_else(|e| panic!("re-parse failed for {original:?}: {e:?}"));
        let mut kb2 = KnowledgeBase::new();
        load::load(&mut kb2, &parsed, &NullResolver)
            .unwrap_or_else(|e| panic!("load failed for {original:?}: {e:?}"));

        // Pull the round-tripped fact and reprint via the second KB.
        // `intern` is idempotent — returns the existing symbol if scan/load
        // interned it for the fact's functor, otherwise creates a fresh one.
        let s_sym = kb2.intern("s");
        let rules = kb2.rules_by_functor(s_sym);
        assert_eq!(rules.len(), 1, "should find exactly one fact for {original:?}");
        let head = kb2.rule_head(rules[0]);
        let printer = TermPrinter::new(&kb2);
        let printed2 = format!("fact {}\n", printer.print_term(head));

        assert_eq!(printed1, printed2,
            "round-trip mismatch for {original:?}:\nfirst print:  {printed1}second print: {printed2}");
    }
}

#[test]
fn round_trip_entity_with_string_fields_preserves_escapes() {
    // Mirrors how stdlib / project files actually serialize state: an entity
    // declaration with String-typed named fields, instantiated by a fact whose
    // values contain quotes, backslashes, em-dashes, etc. This is the WI-082
    // shape (a WorkItem fact with a description field containing escaped quotes).
    //
    // Strategy: write an `entity` declaration plus a `fact` literal directly as
    // text, parse it, then verify the parsed fact has the original (decoded)
    // string values.
    let id_value      = r#"WI-001"#;
    let desc_value    = r#"Use Quoted("cpp", "...") with em-dash — and a \backslash"#;
    let payload_value = "newline\nand\ttab and \"quotes\"";

    // Build the source text via the printer's escape rules so the parser
    // sees exactly the shape the printer would produce.
    let mut kb1 = KnowledgeBase::new();
    let entity_sym = kb1.intern("Account");
    let id_field = kb1.intern("id");
    let desc_field = kb1.intern("description");
    let payload_field = kb1.intern("payload");
    let id_lit = kb1.alloc(Term::Const(Literal::String(id_value.into())));
    let desc_lit = kb1.alloc(Term::Const(Literal::String(desc_value.into())));
    let payload_lit = kb1.alloc(Term::Const(Literal::String(payload_value.into())));
    let fact_term = kb1.alloc(Term::Fn {
        functor: entity_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (desc_field, desc_lit),
            (id_field, id_lit),
            (payload_field, payload_lit),
        ]),
    });
    let printed1 = print::print_fact(&kb1, fact_term, None);

    // Round-trip through parse and load.
    let parsed = parse::parse(&printed1)
        .expect("entity-with-strings fact should parse after printer escapes");
    let mut kb2 = KnowledgeBase::new();
    load::load(&mut kb2, &parsed, &NullResolver)
        .expect("entity-with-strings fact should load");

    let acc_sym = kb2.intern("Account");
    let rules = kb2.rules_by_functor(acc_sym);
    assert_eq!(rules.len(), 1, "exactly one Account fact after round-trip");

    // Reprint via the second KB and compare textually — if any escape was
    // misdecoded, the second print would carry doubled or mangled escapes.
    let head = kb2.rule_head(rules[0]);
    let printer = TermPrinter::new(&kb2);
    let printed2 = format!("fact {}\n", printer.print_term(head));
    assert_eq!(printed1, printed2,
        "entity round-trip mismatch:\nfirst print:  {printed1}second print: {printed2}");
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
    let eq_results = kb2.rules_by_functor(eq_sym2);
    assert_eq!(eq_results.len(), 1, "should find 1 Eq fact");

    // Verify we can find the parent fact by functor
    let parent_sym2 = kb2.intern("parent");
    let parent_results = kb2.rules_by_functor(parent_sym2);
    assert_eq!(parent_results.len(), 1, "should find 1 parent fact");
}

// ── Retract: file modification at flush ───────────────────────

#[test]
fn retract_unknown_rule_is_noop() {
    // Buffering a retract for an out-of-bounds RuleId returns Ok(false)
    // without panicking, and flush is a clean no-op.
    let dir = tempfile::tempdir().expect("create temp dir");
    let mut store = FileStore::new(dir.path().to_path_buf(), FileConvention::Flat);
    let kb = KnowledgeBase::new();

    let result = store.retract(&kb, RuleId::from_index(999));
    assert!(matches!(result, Ok(false)));

    // Flush succeeds with no work to do (no file is created).
    store.flush(&kb).unwrap();
    assert!(!dir.path().join("facts.anthill").exists());
}

#[test]
fn retract_drops_fact_block_from_disk() {
    let dir = tempfile::tempdir().expect("create temp dir");
    let mut store = FileStore::new(dir.path().to_path_buf(), FileConvention::Flat);

    let mut kb = KnowledgeBase::new();
    let sort = kb.make_name_term("Fact");
    let domain = kb.make_name_term("test");

    // Persist three facts: Foo, Bar, Baz.
    let foo = kb.make_name_term("Foo");
    let bar = kb.make_name_term("Bar");
    let baz = kb.make_name_term("Baz");
    let foo_id = kb.assert_fact(foo, sort, domain, None);
    let bar_id = kb.assert_fact(bar, sort, domain, None);
    let _baz_id = kb.assert_fact(baz, sort, domain, None);

    store.persist(&kb, kb.fact_term(foo_id), sort, domain, None).unwrap();
    store.persist(&kb, kb.fact_term(bar_id), sort, domain, None).unwrap();
    store.persist(&kb, baz, sort, domain, None).unwrap();
    store.flush(&kb).unwrap();

    let path = dir.path().join("facts.anthill");
    let after_persist = std::fs::read_to_string(&path).unwrap();
    assert!(after_persist.contains("fact Foo"));
    assert!(after_persist.contains("fact Bar"));
    assert!(after_persist.contains("fact Baz"));

    // Retract Bar via the store (must come before kb.retract).
    store.retract(&kb, bar_id).unwrap();
    kb.retract(bar_id);
    store.flush(&kb).unwrap();

    let after_retract = std::fs::read_to_string(&path).unwrap();
    assert!(after_retract.contains("fact Foo"), "Foo should remain");
    assert!(after_retract.contains("fact Baz"), "Baz should remain");
    assert!(!after_retract.contains("fact Bar"), "Bar should be dropped");
}

#[test]
fn retract_then_persist_replaces_in_place() {
    // Claim/deliver-style update: retract the old WorkItem, persist a
    // new one with the same id, expect a single fact on disk with the
    // new contents.
    let dir = tempfile::tempdir().expect("create temp dir");
    let mut store = FileStore::new(dir.path().to_path_buf(), FileConvention::Flat);

    let mut kb = KnowledgeBase::new();
    let sort = kb.make_name_term("Fact");
    let domain = kb.make_name_term("test");

    let wi_sym = kb.intern("WorkItem");
    let id_sym = kb.intern("id");
    let status_sym = kb.intern("status");
    let id_lit = kb.alloc(Term::Const(Literal::String("WI-X".into())));
    let open_term = kb.make_name_term("Open");
    let claimed_term = kb.make_name_term("Claimed");

    let mut named_open = SmallVec::<[(_, _); 2]>::new();
    named_open.push((id_sym, id_lit));
    named_open.push((status_sym, open_term));
    named_open.sort_by_key(|(s, _)| s.index());
    let wi_open = kb.alloc(Term::Fn {
        functor: wi_sym,
        pos_args: SmallVec::new(),
        named_args: named_open,
    });
    let open_id = kb.assert_fact(wi_open, sort, domain, None);

    store.persist(&kb, kb.fact_term(open_id), sort, domain, None).unwrap();
    store.flush(&kb).unwrap();

    let path = dir.path().join("facts.anthill");
    let after_open = std::fs::read_to_string(&path).unwrap();
    assert_eq!(after_open.matches("fact WorkItem(").count(), 1);
    assert!(after_open.contains("status: Open"));

    // Update: retract the Open fact, persist Claimed.
    store.retract(&kb, open_id).unwrap();
    kb.retract(open_id);

    let mut named_claimed = SmallVec::<[(_, _); 2]>::new();
    named_claimed.push((id_sym, id_lit));
    named_claimed.push((status_sym, claimed_term));
    named_claimed.sort_by_key(|(s, _)| s.index());
    let wi_claimed = kb.alloc(Term::Fn {
        functor: wi_sym,
        pos_args: SmallVec::new(),
        named_args: named_claimed,
    });
    let claimed_id = kb.assert_fact(wi_claimed, sort, domain, None);
    store.persist(&kb, kb.fact_term(claimed_id), sort, domain, None).unwrap();
    store.flush(&kb).unwrap();

    let after_claim = std::fs::read_to_string(&path).unwrap();
    assert_eq!(
        after_claim.matches("fact WorkItem(").count(),
        1,
        "exactly one WorkItem fact on disk after update; got:\n{after_claim}"
    );
    assert!(after_claim.contains("status: Claimed"));
    assert!(!after_claim.contains("status: Open"));
}

#[test]
fn retract_preserves_inter_fact_text() {
    // A pre-existing file with a header comment and blank-line spacing
    // between facts: retract should leave the header and the surviving
    // facts in their original positions.
    let dir = tempfile::tempdir().expect("create temp dir");
    let path = dir.path().join("facts.anthill");
    let original = "-- header comment\n\nfact A\n\nfact B\n\nfact C\n";
    std::fs::write(&path, original).unwrap();

    // Load facts into a KB so the store can canonicalize them.
    let mut store = FileStore::new(dir.path().to_path_buf(), FileConvention::Flat);
    let parsed = store.pull().expect("pull");
    let mut kb = KnowledgeBase::new();
    for pf in &parsed {
        load::load(&mut kb, pf, &NullResolver).unwrap();
    }

    // Find the rule for B by walking by_sort and matching the printed head.
    let fact_sort = kb.make_name_term("Fact");
    let mut b_id_opt = None;
    for rid in kb.by_sort(fact_sort) {
        let head = kb.rule_head(rid);
        if anthill_core::persistence::print::TermPrinter::new(&kb).print_term(head) == "B" {
            b_id_opt = Some(rid);
            break;
        }
    }
    let b_id = b_id_opt.expect("found B rule");

    store.retract(&kb, b_id).unwrap();
    kb.retract(b_id);
    store.flush(&kb).unwrap();

    let after = std::fs::read_to_string(&path).unwrap();
    assert!(after.contains("-- header comment"), "header preserved");
    assert!(after.contains("fact A"));
    assert!(after.contains("fact C"));
    assert!(!after.contains("fact B"));
}

#[test]
fn flush_is_idempotent_after_retract() {
    // Calling flush twice with no new pending operations must not change
    // the file. Guards against the persist-buffer being replayed.
    let dir = tempfile::tempdir().expect("create temp dir");
    let mut store = FileStore::new(dir.path().to_path_buf(), FileConvention::Flat);

    let mut kb = KnowledgeBase::new();
    let sort = kb.make_name_term("Fact");
    let domain = kb.make_name_term("test");
    let foo = kb.make_name_term("Foo");
    let bar = kb.make_name_term("Bar");
    let _foo_id = kb.assert_fact(foo, sort, domain, None);
    let bar_id = kb.assert_fact(bar, sort, domain, None);

    store.persist(&kb, foo, sort, domain, None).unwrap();
    store.persist(&kb, bar, sort, domain, None).unwrap();
    store.retract(&kb, bar_id).unwrap();
    kb.retract(bar_id);
    store.flush(&kb).unwrap();

    let first = std::fs::read_to_string(dir.path().join("facts.anthill")).unwrap();

    // Second flush — buffers empty, should be a no-op on disk.
    store.flush(&kb).unwrap();
    let second = std::fs::read_to_string(dir.path().join("facts.anthill")).unwrap();
    assert_eq!(first, second, "flush must be idempotent");
}
