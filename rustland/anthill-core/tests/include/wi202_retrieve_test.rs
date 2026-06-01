//! IndexedFileStore primary-key index + QueryableStore::retrieve.

use std::path::PathBuf;

use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::{KnowledgeBase, RuleId};
use anthill_core::persistence::file_store::FileConvention;
use anthill_core::persistence::indexed_file_store::IndexedFileStore;
use anthill_core::persistence::Store;

use smallvec::SmallVec;

/// Allocate `WorkItem(id: "...", status: ...)` in the KB. Returns the
/// term id and the rule id (the asserted fact's RuleId).
fn make_wi(kb: &mut KnowledgeBase, id_str: &str, status_name: &str) -> (TermId, RuleId) {
    let wi_sym = kb.intern("WorkItem");
    let id_sym = kb.intern("id");
    let status_sym = kb.intern("status");
    let id_term = kb.alloc(Term::Const(Literal::String(id_str.into())));
    let status_term = kb.make_name_term(status_name);
    let mut named: SmallVec<[(_, _); 2]> = SmallVec::new();
    // named_args must be sorted by symbol index — easier here to use
    // a hand-sorted insertion by interned symbol value.
    named.push((id_sym, id_term));
    named.push((status_sym, status_term));
    named.sort_by_key(|(s, _)| s.index());
    let head = kb.alloc(Term::Fn {
        functor: wi_sym,
        pos_args: SmallVec::new(),
        named_args: named,
    });
    let sort = kb.make_name_term("Fact");
    let domain = kb.make_name_term("test");
    let rid = kb.assert_fact(head, sort, domain, None);
    (head, rid)
}

/// Build a pattern like `WorkItem(id: "X")` (with id only).
fn pattern_with_id(kb: &mut KnowledgeBase, id_str: &str) -> TermId {
    let wi_sym = kb.intern("WorkItem");
    let id_sym = kb.intern("id");
    let id_term = kb.alloc(Term::Const(Literal::String(id_str.into())));
    kb.alloc(Term::Fn {
        functor: wi_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(id_sym, id_term)]),
    })
}

/// `WorkItem(status: <status_name>)` — no id constraint, slow path.
fn pattern_with_status(kb: &mut KnowledgeBase, status_name: &str) -> TermId {
    let wi_sym = kb.intern("WorkItem");
    let status_sym = kb.intern("status");
    let status_term = kb.make_name_term(status_name);
    kb.alloc(Term::Fn {
        functor: wi_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(status_sym, status_term)]),
    })
}

/// `WorkItem()` — no fields constrained, returns all WorkItem facts.
fn pattern_any(kb: &mut KnowledgeBase) -> TermId {
    let wi_sym = kb.intern("WorkItem");
    kb.alloc(Term::Fn {
        functor: wi_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    })
}

fn fresh_store() -> IndexedFileStore {
    IndexedFileStore::new(PathBuf::from("/tmp/wi202-test"), FileConvention::Flat)
}

#[test]
fn retrieve_fast_path_via_by_id() {
    let mut kb = KnowledgeBase::new();
    let mut store = fresh_store();

    let (_, rid_a) = make_wi(&mut kb, "WI-001", "Open");
    let (_, rid_b) = make_wi(&mut kb, "WI-002", "Claimed");
    store.index_by_id(rid_a, &kb);
    store.index_by_id(rid_b, &kb);

    let pat = pattern_with_id(&mut kb, "WI-001");
    let hits = store.retrieve(&kb, pat).expect("retrieve");
    assert_eq!(hits.len(), 1);
    // The hit's term is the rule's head — should be the WI-001 entry.
    let head_id = hits[0];
    if let Term::Fn { named_args, .. } = kb.get_term(head_id) {
        let id_val = named_args.iter()
            .find(|(s, _)| kb.resolve_sym(*s) == "id")
            .expect("hit has id field");
        if let Term::Const(Literal::String(s)) = kb.get_term(id_val.1) {
            assert_eq!(s, "WI-001");
        } else {
            panic!("id is not a String");
        }
    } else {
        panic!("hit is not Fn");
    }
}

#[test]
fn retrieve_fast_path_missing_id_returns_empty() {
    let mut kb = KnowledgeBase::new();
    let mut store = fresh_store();
    let (_, rid) = make_wi(&mut kb, "WI-001", "Open");
    store.index_by_id(rid, &kb);

    let pat = pattern_with_id(&mut kb, "WI-NOPE");
    let hits = store.retrieve(&kb, pat).expect("retrieve");
    assert!(hits.is_empty());
}

#[test]
fn retrieve_slow_path_by_status() {
    // No `id` in the pattern, so retrieve walks rules_by_functor and
    // pattern-matches each candidate. Two Open + one Claimed; only
    // the two Open should come back.
    let mut kb = KnowledgeBase::new();
    let mut store = fresh_store();
    let (_, rid_a) = make_wi(&mut kb, "WI-001", "Open");
    let (_, rid_b) = make_wi(&mut kb, "WI-002", "Open");
    let (_, rid_c) = make_wi(&mut kb, "WI-003", "Claimed");
    store.index_by_id(rid_a, &kb);
    store.index_by_id(rid_b, &kb);
    store.index_by_id(rid_c, &kb);

    let pat = pattern_with_status(&mut kb, "Open");
    let hits = store.retrieve(&kb, pat).expect("retrieve");
    assert_eq!(hits.len(), 2, "expected two Open WorkItems, got {}", hits.len());
}

#[test]
fn retrieve_empty_pattern_returns_all() {
    let mut kb = KnowledgeBase::new();
    let mut store = fresh_store();
    let (_, rid_a) = make_wi(&mut kb, "WI-001", "Open");
    let (_, rid_b) = make_wi(&mut kb, "WI-002", "Claimed");
    let (_, rid_c) = make_wi(&mut kb, "WI-003", "Verified");
    store.index_by_id(rid_a, &kb);
    store.index_by_id(rid_b, &kb);
    store.index_by_id(rid_c, &kb);

    let pat = pattern_any(&mut kb);
    let hits = store.retrieve(&kb, pat).expect("retrieve");
    assert_eq!(hits.len(), 3);
}

#[test]
fn retract_drops_from_by_id() {
    let mut kb = KnowledgeBase::new();
    let mut store = fresh_store();
    let (_, rid) = make_wi(&mut kb, "WI-001", "Open");
    store.index_by_id(rid, &kb);

    // Before retract: present.
    let pat = pattern_with_id(&mut kb, "WI-001");
    assert_eq!(store.retrieve(&kb, pat).unwrap().len(), 1);

    // Retract via Store::retract — should remove from by_id and (since
    // there's no source_map entry for this runtime-asserted fact) fall
    // through to the inner FileStore retract.
    let _ = store.retract(&kb, rid);
    kb.retract(rid);

    // After retract: empty.
    let pat2 = pattern_with_id(&mut kb, "WI-001");
    assert!(store.retrieve(&kb, pat2).unwrap().is_empty());
}

#[test]
fn retrieve_default_on_filestore_returns_not_queryable() {
    // The bare `Store::retrieve` default is `NotQueryable`. A FileStore
    // (no QueryableStore impl) should hit it.
    use anthill_core::persistence::file_store::FileStore;
    use anthill_core::persistence::PersistenceError;
    let kb = KnowledgeBase::new();
    let store = FileStore::new(PathBuf::from("/tmp/wi202-fs"), FileConvention::Flat);
    let mut kb2 = kb;
    let pat = pattern_any(&mut kb2);
    match store.retrieve(&kb2, pat) {
        Err(PersistenceError::NotQueryable) => {}
        other => panic!("expected NotQueryable, got {other:?}"),
    }
}
