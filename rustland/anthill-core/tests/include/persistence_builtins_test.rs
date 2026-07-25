//! Integration tests for `anthill.persistence.Store.{persist, retract,
//! flush}` builtins (proposal 007 §4).
//!
//! Full path: an anthill program receives a `FileStore(...)` value,
//! calls `persist` + `flush` on it, the on-disk file ends up containing
//! the fact, and a fresh process can `pull` it back via `BulkStore`.


use anthill_core::eval::{Interpreter, Value};
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::file_store::{FileConvention, FileStore};
use anthill_core::persistence::{BulkStore, PersistenceError, Store};
use anthill_core::kb::term::TermId;

use crate::common::interp_for;

fn stored_reference(interp: &mut Interpreter, stored: &Value) -> Value {
    let reference = interp.kb_mut().intern("reference");
    match stored {
        Value::Entity { named, .. } => named.iter().find(|(name, _)| *name == reference)
            .map(|(_, value)| value.clone())
            .expect("StoredRef carries reference"),
        other => panic!("persist must return StoredRef, got {other:?}"),
    }
}

/// Build a `Value::Entity` matching `FileStore(root: <r>, convention: Flat)`.
/// All names go through `kb_mut().intern` — the canonical-key path doesn't
/// care whether the symbol is resolved or fresh, since both produce the
/// same short_name on `resolve_sym`. Mutable borrow because intern may
/// allocate a new symbol slot.
fn filestore_value(interp: &mut Interpreter, root: &str) -> Value {
    let fs = interp.kb_mut().intern("FileStore");
    let flat = interp.kb_mut().intern("Flat");
    let root_sym = interp.kb_mut().intern("root");
    let convention_sym = interp.kb_mut().intern("convention");
    Value::Entity {
        functor: fs,
        pos: vec![].into(),
        named: vec![
            (root_sym, Value::Str(root.to_string())),
            (convention_sym, Value::Entity {
                functor: flat,
                pos: vec![].into(),
                named: vec![].into(),
            }),
        ].into(),
    }
}

#[test]
fn persist_then_flush_writes_fact_to_disk() {
    let dir = tempfile::tempdir().expect("tempdir");
    let root = dir.path().to_path_buf();

    // We don't have a `main` lookup driver here — we call the persist /
    // flush builtins directly with constructed Values to keep the test
    // tight and avoid bringing in the full interpreter dispatch.
    let src = "namespace test.persist\n  -- placeholder\nend\n";
    let mut interp = interp_for(src);

    let store_val = filestore_value(&mut interp, root.to_str().unwrap());
    let key = interp.store_canonical_key(&store_val).expect("canonical key");

    interp.register_mirror(
        key.clone(),
        Box::new(FileStore::new(root.clone(), FileConvention::Flat)),
    );

    // Build a Foo(value: 7) entity.
    let foo_sym = interp.kb_mut().intern("Foo");
    let value_sym = interp.kb_mut().intern("value");
    let foo_val = Value::Entity {
        functor: foo_sym,
        pos: vec![].into(),
        named: vec![(value_sym, Value::Int(7))].into(),
    };

    let none_val = Value::Unit;
    let result = interp.call("anthill.persistence.Store.persist", &[store_val.clone(), foo_val, none_val.clone()])
        .expect("persist call");
    assert!(matches!(result, Value::Entity { .. }), "persist returns StoredRef");

    let nil_val = Value::Unit;  // delta arg, ignored in v1
    let flushed = interp.call("anthill.persistence.Store.flush", &[store_val.clone(), nil_val])
        .expect("flush call");
    assert!(matches!(flushed, Value::Bool(true)));

    // Verify the fact is on disk.
    let path = root.join("facts.anthill");
    assert!(path.exists(), "facts.anthill must exist after flush");
    let content = std::fs::read_to_string(&path).unwrap();
    assert!(content.contains("fact Foo(value: 7)"), "got:\n{content}");

    // Round-trip: a fresh KB pulls the fact back.
    let pull_store = FileStore::new(root, FileConvention::Flat);
    let parsed_files = pull_store.pull().expect("pull");
    let mut kb2 = KnowledgeBase::new();
    for pf in &parsed_files {
        load::load(&mut kb2, pf, &NullResolver).expect("load");
    }
    // Find the Foo fact by walking facts under the default Fact sort.
    // After pull+load, "Foo" gets a fresh symbol in kb2's namespace; we
    // don't know its qname, so we identify by the printed head shape.
    let fact_sort = kb2.make_name_term("Fact");
    let printer = anthill_core::persistence::print::TermPrinter::new(&kb2);
    let foo_count = kb2.by_sort(fact_sort)
        .into_iter()
        .filter(|&rid| printer.print_term(kb2.rule_head(rid)).contains("Foo(value: 7)"))
        .count();
    assert_eq!(foo_count, 1, "exactly one Foo(value: 7) fact after round-trip");
}

#[test]
fn failed_mirror_persist_does_not_assert_a_resident_fact() {
    // The declared adapter returns StoredRef, and its store-before-KB ordering
    // is already owned in one place:
    // an I/O failure cannot manufacture a resident-only fact.
    struct FailingStore;
    impl Store for FailingStore {
        fn persist(
            &mut self,
            _kb: &KnowledgeBase,
            _fact: TermId,
            _sort: TermId,
            _domain: TermId,
            _meta: Option<TermId>,
        ) -> Result<(), PersistenceError> {
            Err(PersistenceError::Io("deliberate test failure".into()))
        }

        fn flush(&mut self, _kb: &KnowledgeBase) -> Result<(), PersistenceError> {
            Ok(())
        }
    }

    let mut interp = interp_for("namespace test.persist_failure\n  entity Foo\nend\n");
    let store_val = filestore_value(&mut interp, "unused");
    let key = interp.store_canonical_key(&store_val).expect("canonical key");
    interp.register_mirror(key, Box::new(FailingStore));
    let foo = interp.kb_mut().try_resolve_symbol("test.persist_failure.Foo")
        .expect("declared Foo resolves");
    let fact = Value::Entity { functor: foo, pos: Vec::new().into(), named: Vec::new().into() };

    let error = interp
        .call("anthill.persistence.Store.persist", &[store_val, fact, Value::Unit])
        .expect_err("the mirror failure must surface");
    assert!(format!("{error:?}").contains("deliberate test failure"));
    assert!(
        interp.kb().rules_by_functor(foo).is_empty(),
        "a failed durable write must not leave a resident-only fact"
    );
}

#[test]
fn retract_via_builtin_removes_fact_from_disk() {
    // persist two facts, retract one via the builtin, flush, verify only
    // the surviving fact is on disk.
    let dir = tempfile::tempdir().expect("tempdir");
    let root = dir.path().to_path_buf();

    // `Bar` is declared non_monotone so the proposal-053 guard permits its
    // retract; `Foo` stays the default (monotone) and is only persisted.
    let src = "namespace test.retract\n  \
        import anthill.reflect.{fact_monotonicity, non_monotone}\n  \
        entity Bar\n  \
        rule fact_monotonicity(Bar) = non_monotone() [simp]\nend\n";
    let mut interp = interp_for(src);

    let store_val = filestore_value(&mut interp, root.to_str().unwrap());
    let key = interp.store_canonical_key(&store_val).expect("canonical key");
    interp.register_mirror(
        key.clone(),
        Box::new(FileStore::new(root.clone(), FileConvention::Flat)),
    );

    let foo_sym = interp.kb_mut().intern("Foo");
    let bar_sym = interp.kb_mut().try_resolve_symbol("test.retract.Bar")
        .expect("declared Bar resolves");
    let foo_val = Value::Entity { functor: foo_sym, pos: vec![].into(), named: vec![].into() };
    let bar_val = Value::Entity { functor: bar_sym, pos: vec![].into(), named: vec![].into() };

    let none_val = Value::Unit;
    let _foo_id = interp.call("anthill.persistence.Store.persist", &[store_val.clone(), foo_val, none_val.clone()]).unwrap();
    let bar_id = interp.call("anthill.persistence.Store.persist", &[store_val.clone(), bar_val, none_val.clone()]).unwrap();
    interp.call("anthill.persistence.Store.flush", &[store_val.clone(), Value::Unit]).unwrap();

    // Sanity: both on disk.
    let path = root.join("facts.anthill");
    let after_persist = std::fs::read_to_string(&path).unwrap();
    assert!(after_persist.contains("fact Foo"));
    assert!(after_persist.contains("fact Bar"));

    // Retract Bar. `retract` is a NonMonotonicStore-trait op (proposal 053 /
    // 007 §2); FileStore declares `fact NonMonotonicStore[FileStore]`.
    let bar_reference = stored_reference(&mut interp, &bar_id);
    let retracted = interp.call("anthill.persistence.NonMonotonicStore.retract", &[store_val.clone(), bar_reference]).unwrap();
    assert!(matches!(retracted, Value::Bool(true)));
    interp.call("anthill.persistence.Store.flush", &[store_val, Value::Unit]).unwrap();

    let after_retract = std::fs::read_to_string(&path).unwrap();
    assert!(after_retract.contains("fact Foo"), "Foo survives");
    assert!(!after_retract.contains("fact Bar"), "Bar dropped from disk:\n{after_retract}");
}

#[test]
fn update_via_builtin_replaces_a_mirrored_row_and_returns_a_fresh_reference() {
    let dir = tempfile::tempdir().expect("tempdir");
    let root = dir.path().to_path_buf();
    let src = "namespace test.update\n  \
        import anthill.reflect.{fact_monotonicity, non_monotone}\n  \
        entity Bar(value: Int64)\n  \
        rule fact_monotonicity(Bar) = non_monotone() [simp]\nend\n";
    let mut interp = interp_for(src);
    let store_val = filestore_value(&mut interp, root.to_str().unwrap());
    let key = interp.store_canonical_key(&store_val).expect("canonical key");
    interp.register_mirror(
        key,
        Box::new(FileStore::new(root.clone(), FileConvention::Flat)),
    );

    let bar = interp.kb_mut().try_resolve_symbol("test.update.Bar")
        .expect("declared Bar resolves");
    let value = interp.kb_mut().intern("value");
    let original = Value::Entity {
        functor: bar,
        pos: Vec::new().into(),
        named: vec![(value, Value::Int(1))].into(),
    };
    let persisted = interp.call(
        "anthill.persistence.Store.persist",
        &[store_val.clone(), original, Value::Unit],
    ).expect("persist");
    interp.call("anthill.persistence.Store.flush", &[store_val.clone(), Value::Unit])
        .expect("flush initial row");

    let replacement = Value::Entity {
        functor: bar,
        pos: Vec::new().into(),
        named: vec![(value, Value::Int(2))].into(),
    };
    let persisted_reference = stored_reference(&mut interp, &persisted);
    let updated = interp.call(
        "anthill.persistence.NonMonotonicStore.update",
        &[store_val.clone(), persisted_reference, replacement],
    ).expect("update");
    let Value::Entity { functor, named, .. } = updated else {
        panic!("update must return Option.some(StoredRef)");
    };
    assert_eq!(interp.kb().resolve_sym(functor), "some");
    let updated_reference = named.iter().find_map(|(_, value)| match value {
        Value::Entity { .. } => Some(stored_reference(&mut interp, value)),
        _ => None,
    }).expect("some carries StoredRef");
    assert!(matches!(updated_reference, Value::FactRef(_)));

    interp.call("anthill.persistence.Store.flush", &[store_val, Value::Unit])
        .expect("flush replacement");
    let text = std::fs::read_to_string(root.join("facts.anthill")).expect("read facts");
    assert!(!text.contains("Bar(value: 1)"), "old row must be gone: {text}");
    assert!(text.contains("Bar(value: 2)"), "replacement must persist: {text}");
}

#[test]
fn store_canonical_key_is_stable() {
    // Two anthill values that should hash to the same store handle —
    // regardless of named-arg input order — must compute the same key.
    let mut interp = interp_for("namespace test.canonical\n  -- placeholder\nend\n");
    let fs = interp.kb_mut().intern("FileStore");
    let conv = interp.kb_mut().intern("convention");
    let root = interp.kb_mut().intern("root");
    let flat = interp.kb_mut().intern("Flat");

    let v1 = Value::Entity {
        functor: fs,
        pos: vec![].into(),
        named: vec![
            (root, Value::Str("/tmp/x".into())),
            (conv, Value::Entity { functor: flat, pos: vec![].into(), named: vec![].into() }),
        ].into(),
    };
    let v2 = Value::Entity {
        functor: fs,
        pos: vec![].into(),
        named: vec![
            // reversed order
            (conv, Value::Entity { functor: flat, pos: vec![].into(), named: vec![].into() }),
            (root, Value::Str("/tmp/x".into())),
        ].into(),
    };
    let k1 = interp.store_canonical_key(&v1).unwrap();
    let k2 = interp.store_canonical_key(&v2).unwrap();
    assert_eq!(k1, k2, "canonical key must ignore named-arg input order");
    assert!(k1.contains("FileStore"));
    assert!(k1.contains("\"/tmp/x\""));
}
