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
use anthill_core::persistence::BulkStore;

use crate::common::interp_for;

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
        pos: vec![],
        named: vec![
            (root_sym, Value::Str(root.to_string())),
            (convention_sym, Value::Entity {
                functor: flat,
                pos: vec![],
                named: vec![],
            }),
        ],
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

    interp.register_store(
        key.clone(),
        Box::new(FileStore::new(root.clone(), FileConvention::Flat)),
    );

    // Build a Foo(value: 7) entity.
    let foo_sym = interp.kb_mut().intern("Foo");
    let value_sym = interp.kb_mut().intern("value");
    let foo_val = Value::Entity {
        functor: foo_sym,
        pos: vec![],
        named: vec![(value_sym, Value::Int(7))],
    };

    let none_val = Value::Unit;
    let result = interp.call("anthill.persistence.Store.persist", &[store_val.clone(), foo_val, none_val.clone()])
        .expect("persist call");
    // The persist builtin returns a FactId-shaped Value::Term.
    assert!(matches!(result, Value::Term(_)));

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
fn retract_via_builtin_removes_fact_from_disk() {
    // persist two facts, retract one via the builtin, flush, verify only
    // the surviving fact is on disk.
    let dir = tempfile::tempdir().expect("tempdir");
    let root = dir.path().to_path_buf();

    let src = "namespace test.retract\n  -- placeholder\nend\n";
    let mut interp = interp_for(src);

    let store_val = filestore_value(&mut interp, root.to_str().unwrap());
    let key = interp.store_canonical_key(&store_val).expect("canonical key");
    interp.register_store(
        key.clone(),
        Box::new(FileStore::new(root.clone(), FileConvention::Flat)),
    );

    let foo_sym = interp.kb_mut().intern("Foo");
    let bar_sym = interp.kb_mut().intern("Bar");
    let foo_val = Value::Entity { functor: foo_sym, pos: vec![], named: vec![] };
    let bar_val = Value::Entity { functor: bar_sym, pos: vec![], named: vec![] };

    let none_val = Value::Unit;
    let _foo_id = interp.call("anthill.persistence.Store.persist", &[store_val.clone(), foo_val, none_val.clone()]).unwrap();
    let bar_id = interp.call("anthill.persistence.Store.persist", &[store_val.clone(), bar_val, none_val.clone()]).unwrap();
    interp.call("anthill.persistence.Store.flush", &[store_val.clone(), Value::Unit]).unwrap();

    // Sanity: both on disk.
    let path = root.join("facts.anthill");
    let after_persist = std::fs::read_to_string(&path).unwrap();
    assert!(after_persist.contains("fact Foo"));
    assert!(after_persist.contains("fact Bar"));

    // Retract Bar.
    let retracted = interp.call("anthill.persistence.Store.retract", &[store_val.clone(), bar_id]).unwrap();
    assert!(matches!(retracted, Value::Bool(true)));
    interp.call("anthill.persistence.Store.flush", &[store_val, Value::Unit]).unwrap();

    let after_retract = std::fs::read_to_string(&path).unwrap();
    assert!(after_retract.contains("fact Foo"), "Foo survives");
    assert!(!after_retract.contains("fact Bar"), "Bar dropped from disk:\n{after_retract}");
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
        pos: vec![],
        named: vec![
            (root, Value::Str("/tmp/x".into())),
            (conv, Value::Entity { functor: flat, pos: vec![], named: vec![] }),
        ],
    };
    let v2 = Value::Entity {
        functor: fs,
        pos: vec![],
        named: vec![
            // reversed order
            (conv, Value::Entity { functor: flat, pos: vec![], named: vec![] }),
            (root, Value::Str("/tmp/x".into())),
        ],
    };
    let k1 = interp.store_canonical_key(&v1).unwrap();
    let k2 = interp.store_canonical_key(&v2).unwrap();
    assert_eq!(k1, k2, "canonical key must ignore named-arg input order");
    assert!(k1.contains("FileStore"));
    assert!(k1.contains("\"/tmp/x\""));
}
