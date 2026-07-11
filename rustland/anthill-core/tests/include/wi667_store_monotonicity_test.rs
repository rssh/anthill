//! WI-667 / proposals 053 + 007 §2 — external-store fact monotonicity and the
//! trait/policy capability model.
//!
//! Two kinds of store capability:
//!   * PROVISION — a trait carrying an op. `retract` moved out of base `Store`
//!     onto `NonMonotonicStore`; it dispatches as
//!     `anthill.persistence.NonMonotonicStore.retract` (retargeted from
//!     `Store.retract`). Backends declare `fact NonMonotonicStore[X]`.
//!   * POLICY — a per-functor value over the universal write ops, answered by
//!     `Store.monotonicity(store, functor)`: a QUERY read to plan, never by
//!     attempting a write. It resolves to the owning store's authority — an
//!     in-memory reflect rule, else the store's materialized policy, else the
//!     `monotone` default.
//!
//! Acceptance:
//!   (1) `Store.monotonicity(store, functor)` is queryable per functor, read
//!       WITHOUT a write.
//!   (2) a synthetic store-owned functor (no in-memory reflect rule) resolves
//!       to the store's policy, not the in-memory `monotone` default.
//!   (3) a NonMonotonicStore backend that cannot honor a declared non_monotone
//!       retract fails LOUD via the Error effect at the write.

use anthill_core::eval::{EvalError, Interpreter, Value};
use anthill_core::kb::term::TermId;
use anthill_core::kb::{KnowledgeBase, RuleId};
use anthill_core::persistence::file_store::{FileConvention, FileStore};
use anthill_core::persistence::{Monotonicity, PersistenceError, Store};

use crate::common::interp_for;

// ── A synthetic policy-bearing store ────────────────────────────
//
// Unlike the filesystem backends (whose per-functor policy IS the project's
// reflect rules, so `owned_monotonicity` returns `[]`), this mock is the
// authority for its own functor: it declares the functor's policy intrinsically
// via `owned_monotonicity`, which `register_store` materializes into the
// facade. Also lets `retract` be forced to fail, exercising acceptance (3).
struct PolicyStore {
    /// Qualified functor name this store owns and its declared write policy.
    functor: String,
    policy: Monotonicity,
    /// When true, `retract` fails (a backend that cannot honor its declared
    /// non_monotone retract) — the write must surface loudly via `Error`.
    fail_retract: bool,
}

impl Store for PolicyStore {
    fn persist(
        &mut self,
        _kb: &KnowledgeBase,
        _fact: TermId,
        _sort: TermId,
        _domain: TermId,
        _meta: Option<TermId>,
    ) -> Result<(), PersistenceError> {
        Ok(())
    }

    fn retract(&mut self, _kb: &KnowledgeBase, _id: RuleId) -> Result<bool, PersistenceError> {
        if self.fail_retract {
            Err(PersistenceError::Io("backend cannot delete this row".into()))
        } else {
            Ok(true)
        }
    }

    fn flush(&mut self, _kb: &KnowledgeBase) -> Result<(), PersistenceError> {
        Ok(())
    }

    fn owned_monotonicity(&self) -> Vec<(String, Monotonicity)> {
        vec![(self.functor.clone(), self.policy)]
    }
}

/// A `PolicyStore()`-shaped store value (canonical-key basis) + its registration.
fn register_policy_store(interp: &mut Interpreter, mock: PolicyStore) -> Value {
    let functor = interp.kb_mut().intern("PolicyStore");
    let store_val = Value::Entity {
        functor,
        pos: vec![].into(),
        named: vec![].into(),
    };
    let key = interp.store_canonical_key(&store_val).expect("canonical key");
    interp.register_store(key, Box::new(mock));
    store_val
}

/// A `FileStore(root, Flat)` value + its registration (reused from the WI-666
/// setup shape).
fn register_file_store(interp: &mut Interpreter, root: &std::path::Path) -> Value {
    let fs = interp.kb_mut().intern("FileStore");
    let flat = interp.kb_mut().intern("Flat");
    let root_sym = interp.kb_mut().intern("root");
    let convention_sym = interp.kb_mut().intern("convention");
    let store_val = Value::Entity {
        functor: fs,
        pos: vec![].into(),
        named: vec![
            (root_sym, Value::Str(root.to_str().unwrap().to_string())),
            (convention_sym, Value::Entity {
                functor: flat, pos: vec![].into(), named: vec![].into(),
            }),
        ].into(),
    };
    let key = interp.store_canonical_key(&store_val).expect("canonical key");
    interp.register_store(key, Box::new(FileStore::new(root.to_path_buf(), FileConvention::Flat)));
    store_val
}

/// A nullary carrier whose head functor is the declared entity `qname` — the
/// `Symbol` argument to `monotonicity` / the fact to persist.
fn functor_value(interp: &mut Interpreter, qname: &str) -> Value {
    let sym = interp.kb_mut().try_resolve_symbol(qname)
        .unwrap_or_else(|| panic!("resolve `{qname}` — is it declared?"));
    Value::Entity { functor: sym, pos: vec![].into(), named: vec![].into() }
}

fn monotonicity(interp: &mut Interpreter, store: &Value, functor: Value) -> Result<Value, EvalError> {
    interp.call("anthill.persistence.Store.monotonicity", &[store.clone(), functor])
}

fn persist(interp: &mut Interpreter, store: &Value, fact: Value) -> Result<Value, EvalError> {
    interp.call("anthill.persistence.Store.persist", &[store.clone(), fact, Value::Unit])
}

fn retract(interp: &mut Interpreter, store: &Value, id: Value) -> Result<Value, EvalError> {
    interp.call("anthill.persistence.NonMonotonicStore.retract", &[store.clone(), id])
}

/// Assert the reflect `Monotonicity` entity `v` is the `<variant>` variant.
fn assert_variant(interp: &mut Interpreter, v: &Value, variant: &str) {
    let qname = format!("anthill.reflect.Monotonicity.{variant}");
    let expected = interp.kb_mut().try_resolve_symbol(&qname)
        .unwrap_or_else(|| panic!("resolve `{qname}`"));
    match v {
        Value::Entity { functor, .. } => assert_eq!(
            *functor, expected,
            "expected Monotonicity.{variant}, got a different variant",
        ),
        other => panic!("expected a Monotonicity entity, got {other:?}"),
    }
}

#[test]
fn monotonicity_query_reads_reflect_rule_without_a_write() {
    // Acceptance (1): `monotonicity(store, functor)` answers per functor as a
    // pure query — a functor with a `non_monotone` reflect rule reports
    // non_monotone, an unlisted functor reports the monotone default, and
    // NOTHING is written to the store.
    let dir = tempfile::tempdir().unwrap();
    let src = "namespace test.q1\n  \
        import anthill.reflect.{fact_monotonicity, non_monotone}\n  \
        entity Widget\n  \
        entity Gadget\n  \
        rule fact_monotonicity(Widget) = non_monotone() [simp]\nend\n";
    let mut interp = interp_for(src);
    let store = register_file_store(&mut interp, dir.path());

    let widget = functor_value(&mut interp, "test.q1.Widget");
    let ans = monotonicity(&mut interp, &store, widget).expect("query ok");
    assert_variant(&mut interp, &ans, "non_monotone");

    let gadget = functor_value(&mut interp, "test.q1.Gadget");
    let ans = monotonicity(&mut interp, &store, gadget).expect("query ok");
    assert_variant(&mut interp, &ans, "monotone");

    // Read WITHOUT a write: the query never buffered/flushed anything.
    assert!(
        !dir.path().join("facts.anthill").exists(),
        "monotonicity query must not write to the store",
    );
}

#[test]
fn external_functor_resolves_to_store_policy_not_default() {
    // Acceptance (2): `Ghost` has NO in-memory reflect rule. Its owning store
    // declares it non_monotone, materialized at registration — so the facade
    // resolves to the store's policy, not the in-memory `monotone` default.
    let src = "namespace test.syn\n  entity Ghost\nend\n";
    let mut interp = interp_for(src);
    let store = register_policy_store(&mut interp, PolicyStore {
        functor: "test.syn.Ghost".into(),
        policy: Monotonicity::NonMonotone,
        fail_retract: false,
    });

    let ghost = functor_value(&mut interp, "test.syn.Ghost");
    let ans = monotonicity(&mut interp, &store, ghost).expect("query ok");
    assert_variant(&mut interp, &ans, "non_monotone");
}

#[test]
fn store_policy_permits_retract_through_the_guard() {
    // Acceptance (2), behavioral: the retract guard reads the same facade, so a
    // store-declared non_monotone functor retracts cleanly even with no
    // in-memory rule. (Without the store policy it would be the monotone
    // default and the guard would refuse.)
    let src = "namespace test.syn\n  entity Ghost\nend\n";
    let mut interp = interp_for(src);
    let store = register_policy_store(&mut interp, PolicyStore {
        functor: "test.syn.Ghost".into(),
        policy: Monotonicity::NonMonotone,
        fail_retract: false,
    });

    let fact = functor_value(&mut interp, "test.syn.Ghost");
    let id = persist(&mut interp, &store, fact).expect("persist ok");
    let ok = retract(&mut interp, &store, id).expect("store-declared non_monotone retracts");
    assert!(matches!(ok, Value::Bool(true)), "retract returns true");
}

#[test]
fn declared_non_monotone_but_backend_cannot_retract_is_loud_error() {
    // Acceptance (3): the guard passes (functor is declared non_monotone by the
    // store), but the backend's retract fails — it must surface LOUDLY via the
    // Error effect at the write, not a silent no-op or a static load check.
    let src = "namespace test.syn\n  entity Ghost\nend\n";
    let mut interp = interp_for(src);
    let store = register_policy_store(&mut interp, PolicyStore {
        functor: "test.syn.Ghost".into(),
        policy: Monotonicity::NonMonotone,
        fail_retract: true,
    });

    let fact = functor_value(&mut interp, "test.syn.Ghost");
    let id = persist(&mut interp, &store, fact).expect("persist ok");
    let err = retract(&mut interp, &store, id)
        .expect_err("a failing backend retract must surface loudly");
    let shown = format!("{err:?}");
    assert!(
        shown.contains("retract failed") && shown.contains("cannot delete"),
        "expected an Error-effect retract failure, got: {shown}",
    );
}

#[test]
fn append_only_default_store_cannot_retract() {
    // The Rust-side gate: a backend that does NOT override `retract` (does not
    // provide NonMonotonicStore) fails loudly if ever asked — mirroring how
    // `retrieve` defaults to NotQueryable. Here the store declares its functor
    // non_monotone so the *guard* passes, isolating the trait-default gate.
    struct AppendOnly;
    impl Store for AppendOnly {
        fn persist(&mut self, _kb: &KnowledgeBase, _f: TermId, _s: TermId, _d: TermId, _m: Option<TermId>)
            -> Result<(), PersistenceError> { Ok(()) }
        fn flush(&mut self, _kb: &KnowledgeBase) -> Result<(), PersistenceError> { Ok(()) }
        fn owned_monotonicity(&self) -> Vec<(String, Monotonicity)> {
            vec![("test.syn.Ghost".into(), Monotonicity::NonMonotone)]
        }
        // no `retract` override → inherits the NotMutable default gate.
    }
    let src = "namespace test.syn\n  entity Ghost\nend\n";
    let mut interp = interp_for(src);
    let functor = interp.kb_mut().intern("AppendOnly");
    let store = Value::Entity { functor, pos: vec![].into(), named: vec![].into() };
    let key = interp.store_canonical_key(&store).expect("key");
    interp.register_store(key, Box::new(AppendOnly));

    let fact = functor_value(&mut interp, "test.syn.Ghost");
    let id = persist(&mut interp, &store, fact).expect("persist ok");
    let err = retract(&mut interp, &store, id)
        .expect_err("an append-only backend cannot retract");
    let shown = format!("{err:?}");
    assert!(shown.contains("append-only"), "expected the NotMutable gate, got: {shown}");
}
