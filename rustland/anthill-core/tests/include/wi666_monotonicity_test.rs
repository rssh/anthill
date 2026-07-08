//! WI-666 / proposal 053 — per-functor fact monotonicity runtime guard.
//!
//! The runtime write boundary (`Store.persist` / `NonMonotonicStore.retract`) consults
//! `anthill.reflect.fact_monotonicity(functor)` — the same reflect predicate
//! the language exposes — and refuses the non-monotone step loudly:
//!   * retract of a functor that is not `non_monotone` → Error;
//!   * persist (assert) of a `constant` functor → Error.
//! The default (a functor with no `fact_monotonicity` rule) is `monotone`:
//! assert succeeds, retract is refused.

use anthill_core::eval::{Interpreter, Value};
use anthill_core::persistence::file_store::{FileConvention, FileStore};

use crate::common::interp_for;

/// A `FileStore(root: <r>, convention: Flat)` value + its registration.
fn setup_store(interp: &mut Interpreter, root: &std::path::Path) -> Value {
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
                functor: flat, pos: vec![].into(), named: vec![].into(), ty: None,
            }),
        ].into(),
        ty: None,
    };
    let key = interp.store_canonical_key(&store_val).expect("canonical key");
    interp.register_store(key, Box::new(FileStore::new(root.to_path_buf(), FileConvention::Flat)));
    store_val
}

/// A nullary fact whose functor is the DECLARED entity `qname` — resolved so
/// the fact's head functor and the `fact_monotonicity(<qname>)` rule share one
/// symbol (the guard keys on the functor symbol, so identity must line up).
fn declared_fact(interp: &mut Interpreter, qname: &str) -> Value {
    let sym = interp.kb_mut().try_resolve_symbol(qname)
        .unwrap_or_else(|| panic!("resolve `{qname}` — is it declared?"));
    Value::Entity { functor: sym, pos: vec![].into(), named: vec![].into(), ty: None }
}

fn persist(interp: &mut Interpreter, store: &Value, fact: Value) -> Result<Value, anthill_core::eval::EvalError> {
    interp.call("anthill.persistence.Store.persist", &[store.clone(), fact, Value::Unit])
}

fn retract(interp: &mut Interpreter, store: &Value, id: Value) -> Result<Value, anthill_core::eval::EvalError> {
    // `retract` moved to the NonMonotonicStore trait (proposal 053 / 007 §2).
    interp.call("anthill.persistence.NonMonotonicStore.retract", &[store.clone(), id])
}

#[test]
fn assert_of_monotone_functor_succeeds() {
    // Acceptance (2): assert of a monotone (default) functor succeeds.
    let dir = tempfile::tempdir().unwrap();
    let mut interp = interp_for("namespace test.mono\n  entity Widget\nend\n");
    let store = setup_store(&mut interp, dir.path());
    let fact = declared_fact(&mut interp, "test.mono.Widget");
    let id = persist(&mut interp, &store, fact).expect("monotone functor asserts");
    assert!(matches!(id, Value::Term { .. }), "persist returns a FactId handle");
}

#[test]
fn retract_of_monotone_functor_is_loud_error() {
    // Acceptance (2): retract of a non-`non_monotone` functor is a loud error.
    let dir = tempfile::tempdir().unwrap();
    let mut interp = interp_for("namespace test.mono\n  entity Widget\nend\n");
    let store = setup_store(&mut interp, dir.path());
    let fact = declared_fact(&mut interp, "test.mono.Widget");
    let id = persist(&mut interp, &store, fact).expect("persist ok");
    let err = retract(&mut interp, &store, id).expect_err("retract of monotone must be refused");
    assert!(format!("{err:?}").contains("not non_monotone"), "wrong error: {err:?}");
}

#[test]
fn non_monotone_functor_retracts_cleanly() {
    // Acceptance (2): a functor marked `non_monotone` retracts cleanly.
    let dir = tempfile::tempdir().unwrap();
    let src = "namespace test.mono\n  \
        import anthill.reflect.{fact_monotonicity, non_monotone}\n  \
        entity Widget\n  \
        rule fact_monotonicity(Widget) = non_monotone() [simp]\nend\n";
    let mut interp = interp_for(src);
    let store = setup_store(&mut interp, dir.path());
    let fact = declared_fact(&mut interp, "test.mono.Widget");
    let id = persist(&mut interp, &store, fact).expect("persist ok");
    let ok = retract(&mut interp, &store, id).expect("non_monotone functor retracts");
    assert!(matches!(ok, Value::Bool(true)), "retract returns true");
}

#[test]
fn assert_of_constant_functor_is_loud_error() {
    // Acceptance (2): assert of a `constant` functor is a loud error.
    let dir = tempfile::tempdir().unwrap();
    let src = "namespace test.mono\n  \
        import anthill.reflect.{fact_monotonicity, constant}\n  \
        entity Frozen\n  \
        rule fact_monotonicity(Frozen) = constant() [simp]\nend\n";
    let mut interp = interp_for(src);
    let store = setup_store(&mut interp, dir.path());
    let fact = declared_fact(&mut interp, "test.mono.Frozen");
    let err = persist(&mut interp, &store, fact).expect_err("assert of constant must be refused");
    assert!(format!("{err:?}").contains("constant"), "wrong error: {err:?}");
}

#[test]
fn reflection_index_functors_are_constant() {
    // WI-665 / proposal 053: the loader-emitted structural reflection facts are
    // `constant` (frozen after load) via rules in reflect.anthill, so a runtime
    // `Store.persist` of one is a loud error — the guarantee a build-once index
    // over them relies on (`op_records` over OperationInfo today; the planned
    // `provides_index` over SortProvidesInfo, WI-660). Proves the stdlib rules
    // fire for these specific functors, not just a project-declared one
    // (`assert_of_constant_functor_is_loud_error`).
    let dir = tempfile::tempdir().unwrap();
    let mut interp = interp_for("namespace test.reflectmono\n  entity Widget\nend\n");
    let store = setup_store(&mut interp, dir.path());
    for qname in ["anthill.reflect.OperationInfo", "anthill.reflect.SortProvidesInfo"] {
        let fact = declared_fact(&mut interp, qname);
        let err = persist(&mut interp, &store, fact)
            .expect_err(&format!("assert of constant reflection functor {qname} must be refused"));
        assert!(format!("{err:?}").contains("constant"), "wrong error for {qname}: {err:?}");
    }
}
