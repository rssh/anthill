//! Integration tests for WI-072 — the `Modify` effect handler.
//! Exercises the arena-backed default handler registered via
//! `default_modify_handler()` plus the `Modify.get` / `Modify.set`
//! builtins that route through it.

mod common;

use anthill_core::eval::{EvalError, Value};

use common::{interp_for, register_modify_handler};

#[test]
fn m5_modify_counter_write_then_read() {
    let src = r#"
namespace test.m5_counter
  import anthill.prelude.{Int, Unit}
  import Modify.{get, set}

  sort CounterState
    entity counter
  end

  operation write(n: Int) -> Unit = set(counter(), n)
  operation read() -> Int = get(counter())
end
"#;
    let mut interp = interp_for(src);
    register_modify_handler(&mut interp);

    interp.call("test.m5_counter.write", &[Value::Int(42)]).expect("write");
    let got = interp.call("test.m5_counter.read", &[]).expect("read");
    assert_eq!(got.as_int(), Some(42), "read returns last-set value");

    interp.call("test.m5_counter.write", &[Value::Int(7)]).expect("overwrite");
    let got = interp.call("test.m5_counter.read", &[]).expect("read again");
    assert_eq!(got.as_int(), Some(7), "subsequent read sees the overwrite");
}

#[test]
fn m5_modify_get_before_set_errors() {
    let src = r#"
namespace test.m5_unset
  import anthill.prelude.{Int}
  import Modify.{get}

  sort CounterState
    entity counter
  end

  operation read() -> Int = get(counter())
end
"#;
    let mut interp = interp_for(src);
    register_modify_handler(&mut interp);

    let err = interp.call("test.m5_unset.read", &[]).unwrap_err();
    match err {
        EvalError::Internal(msg) => assert!(msg.contains("no value set"), "got {msg}"),
        other => panic!("expected Internal 'no value set', got {other:?}"),
    }
}

#[test]
fn m5_modify_two_resources_are_independent() {
    // Two distinct resource entities should not share state.
    let src = r#"
namespace test.m5_independent
  import anthill.prelude.{Int, Unit}
  import Modify.{get, set}

  sort Cells
    entity a
    entity b
  end

  operation put_a(n: Int) -> Unit = set(a(), n)
  operation put_b(n: Int) -> Unit = set(b(), n)
  operation get_a() -> Int = get(a())
  operation get_b() -> Int = get(b())
end
"#;
    let mut interp = interp_for(src);
    register_modify_handler(&mut interp);
    interp.call("test.m5_independent.put_a", &[Value::Int(1)]).unwrap();
    interp.call("test.m5_independent.put_b", &[Value::Int(99)]).unwrap();
    let a = interp.call("test.m5_independent.get_a", &[]).unwrap();
    let b = interp.call("test.m5_independent.get_b", &[]).unwrap();
    assert_eq!(a.as_int(), Some(1));
    assert_eq!(b.as_int(), Some(99));
}

#[test]
fn m5_modify_self_referential_set_errors_with_cyclic_reference() {
    // `set(counter, counter)` would store the resource-identifier entity
    // as its own value — the simplest self-cycle. The handler's bounded
    // structural walk catches this.
    let src = r#"
namespace test.m5_cycle
  import anthill.prelude.{Unit}
  import Modify.{set}

  sort CycleState
    entity counter
  end

  operation bad() -> Unit = set(counter(), counter())
end
"#;
    let mut interp = interp_for(src);
    register_modify_handler(&mut interp);
    let err = interp.call("test.m5_cycle.bad", &[]).unwrap_err();
    assert!(
        matches!(err, EvalError::CyclicReference),
        "expected CyclicReference, got {err:?}",
    );
}

#[test]
fn m5_modify_rust_side_roundtrip() {
    // Drive Modify directly through the handler from Rust — no anthill
    // program involved. Confirms the arena is usable by host-side code
    // (e.g. for seeding initial state before an anthill entry point).
    let mut interp = interp_for("namespace test.m5_rs end\n");
    register_modify_handler(&mut interp);

    // Minimal Entity-shaped target: a nullary constructor the anthill
    // side hasn't declared. We intern the symbol directly.
    let target_sym = interp.kb_mut().intern("rs_counter");
    let target = Value::Entity { functor: target_sym, pos: Vec::new(), named: Vec::new() };

    let set_sym = interp.kb_mut().intern("set");
    interp.invoke_effect_handler("Modify", set_sym, &[target.clone(), Value::Int(100)])
        .expect("set ok");
    let get_sym = interp.kb_mut().intern("get");
    let got = interp.invoke_effect_handler("Modify", get_sym, &[target])
        .expect("get ok");
    assert_eq!(got.as_int(), Some(100));
}

#[test]
fn m5_modify_handler_taken_is_none() {
    // take_effect_handler pulls the handler out; subsequent invoke should
    // surface a clean "no handler" error rather than panicking.
    let mut interp = interp_for("namespace test.m5_take end\n");
    register_modify_handler(&mut interp);
    let taken = interp.take_effect_handler("Modify");
    assert!(taken.is_some(), "take returns the previously-registered handler");

    let target_sym = interp.kb_mut().intern("x");
    let target = Value::Entity { functor: target_sym, pos: Vec::new(), named: Vec::new() };
    let get_sym = interp.kb_mut().intern("get");
    let err = interp.invoke_effect_handler("Modify", get_sym, &[target]).unwrap_err();
    assert!(
        matches!(&err, EvalError::Internal(m) if m.contains("no handler")),
        "expected 'no handler' Internal, got {err:?}",
    );
}
