//! Integration tests for M1 of the expression evaluator (WI-042).
//!
//! Covers: integer/bool literals, variable binding via `let`, `if` branching,
//! and operation-to-operation calls with positional arguments.

mod common;

use anthill_core::eval::{EvalError, Interpreter, Value};

use common::load_kb_with;

fn expect_int(v: Value) -> i64 {
    v.as_int().unwrap_or_else(|| panic!("expected Int, got {v:?}"))
}

#[test]
fn m1_literal_return() {
    let src = r#"
namespace test.m1_lit
  operation main() -> Int
    = 42
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m1_lit.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 42);
}

#[test]
fn m1_if_true_then_else() {
    let src_true = r#"
namespace test.m1_if_true
  operation main() -> Int
    = if true then 1 else 2
end
"#;
    let kb = load_kb_with(src_true);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m1_if_true.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 1);
}

#[test]
fn m1_if_false_then_else() {
    let src = r#"
namespace test.m1_if_false
  operation main() -> Int
    = if false then 1 else 2
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m1_if_false.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 2);
}

#[test]
fn m1_let_binds_local() {
    // Block-style let: `let x = value <newline> body` (no `in` keyword).
    let src = r#"
namespace test.m1_let
  operation main() -> Int
    = let x = 7
      x
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m1_let.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 7);
}

#[test]
fn m1_operation_call() {
    // `main` calls a zero-arg helper that returns a literal.
    let src = r#"
namespace test.m1_call
  operation helper() -> Int
    = 11
  operation main() -> Int
    = helper()
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m1_call.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 11);
}

#[test]
fn m1_operation_call_with_arg() {
    // Identity operation exercises param binding + arg plumbing.
    let src = r#"
namespace test.m1_arg
  operation id(x: Int) -> Int
    = x
  operation main() -> Int
    = id(99)
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    let result = interp.call("test.m1_arg.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 99);
}

#[test]
fn m1_non_tail_recursion_hits_depth_cap() {
    // Non-tail recursion (the recursive call wrapped in a `let` makes this
    // frame non-trivially "waiting"): each call genuinely adds an activation
    // frame and the cap catches runaway recursion. Tail infinite recursion
    // would instead loop forever under TCO — see `m1_tail_recursion_deep`.
    let src = r#"
namespace test.m1_non_tail
  operation f() -> Int =
    let _ = f()
    0
  operation main() -> Int = f()
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    interp.set_stack_depth_cap(64);
    let err = interp.call("test.m1_non_tail.main", &[]).unwrap_err();
    match err {
        EvalError::DepthExceeded { cap } => assert_eq!(cap, 64),
        other => panic!("expected DepthExceeded, got {other:?}"),
    }
}

#[test]
fn m1_infinite_tail_loop_hits_step_cap() {
    // TCO makes `loop() = loop()` run in O(1) stack. Without a step cap
    // that's an infinite time loop — `depth_cap` can't catch it because
    // the stack doesn't grow. `step_cap` is the orthogonal limit designed
    // for this: it bounds wall-time work, not memory. Together the two
    // caps cover the full recursion failure-mode matrix.
    let src = r#"
namespace test.m1_loop
  operation loop() -> Int = loop()
  operation main() -> Int = loop()
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::with_config(
        kb,
        anthill_core::eval::EvalConfig {
            depth_cap: None,
            step_cap: Some(1_000),
        },
    );
    let err = interp.call("test.m1_loop.main", &[]).unwrap_err();
    match err {
        EvalError::StepsExhausted { cap } => assert_eq!(cap, 1_000),
        other => panic!("expected StepsExhausted, got {other:?}"),
    }
}

#[test]
fn m1_recursive_operation_multi_level() {
    // Multi-level recursive operation using only M1 primitives (no
    // arithmetic, no pattern matching). The recursion is terminated by a
    // Bool-threaded state machine: each call tightens the args toward the
    // base case `(true, true) -> 42`, taking 3 tail calls from the initial
    // `(false, false)`. Proves operation-call recursion works at M1 and
    // that TCO keeps all three calls in a constant-depth stack — cap=2
    // would suffice; we use 4 to keep headroom for the test driver.
    let src = r#"
namespace test.m1_rec
  operation go(a: Bool, b: Bool) -> Int =
    if a then
      if b then 42
      else go(true, true)
    else go(true, false)
  operation main() -> Int = go(false, false)
end
"#;
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    interp.set_stack_depth_cap(4);
    let result = interp.call("test.m1_rec.main", &[]).expect("call main");
    assert_eq!(expect_int(result), 42);
}
