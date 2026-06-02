//! WI-272 — Phase E of proposal 042: operation type arguments
//! threaded into `Frame.type_args` at call entry.
//!
//! Acceptance fixture per `docs/design/operation-call-model.md`
//! §"Operation type arguments":
//!
//! 1. `foo[Int](42)` against `operation foo[T](x: T) -> T = x` lands
//!    on a frame whose `type_args` has one entry — keyed `T`, value
//!    `sort_ref(name = Int)`. Sort-level entries (none here, since
//!    `Driver` declares no `requires`) occupy the leading positions;
//!    `T` follows in declaration order.
//! 2. A second call `foo[String]("hi")` produces a fresh frame whose
//!    `T` entry holds `sort_ref(name = String)` — per-call binding,
//!    not shared with the prior call.
//! 3. Negative case: `foo(42)` with no explicit binding produces a
//!    frame whose `T` is the typer-inferred `Int` (identical to the
//!    explicit form).
//!
//! Inspection strategy: foo's body calls a non-generic
//! `peek_dummy(0) -> Int` builtin in a `let` whose value is
//! discarded, then yields `x`. The builtin runs while foo's frame
//! is the top of the stack (builtins don't push their own frame —
//! see `dispatch_call_with_requirements`'s builtin branch), so the
//! captured channel is exactly the one the eval installed at
//! foo-call entry.

use std::sync::{Arc, Mutex};

use anthill_core::eval::{Interpreter, Value};
use anthill_core::kb::term::{Term, TermId};

use crate::common;

/// Snapshot of the frame's `type_args` channel rendered as
/// `(declared-name, type-term)` pairs. Names are resolved through the
/// kb so the assertions read naturally.
type Snapshot = Vec<(String, TermId)>;

const FIXTURE_SRC: &str = r#"
namespace test.wi272.frame
  import anthill.prelude.{Int, String}

  sort Driver
    operation foo[T](x: T) -> T =
      let _peek = peek_dummy(0)
      x
    operation peek_dummy(_: Int) -> Int
    operation driver_int() -> Int = foo[Int](42)
    operation driver_string() -> String = foo[String]("hi")
    operation driver_inferred() -> Int = foo(42)
  end
end
"#;

/// Build an interpreter loaded with the fixture and the peek_dummy
/// builtin registered to write `Frame.type_args` into `captured`.
fn fixture_interp(captured: Arc<Mutex<Option<Snapshot>>>) -> Interpreter {
    let kb = common::load_kb_with(FIXTURE_SRC);
    let mut interp = Interpreter::new(kb);
    interp.register_builtin(
        "test.wi272.frame.Driver.peek_dummy",
        move |interp, _args| {
            // The top frame is foo's (builtins run in the caller's
            // frame — no new frame push), so its `type_args` channel
            // is the one we want to assert against.
            let snap_raw = interp.top_frame_type_args_for_test();
            let snap: Snapshot = snap_raw
                .iter()
                .map(|(s, t)| (interp.kb().resolve_sym(*s).to_string(), *t))
                .collect();
            *captured.lock().unwrap() = Some(snap);
            Ok(Value::Int(0))
        },
    ).expect("register peek_dummy builtin");
    interp
}

/// Walk a `sort_ref(name = Ref(Int))` term back to its sort short name.
/// The typer encodes scalar types this way (see
/// `KnowledgeBase::make_sort_ref_by_name`); the test asserts on the
/// short name to avoid hardcoding TermId equality across runs.
fn extract_sort_ref_name(interp: &Interpreter, tid: TermId) -> Option<String> {
    // WI-361: a bare sort is the term-backed `Ref(S)` or the deep
    // `sort_ref(name: Ref(S))`; `extract_sort_ref_sym` recognizes both.
    let sym = anthill_core::kb::typing::extract_sort_ref_sym(interp.kb(), &anthill_core::kb::term_view::TermIdView(tid))?;
    let qn = interp.kb().qualified_name_of(sym);
    Some(qn.rsplit('.').next().unwrap_or(qn).to_string())
}

#[test]
fn explicit_int_binding_installs_t_on_frame() {
    let captured = Arc::new(Mutex::new(None));
    let mut interp = fixture_interp(captured.clone());

    let result = interp.call("test.wi272.frame.Driver.driver_int", &[])
        .expect("driver_int / foo[Int](42) should run");
    assert_eq!(result.as_int(), Some(42), "body returns x = 42");

    let snap = captured.lock().unwrap().clone()
        .expect("peek_dummy should have captured the frame");
    // `Driver` declares no `requires`, so the frame has no
    // sort-level entries — the type-arg channel is exactly `[T]`
    // in declaration order. (Acceptance bullet (c): "sort-level
    // first then T".)
    assert_eq!(snap.len(), 1, "expected one entry (T); got {:?}", snap);
    assert_eq!(snap[0].0, "T", "first (and only) entry's key should be `T`");
    let name = extract_sort_ref_name(&interp, snap[0].1)
        .expect("T should bind to a sort_ref(...)");
    assert_eq!(name, "Int", "T should be `Int` for foo[Int](42)");
}

#[test]
fn second_call_with_different_binding_is_per_call_fresh() {
    let captured = Arc::new(Mutex::new(None));
    let mut interp = fixture_interp(captured.clone());

    // First call: foo[Int](42).
    interp.call("test.wi272.frame.Driver.driver_int", &[])
        .expect("foo[Int](42) should run");
    let snap1 = captured.lock().unwrap().clone()
        .expect("first call should have captured");
    let name1 = extract_sort_ref_name(&interp, snap1[0].1).unwrap();
    assert_eq!(name1, "Int");

    // Second call: foo[String]("hi"). A *fresh* frame — no carry-over
    // of the first call's `T = Int`.
    interp.call("test.wi272.frame.Driver.driver_string", &[])
        .expect("foo[String](\"hi\") should run");
    let snap2 = captured.lock().unwrap().clone()
        .expect("second call should have captured");
    assert_eq!(snap2.len(), 1, "fresh frame has exactly one type-arg entry");
    let name2 = extract_sort_ref_name(&interp, snap2[0].1).unwrap();
    assert_eq!(name2, "String",
        "T should be `String` on the second call, not `Int` from the first");
}

#[test]
fn inferred_binding_matches_explicit() {
    // foo(42) with no `[T = …]` — the typer infers T = Int from the
    // arg's type. The frame's `type_args` channel should be identical
    // to `foo[Int](42)`. Negative case per design doc §"Test fixture".
    let captured = Arc::new(Mutex::new(None));
    let mut interp = fixture_interp(captured.clone());

    interp.call("test.wi272.frame.Driver.driver_inferred", &[])
        .expect("driver_inferred / foo(42) should run");
    let snap = captured.lock().unwrap().clone()
        .expect("inferred call should have captured the frame");
    assert_eq!(snap.len(), 1, "expected one entry (T); got {:?}", snap);
    assert_eq!(snap[0].0, "T");
    let name = extract_sort_ref_name(&interp, snap[0].1).unwrap();
    assert_eq!(name, "Int",
        "T should infer to `Int` from the arg literal; got `{name}`");
}
