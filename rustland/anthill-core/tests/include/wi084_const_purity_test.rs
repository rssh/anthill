//! WI-084 / proposal 039 — term-level constants, the **purity gate** (the
//! remaining Phase-3 piece).
//!
//! An anthill-bodied `const` must fold to a value PURELY: its body may not
//! invoke an effectful operation (a non-empty declared effect row — e.g. an
//! allocator's `Modify[result]`). A const denotes ONE memoized value shared by
//! every reference, so an effectful body is unsound (the generativity hazard:
//! `Cell.new() != Cell.new()`). The gate is a static, LOAD-time check
//! (`check_const_purity` in kb/load.rs), conservative by construction: only
//! provably-pure forms are accepted; unrecognized / dynamically-dispatched
//! forms are rejected, so it can never silently admit an effect.
//!
//! Bodyless (host-supplied) consts have no body and are trusted — not checked.

use crate::common::try_load_kb_with;

fn errs(r: Result<anthill_core::kb::KnowledgeBase, Vec<String>>) -> String {
    match r {
        Ok(_) => String::new(),
        Err(es) => es.join("\n"),
    }
}

#[test]
fn allocator_bodied_const_is_rejected_at_load() {
    // `Cell.new` carries `effects Modify[result]` (027.1), so memoizing its
    // result would share one cell across all references — the bug the gate
    // prevents. This must be a load-time error.
    let src = r#"
namespace test.wi084purity.alloc
  import anthill.prelude.{Int64, Cell}
  const COUNTER: Cell[T = Int64] = Cell.new(0)
end
"#;
    let joined = errs(try_load_kb_with(src));
    assert!(
        joined.contains("COUNTER") && (joined.contains("effectful") || joined.contains("Cell.new")),
        "an allocator-bodied const must be rejected at load; got:\n{joined}"
    );
}

#[test]
fn const_calling_an_error_effect_op_is_rejected() {
    // Not just allocators: ANY non-empty effect row disqualifies a body. A
    // user op declaring `effects Error` makes a const that calls it impure.
    let src = r#"
namespace test.wi084purity.errfx
  import anthill.prelude.{Int64}
  operation risky() -> Int64
    effects Error
    = 1
  const X: Int64 = risky()
end
"#;
    let joined = errs(try_load_kb_with(src));
    assert!(
        joined.contains("X") && (joined.contains("effectful") || joined.contains("risky")),
        "a const calling an Error-effect op must be rejected; got:\n{joined}"
    );
}

#[test]
fn effectful_call_buried_in_composition_is_rejected() {
    // The walk must descend into composition (here a `let` rhs), not just check
    // the top-level form — an effectful call anywhere in the body disqualifies it.
    let src = r#"
namespace test.wi084purity.buried
  import anthill.prelude.{Int64}
  operation risky() -> Int64
    effects Error
    = 1
  const BAD: Int64 =
    let x = risky()
    x
end
"#;
    let joined = errs(try_load_kb_with(src));
    assert!(
        joined.contains("BAD") && (joined.contains("effectful") || joined.contains("risky")),
        "an effectful call buried in a let must still be rejected; got:\n{joined}"
    );
}

#[test]
fn pure_const_bodies_still_load() {
    // Regression: the gate must NOT reject pure bodies — literals, arithmetic
    // (a pure operation call), references to other consts, and composition.
    let src = r#"
namespace test.wi084purity.ok
  import anthill.prelude.{Int64, Float}
  const N: Int64 = -1
  const PI: Float = 3.0
  const TWO_PI: Float = 2.0 * PI
  operation pure_double(x: Int64) -> Int64 = x
  const D: Int64 = pure_double(21)
end
"#;
    let r = try_load_kb_with(src);
    assert!(r.is_ok(), "pure const bodies must load cleanly:\n{}", errs(r));
}

#[test]
fn const_calling_a_pure_user_op_loads() {
    // A const whose body calls a user operation with an EMPTY effect row is
    // pure and loads — confirming the gate checks the declared effect row, not
    // merely "is it a call".
    let src = r#"
namespace test.wi084purity.pureop
  import anthill.prelude.{Int64}
  operation inc(x: Int64) -> Int64 = x
  const ONE_INC: Int64 = inc(1)
end
"#;
    let r = try_load_kb_with(src);
    assert!(r.is_ok(), "a const calling a pure op must load:\n{}", errs(r));
}
