//! WI-782 — an arrow's PARAMETER LIST is applied positionally, so the type
//! relation over it must align positionally too.
//!
//! `align_named_tuple_fields` tried a by-NAME rung first in BOTH `TupleAlign`
//! modes. That rung is order-insensitive and width-subtyping, and the runtime is
//! neither: eval binds slot `i` to argument `i` and passes exactly as many
//! arguments as the call site's type says. Two programs slipped through, both
//! load-clean on the pre-fix tree:
//!
//!   1. ORDER — `(y: Bool, x: Int64) -> Int64` satisfied `(x: Int64, y: Bool) ->
//!      Int64` because the same NAMES occur on both sides. Applied positionally,
//!      `f(7, true)` then put `7` into the `Bool` slot: an operation declared
//!      `-> Int64` evaluated to `Bool(true)`, no trap.
//!   2. ARITY — a 2-parameter callback satisfied a 3-parameter one, the extra
//!      field width-ignored, then trapped `ArityMismatch{expected:2, got:3}`.
//!
//! (1) is why these are driven end-to-end rather than asserted at load: its
//! symptom was a wrong-typed VALUE, which no load-verdict assertion sees. Both
//! are now refused at load, so each rejection below is paired with a neighbouring
//! program that must still load and evaluate — a fix that merely rejected more
//! would satisfy the rejections alone.
//!
//! `ParamList` now ignores binder names entirely: equal arity, then a straight
//! index zip. Names label slots and are not part of the correspondence (see
//! `docs/kernel-language.md` §Arrow types), which is what lets a named-binder
//! callback take an eta arrow — and the permutation in (1) is caught by the
//! TYPES at each slot rather than by a name test.
//!
//! STILL OPEN, deliberately: WI-782's third case, where the param slot does not
//! record parameter-list ARITY, so a one-tuple-parameter operation is the same
//! term as an n-parameter one. `known_gap_*` below pins its current behavior. It
//! is deferred to WI-791 with a measured reason: the obvious fix (wrap the
//! arity-1 tuple-typed list at the mint) was implemented and REVERTED, because
//! the wrap is decided from the spelling at mint time but read back after
//! substitution — it leaked into a type variable and broke
//! `apply1(get_a, (a: 1, b: 2))`, a program that works today.

use crate::common::{interp_for, try_load_kb_with};

fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// Assert the program is refused AND that the diagnostic names both arrow
/// spellings adjacently, in the loader's own `expected …, got …` phrasing — the
/// weaker "mentions both somewhere" would also be satisfied by an unrelated
/// error that happened to print two arrow types.
fn assert_refused_naming(src: &str, expected: &str, got: &str) {
    let errs = match try_load_kb_with(src) {
        Ok(_) => panic!(
            "must NOT load: a parameter list is applied positionally, so `{got}` \
             cannot stand where `{expected}` is required"
        ),
        Err(errs) => errs,
    };
    let wanted = format!("expected {expected}, got {got}");
    assert!(
        errs.iter().any(|e| e.contains("type mismatch") && e.contains(&wanted)),
        "rejection must be a type mismatch reading `{wanted}`; got: {errs:?}",
    );
}

// ── (1) ORDER ──────────────────────────────────────────────────

/// THE case that returned a wrong-typed value. `impl` binds `(y: Bool, x:
/// Int64)`; `take` applies its callback as `f(7, true)`. Matching the two lists
/// by NAME pairs `x` with `x` and `y` with `y` and finds them compatible, but
/// nothing ever reorders the ARGUMENTS, so `7` reached the `Bool` binder and
/// `drive`, declared `-> Int64`, evaluated to `Bool(true)`.
#[test]
fn permuted_parameter_list_is_refused() {
    assert_refused_naming(
        r#"
namespace test.wi782.order
  import anthill.prelude.{Int64, Bool}
  operation take(f: (x: Int64, y: Bool) -> Int64) -> Int64
    = f(7, true)
  operation pass(g: (y: Bool, x: Int64) -> Int64) -> Int64
    = take(g)
  operation impl(y: Bool, x: Int64) -> Int64
    = x
  operation drive() -> Int64
    = pass(impl)
end
"#,
        "(x: Int64, y: Bool) -> Int64",
        "(y: Bool, x: Int64) -> Int64",
    );
}

/// The control: the same program with the parameters in the DECLARED order still
/// loads and evaluates. Without it, a fix that rejected every named parameter
/// list would pass the test above.
#[test]
fn same_order_parameter_list_still_applies() {
    let src = r#"
namespace test.wi782.sameorder
  import anthill.prelude.{Int64}
  operation take(f: (x: Int64, y: Int64) -> Int64) -> Int64
    = f(10, 3)
  operation pass(g: (x: Int64, y: Int64) -> Int64) -> Int64
    = take(g)
  operation minus(x: Int64, y: Int64) -> Int64
    = x - y
  operation drive() -> Int64
    = pass(minus)
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi782.sameorder.drive"), 7);
}

/// Binder names are labels on slots, not part of the correspondence: two lists
/// that differ ONLY in what they call their slots still relate. This is the
/// other half of dropping the by-name rung — the fix must not replace
/// "matched by name" with "must be named the same", which would reject
/// alpha-renaming.
#[test]
fn differently_named_parameter_lists_still_relate() {
    let src = r#"
namespace test.wi782.renamed
  import anthill.prelude.{Int64}
  operation take(f: (x: Int64, y: Int64) -> Int64) -> Int64
    = f(10, 3)
  operation pass(g: (p: Int64, q: Int64) -> Int64) -> Int64
    = take(g)
  operation minus(p: Int64, q: Int64) -> Int64
    = p - q
  operation drive() -> Int64
    = pass(minus)
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi782.renamed.drive"), 7);
}

// ── (2) ARITY ──────────────────────────────────────────────────

/// Width subtyping is not available to a parameter list: `take3` applies its
/// callback with THREE arguments, so a 2-parameter value is not a supertype of a
/// 3-parameter one — it is an `ArityMismatch` waiting to happen, which is exactly
/// what it used to be (trapped `expected: 2, got: 3` at eval).
#[test]
fn narrower_parameter_list_is_refused() {
    assert_refused_naming(
        r#"
namespace test.wi782.arity
  import anthill.prelude.{Int64}
  operation take3(f: (a: Int64, b: Int64, c: Int64) -> Int64) -> Int64
    = f(1, 2, 3)
  operation pass2(g: (a: Int64, b: Int64) -> Int64) -> Int64
    = take3(g)
  operation impl2(a: Int64, b: Int64) -> Int64
    = a - b
  operation drive() -> Int64
    = pass2(impl2)
end
"#,
        "(a: Int64, b: Int64, c: Int64) -> Int64",
        "(a: Int64, b: Int64) -> Int64",
    );
}

// ── the positional rung this must NOT break ────────────────────

/// The WI-442 / WI-775 shape the positional correspondence exists for, and the
/// only one measured to reach it anywhere in the workspace: a multi-param op's
/// eta arrow `(_1, _2)` meeting a named-binder callback `(acc, x)`. Requiring
/// names to agree would reject `foldLeft` outright.
#[test]
fn eta_arrow_still_satisfies_a_named_binder_callback() {
    let src = r#"
namespace test.wi782.eta
  import anthill.prelude.{Int64, List}
  operation shift(acc: Int64, x: Int64) -> Int64
    = acc * 10 + x
  operation drive() -> Int64
    = [1, 2, 3].foldLeft(0, shift)
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi782.eta.drive"), 123);
}

// ── tuple-typed parameters must keep working ───────────────────

/// A callback taking ONE tuple-typed parameter, driven to a value through the
/// arrow spelling. `get_a` reads `t.a`, so this also proves the tuple reaching
/// the callee is NAME-keyed.
#[test]
fn tuple_typed_parameter_still_applies_end_to_end() {
    let src = r#"
namespace test.wi782.tupleparam
  import anthill.prelude.{Int64}
  operation get_a(t: (a: Int64, b: Int64)) -> Int64
    = t.a
  operation take(f: (u: (a: Int64, b: Int64)) -> Int64) -> Int64
    = f((a: 7, b: 8))
  operation drive() -> Int64
    = take(get_a)
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi782.tupleparam.drive"), 7);
}

/// The same through `Function[A, B]`, whose `A` is ONE tuple-typed ARGUMENT
/// (WI-775) rather than a parameter list.
#[test]
fn function_spelling_of_a_tuple_argument_still_applies() {
    let src = r#"
namespace test.wi782.fnspelling
  import anthill.prelude.{Int64, Function}
  operation get_a(t: (a: Int64, b: Int64)) -> Int64
    = t.a
  operation take(f: Function[A = (a: Int64, b: Int64), B = Int64]) -> Int64
    = f((a: 7, b: 8))
  operation drive() -> Int64
    = take(get_a)
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi782.fnspelling.drive"), 7);
}

/// A generic callback whose parameter type is a TYPE PARAMETER instantiated at a
/// tuple, with the callback supplied as an eta op reference. The parameter slot
/// here becomes a tuple only through SUBSTITUTION, which is the case that
/// defeated the reverted WI-791 wrapper — pinned so a future attempt has to keep
/// it working.
#[test]
fn type_parameter_instantiated_at_a_tuple_still_applies() {
    let src = r#"
namespace test.wi782.typaram
  import anthill.prelude.{Int64}
  operation apply1[T](f: (x: T) -> Int64, v: T) -> Int64
    = f(v)
  operation get_a(t: (a: Int64, b: Int64)) -> Int64
    = t.a
  operation drive() -> Int64
    = apply1(get_a, (a: 7, b: 8))
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi782.typaram.drive"), 7);
}

/// An arity-1 NON-tuple parameter, the overwhelmingly common shape.
#[test]
fn arity_one_non_tuple_parameter_still_applies() {
    let src = r#"
namespace test.wi782.scalarparam
  import anthill.prelude.{Int64}
  operation inc(v: Int64) -> Int64
    = v + 1
  operation take(f: (w: Int64) -> Int64) -> Int64
    = f(41)
  operation drive() -> Int64
    = take(inc)
end
"#;
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi782.scalarparam.drive"), 42);
}

// ── the KNOWN GAP, pinned so it stays visible ──────────────────

/// WI-791 (WI-782 case 3): the param slot does not record parameter-list ARITY.
/// An arity-1 list collapses to its parameter's bare type, so a ONE-tuple-
/// parameter operation and a TWO-parameter one build the identical term and each
/// is accepted for the other — then traps at eval.
///
/// This test asserts the CURRENT, WRONG behavior on purpose, so the gap is
/// visible in the suite rather than merely written down. It is a LOUD trap, not
/// a silent wrong answer, which is why WI-782 shipped without it. When WI-791
/// lands, this test SHOULD fail — replace it with a load-rejection assertion.
#[test]
fn known_gap_tuple_typed_parameter_is_not_distinguished_from_a_two_parameter_list() {
    let src = r#"
namespace test.wi782.knowngap
  import anthill.prelude.{Int64}
  operation get_a(t: (a: Int64, b: Int64)) -> Int64
    = t.a
  operation drive() -> Int64
    = let f: (_1: Int64, _2: Int64) -> Int64 = get_a
      f((7, 8))
end
"#;
    assert!(
        try_load_kb_with(src).is_ok(),
        "WI-791 not yet fixed: this program is still expected to LOAD (wrongly)",
    );
    let mut interp = interp_for(src);
    let err = interp
        .call("test.wi782.knowngap.drive", &[])
        .expect_err("WI-791 not yet fixed: this program is still expected to TRAP at eval");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("tuple has no component 'a'"),
        "the known gap should still surface as the WI-791 component miss; got: {msg}",
    );
}
