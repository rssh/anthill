//! WI-792 — an ARGUMENT is checked against the PARAMETER SLOT it lands in, at
//! the two positions where nothing checked it.
//!
//! Both are the same defect wearing different clothes: a conformance check that
//! simply did not run. They are independent of each other, and each closes a
//! program that loaded clean and then either trapped or — the headline — returned
//! a value of the wrong type with no complaint at all.
//!
//!   * LOCUS 1, the APPLICATION site (calling a function VALUE). `check_apply_iter`
//!     Path 2 read only the arrow's `result` and `effects` children and DISCARDED
//!     `param`, so no positional argument was ever compared against a parameter.
//!     `f(true, 7)` against a declared `(x: Int64, y: Bool) -> Int64` loaded, and
//!     an operation declared `-> Int64` returned `Bool(true)`. No permutation, no
//!     subtyping, no conformance question — the call put each value in the wrong
//!     slot and nothing objected.
//!   * LOCUS 2, the ARGUMENT-PASSING site (handing a callback to a
//!     TYPE-PARAMETERIZED operation). `validate_arg_against_param` skips
//!     `types_compatible` entirely when either side is non-ground, and a declared
//!     `(x: T, y: T) -> Int64` is non-ground while `T` is free, so WI-791's arity
//!     equality was never reached. The non-ground fallback,
//!     `validate_arrow_param_result`, was arity-blind.
//!
//! WHY LOCUS 2 IS A FEW LINES: arity is THE ONE COMPONENT that check can always
//! decide. It is a ground `Const(Int)` sibling no matter how polymorphic the
//! param and result types are, so the groundness discipline that justifies
//! deferring everything else (WI-385/WI-469 — a genuinely polymorphic component
//! must not be rejected early) does not reach it.
//!
//! Every rejection below is paired with a neighbouring program that must still
//! load AND EVALUATE. A fix that merely rejected more would satisfy the
//! rejections alone, and two of the controls are the exact programs the two
//! design decisions below protect.

use crate::common::{interp_for, try_load_kb_with};

fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// Evaluate `op` in a FRESH interpreter, asserting the program loaded clean.
/// Fresh per case deliberately: after any trapped call, reusing one interpreter
/// makes every later call return a bogus `Internal("deliver: parent frame had no
/// awaiting state")`, which reads as a second independent bug.
fn eval_int(src: &str, op: &str) -> i64 {
    run_int(&mut interp_for(src), op)
}

/// Assert the program is refused at LOAD, and that some diagnostic reads
/// `expected {expected}, got {got}`. Pinning the pair matters: the whole defect
/// class here is a check that reported NOTHING, so an assertion that merely
/// counts errors would pass on a fix that rejected the program for an unrelated
/// reason.
fn assert_refused_naming(src: &str, expected: &str, got: &str) {
    let errs = match try_load_kb_with(src) {
        Ok(_) => panic!("must NOT load: expected `{expected}`, got `{got}`"),
        Err(errs) => errs,
    };
    let wanted = format!("expected {expected}, got {got}");
    assert!(
        errs.iter().any(|e| e.contains("type mismatch") && e.contains(&wanted)),
        "rejection must be a type mismatch reading `{wanted}`; got: {errs:?}",
    );
}

// ── LOCUS 1: the application site ──────────────────────────────

/// THE HEADLINE, and the one case in this file that was a SILENT WRONG ANSWER
/// rather than a deferred trap. Measured on the parent commit: this loaded clean
/// and `drive()` — declared `-> Int64` — evaluated to `Bool(true)`.
///
/// Both slots are named, so both mismatches are reported; asserting only one
/// would pass on a fix that checked just the first argument.
#[test]
fn positional_argument_types_are_checked_at_a_function_value_application() {
    let src = r#"
namespace test.wi792.headline
  import anthill.prelude.{Int64, Bool}
  operation impl(x: Int64, y: Bool) -> Int64
    = x
  operation take(f: (x: Int64, y: Bool) -> Int64) -> Int64
    = f(true, 7)
  operation drive() -> Int64
    = take(impl)
end
"#;
    assert_refused_naming(src, "Int64", "Bool");
    assert_refused_naming(src, "Bool", "Int64");
}

/// The control for the headline: the SAME program with the two arguments the
/// right way round still loads and still evaluates. Driven, not merely loaded —
/// the defect was invisible at load, so a load assertion proves nothing about it.
#[test]
fn a_conforming_function_value_application_still_evaluates() {
    let src = r#"
namespace test.wi792.ok
  import anthill.prelude.{Int64, Bool}
  operation impl(x: Int64, y: Bool) -> Int64
    = x
  operation take(f: (x: Int64, y: Bool) -> Int64) -> Int64
    = f(7, true)
  operation drive() -> Int64
    = take(impl)
end
"#;
    assert_eq!(eval_int(src, "test.wi792.ok.drive"), 7);
}

/// The NAMED channel of the same check. WI-783 taught this path to resolve a
/// label to its declared slot and reorder the call; it did not then check what
/// landed in the slot, which is the same silence in the other channel. Here the
/// labels are correct and exhaustive — only the TYPES are swapped — so nothing
/// but a per-argument type check can refuse it.
#[test]
fn named_argument_types_are_checked_at_a_function_value_application() {
    let src = r#"
namespace test.wi792.named
  import anthill.prelude.{Int64, Bool}
  operation impl(x: Int64, y: Bool) -> Int64
    = x
  operation take(f: (x: Int64, y: Bool) -> Int64) -> Int64
    = f(y: 7, x: true)
  operation drive() -> Int64
    = take(impl)
end
"#;
    assert_refused_naming(src, "Int64", "Bool");
    assert_refused_naming(src, "Bool", "Int64");
}

/// ARITY at the application site, in both directions. The type loop alone cannot
/// own this: a truncated call whose prefix happens to conform would slip through
/// it, and eval refuses any count but an exact one (`spread_eta_args`), so a
/// load-clean verdict would just defer the same rejection.
///
/// One arity error, not a cascade of mis-aligned slot mismatches — a call whose
/// count is wrong has no slot correspondence to report against.
#[test]
fn argument_count_is_checked_against_the_parameter_list() {
    let program = |call: &str| {
        format!(
            r#"
namespace test.wi792.arity
  import anthill.prelude.{{Int64}}
  operation sub2(a: Int64, b: Int64) -> Int64
    = a - b
  operation take(f: (x: Int64, y: Int64) -> Int64) -> Int64
    = {call}
  operation drive() -> Int64
    = take(sub2)
end
"#
        )
    };
    for (call, got) in [("f(1, 2, 3)", "3 arguments"), ("f(1)", "1 argument")] {
        assert_refused_naming(
            &program(call),
            "2 arguments — the parameter list this function value declares",
            got,
        );
    }
    // The control on the same shape: the exact count loads and evaluates.
    assert_eq!(eval_int(&program("f(10, 3)"), "test.wi792.arity.drive"), 7);
}

/// DECISION 2, and the reason locus 1 cannot simply read `arrow_parts`. A
/// `Function[A, B, E]` STATES NO ARITY and cannot — WI-775 settled that its `A`
/// is the ONE argument `apply(f, x: A)` passes — so a two-tuple `A` denotes both
/// "one tuple argument" and "the eta arrow of a 2-parameter operation", and BOTH
/// application forms are legal at that slot.
///
/// `arrow_parts` decomposes a `Function` too, so a naive "argument i against
/// parameter slot i" would read that `A` as ONE parameter and refuse `f(3, 10)`
/// as 2-against-1. The skip is deliberate, not inherited: locus 2 gets it free
/// (`arrow_arity` returns `None` for a `Function`), locus 1 does it on purpose by
/// gating on `TypeExtractor::Arrow`.
///
/// The 2x2 matrix is already pinned by
/// `operations_and_lambdas_are_interchangeable_in_both_application_forms`
/// (wi784) and `function_spelling_states_no_arity_and_still_bridges` (wi791);
/// this drives the one cell locus 1 could have broken, so the file that
/// introduced the hazard also states it.
#[test]
fn a_function_spelling_states_no_arity_so_neither_form_is_refused() {
    let src = r#"
namespace test.wi792.fnspell
  import anthill.prelude.{Int64, Function}
  operation sub2(a: Int64, b: Int64) -> Int64
    = a - b
  operation spread(f: Function[A = (Int64, Int64), B = Int64]) -> Int64
    = f(3, 10)
  operation gathered(f: Function[A = (Int64, Int64), B = Int64]) -> Int64
    = f((3, 10))
  operation drive_spread() -> Int64
    = spread(sub2)
  operation drive_gathered() -> Int64
    = gathered(sub2)
end
"#;
    for op in ["drive_spread", "drive_gathered"] {
        assert_eq!(
            eval_int(src, &format!("test.wi792.fnspell.{op}")),
            -7,
            "{op}: a `Function` slot states no arity, so both application forms stay legal",
        );
    }
}

/// DECISION 3. A function-value application is the THIRD argument position, so
/// it must ACT on the WI-408 some-coercion, not merely tolerate it: `f(7, 3)`
/// against a declared `(o: Option[T = Int64], d: Int64) -> Int64` has to REWRITE
/// the argument to `some(7)`.
///
/// This is driven rather than load-asserted because that is the only way to tell
/// the fix from the known-bad shortcut. Accepting the argument WITHOUT wrapping —
/// the WI-385 lenient-accept interim WI-408 replaced — ALSO loads clean, so a
/// load assertion cannot separate them: it leaves the value bare in memory while
/// its type says `Option[T]`, and `orElse` then matches neither `some` nor
/// `none`. Measured on the parent commit, that is exactly what happened — the
/// program loaded and `drive()` RAISED on the failed match. Only a real wrap
/// returns 7.
#[test]
fn some_coercion_is_applied_at_a_function_value_application() {
    let src = r#"
namespace test.wi792.opt
  import anthill.prelude.{Int64, Option, some, none}
  operation orElse(o: Option[T = Int64], d: Int64) -> Int64 =
    match o
      case none() -> d
      case some(v) -> v
  operation take(f: (o: Option[T = Int64], d: Int64) -> Int64) -> Int64
    = f(7, 3)
  operation drive() -> Int64
    = take(orElse)
end
"#;
    assert_eq!(eval_int(src, "test.wi792.opt.drive"), 7);
}

// ── LOCUS 2: the argument-passing site ─────────────────────────

/// THE GENERIC-CALLBACK GAP, pinned in WI-791 as
/// `known_gap_generic_callback_arrow_is_not_conformance_checked` and inverted
/// there now that it is closed. Measured identical on WI-791's commit AND on its
/// parent: it LOADED and trapped `ArityMismatch { expected: 1, got: 2 }` at eval.
///
/// `get_a` takes ONE tuple-typed parameter; the slot declares TWO. The SAME
/// program written non-generically is refused by WI-791
/// (`positionally_spelled_two_parameter_callback_is_refused`) — genericity was
/// the whole difference, which is what made this a gap rather than a policy.
#[test]
fn a_generic_callback_slot_checks_arity() {
    assert_refused_naming(
        r#"
namespace test.wi792.gena
  import anthill.prelude.{Int64}
  operation apply2[T](f: (x: T, y: T) -> Int64, v: T, w: T) -> Int64
    = f(v, w)
  operation get_a(t: (a: Int64, b: Int64)) -> Int64
    = t.a
  operation drive() -> Int64
    = apply2(get_a, 7, 8)
end
"#,
        "(x: ?T, y: ?T) -> Int64",
        "((a: Int64, b: Int64)) -> Int64",
    );
}

/// DECISION 1 (user, WI-792): the DUAL is refused too, and this one WORKED
/// BEFORE — it loaded and evaluated to -1. Recorded as a decision because it is a
/// deliberate loss, not a side effect.
///
/// It worked only because eval's `spread_eta_args` spreads a single POSITIONAL
/// tuple argument across a multi-parameter operation; the name-keyed spelling of
/// the identical program already trapped. WI-791 took exactly this trade one rung
/// over (`two_parameter_operation_is_refused_for_a_tuple_argument_arrow`), on the
/// grounds that letting a type relation depend on how a caller happens to build
/// its tuple is incoherent — so taking it here is consistency, and taking the
/// other side would not have been.
///
/// Nothing is lost: since WI-784 the spread convention is reachable through
/// `Function[A, B]` for operations AND lambdas in both application forms
/// (`a_function_spelling_states_no_arity_so_neither_form_is_refused` above).
#[test]
fn a_generic_callback_slot_checks_arity_in_the_spread_direction_too() {
    assert_refused_naming(
        r#"
namespace test.wi792.genb
  import anthill.prelude.{Int64}
  operation apply1[T](f: (x: T) -> Int64, v: T) -> Int64
    = f(v)
  operation two(a: Int64, b: Int64) -> Int64
    = a - b
  operation drive() -> Int64
    = apply1(two, (7, 8))
end
"#,
        "?T -> Int64",
        "(_1: Int64, _2: Int64) -> Int64",
    );
}

/// The control that keeps locus 2 from being "refuse every generic callback":
/// a matching generic callback still loads and EVALUATES, in both arities.
///
/// `apply1` here is the program the reverted WI-782 in-slot encoding broke and
/// that WI-791's sibling `arity` child exists to keep working — its slot is
/// written `(x: T) -> Int64`, so its arity is 1 at the mint and stays 1 after
/// `T := (a: Int64, b: Int64)`. The arity equality added by this ticket compares
/// counts that substitution cannot touch, so it leaves that program alone.
#[test]
fn matching_generic_callbacks_still_apply() {
    let two_param = r#"
namespace test.wi792.gen2
  import anthill.prelude.{Int64}
  operation apply2[T](f: (x: T, y: T) -> Int64, v: T, w: T) -> Int64
    = f(v, w)
  operation minus(a: Int64, b: Int64) -> Int64
    = a - b
  operation drive() -> Int64
    = apply2(minus, 10, 3)
end
"#;
    assert_eq!(eval_int(two_param, "test.wi792.gen2.drive"), 7);

    let one_tuple_param = r#"
namespace test.wi792.typaram
  import anthill.prelude.{Int64}
  operation apply1[T](f: (x: T) -> Int64, v: T) -> Int64
    = f(v)
  operation get_a(t: (a: Int64, b: Int64)) -> Int64
    = t.a
  operation drive() -> Int64
    = apply1(get_a, (a: 7, b: 8))
end
"#;
    assert_eq!(eval_int(one_tuple_param, "test.wi792.typaram.drive"), 7);
}
