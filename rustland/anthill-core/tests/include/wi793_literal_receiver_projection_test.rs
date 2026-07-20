//! WI-793: a path-dependent callback parameter (`f: (acc: Acc, x: xs.T) -> Acc`)
//! resolves its element type from a receiver argument the typer has to SYNTHESIZE —
//! a list literal, a `cons` spine, a call — not only from one whose type is already
//! lying around.
//!
//! THE DEFECT: `List.foldLeft([1, 2, 3], 0, lambda (acc, x) -> acc * 10 + x)` did not
//! LOAD. `xs.T` never resolved for the LAMBDA binder, so a correct program was rejected
//! with `type mismatch in add.b (op-arg): expected Int64, got xs.T`.
//!
//! THE BOUNDARY IS NARROW AND BOTH OBVIOUS READINGS ARE WRONG. Not "lambdas break
//! `List.foldLeft`" — the same lambda against a declared `List[T = Int64]` parameter
//! loaded. Not "list literals break `List.foldLeft`" — the same literal with a named
//! operation callback loaded. It took the LITERAL receiver and the LAMBDA together: a
//! named operation carries its own declared param types and never needs `xs.T` resolved,
//! and a declared parameter pins the element type before the call.
//!
//! ROOT CAUSE, and why the fix is a fourth rung rather than a new mechanism: the hint
//! path read a receiver argument's type through three no-synthesis readers — an env
//! binding, a rule's schema, a stamp from an earlier frame. An ordinary EXPRESSION
//! argument has none at hint time. A lambda's body is checked at synthesis against the
//! pushed hint, so the binder bound the raw rigid neutral and the body failed.
//!
//! THE TELL that this was a missing peer: the DOT-CALL spelling
//! `[1, 2, 3].foldLeft(0, λ)` already worked, because the `DotApply` frame pre-types its
//! receiver (WI-443) and stamps it (WI-732) — rung 3. Same call, same types, different
//! spelling. `qualified_and_dot_call_spellings_agree` pins the two together so they
//! cannot drift apart again.
//!
//! Every test DRIVES the program end-to-end and compares against the NAMED-OPERATION
//! spelling of the same fold. A load assertion alone would be satisfied by any binder
//! type permissive enough to stop complaining; agreement with the control is what
//! actually says the element type arrived.

use crate::common::{interp_for, try_load_kb_with};

/// Evaluate `op` in a FRESH interpreter, asserting the program loaded clean. Fresh per
/// case on purpose: after any trapped call a reused `Interpreter` returns a bogus
/// `Internal` for every later call, which reads as a second independent bug.
fn eval_int(src: &str, op: &str) -> i64 {
    if let Err(errs) = try_load_kb_with(src) {
        panic!("expected a clean load; got: {errs:?}");
    }
    match interp_for(src).call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// THE HEADLINE. `foldLeft` over a literal, lambda vs named operation, driven.
#[test]
fn foldleft_over_a_literal_agrees_for_lambda_and_operation() {
    let src = r#"
namespace test.wi793.foldleft
  import anthill.prelude.{Int64, List, nil, cons}

  operation shift(acc: Int64, x: Int64) -> Int64 = acc * 10 + x

  operation drive_op() -> Int64 = List.foldLeft([1, 2, 3], 0, shift)
  operation drive_lambda() -> Int64 =
    List.foldLeft([1, 2, 3], 0, lambda (acc, x) -> acc * 10 + x)
end
"#;
    let via_op = eval_int(src, "test.wi793.foldleft.drive_op");
    let via_lambda = eval_int(src, "test.wi793.foldleft.drive_lambda");
    assert_eq!(via_op, 123, "the operation spelling is the control and already worked");
    assert_eq!(via_lambda, via_op, "the lambda spelling must reach the same answer");
}

/// `foldRight` was affected identically and is fixed identically. Its callback takes the
/// element FIRST (`(x: xs.T, acc: Acc)`), so it also checks that the resolved element
/// lands in the right SLOT rather than merely somewhere in the parameter list — a fix
/// that pinned the wrong slot would still load and would return a different number.
#[test]
fn foldright_over_a_literal_agrees_for_lambda_and_operation() {
    let src = r#"
namespace test.wi793.foldright
  import anthill.prelude.{Int64, List, nil, cons}

  operation shift(x: Int64, acc: Int64) -> Int64 = acc * 10 + x

  operation drive_op() -> Int64 = List.foldRight([1, 2, 3], 0, shift)
  operation drive_lambda() -> Int64 =
    List.foldRight([1, 2, 3], 0, lambda (x, acc) -> acc * 10 + x)
end
"#;
    let via_op = eval_int(src, "test.wi793.foldright.drive_op");
    let via_lambda = eval_int(src, "test.wi793.foldright.drive_lambda");
    assert_eq!(via_op, 321, "foldRight folds from the right, so the digits reverse");
    assert_eq!(via_lambda, via_op, "the lambda spelling must reach the same answer");
}

/// IT IS NOT ABOUT LITERALS. The literal is just the most reachable receiver whose type
/// nothing had computed yet; a `cons` spine and a CALL are in exactly the same position
/// and were broken in exactly the same way. Pinned because a fix aimed at the literal
/// SYNTAX (reading element types off a collection node) would pass the headline test and
/// fail both of these — the fix has to be about synthesizing the receiver's TYPE.
#[test]
fn a_cons_spine_and_a_call_receiver_resolve_too() {
    let src = r#"
namespace test.wi793.otherreceivers
  import anthill.prelude.{Int64, List, nil, cons}

  operation mk() -> List[T = Int64] = [1, 2, 3]

  operation drive_call() -> Int64 =
    List.foldLeft(mk(), 0, lambda (acc, x) -> acc * 10 + x)
  operation drive_cons() -> Int64 =
    List.foldLeft(cons(head: 1, tail: cons(head: 2, tail: cons(head: 3, tail: nil))),
                  0, lambda (acc, x) -> acc * 10 + x)
end
"#;
    assert_eq!(eval_int(src, "test.wi793.otherreceivers.drive_call"), 123);
    assert_eq!(eval_int(src, "test.wi793.otherreceivers.drive_cons"), 123);
}

/// The two SPELLINGS of one call must agree. The dot form worked throughout (its
/// receiver is pre-typed and stamped by the `DotApply` frame) and the qualified form did
/// not — that asymmetry IS the defect, so pin both in one test: a regression that takes
/// the qualified form away again cannot hide behind the dot form still passing.
#[test]
fn qualified_and_dot_call_spellings_agree() {
    let src = r#"
namespace test.wi793.spellings
  import anthill.prelude.{Int64, List, nil, cons}

  operation drive_qualified() -> Int64 =
    List.foldLeft([1, 2, 3], 0, lambda (acc, x) -> acc * 10 + x)
  operation drive_dot() -> Int64 =
    [1, 2, 3].foldLeft(0, lambda (acc, x) -> acc * 10 + x)
end
"#;
    let qualified = eval_int(src, "test.wi793.spellings.drive_qualified");
    let dot = eval_int(src, "test.wi793.spellings.drive_dot");
    assert_eq!(dot, 123, "the dot spelling was never broken — it is the control");
    assert_eq!(qualified, dot, "the qualified spelling must reach the same answer");
}

/// NESTED: the receiver argument is itself a projecting higher-order call, so resolving
/// the outer fold's element type requires resolving the inner map's first. Drives the
/// re-entrant path — `mapElems` doubles each element, then the fold reads `[2, 4, 6]`.
#[test]
fn a_projecting_call_as_the_receiver_resolves() {
    let src = r#"
namespace test.wi793.nested
  import anthill.prelude.{Int64, List, nil, cons}

  operation drive() -> Int64 =
    List.foldLeft(List.mapElems([1, 2, 3], lambda (x) -> x * 2),
                  0, lambda (acc, x) -> acc * 10 + x)
end
"#;
    assert_eq!(eval_int(src, "test.wi793.nested.drive"), 246);
}

/// SOUNDNESS. Resolving the element type must REJECT the programs it now has the
/// information to reject — otherwise "it loads" would be indistinguishable from having
/// widened the binder to something permissive. Using an `Int64` element as a `String`
/// is refused, and the diagnostic names the real mismatch rather than the projection.
#[test]
fn a_wrong_element_use_is_rejected() {
    let src = r#"
namespace test.wi793.wronguse
  import anthill.prelude.{Int64, String, List, nil, cons}

  operation len(s: String) -> Int64 = 1

  operation drive() -> Int64 =
    List.foldLeft([1, 2, 3], 0, lambda (acc, x) -> acc + len(x))
end
"#;
    let errs = try_load_kb_with(src).err().expect("using an Int64 element as a String must fail");
    assert!(
        errs.iter().any(|e| e.contains("expected String, got Int64")),
        "the diagnostic must name the element mismatch, not the projection; got: {errs:?}",
    );
}

/// A binder ANNOTATION that CONTRADICTS the resolved element type is rejected. Before
/// WI-793 this program could not be judged at all — the slot's type was an unresolved
/// projection, so there was nothing for `String` to contradict.
///
/// SCOPE, measured rather than assumed: this holds at a ONE-binder callback. The
/// MULTI-binder twin (`lambda (acc: Int64, x: String)`) still loads clean, and that is a
/// SEPARATE defect in the arrow-arity channel, not this one — it reproduces with no
/// projection and no literal anywhere (`operation apply2(f: (a: Int64, b: Int64) -> …)`
/// applied to `lambda (a: Int64, b: String) -> a`), so no element-type resolution could
/// have fixed it. Tracked as WI-794; `known_gap_multi_binder_annotation_is_unchecked`
/// there pins it.
#[test]
fn a_contradicting_binder_annotation_is_rejected() {
    let src = r#"
namespace test.wi793.contra
  import anthill.prelude.{Int64, String, List, nil, cons}

  operation drive() -> List[T = Int64] =
    List.mapElems([1, 2, 3], lambda (x: String) -> 5)
end
"#;
    let errs = try_load_kb_with(src)
        .err()
        .expect("a String binder over an Int64 element must be refused");
    assert!(
        errs.iter().any(|e| e.contains("String")),
        "the diagnostic must name the contradicting annotation; got: {errs:?}",
    );
}

/// THE STAGED ARGUMENT IS NOT ALWAYS ARGUMENT ZERO. Staging types the projection
/// receiver ahead of its siblings, so its result reaches the results stack BEFORE theirs
/// whatever its position in the call — and the `Apply` frame has to splice it back into
/// the right slot. Every other test here puts the receiver at positional 0, where that
/// permutation is the identity and a wrong one would still pass.
///
/// Here the projected receiver is the SECOND parameter, so the splice is exercised for
/// real: get it wrong and `init` and `xs` swap, which is a type error rather than a
/// silently different answer.
#[test]
fn a_staged_receiver_in_a_later_position_is_spliced_back_correctly() {
    let src = r#"
namespace test.wi793.later
  import anthill.prelude.{Int64, List, nil, cons}

  operation myFold[Acc, EffP](init: Acc, xs: List, f: (acc: Acc, x: xs.T) -> Acc @ {EffP})
      -> Acc effects EffP =
    List.foldLeft(xs, init, f)

  operation drive() -> Int64 =
    myFold(0, [1, 2, 3], lambda (acc, x) -> acc * 10 + x)
end
"#;
    assert_eq!(eval_int(src, "test.wi793.later.drive"), 123);
}

/// The NAMED channel. A named argument's position in the call need not follow the
/// parameter's declared position, so the unified index staging keys on has to survive a
/// caller reordering the labels. Written with the receiver label LAST — the reverse of
/// its declared slot — so a splice that assumed declaration order would misplace it.
#[test]
fn a_staged_receiver_passed_by_label_out_of_order_resolves() {
    let src = r#"
namespace test.wi793.named
  import anthill.prelude.{Int64, List, nil, cons}

  operation myFold[Acc, EffP](xs: List, init: Acc, f: (acc: Acc, x: xs.T) -> Acc @ {EffP})
      -> Acc effects EffP =
    List.foldLeft(xs, init, f)

  operation drive() -> Int64 =
    myFold(init: 0, f: lambda (acc, x) -> acc * 10 + x, xs: [1, 2, 3])
end
"#;
    assert_eq!(eval_int(src, "test.wi793.named.drive"), 123);
}

/// A staged argument that FAILS to type must report ITS OWN error, not be swallowed and
/// not be replaced by a downstream complaint about the projection it left unresolved.
/// This is the case that distinguishes staging from typing the receiver out of band: the
/// staged result rides into the `Apply` frame, so `collect_arg_errors` reports it.
#[test]
fn a_staged_receiver_that_fails_to_type_reports_its_own_error() {
    let src = r#"
namespace test.wi793.badrecv
  import anthill.prelude.{Int64, List, nil, cons}

  operation drive() -> Int64 =
    List.foldLeft(nosuchthing(), 0, lambda (acc, x) -> acc * 10 + x)
end
"#;
    let errs = try_load_kb_with(src).err().expect("an unresolvable receiver must fail to load");
    assert!(
        errs.iter().any(|e| e.contains("nosuchthing")),
        "the staged argument's OWN error must surface, not a downstream `xs.T` complaint; \
         got: {errs:?}",
    );
}

/// The ORDINARY call is untouched. The staging that types a receiver first is gated
/// on a parameter some sibling actually PROJECTS, so a higher-order call with no
/// projection in its signature never pays for it and never changes behaviour. Asserted
/// as a live program rather than as a claim about the gate.
#[test]
fn a_higher_order_call_without_a_projection_is_unaffected() {
    let src = r#"
namespace test.wi793.noproj
  import anthill.prelude.{Int64}

  operation apply2(f: (a: Int64, b: Int64) -> Int64) -> Int64 = f(3, 10)

  operation drive() -> Int64 = apply2(lambda (a, b) -> a - b)
end
"#;
    assert_eq!(eval_int(src, "test.wi793.noproj.drive"), -7);
}
