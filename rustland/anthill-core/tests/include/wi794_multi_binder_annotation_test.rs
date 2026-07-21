//! WI-794: a MULTI-BINDER lambda's parameter annotations were never checked against the
//! callback parameter slot, so a contradicting annotation loaded clean.
//!
//! The discriminator was BINDER COUNT and nothing else — bisected, not assumed. It was
//! NOT about path-dependent types (these programs have none), not about a decoupled
//! effect row (the one-binder contradiction is rejected with `@ {EffP}` and with a closed
//! `@ {}` alike), and not about an unbound accumulator type param. Adding a second binder
//! to any refused shape made it load clean.
//!
//! ROOT CAUSE: `extend_env_from_pattern`'s `Pattern::Var` arm read
//! `scrutinee_type.or_else(annotation)` — when BOTH were present the annotation was
//! DROPPED with nothing comparing the two. WI-517 chose that priority deliberately (the
//! context type is what the value IS, so it must win for the BINDING) and reasoned a
//! contradiction would "surface loudly through the body's own use of the binder". That
//! holds only when the body actually uses that binder at a type-constraining position:
//! in `lambda (a: Int64, b: String) -> a` nothing ever reads `b`. Arity 1 escaped because
//! its annotation wins the priority ladder one altitude up, at the lambda itself, so the
//! arrow carries it and the argument-position subsumption check catches the mismatch.
//!
//! THE FIX keeps the context winning — the binding, the arrow and every runtime value are
//! untouched — and reports the losing annotation instead of discarding it. So this closes
//! a missing DIAGNOSTIC, which is exactly why it stayed invisible: no program computed a
//! wrong answer, the user's explicit statement of intent was just inert.
//!
//! The check is at the DROP SITE rather than at the argument position, which means it
//! needs no alignment logic of its own: `Pattern::Tuple` has already split the context
//! type into components and handed each binder its own, so the comparison is per-binder
//! and cannot drift from the binding it validates. It covers every pattern position that
//! admits a `typed_binder` — the `let` and `match` cases below are the same code path.

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

/// Load `src`, expecting rejection, and return the diagnostics.
fn reject(src: &str, why: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_else(|| panic!("{why}"))
}

/// Reject, AND pin that it was THIS check that rejected — the `binder-annotation` kind
/// tag no other diagnostic carries. Without this the tests here would be blind: every
/// contradicting program below is wrong in more than one way once the annotation is
/// believed, so a rejection alone proves nothing about which mechanism fired, and the
/// suite would stay green if the per-binder check were deleted.
fn reject_as_binder_annotation(src: &str, why: &str) -> String {
    let msg = reject(src, why).join("\n");
    assert!(
        msg.contains("binder-annotation"),
        "{why}: expected the per-binder check to fire; got: {msg}",
    );
    msg
}

/// THE CONTROL, and it was already positive: at ONE binder the contradiction IS caught.
/// It is caught by a DIFFERENT mechanism than the multi-binder case below (the arrow
/// subsumption at the argument position, not the per-binder check), so it stays here to
/// pin that the fix did not disturb it — the diagnostic still names both arrow types.
#[test]
fn one_binder_contradicting_annotation_is_rejected() {
    let src = r#"
namespace test.wi794.one
  import anthill.prelude.{Int64, String}

  operation apply1(f: (a: Int64) -> Int64) -> Int64 = f(1)

  operation drive() -> Int64 = apply1(lambda (a: String) -> 1)
end
"#;
    let errs = reject(src, "a String binder in an Int64 slot must be refused at arity 1");
    let msg = errs.join("\n");
    assert!(
        msg.contains("String"),
        "the diagnostic must name the contradicting annotation; got: {msg}",
    );
    // AND it must still be rejected by the OLD mechanism. At arity 1 the annotation wins
    // the priority ladder at the lambda, so `param_type` IS the annotation and the
    // per-binder comparison sees two identical types and stands down — the arrow
    // subsumption at the argument position is what refuses it. Pinning the ABSENCE of
    // the tag keeps that split honest: reroute arity 1 through the new check and this
    // fails, which is the point (the two arities are caught by different machinery, and
    // WI-794's bisection depended on exactly that).
    assert!(
        !msg.contains("binder-annotation"),
        "arity 1 must keep its arrow-subsumption diagnostic, not the per-binder one; got: {msg}",
    );
    assert!(
        msg.contains("op-arg"),
        "arity 1's diagnostic is the argument-position one; got: {msg}",
    );
}

/// THE HEADLINE — the gap WI-794 closed. A contradicting annotation at TWO binders is
/// rejected, in the SECOND slot (the ticket's repro), in the FIRST, and in BOTH. All
/// three are asserted because each rules out a different half-fix: checking only slot 0,
/// checking only the last slot, or bailing as soon as one slot disagrees.
#[test]
fn multi_binder_contradicting_annotation_is_rejected() {
    let cases: [(&str, &str); 3] = [
        ("second", "lambda (a: Int64, b: String) -> a"),
        ("first", "lambda (a: String, b: Int64) -> b"),
        ("both", "lambda (a: String, b: String) -> 1"),
    ];
    for (which, lambda) in cases {
        let src = format!(
            r#"
namespace test.wi794.two{which}
  import anthill.prelude.{{Int64, String}}

  operation apply2(f: (a: Int64, b: Int64) -> Int64) -> Int64 = f(1, 2)

  operation drive() -> Int64 = apply2({lambda})
end
"#
        );
        let msg = reject_as_binder_annotation(
            &src,
            &format!("the {which} binder's contradiction must be refused"),
        );
        assert!(
            msg.contains("String"),
            "the {which} case must name the written annotation; got: {msg}",
        );
    }
}

/// The diagnostic NAMES THE BINDER and BOTH TYPES, and is LOCATED. Without the binder
/// name a multi-parameter callback leaves the reader hunting which annotation is wrong —
/// the whole point of checking per-binder rather than per-arrow.
#[test]
fn the_diagnostic_names_the_binder_and_both_types() {
    let src = r#"
namespace test.wi794.msg
  import anthill.prelude.{Int64, String}

  operation apply3(f: (a: Int64, b: Int64, c: Int64) -> Int64) -> Int64 = f(1, 2, 3)

  operation drive() -> Int64 = apply3(lambda (a: Int64, b: String, c: Int64) -> a)
end
"#;
    let msg = reject_as_binder_annotation(src, "a contradicting middle binder must be refused");
    // The binder that is actually wrong, and ONLY that one — `a` and `c` agree with
    // their slots and naming them would send the reader to the wrong annotation.
    assert!(msg.contains(".b "), "must name the offending binder `b`; got: {msg}");
    assert!(
        !msg.contains(".a ") && !msg.contains(".c "),
        "must not implicate the agreeing binders; got: {msg}",
    );
    // Both types: what the slot is, and what was written.
    assert!(msg.contains("Int64"), "must name the slot type Int64; got: {msg}");
    assert!(msg.contains("String"), "must name the written type String; got: {msg}");
    // Located. Line 7 is the lambda. The span is the LAMBDA's, not the written type's —
    // the loader lowers a binder annotation through hash-consed KB terms, which own no
    // span, so the annotation occurrence inherits its parent pattern's. That is exactly
    // why the binder NAME above is load-bearing: without it a wrong annotation in a
    // multi-parameter callback would be located only to the lambda as a whole.
    assert!(
        msg.starts_with("7:"),
        "the diagnostic must be located at the lambda's line; got: {msg}",
    );
}

/// An AGREEING multi-binder annotation still loads AND STILL COMPUTES. Load-clean alone
/// would be satisfied by a check that silently stopped typing the lambda, so the value is
/// what actually says the binders still bind: `3 - 10 = -7`.
#[test]
fn multi_binder_annotation_that_agrees_still_loads_and_evaluates() {
    let src = r#"
namespace test.wi794.agree
  import anthill.prelude.{Int64}

  operation apply2(f: (a: Int64, b: Int64) -> Int64) -> Int64 = f(3, 10)

  operation drive() -> Int64 = apply2(lambda (a: Int64, b: Int64) -> a - b)
end
"#;
    assert_eq!(eval_int(src, "test.wi794.agree.drive"), -7);
}

/// An UNANNOTATED multi-binder lambda is untouched — its binders type from the slot,
/// which is the normal path and the one every stdlib fold takes. This is the test that
/// would fail if the check fired on an ABSENT annotation instead of a contradicting one.
#[test]
fn unannotated_multi_binder_lambda_is_unaffected() {
    let src = r#"
namespace test.wi794.bare
  import anthill.prelude.{Int64}

  operation apply2(f: (a: Int64, b: Int64) -> Int64) -> Int64 = f(3, 10)

  operation drive() -> Int64 = apply2(lambda (a, b) -> a - b)
end
"#;
    assert_eq!(eval_int(src, "test.wi794.bare.drive"), -7);
}

/// A PARTIALLY annotated lambda: one binder written, one left to the slot. The written
/// one is still checked and the bare one still types from context — mixing the two must
/// not disable either.
#[test]
fn a_partially_annotated_lambda_checks_only_the_written_binder() {
    let ok = r#"
namespace test.wi794.partok
  import anthill.prelude.{Int64}

  operation apply2(f: (a: Int64, b: Int64) -> Int64) -> Int64 = f(3, 10)

  operation drive() -> Int64 = apply2(lambda (a, b: Int64) -> a - b)
end
"#;
    assert_eq!(eval_int(ok, "test.wi794.partok.drive"), -7);

    let bad = r#"
namespace test.wi794.partbad
  import anthill.prelude.{Int64, String}

  operation apply2(f: (a: Int64, b: Int64) -> Int64) -> Int64 = f(3, 10)

  operation drive() -> Int64 = apply2(lambda (a, b: String) -> 1)
end
"#;
    reject_as_binder_annotation(
        bad, "a written contradiction beside a bare binder must still be refused",
    );
}

/// THE DIRECTION OF THE CHECK, which nothing else here pins. Every other fixture pairs
/// DISJOINT types (`String` at an `Int64` slot), and those fail conformance BOTH ways —
/// so the whole suite would stay green if the comparison were reversed, or replaced with
/// plain equality. Only an asymmetric pair distinguishes them.
///
/// The rule: the binder really holds a `context_ty` value (the context wins — WI-517's
/// soundness decision), so the annotation is a CLAIM about that value, true exactly when
/// `context_ty` conforms to it. A WIDER annotation is imprecise but TRUE and is accepted;
/// a NARROWER one is FALSE and is refused. `Square` provides `Shape`, which is the
/// `sort_provides_admissibly` widening `types_compatible` implements.
///
/// This matters because the call reads `types_compatible(kb, subst, context_ty,
/// annotation)` — parameters `(actual, expected)` — while the error it builds names the
/// sides the other way round (`expected` = the slot, `actual` = what the user wrote), on
/// purpose, so the message reads in the user's direction. Anyone "tidying" that apparent
/// inconsistency by swapping the arguments flips the rule, and these two cases are what
/// catch it.
#[test]
fn a_wider_annotation_is_accepted_and_a_narrower_one_is_refused() {
    // Slot `Square`, annotation `Shape` — imprecise but true.
    let wider = r#"
namespace test.wi794.wider
  import anthill.prelude.{Int64}

  sort Shape
  end

  sort Square
    fact Shape
    entity mk(n: Int64)
  end

  operation apply2(f: (a: Square, b: Int64) -> Int64) -> Int64 = f(mk(n: 1), 2)

  operation drive() -> Int64 = apply2(lambda (a: Shape, b: Int64) -> b)
end
"#;
    assert_eq!(eval_int(wider, "test.wi794.wider.drive"), 2);

    // Slot `Shape`, annotation `Square` — the binder may hold any `Shape`, so the
    // narrower claim is false.
    let narrower = r#"
namespace test.wi794.narrower
  import anthill.prelude.{Int64}

  sort Shape
  end

  sort Square
    fact Shape
    entity mk(n: Int64)
  end

  operation apply2(f: (a: Shape, b: Int64) -> Int64) -> Int64 = f(mk(n: 1), 2)

  operation drive() -> Int64 = apply2(lambda (a: Square, b: Int64) -> b)
end
"#;
    let msg = reject_as_binder_annotation(
        narrower, "a narrower binder annotation is a false claim and must be refused",
    );
    // Order matters here and is the point: the SLOT is `expected`, the WRITTEN type is
    // `actual`. Asserting both names would pass under a swap; asserting their order does
    // not.
    assert!(
        msg.contains("expected Shape, got Square"),
        "the diagnostic must read slot-then-annotation; got: {msg}",
    );
}

/// THE OVER-REJECTION GUARD, and the reason the check is gated on GROUNDNESS. A generic
/// callback slot threads a type VARIABLE (`Acc`) and an unresolved PROJECTION (`xs.T`)
/// into the binders; annotating them is a legitimate way to pin them, and the annotation
/// is not a contradiction of anything the typer has yet decided. Reject here and every
/// annotated fold in the language breaks — so the check stands down and leaves the slot
/// to unification. DRIVEN, because a load assertion would also pass if the annotations
/// had quietly stopped pinning anything.
#[test]
fn an_annotated_binder_at_a_generic_slot_is_not_false_rejected() {
    let src = r#"
namespace test.wi794.generic
  import anthill.prelude.{Int64, List, nil, cons}

  operation drive() -> Int64 =
    List.foldLeft([1, 2, 3], 0, lambda (acc: Int64, x: Int64) -> acc * 10 + x)
end
"#;
    assert_eq!(eval_int(src, "test.wi794.generic.drive"), 123);
}

/// The same slot through the OTHER callable spelling. `Function[(Int64, Int64), Int64]`
/// reaches the binders as a tuple-typed parameter rather than a parameter list, so it
/// exercises a different reader on the way to the same per-binder comparison.
#[test]
fn a_function_typed_callback_slot_is_checked_too() {
    let src = r#"
namespace test.wi794.fnslot
  import anthill.prelude.{Int64, String, Function}

  operation apply_pair(f: Function[(Int64, Int64), Int64], p: (Int64, Int64)) -> Int64 = f(p)

  operation drive() -> Int64 = apply_pair(lambda (a: Int64, b: String) -> a, (1, 2))
end
"#;
    reject_as_binder_annotation(
        src, "a contradicting binder under a Function[...] slot must be refused",
    );
}

/// The check lives where the annotation was being dropped, so it covers every pattern
/// position that admits a `typed_binder` — not just callback arguments. A `let`
/// destructure of a known tuple is one such position.
#[test]
fn a_let_destructuring_binder_annotation_is_checked() {
    let bad = r#"
namespace test.wi794.letpat
  import anthill.prelude.{Int64, String}

  operation mk() -> (Int64, Int64) = (3, 10)
  operation drive() -> Int64 =
    let (a: String, b) = mk()
    b
end
"#;
    reject_as_binder_annotation(bad, "a contradicting let-destructure annotation must be refused");

    let good = r#"
namespace test.wi794.letpatok
  import anthill.prelude.{Int64}

  operation mk() -> (Int64, Int64) = (3, 10)
  operation drive() -> Int64 =
    let (a: Int64, b) = mk()
    a - b
end
"#;
    assert_eq!(eval_int(good, "test.wi794.letpatok.drive"), -7);
}

/// A WRONG BINDER COUNT must not be reported as a wrong ANNOTATION. Zipping a 2-binder
/// pattern against a 3-component slot by index pairs `y` with the slot's SECOND
/// component, so the per-binder check would say "binder y: expected String, got Int64" —
/// blaming an annotation that is fine for a missing parameter. The check stands down
/// unless the arities agree (the rule `validate_callback_effect_row` already follows),
/// leaving the arrow-level arity diagnostic to own it.
///
/// This is a regression guard on THIS ticket's own change: the misleading message was
/// measured on the first cut of the fix, not hypothesized.
#[test]
fn a_wrong_binder_count_is_not_reported_as_a_wrong_annotation() {
    let src = r#"
namespace test.wi794.arity
  import anthill.prelude.{Int64, String}

  operation apply3(f: (a: Int64, b: String, c: Int64) -> Int64) -> Int64 = f(1, "x", 3)

  operation drive() -> Int64 = apply3(lambda (x: Int64, y: Int64) -> x)
end
"#;
    let errs = reject(src, "a 2-binder lambda at a 3-parameter slot must be refused");
    let msg = errs.join("\n");
    assert!(
        !msg.contains("binder-annotation"),
        "an arity defect must not be reported against a binder annotation; got: {msg}",
    );
}

/// The third pattern position: a `match` ARM. `case (a: String, b) -> …` over an
/// `(Int64, Int64)` scrutinee is the same contradiction the lambda case makes, reached
/// through the branch-env code path rather than the lambda one. Tested because that path
/// was threaded by hand — an untested branch there would be a check that silently never
/// runs, which is the failure mode this whole ticket is about.
#[test]
fn a_match_arm_binder_annotation_is_checked() {
    let bad = r#"
namespace test.wi794.matchpat
  import anthill.prelude.{Int64, String}

  operation mk() -> (Int64, Int64) = (3, 10)
  operation drive() -> Int64 =
    match mk()
      case (a: String, b) -> b
end
"#;
    reject_as_binder_annotation(bad, "a contradicting match-arm annotation must be refused");

    let good = r#"
namespace test.wi794.matchpatok
  import anthill.prelude.{Int64}

  operation mk() -> (Int64, Int64) = (3, 10)
  operation drive() -> Int64 =
    match mk()
      case (a: Int64, b) -> a - b
end
"#;
    assert_eq!(eval_int(good, "test.wi794.matchpatok.drive"), -7);
}
