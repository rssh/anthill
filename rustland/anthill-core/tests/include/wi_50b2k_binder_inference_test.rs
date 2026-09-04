//! WI-20260904-50B2K — AN UN-ANNOTATED LAMBDA BINDER IS INFERRED FROM ITS OWN BODY.
//!
//! `type_check_node`'s `Expr::Lambda` arm picks the binder's type from a three-rung
//! ladder: the annotation, the `expected` arrow's param slot (the CHECKING direction),
//! and — when neither applies — a fresh one it mints itself. That last rung is
//! SYNTHESIS, and the ladder's own comment has always said what it is for: "left for
//! body usage and the eventual call site to pin via unification".
//!
//! It could not be pinned. Rung 3 minted a `TypeExtractor.TypeVar`, whose whole content
//! is that it is NEVER BOUND — inert by design, compatible with anything without
//! committing (`KnowledgeBase::make_type_var`'s doc; the M6 flounder posture). That form
//! answers a different question, "no type is available here", which is right for
//! `value_type_term`'s RUN-TIME fallback (a runtime reader must not commit what typing
//! never decided) and wrong for a binder whose type is to be INFERRED.
//!
//! THE OBSERVED FAILURE WAS THE INERTNESS' SIGNATURE, not a unification failure: a type
//! that could not be compared would leave NO candidate instance, while one that compares
//! against everything and commits to nothing leaves ALL of them —
//!
//! ```text
//!   :- ?r <=> apply1(lambda x -> x + 1, 2)
//!        ambiguous dispatch of `anthill.prelude.Additive.add`: 3 instances provide
//!        `anthill.prelude.Additive` … and the call selects none
//! ```
//!
//! WHICH ROWS FALL WHEN THE CHANGE IS BACKED OUT (rung 3 restored to `make_type_var`):
//! only the first. The other two never reach rung 3 — one wins at rung 1, the other at
//! rung 2 — so they are the controls that say this change did not simply widen
//! acceptance everywhere. They pass either way BY DESIGN, and that is stated rather than
//! left to look like coverage.

use anthill_core::kb::KnowledgeBase;

/// A higher-order operation to hand a lambda to, so a row that claims a binder was
/// inferred has a call that can only work if it was.
const PREAMBLE: &str = "  import anthill.prelude.{Int64, Bool, Function}\n  \
   operation apply1(f: Function[A = Int64, B = Int64], n: Int64) -> Int64 = f(n)\n";

fn load(ns: &str, body: &str) -> KnowledgeBase {
    let src = format!("namespace {ns}\n{PREAMBLE}{body}end\n");
    crate::common::try_load_kb_with(&src).unwrap_or_else(|errs| {
        panic!(
            "must load; got {} error(s):\n{}",
            errs.len(),
            errs.join("\n")
        )
    })
}

/// The one definite Int64 answer of a unary goal — the VALUE, not "something answered".
/// `definite_unary` is used rather than a solution count because a FLOUNDERED solution
/// counts as one there (WI-20260822-WZX6B) and every row here would then pass on a
/// residual.
fn only_int(kb: &mut KnowledgeBase, qn: &str) -> i64 {
    let mut vs = crate::common::definite_unary(kb, qn);
    assert_eq!(vs.len(), 1, "{qn}: expected exactly one answer, got {vs:?}");
    let v = vs.pop().unwrap();
    v.as_int()
        .unwrap_or_else(|| panic!("{qn}: expected an Int64 answer, got {v:?}"))
}

/// **THE ROW THIS TICKET EXISTS FOR.** An un-annotated binder in a RULE body, where no
/// expectation reaches rung 2, is pinned by the evidence in its own body: `x + 1` has an
/// `Int64` literal, so `Additive` resolves and the call answers.
///
/// FAILS ON THE BACK-OUT with "ambiguous dispatch of `Additive.add`: 3 instances".
#[test]
fn an_unannotated_binder_in_a_rule_body_is_inferred_from_its_own_body() {
    let mut kb = load(
        "zz50b2k.infer",
        "  rule value(?r) :- ?r <=> apply1(lambda x -> x + 1, 2)\n",
    );
    assert_eq!(only_int(&mut kb, "zz50b2k.infer.value"), 3);
}

/// CONTROL — rung 1. The annotated twin wins at the annotation and never reaches the
/// mint, so it answers both before and after. Green either way BY DESIGN.
#[test]
fn the_annotated_twin_is_unmoved() {
    let mut kb = load(
        "zz50b2k.ann",
        "  rule value(?r) :- ?r <=> apply1(lambda (x: Int64) -> x + 1, 2)\n",
    );
    assert_eq!(only_int(&mut kb, "zz50b2k.ann.value"), 3);
}

/// CONTROL — rung 2. In an OPERATION body the callee's arrow slot supplies the binder's
/// type through the checking direction, so this one never reaches the mint either.
/// Green either way BY DESIGN — and it is the row that says the rule-body and
/// operation-body spellings now agree rather than the rule-body one having been widened
/// past it.
#[test]
fn the_operation_body_twin_is_unmoved() {
    let mut kb = load(
        "zz50b2k.viaop",
        "  operation viaop() -> Int64 = apply1(lambda x -> x + 1, 2)\n  \
           rule value(?r) :- ?r <=> viaop()\n",
    );
    assert_eq!(only_int(&mut kb, "zz50b2k.viaop.value"), 3);
}




/// **THE SUB-PATTERN LADDER WAS NOT FLIPPED, AND THIS ROW SAYS WHY IT COULD NOT BE.** A
/// tuple-destructuring binder's COMPONENTS take their type from a ladder of their own
/// (`scrutinee_type` -> the component's annotation -> a fresh one), and rung 3 there still
/// mints a `type_var`. Flipping it as the lambda's own rung 3 was flipped FAILED FOUR
/// ROWS, all one error — "type mismatch in match.rule (rule): expected Int64, got ??pat" —
/// on the shape `match s case SetLiteral(a, _, _) -> a` over a `Set[T = Int64]`.
/// `SetLiteral` is a parse-level marker with NO declared field types, so its sub-patterns
/// arrive with no context type and NOTHING CAN EVER PIN THEM. That site serves both
/// questions at once: a tuple binder's component is a type to be INFERRED, an undeclared
/// constructor's field is a type nobody can NAME. See the note at the mint.
///
/// THIS ROW IS THE CONTROL THAT KEEPS THE OTHER HALF HONEST — the identical two-binder
/// lambda, applied from an OPERATION body, and it DRIVES the capability (answers 3). It
/// therefore pins that the rule-body spelling's zero answers are an APPLICATION gap
/// (WI-20260904-QQPQ2: a multi-binder lambda in a rule body loads and is never applied —
/// measured, its ANNOTATED twin answers nothing either, while `sum2((a: 1, b: 2))` in the
/// same position answers 3) and not a typing one.
///
/// GREEN EITHER WAY BY DESIGN under every back-out in this file: an operation body takes
/// its component types from the callee's declared arrow through the checking direction and
/// never reaches the sub-pattern's rung 3 at all.
#[test]
fn the_tuple_binders_operation_body_twin_drives_and_is_unmoved() {
    let mut kb = load2(
        "zz50b2k.tupleop",
        "  operation viaop2() -> Int64 = apply2(lambda (a, b) -> a + b, (a: 1, b: 2))\n  \
           rule value(?r) :- ?r <=> viaop2()\n",
    );
    assert_eq!(only_int(&mut kb, "zz50b2k.tupleop.value"), 3);
}

/// A tuple-parameter higher-order operation, so the row above has a slot whose
/// components a lambda must destructure.
fn load2(ns: &str, body: &str) -> KnowledgeBase {
    let src = format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, Bool, Function}}\n  \
         operation apply2(f: Function[A = (a: Int64, b: Int64), B = Int64], \
         p: (a: Int64, b: Int64)) -> Int64 = f(p)\n{body}end\n"
    );
    crate::common::try_load_kb_with(&src).unwrap_or_else(|errs| {
        panic!("must load; got {} error(s):\n{}", errs.len(), errs.join("\n"))
    })
}


/// **A KNOWN GAP, PINNED RATHER THAN ASSERTED AWAY.** The op-return now SOLVES the body's
/// free variables from the declaration before comparing, which is what lets a let-bound
/// un-annotated lambda be returned at all. The same mechanism lets the DECLARATION win
/// over a constraint the body's own use implies, with nothing recording the body's side:
/// below, `?v` is committed to `String` while the body hands it to an `Int64` parameter.
///
/// NOT A REGRESSION, and that is measured — `/code-review` drove it with the op-return
/// solve BACKED OUT and it loaded clean there too. What this ticket added is the
/// MECHANISM, so the row exists to say what nothing covers: there is no control asserting
/// the opposite direction, and if a future change makes the body's use bind first, this
/// row goes red and points at the paragraph that says why it was left.
///
/// The row asserts the CURRENT permissive behaviour deliberately. Flipping it to a
/// refusal is a decision about whether a lambda binder's uses constrain it — WI-20260904-
/// 50B2K part (c), the generalization half, is where that lands.
#[test]
fn known_gap_the_declaration_may_solve_a_binder_the_body_contradicts() {
    let src = "\
namespace zz50b2k.gap
  import anthill.prelude.{Int64, String, Function}
  operation twice(v: Int64) -> Int64 = v
  operation outer() -> Function[A = String, B = Int64]
    = let f = lambda v -> twice(v)
      f
end
";
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default();
    assert!(
        errs.is_empty(),
        "KNOWN GAP: this loads today — `?v` is solved to `String` from the declaration \
         while the body hands it to an `Int64` parameter. If it now REFUSES, the gap has \
         been closed: delete this row and say which change closed it. Got: {errs:?}",
    );
}

/// **THE REFLECT-`Term` ESCAPE OUTRANKS THE CALLABLE VERDICT.** `value -> Term` is a TOTAL
/// conversion — `validate_arg_against_param` states it as "accept any actual vs declared
/// Term" — so a FUNCTION is admissible in a `Term` slot and
/// `callable_against_callable_free` must decline there.
///
/// FOUND BY `/code-review`, and it was a live regression: with the escape left to the
/// callers, the new verdict answered first at `nominal_head_mismatch`'s top and this
/// program flipped from LOADS CLEAN to "expected Term, got ??param -> ??param".
///
/// THE ANNOTATED TWIN IS THE CONTROL, and its asymmetry is the whole signature: it is
/// GROUND, so it never reaches the non-ground branch where the verdict lives, and it
/// loaded clean throughout. A row with only the bare spelling would not have shown that
/// the defect was confined to the non-ground path.
#[test]
fn a_lambda_in_a_reflect_term_slot_is_still_accepted() {
    // The lambda goes DIRECTLY into `term_to_string(t: Term)`. An `as_term(..)` wrapper
    // would route it through a GENERIC `E` slot instead and the row would measure nothing
    // — verified by backing the guard out and watching the wrapped spelling stay green.
    let src = |lam: &str| {
        format!(
            "\
namespace zz50b2k.term{}
  import anthill.prelude.{{Int64, String}}
  import anthill.reflect.{{term_to_string}}
  operation p() -> String = term_to_string({lam})
end
",
            if lam.contains(':') { "ann" } else { "bare" }
        )
    };
    for lam in ["lambda x -> x", "lambda (x: Int64) -> x"] {
        let errs = crate::common::try_load_kb_with(&src(lam))
            .err()
            .unwrap_or_default();
        assert!(
            errs.is_empty(),
            "a lambda in a reflect `Term` slot must be accepted ({lam}); got: {errs:?}",
        );
    }
}
