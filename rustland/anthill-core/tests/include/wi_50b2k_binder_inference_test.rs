//! WI-20260904-50B2K — AN UN-ANNOTATED LAMBDA BINDER IS INFERRED: from its own body,
//! and — part (b) — from the declaration of the slot it was written in.
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
//! FOUR BACK-OUTS, because this ticket is three changes — and the third is a SPLIT, whose
//! two halves must be backed out separately or one would credit the other:
//!
//!   * **(a)** rung 3 restored to `make_type_var` — the binder gets an INERT type again.
//!   * **(b)** `data_slot_arg_hints` returning `unhinted` unconditionally — the callee's
//!     declared slot type stops reaching a rule-body data term's children.
//!   * **(pat-infer)** `parent_type_is_inference_hole` forced `false` — a tuple binder's
//!     component stops being an inference hole when its parent type is one.
//!   * **(pat-inert)** the `match unpinned` dropped for an unconditional variable — an
//!     UNDECLARED constructor's field becomes one when it can never be solved.
//!
//! THE MATRIX, DRIVEN — every cell, because the halves OVERLAP and a one-cell reading
//! would have credited the wrong one:
//!
//! ```text
//!   (a) out            1 row   part_a_a_binder_no_declaration_reaches_…
//!   (b) out            2 rows  part_b_a_binder_typed_from_the_declaration_…
//!                              part_b_a_permuted_named_tuple_binds_…
//!   both out           4 rows  those three, plus
//!                              an_unannotated_binder_in_a_rule_body_is_inferred_from_its_own_body
//!   pat-infer out      1 row   pat_a_tuple_binders_component_is_inferred_… (all 3 arms)
//!   pat-inert out      1 row   control_an_undeclared_constructors_field_stays_unnameable
//!                              — plus four PRE-EXISTING rows outside this file, named at
//!                              that row's site
//! ```
//!
//! THE OVERLAP IS THE FINDING. The row this ticket was OPENED on fell on the (a) back-out
//! when (a) shipped; (b) then reached that same slot with `apply1`'s declared type, so the
//! binder is typed at rung 2 and rung 3 is never asked — it now measures "at least one of
//! the two". `part_a_…` is what isolates (a): its lambda sits in an ENTITY FIELD, the one
//! slot shape (b) deliberately does not hint, so rung 3 alone decides it.
//!
//! The remaining rows never reach rung 3 or are hinted with nothing — one wins at rung 1,
//! one at rung 2, one sits in a non-callable slot, one measures a scope DECISION rather
//! than a capability — so they pass under every cell BY DESIGN, and that is stated rather
//! than left to look like coverage.
//!
//! BACK-OUT (b) WAS RUN OVER THE WHOLE BINARY, not just this file: **2 of 4118** rows
//! fail, and they are exactly the two `part_b_*` rows. So what the hint changes in the
//! corpus is those two programs and nothing else — the narrowness is measured rather than
//! argued from the gates.

use anthill_core::kb::term_view::TermView;
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
    v.literal_int64(kb)
        .unwrap_or_else(|| panic!("{qn}: expected an Int64 answer, got {v:?}"))
}

/// **THE ROW THIS TICKET WAS OPENED ON.** An un-annotated binder in a RULE body, where no
/// expectation reaches rung 2, is pinned by the evidence in its own body: `x + 1` has an
/// `Int64` literal, so `Additive` resolves and the call answers.
///
/// **IT NO LONGER MEASURES (a) ALONE, AND THAT IS A MEASUREMENT, NOT A CONCESSION.** It
/// fell on the (a) back-out when (a) shipped; part (b) then reached this very slot with
/// `apply1`'s declared `Function[A = Int64, B = Int64]`, so the binder is now typed at
/// rung 2 and rung 3 is never asked. Driven: back out (a) alone and this row PASSES; back
/// out both and it fails with the original "ambiguous dispatch of `Additive.add`: 3
/// instances". So it says "at least one of the two halves is present", and the row that
/// isolates (a) is `part_a_a_binder_no_declaration_reaches_is_still_inferred_from_its_body`
/// below — a slot part (b) does not hint.
///
/// Kept rather than replaced: it is the program the ticket was opened on, and its answer
/// is the acceptance the user stated.
#[test]
fn an_unannotated_binder_in_a_rule_body_is_inferred_from_its_own_body() {
    let mut kb = load(
        "zz50b2k.infer",
        "  rule value(?r) :- ?r <=> apply1(lambda x -> x + 1, 2)\n",
    );
    assert_eq!(only_int(&mut kb, "zz50b2k.infer.value"), 3);
}

/// **THE ROW THAT ISOLATES PART (a)** — a binder NO declaration reaches, pinned by its
/// own body alone.
///
/// The lambda sits in an ENTITY FIELD, which `data_slot_arg_hints` deliberately does not
/// hint (see `an_entity_field_lambda_is_refused_in_both_bodies_once_its_body_pins_the_binder`), so part (b)
/// cannot reach it in either direction and rung 3 is the only thing that decides. `x + 1`
/// then pins the binder through `Additive.add`'s signature — but only if rung 3 minted
/// something that CAN be pinned.
///
/// MEASURED, all four cells: with (a) it answers 3 whether (b) is in or out; with (a)
/// backed out it is REFUSED, again whether (b) is in or out, with
/// "ambiguous dispatch of `Additive.add`: 3 instances … and the call selects none" — the
/// inertness' own signature, since a type that could not be compared would leave NO
/// candidate instance rather than all three.
///
/// THE OPERATION-BODY TWIN IS THE CONTROL AND IT MOVES WITH IT, which is the point: an
/// entity field takes no lambda hint in either body, so both spellings sit on rung 3 and
/// both were refused before (a). This is the one shape where the two bodies were already
/// in agreement and the mint alone was wrong.
#[test]
fn part_a_a_binder_no_declaration_reaches_is_still_inferred_from_its_body() {
    for (ns, body) in [
        (
            "zz50b2k.entlit",
            "  rule value(?r) :- ?r <=> runit(holder(f: lambda x -> x + 1), 2)\n",
        ),
        (
            "zz50b2k.entlitop",
            "  operation w() -> Int64 = runit(holder(f: lambda x -> x + 1), 2)\n  \
               rule value(?r) :- ?r <=> w()\n",
        ),
    ] {
        let mut kb =
            crate::common::try_load_kb_with(&holder_src(ns, body)).unwrap_or_else(|errs| {
                panic!("{ns}: an un-hinted binder must be pinned by its own body; got: {errs:?}")
            });
        assert_eq!(only_int(&mut kb, &format!("{ns}.value")), 3);
    }
}

/// A `Function`-typed ENTITY FIELD to put a lambda in — the one slot shape part (b)
/// leaves alone, so a row built on it measures rung 3 and nothing else. `takes_str` rides
/// along for the row that needs a use CONTRADICTING an `Int64` binder; the rows that do
/// not call it are unaffected by its presence, and ONE fixture is what keeps the two rows
/// comparable.
fn holder_src(ns: &str, body: &str) -> String {
    format!(
        "\
namespace {ns}
  import anthill.prelude.{{Int64, String, Function}}
  operation takes_str(s: String) -> Int64 = 7
  sort Holder
    entity holder(f: Function[A = Int64, B = Int64])
  end
  operation runit(h: Holder, n: Int64) -> Int64 =
    match h
      case holder(f) -> f(n)
{body}end
"
    )
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

/// **PART (b) — THE BINDER TAKES ITS TYPE FROM THE CALLEE'S DECLARATION, AND THE BODY IS
/// THEN CHECKED AGAINST IT.** `takes_str` declares `s: String` and is handed the binder;
/// the only statement about that binder in the whole program is `apply1`'s declared
/// `f: Function[A = Int64, B = Int64]`, one level up in a slot WI-1058 does not
/// type-check. So the program is ill-typed and the question is whether anything can say
/// so.
///
/// **THE BACK-OUT IS A FAIL-OPEN, NOT AN ABSENCE** — measured, with
/// `data_slot_arg_hints` returning `unhinted` unconditionally: it LOADS CLEAN and the
/// goal ANSWERS 7, running an `Int64` through a `String` parameter. That is why the row
/// asserts a REFUSAL and names the message: a row asserting "it does not answer 7" would
/// also pass on a program that answers nothing for an unrelated reason.
///
/// THE FIRST WITNESS WRITTEN HERE MEASURED NOTHING and is recorded so it is not
/// re-invented: `apply1(lambda x -> x + x, 2)` answers 4 with the hint AND without it.
/// After part (a) the binder is a real inference variable, so the `Additive` dispatch
/// DEFERS instead of tying, and the runtime picks `Int64` from the actual argument —
/// exactly the outcome the hint would have produced. What the DECLARATION adds is
/// therefore observable in exactly two places: where the body's own use CONTRADICTS it
/// (this row) and where the declaration carries LABELS the body cannot invent (the tuple
/// row below). "It answers" is not one of them.
#[test]
fn part_b_a_binder_typed_from_the_declaration_refuses_a_body_that_contradicts_it() {
    let errs = crate::common::try_load_kb_with(&mismatch_src(
        "zz50b2k.contra",
        "  rule value(?r) :- ?r <=> apply1(lambda x -> takes_str(x), 2)\n",
    ))
    .err()
    .unwrap_or_default();
    assert!(
        errs.iter().any(
            |e| e.contains("type mismatch in takes_str.s (op-arg): expected String, got Int64")
        ),
        "the binder must be typed `Int64` from `apply1`'s declaration and its use refused; \
         got: {errs:?}",
    );
    // CONTROLS — the same program in the two spellings that already reach a binder type,
    // both REFUSED WITH THE SAME MESSAGE under the back-out too. They are what makes the
    // row above an AGREEMENT rather than a new refusal the rule-body spelling invented:
    // one wins at rung 1 (the annotation), the other at rung 2 (an operation body's
    // checking direction). Green either way BY DESIGN.
    for (ns, body) in [
        (
            "zz50b2k.contraop",
            "  operation w() -> Int64 = apply1(lambda x -> takes_str(x), 2)\n  \
               rule value(?r) :- ?r <=> w()\n",
        ),
        (
            "zz50b2k.contraann",
            "  rule value(?r) :- ?r <=> apply1(lambda (x: Int64) -> takes_str(x), 2)\n",
        ),
    ] {
        let errs = crate::common::try_load_kb_with(&mismatch_src(ns, body))
            .err()
            .unwrap_or_default();
        assert!(
            errs.iter()
                .any(|e| e
                    .contains("type mismatch in takes_str.s (op-arg): expected String, got Int64")),
            "{ns}: the already-typed spellings must refuse identically; got: {errs:?}",
        );
    }
}

/// The preamble for the rows above: a `String` parameter to hand the binder to, so a
/// binder typed `Int64` has a use that CONTRADICTS it.
fn mismatch_src(ns: &str, body: &str) -> String {
    format!(
        "namespace {ns}\n  import anthill.prelude.{{String}}\n{PREAMBLE}\
         operation takes_str(s: String) -> Int64 = 7\n{body}end\n"
    )
}

/// **PART (b) BUYS THE LABELS AS WELL AS THE TYPE**, and this is the order-sensitive
/// witness for it. A tuple pattern takes its component labels from the EXPECTED type
/// (`bind_and_label_pattern`, WI-803); with none, `match_tuple_pattern` zips in source
/// order and the value's source order is the LITERAL's, not the binders'.
///
/// `a - b` over `(b: 2, a: 1)` is `-1` read BY NAME and `1` read BY SLOT. A `+` fixture
/// would have summed to 3 under either correspondence and measured nothing.
///
/// FAILS ON THE PART-(b) BACK-OUT with `1` — the value
/// `wi_qqpq2_tuple_carrier_test::known_gap_a_rule_body_lambdas_binders_zip_by_slot`
/// asserted while the gap stood; that row is deleted by this change and this one replaces
/// it. GREEN UNDER THE PART-(a) BACK-OUT, measured, and for BOTH arms: the annotated arm's
/// binder types come from rung 1, and the bare arm's come from the hint's named-tuple
/// COMPONENTS (`named_tuple_field_types`), not from the sub-pattern's own rung 3. So this
/// row is (b)'s alone — the first draft's claim that its bare arm "needs both halves at
/// once" was written from the ladder and refuted by driving it.
#[test]
fn part_b_a_permuted_named_tuple_binds_a_rule_body_lambdas_binders_by_name() {
    let mut kb = load2(
        "zz50b2k.binderlabel",
        "  rule value(?r) :- ?r <=> apply2(lambda (a: Int64, b: Int64) -> a - b, (b: 2, a: 1))\n",
    );
    assert_eq!(
        only_int(&mut kb, "zz50b2k.binderlabel.value"),
        -1,
        "a rule-body lambda's binders must take their labels from the callee's declared \
         tuple, not from the literal's written order",
    );
    // The UN-ANNOTATED twin. It needs part (b) for the same two things the annotated arm
    // does — the labels AND the component types — because both ride the hint's named
    // tuple; it does NOT need part (a), measured. Written as a second arm rather than a
    // second row because it is the SAME claim: a wrong answer here and a wrong answer
    // above have one cause.
    let mut bare = load2(
        "zz50b2k.binderlabelbare",
        "  rule value(?r) :- ?r <=> apply2(lambda (a, b) -> a - b, (b: 2, a: 1))\n",
    );
    assert_eq!(only_int(&mut bare, "zz50b2k.binderlabelbare.value"), -1);
}

/// **THE ENTITY-FIELD GAP IS CLOSED, AND THE ROW IT REPLACES SAID TO WRITE THIS.** Its
/// instruction was "if BOTH spellings refuse the gap is closed (delete this row, naming
/// the change)". Both refuse. The change is part (c)'s first slice — the arrow now
/// reflects what the lambda's BODY solved — plus the check reading an entity's FIELDS.
///
/// `runit(holder(f: lambda x -> takes_str(x)), 2)` hands an `Int64` binder to a `String`
/// parameter. It used to LOAD in both spellings and answer 7: the lambda is in an entity
/// FIELD, which takes no hint in either body, so its binder stayed unpinned and its arrow
/// said `??param -> Int64` — nothing to disagree with `Function[A = Int64, B = Int64]`.
/// Now the body's own `takes_str(x)` call solves the binder to `String`, the arrow reads
/// `String -> Int64`, and both spellings refuse it.
///
/// **THE TWO HALVES HAD TO LAND TOGETHER, AND THE FIRST ONE ALONE CREATED AN ASYMMETRY** —
/// measured, and this row is what caught it. With only the arrow change, the OPERATION
/// body refused (its entity-field check compares the argument) while the RULE body still
/// loaded, because a rule-body data term is name-checked only (WI-1058) and
/// `data_slot_declared_types` read an operation's parameters alone. Extending the CHECK to
/// an entity's fields closed it. The HINT still reads operations only, deliberately: a
/// hint IMPOSES a type and the constructor chain has no lambda arm, so hinting a field
/// would put the mirror-image asymmetry back.
///
/// BACK-OUT, either half: drop the `resolve_type_deep_value` through `body_solutions` at
/// the `LambdaBody` frame and BOTH arms load again; drop the `entity_field_types` fallback
/// in `data_slot_arg_hints` and only the rule arm does — which is the asymmetry, restored.
#[test]
fn an_entity_field_lambda_is_refused_in_both_bodies_once_its_body_pins_the_binder() {
    for (ns, body) in [
        (
            "zz50b2k.entrule",
            "  rule value(?r) :- ?r <=> runit(holder(f: lambda x -> takes_str(x)), 2)\n",
        ),
        (
            "zz50b2k.entop",
            "  operation w() -> Int64 = runit(holder(f: lambda x -> takes_str(x)), 2)\n  \
               rule value(?r) :- ?r <=> w()\n",
        ),
    ] {
        let errs = crate::common::try_load_kb_with(&holder_src(ns, body))
            .err()
            .unwrap_or_else(|| {
                panic!("{ns}: an Int64 binder in a String parameter must be refused")
            });
        assert!(
            errs.iter()
                .any(|e| e.contains("expected Function[A = Int64, B = Int64], got String -> Int64")),
            "{ns}: expected the solved-arrow mismatch, got: {errs:?}",
        );
    }
}

/// CONTROL — PART (b) DOES NOT REACH A SLOT THAT DECLARES NO FUNCTION. `term_to_string`
/// takes a reflect `Term`, which is not callable, so `hof_arg_hint`'s own gate declines
/// and the lambda is typed exactly as it was before this ticket. The row that says the
/// hint is the callee's DECLARED type and not "an arrow, everywhere a lambda is written".
///
/// GREEN EITHER WAY BY DESIGN, under every back-out. It is the acceptance half of
/// `a_lambda_in_a_reflect_term_slot_is_still_accepted` moved into a RULE body, where part
/// (b) is what could newly have refused it.
///
/// AND IT SAYS MORE SINCE THE SLOT CHECK LANDED. A reflect `Term` slot now HAS a declared
/// type reaching the check, and this program still loads — because the check runs through
/// `validate_arg_against_param`, which carries the reflect-`Term` ESCAPE. A bare
/// `types_compatible` in its place would refuse this row, which is the measurement that
/// says reusing the operation body's own argument checker was the load-bearing choice and
/// not a convenience. Its sibling
/// `a_lambda_in_a_non_callable_slot_is_refused_in_both_bodies` is the same shape at a slot
/// with NO escape, and it is refused.
#[test]
fn control_a_non_callable_slot_hints_a_rule_body_lambda_with_nothing() {
    let src = "\
namespace zz50b2k.rterm
  import anthill.prelude.{Int64, String}
  import anthill.reflect.{term_to_string}
  rule value(?r) :- ?r <=> term_to_string(lambda x -> x)
end
";
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default();
    assert!(
        errs.is_empty(),
        "a lambda in a rule-body reflect `Term` slot must still be accepted; got: {errs:?}",
    );
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
/// lambda, applied from an OPERATION body, and it DRIVES the capability (answers 3). When
/// it was written the RULE-body spelling answered nothing, and this row is what pinned
/// that as an APPLICATION gap rather than a typing one; WI-20260904-QQPQ2 then closed it
/// (a tuple destructures on every carrier, not only `Value::Tuple`), so the rule-body
/// twin now answers too — see
/// `part_b_a_permuted_named_tuple_binds_a_rule_body_lambdas_binders_by_name`'s bare arm,
/// which drives exactly that spelling.
///
/// WHAT THE ROW STILL SAYS is the sub-pattern claim above: an operation body takes its
/// component types from the callee's declared arrow through the checking direction and
/// never reaches the sub-pattern's rung 3 at all. GREEN UNDER EVERY CELL OF THIS FILE'S
/// BACK-OUT MATRIX, by design.
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
        panic!(
            "must load; got {} error(s):\n{}",
            errs.len(),
            errs.join("\n")
        )
    })
}

/// **THE BODY'S OWN USE NOW BINDS FIRST, AND THE ROW THIS REPLACES SAID TO WRITE THIS.**
/// Its instruction was "if it now REFUSES, the gap has been closed: delete this row and
/// say which change closed it". The change is part (c)'s first slice.
///
/// The gap was: the op-return SOLVES the body's free variables from the declaration before
/// comparing (this ticket's fifth edit, which is what lets a let-bound un-annotated lambda
/// be returned at all), and nothing recorded the body's own side — so the DECLARATION won.
/// `?v` was committed to `String` while the body handed it to an `Int64` parameter, and
/// the program LOADED. A wrong value, not a missing refusal.
///
/// WHAT CLOSED IT: a call now REPORTS what it solved into the walk's substitution
/// (`report_call_solutions`), and the `LambdaBody` frame resolves the arrow's parameter
/// through it. The body's `twice(v)` binds `?v := Int64` — it always did, into the σ that
/// was dropped with the call — so the arrow reads `Int64 -> Int64` and the declaration has
/// a solved type to disagree with instead of a free variable to bind.
///
/// ```text
///   type mismatch in outer.return (op-return):
///     expected Function[A = String, B = Int64], got Int64 -> Int64
/// ```
///
/// BACK-OUT: drop the `resolve_type_deep_value` through `body_solutions` at the
/// `LambdaBody` frame — the arrow reverts to `??param -> Int64`, the declaration solves it
/// to `String`, and this loads again.
///
/// ITS CONTROL IS THE PROGRAM THE FIFTH EDIT EXISTS FOR:
/// `parse_test::wi342_env_dataflow_let_bound_lambda_carries_modify_effect` returns exactly
/// this shape with a declaration the body AGREES with, and must stay green — the point is
/// that the body now decides, not that returning a let-bound lambda stopped working.
#[test]
fn the_body_use_binds_a_let_bound_lambdas_binder_before_the_declaration_can() {
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
        .expect("the body pins `?v` to Int64; a String declaration must be refused");
    assert!(
        errs.iter()
            .any(|e| e.contains("expected Function[A = String, B = Int64], got Int64 -> Int64")),
        "expected the solved-arrow mismatch at the op-return, got: {errs:?}",
    );

    // THE AGREEING TWIN still loads — the body decides, and a declaration that agrees with
    // it is accepted exactly as before.
    let ok = src.replace("A = String", "A = Int64");
    let errs = crate::common::try_load_kb_with(&ok)
        .err()
        .unwrap_or_default();
    assert!(
        errs.is_empty(),
        "the agreeing declaration must still load; got: {errs:?}"
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

/// **THE `?pat` CENSUS ROW — A TUPLE BINDER'S COMPONENT IS INFERRED WHEN THE PARENT TYPE
/// IS ITSELF A HOLE.** The direct sibling of rung 3, one level down.
///
/// `bind_and_label_pattern`'s fallback minted the same inert `type_var` for two different
/// absences, and the ticket measured what flipping it wholesale costs: FOUR rows, all
/// `match s case SetLiteral(a, _, _) -> a`, because an undeclared constructor's field can
/// never be pinned. It is now SPLIT on [`UnpinnedBinder`] — this row drives the half that
/// commits, `control_an_undeclared_constructors_field_stays_unnameable` the half that
/// does not.
///
/// THE ERROR IT REMOVES IS THE INERTNESS' OWN SIGNATURE, the same one the ticket was
/// opened on and for the same reason: a type compatible with everything that commits to
/// nothing leaves ALL three instances, not none.
///
/// ```text
///   ambiguous dispatch of `anthill.prelude.Additive.add`: 3 instances provide
///   `anthill.prelude.Additive` … and the call selects none
/// ```
///
/// THREE ARMS, and the second and third are the SYMMETRY this ticket exists to keep: a
/// lambda in an ENTITY FIELD takes no hint in either body (see
/// `an_entity_field_lambda_is_refused_in_both_bodies_once_its_body_pins_the_binder`), so both spellings sat
/// on the fallback and both move together. A fix that moved only one of them would have
/// put back the asymmetry the ticket removes.
///
/// MEASURED — all three arms are REFUSED with the `Additive` ambiguity when
/// `parent_type_is_inference_hole` is neutralized to `false`, and answer 2 with it.
#[test]
fn pat_a_tuple_binders_component_is_inferred_when_the_parent_type_is_a_hole() {
    // A LET-BOUND lambda in an operation body: no expectation reaches it in EITHER
    // spelling, so the whole param type is rung 3's fresh variable and the components
    // are the fallback's.
    let mut kb = crate::common::try_load_kb_with(&format!(
        "namespace zz50b2k.patlet\n  import anthill.prelude.{{Int64, Function}}\n  \
         operation apply2(f: Function[A = (a: Int64, b: Int64), B = Int64], \
         p: (a: Int64, b: Int64)) -> Int64 = f(p)\n  \
         operation viaop() -> Int64 = let g = lambda (a, b) -> a + 1  apply2(g, (a: 1, b: 2))\n  \
         rule value(?r) :- ?r <=> viaop()\n{}",
        "end\n"
    ))
    .unwrap_or_else(|errs| panic!("let arm must load; got:\n{}", errs.join("\n")));
    assert_eq!(only_int(&mut kb, "zz50b2k.patlet.value"), 2);

    // AN ENTITY FIELD, both bodies. `data_slot_arg_hints` deliberately does not hint one,
    // so neither spelling reaches rung 2 and both sit on the fallback.
    for (ns, body) in [
        (
            "zz50b2k.patent",
            "  rule value(?r) :- ?r <=> runit2(holder2(f: lambda (a, b) -> a + 1), (a: 1, b: 2))\n",
        ),
        (
            "zz50b2k.patentop",
            "  operation w() -> Int64 = runit2(holder2(f: lambda (a, b) -> a + 1), (a: 1, b: 2))\n  \
               rule value(?r) :- ?r <=> w()\n",
        ),
    ] {
        let mut kb = crate::common::try_load_kb_with(&holder2_src(ns, body))
            .unwrap_or_else(|errs| panic!("{ns} must load; got:\n{}", errs.join("\n")));
        assert_eq!(only_int(&mut kb, &format!("{ns}.value")), 2, "{ns}");
    }
}

/// A TUPLE-parameter callable in an entity field, so a lambda written there destructures
/// components no declaration reaches — the one slot shape part (b) does not hint, in
/// either body.
fn holder2_src(ns: &str, body: &str) -> String {
    format!(
        "\
namespace {ns}
  import anthill.prelude.{{Int64, Function}}
  sort Holder2
    entity holder2(f: Function[A = (a: Int64, b: Int64), B = Int64])
  end
  operation runit2(h: Holder2, p: (a: Int64, b: Int64)) -> Int64 =
    match h
      case holder2(f) -> f(p)
{body}end
"
    )
}

/// **THE OTHER HALF OF THE SPLIT, AND IT IS WHAT THE FIRST ATTEMPT GOT WRONG.**
/// `SetLiteral` is a parse-level marker with NO declared field types, so its sub-patterns
/// arrive with no context type and nothing will EVER pin them. An inference variable here
/// would stay unsolved and reach the op-return conformance unbound — the flip that failed
/// four rows with "type mismatch in match.rule (rule): expected Int64, got ??pat".
///
/// The scrutinee here is a CONCRETE `Set[T = Int64]`, which is the point: the absence is
/// the ENTITY's declaration, not the parent's type, so no parent could have supplied it.
/// `bind_and_label_pattern`'s constructor arm therefore answers `Unnameable` outright
/// rather than reading the scrutinee.
///
/// BACK-OUT: make the fallback mint the engine's variable unconditionally (drop the
/// `match unpinned`) and this row fails, along with `eval_test::m2_set_literal_as_entity`,
/// `wi1094_named_slot_inference_test::two_inferred_sets_agree_and_merge`,
/// `wi1094_named_slot_inference_test::inference_does_not_override_a_dictionary_the_caller_supplies`
/// and `wi844_sorted_set_driver_test::omitting_the_ordering_is_resolved_and_runs`.
#[test]
fn control_an_undeclared_constructors_field_stays_unnameable() {
    let src = "namespace zz50b2k.setlit\n  import anthill.prelude.{Int64, Set}\n  \
       operation first_of_three(s: Set[T = Int64]) -> Int64 =\n    \
         match s\n      case SetLiteral(a, _, _) -> a\n      case _ -> 0\n  \
       rule value(?r) :- ?r <=> first_of_three({10, 20, 30})\nend\n";
    let mut kb = crate::common::try_load_kb_with(src)
        .unwrap_or_else(|errs| panic!("must load; got:\n{}", errs.join("\n")));
    // READ THROUGH BOTH CARRIERS, not `only_int`. The arm's result IS its bound pattern
    // variable, which is WI-20260904-EMVCB's shape exactly: such a result answers the
    // argument's `Value::Node` where an arithmetic one answers a `Value::Int`. That is an
    // evaluation question and not this row's — asserting the VALUE either way keeps the
    // row measuring the mint, and it will keep passing when EMVCB lands.
    let mut vs = crate::common::definite_unary(&mut kb, "zz50b2k.setlit.value");
    assert_eq!(vs.len(), 1, "expected exactly one answer, got {vs:?}");
    assert_eq!(int_through_any_carrier(&vs.pop().unwrap(), &kb), 10);
}

/// The `Int64` a value carries, on ANY carrier — see the EMVCB note at the one caller.
///
/// WI-20260827-14EV6: this used to be TWO reads, `Value::as_int` plus a hand-rolled
/// `Value::Node` / `NodeKind::Expr` / `Expr::Const(Literal::Int)` descent for the
/// carrier the first one could not see. `literal_int64` answers both — `occ_head`'s
/// `Expr::Const` arm IS that descent, reached through the same `as_expr` the hand-rolled
/// one matched by hand — so the second branch became unreachable and is gone.
fn int_through_any_carrier(v: &anthill_core::eval::Value, kb: &KnowledgeBase) -> i64 {
    v.literal_int64(kb)
        .unwrap_or_else(|| panic!("expected an Int64 answer on some carrier, got {v:?}"))
}

/// **THE ROW PART (c) WAS INSTRUCTED TO FLIP, AND THE SINGLE-BINDER ARM IS FLIPPED.**
///
/// `let g = lambda x -> x + x  g(2)` now LOADS AND ANSWERS 4. Nothing in the lambda's own
/// body constrains `x`, so `Additive.add`'s dispatch is abstract and the typer used to
/// demand "`requires Additive[T = …]` on enclosing sort" — a repair with NOWHERE TO GO,
/// because a lambda binder is not a type parameter of any sort or operation. Part (c)'s
/// answer is that the constraint stays owing until the evidence arrives, and for a binder
/// the evidence is at the USE: `g(2)` solves `x` at `Int64`, `Additive` provides `Int64`,
/// and the call is licensed exactly as WI-562's and WI-590's declared-`requires` licences
/// leave theirs — as the spec op, for value-directed eval.
///
/// **BACK-OUT, THREE AXES, EACH ITS OWN ROW HERE:**
///  * Drop the fourth licence (`walk_minted_carriers` / `defer_abstract_dispatch`) and the
///    `single` arm is refused again. This row.
///  * Drop the Path 2 report (`report_walk_solutions` at the env-bound-arrow argument
///    loops) and the `single` arm is refused again, because `g(2)` calls an ARROW VALUE,
///    not a named operation — the walk sees the use through no other channel. Same row,
///    and the two are independent: the licence without the report defers a requirement
///    nothing can ever answer.
///  * Drop the DISCHARGE's `observed`/`provides` test and `a_binder_used_at_a_carrier_-
///    without_the_instance_is_still_refused` goes green-when-it-should-fail — that row is
///    the one that says this is a licence and not a hole.
///
/// **THE TUPLE ARM IS STILL REFUSED, AND IT IS A DIFFERENT GAP WITH AN OWNER.** It reaches
/// the licence — measured, `minted=2` on `argtys=[??pat, ??pat]` — and is refused at the
/// discharge for want of an observation. `apply2(g, …)` DOES solve the lambda's arrow
/// against `Function[A = (a: Int64, b: Int64), B = Int64]`, but that binds the arrow's
/// PARAM, and a binder-list lambda's `?pat` components are separate variables the param
/// does not mention: nothing links `?param` to `named_tuple(a: ?pat_a, b: ?pat_b)`. That
/// link is WI-20260904-34J8Z ("a binder-list lambda's arrow param is a variable where its
/// arity says `named_tuple`"), not this licence — so the arm is kept, DRIVEN, and asserted
/// at its wrong value rather than deleted.
#[test]
fn part_c_a_binder_the_body_leaves_free_is_answered_by_its_use() {
    let src = "namespace zz50b2k.patgap\n  import anthill.prelude.{Int64}\n  \
               operation viaop() -> Int64 = let g = lambda x -> x + x  g(2)\nend\n";
    let mut kb = crate::common::try_load_kb_with(src)
        .unwrap_or_else(|errs| panic!("must load; got: {errs:?}"));
    assert_eq!(only_int(&mut kb, "zz50b2k.patgap.viaop"), 4);
}

/// The TUPLE arm of the row above, kept because the program is part (c)'s own acceptance
/// and asserted at the value it actually has. See that row for why the link it needs is
/// WI-20260904-34J8Z's and not this licence's.
#[test]
fn known_gap_a_binder_list_lambdas_components_are_not_solved_by_the_slot() {
    let src = "namespace zz50b2k.patgap2\n  import anthill.prelude.{Int64, Function}\n  \
               operation apply2(f: Function[A = (a: Int64, b: Int64), B = Int64], \
               p: (a: Int64, b: Int64)) -> Int64 = f(p)\n  \
               operation viaop() -> Int64 = \
               let g = lambda (a, b) -> a + b  apply2(g, (a: 1, b: 2))\nend\n";
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .expect("expected a refusal, but it loaded — WI-20260904-34J8Z may have landed");
    assert!(
        errs.iter().any(|e| e.contains("anthill.prelude.Additive")),
        "expected an unresolved `Additive`, got: {errs:?}",
    );
}

/// **THE LICENCE IS A LICENCE, NOT A HOLE** — the negative control, and the row that fails
/// if the discharge stops asking whether the observed carrier PROVIDES the spec.
///
/// `Bool` has no `Additive` instance. The binder is solved — `g(tt())` observes it at
/// `Bool`, so this row is NOT the "no evidence" case below — and the requirement is
/// raised at the walk's end exactly as it would have been at the call.
///
/// BACK-OUT: make `WalkSolutions::discharge` license on `!observed.is_empty()` alone and
/// this row loads, which is the whole difference between deferring a question and
/// dropping it.
#[test]
fn a_binder_used_at_a_carrier_without_the_instance_is_still_refused() {
    let src = "namespace zz50b2k.patgap3\n  import anthill.prelude.{Int64, Bool}\n  \
               operation tt() -> Bool = true\n  \
               operation viaop() -> Int64 = let g = lambda x -> x + x  let q = g(tt())  1\nend\n";
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .expect("expected a refusal, but it loaded");
    assert!(
        errs.iter().any(|e| e.contains("anthill.prelude.Additive")),
        "expected an unresolved `Additive`, got: {errs:?}",
    );
}

/// **A BINDER WITH NO USE IN ITS WALK IS GENERALIZED — part (c)'s remaining half, delivered.**
///
/// `let g = lambda x -> x + x  1` LOADS and answers 1. Nothing in the walk ever applies `g`,
/// so the licence beside it has no evidence and used to refuse — naming a `requires` clause
/// with nowhere to go, because a lambda has no declaration site to write one at. The answer
/// this row has always named is that the constraint goes INTO THE TYPE: `g` is
/// `∀a. Additive[a] => (a) -> a`, and an obligation nobody has taken on is owed by nobody.
///
/// **THE CONSTRAINT BELONGS IN THE TYPE, AND A CONTEXT SLOT IS NOT WHAT THE DECLARATION
/// FORBIDS.** `TypeExtractor.PolyType`'s declaration says "A BINDER CARRIES NO BOUND …
/// duplicating one here would give it two owners", and an earlier revision of this comment
/// read that as ruling the whole design out. It does not, and the distinction is worth
/// keeping because it is easy to misread twice (user correction, 2026-09-05):
///
///   * What it forbids is a PER-BINDER bound — an element of `binders` carrying its own —
///     and its reason is grammatical: §5.4 is `TypeParam ::= Name` and WI-850 refused the
///     `= default` arm, so there is no spelling for `T: Additive` on a binder.
///   * A SEPARATE CONTEXT SLOT (`∀a. C a => t`) is a different construct and that paragraph
///     does not address it.
///   * The "two owners" reason is about a SORT, whose written clause `SortRequiresInfo`
///     already reflects. A lambda has no declaration and so no such entry: a context on its
///     type duplicates nothing and would be the only owner.
///
/// A BOUND IS THE PRIMARY NOTION AND `requires` IS THE SPELLING IT DRIVES, not a rival to
/// it — so carrying `Additive[X]` in the type is that fact in the form a type with no
/// declaration site can hold. The static and dynamic halves are COMPLEMENTARY, not
/// alternatives: the TYPE carries the constraint, and the IR carries the dictionary
/// (`lambda_within` — WI-816 option (b), which the user's 2026-09-05 feedback there says
/// must NOT be deleted precisely because part (c) is intended).
///
/// **BACK-OUT, MEASURED VERBATIM.** Make `WalkSolutions::generalize_for_arrow` answer
/// `None` and this program is refused again with
/// `missing \`requires Additive[T = …]\` on enclosing sort`, while every other row in this
/// file — including the two that must stay REFUSED — is unmoved. That single-row back-out
/// is what says the generalization is what moved this program and not something beside it.
#[test]
fn part_c_a_binder_no_use_pins_is_generalized_into_a_polytype() {
    let src = "namespace zz50b2k.patgap4\n  import anthill.prelude.{Int64}\n  \
               operation viaop() -> Int64 = let g = lambda x -> x + x  1\nend\n";
    let mut kb = crate::common::try_load_kb_with(src)
        .unwrap_or_else(|errs| panic!("must load; got: {errs:?}"));
    // DRIVE IT, not merely load it: the operation runs and answers its body.
    assert_eq!(only_int(&mut kb, "zz50b2k.patgap4.viaop"), 1);
}

/// **WHAT STEP 2 DID *NOT* BUY, and this row exists because I nearly shipped it as the
/// witness.** One lambda applied at `Int64` AND at `Float` answers 11 (`g(2)` = 4 plus a
/// `f2i(g(1.5))` = 7) — and it answered 11 BEFORE the generalization too.
///
/// The reason is worth keeping: a use of an env-bound arrow goes through
/// `check_apply_iter`'s Path 2, whose σ is FRESH per call, so the second use never sees the
/// first one's binding; and the discharge reads `observed`, which is appended per use
/// BEFORE `report_call_solutions`' first-wins filter. Multi-type USE was therefore already
/// licensed by the walk-lifetime machinery, and the ∀ changes the mechanism without
/// changing the answer.
///
/// PASSES EITHER WAY, AND SAYS SO: it is a control against crediting the ∀ for a capability
/// the licence already had. What the ∀ buys is the row above — a lambda with NO use at all.
#[test]
fn control_a_multi_type_use_was_already_licensed_and_is_unmoved() {
    let src = "namespace zz50b2k.twoty\n  import anthill.prelude.{Int64, Float}\n  \
               operation f2i(f: Float) -> Int64 = 7\n  \
               operation viaop() -> Int64 = \
               let g = lambda x -> x + x  g(2) + f2i(g(1.5))\nend\n";
    let mut kb = crate::common::try_load_kb_with(src)
        .unwrap_or_else(|errs| panic!("must load; got: {errs:?}"));
    assert_eq!(only_int(&mut kb, "zz50b2k.twoty.viaop"), 11);
}

/// **AN ALIAS OF A GENERALIZED LAMBDA IS AS POLYMORPHIC AS THE THING IT ALIASES** — part
/// (c) step 3, and the wart step 2 shipped deliberately.
///
/// `let g = lambda x -> x + x  let h = g  1` was REFUSED while the same program without the
/// unused alias LOADED: `check_bare_ref` instantiates at every reference, so the alias minted
/// a fresh carrier and an obligation on it, and nothing then pinned that carrier. Adding an
/// unused alias broke a working program.
///
/// THE FIX IS THE OTHER HALF OF THE STANDARD RULE — instantiate freely at a reference,
/// GENERALIZE AGAIN AT THE BINDING (`WalkSolutions::regeneralize_for_let`, hooked at the
/// `LetAfterValue` frame). The narrower repair, instantiating only where something expects a
/// type, was measured and REJECTED: it accepts a function value into a `Bool` slot, since an
/// argument slot is hinted only when it is callable
/// (`a_function_value_is_still_refused_by_a_non_callable_slot`).
///
/// SEVEN SHAPES, because a rule about binding must be driven at more than the one program it
/// was written for: the alias unused and used, used TWICE (two instantiations of the alias's
/// own ∀), aliased twice, in both spellings, and the two un-aliased controls that must not
/// move. Values are asserted, not just loading.
///
/// BACK-OUT, MEASURED: make `regeneralize_for_let` answer `None` and this test fails on its
/// `unused` case with the `Additive` refusal, while the five USED and un-aliased cases pass
/// unchanged and so does every other row in this file — including
/// `a_nested_lambda_does_not_quantify_its_enclosing_binder`. That split is what says step 3
/// closes a gap rather than changing what an alias means: nothing that already worked moved.
#[test]
fn an_alias_of_a_generalized_lambda_is_generalized_again() {
    for (tag, body, want) in [
        ("unused", "let g = lambda x -> x + x  let h = g  1", 1),
        (
            "unused, varref",
            "let g = lambda x -> x + x  let h = ?g  1",
            1,
        ),
        ("used", "let g = lambda x -> x + x  let h = g  h(2)", 4),
        // TWICE — the alias's OWN ∀ is eliminated per use, which is the property
        // re-generalization restores rather than merely the absence of a refusal.
        (
            "used twice",
            "let g = lambda x -> x + x  let h = g  h(2) + h(3)",
            10,
        ),
        (
            "aliased twice",
            "let g = lambda x -> x + x  let h = g  let k = g  h(2)",
            4,
        ),
        // CONTROLS: no alias at all, used and unused. Unmoved by this change.
        ("no alias, used", "let g = lambda x -> x + x  g(2)", 4),
        ("no alias, unused", "let g = lambda x -> x + x  1", 1),
    ] {
        let ns = format!("zz50b2k.al{}", tag.replace([' ', ','], ""));
        let src = format!(
            "namespace {ns}\n  import anthill.prelude.{{Int64}}\n  \
             operation viaop() -> Int64 = {body}\nend\n"
        );
        let mut kb = crate::common::try_load_kb_with(&src)
            .unwrap_or_else(|errs| panic!("{tag}: must load; got: {errs:?}"));
        assert_eq!(only_int(&mut kb, &format!("{ns}.viaop")), want, "{tag}");
    }

    // NEGATIVE — re-generalizing must not launder the constraint. `Bool` has no `Additive`,
    // and the alias applied to one is refused exactly as the un-aliased program is.
    let neg = "namespace zz50b2k.alneg\n  import anthill.prelude.{Int64, Bool}\n  \
               operation tt() -> Bool = true\n  \
               operation viaop() -> Int64 = \
               let g = lambda x -> x + x  let h = g  let q = h(tt())  1\nend\n";
    let errs = crate::common::try_load_kb_with(neg)
        .err()
        .expect("an alias applied at `Bool` must still be refused, but it loaded");
    assert!(
        errs.iter().any(|e| e.contains("anthill.prelude.Additive")),
        "expected an unresolved `Additive` through the alias, got: {errs:?}",
    );
}

/// **A GENERALIZED LAMBDA IS STILL REFUSED BY A NON-CALLABLE SLOT** — the guard on the
/// wrong accept the row above names.
///
/// `needs_b(g)` where `needs_b(b: Bool)`: the schema must be ELIMINATED at the reference so
/// the conformance relation sees an arrow and refuses it. The message is
/// `expected Bool, got ??param -> ?_` — an ARROW, which is the evidence the ∀-elimination
/// ran, since a conformance relation has no arm for a `PolyType` and lets one through.
///
/// **BOTH SPELLINGS OF THE SAME BINDING, because the first cut eliminated at ONE of the
/// three env readers and `g` and `?g` disagreed.** `/code-review` drove it: `needs_b(g)` was
/// refused and `needs_b(?g)` LOADED — one program, two verdicts, a question mark apart — and
/// the escaped schema also reached a user diagnostic as raw internals
/// (`got PolyType[binders = cons[…], context = cons[…]]`). The elimination now has ONE owner
/// (`eliminate_env_schema`) and every reader of `env.lookup_var` goes through it.
///
/// THE PINNED-BINDER CONTROL is the row that says the `?g` path itself was never broken: the
/// same spelling with a binder the body pins (`lambda x -> 1`, no ∀ at all) was refused all
/// along, so what leaked was the SCHEMA and not the reference.
///
/// BACK-OUT: gate `check_bare_ref`'s instantiation on `expected.is_some()` and the `g` row
/// LOADS; drop the `Expr::Var` arm's call to `eliminate_env_schema` and the `?g` row LOADS.
/// Two axes, two rows — a fixture with only one spelling measured only one of them, which is
/// how the second survived a review pass.
#[test]
fn a_function_value_is_still_refused_by_a_non_callable_slot() {
    for (tag, arg, body) in [
        // THE BODY IS `x + x` AND THAT IS THE POINT — it is what makes the binder
        // unpinnable, defers the `Additive` requirement, and gives the lambda a ∀ to leak.
        // The first cut wrote `x` here and the row passed on a plain arrow, measuring
        // nothing; the back-out is what showed it.
        ("ident", "g", "x + x"),
        ("varref", "?g", "x + x"),
        // CONTROL: the same `?g` spelling with a body that PINS the binder, so there is no
        // ∀ to escape. Refused before step 2 and after — the reference path is not what
        // moved, the schema is.
        ("varref, no forall", "?g", "1"),
    ] {
        let ns = format!("zz50b2k.slot{}", tag.replace([' ', ','], ""));
        let src = format!(
            "namespace {ns}\n  import anthill.prelude.{{Int64, Bool}}\n  \
             operation needs_b(b: Bool) -> Int64 = 1\n  \
             operation viaop() -> Int64 = let g = lambda x -> {body}  needs_b({arg})\nend\n"
        );
        let errs = crate::common::try_load_kb_with(&src)
            .err()
            .unwrap_or_else(|| {
                panic!("{tag}: a function value in a `Bool` slot must be refused, but it loaded")
            });
        assert!(
            errs.iter()
                .any(|e| e.contains("expected Bool") && e.contains("->")),
            "{tag}: expected the arrow-vs-Bool mismatch (the ∀ eliminated at the \
             reference), got: {errs:?}",
        );
    }
}

/// **`g` AND `?g` ARE ONE BINDING AND MUST GET ONE VERDICT** — the row that guards the
/// one-binding-two-readers defect, now stated on the ACCEPTING side.
///
/// Before `visit_type`'s `Expr::Var` arm got the ∀-elimination, `let h = g  1` was REFUSED
/// and `let h = ?g  1` LOADED — one program, two verdicts, a question mark apart. Step 3
/// makes both LOAD, so the row moved with them: what it measures is the AGREEMENT, and it
/// would fail just as loudly if one spelling regressed to a refusal.
///
/// THE REFUSING HALF OF THE SAME GUARD is `a_function_value_is_still_refused_by_a_non_-
/// callable_slot`, which drives both spellings into a `Bool` slot. Between them the two rows
/// pin the pair on both sides of the verdict.
#[test]
fn both_spellings_of_an_alias_agree() {
    for (tag, rhs) in [("ident", "g"), ("varref", "?g")] {
        let ns = format!("zz50b2k.sp{tag}");
        let src = format!(
            "namespace {ns}\n  import anthill.prelude.{{Int64}}\n  \
             operation viaop() -> Int64 = let g = lambda x -> x + x  let h = {rhs}  h(2)\nend\n"
        );
        let mut kb = crate::common::try_load_kb_with(&src)
            .unwrap_or_else(|errs| panic!("{tag}: must load; got: {errs:?}"));
        assert_eq!(only_int(&mut kb, &format!("{ns}.viaop")), 4, "{tag}");
    }
}

/// **A DIRECT APPLICATION OF A MULTI-BINDER LAMBDA ABORTED THE TYPER**, found by
/// /code-review on this change and fixed with it.
///
/// `let g = lambda (a, b) -> a  g((a: 1, b: 2))` hit
/// `arrow_positional_param_slots`' `debug_assert!` — "an `arrow` of arity != 1 must carry
/// its parameter list as a `named_tuple`" — because a lambda's arity is its WRITTEN
/// binder count while its param type comes from the three-rung ladder, whose bottom rung
/// is a variable. `lambda_written_arity`'s own comment says exactly that ("`param_type`
/// cannot supply it — an unannotated lambda's is a fresh type var"), so the two comments
/// CONTRADICTED each other and the assert was the wrong half.
///
/// **THE ANNOTATED ARM IS THE CONTROL AND IT ABORTED IDENTICALLY**, which is what says
/// the MINT is not what decides this: per-binder annotations are read one level down, so
/// the arrow's param is a variable in both spellings. A row driving only the un-annotated
/// one would have read a pre-existing defect as this ticket's.
///
/// PRE-EXISTING — the same two programs abort on `origin/main`, where rung 3 minted the
/// inert `type_var` (equally not a `named_tuple`). Fixed here because this change makes
/// the shape a first-class INFERRED form, and the fixture that drives it
/// (`pat_a_…`) uses the INDIRECT `apply2(g, …)` spelling — one call shape away.
///
/// BACK-OUT: drop `|| arrow_param_is_undetermined(kb, fn_type)` from that assert and both
/// arms abort. In RELEASE the assert is absent and the same shape silently returns `None`,
/// which is the withholding this fix makes the debug build agree with.
///
/// THE PERMUTED ARM IS A KNOWN GAP, DRIVEN AND ASSERTED AT ITS WRONG VALUE: `g((b: 2,
/// a: 1))` answers 2, not 1. Nothing declares this lambda's parameter type, so
/// `bind_and_label_pattern` has no labels and `match_tuple_pattern` falls to source order
/// — kernel-language.md §6.7's documented fallback, and the reason it cannot be closed
/// here is WI-20260904-34J8Z: the labels would have to be INVENTED, and WI-803 takes them
/// from the expected type.
#[test]
fn a_direct_application_of_a_multi_binder_lambda_no_longer_aborts_the_typer() {
    for (tag, binders, arg, want) in [
        ("unannotated", "(a, b)", "(a: 1, b: 2)", 1),
        (
            "annotated control",
            "(a: Int64, b: Int64)",
            "(a: 1, b: 2)",
            1,
        ),
        (
            "known gap: permuted binds by SLOT, not by name",
            "(a, b)",
            "(b: 2, a: 1)",
            2,
        ),
    ] {
        let src = format!(
            "namespace zz50b2k.direct\n  import anthill.prelude.{{Int64, Function}}\n  \
             operation viaop() -> Int64 = let g = lambda {binders} -> a  g({arg})\n  \
             rule value(?r) :- ?r <=> viaop()\nend\n"
        );
        let mut kb = crate::common::try_load_kb_with(&src)
            .unwrap_or_else(|errs| panic!("{tag} must load; got:\n{}", errs.join("\n")));
        assert_eq!(only_int(&mut kb, "zz50b2k.direct.value"), want, "{tag}");
    }
}

/// **PART (b)'s HINT IS ALSO CHECKED** — a `/code-review` finding on the `?pat` tree,
/// fixed rather than filed.
///
/// Part (b) carried the callee's declared slot type down and stopped there, so a lambda
/// whose WHOLE ARROW contradicts the slot still loaded in a rule body — and this was a
/// WRONG VALUE, not a missing refusal: the rule answered a `String` from a call declared
/// `-> Int64`.
///
/// ```text
///   BEFORE  rule apply1(lambda x -> "no", 2)   loads, answers "no"
///   AFTER   type mismatch in value.body (rule):
///           expected Function[A = Int64, B = Int64], got Int64 -> String
///   TWIN    operation … = apply1(lambda x -> "no", 2)
///           type mismatch in apply1.f (op-arg): expected …, got Int64 -> String
/// ```
///
/// FOUR ARMS, and the last two are what say the fix is narrow rather than merely present:
///
///   1. the rule-body spelling, now REFUSED (it was the gap);
///   2. its operation-body twin, refused before and after — the AGREEMENT is the point,
///      and the two messages differ only in which context names the site;
///   3. a CORRECT lambda in the same slot still answers 3, so the check refuses a
///      contradiction and not the channel;
///   4. a GENERIC callee (`pick[X](f: Function[A = X, B = X], v: X)`) still LOADS. This
///      is the objection the fix was first filed as a ticket for: the check runs on a
///      FRESH σ, which cannot bind a callee's type parameters. It is not a fail-open
///      because `validate_arg_against_param` gates on GROUNDNESS — an unresolved declared
///      param reaches that gate and is withheld, which is exactly the subset a fresh σ can
///      answer. Driven, not argued.
///
/// BACK-OUT: drop the `validate_arg_against_param` call in `dispatch_calls_in_occ`'s `Ok`
/// arm. Measured over the whole binary: **1 row of 4126** — this one — so what the check
/// refuses in the corpus is this program and nothing else.
#[test]
fn part_b_a_rule_body_data_slot_checks_its_children_against_the_declaration() {
    let src_of = |body: &str| {
        format!(
            "namespace zz50b2k.slotcheck\n  import anthill.prelude.{{Int64, String, Function}}\n  \
             operation apply1(f: Function[A = Int64, B = Int64], n: Int64) -> Int64 = f(n)\n  \
             operation pick[X](f: Function[A = X, B = X], v: X) -> X = f(v)\n\
             {body}end\n"
        )
    };
    const WHOLE_ARROW: &str = "expected Function[A = Int64, B = Int64], got Int64 -> String";

    // 1. THE GAP, CLOSED — the rule-body spelling is refused.
    let errs = crate::common::try_load_kb_with(&src_of(
        "  rule value(?r) :- ?r <=> apply1(lambda x -> \"no\", 2)\n",
    ))
    .err()
    .expect("a lambda contradicting its slot must be refused in a rule body");
    assert!(
        errs.iter().any(|e| e.contains(WHOLE_ARROW)),
        "expected the whole-arrow mismatch, got: {errs:?}",
    );

    // 2. THE OPERATION-BODY TWIN, refused before and after — the agreement is the point.
    let errs = crate::common::try_load_kb_with(&src_of(
        "  operation w() -> Int64 = apply1(lambda x -> \"no\", 2)\n",
    ))
    .err()
    .expect("the operation-body twin must be refused");
    assert!(
        errs.iter().any(|e| e.contains(WHOLE_ARROW)),
        "expected the same mismatch in the op body, got: {errs:?}",
    );

    // 3. A CORRECT lambda in the same slot still ANSWERS — the check refuses a
    //    contradiction, not the channel.
    let mut kb = crate::common::try_load_kb_with(&src_of(
        "  rule value(?r) :- ?r <=> apply1(lambda x -> x + 1, 2)\n",
    ))
    .unwrap_or_else(|errs| {
        panic!(
            "a conforming lambda must still load; got:\n{}",
            errs.join("\n")
        )
    });
    assert_eq!(only_int(&mut kb, "zz50b2k.slotcheck.value"), 3);

    // 4. A GENERIC callee still LOADS — the fresh σ cannot bind `X`, so the groundness
    //    gate withholds rather than refusing. This is the row that says the fix is not a
    //    fail-open for the case it cannot decide.
    crate::common::try_load_kb_with(&src_of(
        "  rule value(?r) :- ?r <=> pick(lambda z -> z, 5)\n",
    ))
    .unwrap_or_else(|errs| {
        panic!(
            "a generic callee's slot must be WITHHELD, not refused; got:\n{}",
            errs.join("\n")
        )
    });
}

/// **THE SLOT CHECK READS WHAT THE SLOT DECLARES, NOT WHAT IT HINTS** — and that is a
/// WIDER list, which is the whole of what this row measures.
///
/// A hint is supplied only where imposing a type top-down is CORRECT (a lambda in a
/// callable slot, a call in a ground slot, …), so gating the check on the hint left every
/// other slot unchecked. A lambda written in a slot declaring `Int64` is exactly such a
/// slot: `hof_arg_hint` declines it — correctly, there is no arrow to impose — and its
/// declared type is nonetheless what the operation-body spelling compares against.
///
/// ```text
///   rule value(?r) :- ?r <=> addI(lambda x -> x, 1)
///     BEFORE  loads
///     AFTER   type mismatch in value.body (rule): expected Int64, got ??param -> ??param
///   operation w() -> Int64 = addI(lambda x -> x, 1)
///     type mismatch in addI.a (op-arg): expected Int64, got ??param -> ??param
/// ```
///
/// THE OPERATION-BODY TWIN IS THE CONTROL and it was refused all along — so this row
/// measures the two spellings COMING INTO AGREEMENT, which is what the ticket is for, and
/// not a new refusal the rule-body spelling invented.
///
/// BACK-OUT: have the check read `expected` (the hint) instead of `declared`. The rule arm
/// then loads and the op arm still refuses — the asymmetry, restored. `data_slot_declared_types`
/// returning `undeclared` unconditionally backs out the same row.
///
/// ITS NEIGHBOUR IS `control_a_non_callable_slot_hints_a_rule_body_lambda_with_nothing`,
/// the same shape at a reflect `Term` slot, which still LOADS — the escape is in the
/// checker, so widening what is checked did not widen what is refused.
#[test]
fn a_lambda_in_a_non_callable_slot_is_refused_in_both_bodies() {
    let src_of = |body: &str| {
        format!(
            "namespace zz50b2k.widen\n  import anthill.prelude.{{Int64}}\n  \
             operation addI(a: Int64, b: Int64) -> Int64 = 9\n{body}end\n"
        )
    };
    for (tag, body) in [
        (
            "rule",
            "  rule value(?r) :- ?r <=> addI(lambda x -> x, 1)\n",
        ),
        ("op", "  operation w() -> Int64 = addI(lambda x -> x, 1)\n"),
    ] {
        let errs = crate::common::try_load_kb_with(&src_of(body))
            .err()
            .unwrap_or_else(|| panic!("{tag}: a lambda in an Int64 slot must be refused"));
        assert!(
            errs.iter()
                .any(|e| e.contains("expected Int64, got ??param -> ??param")),
            "{tag}: expected the arrow-against-Int64 mismatch, got: {errs:?}",
        );
    }
}

/// **A POSITIONAL ARGUMENT BESIDE A NAMED ONE WAS HINTED FROM THE WRONG SLOT** — found by
/// /code-review, and the defect was in the SHARED hint chain rather than in this ticket's
/// new channel.
///
/// `apply_arg_hints` mapped a positional argument with `params[i]`, but a named argument
/// CONSUMES a parameter, so a positional one beside it does not land at its own index.
/// The check has always used the rank-among-NOT-named rule
/// (`positional_param_indices`, WI-20260827-1F0QP); the hint did not. So the two read
/// DIFFERENT SLOTS, and the visible result is a well-typed program REFUSED:
///
/// ```text
///   operation f4(a: Function[A = String, B = String],
///                b: Function[A = Int64,  B = Int64]) -> Int64
///   f4(lambda x -> x + 1, a: g)
///     BEFORE  type mismatch in add.b (op-arg): expected String, got Int64
///     AFTER   loads
/// ```
///
/// The lambda is parameter `b`; the raw index hinted it with `a`'s `String`, so its body
/// was checked at the wrong type.
///
/// **BOTH SPELLINGS REPORTED IT IDENTICALLY, AND THAT IS WHY IT SURVIVED.** This ticket's
/// design point is that a rule body hints through the operation body's OWN chain, so the
/// two cannot come to hint differently — which is exactly what kept a shared defect
/// SYMMETRIC and therefore invisible to every rule-vs-op comparison in this file. It
/// surfaced only because `data_slot_arg_hints`' sibling list was corrected to the right
/// owner and left this one disagreeing INSIDE ONE FUNCTION.
///
/// BACK-OUT: restore `op_params.and_then(|ps| ps.get(i))` in `apply_arg_hints`' positional
/// loop; both arms below fail. The all-positional arm is the CONTROL — it has no named
/// argument, so the two mappings agree by construction and it passes either way.
#[test]
fn a_positional_argument_beside_a_named_one_is_hinted_from_the_slot_it_takes() {
    let src_of = |body: &str| {
        format!(
            "namespace zz50b2k.slotmap\n  import anthill.prelude.{{Int64, String, Function}}\n  \
             operation g(s: String) -> String = s\n  \
             operation f4(a: Function[A = String, B = String], \
             b: Function[A = Int64, B = Int64]) -> Int64 = 1\n{body}end\n"
        )
    };
    for (tag, body) in [
        (
            "rule",
            "  rule value(?r) :- ?r <=> f4(lambda x -> x + 1, a: g)\n",
        ),
        (
            "op",
            "  operation w() -> Int64 = f4(lambda x -> x + 1, a: g)\n",
        ),
        // CONTROL: no named argument, so raw index and rank-among-unnamed agree.
        (
            "all-positional control",
            "  rule value(?r) :- ?r <=> f4(g, lambda x -> x + 1)\n",
        ),
    ] {
        let errs = crate::common::try_load_kb_with(&src_of(body))
            .err()
            .unwrap_or_default();
        assert!(
            errs.is_empty(),
            "{tag}: the lambda is parameter `b` and must be hinted `Int64`; got: {errs:?}",
        );
    }
}
/// **BOTH ARROW HALVES RESOLVE TOGETHER, OR A SHARED BINDER SPLITS** — /code-review on the
/// first cut of part (c), and it was a WRONG ACCEPT rather than a lost refusal.
///
/// That cut resolved only the arrow's DOMAIN through what the body solved. When the
/// binder's variable occurs in the codomain too, the two halves stop being the same
/// variable: the domain reads `Int64` while the codomain still reads `??param`, so nothing
/// conflicts, and the op-return's declaration-solve is free to bind the leftover to
/// whatever the declaration says.
///
/// ```text
///   operation outer() -> Function[A = Int64, B = (a: Int64, b: String)]
///     = let f = lambda v -> (a: twice(v), b: v)  f
///
///   domain-only   LOADS — `b` accepted as String though `v : Int64`
///   both halves   type mismatch in outer.return (op-return):
///                 expected Function[A = Int64, B = (a: Int64, b: String)],
///                 got Int64 -> (a: Int64, b: Int64)
/// ```
///
/// THE AGREEING TWIN IS THE CONTROL and must load — the point is that the body decides,
/// not that a lambda returning a tuple stopped working.
///
/// BACK-OUT: drop the `body_ty` / `body_effects` resolutions at the `LambdaBody` frame and
/// the first arm loads again. The frame's own comment states the invariant this protects
/// ("the arrow's param slot and the body's view of the param agree"), and Path 1 states
/// the rule: resolve the return type AND the effect row, or one call reports two states of
/// one σ.
#[test]
fn both_halves_of_a_solved_arrow_resolve_together() {
    let src_of = |b: &str| {
        format!(
            "namespace zz50b2k.desync\n  import anthill.prelude.{{Int64, String, Function}}\n  \
             operation twice(v: Int64) -> Int64 = v\n  \
             operation outer() -> Function[A = Int64, B = {b}]\n    \
               = let f = lambda v -> (a: twice(v), b: v)\n      f\nend\n"
        )
    };
    let errs = crate::common::try_load_kb_with(&src_of("(a: Int64, b: String)"))
        .err()
        .expect("`v` is Int64 in both halves; a String codomain component must be refused");
    assert!(
        errs.iter()
            .any(|e| e.contains("got Int64 -> (a: Int64, b: Int64)")),
        "expected the arrow solved in BOTH halves, got: {errs:?}",
    );

    let errs = crate::common::try_load_kb_with(&src_of("(a: Int64, b: Int64)"))
        .err()
        .unwrap_or_default();
    assert!(
        errs.is_empty(),
        "the agreeing declaration must still load; got: {errs:?}"
    );
}

/// **A NESTED LAMBDA MUST NOT QUANTIFY ITS ENCLOSING BINDER** — the side condition every
/// let-generalization has, which the first cut of step 2 omitted, and `/code-review`
/// MEASURED the wrong accept it let through.
///
/// `let g = lambda x -> (x + x, lambda y -> x)  let r = g(true)  1` LOADED. The INNER
/// lambda's arrow is `(?y) -> ?x`, so the OUTER binder `?x` is free in it and the
/// generalization quantified it THERE — at a frame that had no business owning it. `g(true)`
/// then pinned `?x := Bool`, but the requirement was already marked generalized with no
/// instantiation of its own, so `Additive[Bool]` was never asked and a program that adds
/// two booleans type-checked.
///
/// THREE ROWS, AND THE MIDDLE ONE IS WHAT ATTRIBUTES IT. The same program with the inner
/// lambda REMOVED was refused all along, so the accept is the nesting and not the `Bool`;
/// and the `Int64` spelling must keep LOADING, so the fix is a side condition and not a
/// blanket refusal of nested lambdas.
///
/// **THE BACK-OUT IS A 2x2 AND THE ROW CANNOT SEPARATE THE TWO GUARDS — measured, and said
/// here rather than credited to one of them.** The repair for this defect was the `env_free`
/// side condition in `generalize_for_arrow`; the review's other finding added a second
/// guard, `discharge`'s `contradicted` test, which refuses to license a generalized
/// requirement whose own carrier was OBSERVED at a non-providing sort. Each alone refuses
/// this program:
///
///     env_free  contradicted   this row
///        on         on           passes
///        off        on           passes
///        on         off          passes
///        off        off          FAILS — the program loads
///
/// So the row measures "at least one of the two is live", and both are kept for different
/// reasons: `env_free` is the principled rule (a variable the environment still holds is not
/// this frame's to quantify, whatever anyone later observes), while `contradicted` is the
/// one that refuses to reach a licence by DISCARDING evidence the walk already collected.
/// A fixture separating them would need an outer binder pinned at a non-providing carrier by
/// a route that produces no observation; none was constructible here, and that absence is
/// the honest state rather than a claim that the pair is redundant.
#[test]
fn a_nested_lambda_does_not_quantify_its_enclosing_binder() {
    let capture_bool = "namespace zz50b2k.cap1\n  import anthill.prelude.{Int64, Bool}\n  \
        operation viaop() -> Int64 = \
        let g = lambda x -> (x + x, lambda y -> x)  let r = g(true)  1\nend\n";
    let errs = crate::common::try_load_kb_with(capture_bool)
        .err()
        .expect("a `Bool` carrier with no `Additive` must be refused, but it loaded");
    assert!(
        errs.iter().any(|e| e.contains("anthill.prelude.Additive")),
        "expected an unresolved `Additive`, got: {errs:?}",
    );

    // CONTROL 1 — the same program with NO inner lambda. Refused before and after, which is
    // what says the accept above was the NESTING rather than the carrier.
    let no_inner = "namespace zz50b2k.cap2\n  import anthill.prelude.{Int64, Bool}\n  \
        operation viaop() -> Int64 = let g = lambda x -> (x + x, x)  let r = g(true)  1\nend\n";
    assert!(
        crate::common::try_load_kb_with(no_inner).is_err(),
        "the inner-lambda-free twin must be refused too",
    );

    // CONTROL 2 — the same NESTING at a carrier that DOES provide `Additive`. It must still
    // load: the repair is a side condition on which frame may quantify, not a refusal of
    // nested lambdas.
    let capture_int = "namespace zz50b2k.cap3\n  import anthill.prelude.{Int64}\n  \
        operation viaop() -> Int64 = \
        let g = lambda x -> (x + x, lambda y -> x)  let r = g(2)  1\nend\n";
    let mut kb = crate::common::try_load_kb_with(capture_int)
        .unwrap_or_else(|errs| panic!("the Int64 nesting must load; got: {errs:?}"));
    assert_eq!(only_int(&mut kb, "zz50b2k.cap3.viaop"), 1);
}

/// **A DESTRUCTURING `let` IS LEFT EXACTLY AS IT WAS, and that is a gate rather than an
/// omission.** `/code-review` drove the regression the first cut of step 3 caused:
///
///     let g = lambda x -> x + x   let (h, k) = (g, g)   h(2) + k(3)
///
/// loads without the generalization and was REFUSED with it — `bound_ty` is the TUPLE, so
/// quantifying it put a ∀ where `bind_and_label_pattern` reads component types, every
/// component fell to the unnameable `?pat` form, and both names reported "unknown functor"
/// for names that are in fact bound. The rule is stated for a VARIABLE binding and is now
/// applied only there; pushing a ∀ inside a tuple's components is a different construct.
///
/// MEASURED IDENTICAL WITH AND WITHOUT `regeneralize_for_let` — all four rows below — which
/// is what says the gate leaves destructuring untouched rather than half-served.
///
/// THE `k`-UNUSED ROW IS THE DESTRUCTURING TWIN OF THE ALIAS WART, AND IT IS PRE-EXISTING:
/// each component reference instantiates, `h(2)` pins one and nothing pins `k`'s, so the
/// discharge refuses. It was refused before step 3 by the same route. Closing it needs the
/// ∀ to live on the COMPONENT — the construct this gate declines — so it is pinned at its
/// value rather than left to look like coverage.
#[test]
fn a_destructuring_let_is_unmoved_by_the_generalization() {
    // Both components USED: loads, and answers `2*2 + 2*3`.
    let used = "namespace zz50b2k.dl1\n  import anthill.prelude.{Int64}\n  \
                operation viaop() -> Int64 = \
                let g = lambda x -> x + x  let (h, k) = (g, g)  h(2) + k(3)\nend\n";
    let mut kb = crate::common::try_load_kb_with(used)
        .unwrap_or_else(|errs| panic!("both components used must load; got: {errs:?}"));
    assert_eq!(only_int(&mut kb, "zz50b2k.dl1.viaop"), 10);

    // KNOWN GAP, PRE-EXISTING: one component unused, so its instance is never pinned.
    let one = "namespace zz50b2k.dl2\n  import anthill.prelude.{Int64}\n  \
               operation viaop() -> Int64 = \
               let g = lambda x -> x + x  let (h, k) = (g, g)  h(2)\nend\n";
    let errs = crate::common::try_load_kb_with(one)
        .err()
        .expect("KNOWN GAP: expected a refusal — if this loads, the ∀ reached a component");
    assert!(
        errs.iter().any(|e| e.contains("anthill.prelude.Additive")),
        "expected an unresolved `Additive` for the unused component, got: {errs:?}",
    );

    // CONTROL: a destructuring `let` with no lambda in it at all is untouched by any of this.
    let plain = "namespace zz50b2k.dl3\n  import anthill.prelude.{Int64}\n  \
                 operation viaop() -> Int64 = let (h, k) = (1, 2)  h + k\nend\n";
    let mut kb = crate::common::try_load_kb_with(plain)
        .unwrap_or_else(|errs| panic!("a plain destructuring let must load; got: {errs:?}"));
    assert_eq!(only_int(&mut kb, "zz50b2k.dl3.viaop"), 3);
}

/// **A LAMBDA WRITTEN DIRECTLY IN AN ARGUMENT SLOT KEEPS ITS ARROW** — the wrong accept that
/// moved generalization from the lambda to the `let`.
///
/// Step 2 quantified at the `LambdaBody` frame, i.e. at EVERY lambda. A lambda written
/// directly as an argument then carried a ∀ into a slot no reader eliminates it for, and
/// `validate_arg_against_param` has no arm for one (`type_head_is_callable` answers `false`
/// for a `PolyType`), so:
///
///     addI(a: Int64, b: Int64)      addI(a: lambda x -> x + x, b: 1)   LOADED
///
/// A function value in an `Int64` slot, in silence. THE CONTROL IS THE SAME PROGRAM WITH A
/// REQUIREMENT-FREE LAMBDA (`lambda x -> x`, which mints no deferral and so never
/// generalized): it was refused all along, which is what isolates the ∀ as the cause rather
/// than the argument position.
///
/// THE FIX IS WHERE, NOT WHAT: the standard rule generalizes at a `let` BINDING, not at a
/// lambda. Moving it there means a lambda in an argument slot simply keeps its arrow and is
/// checked as one — no consumer had to learn to eliminate, and the wrong-FRAME capture defect
/// (`a_nested_lambda_does_not_quantify_its_enclosing_binder`) became structurally impossible
/// at the same time, since there is now one generalization point instead of one per lambda.
///
/// BACK-OUT: call the producer from the `LambdaBody` frame again and the first row LOADS
/// while the second stays refused.
#[test]
fn a_lambda_in_an_argument_slot_is_not_generalized() {
    for (tag, lam) in [
        ("constrained", "lambda x -> x + x"),
        ("plain control", "lambda x -> x"),
    ] {
        let ns = format!("zz50b2k.dir{}", tag.len());
        let src = format!(
            "namespace {ns}\n  import anthill.prelude.{{Int64}}\n  \
             operation addI(a: Int64, b: Int64) -> Int64 = a + b\n  \
             operation viaop() -> Int64 = addI(a: {lam}, b: 1)\nend\n"
        );
        let errs = crate::common::try_load_kb_with(&src)
            .err()
            .unwrap_or_else(|| {
                panic!("{tag}: a function value in an `Int64` slot must be refused, but it loaded")
            });
        assert!(
            errs.iter()
                .any(|e| e.contains("expected Int64") && e.contains("->")),
            "{tag}: expected the arrow-vs-Int64 mismatch, got: {errs:?}",
        );
    }
}

/// **KNOWN GAP: AN ANNOTATED ALIAS OF AN UN-ANNOTATED LAMBDA IS REFUSED**, and it is part
/// (a)'s rung-3 flip meeting `types_compatible`, not part (c)'s ∀.
///
///     let g = lambda x -> x   let h: Function[A = Int64, B = Int64] = g   h(2)
///       -> type mismatch in h.annotation (let-binding):
///          expected Function[A = Int64, B = Int64], got ??param -> ??param
///
/// The lambda mints NO requirement, so nothing here is generalized — which is what places the
/// gap. Rung 3 now gives an un-annotated binder a real FLEXIBLE variable where it used to
/// mint the inert `type_var` form, and `types_compatible_term_dispatch` has an arm that
/// accepts a `type_var` against anything and none for a flex variable, so the subtype
/// relation refuses what unification would accept. §8 says a flex variable "unifies with
/// anything"; the SUBTYPE relation does not bind it.
///
/// CONTROL, AND IT IS WHAT MAKES THIS A GAP RATHER THAN A RULE: the same annotation written
/// DIRECTLY on the lambda LOADS and answers 4, because the annotation threads down as
/// `expected` and the binder takes rung 2 instead of rung 3. One program, two spellings, two
/// verdicts.
///
/// NOT FIXED HERE DELIBERATELY. The repair is an arm in `types_compatible`, a hot relation
/// shared by every conformance check in the typer — WI-20260826-N01PY is this repo's record
/// of what widening one reaches — and the failure is a REFUSAL of an unusual spelling rather
/// than a wrong accept. Driven and asserted at its value so it cannot be mistaken for
/// coverage. /code-review found it.
#[test]
fn known_gap_an_annotated_alias_of_an_unannotated_lambda_is_refused() {
    let aliased = "namespace zz50b2k.ann1\n  import anthill.prelude.{Int64, Function}\n  \
        operation viaop() -> Int64 = \
        let g = lambda x -> x  let h: Function[A = Int64, B = Int64] = g  h(2)\nend\n";
    let errs = crate::common::try_load_kb_with(aliased)
        .err()
        .expect("KNOWN GAP: expected a refusal — if this loads, `types_compatible` grew the arm");
    assert!(
        errs.iter().any(|e| e.contains("h.annotation")),
        "expected the let-binding annotation mismatch, got: {errs:?}",
    );

    // CONTROL: the annotation written directly on the lambda takes rung 2 and loads.
    let direct = "namespace zz50b2k.ann2\n  import anthill.prelude.{Int64, Function}\n  \
        operation viaop() -> Int64 = \
        let h: Function[A = Int64, B = Int64] = lambda x -> x  h(2)\nend\n";
    let mut kb = crate::common::try_load_kb_with(direct)
        .unwrap_or_else(|errs| panic!("the directly-annotated twin must load; got: {errs:?}"));
    assert_eq!(only_int(&mut kb, "zz50b2k.ann2.viaop"), 2);
}
