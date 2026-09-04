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
//! TWO BACK-OUTS, because this ticket is two changes and each row names the one it
//! measures:
//!
//!   * **(a)** rung 3 restored to `make_type_var` — the binder gets an INERT type again.
//!   * **(b)** `data_slot_arg_hints` returning `unhinted` unconditionally — the callee's
//!     declared slot type stops reaching a rule-body data term's children.
//!
//! THE MATRIX, DRIVEN — all three cells, because the two halves OVERLAP and a one-cell
//! reading would have credited the wrong one:
//!
//! ```text
//!   (a) out            1 row   part_a_a_binder_no_declaration_reaches_…
//!   (b) out            2 rows  part_b_a_binder_typed_from_the_declaration_…
//!                              part_b_a_permuted_named_tuple_binds_…
//!   both out           4 rows  those three, plus
//!                              an_unannotated_binder_in_a_rule_body_is_inferred_from_its_own_body
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
/// hint (see `known_gap_an_entity_field_lambda_is_unhinted_in_both_bodies`), so part (b)
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
        let mut kb = crate::common::try_load_kb_with(&holder_src(ns, body)).unwrap_or_else(|errs| {
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
        errs.iter()
            .any(|e| e.contains("type mismatch in takes_str.s (op-arg): expected String, got Int64")),
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
            errs.iter().any(|e| e
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

/// **THE SCOPE DECISION PART (b) MADE, PINNED AS A ROW RATHER THAN LEFT IN A COMMENT.**
/// `data_slot_arg_hints` reads an OPERATION's parameters and deliberately not an ENTITY's
/// fields: the two have different hint chains, and the constructor chain has no lambda arm
/// at all (`arrow_slot_arg_hint` reads a bare operation NAME; `hof_arg_hint` is the
/// operation chain's). So a lambda in an entity FIELD is unhinted — in a rule body and in
/// an operation body alike.
///
/// THE ASSERTION IS THE SYMMETRY, and that is the point. Both spellings LOAD the same
/// ill-typed program (an `Int64` binder handed to a `String` parameter) and both answer 7.
/// If either side starts refusing while the other does not, an asymmetry has been created
/// where this ticket removed one, and this row says so; if BOTH start refusing, the
/// entity-field gap has been closed and the row should be deleted with a note naming the
/// change that closed it.
///
/// GREEN EITHER WAY under both of this ticket's back-outs — it measures a decision, not a
/// capability, which is stated rather than left to look like coverage.
#[test]
fn known_gap_an_entity_field_lambda_is_unhinted_in_both_bodies() {
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
        let mut kb = crate::common::try_load_kb_with(&holder_src(ns, body)).unwrap_or_else(|errs| {
            panic!(
                "KNOWN GAP: an entity-field lambda takes no hint in EITHER body, so this \
                 ill-typed program loads. {ns} now refuses — if BOTH spellings refuse the \
                 gap is closed (delete this row, naming the change); if only one does, an \
                 asymmetry has been created. Got: {errs:?}"
            )
        });
        assert_eq!(only_int(&mut kb, &format!("{ns}.value")), 7);
    }
}

/// CONTROL — PART (b) DOES NOT REACH A SLOT THAT DECLARES NO FUNCTION. `term_to_string`
/// takes a reflect `Term`, which is not callable, so `hof_arg_hint`'s own gate declines
/// and the lambda is typed exactly as it was before this ticket. The row that says the
/// hint is the callee's DECLARED type and not "an arrow, everywhere a lambda is written".
///
/// GREEN EITHER WAY BY DESIGN, under both back-outs. It is the acceptance half of
/// `a_lambda_in_a_reflect_term_slot_is_still_accepted` moved into a RULE body, where part
/// (b) is what could newly have refused it.
#[test]
fn control_a_non_callable_slot_hints_a_rule_body_lambda_with_nothing() {
    let src = "\
namespace zz50b2k.rterm
  import anthill.prelude.{Int64, String}
  import anthill.reflect.{term_to_string}
  rule value(?r) :- ?r <=> term_to_string(lambda x -> x)
end
";
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
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
