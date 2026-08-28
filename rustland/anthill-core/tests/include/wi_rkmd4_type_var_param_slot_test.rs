//! WI-RKMD4 — an argument whose SORT differs from a parameter type CONTAINING A TYPE
//! VARIABLE must be refused, and the variable's own slot must stay free.
//!
//! ## What was wrong, and why the silent pass was the worst outcome available
//!
//! `validate_arg_against_param` gates on groundness (WI-385): a pair still carrying a
//! variable is someone else's to settle, so it returned `Ok` unchecked. Right about the
//! variable's SLOT, wrong about the constructor the slot hangs off —
//! `sum_flat(m: Text[Trust = ?t])` applied to a `Message[Trust = Untrusted]` disagrees at
//! `Message`/`Text` under every instantiation of `?t`, and nobody downstream re-asked it.
//! The arg-unify loop's failure to bind `?t` is discarded, so `?t` reached the next call
//! still FREE — the maximally permissive value, because the consumer instantiates it to
//! whatever it wants. On `examples/guardians`, where `?t` is an information-flow label,
//! that consumer was `sink(body: Text[Trust = Public])` and the accepted program was an
//! exfiltration: the label was laundered, not merely unchecked.
//!
//! ## Which rows measure the fix
//!
//! MEASURED, with `nominal_head_mismatch` mutated to `return false` at its entry (which
//! neutralizes both of its call sites at once): **exactly the seven `refuses_` rows below
//! fail**, plus `guardians_test::a_wrong_sort_at_a_label_polymorphic_parameter_is_refused`
//! — and nothing else in the workspace, `wi836_type_var_arg_agreement_test` and
//! `wi453_hk_concrete_fill_test` included, both of which the first cut DID break and which
//! are therefore worth naming here.
//!
//! TWO of the seven measure a SECOND back-out — restoring the boundary conversions to
//! every recursion depth instead of the argument position (`HeadPosition`). They are the
//! last section of this file, each with a ground twin, and both were found by
//! `/code-review` after the workspace was green: the carve-out this ticket needed had
//! re-opened the ticket's own defect one level down.
//!
//! Every `control_` row passes either way BY DESIGN, and each pins a different accept the
//! fix must not take away: the variable propagating through a matching sort, a polymorphic
//! call at its own declared sort, a conforming callback, a ground callback mismatch that
//! was already refused, a callback RESULT that was never part of the hole, and the WI-408
//! some-coercion at an `Option` slot. Without them, five refusals are consistent with a
//! gate that refuses everything.
//!
//! Each row is its OWN namespace in its OWN load, so a back-out that breaks one cannot
//! take a control down with it.
//!
//! ## The one control that is NOT here, and why it is not
//!
//! `nominal_heads_compatible` asks its question through `types_compatible`, so a head
//! pairing that differs by SYMBOL and agrees by PROVIDER ADMISSIBILITY must still be
//! accepted — the property that makes the reuse load-bearing rather than decorative. That
//! is measured, and not by a row in this file: instrumenting the predicate and running the
//! whole corpus shows only two such pairings ever reach it — `Relation`/`Stream` (12
//! calls) and `WorkItemStore`/`Cell` (1) — and deleting the `sort_ref`↔`sort_ref` arm
//! WI-RKMD4 added to `types_compatible_view_structural` turns exactly eleven pre-existing
//! tests red: `wi737_floundered_relation_test` (7 rows),
//! `wi714_relation_reference_test::wi714_cross_sort_rule_body_subgoal`,
//! `wi730_boolean_condition_test::wi730_negation_over_an_unbound_column_flounders_loudly`,
//! `wi749_rule_ref_zero_arg_member_test::wi749_zero_arg_member_on_rule_ref_matches_let_bound`
//! and `wi1078_unbound_return_var_test::an_eliminated_projection_is_not_a_candidate`. A
//! rule reference IS a `Relation[T]` value (WI-714) and `Relation` provides `Stream`.
//!
//! TWO HAND-WRITTEN ATTEMPTS AT SUCH A ROW ARE RECORDED BECAUSE BOTH MEASURED NOTHING,
//! and the reasons are not obvious. `mk(n) -> List[T = ?e]` against `consume(s: Stream)`
//! never reaches the gate: `?e` appears only in the RETURN, which makes it existential
//! (WI-1078) and therefore rigid, and a rigid is DETERMINED (WI-1059), so the pair goes
//! down the ground path. A hand-built `person_row.isEmpty` mimicking those `Relation`
//! tests does not reach it either — verified by instrumenting the predicate, not by
//! reasoning. Both passed with the arm deleted, which is how they were caught. Reaching
//! this gate needs a FLEX variable the argument-unify loop failed to bind, which is what
//! every `refuses_` row below is built from.

use super::common::try_load_kb_with;

fn errors(src: &str) -> Vec<String> {
    match try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    }
}

/// `Trust`, `Text` and `Message` — two sorts carrying the SAME label parameter, which is
/// the whole point: a vocabulary of ONE sort cannot exercise a sort mismatch, and that is
/// why every probe written before this one was blind to the defect.
fn vocabulary(ns: &str) -> String {
    format!(
        "enum {ns}.Trust
  entity Untrusted
  entity Public
end
enum {ns}.Text
  import anthill.prelude.{{String}}
  sort Trust = ?
  entity text(raw: String)
end
enum {ns}.Message
  import anthill.prelude.{{String}}
  sort Trust = ?
  entity message(raw: String)
end
"
    )
}

fn program(ns: &str, body: &str) -> String {
    format!(
        "{}namespace {ns}
  import anthill.prelude.{{String, List, Unit, Option}}
  import {ns}.Trust.{{Untrusted, Public}}
  import {ns}.{{Text, Message}}
{body}
end
",
        vocabulary(ns)
    )
}

fn sole_error(src: &str) -> String {
    let errs = errors(src);
    assert_eq!(errs.len(), 1, "expected exactly one error, got: {errs:#?}");
    errs.into_iter().next().unwrap()
}

// ── the defect: a wrong sort against a variable-containing parameter ──────────

/// FLAT. `Message` where `Text[Trust = ?t]` is declared. FAILS ON BACK-OUT (loaded clean,
/// and the leak went through).
#[test]
fn refuses_a_wrong_sort_against_a_variable_containing_parameter() {
    let src = program(
        "nest4",
        "  operation fetch_one() -> Message[Trust = Untrusted]
  operation sum_flat(m: Text[Trust = ?t]) -> Text[Trust = ?t]
  operation sink(body: Text[Trust = Public]) -> Unit
  operation leak() -> Unit = sink(sum_flat(fetch_one()))",
    );
    let err = sole_error(&src);
    // Refused at the POLYMORPHIC call, not at the sink: the point is that `?t` never gets
    // to reach the sink free.
    assert!(
        err.contains("type mismatch in sum_flat.m (op-arg)")
            && err.contains("expected Text[Trust = ?")
            && err.contains("got Message[Trust = Untrusted]"),
        "{err}"
    );
}

/// CONTAINER, one level down. `List[T = Message[…]]` where `List[T = Text[Trust = ?t]]`
/// is declared — the heads agree at `List` and disagree beneath it, so a head-ONLY test
/// would call this program clean. FAILS ON BACK-OUT.
#[test]
fn refuses_a_wrong_element_sort_beneath_a_matching_container() {
    let src = program(
        "nest3",
        "  operation fetch_msgs() -> List[T = Message[Trust = Untrusted]]
  operation sum_list(msgs: List[T = Text[Trust = ?t]]) -> Text[Trust = ?t]
  operation sink(body: Text[Trust = Public]) -> Unit
  operation leak() -> Unit = sink(sum_list(fetch_msgs()))",
    );
    let err = sole_error(&src);
    assert!(
        err.contains("type mismatch in sum_list.msgs (op-arg)")
            && err.contains("got List[T = Message[Trust = Untrusted]]"),
        "{err}"
    );
}

// ── controls: green either way, and each pins a different accept ──────────────

/// NESTING IS NOT THE CAUSE — the variable is. Same container shape as the row above with
/// the element sort RIGHT: `?t` must still bind to `Untrusted` and PROPAGATE, so the one
/// refusal belongs to the SINK and the polymorphic call is untouched. Asserting the
/// error's SITE is what makes this a control rather than a bare "still refused": a fix
/// that over-refused would move the refusal to `sum_list.msgs` and this row would catch
/// it. Passes either way by design.
#[test]
fn control_a_matching_element_sort_still_propagates_and_the_sink_refuses() {
    let src = program(
        "nest2",
        "  operation fetch_texts() -> List[T = Text[Trust = Untrusted]]
  operation sum_list(msgs: List[T = Text[Trust = ?t]]) -> Text[Trust = ?t]
  operation sink(body: Text[Trust = Public]) -> Unit
  operation leak() -> Unit = sink(sum_list(fetch_texts()))",
    );
    let err = sole_error(&src);
    assert!(
        err.contains("type mismatch in sink.body (op-arg)")
            && err.contains("expected Text[Trust = Public]")
            && err.contains("got Text[Trust = Untrusted]"),
        "{err}"
    );
}

/// GROUND AGAINST GROUND was always checked — the pair that says this ticket is a narrow
/// claim about the variable and not "the typer does not check arguments". Passes either
/// way by design.
#[test]
fn control_ground_against_ground_was_already_refused() {
    let src = program(
        "gnd",
        "  operation fetch_one() -> Message[Trust = Untrusted]
  operation sink(body: Text[Trust = Public]) -> Unit
  operation leak() -> Unit = sink(fetch_one())",
    );
    let err = sole_error(&src);
    assert!(
        err.contains("type mismatch in sink.body (op-arg)")
            && err.contains("got Message[Trust = Untrusted]"),
        "{err}"
    );
}

/// THE POLYMORPHIC CALL ITSELF STILL LOADS. The right sort with a free label: `?t` binds
/// to `Untrusted`, the result carries it, and the matching sink takes it. This is the
/// over-refusal arm — the fix must add refusals only where the HEADS disagree, never at a
/// conforming variable position. Passes either way by design; RED if the new gate ever
/// read a free slot as a disagreement.
#[test]
fn control_a_conforming_polymorphic_call_still_loads_clean() {
    let src = program(
        "okpoly",
        "  operation fetch_text() -> Text[Trust = Untrusted]
  operation sum_flat(m: Text[Trust = ?t]) -> Text[Trust = ?t]
  operation audit(body: Text[Trust = Untrusted]) -> Unit
  operation ok() -> Unit = audit(sum_flat(fetch_text()))",
    );
    assert!(errors(&src).is_empty(), "{:#?}", errors(&src));
}

// ── the same defect one coordinate over: a CALLBACK PARAMETER ────────────────
//
// `validate_arrow_param_result` carries WI-385's groundness gate per COMPONENT, and it
// skipped a callback parameter still carrying a variable for exactly the reason the
// top-level gate did. Both `refuses_` rows below FAIL ON BACK-OUT of that second call;
// both `control_` rows pass either way.
//
// TWO RESIDUALS, stated rather than left to be discovered. (1) A pairing where one side
// is a `Function[A, B, E]` and the other an arrow states no agreed arity, so `A` admits
// two readings (whole-argument vs spread) and a head disagreement is not decidable — that
// arm is untouched. (2) A `Function` HEAD is withheld wherever the walk meets one, on
// WI-836's measurement; `wi836…::a_callback_slot_nested_in_a_sort_application_still_withholds`
// is the program that pins why, and it is refused without the withholding. Note the
// withholding is per NODE, not per type: a first cut dropped the whole check whenever a
// callable appeared ANYWHERE in either side, which is an exclusion wider than WI-836's
// evidence — that ticket is about a callable being COMPARED.

/// One callback arrow per row: `cb` is the value, `run`'s `f` is the slot.
fn callback_program(ns: &str, cb_param: &str, slot_param: &str) -> String {
    format!(
        "{}namespace {ns}
  import anthill.prelude.{{String, Int64}}
  import {ns}.Trust.{{Untrusted, Public}}
  import {ns}.{{Text, Message}}
  operation cb({cb_param}) -> Int64 = 1
  operation run(f: ({slot_param}) -> Int64) -> Int64 = 2
  operation go() -> Int64 = run(cb)
end
",
        vocabulary(ns)
    )
}

/// The variable on the VALUE's side: a `Text[Trust = ?t]` callback handed to a slot that
/// declares `Message[Trust = Untrusted]`. FAILS ON BACK-OUT.
#[test]
fn refuses_a_wrong_sort_in_a_callback_parameter() {
    let err = sole_error(&callback_program(
        "cbap",
        "t: Text[Trust = ?t]",
        "m: Message[Trust = Untrusted]",
    ));
    assert!(
        err.contains("type mismatch in run.f (op-arg)")
            && err.contains("expected Message[Trust = Untrusted] -> Int64")
            && err.contains("got Text[Trust = ?"),
        "{err}"
    );
}

/// The variable on the SLOT's side — the mirror, and it needs its own row because the
/// parameter position is contravariant, so the two are not one program written twice.
/// FAILS ON BACK-OUT.
#[test]
fn refuses_a_wrong_sort_at_a_variable_bearing_callback_slot() {
    let err = sole_error(&callback_program(
        "cbbp",
        "t: Message[Trust = Untrusted]",
        "m: Text[Trust = ?t]",
    ));
    assert!(
        err.contains("type mismatch in run.f (op-arg)")
            && err.contains("got Message[Trust = Untrusted] -> Int64"),
        "{err}"
    );
}

/// GROUND AGAINST GROUND at the same position was always refused — the pair that says the
/// two rows above are about the variable and not about callbacks. Passes either way.
#[test]
fn control_a_ground_callback_parameter_mismatch_was_already_refused() {
    let err = sole_error(&callback_program(
        "cbdp",
        "t: Text[Trust = Public]",
        "m: Message[Trust = Untrusted]",
    ));
    assert!(
        err.contains("type mismatch in run.f (op-arg)")
            && err.contains("got Text[Trust = Public] -> Int64"),
        "{err}"
    );
}

/// AND A MATCHING CALLBACK STILL LOADS — the over-refusal arm for the callback
/// coordinate. Passes either way; RED if the new component check refused a conforming
/// pair. Without it the three rows above would be consistent with a gate that refuses
/// every callback.
#[test]
fn control_a_matching_callback_parameter_still_loads_clean() {
    let src = callback_program(
        "cbep",
        "t: Message[Trust = Untrusted]",
        "m: Message[Trust = Untrusted]",
    );
    assert!(errors(&src).is_empty(), "{:#?}", errors(&src));
}

/// THE CALLBACK RESULT WAS NEVER PART OF THE HOLE, and this row is here to keep that
/// true rather than to credit the fix: a `-> Text[Trust = ?t]` callback at a slot
/// declaring `-> Message[Trust = Untrusted]` is refused with the component gate
/// untouched, so nothing was added there. Passes either way by design; it turns RED if
/// whatever route currently decides it stops doing so.
#[test]
fn control_a_variable_bearing_callback_result_was_already_refused() {
    let src = format!(
        "{}namespace cbcp
  import anthill.prelude.{{String, Int64}}
  import cbcp.Trust.{{Untrusted, Public}}
  import cbcp.{{Text, Message}}
  operation cb(n: Int64) -> Text[Trust = ?t] = text(raw: \"x\")
  operation run(f: (n: Int64) -> Message[Trust = Untrusted]) -> Int64 = 2
  operation go() -> Int64 = run(cb)
end
",
        vocabulary("cbcp")
    );
    let err = sole_error(&src);
    assert!(
        err.contains("type mismatch in run.f (op-arg)") && err.contains("got Int64 -> Text[Trust = ?"),
        "{err}"
    );
}

// ── the `Option` boundary: withheld at the HEAD, not below it ────────────────

/// A wrong element sort beneath a shared `Option` head. The WI-408 some-coercion owns a
/// head disagreement at an `Option` slot — a bare `T` there is a coercion, not a mismatch
/// — but two `Option`s agree at their head, so the element is judged like any other
/// container's. FAILS ON BACK-OUT (and would also fail against a first cut that withheld
/// the whole check whenever the declared type was an `Option`).
#[test]
fn refuses_a_wrong_element_sort_beneath_a_shared_option() {
    let src = program(
        "optel",
        "  operation fetch_opt() -> Option[T = Message[Trust = Untrusted]]
  operation sum_opt(m: Option[T = Text[Trust = ?t]]) -> Text[Trust = ?t]
  operation sink(body: Text[Trust = Public]) -> Unit
  operation leak() -> Unit = sink(sum_opt(fetch_opt()))",
    );
    let err = sole_error(&src);
    assert!(
        err.contains("type mismatch in sum_opt.m (op-arg)")
            && err.contains("got Option[T = Message[Trust = Untrusted]]"),
        "{err}"
    );
}

/// AND THE COERCION IS UNTOUCHED: a bare `Text` at an `Option`-declared slot whose element
/// still carries the variable is a head disagreement the some-coercion owns, so it is not
/// reported here. Passes either way by design — RED if the head verdict were taken at an
/// `Option` slot.
#[test]
fn control_a_bare_value_at_an_option_slot_is_left_to_the_some_coercion() {
    let src = program(
        "optco",
        "  operation fetch_text() -> Text[Trust = Untrusted]
  operation sum_opt(m: Option[T = Text[Trust = ?t]]) -> Text[Trust = ?t]
  operation audit(body: Text[Trust = Untrusted]) -> Unit
  operation ok() -> Unit = audit(sum_opt(fetch_text()))",
    );
    assert!(errors(&src).is_empty(), "{:#?}", errors(&src));
}

// ── the boundary conversions are the ARGUMENT position's, not every depth's ───
//
// Both rows below were found by `/code-review`, and both are the ticket's own defect
// re-opened by its own carve-out. `Option` and reflect-`Term` are withheld because the
// GROUND path accepts them instead of comparing — the WI-408 some-coercion is inserted by
// `check_apply_iter` around the ARGUMENT OCCURRENCE, and reflect-`Term` takes any value at
// an argument slot. Neither rewrite exists for a nested binding or a callback component,
// so honouring them deeper withholds a verdict nobody else reaches. `HeadPosition` is what
// keeps the two apart, and it is an enum rather than a second bool precisely so that
// "outer" and "directed" cannot drift out of step.
//
// Each row carries its GROUND TWIN, and the twins are what make these rows about the
// withholding rather than about `Option`: both twins are refused with the fix backed out.

/// NESTED. `Message` against a declared `Option[…]` ONE LEVEL DOWN, beneath a `List` the
/// two sides agree on. FAILS ON BACK-OUT of the `HeadPosition::Argument` guard — it loaded
/// clean and laundered `?t` to `Public` at the sink.
#[test]
fn refuses_a_wrong_sort_against_a_nested_option_slot() {
    let src = program(
        "optnest",
        "  operation fetch() -> List[T = Message[Trust = Untrusted]]
  operation take(xs: List[T = Option[T = Text[Trust = ?t]]]) -> Text[Trust = ?t]
  operation sink(body: Text[Trust = Public]) -> Unit
  operation leak() -> Unit = sink(take(fetch()))",
    );
    let err = sole_error(&src);
    assert!(
        err.contains("type mismatch in take.xs (op-arg)")
            && err.contains("got List[T = Message[Trust = Untrusted]]"),
        "{err}"
    );
}

/// GROUND TWIN of the row above — the same program with the label written out. Refused
/// either way, which is what says the row above measures the WITHHOLDING and not
/// `Option`.
#[test]
fn control_the_nested_option_slot_was_already_refused_when_ground() {
    let src = program(
        "optnestg",
        "  operation fetch() -> List[T = Message[Trust = Untrusted]]
  operation take(xs: List[T = Option[T = Text[Trust = Untrusted]]]) -> Text[Trust = Untrusted]
  operation sink(body: Text[Trust = Public]) -> Unit
  operation leak() -> Unit = sink(take(fetch()))",
    );
    let err = sole_error(&src);
    assert!(err.contains("type mismatch in take.xs (op-arg)"), "{err}");
}

/// A CALLBACK COMPONENT, with the `Option` on the VALUE's side. The arrow site hands the
/// pair over SLOT-first (the position is contravariant), so an `Option` guard reading the
/// `declared` argument reads the callback's own parameter — and withheld the verdict for
/// the wrong side. FAILS ON BACK-OUT; the mirror (`Option` on the slot's side) was refused
/// before and is covered by `refuses_a_wrong_sort_at_a_variable_bearing_callback_slot`.
#[test]
fn refuses_a_wrong_sort_at_a_callback_whose_own_parameter_is_an_option() {
    let src = format!(
        "{}namespace cbopt
  import anthill.prelude.{{String, Int64, Option}}
  import cbopt.Trust.{{Untrusted, Public}}
  import cbopt.{{Text, Message}}
  operation cb(t: Option[T = Text[Trust = ?t]]) -> Int64 = 1
  operation run(f: (m: Message[Trust = Untrusted]) -> Int64) -> Int64 = 2
  operation go() -> Int64 = run(cb)
end
",
        vocabulary("cbopt")
    );
    let err = sole_error(&src);
    assert!(
        err.contains("type mismatch in run.f (op-arg)")
            && err.contains("got Option[T = Text[Trust = ?"),
        "{err}"
    );
}

/// GROUND TWIN of the row above. Refused either way.
#[test]
fn control_the_callback_option_parameter_was_already_refused_when_ground() {
    let src = format!(
        "{}namespace cboptg
  import anthill.prelude.{{String, Int64, Option}}
  import cboptg.Trust.{{Untrusted, Public}}
  import cboptg.{{Text, Message}}
  operation cb(t: Option[T = Text[Trust = Public]]) -> Int64 = 1
  operation run(f: (m: Message[Trust = Untrusted]) -> Int64) -> Int64 = 2
  operation go() -> Int64 = run(cb)
end
",
        vocabulary("cboptg")
    );
    let err = sole_error(&src);
    assert!(err.contains("type mismatch in run.f (op-arg)"), "{err}");
}
