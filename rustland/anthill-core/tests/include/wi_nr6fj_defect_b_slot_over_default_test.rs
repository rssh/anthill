//! WI-20260917-NR6FJ DEFECT B — A DEFAULTED SPEC OP CALLED INSIDE AN OPERATION THAT DECLARED
//! `requires Spec[T = C]` READS THE SLOT; it no longer folds the spec's own default.
//!
//! A `requires` is an IMPLICIT PARAMETER — "the A dictionary is PASSED IN, an inbound
//! slot the caller fills" (`SupplySource`'s own words). The author of
//!
//! ```text
//! operation viaop() -> Int64 requires Desc[T = Rich] = Desc.tag()
//! ```
//!
//! has said which `Desc` dictionary is in scope. Before this, `Desc.tag()` ignored it
//! and ran `Desc`'s own `= 1`.
//!
//! ## The measurement that made this a defect and not a policy
//!
//! Same program, same declaration, and the ONLY difference between the two rows is
//! whether the spec's operation happens to carry a default body:
//!
//! | `Desc.tag`                     | before | after |
//! |--------------------------------|--------|-------|
//! | `operation tag() -> Int64`     | 7 ✓    | 7     |
//! | `operation tag() -> Int64 = 1` | **1**  | **7** |
//!
//! So adding a default to a spec silently changed a caller's answer from 7 to 1 — and
//! the caller cannot see the thing that decided it. That contradicts the rule the
//! codebase already states at [`spec_op_parent_sort`]: *"defaults fill gaps, they do not
//! shadow"*. `Rich` writes its own `tag`; nothing should have shadowed it.
//!
//! ## Where it was
//!
//! `lookup_spec_op_dispatch` is body-less-only, so a defaulted op never reaches the
//! WI-210 dispatch block; the WI-444 defaulted block above it pins the carrier's
//! override, but only from a SELF-RECEIVER or a CARRIER-PARAM argument. A NULLARY op has
//! neither, so nothing pinned and the default ran. `carrier_from_declared_slot` adds the
//! declared slot as a third carrier source, consulted only when those two are silent.
//!
//! ## Back-out
//!
//! Drop the `.or_else(carrier_from_declared_slot)` and THREE rows fail, each by
//! answering the spec's `1`: the two acceptances and
//! `a_parameterized_carrier_in_the_slot_dispatches_to_its_own_member`. The other FOUR
//! pass either way BY DESIGN and say so at their sites (one of them,
//! `an_abstract_argument_still_dispatches_on_the_runtime_value`, is the control on the
//! change's GATE rather than on its feature, and fails only when that gate is removed) — they exist because the obvious
//! over-fire (route every defaulted call whose enclosing chain merely NAMES the spec
//! into dispatch) was BUILT and MEASURED, and it broke three shipped rows where the
//! default is the right answer. See `a_type_variable_slot_now_reaches_the_provider_too`
//! for which three and why a static reroute is the wrong instrument.
//!
//! Full workspace with the change in: 7114 passed, 0 failed — 7105 before, and the NINE
//! that moved are this file's own rows. Zero corpus rows changed their verdict.
//!
//! ## THE RESIDUE IS CLOSED — WI-20260919-H20YY
//!
//! This ticket closed the half where the declared slot names a CONCRETE carrier and left
//! the TYPE-PARAMETER half open, pinned by `a_type_variable_slot_now_reaches_the_
//! provider_too` (then named `..._is_unchanged_and_still_disagrees`). H20YY closed that
//! half with the instrument this file's own prose named — a DEFERRAL at the call rather
//! than a static reroute — so that row is now a positive and every cell of the table
//! above reads 7. A slot over a type parameter has no carrier to pin; it has a
//! dictionary, and the call is classified to walk it.

use anthill_core::eval::Value;

/// `Rich` overrides `tag` with 7, `Other` with 9. `Bare` provides but overrides NOTHING,
/// so it is only legal beside a DEFAULTED spec op — with a body-less one the loader
/// refuses it outright (*"provides `Desc` but backs no operation `Desc.tag`"*), which is
/// why it rides in `extra` rather than in the fixture body.
fn fixture_with(ns: &str, spec_op: &str, extra: &str, tail: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
{spec_op}  end

  sort Rich
    import anthill.prelude.Int64
    entity rich
    provides Desc[T = Rich]
    operation tag() -> Int64 = 7
  end

  sort Other
    import anthill.prelude.Int64
    entity other
    provides Desc[T = Other]
    operation tag() -> Int64 = 9
  end

{extra}
{tail}end
"#
    )
}

const DEFAULTED: &str = "    operation tag() -> Int64 = 1\n";
const BODY_LESS: &str = "    operation tag() -> Int64\n";

/// The override-less carrier, legal only beside [`DEFAULTED`] — see [`fixture_with`].
const BARE: &str = "  sort Bare\n    entity bare\n    provides Desc[T = Bare]\n  end\n";

/// The fixture as every row but the `Bare` one wants it.
fn fixture(ns: &str, spec_op: &str, tail: &str) -> String {
    fixture_with(ns, spec_op, "", tail)
}

fn answer(ns: &str, spec_op: &str, tail: &str) -> Option<i64> {
    let mut kb = crate::common::load_kb_with(&fixture(ns, spec_op, tail));
    match crate::common::query_unary(&mut kb, &format!("{ns}.answer")).as_slice() {
        [(Value::Int(i), true)] => Some(*i),
        other => panic!("expected one integer answer, got {other:?}"),
    }
}

/// The call under test, parameterised by what the operation declares.
fn via(requires: &str) -> String {
    format!(
        "  operation viaop() -> Int64 {requires}= Desc.tag()\n  \
         rule answer(?r) :- viaop(?r)\n"
    )
}

/// THE ACCEPTANCE — the declared slot decides, and the carrier's own `tag` answers.
///
/// FAILS WITH THE CHANGE BACKED OUT by answering `1`: the author's
/// `requires Desc[T = Rich]` ignored and `Desc`'s own `= 1` folded in its place, while
/// `Rich`'s written `= 7` — an implementation the program contains — never runs.
#[test]
fn a_defaulted_spec_op_reads_the_declared_slot() {
    assert_eq!(
        answer("test.defb.acc", DEFAULTED, &via("requires Desc[T = Rich] ")),
        Some(7),
    );
}

/// THE DISCRIMINATOR — the two spellings of the SAME spec now agree.
///
/// This is the row that states the defect rather than an instance of it: the two
/// programs differ in exactly one character sequence, `= 1` on the spec's declaration,
/// which is invisible to the caller and used to decide its answer.
///
/// FAILS WITH THE CHANGE BACKED OUT on the `DEFAULTED` half only; the `BODY_LESS` half
/// passed before and still does, which is what pins the disagreement as the defect.
#[test]
fn both_spellings_of_the_spec_now_answer_the_same() {
    let defaulted = answer("test.defb.d", DEFAULTED, &via("requires Desc[T = Rich] "));
    let body_less = answer("test.defb.b", BODY_LESS, &via("requires Desc[T = Rich] "));
    assert_eq!(
        (defaulted, body_less),
        (Some(7), Some(7)),
        "whether the spec's op carries a default body must not change what the CALLER \
         gets; it is not something the caller can see",
    );
}

/// CONTROL — NO SLOT, NO CHANGE: the default still runs.
///
/// PASSES EITHER WAY BY DESIGN. It is what says the change keys on the DECLARATION and
/// not on the presence of a provider: nobody demanded `Desc` here, so the spec's own
/// fallback is the right answer and the widening must not reach it.
#[test]
fn with_no_slot_declared_the_default_still_runs() {
    assert_eq!(answer("test.defb.nos", DEFAULTED, &via("")), Some(1));
}

/// CONTROL — DEFAULTS FILL GAPS. A carrier that PROVIDES the spec but writes no `tag`
/// of its own still gets the spec's default.
///
/// PASSES EITHER WAY BY DESIGN, and it is the other half of the rule the acceptance
/// enforces: reading the slot means "use the carrier's implementation if it has one",
/// not "never use the default". Without this row the acceptance would be satisfied by a
/// change that refused or mis-dispatched every defaulted call with a slot.
#[test]
fn a_providing_carrier_with_no_override_still_takes_the_default() {
    let mut kb = crate::common::load_kb_with(&fixture_with(
        "test.defb.bare",
        DEFAULTED,
        BARE,
        &via("requires Desc[T = Bare] "),
    ));
    assert!(
        matches!(
            crate::common::query_unary(&mut kb, "test.defb.bare.answer").as_slice(),
            [(Value::Int(1), true)]
        ),
        "`Bare` provides `Desc` and writes no `tag`; the spec's default is exactly what \
         fills that gap",
    );
}

/// CONTROL — AN ARGUMENT THAT PINS THE CARRIER STILL WINS over the declared slot.
///
/// `describe(x: T)` called at a `Plain` inside an operation whose slot names `Rich`
/// answers `Plain`'s `3`, not `Rich`'s `7`: the value being described is the carrier.
///
/// PASSES EITHER WAY BY DESIGN — before the change the argument pinned it and the slot
/// was never consulted; after, the slot is an `.or_else` BEHIND the argument. This row
/// is what makes that ordering a decision rather than an accident, and it fails against
/// the same change written with the two sources swapped.
#[test]
fn an_argument_pinned_carrier_outranks_the_declared_slot() {
    let src = r#"namespace test.defb.arg
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Plain
    import anthill.prelude.Int64
    entity plain
    provides Desc[T = Plain]
    operation describe(x: Plain) -> Int64 = 3
  end

  sort Rich
    import anthill.prelude.Int64
    entity rich
    provides Desc[T = Rich]
    operation describe(x: Rich) -> Int64 = 7
  end

  operation viaop(x: Plain) -> Int64 requires Desc[T = Rich] = Desc.describe(x)
  rule answer(?r) :- viaop(plain(), ?r)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert!(
        matches!(
            crate::common::query_unary(&mut kb, "test.defb.arg.answer").as_slice(),
            [(Value::Int(3), true)]
        ),
        "the ARGUMENT names the carrier here; the slot speaks only where the arguments \
         are silent",
    );
}

/// CONTROL — TWO SLOTS THAT DISAGREE PIN NOTHING, and the default runs as before.
///
/// PASSES EITHER WAY BY DESIGN, and it is here to refuse one specific shortcut: taking
/// the FIRST matching entry of the chain. That would make the answer depend on the order
/// two `requires` were written — the silent route-order choice WI-1010's family of
/// refusals exists to prevent. No corpus program writes two such slots, so this row is
/// the only thing holding the behaviour.
#[test]
fn two_slots_that_disagree_pin_nothing() {
    assert_eq!(
        answer(
            "test.defb.two",
            DEFAULTED,
            &via("requires Desc[T = Rich], Desc[T = Other] "),
        ),
        Some(1),
    );
}

/// A PARAMETERIZED CARRIER IN THE SLOT dispatches to the carrier's own `tag`.
///
/// `requires Desc[T = Box[E = Int64]]` answers `Box`'s `5`, not the spec's `1`.
///
/// PASSES EITHER WAY? NO — it FAILS WITH THE CHANGE BACKED OUT, by answering `1`. It is
/// listed among the controls because what it CONTROLS is a construction choice, not the
/// defect: `carrier_from_declared_slot` hands back a [`GoalCarrier::bare`], which drops
/// the carrier's type ARGUMENTS (`E = Int64`) and keeps only the base `Box`. That is the
/// documented shape for "a carrier whose arguments this route cannot see", and this row
/// is the measurement that it is harmless here rather than an assumption that it is: a
/// NULLARY spec op has no argument position for the element to reach, so the join
/// `carrier_arg_impl_subst` would make has nothing to do. Should this function ever be
/// widened to a call that DOES take the carrier's elements, that reasoning expires and
/// this row is where a reader will look for it.
#[test]
fn a_parameterized_carrier_in_the_slot_dispatches_to_its_own_member() {
    let src = r#"namespace test.defb.param
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation tag() -> Int64 = 1
  end

  sort Box
    import anthill.prelude.Int64
    sort E = ?
    entity boxed(v: E)
    provides Desc[T = Box]
    operation tag() -> Int64 = 5
  end

  operation viaop() -> Int64 requires Desc[T = Box[E = Int64]] = Desc.tag()
  rule answer(?r) :- viaop(?r)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert!(
        matches!(
            crate::common::query_unary(&mut kb, "test.defb.param.answer").as_slice(),
            [(Value::Int(5), true)]
        ),
        "the slot names `Box` at an instantiation; the base is what dispatches",
    );
}

/// AN ABSTRACT ARGUMENT STILL DISPATCHES ON THE RUNTIME VALUE — the row that caught a
/// regression this ticket had already written.
///
/// `operation viaop[U](x: U) -> Int64 requires Desc[T = Rich] = Desc.describe(x)` called
/// at `plain()` answers `Plain`'s `3`. `Desc.describe(x: T)` HAS a carrier parameter; it
/// is merely abstract at this call, so the carrier is eval's to read off the runtime
/// value and no static guess may pre-empt it.
///
/// THE FIRST CUT OF THE CHANGE ANSWERED 7 HERE — `Rich`'s `describe` run on a `plain()`
/// value — because it consulted the slot whenever `statically_pinned_carrier` returned
/// `None`, without distinguishing "this call names no carrier" from "this call's carrier
/// is not yet known". Those are not the same thing, and the second belongs to eval.
/// `carrier_from_declared_slot` now asks the DECLARATION (does the spec op declare a
/// carrier-typed parameter at all) rather than the call-site classification, which is
/// `None` for both.
///
/// FAILS WITH THAT GATE REMOVED, by answering 7, which makes it the control on the gate
/// rather than on the feature; it passes both with the whole change backed out and with
/// the finished change in.
#[test]
fn an_abstract_argument_still_dispatches_on_the_runtime_value() {
    let src = r#"namespace test.defb.abs
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Plain
    import anthill.prelude.Int64
    entity plain
    provides Desc[T = Plain]
    operation describe(x: Plain) -> Int64 = 3
  end

  sort Rich
    import anthill.prelude.Int64
    entity rich
    provides Desc[T = Rich]
    operation describe(x: Rich) -> Int64 = 7
  end

  operation viaop[U](x: U) -> Int64 requires Desc[T = Rich] = Desc.describe(x)
  rule answer(?r) :- viaop(plain(), ?r)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert!(
        matches!(
            crate::common::query_unary(&mut kb, "test.defb.abs.answer").as_slice(),
            [(Value::Int(3), true)]
        ),
        "the value being described is a `Plain`; a slot naming `Rich` must not decide \
         a dispatch the runtime value owns",
    );
}

/// THE RESIDUE, NOW CLOSED — WI-20260919-H20YY. A slot over a TYPE PARAMETER reaches the
/// provider too, and the two spellings finally agree at every shape.
///
/// `operation viaop[U](x: U) -> Int64 requires Desc[T = U] = Desc.tag()` called at a
/// `Rich`. This row asserted `(1, 7)` — the DEFAULTED spelling folding to the spec's own
/// default while the BODY-LESS one dispatched — and was written so that closing the
/// residue would FAIL IT. This is that failure, taken as the flip it was built to be.
///
/// WHY NR6FJ COULD NOT CLOSE IT, and what changed. Its instrument was a CARRIER:
/// `carrier_from_declared_slot` admits only a sort-like binding, and over `Desc[T = U]`
/// there is no carrier to name — which provider `U` stands for is settled per call. This
/// row's own doc drew the right conclusion at the time: *"with no concrete carrier the
/// dispatch belongs at the call, where the frame holds the dictionary"*. H20YY is that,
/// and the ROUTE is what makes it safe — the call is classified
/// `CallClass::DeferToRequirement`, exactly as a body-less op's is, so eval walks the
/// slot's dictionary and `resolve_op_target` yields the provider's override when it has
/// one and the SPEC OP ITSELF when it does not.
///
/// THAT LAST CLAUSE IS WHY THE REJECTED FIX'S THREE CASUALTIES SURVIVE. The instrument
/// rejected here was a static reroute of every defaulted call whose chain merely NAMES
/// the spec into the WI-210 dispatch block, which broke three shipped rows where the
/// default is the right answer: `wi886_cpp_mapping_language_test::
/// eval_runs_the_spec_default_when_the_only_implementation_is_cpp`,
/// `wi876_operation_mapping_test::the_whole_comparison_surface_works_from_one_operation`
/// and `wi869_per_provision_conditions_test::
/// the_inherited_comparison_surface_works_from_compare_alone`. A deferral does not
/// reroute anything: a provider with no override still runs the default, through the
/// same dictionary. All three are green, and
/// [`a_providing_carrier_with_no_override_still_takes_the_default`] is this file's own
/// row for that rule.
///
/// BACK-OUT: make `defer_defaulted_call_to_slot` return `false` at entry and this
/// returns to `(1, 7)`, the state it pinned before.
#[test]
fn a_type_variable_slot_now_reaches_the_provider_too() {
    let tv = "  operation viaop[U](x: U) -> Int64 requires Desc[T = U] = Desc.tag()\n  \
              rule answer(?r) :- viaop(rich(), ?r)\n";
    assert_eq!(
        (
            answer("test.defb.tvd", DEFAULTED, tv),
            answer("test.defb.tvb", BODY_LESS, tv),
        ),
        (Some(7), Some(7)),
        "a slot over a type parameter must reach the provider in BOTH spellings — \
         WI-20260919-H20YY closed the residue this row was built to pin",
    );
}
