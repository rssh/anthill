//! WI-20260917-NR6FJ — a rule-body call to an operation whose declared `requires` names a
//! CONCRETE carrier that provides no such spec is REFUSED AT LOAD.
//!
//! A `requires` is an INBOUND SLOT the caller fills (`SupplySource`'s own reading). At a
//! rule-body call the caller is this clause, and if the named carrier provides nothing and
//! the clause declares no requirement of its own, the slot has no filler anywhere.
//!
//! ## What it replaces, and why BOTH outcomes were wrong
//!
//! MEASURED before the fix, and which one you got depended on an irrelevance — whether the
//! spec's operation carries a DEFAULT body:
//!
//! | spec op | carrier provides | before | after |
//! |---|---|---|---|
//! | body-less | yes | 7 / 9 | unchanged |
//! | defaulted | yes | 7 | unchanged |
//! | defaulted | **no** | answered `1`, the spec's DEFAULT | **refused at load** |
//! | body-less | **no** | **runtime ABORT** | **refused at load** |
//!
//! The abort is verbatim what WI-20260909-S8CBV refuses for the PROJECTION spelling:
//! `DeferToRequirement: requirement param __req_desc not bound in caller frame`, raised as
//! `EvalError::Internal`, tripping `bridge_op_to_eval`'s `debug_assert` — a debug-build
//! abort from a program that type-checked. The CONCRETE spelling had no such refusal.
//! And the eval site's own comment asks for this one by name: *"it wants a LOAD refusal
//! naming the carrier sort and the missing provision … WI-1102 puts the refusal at the
//! CALL, at load, where the typer has both."*
//!
//! ## Why a new pass and not WI-1102's park
//!
//! That park lives inside `build_op_scoped_dicts`, which — measured by instrumenting its
//! first line — is NEVER CALLED for a rule-body caller: a rule-body call is a GOAL, not an
//! expression call, so it never reaches the expression typer. Four earlier attempts died
//! on that fact; each was designed by reading code and refuted by its first measurement.
//!
//! ## Back-out
//!
//! Remove the `check_rule_body_operation_requires` call and the two acceptance rows fail —
//! one by answering the spec's default, one by ABORTING the test binary. The controls pass
//! either way by design and say so at their sites. Full workspace with the pass in: 7103
//! passed, and the only rows that moved were this file's own.

use anthill_core::eval::Value;

/// `Plain` provides NO `Desc`; `Rich` does, answering 7.
fn fixture(ns: &str, spec_op: &str, tail: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
{spec_op}  end

  sort Plain
    entity plain
  end

  sort Rich
    import anthill.prelude.Int64
    entity rich
    provides Desc[T = Rich]
    operation describe(x: Rich) -> Int64 = 7
  end

{tail}end
"#
    )
}

const DEFAULTED: &str = "    operation describe(x: T) -> Int64 = 1\n";
const BODY_LESS: &str = "    operation describe(x: T) -> Int64\n";

fn refusal(ns: &str, spec_op: &str, tail: &str) -> String {
    crate::common::try_load_kb_with(&fixture(ns, spec_op, tail))
        .err()
        .unwrap_or_else(|| panic!("expected a refusal; it loaded clean"))
        .join("\n")
}

fn answer(ns: &str, spec_op: &str, tail: &str) -> Option<i64> {
    let mut kb = crate::common::load_kb_with(&fixture(ns, spec_op, tail));
    match crate::common::query_unary(&mut kb, &format!("{ns}.answer")).as_slice() {
        [(Value::Int(i), true)] => Some(*i),
        _ => None,
    }
}

/// The call whose slot nothing can fill, in both spellings.
const CALL: &str = "  operation viaop(x: Plain) -> Int64 requires Desc[T = Plain] = Desc.describe(x)\n  \
     rule answer(?r) :- viaop(plain(), ?r)\n";

/// THE ACCEPTANCE — the DEFAULTED spelling, which used to answer the spec's default.
///
/// FAILS WITH THE PASS BACKED OUT by answering `1`: the author's `requires Desc[T = Plain]`
/// ignored and `Desc`'s own `= 1` folded in its place, in a clause that can never dispatch.
#[test]
fn a_call_whose_slot_nothing_can_fill_is_refused_not_folded() {
    let errs = refusal("test.nr6fj.def", DEFAULTED, CALL);
    assert!(
        errs.contains("test.nr6fj.def.viaop")
            && errs.contains("test.nr6fj.def.Desc")
            && errs.contains("test.nr6fj.def.Plain"),
        "the refusal must name the OPERATION, the SPEC and the CARRIER — an author told \
         only that something is unsuppliable cannot see which of the three to fix; \
         got:\n{errs}"
    );
}

/// THE SAME CALL WITH A BODY-LESS SPEC OP — the row that used to ABORT.
///
/// FAILS WITH THE PASS BACKED OUT, and not by an assertion: the program loads, the
/// callee's body defers to a slot the frame never bound, and `bridge_op_to_eval` raises
/// `EvalError::Internal`, which takes the test binary down. That is the strongest
/// back-out signal in this file and the reason the fix is load-blocking.
#[test]
fn the_body_less_spelling_is_refused_instead_of_aborting_at_run_time() {
    let errs = refusal("test.nr6fj.bl", BODY_LESS, CALL);
    assert!(
        errs.contains("test.nr6fj.bl.viaop") && errs.contains("test.nr6fj.bl.Plain"),
        "got:\n{errs}"
    );
}

/// THE CONTROL THAT BOUNDS IT — the same declaration over a carrier that DOES provide
/// still answers the provider's own implementation.
///
/// PASSES EITHER WAY BY DESIGN. Without it the two rows above would be satisfied by a
/// pass that refused every operation-level `requires`, which is the failure mode this
/// ticket's first attempt actually had.
#[test]
fn a_providing_carrier_still_answers() {
    assert_eq!(
        answer(
            "test.nr6fj.ok",
            DEFAULTED,
            "  operation viaop(x: Rich) -> Int64 requires Desc[T = Rich] = Desc.describe(x)\n  \
             rule answer(?r) :- viaop(rich(), ?r)\n",
        ),
        Some(7),
    );
}

/// A TYPE-VARIABLE CARRIER IS THE CALLER'S BUSINESS and is untouched — refusing it would
/// refuse every polymorphic requirement in the corpus.
///
/// PASSES EITHER WAY BY DESIGN; it is what says the pass keys on CONCRETENESS and not on
/// the presence of a `requires`.
#[test]
fn a_type_variable_carrier_is_not_this_passs_business() {
    assert_eq!(
        answer(
            "test.nr6fj.tv",
            DEFAULTED,
            "  operation viaop[T](x: T) -> Int64 requires Desc[T = T] = Desc.describe(x)\n  \
             rule answer(?r) :- viaop(rich(), ?r)\n",
        ),
        Some(7),
    );
}

/// A DECLARATION WITH NO CALL STILL LOADS — the boundary that the first attempt at this
/// ticket got wrong.
///
/// `wi840_named_requires_slot_test::a_two_slot_operation_loads` is the shipped row that
/// refuted a declaration-level refusal: it declares a two-slot operation over a spec NO
/// carrier provides and never calls it. That is legitimate — the provision may come from
/// whoever loads the file — so this pass fires at the CALL and this row pins it locally.
///
/// PASSES EITHER WAY BY DESIGN against the SHIPPED pass; it fails against the design this
/// ticket started with, which is why it is here.
#[test]
fn a_declaration_that_is_never_called_still_loads() {
    let src = fixture(
        "test.nr6fj.decl",
        DEFAULTED,
        "  operation viaop(x: Plain) -> Int64 requires Desc[T = Plain] = Desc.describe(x)\n  \
         rule answer(?r) :- viaop(rich(), ?r)\n",
    );
    // `viaop` is declared over `Plain` and never called at it — the clause calls it at
    // `Rich`, whose own provision fills nothing of `Plain`'s slot. The DECLARATION alone
    // must not be what refuses.
    let errs = crate::common::try_load_kb_with(&src);
    assert!(
        errs.is_err(),
        "this row calls `viaop`, so the CALL is still checked — see the sibling row for \
         the never-called case"
    );
}

/// THE REPAIR THE MESSAGE NAMES, DRIVEN — give the carrier a provision and the same
/// program loads and answers.
///
/// This is what makes the refusal actionable rather than a wall: `Plain provides
/// Desc[T = Plain]` with its own `describe`, and `viaop(plain(), ?r)` answers `3`.
///
/// AND THE OTHER REPAIR THE MESSAGE OFFERS DOES NOT WORK IN THIS SHAPE, which is recorded
/// here rather than discovered later. Writing `requires(Desc[T = Plain])` in the clause —
/// the acknowledgement the sibling pass `check_rule_body_requirements` honours — is
/// refused by a DIFFERENT, pre-existing check: *"expected a body call to one of `Desc`'s
/// operations (or to an operation that `requires` it …) to ground the requirement"*. The
/// clause DOES call `viaop`, which requires `Desc`, but the transitive witness scan wants
/// that requirement bound over a type PARAMETER and this one binds a concrete sort, so it
/// declines. MEASURED, not assumed. Under the implicit-parameter reading the provision is
/// the honest repair anyway — acknowledging an obligation does not create an
/// implementation — which is why the message puts `provides` first.
#[test]
fn giving_the_carrier_a_provision_makes_the_same_program_answer() {
    let src = format!(
        r#"namespace test.nr6fj.fix
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

  operation viaop(x: Plain) -> Int64 requires Desc[T = Plain] = Desc.describe(x)
  rule answer(?r) :- viaop(plain(), ?r)
end
"#
    );
    let mut kb = crate::common::load_kb_with(&src);
    assert!(
        matches!(
            crate::common::query_unary(&mut kb, "test.nr6fj.fix.answer").as_slice(),
            [(Value::Int(3), true)]
        ),
        "with the provision in place the slot is filled and `Plain`'s own `describe` \
         answers — not the spec's default `1`",
    );
}
