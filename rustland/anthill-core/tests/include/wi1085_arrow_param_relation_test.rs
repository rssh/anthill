//! WI-1085 — an arrow's PARAMETER LIST is compared POSITIONALLY, and the comparison is
//! reached at all.
//!
//! `validate_arrow_param_result` served both callable spellings through one param
//! comparison, `types_compatible(d_param, a_param)` — by name. `arrow_parts` maps an
//! `arrow`'s `param` and a `Function[A = …]`'s `A` onto the same slot, so the function had
//! nothing left to tell them apart by, and the two want opposite relations:
//!
//!   * a `Function[A = …]`'s `A` is ONE argument's DATA type — what flows to
//!     `apply(f, x: A)` — so it aligns BY NAME (WI-775);
//!   * a genuine arrow's `param` at arity ≠ 1 is a parameter LIST, APPLIED positionally, so
//!     it aligns by POSITION with the synthetic `_1.._n` escape (WI-782/WI-442) — which is
//!     what lets a named-binder callback slot take an operation's eta arrow at all.
//!
//! The discriminator is `type_dispatch_name_view(declared)`, and the relation the arrow arm
//! needed already existed twice: `unify_arrow_params` on the unify side and
//! `arrow_params_compatible` on the subtype side, the latter being exactly what the GROUND
//! path (`arrow_compatible_view`) applies to the same pair. This is a routing fix.
//!
//! ## THE GROUNDNESS GATE WAS HIDING THE DISAGREEMENT, not preventing it
//!
//! Both halves are needed and neither is sufficient. The by-name comparison was WRONG for
//! every arrow-vs-arrow pair, and it survived only because it was almost never RUN: the gate
//! tested each component for groundness AS WRITTEN, so a variable the argument-unify loop had
//! already pinned still read as non-ground. WI-1084 measured exactly this — it
//! σ-resolved the RESULT and could not σ-resolve the PARAM, because doing so made both sides
//! ground for an ordinary higher-order call and the by-name comparison then refused 38 rows
//! across WI-064/278/411/424/492/493/585 and the stdlib combinators, all reading
//! `expected (acc: ?Acc, x: Element), got (_1: Int64, _2: Int64)` at `foldLeft.f` /
//! `foldRight.f`. Splitting the relation is what lets the resolution land.
//!
//! So the PARAM position of a non-ground callable argument was checked by NOTHING: the
//! whole-type `types_compatible` is withheld one frame up (WI-836's `type_contains_callable`
//! carve-out) and this component check skipped. That is the mirror of the RESULT hole
//! WI-1084 closed, and it is why WI-836's own known-gap pin —
//! `wi836…::two_callback_arguments_sharing_a_type_var_must_agree`, now inverted — falls out
//! of this ticket.
//!
//! ## THE CORPUS IS SILENT — so this file and `wi836…` are the whole coverage
//!
//! All seven tiers (`stdlib`, `rustland/anthill-stl/anthill`, `rustland/anthill-todo/anthill`,
//! `rustland/anthill-cpp-gen/anthill`, `examples/`, `anthill-todo/`, `anthill-testcases/`)
//! load with ZERO errors and IDENTICAL fact/rule totals before and after — measured both
//! ways, tier by tier. That is evidence nothing broke and NOT evidence anything works: no
//! corpus program passes a callback whose parameter type contradicts a σ-pinned slot, which
//! is exactly why the hole survived. Every claim below is driven here or not at all.
//!
//! ## What fails when each piece is backed out — DRIVEN, one revert each, whole crate
//!
//! | revert | cost |
//! |---|---|
//! | the ARROW arm's relation back to `types_compatible` (σ-resolution KEPT) | **35** — WI-064/278/411/413/424/492/493/585/588/714/775/782/783/784/791/792/793 plus [`an_operations_eta_arrow_still_fills_a_named_binder_slot`] here, which is their compact twin. Every one reads `expected (acc: …), got (_1: …)`. A wider spread than WI-1084's 38-row measurement named, and a different tree: the two counts are not the same set |
//! | the ARROW arm's σ-resolution (positional relation KEPT) | **2** — [`a_parameter_disagreement_is_refused_for_a_polymorphic_callback`] here and `wi836…::two_callback_arguments_sharing_a_type_var_must_agree`, both back to loading clean. NOTHING else in the crate notices, and that is the honest shape of the hole: it is reachable only where σ pins a callback's parameter from somewhere else, so no existing program was relying on the check either way |
//! | σ-resolving the `Function` arm TOO (the half deliberately NOT taken HERE) | **6** — all four `wi787_eta_spread_named_tuple_test` rows, [`a_function_slot_still_spreads_an_operation_across_its_components`] here, and `wi1083…::a_requires_carrying_member_runs_as_a_function_value`. Every one a program that EVALUATES; the last is WI-1083's headline, which reaches its dictionary through a `Function`-typed slot. **WI-1087 has since taken it**, and the six survive: they are all the SPREAD reading, which that ticket relates positionally instead of refusing, so the resolution no longer costs them. Measured on THIS ticket's tree, where the by-name relation was still unconditional |
//! | rendering the verdict AS WRITTEN instead of through σ | **5** — `wi791…::generic_callback_arrow_arity_is_conformance_checked`, `wi792…`'s two arity rows (all three printing `?T` where σ has pinned it), and this file's two refusal rows, which assert the resolved rendering. A message change only: no verdict moves |
//! | selecting the relation from the DECLARED spelling alone (this ticket's first cut) | **1** — [`a_function_typed_argument_at_an_arrow_slot_is_refused_whatever_the_labels`], newly refused. The MIRROR pairing is real and reachable: keying on `declared` gives the positional relation to a `Function`-typed ARGUMENT at an arrow slot, which is the same WI-775 hole from the other side. Found by review; nothing else in the crate notices |
//!
//! Rows that pass BOTH ways, by design, and say so at their sites:
//! [`a_parameter_disagreement_is_refused_for_a_monomorphic_callback`].
//!
//! REFERENCE: WI-1084 (where this was measured — the σ-resolution that exposed it and the
//! result-half fix that is its twin), WI-775 (what `Function`'s `A` means), WI-782 (the
//! `_1.._n` convention and the positional zip), WI-791 (arity selects WHICH relation),
//! WI-836 (the carve-out one frame up, and the gap this closes), WI-801 (the arity a
//! `Function` slot CAN decide), WI-442/WI-790 (`TupleAlign::PARAM_LIST` and what makes a
//! label synthetic), WI-1087 (the `Function`-arm coherence question this handed over, since
//! decided — `A` at the spread arity IS a parameter list, so the two spellings of `A` agree
//! and this file's `Function`-arm rows moved with it).

use crate::wi1012_static_supplier_tie_test::refusal;

fn drive_int(src: &str, op: &str) -> i64 {
    // A FRESH interpreter per call: reusing one after a trapped call returns a bogus
    // `Internal(...)` on every later call, which reads as an unrelated second failure.
    match crate::common::interp_for(src)
        .call(op, &[])
        .unwrap_or_else(|e| panic!("call {op}: {e:?}"))
    {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// THE ACCEPTANCE HALF, and the compact twin of the 38 rows WI-1084 measured. `myfold`'s
/// slot names its binders `(acc, x)`; `add2`'s eta arrow spells its parameter list with the
/// synthetic `(_1, _2)`, because that is what `operation_as_function_value` mints for a
/// multi-parameter operation. The two are the same parameter list — a list is APPLIED, so
/// slot `i` is slot `i` and `_1.._n` makes no claim about which is which (WI-442) — and the
/// by-name relation this arm used to take cannot say so.
///
/// DRIVEN to a value: before this ticket the program loaded because `?Acc` made the slot
/// read non-ground and the comparison was skipped, so "it loads" is exactly the property
/// that hid which relation was being applied.
///
/// CONTROL: with the arrow arm back on `types_compatible`, this is refused at load with
/// `expected (acc: Int64, x: Int64) -> Int64, got (_1: Int64, _2: Int64) -> Int64` — the
/// shape of all 38.
#[test]
fn an_operations_eta_arrow_still_fills_a_named_binder_slot() {
    let src = "namespace test.wi1085.pos\n\
        \x20 import anthill.prelude.{Int64}\n\
        \x20 operation add2(a: Int64, b: Int64) -> Int64 = a + b\n\
        \x20 operation myfold[Acc](f: (acc: Acc, x: Int64) -> Acc, z: Acc) -> Acc = f(z, 1)\n\
        \x20 operation drive() -> Int64 = myfold(add2, 10)\n\
        end\n";
    assert_eq!(drive_int(src, "test.wi1085.pos.drive"), 11);
}

/// THE REFUSAL HALF. The same shape with the callback's SECOND parameter contradicted: the
/// slot demands a `Bool` there and `add2` takes an `Int64`. Positional alignment is what
/// makes the disagreement visible — `acc` lines up with `_1` and `x` with `_2` — and the
/// σ-resolution is what makes it reachable, since `?Acc` is pinned to `Int64` by `z` and the
/// slot reads non-ground until it is.
///
/// CONTROL: before this ticket this LOADED CLEAN and trapped at eval. Its monomorphic twin
/// below was refused throughout, which is what says the polymorphic verdict was wrong rather
/// than the rule being lax.
#[test]
fn a_parameter_disagreement_is_refused_for_a_polymorphic_callback() {
    let msg = refusal(
        "namespace test.wi1085.bad\n\
         \x20 import anthill.prelude.{Int64, Bool}\n\
         \x20 operation add2(a: Int64, b: Int64) -> Int64 = a + b\n\
         \x20 operation myfold[Acc](f: (acc: Acc, x: Bool) -> Acc, z: Acc) -> Acc \
            = f(z, true)\n\
         \x20 operation drive() -> Int64 = myfold(add2, 10)\n\
         end\n",
    );
    assert!(
        msg.contains("myfold.f") && msg.contains("(acc: Int64, x: Bool)"),
        "the disagreement is refused at the argument, naming the slot and the parameter list \
         σ resolved it to: {msg}",
    );
}

/// The monomorphic twin — refused before this ticket and after it, by the GROUND path
/// (`arrow_compatible_view`, which has applied the positional relation all along). Here to
/// fix what the row above measures, not to measure anything itself: it is the row that says
/// the polymorphic acceptance was a hole rather than the rule.
#[test]
fn a_parameter_disagreement_is_refused_for_a_monomorphic_callback() {
    let msg = refusal(
        "namespace test.wi1085.badm\n\
         \x20 import anthill.prelude.{Int64, Bool}\n\
         \x20 operation add2(a: Int64, b: Int64) -> Int64 = a + b\n\
         \x20 operation myfoldm(f: (acc: Int64, x: Bool) -> Int64, z: Int64) -> Int64 \
            = f(z, true)\n\
         \x20 operation drive() -> Int64 = myfoldm(add2, 10)\n\
         end\n",
    );
    assert!(msg.contains("myfoldm.f"), "{msg}");
}

/// THE MIRROR PAIRING — a `Function`-typed ARGUMENT arriving at an `arrow` SLOT — is
/// refused, and NOT because of the labels. WI-1085 refused it by name; WI-1087 kept it
/// refused for the reason that actually governs it, after briefly getting this wrong.
///
/// AN ARROW SLOT STATES A HARD ARITY and applies its value with exactly that many
/// arguments. A `Function`-typed VALUE states none — WI-801: it may be the whole-`A`
/// reading (arity 1) or the spread one (arity `|A|`), and nothing in the type says which.
/// So matching the slot's `n` against `|A|` proves nothing about the callable inside. The
/// OTHER direction is sound for the mirror-image reason and is what WI-1087 delivered: a
/// `Function` SLOT admits both counts, and the arrow VALUE states which one it is.
///
/// MEASURED (review) when WI-1087's first cut made this arm symmetric — this loaded clean
/// and trapped `ArityMismatch { expected: 1, got: 2 }` at eval, which is the
/// load-clean-then-trap class WI-782/791/792/801 exist to remove:
///
/// ```text
/// operation whole(t: (Int64, Int64)) -> Int64 = t._1        -- ONE parameter
/// operation pass(f: Function[A = (Int64, Int64), …]) = take(f, 1)
/// operation take[Acc](g: (p: Acc, q: Int64) -> Int64, …) = g(z, 2)   -- applies TWO
/// ```
///
/// BOTH label shapes are asserted, because the labels are exactly what does NOT decide it:
/// the second fixture's `A` is written positionally, so its `_1, _2` line up with the
/// slot's parameter list under the synthetic escape and it would be ACCEPTED if the
/// positional relation reached here. It is refused all the same.
#[test]
fn a_function_typed_argument_at_an_arrow_slot_is_refused_whatever_the_labels() {
    let case = |ns: &str, a_ty: &str| {
        format!(
            "namespace {ns}\n\
             \x20 import anthill.prelude.{{Int64, Function}}\n\
             \x20 operation take[Acc](g: (p: Acc, q: Int64) -> Int64, z: Acc) -> Int64 \
                = g(z, 2)\n\
             \x20 operation pass(f: Function[A = {a_ty}, B = Int64, E = {{}}]) -> Int64 \
                = take(f, 1)\n\
             end\n"
        )
    };
    for (ns, a_ty) in [
        ("test.wi1085.mirror", "(a: Int64, b: Int64)"),
        ("test.wi1085.mirrorpos", "(Int64, Int64)"),
    ] {
        let msg = refusal(&case(ns, a_ty));
        assert!(
            msg.contains("take.g"),
            "a `Function` value states no arity, so it cannot satisfy a slot that does \
             (A = {a_ty}): {msg}",
        );
    }
}

/// THE HALF DELIBERATELY NOT TAKEN, driven so the decision has a program under it rather
/// than only a comment. A `Function[A = T, B = Int64]` slot with `T` pinned by the SIBLING
/// argument `t` accepts a 2-parameter operation, and eval SPREADS the tuple across its
/// parameters (WI-787) — `3 - 10`.
///
/// The `Function` arm keeps BOTH its relation (by name, WI-775) and its OPERAND (the
/// component as written). σ-resolving it would extend WI-775's refusal to a pairing only a
/// VARIABLE `A` can present, and this row plus `wi787_eta_spread_named_tuple_test`'s four
/// would become load errors. That is a change to WI-775's decision surface — its own pin,
/// `wi775…::function_sort_argument_type_does_not_bridge_keyings`, refuses the same pairing
/// written out concretely — and not to a walk depth. WI-1087 holds which rule wins.
///
/// CONTROL: this is the row that fails when the `Function` arm is σ-resolved; it passes
/// either way under the arrow arm's two halves.
#[test]
fn a_function_slot_still_spreads_an_operation_across_its_components() {
    let src = "namespace test.wi1085.fn\n\
        \x20 import anthill.prelude.{Int64, Function}\n\
        \x20 operation sub2(p: Int64, q: Int64) -> Int64 = p - q\n\
        \x20 operation apT[T](f: Function[A = T, B = Int64], t: T) -> Int64 = f(t)\n\
        \x20 operation drive() -> Int64 = apT(sub2, (acc: 3, x: 10))\n\
        end\n";
    assert_eq!(drive_int(src, "test.wi1085.fn.drive"), -7);
}
