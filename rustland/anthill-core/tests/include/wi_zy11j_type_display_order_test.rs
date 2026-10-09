//! A type's named arguments are printed in the order its sort declares its parameters.
//! Found while closing WI-20261009-ZY11J; it has no ticket of its own.
//!
//! BEFORE. They were printed in the order the carrier holds them, which is canonical and
//! follows the order the parameter NAMES were first interned in. That is no order an
//! author wrote — over `sort Vq[Elq, Nq]` a refusal read `Vq[Nq = 3, Elq = Int64]` — and
//! not one order either: with names an earlier load had interned (`E`, `N`) the same
//! source printed `Vec[N = 3, E = Int64]` loaded in one call and `Vec[E = Int64, N = 3]`
//! loaded after the library, so
//! `wi_hzvqa_alias_receiver_test::an_alias_written_positionally_or_fixing_a_constant_is_at_it`
//! failed under `ANTHILL_TEST_TWO_STEP_LOAD=1`.
//!
//! CONTROLS — measured, with the printing left in the carrier's order
//! (`type_application_display` asked for `NamedOrder::Stored` by the display walk):
//!
//!   FAIL, under either load recipe:
//!     arguments_are_printed_in_declared_order — its `Vq` half. The `Vec` half's names
//!       are the library's, interned before this source in either recipe, and passes.
//!   FAIL under the one-call recipe, and six of them under the two-call one too: the
//!     seven tests that had pinned the carrier's order and now assert the declared one —
//!     wi_0rp29_member_rule_test::a_receiver_binding_circular_around_another_parameter_is_refused,
//!     wi_0rp29_review9_regressions_test::a_foreign_unwritten_slot_is_one_type_for_a_{carrier_param,self_receiver}_call,
//!     wi_80zv8_written_carrier_test::the_carrier_slot_takes_the_arguments_whole_type,
//!     wi_9tgp7_branch_expected_flex_var_test::the_branch_join_reaches_the_result_type,
//!     wi_hzvqa_alias_receiver_test::an_alias_written_positionally_or_fixing_a_constant_is_at_it
//!     (the one the two-call recipe passes: there the carrier's order is the declared one),
//!     wi_w6jh0_companion_receiver_bracket_test::a_receiver_bracket_on_a_non_constructor_callee_is_read.
//!   PASS EITHER WAY, by design:
//!     a_row_written_in_another_order_is_the_same_row — a row's canonical order is keyed
//!       by the carrier's order still (`effect_atom_order_key`), which must not move with
//!       what a reader is shown.

use anthill_core::eval::Value;

use crate::common::{interp_for, load_errors_of};

/// A sort over two parameters holding a value in the second, named `e`/`n` as given, and
/// a `let` that claims the wrong value for it. `Earlier` declares the same two names the
/// other way round and above it, so the names are interned second-first: without it the
/// carrier's order is the declared one by accident, and the row would pass either way.
fn mismatch(ns: &str, sort: &str, e: &str, n: &str, receiver: &str) -> String {
    format!(
        "namespace test.{ns}\n  import anthill.prelude.{{Int64}}\n  \
         sort Earlier[{n}, {e}]\n    entity earlier(a: {n}, b: {e})\n  end\n  \
         sort {sort}[{e}, {n}]\n    entity mk(e: {e})\n    \
         operation same(x: {sort}[{e}, {n}]) -> {sort}[{e}, {n}] = x\n  end\n  \
         operation go() -> Int64 =\n    let v: {sort}[Int64, 4] = {receiver}.same(mk(e: 1))\n    2\nend\n"
    )
}

/// The refusal names both types with the element first and the value second, as the sort
/// declares them — whichever order the receiver writes them in, and whether or not the
/// library has parameters of the same names.
#[test]
fn arguments_are_printed_in_declared_order() {
    for (sort, e, n) in [("Vec", "E", "N"), ("Vq", "Elq", "Nq")] {
        for (spelling, receiver) in [
            ("declared", format!("{sort}[{e} = Int64, {n} = 3]")),
            ("swapped", format!("{sort}[{n} = 3, {e} = Int64]")),
            ("partial", format!("{sort}[{n} = 3]")),
        ] {
            let ns = format!("disporder{}{spelling}", sort.to_lowercase());
            let errs = load_errors_of(&mismatch(&ns, sort, e, n, &receiver));
            let expected = format!(
                "v.annotation (let-binding): expected {sort}[{e} = Int64, {n} = 4], got {sort}[{e} = Int64, {n} = 3]"
            );
            assert!(errs.iter().any(|err| err.contains(&expected)), "{ns}: {errs:#?}");
        }
    }
}

/// A row's atoms are still ordered by the carrier's own order of a label's arguments, so
/// one row written two ways is one row: an operation declaring `{Tag[A = Int64, B =
/// String], Other}` may call one declaring `{Other, Tag[B = String, A = Int64]}`.
#[test]
fn a_row_written_in_another_order_is_the_same_row() {
    let src = "namespace test.disporderrow\n  import anthill.prelude.{Int64, String, Effect}\n  \
               sort Tag[A, B]\n    entity tag\n  end\n  namespace Tag\n    provides Effect[T = Tag]\n  end\n  \
               sort Other\n    entity other\n  end\n  namespace Other\n    provides Effect[T = Other]\n  end\n  \
               operation inner() -> Int64 effects {Other, Tag[B = String, A = Int64]} = 7\n  \
               operation go() -> Int64 effects {Tag[A = Int64, B = String], Other} = inner()\nend\n";
    let mut interp = interp_for(src);
    match interp.call("test.disporderrow.go", &[]) {
        Ok(Value::Int(7)) => {}
        other => panic!("expected 7, got {other:?}"),
    }
}
