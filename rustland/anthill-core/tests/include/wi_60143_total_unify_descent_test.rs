//! WI-20260904-60143 — an AUTHOR-ORDERED SLOT LIST unifies EVERY slot, so what a `false`
//! leaves in σ does not depend on how the disagreeing type was SPELLED.
//!
//! ## The idiom, and why the ticket's own repair was the wrong one
//!
//! ~16 call sites in `kb/typing.rs` DISCARD this relation's boolean (the census is on the
//! ticket). The stated reason is sound: unify is EQUALITY while argument passing is
//! SUBTYPING plus conversions, so a unify-`false` must not by itself reject. What those
//! sites take from the call is the SUBSTITUTION — `unify_arrow_function_view`'s doc says so
//! outright: "ITS JOB IS TO BIND … which is why 'answered false having bound nothing' was a
//! defect and 'answers false having bound `?A1`' is the fix" (WI-1084).
//!
//! The ticket proposed the opposite — snapshot σ and ROLL BACK on `false`. Built and
//! measured, that costs **4 rows**, because each is reached exactly BY the partial binding:
//!
//! | fails with a rollback inside `unify_types` |
//! |---|
//! | `kb::typing::tests::wi1084_arrow_function_unify_tests::the_two_spellings_of_one_slot_answer_alike` |
//! | `wi1078_unbound_return_var_test::the_tie_survives_the_opening` |
//! | `wi1082_self_return_tie_test::a_bodyless_member_cannot_launder_either` |
//! | `wi1083_polytype_test::a_result_type_disagreement_is_refused` |
//!
//! All four are groundness-gated: the variable pinned by the AGREEING component is what
//! makes the disagreeing one read GROUND and therefore comparable. Roll that back, the slot
//! reads non-ground, the check defers, and the program loads clean. The partial bindings are
//! not the defect — they are the channel.
//!
//! ## What the defect actually was: WHICH partial bindings, decided by ORDER
//!
//! The early `return false` stopped the loop at the first disagreeing slot, so a caller
//! reading σ afterwards got the slots WRITTEN BEFORE it and not the ones after. Since a
//! parameterized type's slots may be written in any order, that made σ a function of the
//! author's spelling. One program, two slot orders, two different user-facing messages:
//!
//! | `Pair[A, B]` slot order | before | with the ticket's rollback | delivered |
//! |---|---|---|---|
//! | disagreement FIRST (`A = Int64, B = X`) | `expected Pair[A = Int64, B = ?X]` | `expected Pair[A = Int64, B = ?X]` | `expected Pair[A = Int64, B = Int64]` |
//! | disagreement SECOND (`A = X, B = Int64`) | `expected Pair[A = Int64, B = Int64]` | `expected Pair[A = ?X, B = Int64]` | `expected Pair[A = Int64, B = Int64]` |
//!
//! Note the middle column: the rollback does not fix the asymmetry, it LEVELS DOWN — it makes
//! the order that worked report `?X` too. Unifying every slot levels up, and it is the
//! completion of the principle WI-1084 already committed this relation to. A later slot
//! cannot un-say an earlier one's disagreement (the verdict is a conjunction either way), so
//! the early exit bought nothing but the arbitrariness.
//!
//! ## THE LINE: AUTHORIAL ORDER, NOT "descend totally"
//!
//! The arbitrary thing was the AUTHOR'S SPELLING. A parameterized type's binding list, a
//! tuple's field list and an arrow's parameter LIST are written in an order that carries no
//! meaning, so "the slots before the first disagreement" is not a property of the two types.
//! Those loops became total. An arrow's `param` / `result` / `effects` are fixed by the FORM,
//! so stopping at the first disagreeing PART is already a function of the types alone — and
//! MAKING THEM TOTAL IS UNSOUND, measured: a `result` binding taken across a disagreeing
//! `param` is drawn from two arrows that are not the same function, and it FILLS UNWRITTEN
//! CARRIER PARAMS from a unify that failed. Built and run, four rows moved, one of them from
//! a refusal to a clean load:
//!
//! | making `unify_arrow_view` / `unify_arrow_function_view` total too |
//! |---|
//! | `wi_mdwew…::ambient_requires_compound_clause_value_is_not_bound_verbatim` — **REFUSED → loads clean** |
//! | `wi_mdwew…::foreign_provision_binding_is_refused_like_its_concrete_twin` — rendering only |
//! | `wi599_carrier_arg_provision_test::a_clause_about_another_parameter_names_that_parameters_element` — rendering only |
//! | `wi599_carrier_arg_provision_test::a_written_bracket_outranks_the_clause` — rendering only |
//!
//! The first is "grant a licence and bind a wrong rigid together", the exact shape that test
//! exists to forbid. So the arrow parts keep their short-circuit, in BOTH spellings — giving
//! `arrow` and `Function[A, B, E]` different rules here would be the defect WI-1084 closed.
//!
//! ## TWO CALL SITES, TWO BACK-OUTS — one per test below
//!
//! "Every slot of an author-ordered list" is an idea; the change is two loops. Each row names
//! the loop whose back-out (restore its `return false` / `.all`) turns it red, MEASURED one
//! at a time on this tree:
//!
//! | loop | back-out effect |
//! |---|---|
//! | `unify_parameterized_view` binding loop | [`the_disagreeing_slot_first_still_pins_the_rest`] → `Pair[A = Int64, B = ?X]` |
//! | `unify_named_tuple_as` slot loop | [`a_param_list_disagreement_is_refused_at_all`] and [`a_data_tuple_disagreement_is_refused_at_all`] → **both LOAD CLEAN** |
//!
//! The second is not a diagnostic improvement but a REFUSAL that did not previously happen:
//! with the descent stopping at the disagreeing slot, nothing pinned `X`, the slot read
//! non-ground, the groundness gate deferred, and `takeT((a: 1, b: 2))` against `(a: Bool, b:
//! X)` loaded clean. Two tuple modes (`PARAM_LIST` and `EQUALITY`) share the loop and are
//! driven separately, since one edit serving two modes is where this file has been bitten.
//!
//! Each fixture puts the type variable ONLY inside the failing pair. An earlier cut of these
//! fixtures also passed a sibling argument typed on that variable (`z: Acc`), which pinned it
//! on its own — every row stayed green under every back-out and measured nothing.
//!
//! [`an_agreeing_call_still_loads`] and [`an_agreeing_tuple_call_still_loads`] pass under
//! every tree; without them, refusing everything would satisfy every row above.

use crate::common::try_load_kb_with;

const PAIR: &str = "namespace test.wi60143\n\
   \x20 import anthill.prelude.{Int64, String}\n\
   \x20 sort Pair[A, B]\n\
   \x20   entity pair(a: A, b: B)\n\
   \x20 end\n";

fn refusal(src: &str) -> String {
    try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected a load refusal; the program loaded clean:\n{src}"))
        .join("\n")
}

fn loads(src: &str) {
    assert!(
        try_load_kb_with(src).is_ok(),
        "must still load: {:?}\n{src}",
        try_load_kb_with(src).err(),
    );
}

/// THE HEADLINE — `unify_parameterized_view`. `A` disagrees (`String` supplied for `Int64`)
/// and `B` is the slot carrying the operation's type parameter, so on the old descent `?X`
/// was never reached and the message showed it raw.
#[test]
fn the_disagreeing_slot_first_still_pins_the_rest() {
    let msg = refusal(&format!(
        "{PAIR}\
         \x20 operation take[X](p: Pair[A = Int64, B = X]) -> X\n\
         \x20 operation drive() -> String = take(pair(a: \"s\", b: 7))\n\
         end\n"
    ));
    assert!(
        msg.contains("expected Pair[A = Int64, B = Int64]") && !msg.contains("?X"),
        "the descent continues past the disagreeing slot and pins `X := Int64` from the \
         agreeing one, so the refusal names a type and not a variable: {msg}",
    );
}

/// THE MIRROR, and the row the ticket's proposed rollback would have broken. It is green on
/// the pre-ticket tree too — that is the point: it says the two orders were made to agree by
/// pinning BOTH, not by un-pinning both.
#[test]
fn the_disagreeing_slot_second_pins_the_rest() {
    let msg = refusal(&format!(
        "{PAIR}\
         \x20 operation take2[X](p: Pair[A = X, B = Int64]) -> X\n\
         \x20 operation drive() -> String = take2(pair(a: 7, b: \"s\"))\n\
         end\n"
    ));
    assert!(
        msg.contains("expected Pair[A = Int64, B = Int64]") && !msg.contains("?X"),
        "the same disagreement written the other way round renders identically: {msg}",
    );
}

/// CONTROL for the two above: a call whose every slot agrees still loads.
#[test]
fn an_agreeing_call_still_loads() {
    loads(&format!(
        "{PAIR}\
         \x20 operation take2[X](p: Pair[A = X, B = Int64]) -> X\n\
         \x20 operation drive() -> String = take2(pair(a: \"s\", b: 7))\n\
         end\n"
    ));
}

/// `unify_named_tuple_as` in `PARAM_LIST` mode — a 2-parameter arrow slot whose FIRST
/// parameter disagrees and whose second carries the variable. Backing the loop out does not
/// merely degrade the message: nothing pins `Acc`, the slot reads non-ground, and the whole
/// call LOADS CLEAN.
#[test]
fn a_param_list_disagreement_is_refused_at_all() {
    let msg = refusal(
        "namespace test.wi60143.plist\n\
         \x20 import anthill.prelude.{Int64, Bool, String}\n\
         \x20 operation add2(a: Int64, b: Int64) -> Int64 = a + b\n\
         \x20 operation myfold[Acc](f: (acc: Bool, x: Acc) -> Int64) -> Acc\n\
         \x20 operation drive() -> String = myfold(add2)\n\
         end\n",
    );
    assert!(
        msg.contains("expected (acc: Bool, x: Int64)") && !msg.contains("?Acc"),
        "the second parameter slot is unified though the first disagreed: {msg}",
    );
}

/// `unify_named_tuple_as` in `EQUALITY` mode — the DATA-tuple twin, driven separately
/// because one loop serving two alignment modes is exactly where a single row would leave
/// half the change unmeasured. Also LOADS CLEAN when backed out.
#[test]
fn a_data_tuple_disagreement_is_refused_at_all() {
    let msg = refusal(
        "namespace test.wi60143.dtuple\n\
         \x20 import anthill.prelude.{Int64, Bool, String}\n\
         \x20 operation takeT[X](t: (a: Bool, b: X)) -> X\n\
         \x20 operation drive() -> String = takeT((a: 1, b: 2))\n\
         end\n",
    );
    assert!(
        msg.contains("expected (a: Bool, b: Int64)") && !msg.contains("?X"),
        "the second field is unified though the first disagreed: {msg}",
    );
}

/// CONTROL for the two tuple rows, which are the ones that turned a clean load into a
/// refusal: an AGREEING call in each mode must still load.
#[test]
fn an_agreeing_tuple_call_still_loads() {
    loads(
        "namespace test.wi60143.okplist\n\
         \x20 import anthill.prelude.{Int64}\n\
         \x20 operation add2(a: Int64, b: Int64) -> Int64 = a + b\n\
         \x20 operation myfold[Acc](f: (acc: Int64, x: Acc) -> Int64) -> Acc\n\
         \x20 operation drive() -> Int64 = myfold(add2)\n\
         end\n",
    );
    loads(
        "namespace test.wi60143.okdtuple\n\
         \x20 import anthill.prelude.{Int64}\n\
         \x20 operation takeT[X](t: (a: Int64, b: X)) -> X\n\
         \x20 operation drive() -> Int64 = takeT((a: 1, b: 2))\n\
         end\n",
    );
}
