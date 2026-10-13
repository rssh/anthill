//! WI-20261013-50ZMN — two requirements of one sort at one type, each under a name of its
//! own, are TWO requirements.
//!
//! `Semi` requires `Plus: Mon[T]` and `Times: Mon[T]`. Until this ticket the two lines were
//! one requirement under two names (kernel-language §5.2 said so, WI-20261013-0K8WD's rows
//! drove it): one `SortRequiresInfo` fact, one entry of the sort's chain, one dictionary
//! slot. `Semi.mulAdd[T = Int64, Plus = Sum, Times = Product](2, 3, 4)` was refused, two
//! providers for one requirement, and a body had no way to say which of the two a call
//! reads — `Plus.combine(a, b)` was an unknown functor.
//!
//! What holds now, each backed out below:
//!
//!   * TWO NAMES ARE TWO ENTRIES (`typing::collect_sort_requires`): the facts still hold a
//!     sort required at some bindings once, and the chain reads one entry for each name its
//!     lines gave it. An operation's own goals were two entries already, and each now
//!     carries its name (`op_requires_entries`).
//!   * EACH HAS A FRAME SLOT OF ITS OWN (`name_slots`): the slot's name was the spec term's
//!     identity, which the two share.
//!   * A SELECTION IS KEPT BY THE NAME (`state_one_requirement`): two names are two keys.
//!   * A BODY READS ONE BY ITS NAME (`read_requirement_by_name`): `Plus.combine(a, b)`,
//!     which the loader reads as `Mon.combine[Mon = Plus](a, b)`
//!     (`Loader::requirement_name_call`), and that bracket's value is a requirement of the
//!     enclosing declaration (`SelectedProvider::Enclosing`).
//!   * A CALLEE'S UNNAMED REQUIREMENT TAKES ONE BY ITS NAME (`forward_by_name`):
//!     `Anon.via[T = T, Mon = Plus](a, b)`.
//!   * A CALL THAT NAMES NEITHER IS REFUSED, at a spec operation's call
//!     (`TypeError::RequirementReadTie`) and at a callee's unnamed requirement.
//!   * A LINE WITH NO NAME BESIDE TWO NAMED ONES IS REFUSED where it is written: a sort's
//!     (`Loader::note_requires_line`) and an operation's
//!     (`check_unnamed_requirement_lines`).
//!   * A NAME REACHES WHAT ITS REQUIREMENT'S DICTIONARY HOLDS: under `requires A: Ord[T]`
//!     and `requires B: Ord[T]`, `A.compare(a, b)` is `WeakOrd`'s `compare` read beneath
//!     `A`, and a call that names neither is refused as one the two cover is
//!     (`frame_tree`, `held_for`) — to any depth, `PartialEq.eq[PartialEq = A](a, b)`
//!     three requirements down. The spelling `A.member(…)` reaches what the qualified
//!     name `Ord.member` would (`load::operation_through_requirement_name`), and a
//!     refusal names it only where it reads.
//!
//! And where else two requirements could have been read by the order of their lines, each
//! found by `/code-review` of the above and each backed out below:
//!
//!   * AN OPERATION'S ENTRY THAT STATES AGAIN A REQUIREMENT ITS SORT NAMES IS HANDED ON AS
//!     THE NAME IS (`named_slot_of_frame_entry`): `fold3(…) requires Mon[T = HT]` under
//!     `requires m: Mon[T = HT]`, called `[Mon = Plus]`.
//!   * A GOAL MET WHILE ANOTHER IS RESOLVED (`scope_requirement_tie`): a conditional
//!     provision's own requirement, which no call names one for, is refused naming both.
//!   * A SLOT THE ARGUMENT'S TYPE BINDS TO A PARAMETER OF THE CALLER'S IS THAT
//!     PARAMETER'S (`project_param_forward`).
//!   * A PROVISION'S CONTRACT IS CHECKED UNDER WHAT HOLDS (`ProvisionScope`): two named
//!     requirements of the carrier are one assumption there, nothing being handed on.
//!   * A NAME IS HELD TO WHAT THE QUALIFIED NAME IS: an `internal` operation is refused
//!     through it, and which sort it requires is known from the scan, wherever in the
//!     sort's body — or in which entry at its address — the `requires` line stands.
//!   * AT A HIGHER-KINDED CARRIER TOO: the carrier's branch stands aside for a call that
//!     names a requirement, and a `requires` keeps the binding it writes for a parameter
//!     declared in a sort's header (`sort CpsMonad[F[T]]`), which was no entry of the
//!     sort's parameter list.
//!   * WHICH FACT A LINE STATES IS READ THROUGH THE VIEW (`place_of_requirement`), as the
//!     chain counts its facts: by identity, a binding written through a type alias made
//!     each line a requirement of its own that no fact held. Found by the node-carrier
//!     control (`ANTHILL_TEST_NODE_CARRIER=1`), under which every row here has the verdict
//!     it has without it.
//!
//! ## Back-out
//!
//! Each mechanism mutated in place, one at a time, and every row of this file run under
//! each one with the rows of the files that read a requirement or select a provider
//! (WI-20261013-0K8WD's file and the family it was measured with, 723 rows). Measured
//! 2026-10-13; a row is named where it FAILS with the mechanism backed out:
//!
//! | backed out | fails |
//! |---|---|
//! | two names of one fact read as one chain entry, under the first name (`collect_sort_requires`) | `a_call_that_names_neither_is_refused`, `a_call_through_a_requirements_name_reads_that_requirement`, `a_callees_unnamed_requirement_takes_one_by_its_name`, `a_goal_met_inside_a_resolution_is_not_read_from_the_first_of_two`, `a_line_with_no_name_beside_two_named_ones_is_refused`, `a_name_given_at_the_key_of_a_restated_requirement_is_handed_on`, `a_name_is_read_wherever_the_body_is_written`, `a_name_reaches_what_its_requirements_dictionary_holds`, `a_name_reaches_what_its_requirements_dictionary_holds_further_down`, `a_name_says_which_requirement_and_not_that_it_fits`, `a_spec_operation_with_a_body_is_read_through_a_name`, `a_witness_with_two_requirements_takes_a_provider_for_each`, `an_operation_written_above_the_requires_lines_reads_them`, `each_of_the_two_is_handed_on_under_its_own_name`, `one_selected_and_the_other_left_out_is_decided_on_its_own`, `the_call_written_in_full_is_the_same_call`, `the_two_carried_by_a_values_type_answer_the_same`, `which_requirement_a_line_states_does_not_turn_on_how_its_binding_is_written`; in `wi_0k8wd_selection_per_requirement_test`: `a_requirement_after_a_restated_one_is_found` |
//! | an operation's own goals left without their names (`op_requires_entries`) | `a_line_with_no_name_beside_two_named_ones_is_refused`, `a_refusal_names_the_requirements_of_its_own_operation`, `a_slot_the_arguments_type_binds_to_a_callers_name_is_that_names`, `a_sorts_and_an_operations_under_two_names_are_two`, `an_operations_own_two_requirements_are_two`, `the_two_carried_by_a_values_type_answer_the_same` |
//! | two requirements of one spec term given one frame slot name (`name_slots`) | `a_call_through_a_requirements_name_reads_that_requirement`, `a_callees_unnamed_requirement_takes_one_by_its_name`, `a_name_given_at_the_key_of_a_restated_requirement_is_handed_on`, `a_name_is_read_wherever_the_body_is_written`, `a_name_reaches_what_its_requirements_dictionary_holds`, `a_slot_the_arguments_type_binds_to_a_callers_name_is_that_names`, `a_spec_operation_with_a_body_is_read_through_a_name`, `a_witness_with_two_requirements_takes_a_provider_for_each`, `an_operation_written_above_the_requires_lines_reads_them`, `an_operations_own_two_requirements_are_two`, `each_of_the_two_is_handed_on_under_its_own_name`, `one_selected_and_the_other_left_out_is_decided_on_its_own`, `the_call_written_in_full_is_the_same_call`, `the_two_carried_by_a_values_type_answer_the_same`, `which_requirement_a_line_states_does_not_turn_on_how_its_binding_is_written`; in `wi_0k8wd_selection_per_requirement_test`: `a_requirement_after_a_restated_one_is_found` |
//! | two entries under two names keyed as one requirement (`state_one_requirement`) | `a_call_through_a_requirements_name_reads_that_requirement`, `a_callees_unnamed_requirement_takes_one_by_its_name`, `a_name_given_at_the_key_of_a_restated_requirement_is_handed_on`, `a_name_is_read_wherever_the_body_is_written`, `a_name_reaches_what_its_requirements_dictionary_holds`, `a_name_reaches_what_its_requirements_dictionary_holds_further_down`, `a_slot_the_arguments_type_binds_to_a_callers_name_is_that_names`, `a_sorts_and_an_operations_under_two_names_are_two`, `a_spec_operation_with_a_body_is_read_through_a_name`, `an_operation_written_above_the_requires_lines_reads_them`, `an_operations_own_two_requirements_are_two`, `each_of_the_two_is_handed_on_under_its_own_name`, `one_selected_and_the_other_left_out_is_decided_on_its_own`, `the_call_written_in_full_is_the_same_call`, `the_two_carried_by_a_values_type_answer_the_same`; in `wi_0k8wd_selection_per_requirement_test`: `a_requirement_after_a_restated_one_is_found` |
//! | a call that names neither read by the walks, the first written (`read_requirement_by_name`'s tie) | `a_call_that_names_neither_is_refused`, `a_name_reaches_what_its_requirements_dictionary_holds`, `a_name_reaches_what_its_requirements_dictionary_holds_further_down`, `a_spec_operation_with_a_body_is_read_through_a_name`, `an_operations_own_two_requirements_are_two` |
//! | a requirement's name at a spec key not read as a selection (`validate_written_selection`) | `a_call_through_a_requirements_name_reads_that_requirement`, `a_callees_unnamed_requirement_takes_one_by_its_name`, `a_line_with_no_name_states_the_named_one_at_a_binding_that_holds_a_value`, `a_name_given_at_the_key_of_a_restated_requirement_is_handed_on`, `a_name_is_held_to_the_call_at_a_higher_kinded_carrier`, `a_name_is_read_wherever_the_body_is_written`, `a_name_reaches_what_its_requirements_dictionary_holds`, `a_name_reaches_what_its_requirements_dictionary_holds_further_down`, `a_name_says_which_requirement_and_not_that_it_fits`, `a_sorts_and_an_operations_under_two_names_are_two`, `a_witness_with_two_requirements_takes_a_provider_for_each`, `an_internal_operation_is_not_reached_through_a_name`, `an_operation_written_above_the_requires_lines_reads_them`, `an_operations_own_two_requirements_are_two`, `one_named_requirement_is_read_with_or_without_its_name`, `one_selected_and_the_other_left_out_is_decided_on_its_own`, `the_call_written_in_full_is_the_same_call`, `the_operation_a_name_reaches_does_not_follow_declaration_order`, `the_two_carried_by_a_values_type_answer_the_same`, `which_requirement_a_line_states_does_not_turn_on_how_its_binding_is_written`; in `wi_0k8wd_selection_per_requirement_test`: `a_requirement_after_a_restated_one_is_found`, `a_requirement_stated_again_with_no_name_is_the_same_one`; and `wi_tx0g6_selection_validation_test::a_spec_key_naming_an_enclosing_requirement_hands_it_on` |
//! | a call that names its requirement left to the walks (`read_requirement_by_name`'s classification) | `a_call_through_a_requirements_name_reads_that_requirement`, `a_name_is_held_to_the_call_at_a_higher_kinded_carrier`, `a_name_is_read_wherever_the_body_is_written`, `a_name_reaches_what_its_requirements_dictionary_holds`, `a_name_reaches_what_its_requirements_dictionary_holds_further_down`, `a_name_says_which_requirement_and_not_that_it_fits`, `a_sorts_and_an_operations_under_two_names_are_two`, `a_spec_operation_with_a_body_is_read_through_a_name`, `a_witness_with_two_requirements_takes_a_provider_for_each`, `an_operation_written_above_the_requires_lines_reads_them`, `an_operations_own_two_requirements_are_two`, `one_selected_and_the_other_left_out_is_decided_on_its_own`, `the_call_written_in_full_is_the_same_call`, `the_two_carried_by_a_values_type_answer_the_same`, `which_requirement_a_line_states_does_not_turn_on_how_its_binding_is_written`; in `wi_0k8wd_selection_per_requirement_test`: `a_requirement_after_a_restated_one_is_found` |
//! | a call through a requirement's name left a qualified name (`Loader::requirement_name_call`) | `a_call_through_a_requirements_name_reads_that_requirement`, `a_line_with_no_name_states_the_named_one_at_a_binding_that_holds_a_value`, `a_name_is_held_to_the_call_at_a_higher_kinded_carrier`, `a_name_is_read_wherever_the_body_is_written`, `a_name_reaches_what_its_requirements_dictionary_holds`, `a_name_says_which_requirement_and_not_that_it_fits`, `a_sorts_and_an_operations_under_two_names_are_two`, `a_spec_operation_with_a_body_is_read_through_a_name`, `a_witness_with_two_requirements_takes_a_provider_for_each`, `an_internal_operation_is_not_reached_through_a_name`, `an_operation_written_above_the_requires_lines_reads_them`, `an_operations_own_two_requirements_are_two`, `one_named_requirement_is_read_with_or_without_its_name`, `one_selected_and_the_other_left_out_is_decided_on_its_own`, `the_operation_a_name_reaches_does_not_follow_declaration_order`, `the_two_carried_by_a_values_type_answer_the_same`, `which_requirement_a_line_states_does_not_turn_on_how_its_binding_is_written`; in `wi_0k8wd_selection_per_requirement_test`: `a_requirement_after_a_restated_one_is_found`, `a_requirement_stated_again_with_no_name_is_the_same_one` |
//! | which sort a name requires read off the slot record alone, not what the scan recorded (`requirement_name_call`) | `a_name_is_read_wherever_the_body_is_written`, `an_operation_written_above_the_requires_lines_reads_them` |
//! | a callee's dep answered by the strategies alone: no name read, no tie refused (`forward_by_name`) | `a_call_that_names_neither_is_refused`, `a_callees_unnamed_requirement_takes_one_by_its_name`, `a_name_reaches_what_its_requirements_dictionary_holds`, `a_name_reaches_what_its_requirements_dictionary_holds_further_down`; and `wi_tx0g6_selection_validation_test::a_spec_key_naming_an_enclosing_requirement_hands_it_on` |
//! | a callee's dep two named requirements cover handed the first (`forward_by_name`'s tie) | `a_call_that_names_neither_is_refused`, `a_name_reaches_what_its_requirements_dictionary_holds`, `a_name_reaches_what_its_requirements_dictionary_holds_further_down` |
//! | a sort's line with no name beside two named ones loads (`Loader::note_requires_line`) | `a_line_with_no_name_beside_two_named_ones_is_refused` |
//! | an operation's line with no name beside two named ones loads (`check_unnamed_requirement_lines`) | `a_line_with_no_name_beside_two_named_ones_is_refused` |
//! | a requirement rendered by its goal alone (`render_requires_entry` / `under_its_name`) | `a_name_is_held_to_the_call_at_a_higher_kinded_carrier`, `a_name_says_which_requirement_and_not_that_it_fits`, `one_selected_and_the_other_left_out_is_decided_on_its_own`; in `wi_0k8wd_selection_per_requirement_test`: `a_requirement_stated_again_with_no_name_is_the_same_one` |
//! | an operation's own name not read as a written selection value (`enclosing_requirement_named`) | `a_sorts_and_an_operations_under_two_names_are_two`, `an_operations_own_two_requirements_are_two` |
//! | the tie looked for among the frame's own entries, not beneath them (`read_requirement_by_name`) | `a_name_reaches_what_its_requirements_dictionary_holds`, `a_name_reaches_what_its_requirements_dictionary_holds_further_down` |
//! | a name read at its own entry and not beneath it (`read_requirement_by_name`) | `a_name_reaches_what_its_requirements_dictionary_holds`, `a_name_reaches_what_its_requirements_dictionary_holds_further_down` |
//! | a callee's dep answered by an entry that covers it, not by one whose dictionary holds it (`held_for`) | `a_name_reaches_what_its_requirements_dictionary_holds`, `a_name_reaches_what_its_requirements_dictionary_holds_further_down` |
//! | a name read as a selection only for the sort it requires (`enclosing_requirement_named`) | `a_name_reaches_what_its_requirements_dictionary_holds`, `a_name_reaches_what_its_requirements_dictionary_holds_further_down` |
//! | the member of a call through a name looked for on the required sort alone (`operation_through_requirement_name`) | `a_name_reaches_what_its_requirements_dictionary_holds` |
//! | the key of an operation with a body of its own naming nothing, whatever its value (`resolve_call_type_arg_targets`) | `a_spec_operation_with_a_body_is_read_through_a_name` |
//! | a call of an operation with a body of its own neither refused nor read by name (the defaulted block) | `a_spec_operation_with_a_body_is_read_through_a_name` |
//! | a member's name for its requirement compared as written with the spec operation's (`MemberEntries`) | and `spec_op_requirement_at_member_test::a_name_an_arguments_type_binds_is_the_members`, `spec_op_requirement_at_member_test::the_member_reads_it_under_its_own_names`, `spec_op_requirement_at_member_test::two_requirements_at_one_type_are_two_at_the_member`, `spec_op_requirement_at_member_test::two_requirements_reach_a_member_chosen_when_the_call_runs` |
//! | an operation's entry that states again a requirement its sort names answered by the goal, not as the name is (`build_op_scoped_dicts` / `named_slot_of_frame_entry`) | `a_name_given_at_the_key_of_a_restated_requirement_is_handed_on`; and `spec_op_requirement_at_member_test::a_name_bound_to_a_parameter_nothing_is_held_for_is_refused`, `wi_wn9p8_forward_soundness_test::a_callees_own_slot_refuses_an_untied_forward` |
//! | a goal met inside a resolution read from the first of two named requirements (`resolve_inner` / `scope_requirement_tie`) | `a_goal_met_inside_a_resolution_is_not_read_from_the_first_of_two`, `a_refusal_names_the_requirements_of_its_own_operation` |
//! | a sort's line with no name that leaves a parameter unbound beside two named ones loads (`check_unnamed_requirement_lines`, the sorts) | `a_line_with_no_name_beside_two_named_ones_is_refused` |
//! | a slot the argument's type binds to a caller's parameter answered by the goal (`project_param_forward`) | `a_slot_the_arguments_type_binds_to_a_callers_name_is_that_names` |
//! | an internal operation reached through a requirement's name (`requirement_name_call`'s visibility gate) | `an_internal_operation_is_not_reached_through_a_name` |
//! | a call that names a requirement answered by the higher-kinded carrier's own provision (the `hk_carrier` branch) | `a_name_is_held_to_the_call_at_a_higher_kinded_carrier` |
//! | a header-declared higher-kinded parameter left out of its sort's parameter list, so a requires drops the binding to it (`exit_sort_with_body`) | `a_name_is_held_to_the_call_at_a_higher_kinded_carrier` |
//! | a provision's contract checked under assumptions that keep their names, two of one sort a tie (`ProvisionScope`) | `the_two_carried_by_a_values_type_answer_the_same` |
//! | the tie refusal advising `Name.member(…)` whether or not that spelling reads (`read_requirement_by_name`) | `a_name_reaches_what_its_requirements_dictionary_holds_further_down` |
//! | the sort's own member taken only where its operation record is already loaded (`operation_through_requirement_name`) | `the_operation_a_name_reaches_does_not_follow_declaration_order` |
//! | which fact a line states decided by the spec's identity, a term's id or an occurrence's address (`place_of_requirement`) | `which_requirement_a_line_states_does_not_turn_on_how_its_binding_is_written` |
//! | the named requirement not held to the call's bindings (`read_requirement_by_name`'s cover) | `a_name_is_held_to_the_call_at_a_higher_kinded_carrier`, `a_name_says_which_requirement_and_not_that_it_fits` |
//! | an entry's name left out of its equality and hash (`RequiresEntry`) | `a_refusal_names_the_requirements_of_its_own_operation` |
//!
//! PASS EITHER WAY, BY DESIGN: [`a_name_that_reaches_no_such_operation_is_refused`] — a
//! name that reaches no operation is the qualified name it was written as, read or not.
//! AND UNDER EVERY BACK-OUT ABOVE, each failing one of WI-20261013-0K8WD's alone (that
//! file's table): [`two_requirements_at_two_types_need_no_name`],
//! [`a_provider_selected_against_the_values_type_is_a_type_error`] and
//! [`a_parameter_that_writes_neither_slot_is_refused`]. Each says so at its site.
//!
//! ## Not reached
//!
//!   * A SPEC OPERATION WITH A BODY OF ITS OWN, WHERE THE PROVIDER HAS NO MEMBER FOR IT.
//!     A call through a name is read from that requirement's dictionary — its provider's
//!     member where it has one ([`a_spec_operation_with_a_body_is_read_through_a_name`]).
//!     Where it has none the spec's body runs, and what ITS calls of the spec's other
//!     operations dispatch on is as it was under one requirement: an argument's value
//!     where there is one, which two witnesses at one type tie, where the call runs
//!     (`AmbiguousSpecOpDispatch`; measured with one requirement and with two, the same).
//!   * A PARAMETER THAT WRITES NEITHER SLOT of a sort with two at one type
//!     (`s: SemiV[T = Int64]`) is refused where its operation is called through it, as two
//!     parameters of one carrier are: the two slots read off the argument's type are told
//!     apart by nothing a body's goal says. [`a_parameter_that_writes_neither_slot_is_refused`]
//!     holds what is; the forward under two names of the signature's own is the spelling
//!     that runs.
//!   * TWO SUCH REQUIREMENTS BENEATH ONE ENTRY OF THE FRAME — a pair in the chain of a
//!     sort the frame requires, and not in the frame — are not looked for where a call is
//!     read by its goal; the walk takes the first.
//!   * A CALL AT A HIGHER-KINDED PARAMETER ITSELF. `CpsMonad.unit(42)` at a result typed
//!     `G[T = Int64]`, under `requires CpsMonad[F = G]`, is a type error at the result
//!     (`expected G[T = Int64], got F[T = Int64]`) — measured with this ticket's change
//!     and with the binding's half of it backed out, the same. So the binding a `requires`
//!     now keeps for such a parameter is driven by the refusal of a call at another
//!     carrier ([`a_name_is_held_to_the_call_at_a_higher_kinded_carrier`]), and by no call
//!     that reads the requirement.

use anthill_core::eval::{Interpreter, Value};

/// Two `Mon[T = Int64]` with no default between them, whose answers differ; a callee with
/// one named requirement to hand a requirement on to, and one with an unnamed requirement.
const DECLS: &str = r#"
  import anthill.prelude.{Int64, String, Bool}
  import anthill.prelude.Numeric.{sub, add, mul}

  sort Mon
    sort T = ?
    operation combine(a: T, b: T) -> T
  end
  sort Sum
    provides Mon[T = Int64]
    operation combine(a: Int64, b: Int64) -> Int64 = add(a, b)
  end
  sort Product
    provides Mon[T = Int64]
    operation combine(a: Int64, b: Int64) -> Int64 = mul(a, b)
  end
  sort Via
    sort T = ?
    requires M: Mon[T]
    operation via(a: T, b: T) -> T = Mon.combine(a, b)
  end
  sort Anon
    sort T = ?
    requires Mon[T]
    operation via(a: T, b: T) -> T = Mon.combine(a, b)
  end
"#;

fn program(ns: &str, body: &str) -> String {
    format!("namespace {ns}\n{DECLS}\n{}end\n", body.replace("NS", ns))
}

/// A `Driver` whose `run` is `call`.
fn driver(call: &str) -> String {
    format!("  sort Driver\n    operation run() -> Int64 =\n      {call}\n  end\n")
}

/// The ticket's sort — two named requirements on `Mon` at `T` — with `members` as its
/// operations.
fn semi_of(members: &str) -> String {
    format!(
        "  sort Semi\n    sort T = ?\n    requires Plus: Mon[T]\n    requires Times: Mon[T]\n{members}  end\n"
    )
}

/// The ticket's sort with `mulAdd`'s body as given, and a `Driver` whose `run` is `call`.
fn semi(ns: &str, body: &str, call: &str) -> String {
    program(
        ns,
        &format!(
            "{}{}",
            semi_of(&format!("    operation mulAdd(a: T, b: T, c: T) -> T = {body}\n")),
            driver(call)
        ),
    )
}

/// Call a nullary operation on a FRESH interpreter — `interp_for` panics on a dirty load,
/// so a value here is also a clean-load assertion.
fn drive(src: &str, entry: &str) -> i64 {
    let mut interp: Interpreter = crate::common::interp_for(src);
    match interp.call(entry, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{entry}: expected an Int64, got {other:?}"),
    }
}

fn run(ns: &str, src: &str) -> i64 {
    drive(src, &format!("{ns}.Driver.run"))
}

use crate::common::{assert_refused_naming, load_errors_of};

/// The four provider pairs, and `mulAdd(2, 3, 4)` under each: `2 × 3`, then `+ 4`, is 10;
/// `2 + 3`, then `× 4`, is 20.
const PAIRS: [(&str, &str, i64); 4] = [
    ("sp", "Plus = Sum, Times = Product", 10),
    ("ps", "Plus = Product, Times = Sum", 20),
    ("ss", "Plus = Sum, Times = Sum", 9),
    ("pp", "Plus = Product, Times = Product", 24),
];

/// A call through each name, the same two calls written in full, and each handed on to a
/// callee under its name.
const DOTTED: &str = "Plus.combine(Times.combine(a, b), c)";
const BRACKET: &str = "Mon.combine[Mon = Plus](Mon.combine[Mon = Times](a, b), c)";
const FORWARD: &str = "Via.via[T = T, M = Plus](Via.via[T = T, M = Times](a, b), c)";

// ── The ticket's rows ────────────────────────────────────────────────

/// THE TICKET'S PROGRAM. `Semi.mulAdd[T = Int64, Plus = Sum, Times = Product](2, 3, 4)` is
/// 10 and 20 with the two swapped, its body written through the names: a call selects a
/// provider for each of the two, and each call of the body reads its own.
#[test]
fn a_call_through_a_requirements_name_reads_that_requirement() {
    for (tag, bracket, expected) in PAIRS {
        let ns = format!("wi50zmn.dotted.{tag}");
        assert_eq!(
            run(&ns, &semi(&ns, DOTTED, &format!("Semi.mulAdd[T = Int64, {bracket}](2, 3, 4)"))),
            expected,
            "`[{bracket}]`",
        );
    }
}

/// THE CALL IN FULL: `Plus.combine(a, b)` is `Mon.combine[Mon = Plus](a, b)` — the bracket
/// key of the call's own dispatch, its value the requirement's name where it was a witness
/// sort.
#[test]
fn the_call_written_in_full_is_the_same_call() {
    for (tag, bracket, expected) in PAIRS {
        let ns = format!("wi50zmn.bracket.{tag}");
        assert_eq!(
            run(&ns, &semi(&ns, BRACKET, &format!("Semi.mulAdd[T = Int64, {bracket}](2, 3, 4)"))),
            expected,
            "`[{bracket}]`",
        );
    }
}

/// EACH IS HANDED ON UNDER ITS OWN NAME to a callee that names the requirement it takes:
/// `Via.via[T = T, M = Plus]`. The forward was there (WI-20260923-WN9P8) and found the
/// caller's slot by the name's declaration; with one entry for the two names both found
/// the one dictionary.
#[test]
fn each_of_the_two_is_handed_on_under_its_own_name() {
    for (tag, bracket, expected) in PAIRS {
        let ns = format!("wi50zmn.forward.{tag}");
        assert_eq!(
            run(&ns, &semi(&ns, FORWARD, &format!("Semi.mulAdd[T = Int64, {bracket}](2, 3, 4)"))),
            expected,
            "`[{bracket}]`",
        );
    }
}

/// A CALLEE'S UNNAMED REQUIREMENT TAKES ONE OF THE TWO BY ITS NAME: `Anon` requires
/// `Mon[T]` under no name, so there is no parameter of it to bind, and `[Mon = Plus]` —
/// the sort's short name, the caller's requirement — is what says which dictionary it is
/// handed. `2 + 3` under `Plus = Sum`, `2 × 3` under `Times = Product`.
#[test]
fn a_callees_unnamed_requirement_takes_one_by_its_name() {
    let call = "Semi.mulAdd[T = Int64, Plus = Sum, Times = Product](2, 3, 4)";
    for (name, expected) in [("Plus", 5), ("Times", 6)] {
        let ns = format!("wi50zmn.anon.{}", name.to_lowercase());
        assert_eq!(
            run(&ns, &semi(&ns, &format!("Anon.via[T = T, Mon = {name}](a, b)"), call)),
            expected,
            "`Anon.via[T = T, Mon = {name}]`",
        );
    }
}

/// A CALL THAT DOES NOT SAY WHICH IS REFUSED, NAMING BOTH — it is not read from the first
/// written. A call of the spec's operation by its qualified name; the same call written as
/// a method of its argument; and a callee whose unnamed requirement the two both cover.
#[test]
fn a_call_that_names_neither_is_refused() {
    let call = "Semi.mulAdd[T = Int64, Plus = Sum, Times = Product](2, 3, 4)";
    for (tag, body) in [
        ("qualified", "Mon.combine(Mon.combine(a, b), c)"),
        ("method", "a.combine(b)"),
    ] {
        let ns = format!("wi50zmn.unsaid.{tag}");
        assert_refused_naming(
            &load_errors_of(&semi(&ns, body, call)),
            &[
                &format!("a call of {ns}.Mon.combine that two requirements of the enclosing declaration cover"),
                "`Plus` and `Times`",
                "write `Plus.combine(…)` or `Times.combine(…)`",
                "`Mon.combine[Mon = Plus](…)` in full",
            ],
            &format!("the goal names neither ({tag})"),
        );
    }
    let ns = "wi50zmn.unsaid.callee";
    assert_refused_naming(
        &load_errors_of(&semi(ns, "Anon.via[T = T](a, b)", call)),
        &[
            &format!("of `{ns}.Anon` cannot be supplied for call to `{ns}.Anon.via`"),
            "the enclosing declaration states two requirements that cover it, `Plus` and `Times`",
            "write `[Mon = Plus]` or `[Mon = Times]` in the call's brackets",
        ],
        "a callee's unnamed requirement, and two that cover it",
    );
    // A callee's NAMED requirement left unwritten is the same question, and the key the
    // refusal names is the callee's own name for it — the forward.
    let ns = "wi50zmn.unsaid.callee.named";
    assert_refused_naming(
        &load_errors_of(&semi(ns, "Via.via[T = T](a, b)", call)),
        &[
            &format!("cannot be supplied for call to `{ns}.Via.via`"),
            "the enclosing declaration states two requirements that cover it, `Plus` and `Times`",
            "write `[M = Plus]` or `[M = Times]` in the call's brackets",
        ],
        "a callee's named requirement left unwritten, and two that cover it",
    );
}

// ── Where the two may be declared ────────────────────────────────────

/// AN OPERATION'S OWN TWO are two as a sort's are — proposal 058 §4's `biFold` — on a
/// member of a sort and on an operation of a namespace: selected by name at the call, and
/// read by name in the body, in either spelling. A body that names neither is refused.
#[test]
fn an_operations_own_two_requirements_are_two() {
    let bifold = |indent: &str, body: &str| {
        format!(
            "{indent}operation biFold[T](a: T, b: T, c: T) -> T\n{indent}  \
             requires plus: Mon[T], times: Mon[T]\n{indent}  = {body}\n"
        )
    };
    let dotted = "plus.combine(times.combine(a, b), c)";
    let in_full = "Mon.combine[Mon = plus](Mon.combine[Mon = times](a, b), c)";
    for (tag, bracket, expected) in [
        ("sp", "plus = Sum, times = Product", 10),
        ("ps", "plus = Product, times = Sum", 20),
        ("ss", "plus = Sum, times = Sum", 9),
    ] {
        for (spelling, body) in [("dotted", dotted), ("full", in_full)] {
            let ns = format!("wi50zmn.op.member.{spelling}.{tag}");
            assert_eq!(
                run(
                    &ns,
                    &program(
                        &ns,
                        &format!(
                            "  sort Use\n{}  end\n{}",
                            bifold("    ", body),
                            driver(&format!("Use.biFold[T = Int64, {bracket}](2, 3, 4)"))
                        )
                    )
                ),
                expected,
                "a member's own two, `[{bracket}]`, {spelling}",
            );
        }
        let ns = format!("wi50zmn.op.free.{tag}");
        assert_eq!(
            run(
                &ns,
                &program(
                    &ns,
                    &format!(
                        "{}{}",
                        bifold("  ", dotted),
                        driver(&format!("biFold[T = Int64, {bracket}](2, 3, 4)"))
                    )
                )
            ),
            expected,
            "a namespace's operation's own two, `[{bracket}]`",
        );
    }
    let ns = "wi50zmn.op.unsaid";
    assert_refused_naming(
        &load_errors_of(&program(
            ns,
            &format!(
                "  sort Use\n{}  end\n{}",
                bifold("    ", "Mon.combine(Mon.combine(a, b), c)"),
                driver("Use.biFold[T = Int64, plus = Sum, times = Product](2, 3, 4)")
            ),
        )),
        &["two requirements of the enclosing declaration cover", "`plus` and `times`"],
        "an operation's own two, and a call that names neither",
    );
}

/// A SORT'S REQUIREMENT AND ONE ITS OPERATION STATES UNDER ANOTHER NAME are two: `m` on
/// the sort, `n` on the operation, both `Mon[T = HT]`.
#[test]
fn a_sorts_and_an_operations_under_two_names_are_two() {
    let decl = "
  sort Holder
    sort HT = ?
    requires m: Mon[T = HT]
    operation fold3(a: HT, b: HT, c: HT) -> HT requires n: Mon[T = HT] =
      m.combine(n.combine(a, b), c)
  end
";
    for (tag, bracket, expected) in [("sp", "m = Sum, n = Product", 10), ("ps", "m = Product, n = Sum", 20)] {
        let ns = format!("wi50zmn.cross.{tag}");
        assert_eq!(
            run(
                &ns,
                &program(
                    &ns,
                    &format!("{decl}{}", driver(&format!("Holder.fold3[HT = Int64, {bracket}](2, 3, 4)")))
                )
            ),
            expected,
            "`[{bracket}]`",
        );
    }
}

/// AN OPERATION MAY STAND ABOVE THE `requires` IT READS: which sort a name requires is
/// read off the sort's own lines, wherever in its body they are.
#[test]
fn an_operation_written_above_the_requires_lines_reads_them() {
    let ns = "wi50zmn.above";
    let src = program(
        ns,
        &format!(
            "  sort Semi\n    sort T = ?\n    operation mulAdd(a: T, b: T, c: T) -> T = {DOTTED}\n    \
             requires Plus: Mon[T]\n    requires Times: Mon[T]\n  end\n{}",
            driver("Semi.mulAdd[T = Int64, Plus = Sum, Times = Product](2, 3, 4)")
        ),
    );
    assert_eq!(run(ns, &src), 10);
}

/// THE OPERATION A NAME REACHES DOES NOT FOLLOW WHICH SORT IS DECLARED FIRST. `Rich`
/// declares `combine` and provides `Base`, which declares it too; `O.combine(a, b)` under
/// `requires O: Rich[T]` is `Rich`'s own, written above `Rich` or below it.
#[test]
fn the_operation_a_name_reaches_does_not_follow_declaration_order() {
    let rich = "
  sort Base
    sort T = ?
    operation combine(a: T, b: T) -> T
  end
  sort Rich
    sort T = ?
    provides Base[T = T]
    operation combine(a: T, b: T) -> T
  end
  sort RSum
    provides Rich[T = Int64]
    operation combine(a: Int64, b: Int64) -> Int64 = add(a, b)
  end
";
    let user = "
  sort Use
    sort T = ?
    requires O: Rich[T]
    operation f(a: T, b: T) -> T = O.combine(a, b)
  end
";
    for (tag, first, second) in [("spec.first", rich, user), ("user.first", user, rich)] {
        let ns = format!("wi50zmn.order.{tag}");
        let src = program(&ns, &format!("{first}{second}{}", driver("Use.f[T = Int64, O = RSum](2, 3)")));
        assert_eq!(run(&ns, &src), 5, "{tag}");
    }
}

/// A NAME IS READ WHEREVER THE DECLARATION'S BODY IS WRITTEN: inside a lambda, through a
/// `let`, by a sibling the body calls, and in a secondary entry at the sort's address —
/// which is another block than the one the `requires` lines stand in.
#[test]
fn a_name_is_read_wherever_the_body_is_written() {
    let call = "Semi.mulAdd[T = Int64, Plus = Sum, Times = Product](2, 3, 4)";
    for (tag, extra, body, expected) in [
        (
            "lambda",
            "    operation ap(f: (x: T) -> T, x: T) -> T = f(x)\n",
            "ap(lambda (x: T) -> Plus.combine(Times.combine(x, b), c), a)",
            10,
        ),
        ("let", "", "let p = Times.combine(a, b)\n      Plus.combine(p, c)", 10),
        (
            "sibling",
            "    operation twice(a: T) -> T = Plus.combine(a, a)\n",
            "twice(Times.combine(a, b))",
            12,
        ),
    ] {
        let ns = format!("wi50zmn.where.{tag}");
        let members = format!("{extra}    operation mulAdd(a: T, b: T, c: T) -> T = {body}\n");
        assert_eq!(
            run(&ns, &program(&ns, &format!("{}{}", semi_of(&members), driver(call)))),
            expected,
            "{tag}",
        );
    }
    let entry = "  namespace Semi\n    operation extra(a: T, b: T) -> T = Times.combine(a, b)\n  end\n";
    let sort = semi_of(&format!("    operation mulAdd(a: T, b: T, c: T) -> T = {DOTTED}\n"));
    for (tag, first, second) in [("below", sort.as_str(), entry), ("above", entry, sort.as_str())] {
        let ns = format!("wi50zmn.where.entry.{tag}");
        let src = program(
            &ns,
            &format!(
                "{first}{second}{}",
                driver("Semi.extra[T = Int64, Plus = Sum, Times = Product](2, 3)")
            ),
        );
        assert_eq!(
            run(&ns, &src),
            6,
            "a secondary entry's operation, read through `Times` — the entry written {tag} the sort",
        );
    }
}

/// A WITNESS WITH TWO REQUIREMENTS OF ONE SORT AT ONE TYPE takes a provider for each
/// where it is selected: `[Mon = Both[A = Sum, B = Product]]` (058 §3.3's bracket value),
/// and its member reads each by its name — `2 + 4` and `3 × 5`.
#[test]
fn a_witness_with_two_requirements_takes_a_provider_for_each() {
    let decl = "
  sort Pt
    entity pt(x: Int64, y: Int64)
  end
  sort Both
    requires A: Mon[T = Int64]
    requires B: Mon[T = Int64]
    provides Mon[T = Pt]
    operation combine(p: Pt, q: Pt) -> Pt = Pt.pt(x: A.combine(p.x, q.x), y: B.combine(p.y, q.y))
  end
  sort Use
    operation go(p: Pt, q: Pt) -> Pt requires Mon[T = Pt] = Mon.combine(p, q)
  end
";
    for (tag, value, expected) in [
        ("sp", "Both[A = Sum, B = Product]", 615),
        ("ps", "Both[A = Product, B = Sum]", 808),
    ] {
        let ns = format!("wi50zmn.witness.{tag}");
        let call = format!(
            "let r = Use.go[Mon = {value}](Pt.pt(x: 2, y: 3), Pt.pt(x: 4, y: 5))\n      add(mul(r.x, 100), r.y)"
        );
        assert_eq!(
            run(&ns, &program(&ns, &format!("{decl}{}", driver(&call)))),
            expected,
            "`[Mon = {value}]`",
        );
    }
}

// ── The two in a value's type ────────────────────────────────────────

/// `SemiV`, a sort with values: the two requirements, a constructor, and `mulAdd` over a
/// value. `ops` are the `Driver`'s own operations, `call` its `run`.
fn semiv(ns: &str, ops: &str, call: &str) -> String {
    program(
        ns,
        &format!(
            "  sort SemiV
    sort T = ?
    requires Plus: Mon[T]
    requires Times: Mon[T]
    entity sv(a: T, b: T, c: T)
    operation mulAdd(s: Self) -> T = match s case sv(a, b, c) -> Plus.combine(Times.combine(a, b), c)
    operation make(a: T, b: T, c: T) -> Self = sv(a: a, b: b, c: c)
  end
  sort Driver
    import NS.SemiV.{{sv, mulAdd}}
{ops}    operation run() -> Int64 =
      {call}
  end
"
        ),
    )
}

/// THE TWO CARRIED BY A VALUE'S TYPE answer the same at a call that writes neither:
/// `SemiV[T = Int64, Plus = Sum, Times = Product]` is a type, and a value of it carries two
/// providers. Written where the value is built, in a result type, in a `let`'s annotation,
/// on the receiver and on the constructor; read by a direct call, by a method call, by the
/// operation used as a function value, and by a generic signature that forwards each under
/// a name of its own. And one in the bracket with the other carried by the type.
#[test]
fn the_two_carried_by_a_values_type_answer_the_same() {
    for (tag, bracket, expected) in [PAIRS[0], PAIRS[1]] {
        let t = format!("SemiV[T = Int64, {bracket}]");
        let mk = format!("    operation mk() -> {t} = sv(a: 2, b: 3, c: 4)\n");
        let relay = format!(
            "{mk}    operation relay[E, A, B](s: SemiV[T = E, Plus = A, Times = B]) -> E\n      \
             requires A: Mon[T = E], B: Mon[T = E]\n      = SemiV.mulAdd(s)\n"
        );
        let ap = format!("{mk}    operation ap(f: (s: {t}) -> Int64, x: {t}) -> Int64 = f(x)\n");
        let rows: [(&str, &str, String); 9] = [
            ("built", "", format!("let s = SemiV.make[T = Int64, {bracket}](2, 3, 4)\n      SemiV.mulAdd(s)")),
            ("result", &mk, "SemiV.mulAdd(mk())".to_string()),
            ("let", "", format!("let s: {t} = sv(a: 2, b: 3, c: 4)\n      SemiV.mulAdd(s)")),
            ("receiver", "", format!("{t}.mulAdd(sv(a: 2, b: 3, c: 4))")),
            ("constructor", "", format!("SemiV.mulAdd(sv[T = Int64, {bracket}](a: 2, b: 3, c: 4))")),
            ("method", &mk, "mk().mulAdd()".to_string()),
            ("relay", &relay, "relay(mk())".to_string()),
            ("eta", &ap, "ap(mulAdd, mk())".to_string()),
            ("mixed", &mk, "SemiV.mulAdd[Times = TIMES](mk())".to_string()),
        ];
        for (row, ops, call) in rows {
            // The bracket's `Times` is the type's, so the two agree.
            let times = bracket.rsplit("Times = ").next().unwrap();
            let ns = format!("wi50zmn.intype.{row}.{tag}");
            assert_eq!(
                run(&ns, &semiv(&ns, ops, &call.replace("TIMES", times))),
                expected,
                "{row}, `{t}`",
            );
        }
    }
}

/// ONE SELECTED AND THE OTHER LEFT OUT: the other is a requirement of its own, decided as
/// a call that selects nothing decides it. At `Cell`, which has a `Mon` of its own beside
/// the witness `CellAlt`, the one left out is the carrier's own — `(2 + 3) × 4` with
/// `Plus = CellAlt` selected, `(2 × 3) + 4` with `Times = CellAlt`. At `Int64`, where
/// `Sum` and `Product` have no default between them, the call is refused for the one left
/// out, under its name.
#[test]
fn one_selected_and_the_other_left_out_is_decided_on_its_own() {
    let cells = "
  sort Cell
    entity cell(n: Int64)
    provides Mon[T = Cell]
    operation combine(a: Cell, b: Cell) -> Cell = cell(n: add(a.n, b.n))
  end
  sort CellAlt
    provides Mon[T = Cell]
    operation combine(a: Cell, b: Cell) -> Cell = Cell.cell(n: mul(a.n, b.n))
  end
";
    let members = format!("    operation mulAdd(a: T, b: T, c: T) -> T = {DOTTED}\n");
    for (tag, bracket, expected) in [("plus", "Plus = CellAlt", 20), ("times", "Times = CellAlt", 10)] {
        let ns = format!("wi50zmn.leftout.default.{tag}");
        let call = format!(
            "Semi.mulAdd[T = Cell, {bracket}](Cell.cell(n: 2), Cell.cell(n: 3), Cell.cell(n: 4)).n"
        );
        assert_eq!(
            run(&ns, &program(&ns, &format!("{cells}{}{}", semi_of(&members), driver(&call)))),
            expected,
            "`[{bracket}]`, the other the carrier's own",
        );
    }
    for (tag, bracket, left_out) in [("one", "Plus = Sum", "Times"), ("none", "", "Plus")] {
        let ns = format!("wi50zmn.leftout.{tag}");
        let comma = if bracket.is_empty() { "" } else { ", " };
        assert_refused_naming(
            &load_errors_of(&semi(&ns, DOTTED, &format!("Semi.mulAdd[T = Int64{comma}{bracket}](2, 3, 4)"))),
            &[
                &format!("requirement `{left_out}: {ns}.Mon[T = anthill.prelude.Int64]` of `{ns}.Semi`"),
                "is ambiguous among providers",
                &format!("{ns}.Sum"),
                &format!("{ns}.Product"),
            ],
            &format!("`[{bracket}]`: `{left_out}` left out, and two providers"),
        );
    }
}

// ── What a name does not do ──────────────────────────────────────────

/// THE NAME SAYS WHICH REQUIREMENT, NOT THAT IT FITS: `Plus` is `Mon[T]`, and a call at
/// `Int64` is not at `T` — refused where it is written, as the same call naming no
/// requirement is not read from `requires Mon[T]` (WI-414). And a WITNESS a call selects
/// in the body outranks both requirements: `Mon.combine[Mon = Sum](a, b)` is 5 whatever
/// the two were given.
#[test]
fn a_name_says_which_requirement_and_not_that_it_fits() {
    let call = "Semi.mulAdd[T = Int64, Plus = Sum, Times = Product](2, 3, 4)";
    let ns = "wi50zmn.wrongtype";
    let members = format!(
        "    operation mulAdd(a: T, b: T, c: T) -> T = {DOTTED}\n    \
         operation bad(a: T) -> Int64 = Plus.combine(1, 2)\n"
    );
    assert_refused_naming(
        &load_errors_of(&program(ns, &format!("{}{}", semi_of(&members), driver(call)))),
        &[
            &format!("`Plus` is `requires Plus: {ns}.Mon[T = {ns}.Semi.T]`"),
            &format!("which is not the instance of {ns}.Mon this call of {ns}.Mon.combine is at"),
        ],
        "`Plus.combine(1, 2)` under `requires Plus: Mon[T]`",
    );
    let ns = "wi50zmn.witness";
    let members = format!(
        "    operation mulAdd(a: T, b: T, c: T) -> T = {DOTTED}\n    \
         operation w(a: Int64, b: Int64) -> Int64 = Mon.combine[Mon = Sum](a, b)\n"
    );
    assert_eq!(
        run(
            ns,
            &program(
                ns,
                &format!(
                    "{}{}",
                    semi_of(&members),
                    driver("Semi.w[T = Int64, Plus = Product, Times = Product](2, 3)")
                )
            )
        ),
        5,
        "a witness selected at the call, under two requirements given `Product`",
    );
}

/// A NAME REACHES THE OPERATIONS ITS REQUIREMENT'S DICTIONARY ANSWERS, and no other: a
/// member neither the required sort nor one it provides declares is the qualified name it
/// was written as, which resolves to nothing.
///
/// CONTROL — passes either way, under every back-out in this file's table and in
/// WI-20261013-0K8WD's: with the name not read at all, `Plus.unit` is that same name.
#[test]
fn a_name_that_reaches_no_such_operation_is_refused() {
    let call = "Semi.mulAdd[T = Int64, Plus = Sum, Times = Product](2, 3, 4)";
    let ns = "wi50zmn.nomember";
    let members = format!(
        "    operation mulAdd(a: T, b: T, c: T) -> T = {DOTTED}\n    \
         operation u() -> T = Plus.unit()\n"
    );
    assert_refused_naming(
        &load_errors_of(&program(ns, &format!("{}{}", semi_of(&members), driver(call)))),
        &["Plus.unit", "unknown functor"],
        "`Mon` declares no `unit`",
    );
}

/// TWO REQUIREMENTS ON A SORT THAT PROVIDES THE ONE AN OPERATION IS DECLARED ON:
/// `requires A: Ord[T]` beside `requires B: Ord[T]`, and `compare`, which is `WeakOrd`'s —
/// an `Ord` dictionary holds a `WeakOrd` one. Each is read through its name, in either
/// spelling, and handed to a callee that requires `WeakOrd`; `"bob"` against `"amyy"` is
/// `-1` by length and `1` by reverse length. A call that names neither is refused naming
/// both, where it is the operation's own call, a method call, or a callee's requirement:
/// the walk by the goal would descend the first.
#[test]
fn a_name_reaches_what_its_requirements_dictionary_holds() {
    let decl = "
  import anthill.prelude.{Ord, WeakOrd}
  sort ByLength
    provides Ord[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(a.length(), b.length())
  end
  sort RevLength
    provides Ord[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(b.length(), a.length())
  end
  sort Cmp
    sort T = ?
    requires WeakOrd[T]
    operation c(a: T, b: T) -> Int64 = WeakOrd.compare(a, b)
  end
  sort Sorted
    sort T = ?
    requires A: Ord[T]
    requires B: Ord[T]
    operation cmp(a: T, b: T) -> Int64 = BODY
  end
";
    let call = r#"Sorted.cmp[T = String, A = ByLength, B = RevLength]("bob", "amyy")"#;
    let src = |ns: &str, body: &str| program(ns, &format!("{}{}", decl.replace("BODY", body), driver(call)));
    for (tag, body, expected) in [
        ("dotted.a", "A.compare(a, b)", -1),
        ("dotted.b", "B.compare(a, b)", 1),
        ("full.a", "WeakOrd.compare[WeakOrd = A](a, b)", -1),
        ("full.b", "WeakOrd.compare[WeakOrd = B](a, b)", 1),
        ("callee.a", "Cmp.c[T = T, WeakOrd = A](a, b)", -1),
        ("callee.b", "Cmp.c[T = T, WeakOrd = B](a, b)", 1),
    ] {
        let ns = format!("wi50zmn.beneath.{tag}");
        assert_eq!(run(&ns, &src(&ns, body)), expected, "`{body}`");
    }
    for (tag, body) in [("qualified", "WeakOrd.compare(a, b)"), ("method", "a.compare(b)")] {
        let ns = format!("wi50zmn.beneath.unsaid.{tag}");
        assert_refused_naming(
            &load_errors_of(&src(&ns, body)),
            &[
                "a call of anthill.prelude.WeakOrd.compare that two requirements of the enclosing declaration cover",
                "`A` and `B`",
                "write `A.compare(…)` or `B.compare(…)`",
            ],
            &format!("`{body}`, beneath two requirements on `Ord`"),
        );
    }
    let ns = "wi50zmn.beneath.unsaid.callee";
    assert_refused_naming(
        &load_errors_of(&src(ns, "Cmp.c[T = T](a, b)")),
        &[
            &format!("cannot be supplied for call to `{ns}.Cmp.c`"),
            "the enclosing declaration states two requirements that cover it, `A` and `B`",
            "write `[WeakOrd = A]` or `[WeakOrd = B]` in the call's brackets",
        ],
        "a callee's `WeakOrd[T]`, beneath two requirements on `Ord`",
    );
}

/// AND WHAT IT HOLDS FURTHER DOWN. `Eq` is two requirements beneath an `Ord` one —
/// `WeakOrd`, which `Ord` provides, requires it — and `PartialEq`, whose `eq` it is, three.
/// A name given at a callee's `Eq`, and at the key of `PartialEq.eq`'s own dispatch, reads
/// it there: `"bob"` is `"bob"`, and is not `"amyy"`.
///
/// `A.eq(…)` IS NOT A SPELLING OF THAT CALL. A name reaches what the required sort
/// declares or provides, as the qualified name `Ord.eq` would, and `Ord` reaches `eq`
/// past a `requires`. So the call that names neither is refused naming the spelling that
/// loads — the call in full — where one a name does reach is told the shorter one too
/// (`A.compare(…)`, in the row above).
#[test]
fn a_name_reaches_what_its_requirements_dictionary_holds_further_down() {
    let decl = "
  import anthill.prelude.{Ord, Eq, PartialEq}
  sort ByLength
    provides Ord[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(a.length(), b.length())
  end
  sort RevLength
    provides Ord[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(b.length(), a.length())
  end
  sort Same
    sort T = ?
    requires Eq[T]
    operation s(a: T, b: T) -> Bool = PartialEq.eq(a, b)
  end
  sort Sorted
    sort T = ?
    requires A: Ord[T]
    requires B: Ord[T]
    operation same(a: T, b: T) -> Int64 = if BODY then 1 else 0
  end
";
    let src = |ns: &str, body: &str, other: &str| {
        program(
            ns,
            &format!(
                "{}{}",
                decl.replace("BODY", body),
                driver(&format!(
                    r#"Sorted.same[T = String, A = ByLength, B = RevLength]("bob", "{other}")"#
                ))
            ),
        )
    };
    for (tag, body) in [
        ("callee.a", "Same.s[T = T, Eq = A](a, b)"),
        ("callee.b", "Same.s[T = T, Eq = B](a, b)"),
        ("full.a", "PartialEq.eq[PartialEq = A](a, b)"),
        ("full.b", "PartialEq.eq[PartialEq = B](a, b)"),
    ] {
        for (other, expected) in [("bob", 1), ("amyy", 0)] {
            let ns = format!("wi50zmn.deeper.{tag}.{other}");
            assert_eq!(run(&ns, &src(&ns, body, other)), expected, "`{body}`, \"bob\" and \"{other}\"");
        }
    }
    let ns = "wi50zmn.deeper.unsaid.callee";
    assert_refused_naming(
        &load_errors_of(&src(ns, "Same.s[T = T](a, b)", "bob")),
        &[
            &format!("cannot be supplied for call to `{ns}.Same.s`"),
            "the enclosing declaration states two requirements that cover it, `A` and `B`",
            "write `[Eq = A]` or `[Eq = B]` in the call's brackets",
        ],
        "a callee's `Eq[T]`, two requirements beneath two on `Ord`",
    );
    let ns = "wi50zmn.deeper.unsaid.qualified";
    let errs = load_errors_of(&src(ns, "PartialEq.eq(a, b)", "bob"));
    assert_refused_naming(
        &errs,
        &[
            "a call of anthill.prelude.PartialEq.eq that two requirements of the enclosing declaration cover",
            "`A` and `B`",
            "write `PartialEq.eq[PartialEq = A](…)` or `PartialEq.eq[PartialEq = B](…)`",
        ],
        "`PartialEq.eq(a, b)`, beneath two requirements on `Ord`",
    );
    assert!(
        !errs.join(" | ").contains("A.eq("),
        "the refusal names `A.eq(…)`, which does not load: {errs:?}",
    );
    let ns = "wi50zmn.deeper.dotted";
    assert_refused_naming(
        &load_errors_of(&src(ns, "A.eq(a, b)", "bob")),
        &["A.eq", "unknown functor"],
        "`A.eq(a, b)`: `Ord` neither declares `eq` nor provides the sort that does",
    );
}

/// A SPEC OPERATION WITH A BODY OF ITS OWN is read through a name as a body-less one is:
/// `Plus.twice(a)` runs the member `Plus`'s provider has for `twice` — `3 + 3` by `Sum`,
/// `3 × 3` by `Product` — in either spelling. A call of it that names neither is refused
/// naming both, where it loaded and ended `AmbiguousSpecOpDispatch` when it ran; and a
/// WITNESS at that key is a key that names nothing, as it was before a name could stand
/// there (the control — it passes with the name's reading backed out).
#[test]
fn a_spec_operation_with_a_body_is_read_through_a_name() {
    let decl = "
  sort Mon2
    sort T = ?
    operation combine(a: T, b: T) -> T
    operation twice(a: T) -> T = combine(a, a)
  end
  sort Sum2
    provides Mon2[T = Int64]
    operation combine(a: Int64, b: Int64) -> Int64 = add(a, b)
    operation twice(a: Int64) -> Int64 = add(a, a)
  end
  sort Product2
    provides Mon2[T = Int64]
    operation combine(a: Int64, b: Int64) -> Int64 = mul(a, b)
    operation twice(a: Int64) -> Int64 = mul(a, a)
  end
  sort Semi2
    sort T = ?
    requires Plus: Mon2[T]
    requires Times: Mon2[T]
    operation f(a: T) -> T = BODY
  end
";
    let src = |ns: &str, body: &str, bracket: &str| {
        program(
            ns,
            &format!(
                "{}{}",
                decl.replace("BODY", body),
                driver(&format!("Semi2.f[T = Int64, {bracket}](3)"))
            ),
        )
    };
    let sp = "Plus = Sum2, Times = Product2";
    let ps = "Plus = Product2, Times = Sum2";
    for (tag, body, bracket, expected) in [
        ("plus.sp", "Plus.twice(a)", sp, 6),
        ("times.sp", "Times.twice(a)", sp, 9),
        ("plus.ps", "Plus.twice(a)", ps, 9),
        ("full.sp", "Mon2.twice[Mon2 = Times](a)", sp, 9),
    ] {
        let ns = format!("wi50zmn.ownbody.{tag}");
        assert_eq!(run(&ns, &src(&ns, body, bracket)), expected, "`{body}`, `[{bracket}]`");
    }
    for (tag, body) in [("qualified", "Mon2.twice(a)"), ("method", "a.twice()")] {
        let ns = format!("wi50zmn.ownbody.unsaid.{tag}");
        assert_refused_naming(
            &load_errors_of(&src(&ns, body, sp)),
            &[
                &format!("a call of {ns}.Mon2.twice that two requirements of the enclosing declaration cover"),
                "`Plus` and `Times`",
                "write `Plus.twice(…)` or `Times.twice(…)`",
            ],
            &format!("`{body}`, an operation with a body of its own"),
        );
    }
    let ns = "wi50zmn.ownbody.witness";
    assert_refused_naming(
        &load_errors_of(&src(ns, "Mon2.twice[Mon2 = Sum2](a)", sp)),
        &["unknown type-param 'Mon2'"],
        "a witness at the key of an operation with a body of its own",
    );
}

// ── A line with no name ──────────────────────────────────────────────

/// A `requires` LINE WITH NO NAME BESIDE TWO NAMED ONES IT COULD STATE IS REFUSED where it
/// is written, naming both: a sort's own line, whichever of the three is written last, an
/// operation's line under its sort's two, and one in an operation's own list.
#[test]
fn a_line_with_no_name_beside_two_named_ones_is_refused() {
    let call = "Semi.mulAdd[T = Int64, Plus = Sum, Times = Product](2, 3, 4)";
    let named = ["    requires Plus: Mon[T]", "    requires Times: Mon[T]"];
    let unnamed = "    requires Mon[T]";
    for (tag, lines) in [
        ("last", [named[0], named[1], unnamed]),
        ("first", [unnamed, named[0], named[1]]),
        ("middle", [named[0], unnamed, named[1]]),
    ] {
        let ns = format!("wi50zmn.noname.sort.{tag}");
        let src = program(
            &ns,
            &format!(
                "  sort Semi\n    sort T = ?\n{}\n    operation mulAdd(a: T, b: T, c: T) -> T = {DOTTED}\n  end\n{}",
                lines.join("\n"),
                driver(call)
            ),
        );
        assert_refused_naming(
            &load_errors_of(&src),
            &[
                &format!("type mismatch in {ns}.Semi.requires"),
                &format!("`requires {ns}.Mon[T = {ns}.Semi.T]` with no name"),
                "beside the requirements `Plus` and `Times`",
            ],
            &format!("a sort's line with no name, written {tag}"),
        );
    }
    // A line that leaves unbound a parameter the two named ones bind is an entry of the
    // sort's own, and states either of them as well.
    let ns = "wi50zmn.noname.sort.leftopen";
    assert_refused_naming(
        &load_errors_of(&program(
            ns,
            "
  sort Two
    sort A = ?
    sort B = ?
    operation mix(a: A, b: A) -> A
  end
  sort Uses
    sort T = ?
    requires P: Two[A = T, B = String]
    requires Q: Two[A = T, B = String]
    requires Two[A = T]
    operation f(a: T, b: T) -> T = P.mix(a, b)
  end
",
        )),
        &[
            &format!("type mismatch in {ns}.Uses.requires"),
            "with no name",
            "beside the requirements `P` and `Q`",
        ],
        "a sort's line with no name that leaves a parameter of the two unbound",
    );
    let ns = "wi50zmn.noname.op.under";
    let members = format!("    operation mulAdd(a: T, b: T, c: T) -> T requires Mon[T] = {DOTTED}\n");
    assert_refused_naming(
        &load_errors_of(&program(ns, &format!("{}{}", semi_of(&members), driver(call)))),
        &[
            &format!("type mismatch in {ns}.Semi.mulAdd.requires"),
            "with no name",
            "beside the requirements `Plus` and `Times`",
        ],
        "an operation's line with no name, under its sort's two",
    );
    let ns = "wi50zmn.noname.op.own";
    assert_refused_naming(
        &load_errors_of(&program(
            ns,
            &format!(
                "  sort Use\n    operation biFold[T](a: T, b: T, c: T) -> T\n      \
                 requires plus: Mon[T], times: Mon[T], Mon[T]\n      \
                 = plus.combine(times.combine(a, b), c)\n  end\n{}",
                driver("Use.biFold[T = Int64, plus = Sum, times = Product](2, 3, 4)")
            ),
        )),
        &[
            &format!("type mismatch in {ns}.Use.biFold.requires"),
            "with no name",
            "beside the requirements `plus` and `times`",
        ],
        "a line with no name in an operation's own list of three",
    );
}

/// A LINE WITH NO NAME STATES THE REQUIREMENT THE LINE BESIDE IT NAMES WHERE THE BINDING
/// HOLDS A VALUE TOO. `Mon[T = Buf[T = Int64, N = 3]]` rides another carrier than a plain
/// type does, and the two lines are still one requirement, `Times`, whichever is written
/// first: a call that names none and a call through the name both read the provider
/// selected under the name — `2 + 3` by `BSum`, `2 × 3` by `BProduct`.
#[test]
fn a_line_with_no_name_states_the_named_one_at_a_binding_that_holds_a_value() {
    let decl = "
  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end
  sort BSum
    provides Mon[T = Buf[T = Int64, N = 3]]
    operation combine(a: Buf[T = Int64, N = 3], b: Buf[T = Int64, N = 3]) -> Buf[T = Int64, N = 3] =
      Buf.buf(v: add(a.v, b.v))
  end
  sort BProduct
    provides Mon[T = Buf[T = Int64, N = 3]]
    operation combine(a: Buf[T = Int64, N = 3], b: Buf[T = Int64, N = 3]) -> Buf[T = Int64, N = 3] =
      Buf.buf(v: mul(a.v, b.v))
  end
  sort SemiB
LINES
    operation unnamed(a: Buf[T = Int64, N = 3], b: Buf[T = Int64, N = 3]) -> Int64 = Mon.combine(a, b).v
    operation named(a: Buf[T = Int64, N = 3], b: Buf[T = Int64, N = 3]) -> Int64 = Times.combine(a, b).v
  end
  sort Mk
    operation two() -> Buf[T = Int64, N = 3] = Buf.buf(v: 2)
    operation three() -> Buf[T = Int64, N = 3] = Buf.buf(v: 3)
  end
";
    let with_name = "    requires Times: Mon[T = Buf[T = Int64, N = 3]]\n";
    let with_none = "    requires Mon[T = Buf[T = Int64, N = 3]]\n";
    for (order, lines) in [
        ("named.first", format!("{with_name}{with_none}")),
        ("unnamed.first", format!("{with_none}{with_name}")),
    ] {
        for (member, provider, expected) in [
            ("unnamed", "BSum", 5),
            ("unnamed", "BProduct", 6),
            ("named", "BSum", 5),
            ("named", "BProduct", 6),
        ] {
            let ns = format!("wi50zmn.noname.held.{order}.{member}.{}", provider.to_lowercase());
            let call = format!("SemiB.{member}[Times = {provider}](Mk.two(), Mk.three())");
            assert_eq!(
                run(&ns, &program(&ns, &format!("{}{}", decl.replace("LINES\n", &lines), driver(&call)))),
                expected,
                "`{call}`, the lines written {order}",
            );
        }
    }
}

/// WHICH REQUIREMENT A LINE STATES DOES NOT TURN ON HOW ITS BINDING IS WRITTEN. `Money` is
/// `Int64`, and a binding written through the alias rides another carrier than the type
/// written out — each line an occurrence of its own. Two names at `Mon[T = Money]`, or one
/// at `Money` and one at `Int64`, are two requirements of one sort at one type, each with
/// its provider (`2 + 4` and `3 × 5`, and the two swapped); and a line with no name at
/// `Money` states the one beside it, whichever is written first.
///
/// Told apart by identity — a term's id, an occurrence's address — the second line was a
/// requirement of its own that no fact held: its name was lost, "a requirement slot whose
/// position in that sort's dictionary chain could not be established".
#[test]
fn which_requirement_a_line_states_does_not_turn_on_how_its_binding_is_written() {
    let both = "
  sort Money = Int64
  sort Pt
    entity pt(x: Int64, y: Int64)
  end
  sort Both
    requires A: Mon[T = FIRST]
    requires B: Mon[T = SECOND]
    provides Mon[T = Pt]
    operation combine(p: Pt, q: Pt) -> Pt = Pt.pt(x: A.combine(p.x, q.x), y: B.combine(p.y, q.y))
  end
  sort Use
    operation go(p: Pt, q: Pt) -> Pt requires Mon[T = Pt] = Mon.combine(p, q)
  end
";
    for (tag, first, second) in [
        ("alias.alias", "Money", "Money"),
        ("alias.plain", "Money", "Int64"),
        ("plain.alias", "Int64", "Money"),
    ] {
        for (order, value, expected) in [
            ("sp", "Both[A = Sum, B = Product]", 615),
            ("ps", "Both[A = Product, B = Sum]", 808),
        ] {
            let ns = format!("wi50zmn.written.two.{tag}.{order}");
            let call = format!(
                "let r = Use.go[Mon = {value}](Pt.pt(x: 2, y: 3), Pt.pt(x: 4, y: 5))\n      add(mul(r.x, 100), r.y)"
            );
            let decl = both.replace("FIRST", first).replace("SECOND", second);
            assert_eq!(
                run(&ns, &program(&ns, &format!("{decl}{}", driver(&call)))),
                expected,
                "`A: Mon[T = {first}]`, `B: Mon[T = {second}]`, `[Mon = {value}]`",
            );
        }
    }
    let one = "
  sort Money = Int64
  sort SemiA
LINES
    operation unnamed(a: Int64, b: Int64) -> Int64 = Mon.combine(a, b)
    operation named(a: Int64, b: Int64) -> Int64 = Times.combine(a, b)
  end
";
    let with_name = "    requires Times: Mon[T = Money]\n";
    let with_none = "    requires Mon[T = Money]\n";
    for (order, lines) in [
        ("named.first", format!("{with_name}{with_none}")),
        ("unnamed.first", format!("{with_none}{with_name}")),
    ] {
        for (member, provider, expected) in [
            ("unnamed", "Sum", 5),
            ("unnamed", "Product", 6),
            ("named", "Product", 6),
        ] {
            let ns = format!("wi50zmn.written.one.{order}.{member}.{}", provider.to_lowercase());
            let call = format!("SemiA.{member}[Times = {provider}](2, 3)");
            assert_eq!(
                run(&ns, &program(&ns, &format!("{}{}", one.replace("LINES\n", &lines), driver(&call)))),
                expected,
                "`{call}`, the lines written {order}",
            );
        }
    }
}

// ── Where else two requirements could be read by their order ────────

/// A REQUIREMENT STATED AGAIN UNDER NO NAME, AND A NAME OF THE CALLER'S GIVEN AT ITS KEY.
/// `Holder` names `m: Mon[T = HT]` and its `fold3` states `Mon[T = HT]` again, so the
/// sort's short name is a key of the one requirement `m`; `[Mon = Plus]` written in
/// `Semi` hands it the caller's `Plus`. The callee's own name for it is then that
/// parameter — the call is the one `[m = Plus]` writes — and nothing is searched for:
/// `(2 + 3) + 4` through `Plus`, `(2 × 3) × 4` through `Times`.
#[test]
fn a_name_given_at_the_key_of_a_restated_requirement_is_handed_on() {
    let holder = "
  sort Holder
    sort HT = ?
    requires m: Mon[T = HT]
    operation fold3(a: HT, b: HT, c: HT) -> HT requires Mon[T = HT] = Mon.combine(Mon.combine(a, b), c)
  end
";
    let call = "Semi.mulAdd[T = Int64, Plus = Sum, Times = Product](2, 3, 4)";
    for (key, name, expected) in [("Mon", "Plus", 9), ("Mon", "Times", 24), ("m", "Plus", 9), ("m", "Times", 24)] {
        let ns = format!("wi50zmn.restated.{}.{}", key.to_lowercase(), name.to_lowercase());
        let members = format!(
            "    operation mulAdd(a: T, b: T, c: T) -> T = Holder.fold3[HT = T, {key} = {name}](a, b, c)\n"
        );
        assert_eq!(
            run(&ns, &program(&ns, &format!("{holder}{}{}", semi_of(&members), driver(call)))),
            expected,
            "`Holder.fold3[HT = T, {key} = {name}]`",
        );
    }
}

/// A GOAL MET WHILE ANOTHER IS RESOLVED has no call to name a requirement at. `BoxM`
/// provides `Mon` at a box of `E` where `Mon[T = E]` holds; `Mon.combine` of two boxes of
/// `T`, written in `Semi`, is neither `Plus` nor `Times` — it is `BoxM`'s, and `BoxM`'s
/// own requirement at `T` is answered by both. Read from the first written it followed
/// the order of two `requires` lines; it is refused, naming both.
///
/// The control beside it: one requirement, and the same call answers by its provider.
#[test]
fn a_goal_met_inside_a_resolution_is_not_read_from_the_first_of_two() {
    let boxes = "
  sort Box2
    sort B = ?
    entity box2(inner: B)
  end
  sort BoxM
    sort E = ?
    requires Mon[T = E]
    provides Mon[T = Box2[B = E]]
    operation combine(a: Box2[B = E], b: Box2[B = E]) -> Box2[B = E] =
      Box2.box2(inner: Mon.combine(a.inner, b.inner))
  end
";
    let body = "    operation both(a: T, b: T) -> T = Mon.combine(Box2.box2(inner: a), Box2.box2(inner: b)).inner\n";
    let ns = "wi50zmn.subgoal.two";
    assert_refused_naming(
        &load_errors_of(&program(
            ns,
            &format!(
                "{boxes}{}{}",
                semi_of(body),
                driver("Semi.both[T = Int64, Plus = Sum, Times = Product](2, 3)")
            ),
        )),
        &[
            "the enclosing declaration states two requirements that answer",
            "`Plus` and `Times`",
        ],
        "`BoxM`'s own `Mon[T = E]` at `T`, under two requirements that answer it",
    );
    for (provider, expected) in [("Sum", 5), ("Product", 6)] {
        let ns = format!("wi50zmn.subgoal.one.{}", provider.to_lowercase());
        let one = format!(
            "  sort One\n    sort T = ?\n    requires Plus: Mon[T]\n{}  end\n",
            body
        );
        assert_eq!(
            run(
                &ns,
                &program(
                    &ns,
                    &format!("{boxes}{one}{}", driver(&format!("One.both[T = Int64, Plus = {provider}](2, 3)")))
                )
            ),
            expected,
            "one requirement, `Plus = {provider}`",
        );
    }
}

/// A REFUSAL NAMES THE REQUIREMENTS OF THE OPERATION IT IS IN. `f` and `g` each state two
/// requirements on `Mon[T = Int64]`, under names of their own, and each calls
/// `Mon.combine` of two boxes of `Int64` — a goal met inside `BoxM`'s resolution, refused
/// naming both. The two calls ask one goal of one operation under frames that differ in
/// their names alone, and the answer to the first is remembered by its frame (a goal with
/// no parameter in it is): with the name left out of what a frame entry is compared by,
/// `g` was told of `p` and `q`.
#[test]
fn a_refusal_names_the_requirements_of_its_own_operation() {
    let ns = "wi50zmn.subgoal.names";
    let body = "Mon.combine(Box2.box2(inner: a), Box2.box2(inner: b)).inner";
    let src = program(
        ns,
        &format!(
            "
  sort Box2
    sort B = ?
    entity box2(inner: B)
  end
  sort BoxM
    sort E = ?
    requires Mon[T = E]
    provides Mon[T = Box2[B = E]]
    operation combine(a: Box2[B = E], b: Box2[B = E]) -> Box2[B = E] =
      Box2.box2(inner: Mon.combine(a.inner, b.inner))
  end
  sort Two
    operation f(a: Int64, b: Int64) -> Int64 requires p: Mon[T = Int64], q: Mon[T = Int64] = {body}
    operation g(a: Int64, b: Int64) -> Int64 requires r: Mon[T = Int64], s: Mon[T = Int64] = {body}
  end
"
        ),
    );
    let errs = load_errors_of(&src);
    assert_refused_naming(
        &errs,
        &[
            "the enclosing declaration states two requirements that answer",
            "`p` and `q`",
            "`r` and `s`",
        ],
        "two operations of one sort, each with two requirements under names of its own",
    );
    assert_eq!(errs.len(), 2, "one refusal for each operation: {errs:?}");
}

/// A SLOT A PARAMETER LEAVES UNWRITTEN, WHERE THE ARGUMENT'S TYPE BINDS IT TO A PARAMETER
/// OF THE CALLER'S. `one(s: OneV[T = E])` takes `M` from its argument; `relay` hands it
/// an `s: OneV[T = E, M = A]` and holds `A` and `B` on `Mon[T = E]`. The dictionary handed
/// on is the one the argument's type says — `A`'s, or `B`'s where it says `B` — and not
/// the first of the two that covers the goal.
#[test]
fn a_slot_the_arguments_type_binds_to_a_callers_name_is_that_names() {
    let decl = "
  sort OneV
    sort T = ?
    requires M: Mon[T]
    entity ov(a: T, b: T)
    operation fold(s: Self) -> T = match s case ov(a, b) -> Mon.combine(a, b)
  end
  sort Driver
    import NS.OneV.{ov}
    operation mk() -> OneV[T = Int64, M = MADE] = ov(a: 2, b: 3)
    operation one[E](s: OneV[T = E]) -> E = OneV.fold(s)
    operation relay[E, A, B](s: OneV[T = E, M = NAME]) -> E
      requires A: Mon[T = E], B: Mon[T = E]
      = one(s)
    operation run() -> Int64 = relay[A = Sum, B = Product](mk())
  end
";
    for (name, made, expected) in [("A", "Sum", 5), ("B", "Product", 6)] {
        let ns = format!("wi50zmn.argbinds.{}", name.to_lowercase());
        assert_eq!(
            run(&ns, &program(&ns, &decl.replace("NAME", name).replace("MADE", made))),
            expected,
            "`s: OneV[T = E, M = {name}]`",
        );
    }
}

/// THE NAME IS HELD TO WHAT THE QUALIFIED NAME IS HELD TO: an `internal` operation of
/// the required sort is refused through a requirement's name as it is by its own.
#[test]
fn an_internal_operation_is_not_reached_through_a_name() {
    let decl = |body: &str| {
        format!(
            "
  sort Hid
    sort T = ?
    operation shown(a: T) -> T
    internal operation raw(a: T) -> T
  end
  sort User
    sort T = ?
    requires H: Hid[T]
    operation f(a: T) -> T = {body}
  end
"
        )
    };
    for (tag, body) in [("name", "H.raw(a)"), ("qualified", "Hid.raw(a)")] {
        let ns = format!("wi50zmn.internal.{tag}");
        assert_refused_naming(
            &load_errors_of(&program(&ns, &decl(body))),
            &["internal", "raw"],
            &format!("`{body}`, an internal operation of `Hid`"),
        );
    }
    let ns = "wi50zmn.internal.shown";
    assert!(
        load_errors_of(&program(ns, &decl("H.shown(a)"))).is_empty(),
        "the operation beside it that is not internal loads",
    );
}

/// A CALL THAT NAMES A REQUIREMENT IS HELD TO IT WHERE THE CARRIER IS HIGHER-KINDED TOO.
/// `unit(42)` at a result typed `Option[T = Int64]` fills `F` to `Option` and is answered
/// by `Option`'s own provision; written `M.unit(42)` under `requires M: CpsMonad[F = G]`
/// it names a requirement at `G`, which is not the call's — refused, where the carrier's
/// provision answered and the name was dropped.
///
/// TWO THINGS HOLD IT, each backed out. The carrier's branch stands aside for a call that
/// names a requirement. And a `requires` keeps the binding it writes for a parameter
/// declared in the sort's header: `F[T]` of `sort CpsMonad[F[T]]` was no entry of the
/// sort's parameter list, so `requires M: CpsMonad[F = G]` was stored as `CpsMonad` at no
/// binding — a requirement that covered a call at any carrier, and with the branch out of
/// the way `M.unit(42)` was read from `M`'s dictionary for a result typed `Option`.
#[test]
fn a_name_is_held_to_the_call_at_a_higher_kinded_carrier() {
    let src = |ns: &str, body: &str| {
        format!(
            "namespace {ns}
  import anthill.prelude.Option.{{none, some}}
  import anthill.prelude.{{Option, Int64}}

  sort CpsMonad[F[T]]
    operation unit[A](a: A) -> F[T = A]
  end
  operation optionUnit[A](a: A) -> Option[T = A] = some(a)

  sort Uses[G[T]]
    requires M: CpsMonad[F = G]
    operation mk() -> Option[T = Int64] = {body}
  end
end

namespace anthill.prelude.Option
  import {ns}.CpsMonad
  provides CpsMonad[F = Self, unit = {ns}.optionUnit]
end
"
        )
    };
    let ns = "wi50zmn.hk.named";
    assert_refused_naming(
        &load_errors_of(&src(ns, "M.unit(42)")),
        &["`M` is `requires M: ", "which is not the instance of"],
        "`M.unit(42)` at a result that fills `F` to `Option`",
    );
    let ns = "wi50zmn.hk.unnamed";
    assert!(
        load_errors_of(&src(ns, "CpsMonad.unit(42)")).is_empty(),
        "the same call naming no requirement is the carrier's own",
    );
}

// ── Not reached ──────────────────────────────────────────────────────

/// NOT REACHED — a parameter typed at the sort with NEITHER slot written. One slot left
/// unwritten is read off the argument's type (WI-20260921-EE0EP); two of one sort at one
/// type are two slots a body's goal cannot tell apart, and the call through the parameter
/// is refused, as it is for two parameters of one carrier. The repair it names — each
/// slot under a name of the signature's own — is the `relay` row of
/// [`the_two_carried_by_a_values_type_answer_the_same`].
///
/// It holds what is, and no back-out of this ticket's fails it; of WI-20261013-0K8WD's
/// one does, a restated line given a place of its own (`place_of_requirement`).
#[test]
fn a_parameter_that_writes_neither_slot_is_refused() {
    let ns = "wi50zmn.neither";
    let ops = "    operation mk() -> SemiV[T = Int64, Plus = Sum, Times = Product] = sv(a: 2, b: 3, c: 4)\n    \
               operation any(s: SemiV[T = Int64]) -> Int64 = SemiV.mulAdd(s)\n";
    assert_refused_naming(
        &load_errors_of(&semiv(ns, ops, "any(mk())")),
        &[
            &format!("reads the named requirement slot `Times: {ns}.Mon` off a parameter whose type omits it"),
            "or another slot of that carrier at the same type",
        ],
        "`s: SemiV[T = Int64]`, both slots unwritten",
    );
}

// ── Controls ─────────────────────────────────────────────────────────

/// CONTROL. ONE requirement under ONE name is read by a call that names it and by one
/// that does not: there is one to read. It fails where a name is not read at all — the
/// fixture writes `Plus.combine` — which is two back-outs, a name at a spec key not taken
/// for a selection and the dotted callee left a qualified name; and under no other.
#[test]
fn one_named_requirement_is_read_with_or_without_its_name() {
    let decl = "
  sort One
    sort T = ?
    requires Plus: Mon[T]
    operation named(a: T, b: T) -> T = Plus.combine(a, b)
    operation unnamed(a: T, b: T) -> T = Mon.combine(a, b)
  end
";
    for (provider, expected) in [("Sum", 5), ("Product", 6)] {
        for member in ["named", "unnamed"] {
            let ns = format!("wi50zmn.control.one.{member}.{}", provider.to_lowercase());
            let call = format!("One.{member}[T = Int64, Plus = {provider}](2, 3)");
            assert_eq!(
                run(&ns, &program(&ns, &format!("{decl}{}", driver(&call)))),
                expected,
                "`{call}`",
            );
        }
    }
}

/// CONTROL — passes under every back-out of this ticket's. Two requirements at TWO types
/// are told apart by the call's own element, and a call that names neither reads the one
/// at its type, as WI-20261013-0K8WD left it: `K` and `V`, each read at a value of its
/// own. It is that ticket's, and fails with its key backed out — a selection read back by
/// its sort alone (`selection_for_slot`).
#[test]
fn two_requirements_at_two_types_need_no_name() {
    let decl = "
  sort Two
    sort K = ?
    sort V = ?
    requires OK: Mon[T = K]
    requires OV: Mon[T = V]
    operation keys(a: K, b: K) -> K = Mon.combine(a, b)
    operation vals(a: V, b: V) -> V = Mon.combine(a, b)
  end
";
    for (member, expected) in [("keys", 5), ("vals", 6)] {
        let ns = format!("wi50zmn.control.twotypes.{member}");
        let call = format!("Two.{member}[K = Int64, V = Int64, OK = Sum, OV = Product](2, 3)");
        assert_eq!(
            run(&ns, &program(&ns, &format!("{decl}{}", driver(&call)))),
            expected,
            "`{call}`",
        );
    }
}

/// CONTROL — passes under every back-out of this ticket's. A provider written in the
/// bracket against the one the argument's type says for the same name is a type error at
/// the argument: the two write one parameter. Of WI-20261013-0K8WD's back-outs one fails
/// it, a restated line given a place of its own (`place_of_requirement`).
#[test]
fn a_provider_selected_against_the_values_type_is_a_type_error() {
    let ns = "wi50zmn.control.against";
    let ops = "    operation mk() -> SemiV[T = Int64, Plus = Sum, Times = Product] = sv(a: 2, b: 3, c: 4)\n";
    assert_refused_naming(
        &load_errors_of(&semiv(ns, ops, "SemiV.mulAdd[Times = Sum](mk())")),
        &["expected SemiV[T = Int64, Plus = Sum, Times = Sum]", "Times = Product]"],
        "`Times = Sum` in the bracket, `Times = Product` in the argument's type",
    );
}
