//! WI-20260929-0RP29 — THE DECLARATION RULE, clause by clause: a member must take every
//! argument list its spec takes (`docs/kernel-language.md`, *Backing conformance*, "The member
//! must take every argument list the spec takes"; `typing/signature.rs`
//! `member_narrower_than_spec`). Found by that ticket's fourth /code-review: the rule as first
//! written decided by UNIFICATION (an equality) against arguments it built too coarsely, so it
//! refused members wider than their spec, and admitted members that tie what the spec leaves
//! open. Each row was measured wrong on the version before the pass that added it (the sections
//! below: the fourth review's rows, the fifth's, the sixth's, the seventh's, the eighth's).
//!
//! The spec's arguments are read as a call writes them, in a substitution of their own: THE
//! RECEIVER per operation (the self-receiver, receiving the declaring sort; else the
//! carrier-param receiver, receiving the sort its binding names; an operation with neither is
//! compared all the same, the member's instance bound by its first position), the carrier at its
//! own parameters MET with what the receiver's type writes; THIS INSTANCE every reference to the
//! declaring sort a binding leaves bare or part-written, as the sort's own operations read it
//! (§3's tie — an independent instance is WRITTEN, `Car[V = ?]`; INTERIM until
//! WI-20261001-80ZV8 makes a bare sort fresh `?` slots everywhere), a foreign sort's unwritten
//! slot any type, each binding read once per spec parameter; another parameter typed by the spec
//! any provider; a spec operation's type
//! parameter the receiver leaves unbound, and an unwritten slot, any type; a projection as the
//! call reads it, over any argument. The member keeps its own variables, bound by unifying with
//! the spec's arguments, a foreign sort's slot fresh per occurrence. The verdict is SUBTYPING, the
//! return's included — every return, read as the call reads it.
//!
//! Every row that can RUNS and answers a number; a row asserting a refusal names its cause.
//!
//! ── SINCE WI-20261001-80ZV8 (proposal 070 §1.3) ──────────────────────────────
//!
//! A SORT'S BARE NAME INSIDE ITS OWN DEFINITION NO LONGER MEANS THIS INSTANCE — it is the
//! sort at `?`, any instance, as everywhere (and was, for one day, a load error) — so the
//! fixtures here write what each bare name MEANT, and the row comments, which quote the
//! declarations as they first stood (`both(s: Car, o: Car)`, `put(s: Sp, …)`, `T = Car`),
//! describe a spelling the fixture no longer has:
//!
//!  * the carrier inside the carrier, and a spec's own RECEIVER, are `Self` — this instance;
//!  * another parameter a spec types by itself, which the bare name read as any provider,
//!    is the spec at `?` (`o: Sp[T = ?]`);
//!  * a binding the rows call "bare" is `T = Self`, and an independent one is still
//!    `T = Car[V = ?]`.
//!
//! The verdicts are the ones the rows pinned, with the refusal texts printing the member's
//! `Self` as the carrier at its own parameters (`o: Car[V = V]`). THE BACK-OUT LEDGER BELOW
//! WAS MEASURED ON THE BARE SPELLING and has not been taken again part by part: the rows the
//! change of spelling moved, and what each of them fails under now, are in the ledgers of
//! `wi_80zv8_bare_own_sort_test` and `wi_80zv8_written_wildcard_test`. Where a comment
//! credits "§3's tie" for a verdict, the tie is now the written `Self`. The arms that read a
//! reference to the declaring sort with a slot LEFT OUT as this instance WENT AT STAGE (e) of
//! proposal 070: such a reference is any instance, read as a slot left out is on every other
//! sort, and the loader no longer writes a `?` into it. A ledger part below that names one of
//! them (`self_references_at_own_parameters`, the bare arms of `is_this_instance`, the
//! unifier's canonical channel, `enforce_member_tie`) can no longer be backed out.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! MEASURED, each part of `member_narrower_than_spec` backed out present but wrong, over the
//! three `wi_0rp29_*` files, `wi1076_self_representing_spec_carrier_test`, `wi_ekwdc`,
//! `wi_s8cbv` and `wi614` (the parts of the fallback, the join and the call re-keys are in the
//! other two files' ledgers):
//!
//!  1. THE MEMBER'S FOREIGN SORTS PER OCCURRENCE — unexpanded. 3 FAIL:
//!     [`a_member_taking_two_bare_foreign_sorts_is_not_narrower`], the main file's
//!     `two_bare_foreign_parameters_of_the_override_are_two` (whose member the rule then
//!     refuses), and `wi1076…::a_spec_with_both_a_carrier_param_and_a_self_receiver_keeps_its_binding`.
//!  2. THE VERDICT BY SUBTYPING — by unification. 3 FAIL: the three `wider` rows.
//!  3. THE RECEIVER'S WRITTEN ARGUMENTS — ignored. 1 FAILS:
//!     [`a_receiver_written_with_arguments_fixes_them`].
//!  4. THE CARRIER PARAMETER'S BINDING MET BY THE INSTANCE — not met. 1 FAILS:
//!     [`a_carrier_parameter_bound_with_arguments_fits_a_member_writing_them`].
//!  5. WHAT STAYS OPEN RIGID — a written `?` left flexible. 1 FAILS:
//!     [`a_written_wildcard_in_a_carrier_binding_is_any_type`].
//!  6. THE RECEIVER PER OPERATION — decided once per spec. 2 FAIL: the two `per_operation` rows.
//!  7. ANOTHER SPEC-TYPED PARAMETER ANY PROVIDER — read as the receiver. 1 FAILS:
//!     [`another_parameter_typed_by_the_spec_is_any_provider`].
//!  8. AN UNWRITTEN SLOT OF THE SPEC ANY TYPE — a wildcard. 1 FAILS:
//!     [`an_unwritten_slot_of_a_spec_parameter_is_any_type`].
//!  9. THE SPEC OPERATION'S TYPE PARAMETERS RIGID — flexible. 1 FAILS:
//!     [`a_spec_operations_type_parameter_is_any_type`].
//! 10. THE REFUSAL'S KIND — the old message rule. 3 FAIL:
//!     [`a_receiver_written_with_arguments_fixes_them_control`],
//!     [`a_written_wildcard_in_a_carrier_binding_is_any_type`],
//!     [`another_parameter_typed_by_the_spec_is_any_provider`] — each names its kind.
//! 11. A SELF-RECEIVER'S OWN CARRIER PARAMETER (`receiving_of_provision`) — independent. 1 FAILS:
//!     [`a_self_receivers_own_carrier_parameter_is_its_instance`].
//! 12. RECEIVING, NOT TAKING — `spec_carrier_param` (a parameter any operation TAKES) as the
//!     self-receiver's carrier. 2 FAIL: [`a_binding_naming_the_carrier_is_an_independent_instance`]
//!     and the main file's `a_member_tied_tighter_than_its_spec_is_refused` (the tie admitted).
//! 13. THE RECEIVER AS THE INSTANCE — the written binding against a rigid instance, the rule as
//!     first written (parts 4 and this together). 2 FAIL:
//!     [`a_carrier_parameter_bound_with_arguments_fixes_them`] and the wildcard row.
//! 14. A MEMBER RECEIVER TYPED BY THE SPEC COMPARED AS THE SPEC'S TYPE — as the carrier. 1 FAILS:
//!     `wi1076…::a_spec_with_both_a_carrier_param_and_a_self_receiver_keeps_its_binding` — a
//!     WITNESS's member `joinTwo(a: Holder, …)`, which the relation does not see the witness's
//!     carrier `Box` fit.
//!
//! MEASURED for the fifth /code-review's fixes, each part backed out present but wrong over the
//! same files:
//!
//! 15. A RECEIVED PARAMETER FOUND THROUGH A BINDING NAMING THE CARRIER — through any binding. 1
//!     FAILS: [`the_received_parameter_is_found_past_a_sibling_parameter_typed_otherwise`].
//! 16. A WRITTEN RECEIVED BINDING IS THAT TYPE — read as this instance. 3 FAIL:
//!     [`two_received_parameters_at_two_written_instances_are_each_that_type`],
//!     [`a_received_parameter_written_with_arguments_is_not_this_instance`] and
//!     [`a_received_parameter_written_with_arguments_control`] (the member writing the binding
//!     then reads as narrower than the instance).
//! 16b. … AND IT DOES NOT CONSTRAIN THE SELF-RECEIVER — the rule before (part 16, the receiver's
//!     instance met by the binding). 3 FAIL: the first two of part 16 and
//!     [`a_received_parameter_written_with_arguments_does_not_narrow_the_self_receiver`].
//! 17. AN OPERATION WITH NO RECEIVER READS ITS RECEIVED PARAMETERS AS THIS INSTANCE — reads none.
//!     2 FAIL: the two `an_operation_with_no_receiver_…` rows.
//! 18. A SOLE PARAMETER IS RECEIVED (WI-1102's second rung) — not. 1 FAILS:
//!     [`an_operation_with_no_receiver_reads_this_instance_through_a_sole_parameter`].
//! 19. A SPEC-TYPED MEMBER RECEIVER AGAINST THE SPEC AT THIS PROVISION — the generic spec. 2
//!     FAIL: [`a_member_receiver_typed_by_the_spec_reads_the_provisions_bindings`] and its
//!     witness twin.
//! 20. THE MEMBER'S VARIABLES BOUND ALONG THE RELATION — left unbound. 2 FAIL:
//!     [`a_generic_member_wider_than_its_spec_is_not_narrower`] and its control, refused at
//!     parameter 2 instead of naming the tie at parameter 3.
//! 21. THE SPEC'S SIDE EXPANDED AT EVERY DEPTH, ON ANY CARRIER — at the top only. 2 FAIL:
//!     [`a_nested_unwritten_slot_of_a_spec_parameter_is_any_type`] and
//!     [`an_unwritten_slot_of_a_type_holding_a_value_is_any_type`].
//! 22. THE MEMBER'S SIDE EXPANDED AT EVERY DEPTH — at the top only. 1 FAILS:
//!     [`a_members_nested_bare_foreign_sorts_are_two`].
//! 23. A WRITTEN `?` ON THE SPEC'S SIDE RIGID — flexible. 1 FAILS:
//!     [`a_written_wildcard_outside_the_receiver_is_any_type`].
//! 24. A PROJECTION OVER THIS INSTANCE JUDGED AT DECLARATION — every one left to the call. 2
//!     FAIL: [`a_projection_over_the_receiver_is_judged_at_declaration`] and
//!     [`a_callback_row_beside_a_projection_is_judged_at_declaration`].
//! 25. THE RECEIVER'S REFUSAL AS THE SPEC WRITES IT — "fixes what the spec leaves open". 1
//!     FAILS: [`a_receiver_the_spec_writes_is_named_as_written`].
//! 26. THE SPEC'S OWN PARAMETERS A PROVISION LEAVES UNBOUND STAY WILDCARDS — made rigid with a
//!     written `?` (the first cut of part 23). 3 FAIL, measured over the whole suite: the three
//!     `wi_kxnex_provision_names_carrier_test` rows, each then refused twice (its own refusal of
//!     a provision naming no carrier, and the member read against "any type"); five guardians
//!     and qa provisions were refused beside the errors their tests expect.
//!
//! MEASURED for the sixth /code-review's fixes, each part backed out present but wrong over the
//! three `wi_0rp29_*` files and `wi_xzmgc_composed_carrier_param_test`:
//!
//! 27. A RECEIVER BINDING'S ROW SLOT NAMING ITS OWN ROW A ROW HOLDING THE LABEL — met by term
//!     unification. 1 FAILS: [`a_receiver_binding_naming_its_own_row_meets_the_instance`].
//! 28. A CIRCULAR RECEIVER BINDING REFUSED — the operation skipped. 1 FAILS:
//!     [`a_receiver_binding_naming_its_own_data_parameter_is_refused`].
//! 29. THE MEETING — the binding's references to the carrier's parameters read as variables of
//!     their own. 2 FAIL: that row (no longer circular) and its control (`W` then any type).
//! 30. THE OPERATION'S TYPE PARAMETERS FLEXIBLE IN THE RECEIVER'S MEETING — rigid first. 1 FAILS:
//!     [`a_self_receiver_written_with_an_operation_type_parameter_binds_it`].
//! 31. A WRITTEN RECEIVER ARGUMENT REACHES A PROVIDER BY ITS VARIANCE — by equality. 1 FAILS:
//!     [`a_written_receiver_argument_reaches_a_provider_by_its_variance`].
//! 32. THE RELATION'S DIRECTION IN `bind_member_vars_along` — never turned. 2 FAIL:
//!     [`a_callback_parameter_wider_by_width_fits_in_either_order`] and
//!     [`a_contravariant_binding_wider_by_width_fits`].
//! 33. WITHDRAWN by the seventh review (part 58): "an effect-row slot kept by the deep
//!     expansion". Its row, `a_bare_label_in_a_row_slot_is_not_expanded`, asserted a member
//!     taking a narrower row loads; a row slot's labels are read as sort applications now
//!     ([`a_label_in_a_row_slot_is_any_payload`]).
//! 34. THE PROJECTION READER — the call's reading alone. 112 FAIL across the three files: every
//!     gated member with a projection position is refused, its rigid-slotted instance unknown to
//!     the call's reading.
//! 35. A PROJECTION OVER ANY PROVIDER READ — skipped, "judged at the call". 1 FAILS:
//!     [`a_projection_over_any_provider_is_any_type`].
//! 36. THIS INSTANCE SLOT BY SLOT — any own parameter in any slot. 1 FAILS:
//!     [`a_permuted_received_binding_is_that_type`] ([`a_permuted_binding_is_not_this_instance`]
//!     passes, as its site says).
//! 37. EACH BINDING READ ONCE PER SPEC PARAMETER — per occurrence. 1 FAILS:
//!     [`one_binding_is_one_type_wherever_it_is_read`].
//! 38. THE RECEIVER'S SORT PER OPERATION — the witness criterion per provision. 3 FAIL:
//!     [`one_binding_is_one_type_wherever_it_is_read`] and two `wi_xzmgc` rows
//!     (`a_composed_element_parameter_is_not_dropped_as_the_carrier`,
//!     `a_self_providing_element_sort_is_not_read_as_the_carrier`).
//! 39. WITHDRAWN by the seventh review (part 47): "an operation the spec cannot dispatch
//!     skipped". The skip's premise was false — a spec call reaches a receiver-less member by its
//!     arguments, a bracket or a `requires` dictionary — and its one row,
//!     `an_operation_the_spec_cannot_dispatch_is_not_compared`, asserted its member loads without
//!     being compared; compared, it is the spec's
//!     ([`an_operation_with_no_receiver_reads_a_bare_binding_as_this_instance`]).
//! 40. A NESTED TIE NAMED AS ONE — `Other`. 1 FAILS: [`a_nested_tie_is_named_as_one`].
//! 41. THE TYPES AS COMPARED PRINTED — the declarations. 2 FAIL:
//!     [`a_projection_refusal_prints_the_type_compared`] and
//!     [`a_self_receiver_written_with_an_operation_type_parameter_binds_it`].
//! 42. AN ARROW'S ROW PRINTED — dropped. 1 FAILS: [`a_callback_refusal_prints_its_row`].
//! 43. THE MEMBER'S PARAMETERS BY THE SPEC'S NAMES, in this rule — by its own. 2 FAIL:
//!     [`a_row_naming_a_parameter_is_compared_by_the_specs_names`] and
//!     [`a_ground_row_naming_a_parameter_is_compared_by_the_specs_names`]; in the per-position
//!     comparison — by its own. 1 FAILS: the ground row.
//! 44. WITHDRAWN by the seventh review (part 50): "an unreceived binding at the carrier's own
//!     parameters independent". Its row asserted `both(s: Car, o: Car)` behind `T = Car[V = V]`
//!     refused; a binding naming the carrier is THIS instance now, received on or not, and the
//!     crash that row was written for is closed at the call instead (part 51).
//! 45. THE RETURN COMPARED — skipped. 1 FAILS: [`a_return_holding_a_projection_is_compared`].
//!     RE-MEASURED after the eighth pass made the rule compare EVERY return (part 59), over the
//!     316 rows named there: 8 FAIL — that row, the four refusals of part 59
//!     ([`a_return_holding_no_projection_is_compared`],
//!     [`a_return_at_a_carrier_binding_is_this_instance`],
//!     [`a_return_naming_an_operation_type_parameter_is_compared`] and the control
//!     [`a_return_naming_a_parameter_by_value_is_compared_by_the_specs_names_control`]),
//!     [`a_field_path_projection_is_compared_by_the_specs_names_control`], and two rows of
//!     `wi347_override_refinement_test` that expect a mismatched return reported
//!     (`a_mismatched_return_type_no_clause_reads_is_not_the_discharge_rules_business`,
//!     `an_impl_only_ensures_over_result_is_not_the_discharge_rules_business`).
//! 46. A PLAIN POSITION SKIPPED — compared. None fails, by design: an efficiency path, measured
//!     by the review's generators (the member rule 4.4x the fifth review's base on `Pair[A =
//!     List, B = Option]` positions, now below it).
//!
//! MEASURED for the seventh /code-review's fixes, over the three `wi_0rp29_*` files and
//! `wi_xzmgc_composed_carrier_param_test` (206 rows):
//!
//! 47. AN OPERATION WITH NO RECEIVER COMPARED — skipped unless the spec's sole parameter is bound
//!     to the declaring sort (the sixth pass's skip, put back). 4 FAIL:
//!     [`an_operation_with_no_receiver_is_compared`],
//!     [`an_operation_with_no_receiver_names_what_a_tie_is_tied_to`],
//!     [`a_requires_dictionary_reaches_an_operation_with_no_receiver`] and
//!     [`a_witness_operation_with_no_receiver_is_compared`] — each member loads.
//! 48. WHAT A TIE WITH NO RECEIVER IS TIED TO — "to the receiver". 1 FAILS:
//!     [`an_operation_with_no_receiver_names_what_a_tie_is_tied_to`].
//! 49. THE MEMBER'S INSTANCE BOUND BY ITS FIRST POSITION where no receiver fixes it — a rigid
//!     instance of its own (the fifth pass's reading). 3 FAIL:
//!     [`an_operation_with_no_receiver_is_compared_control`],
//!     [`an_operation_with_no_receiver_binds_the_members_instance_by_its_first_position`] (each
//!     refused at parameter 1) and [`an_operation_with_no_receiver_names_what_a_tie_is_tied_to`]
//!     (refused at parameter 1, not as the tie at parameter 2).
//! 50. A BINDING'S REFERENCE TO THE DECLARING SORT IS THIS INSTANCE (the interim reading: a
//!     `provides` clause reads the name as the sort's own operations do) — an independent
//!     instance, every binding. 6 FAIL: [`a_binding_naming_the_carrier_is_this_instance`],
//!     [`an_operation_with_no_receiver_reads_a_bare_binding_as_this_instance`], two earlier rows
//!     that read a RECEIVED binding so ([`a_self_receivers_own_carrier_parameter_is_its_instance`],
//!     [`the_received_parameter_is_found_past_a_sibling_parameter_typed_otherwise`]) and two of
//!     `wi_0rp29_call_binding_test` (`a_carrier_binding_is_the_receivers_instance_whether_or_not_received`,
//!     `a_received_bare_carrier_binding_is_the_receivers_instance_at_the_call_control`) — each
//!     tied member refused at its declaration.
//! 51. A SELF-RECEIVER CALL HOLDS A BINDING NAMING THE CARRIER — skipped, the argument held to
//!     nothing. 1 FAILS: [`a_binding_naming_the_carrier_holds_a_self_receiver_call_to_this_instance`]
//!     (both programs load).
//!
//! Then, over the same four files (228 rows):
//!
//! 52. A WRITTEN RECEIVER ARGUMENT'S FOREIGN SORT FRESH PER OCCURRENCE — met unexpanded. 1 FAILS:
//!     [`a_written_receiver_argument_is_fresh_per_occurrence`] (the member loads).
//! 53. THE OPERATION'S VARIABLES BOUND ALONG THE VARIANCE RELATION in the receiver's meeting —
//!     not bound. 1 FAILS: [`a_receiver_reached_by_variance_binds_the_operations_parameter`].
//! 54. THE RECEIVER BINDING'S FOREIGN SORTS EXPANDED — met as written. 1 FAILS:
//!     [`a_receiver_bindings_unwritten_slot_is_any_type`].
//! 55. A SUBSTITUTION BINDING A VARIABLE INSIDE ITSELF DETECTED (`binds_a_cycle`) — not looked
//!     for. The test binary ABORTS, its stack overflowed in
//!     [`a_receiver_binding_circular_around_another_parameter_is_refused`]
//!     ([`a_written_receiver_argument_admitting_no_receiver_is_not_reached`] overflows alike) —
//!     measured with those two rows alone, and with the CLI on their programs.
//! 56. A ROW SLOT THAT IS ANOTHER PARAMETER'S ROW READ AS THAT ROW — bound around it. 1 FAILS:
//!     [`a_row_slot_that_is_another_parameters_row_is_that_row`] (refused as circular).
//! 57. A BOUND SPEC PARAMETER'S VARIABLE READS ITS BINDING — left a wildcard. 2 FAIL:
//!     [`a_binding_naming_another_spec_parameter_reads_its_binding`] and
//!     [`a_callback_rows_tail_reads_the_provisions_row`].
//! 58. A ROW SLOT'S LABELS READ AS SORT APPLICATIONS (`expand_sorts_and_row_labels`) —
//!     kept as written. 1 FAILS: [`a_label_in_a_row_slot_is_any_payload`] (both spellings load).
//!
//! MEASURED for the seventh /code-review's findings 10, 12 and 15 (the eighth pass), each part
//! backed out present but wrong over the three `wi_0rp29_*` files,
//! `wi_xzmgc_composed_carrier_param_test` and `wi347_override_refinement_test` (316 rows):
//!
//! 59. EVERY RETURN COMPARED BY THE RULE — only one holding a projection, the per-position
//!     comparison judging the rest by the member's own names (the return's handling before this
//!     pass). 5 FAIL: [`a_return_holding_no_projection_is_compared`],
//!     [`a_return_at_a_carrier_binding_is_this_instance`],
//!     [`a_return_naming_an_operation_type_parameter_is_compared`] (each member loads),
//!     [`a_return_naming_a_parameter_by_value_is_compared_by_the_specs_names`] and
//!     [`a_member_no_spec_call_reaches_keeps_the_per_position_return`] (each verbatim member
//!     refused). With the per-position comparison left by the spec's names, the first three.
//! 60. THE RECEIVER'S MEETING AN EQUALITY — unification alone, which falls back to the subtype
//!     relation between two types holding no variable. 2 FAIL:
//!     [`a_provision_an_invariant_parameter_excludes_is_not_reached`] (the member refused for a
//!     receiver no call sends) and [`a_member_no_spec_call_reaches_keeps_the_per_position_return`]
//!     (its provision then read as reached, the refusal the rule's).
//! 61. THE PER-POSITION RETURN BY THE SPEC'S NAMES — by the member's own. 1 FAILS:
//!     [`a_member_no_spec_call_reaches_keeps_the_per_position_return`].
//! 62. A NEUTRAL PROJECTION'S FIELD-PATH RECEIVER RE-KEYED AT ITS HEAD (`rekeyed_neutral`,
//!     projection.rs) — a single reference only. 2 FAIL:
//!     [`a_field_path_projection_is_compared_by_the_specs_names`] and
//!     [`a_carrier_param_receivers_field_path_projection_is_compared`].
//! 63. THE RULE'S NEUTRAL OVER A FIELD OF ABSTRACT TYPE (`ProjectionReader::read`) — a single
//!     reference only, a path left to the call's reading. 1 FAILS:
//!     [`a_field_path_projection_over_an_abstract_field_is_the_same_projection`].
//! 64. A SPEC MEMBER THE PROVISION LEAVES UNBOUND READ AS ITS WILDCARD — left to the call's
//!     reading. 2 FAIL: [`a_projection_over_a_member_the_provision_leaves_unbound_is_a_wildcard`]
//!     and [`a_projection_over_a_member_the_provision_leaves_unbound_is_one_type`] (refused at
//!     parameter 2, as unreadable).
//! 65. THE RELATION ASKED OVER THE SPEC'S RETURN WITH ITS SLOTS LEFT UNWRITTEN — over the
//!     expanded one alone. 2 FAIL: [`a_member_returning_a_provider_of_the_specs_bare_sort_fits`]
//!     and `wi347_override_refinement_test::a_covariant_return_type_still_discharges_the_result_clause`.
//! 66. A REFUSAL'S SPEC SIDE READ THROUGH THE MEMBER'S SUBSTITUTION — as the spec side resolved
//!     it. 1 FAILS: [`a_projection_over_a_member_the_provision_leaves_unbound_is_one_type`] (the
//!     wildcard printed `?_`).
//! 67. THE MEMBER'S VARIABLES IN A SUBSTITUTION OF THEIR OWN (the sixth pass's split, measured
//!     here for finding 15) — started from the spec side's. 4 FAIL:
//!     [`a_receiver_binding_naming_its_own_row_meets_the_instance`],
//!     [`an_operation_with_no_receiver_binds_the_members_instance_by_its_first_position`],
//!     [`an_operation_with_no_receiver_is_compared_control`] and
//!     [`an_operation_with_no_receiver_names_what_a_tie_is_tied_to`].
//! 68. A PROJECTION OF THE CARRIER'S OWN PARAMETER READ AS THE RECEIVER'S SLOT (the sixth
//!     pass's reading, measured here for finding 15) — as the provision's binding of that name.
//!     2 FAIL: [`a_projection_reads_the_carriers_own_parameter_first`] and
//!     [`a_projection_over_a_carrier_param_receiver_reads_its_type_control`].
//!
//! Every row fails under at least one part but three rows of the sixth review and the
//! `_control`s named below. The three — [`a_wildcard_bound_to_a_member_variable_is_not_frozen`],
//! [`a_permuted_binding_is_not_this_instance`] and [`one_binding_is_one_type_for_a_witness`] —
//! fail under no single part measured here: each pins the tree the sixth review saw, whose rule
//! compared in ONE substitution (MEASURED with that tree's binary: each program refused there,
//! and answering 3, 1 and 43 since); part 67 is the nearest back-out of that split the present
//! code admits, and it fails four other rows. The `_control`s pass either way by design:
//! the RIGHTLY-typed members the rule must not refuse —
//! [`another_parameter_typed_by_the_spec_is_any_provider_control`],
//! [`a_binding_naming_the_carrier_is_an_independent_instance_control`],
//! [`a_spec_operations_type_parameter_is_any_type_control`] and
//! [`an_unwritten_slot_of_a_spec_parameter_is_any_type_control`] — and the WRONGLY-typed member
//! it must refuse whatever a part admits, [`a_member_taking_two_bare_foreign_sorts_is_not_narrower_control`].
//! The sixth review's rows add three controls passing under every part, as their sites say —
//! [`a_self_receiver_written_with_an_operation_type_parameter_binds_it_control`],
//! [`a_callback_parameter_wider_by_width_fits_control`] and
//! [`a_return_holding_a_projection_is_compared_control`] — and two rows NAMED controls that a
//! part fails, each said at its site: [`a_receiver_binding_naming_its_own_data_parameter_is_refused_control`]
//! (part 29) and [`a_projection_over_a_carrier_param_receiver_reads_its_type_control`] (part 68).
//! The seventh review's: [`a_requires_dictionary_reaches_an_operation_with_no_receiver_control`]
//! and [`a_witness_operation_with_no_receiver_is_compared_control`] under none (each pins that
//! the spec call REACHES the member), [`an_operation_with_no_receiver_is_compared_control`] under
//! part 49 only; [`a_binding_naming_the_carrier_at_a_wildcard_is_an_independent_instance`] and
//! its control under none (the independent instance a provision can still write); and the six
//! `_control`s of parts 52–58 under none, each a member as wide as its spec that the spec call
//! then RUNS.
//! The eighth pass's: [`a_return_holding_no_projection_is_compared_control`],
//! [`a_return_at_a_carrier_binding_is_this_instance_control`],
//! [`a_return_naming_an_operation_type_parameter_is_compared_control`],
//! [`a_provision_an_invariant_parameter_excludes_is_not_reached_control`] and
//! [`a_projection_over_a_member_the_provision_leaves_unbound_is_a_wildcard_control`] under none
//! — each a member the rule must admit, run through the spec call, or a refusal every reading
//! makes; [`a_return_naming_a_parameter_by_value_is_compared_by_the_specs_names_control`] and
//! [`a_field_path_projection_is_compared_by_the_specs_names_control`] under part 45 alone (no
//! return compared at all), as their sites say.
//! Three earlier controls DO fail under a part, as stated above and at their sites:
//! [`a_receiver_written_with_arguments_fixes_them_control`] (part 10),
//! [`a_received_parameter_written_with_arguments_control`] (part 16) and
//! [`a_generic_member_wider_than_its_spec_control`] (part 20).
//!
//! MEASURED for the eighth /code-review's findings (the ninth pass), each part backed out present
//! but wrong over the three `wi_0rp29_*` files, `wi_xzmgc_composed_carrier_param_test`,
//! `wi347_override_refinement_test` and `wi_f3fyj_value_in_type_binding_test` (434 rows). Where the
//! test PROCESS dies under a part — a stack overflow, which no harness catches — every row was run
//! in a process of its own:
//!
//! 69. THE RETURN'S VERDICT THE RELATION'S — unification's `true` taken for it. 2 FAIL:
//!     [`a_return_narrower_at_an_invariant_slot_is_refused`] and
//!     [`a_returned_function_narrower_in_its_parameter_is_refused`].
//! 70. THE MEMBER'S VARIABLES BOUND ALONG THE RELATION AT THE RETURN (`bind_member_vars_along`) —
//!     not bound. 1 FAILS: [`a_generic_members_wider_return_is_bound_along_the_relation`].
//! 71. AN UNWRITTEN RETURN SLOT WHOEVER PICKS IT'S (`expand_sorts_by_polarity`) — the
//!     member's to instantiate on both sides, as a parameter's. 4 FAIL:
//!     [`a_members_bare_return_is_a_type_the_caller_does_not_know`],
//!     [`a_provision_slot_a_parameter_reads_ties_the_return`],
//!     [`a_return_slot_tied_to_a_parameter_is_tied_by_the_member`] and
//!     [`a_returned_functions_parameter_turns_the_slots_over`].
//! 72. A PROVISION'S SLOT ONLY THE RETURN READS LEFT OPEN (`return_only`) — any type, as one a
//!     parameter reads. 2 FAIL: [`a_provision_slot_only_the_return_reads_is_the_members_to_pick`]
//!     and `wi_f3fyj_value_in_type_binding_test`'s `the_ground_binding_is_the_baseline` (the
//!     baseline `fresh(n) -> Buf[T = Int64]` behind `-> State`, `N` unwritten in both, is then
//!     refused).
//! 73. THE MEMBER HELD TO LEAVING SUCH A SLOT OPEN (`leaves_open`) — not held. 1 FAILS:
//!     [`a_member_fixing_a_slot_the_provision_leaves_open_is_refused`].
//! 74. UNREACHED ONLY WHERE THE RECEIVER'S TYPE IS CLOSED AS WRITTEN (`receiver_type_is_closed`) —
//!     whatever it writes. 1 FAILS:
//!     [`a_receiver_argument_the_call_does_not_check_leaves_the_member_reached`].
//! 75. A UNIFIER BINDING A VARIABLE INSIDE ITSELF DROPPED AT A PARAMETER (`binds_a_cycle`) —
//!     walked. The PROCESS dies: 1 DIES
//!     ([`a_unifier_binding_a_variable_inside_itself_is_refused_not_walked`]), and no other row
//!     fails. [`a_unifier_binding_a_variable_inside_itself_is_refused_not_walked_control`], which
//!     the same overflow once took, passes.
//! 76. A PROJECTION READ FROM THE PROVISION ITS RECEIVER'S DECLARATION NAMES
//!     (`ProjectionReader::read`) — from the provision under check, whatever the declaration. 4
//!     FAIL: [`a_specs_projection_over_a_carrier_typed_parameter_is_the_carriers_own`],
//!     [`a_witness_members_projection_is_read_as_its_receiver_is_declared`],
//!     [`the_rule_reads_a_projection_from_the_spec_its_receiver_is_declared_by`] and
//!     [`the_rule_reads_a_projection_from_the_spec_its_receiver_is_declared_by_at_the_return`].
//! 77. A WITNESS'S BINDING READ THROUGH ITS CARRIER VIEW AT THE RECEIVER PROJECTED (`witness_view`)
//!     — at the operation's receiver. 1 FAILS:
//!     [`a_witness_binding_is_read_at_the_receiver_projected`].
//! 78. A BINDING READ ONCE PER SPEC PARAMETER WHATEVER CARRIER ITS EXPANSION RIDES (the template) —
//!     one whose expansion is no term falls back to the binding unexpanded. 3 FAIL:
//!     [`a_binding_holding_a_braced_label_stays_in_the_template`],
//!     [`a_member_fixing_a_slot_the_provision_leaves_open_is_refused`] and
//!     [`a_return_slot_tied_to_a_parameter_is_tied_by_the_member`].
//! 79. A LABEL STANDING WHERE A ROW DOES THE ROW HOLDING IT, IN THE TEMPLATE
//!     (`row_parameter_binding_as_row`) — left a label. 1 FAILS:
//!     [`an_unbraced_row_binding_is_the_row_holding_it`].
//! 80. AN ARROW'S OWN ROW EXPANDED (`expand_row_labels` under an arrow, sort_alias.rs) — not
//!     expanded. 1 FAILS: [`an_arrows_own_row_is_expanded`].
//! 81. AN ALIAS'S WRITTEN ARGUMENTS EXPANDED (sort_alias.rs) — an alias kept as written. 1 FAILS:
//!     [`an_aliass_written_row_is_expanded`].
//! 82. TWO SIDES THAT PRINT ALIKE SAID SO — not said. 2 FAIL:
//!     [`a_provision_slot_a_parameter_reads_ties_the_return`] and
//!     [`an_arrows_own_row_is_expanded`].
//! 83. A PARAMETER'S VERDICT THE RELATION'S — unification's `true` taken for it. 1 FAILS:
//!     [`a_parameter_narrower_at_an_invariant_slot_is_refused_behind_a_projection`].
//! 84. THE PROVISION'S ANY-TYPES SEEDED INTO THE MEMBER'S SUBSTITUTION (`provision_any`) — not
//!     seeded. 4 FAIL: [`a_witness_parameter_is_no_type_a_member_fixes`] and the main file's
//!     `a_bracket_reaches_the_fallback_past_an_unreduced_return`,
//!     `an_overrides_own_type_parameter_is_bound_by_its_argument_control` and
//!     `the_fallback_keys_the_override_by_position` (the three of the main file each read an
//!     override's own type parameter off a provision's any-type).
//! 85. A LABEL IN A ROW SLOT THE ROW HOLDING IT, IN THE EXPANSION WALK (`row_holding_label`,
//!     sort_alias.rs) — left a label (the template's own parameter still read as a row). 1 FAILS:
//!     [`a_label_in_a_row_slot_is_one_row_however_it_is_braced`].
//! 86. A UNIFIER BINDING A VARIABLE INSIDE ITSELF DROPPED AT THE RETURN — taken. The PROCESS dies:
//!     1 DIES ([`a_return_unifying_only_through_itself_is_refused`]), and no other row fails.
//! 87. THE DECLARING SORT'S OWN PARAMETERS ANY TYPE, NOT AMONG THE PROVISION'S OPEN SLOTS
//!     (`declaring_own`) — left among them. 1 FAILS:
//!     [`a_witness_parameter_is_no_type_a_member_fixes`].
//! 88. A RETURN REFUSAL SAYING THAT THE MEMBER'S RETURN LEAVES A SLOT UNWRITTEN (`holds_rigid`) —
//!     not said. 1 FAILS: [`a_return_slot_tied_to_a_parameter_is_tied_by_the_member`].
//! 89. AN UNBOUND SPEC PARAMETER'S WILDCARD LEFT UNWRITTEN WHERE THE RELATION IS ASKED
//!     (`unwrite_wildcards`) — left written. 2 FAIL:
//!     [`a_member_returning_its_carrier_fits_a_view_over_an_unbound_parameter`] and
//!     [`a_member_returning_its_carrier_fits_a_view_whose_wildcard_met_its_own_variable`].
//! 90. A RECEIVER'S ARGUMENTS REPLACE ITS SORT'S PARAMETERS ONCE (`PatternSubst`, pattern.rs) — to
//!     a fixpoint. The PROCESS dies: 3 DIE
//!     ([`a_field_path_off_a_parameter_writing_its_sorts_own_parameter_is_replaced_once`],
//!     [`a_parameter_writing_its_sorts_own_parameter_is_replaced_once`] and
//!     [`a_parameter_writing_its_sorts_own_parameter_is_replaced_once_misfit`]), and no other row
//!     fails. The walker's own unit tests, `typing::tests::wi417_cycle_tests`:
//!     `walk_pattern_field_type_deep_replaces_a_parameter_once` dies as these do, and
//!     `walk_pattern_field_type_deep_keeps_an_arguments_own_parameter` — nothing cycles — FAILS
//!     without dying.
//! 91. A PROJECTION READS EACH ARGUMENT AS BOUND SO FAR (`resolve_recorded`) — as recorded when its
//!     position was compared. 4 FAIL: [`a_projection_reads_its_receiver_as_bound_so_far`],
//!     [`a_projection_reads_its_receiver_as_bound_so_far_misfit`],
//!     [`a_projection_reads_its_sorts_own_parameter_as_bound_so_far`] and
//!     [`a_projection_reads_its_sorts_own_parameter_as_bound_so_far_misfit`].
//!
//! Parts 87 and 90 TOGETHER — the declaring sort's parameter left open, and replaced to a fixpoint
//! — and the process dies again: 5 DIE, part 90's three and
//! [`a_witness_parameter_is_any_type_whoever_reads_it`] with its `_misfit`, which fail under no
//! single part (either part alone keeps `V` from being bound inside itself and walked); the same
//! five under 84 and 90 together.
//!
//! EARLIER PARTS RE-MEASURED, this pass having rewritten the code they back out:
//!   * part 59 (every return compared by the rule — only one holding a projection): 15 FAIL — its
//!     rows that drive a return holding no projection, this pass's return rows with them:
//!     [`a_member_fixing_a_slot_the_provision_leaves_open_is_refused`],
//!     [`a_members_bare_return_is_a_type_the_caller_does_not_know`],
//!     [`a_provision_slot_a_parameter_reads_ties_the_return`],
//!     [`a_return_at_a_carrier_binding_is_this_instance`],
//!     [`a_return_holding_no_projection_is_compared`],
//!     [`a_return_naming_a_parameter_by_value_is_compared_by_the_specs_names_control`],
//!     [`a_return_naming_an_operation_type_parameter_is_compared`],
//!     [`a_return_narrower_at_an_invariant_slot_is_refused`],
//!     [`a_return_slot_tied_to_a_parameter_is_tied_by_the_member`],
//!     [`a_return_unifying_only_through_itself_is_refused`],
//!     [`a_returned_function_narrower_in_its_parameter_is_refused`] and
//!     [`a_returned_functions_parameter_turns_the_slots_over`]; `wi347_override_refinement_test`'s
//!     `a_mismatched_return_type_no_clause_reads_is_not_the_discharge_rules_business` and
//!     `an_impl_only_ensures_over_result_is_not_the_discharge_rules_business`;
//!     `wi_f3fyj_value_in_type_binding_test`'s `a_wrong_member_return_is_refused`.
//!   * part 60 (the receiver's meeting an equality — unification alone): 2 FAIL — as before:
//!     [`a_member_no_spec_call_reaches_keeps_the_per_position_return`] and
//!     [`a_provision_an_invariant_parameter_excludes_is_not_reached`].
//!   * part 64 (an unbound spec member read as its wildcard — left to the call's reading): 4 FAIL —
//!     its two rows and two of this pass's:
//!     [`a_member_returning_its_carrier_fits_a_view_over_an_unbound_parameter`],
//!     [`a_projection_over_a_member_the_provision_leaves_unbound_is_a_wildcard`],
//!     [`a_projection_over_a_member_the_provision_leaves_unbound_is_one_type`] and
//!     [`a_unifier_binding_a_variable_inside_itself_is_refused_not_walked`].
//!   * part 65 (the relation asked over the spec's return with its slots left unwritten — over the
//!     expanded one alone): 4 FAIL — its two rows and the two of part 89:
//!     [`a_member_returning_a_provider_of_the_specs_bare_sort_fits`],
//!     [`a_member_returning_its_carrier_fits_a_view_over_an_unbound_parameter`],
//!     [`a_member_returning_its_carrier_fits_a_view_whose_wildcard_met_its_own_variable`] and
//!     `wi347_override_refinement_test`'s
//!     `a_covariant_return_type_still_discharges_the_result_clause`.
//!   * part 67 (the member's variables in a substitution of their own — started from the spec
//!     side's): 4 FAIL — as before: [`a_receiver_binding_naming_its_own_row_meets_the_instance`],
//!     [`an_operation_with_no_receiver_binds_the_members_instance_by_its_first_position`],
//!     [`an_operation_with_no_receiver_is_compared_control`] and
//!     [`an_operation_with_no_receiver_names_what_a_tie_is_tied_to`].
//!
//! Of this pass's 43 rows, every one fails or dies under at least one part but the two witness rows
//! above and eight `_control`s, each passing either way by design, as its site says:
//! [`a_returned_function_as_the_spec_writes_it_fits_control`],
//! [`a_members_bare_return_is_a_type_the_caller_does_not_know_control`],
//! [`a_returned_functions_parameter_turns_the_slots_over_control`],
//! [`a_receiver_argument_the_call_does_not_check_leaves_the_member_reached_control`],
//! [`a_unifier_binding_a_variable_inside_itself_is_refused_not_walked_control`],
//! [`the_rule_reads_a_projection_from_the_spec_its_receiver_is_declared_by_control`],
//! [`a_witness_parameter_is_no_type_a_member_fixes_control`] and
//! [`a_return_slot_tied_to_a_parameter_is_tied_by_the_member_control`].

use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64};

/// `sort App` running `go()`, appended to a program.
const APP: &str = r#"
  sort App
    entity app
    requires anthill.cli.Main
    operation main(args: List[String]) -> Int64 = go()
  end
"#;

/// A spec `Sp` (one parameter, `T`), the carrier `Car[V]` providing it at `provision`, the
/// spec operation `spec_op`, the member `member`, then `rest` (a `go()` among it).
fn car_program(ns: &str, spec_op: &str, provision: &str, member: &str, rest: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String, List, Option, Error}}
  import anthill.prelude.Option.{{some, none}}

  sort Animal
    entity cat(n: Int64)
    entity dog(n: Int64)
  end

  sort Sp
    sort T = ?
    {spec_op}
  end

  sort Car
    sort V = ?
    entity car(v: V)
    provides {provision}
    {member}
  end
{rest}{APP}end
"#
    )
}

// ── the member keeps its own variables: two bare foreign sorts are two ──────────

/// TWO BARE FOREIGN SORTS ARE TWO: `count2(s: Car, xs: List, ys: List)` behind
/// `count2(s: Sp, xs: List[T = T], ys: List[T = Int64])` takes lists of any two element types,
/// as a call reads it (WI-374 expands each bare `List` fresh). Unified as written, the two
/// shared `List`'s own `T`, bound `V` then `Int64`: refused "parameter 3 (`ys: List`) takes less
/// than the spec's". Runs to 2 + 3.
#[test]
fn a_member_taking_two_bare_foreign_sorts_is_not_narrower() {
    let ns = "wi0rp29mr.bare";
    let src = car_program(
        ns,
        "operation count2(s: Self, xs: List[T = T], ys: List[T = Int64]) -> Int64",
        "Sp[T = V]",
        "operation count2(s: Self, xs: List, ys: List) -> Int64 = List.length(xs) + List.length(ys)",
        r#"
  operation go() -> Int64 =
    let c: Car[V = String] = car(v: "k")
    Sp.count2(c, ["a", "b"], [1, 2, 3])
"#,
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(5));
}

/// … AND ITS CONTROL: a member FIXING a foreign sort's element the spec leaves open
/// (`xs: List[T = Int64]` behind `xs: List[T = T]`, `T` any `V`) is refused. Passes either way
/// by design: it guards the per-occurrence expansion against admitting what the spec leaves open.
#[test]
fn a_member_taking_two_bare_foreign_sorts_is_not_narrower_control() {
    let src = car_program(
        "wi0rp29mr.bare_c",
        "operation count2(s: Self, xs: List[T = T], ys: List[T = Int64]) -> Int64",
        "Sp[T = V]",
        "operation count2(s: Self, xs: List[T = Int64], ys: List) -> Int64 = List.length(ys)",
        "\n  operation go() -> Int64 = 0\n",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["parameter 2 (`xs: List[T = Int64]`) takes less than the spec's"],
        "a member fixing what the spec leaves open is narrower",
    );
}

// ── the verdict is subtyping ─────────────────────────────────────────────────

/// A MEMBER WIDER BY TUPLE WIDTH FITS: `t: (a: V)` takes every `(a: T, b: T)` the spec passes
/// (name-keyed width, WI-803). A unify-`false` refused it. Runs to 41 + 1.
#[test]
fn a_member_wider_by_tuple_width_is_not_narrower() {
    let ns = "wi0rp29mr.width";
    let src = car_program(
        ns,
        "operation op(s: Self, t: (a: T, b: T)) -> T",
        "Sp[T = V]",
        "operation op(s: Self, t: (a: V)) -> V = t.a",
        r#"
  operation use(c: Car[V = Int64]) -> Int64 = Sp.op(c, (a: 41, b: 2)) + Car.op(c, (a: 1, b: 7))
  operation go() -> Int64 = use(car(v: 40))
"#,
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(42));
}

/// A MEMBER WIDER BY CONTRAVARIANCE FITS: `f: (a: cat) -> Int64` takes every `(a: Animal) ->
/// Int64` callback the spec passes. Runs to 1 + 1.
#[test]
fn a_member_wider_by_contravariance_is_not_narrower() {
    let ns = "wi0rp29mr.contra";
    let src = car_program(
        ns,
        "operation feed(s: Self, f: (a: Animal) -> Int64) -> Int64",
        "Sp[T = V]",
        "operation feed(s: Self, f: (a: cat) -> Int64) -> Int64 =\n      let c: cat = cat(n: 41)\n      f(c)",
        r#"
  operation weigh(a: Animal) -> Int64 = 1
  operation use(k: Car[V = Int64]) -> Int64 = Sp.feed(k, weigh) + Car.feed(k, weigh)
  operation go() -> Int64 = use(car(v: 40))
"#,
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(2));
}

/// A MEMBER WIDER BY ITS CALLBACK'S ROW FITS: a callback allowed to raise `Error[String]` takes
/// every pure one the spec passes. Runs to 42 + 42 - 42.
#[test]
fn a_member_wider_by_its_callback_row_is_not_narrower() {
    let ns = "wi0rp29mr.row";
    let src = car_program(
        ns,
        "operation feed(s: Self, f: (x: Int64) -> Int64) -> Int64",
        "Sp[T = V]",
        "operation feed(s: Self, f: (x: Int64) -> Int64 @ Error[String]) -> Int64 = 42",
        r#"
  operation inc(x: Int64) -> Int64 = x + 1
  operation go() -> Int64 =
    let k: Car[V = Int64] = car(v: 1)
    Sp.feed(k, inc) + Car.feed(k, inc) - 42
"#,
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(42));
}

// ── the receiver ─────────────────────────────────────────────────────────────

/// A RECEIVER WRITTEN WITH ARGUMENTS FIXES THEM: `total(s: Sp[T = Int64], k)` receives only the
/// `Car`s whose `T` — `V` at this provision — is `Int64`, so `total(s: Car[V = Int64], k)`
/// takes every receiver it can be given. Read as any `Car`, it was refused. Runs to 40 + 2.
#[test]
fn a_receiver_written_with_arguments_fixes_them() {
    let ns = "wi0rp29mr.recv";
    let src = car_program(
        ns,
        "operation total(s: Sp[T = Int64], k: Int64) -> Int64",
        "Sp[T = V]",
        "operation total(s: Car[V = Int64], k: Int64) -> Int64 = s.v + k",
        r#"
  operation go() -> Int64 =
    let b: Car[V = Int64] = car(v: 40)
    Sp.total(b, 2)
"#,
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(42));
}

/// … AND ITS CONTROL: behind an UNWRITTEN receiver the same member fixes what the spec leaves
/// open — refused, naming the receiver as the receiver (the message had called it a tie).
#[test]
fn a_receiver_written_with_arguments_fixes_them_control() {
    let src = car_program(
        "wi0rp29mr.recv_c",
        "operation total(s: Self, k: Int64) -> Int64",
        "Sp[T = V]",
        "operation total(s: Car[V = Int64], k: Int64) -> Int64 = s.v + k",
        "\n  operation go() -> Int64 = 0\n",
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "`s` is the receiver",
            "fixes what the spec leaves open; type `s` as `Self` — `Car` at its own parameters —",
        ],
        "a receiver narrowed to one instance",
    );
}

/// A CARRIER PARAMETER BOUND WITH ARGUMENTS FIXES THEM: at `provides Desc[T = Box[B = Int64]]`
/// the receiver is a `Box[B = Int64]`, and `describe(x: Box)` — this instance — is one. Compared
/// against a fresh rigid for `B`, it was refused as narrower. Runs to 5.
#[test]
fn a_carrier_parameter_bound_with_arguments_fixes_them() {
    let ns = "wi0rp29mr.bound";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Box
    sort B = ?
    entity box(inner: B)
    provides Desc[T = Box[B = Int64]]
    operation describe(x: Self) -> Int64 = 5
  end
  operation go() -> Int64 = Desc.describe(box(inner: 1))
{APP}end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(5));
}

/// … AND A MEMBER WRITING THE BINDING'S ARGUMENTS FITS IT: `describe(x: Box[B = Int64])` at
/// `provides Desc[T = Box[B = Int64]]` receives exactly the `Box`es the provision covers. Read
/// against a fresh rigid for `B` instead of the written `Int64`, it was refused (the wi1102
/// fixture shape). Runs to 5.
#[test]
fn a_carrier_parameter_bound_with_arguments_fits_a_member_writing_them() {
    let ns = "wi0rp29mr.bound_w";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Box
    sort B = ?
    entity box(inner: B)
    provides Desc[T = Box[B = Int64]]
    operation describe(x: Box[B = Int64]) -> Int64 = 5
  end
  operation go() -> Int64 = Desc.describe(box(inner: 1))
{APP}end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(5));
}

/// A WRITTEN `?` IN A CARRIER BINDING IS ANY TYPE: at `provides Show[T = Car[V = ?]]` the
/// receiver is a `Car` at some `V`, which `show(x: Car[V = Int64], k)` fixes. Unified with the
/// `?` it was admitted, and `Show.show(car(v: "str"), 7)` died adding 7 to a string.
#[test]
fn a_written_wildcard_in_a_carrier_binding_is_any_type() {
    let src = format!(
        r#"
namespace wi0rp29mr.wild
  import anthill.prelude.{{Int64, String, List}}
  sort Show
    sort T = ?
    operation show(x: T, k: Int64) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Show[T = Car[V = ?]]
    operation show(x: Car[V = Int64], k: Int64) -> Int64 = x.v + k
  end
  operation go() -> Int64 =
    let c: Car[V = String] = car(v: "str")
    Show.show(c, 7)
{APP}end
"#
    );
    assert_refused_naming(
        &load_errors(&src),
        &["`x` is the receiver"],
        "the receiver is any `Car`",
    );
}

/// THE RECEIVER IS DECIDED PER OPERATION: `Coll` receives on `C` in `size(c: C, k)` and on
/// itself in `touch(s: Coll)`; decided once per spec, `size`'s `c` was an independent `Car`
/// and the member refused as tying it to itself. Runs to 7 + 1.
#[test]
fn the_receiver_is_decided_per_operation() {
    let ns = "wi0rp29mr.perop";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Coll
    sort C = ?
    sort T = ?
    operation size(c: C, k: Int64) -> Int64
    operation touch(s: Self) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Coll[C = Self, T = V]
    operation size(c: Self, k: Int64) -> Int64 = k
    operation touch(s: Self) -> Int64 = 1
  end
  operation go() -> Int64 =
    let k: Car[V = Int64] = car(v: 3)
    Coll.size(k, 7) + Coll.touch(k)
{APP}end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(8));
}

/// … AND TWO PARAMETERS THE OPERATIONS RECEIVE ON: at `Rel[A = Car, B = Car]` `right` receives
/// on `B`, which the rule read as an independent `Car` (only the first received parameter was
/// the receiver). Runs to 3 + 5.
#[test]
fn the_receiver_is_decided_per_operation_over_two_carrier_parameters() {
    let ns = "wi0rp29mr.twoc";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Rel
    sort A = ?
    sort B = ?
    operation left(a: A, k: Int64) -> Int64
    operation right(b: B, k: Int64) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Rel[A = Self, B = Self]
    operation left(a: Self, k: Int64) -> Int64 = k
    operation right(b: Self, k: Int64) -> Int64 = k + 1
  end
  operation go() -> Int64 =
    let c: Car[V = Int64] = car(v: 3)
    Rel.left(c, 3) + Rel.right(c, 4)
{APP}end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(8));
}

/// A SELF-RECEIVER'S OWN CARRIER PARAMETER IS ITS INSTANCE: in `mix(s: Coll, c: C)`, `s`'s
/// carrier IS `C` (the one `size(c: C, k)` receives on, bound to `Car`), so `c` is the
/// receiver's instance and `mix(s: Car, c: Car)` — tying them — takes every argument list the
/// spec does. Read as an independent `Car`, the member was refused for the tie. Runs to 7.
#[test]
fn a_self_receivers_own_carrier_parameter_is_its_instance() {
    let ns = "wi0rp29mr.mix";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Coll
    sort C = ?
    sort T = ?
    operation size(c: C, k: Int64) -> Int64
    operation mix(s: Self, c: C) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Coll[C = Self, T = V]
    operation size(c: Self, k: Int64) -> Int64 = k
    operation mix(s: Self, c: Self) -> Int64 = 7
  end
  operation go() -> Int64 =
    let k: Car[V = Int64] = car(v: 3)
    Coll.mix(k, k)
{APP}end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(7));
}

// ── the rest of the spec's arguments ─────────────────────────────────────────

/// ANOTHER PARAMETER TYPED BY THE SPEC IS ANY PROVIDER: `both(s: Sp, o: Sp[T = Int64])` takes
/// any `Sp` provider at `Int64` for `o`, so `both(s: Car, o: Car)` — which also ties `o` to the
/// receiver — takes less. Read as the receiver's instance, it was admitted, and `Sp.both(a, b)`
/// over a `Car[V = String]` and a `Car[V = Int64]` died at run time.
#[test]
fn another_parameter_typed_by_the_spec_is_any_provider() {
    let src = car_program(
        "wi0rp29mr.anyp",
        "operation both(s: Self, o: Sp[T = Int64]) -> Option[T = s.T]",
        "Sp[T = V]",
        "operation both(s: Self, o: Self) -> Option[T = V] = some(o.v)",
        "\n  operation go() -> Int64 = 0\n",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["parameter 2 (`o: Car[V = V]`)", "admits any provider of `Sp`"],
        "a member taking only its carrier where the spec takes any provider",
    );
}

/// … AND ITS CONTROL: a member typing `o` by the spec takes any provider. Runs to the length of
/// the receiver's `"abc"`. Passes either way by design: a member the rule must not refuse.
#[test]
fn another_parameter_typed_by_the_spec_is_any_provider_control() {
    let ns = "wi0rp29mr.anyp_c";
    let src = car_program(
        ns,
        "operation both(s: Self, o: Sp[T = Int64]) -> Option[T = s.T]",
        "Sp[T = V]",
        "operation both(s: Self, o: Sp[T = Int64]) -> Option[T = V] = some(s.v)",
        r#"
  operation go() -> Int64 =
    let a: Car[V = String] = car(v: "abc")
    let b: Car[V = Int64] = car(v: 41)
    match Sp.both(a, b)
      case some(str) -> String.length(str)
      case none() -> 0
"#,
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(3));
}

/// `Sp { both(s: Sp, o: T) }` at `Car provides Sp[T = {binding}]`, `Car`'s own `both` being
/// `member`; `go` calls `Sp.both(x, {arg})` over `x: Car[V = Int64]` and `y: Car[V = {y.0}]`.
/// `car` carries a function of its own `V`, so a body can RELY on two `Car`s being one instance.
fn both_program(ns: &str, binding: &str, member: &str, y: (&str, &str), arg: &str) -> String {
    let (y_ty, y_val) = y;
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Sp
    sort T = ?
    operation both(s: Self, o: T) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V, f: (x: V) -> Int64)
    provides Sp[T = {binding}]
    {member}
  end
  operation go() -> Int64 =
    let x: Car[V = Int64] = car(v: 1, f: lambda (n: Int64) -> n + 1)
    let y: Car[V = {y_ty}] = car(v: {y_val}, f: lambda (k: {y_ty}) -> 0)
    Sp.both(x, {arg})
{APP}end
"#
    )
}

/// `both` applying the receiver's function to `o`'s value: checks only where `o` is the
/// receiver's instance, which a bare `Car` inside `sort Car` is (§3's tie).
const TIED_BOTH: &str =
    "operation both(s: Self, o: Self) -> Int64 =\n      match s\n        case car(_, g) -> g(o.v)";

/// A BINDING NAMING THE CARRIER IS THIS INSTANCE, as the bare name is in the carrier's own
/// operations (§3's tie): a `provides` clause is written inside the sort, so `Sp[T = Car]` —
/// and `Sp[T = Car[V = V]]`, the same type — binds `T` to the receiver's own `Car`, whether or
/// not an operation RECEIVES on `T`. `both(s: Car, o: Car)` is then exactly the spec's, and
/// runs: 41 + 1. INTERIM (user, 2026-10-01): WI-20261001-80ZV8 makes a bare sort fresh `?` slots
/// in both places. Read as an independent instance where no operation received on `T` (the
/// fourth-to-sixth passes), the member was refused as tying `o`. FAILS under ledger part 50.
#[test]
fn a_binding_naming_the_carrier_is_this_instance() {
    for (ns, binding) in [
        ("wi0rp29mr7.this_self", "Self"),
        ("wi0rp29mr7.this_own", "Car[V = V]"),
    ] {
        let src = both_program(ns, binding, TIED_BOTH, ("Int64", "41"), "y");
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(42), "{binding}");
    }
}

/// … AND THE CALL HOLDS A SELF-RECEIVER'S ARGUMENT TO IT: `Sp.both(x, y)` over a `Car[V =
/// String]` beside the receiver's `Car[V = Int64]`, and `Sp.both(x, 5)`, are refused at load.
/// The self-receiver call skipped a binding naming the carrier, so both loaded and the member
/// died in its body — "type mismatch: expected Int64, got String and Int64", and "field_access:
/// receiver is not an entity (got Int64)" (MEASURED). FAILS under ledger part 51.
#[test]
fn a_binding_naming_the_carrier_holds_a_self_receiver_call_to_this_instance() {
    for (ns, binding) in [
        ("wi0rp29mr7.hold_self", "Self"),
        ("wi0rp29mr7.hold_own", "Car[V = V]"),
    ] {
        let two = both_program(ns, binding, TIED_BOTH, ("String", "\"s\""), "y");
        assert_refused_naming(
            &load_errors(&two),
            &["both.o (op-arg): expected Car[V = Int64], got Car[V = String]"],
            &format!("a second instance at `T = {binding}`"),
        );
        let five = both_program(ns, binding, TIED_BOTH, ("String", "\"s\""), "5");
        assert_refused_naming(
            &load_errors(&five),
            &["both.o (op-arg): expected Car[V = Int64], got Int64"],
            &format!("a `5` at `T = {binding}`"),
        );
    }
}

/// AN INDEPENDENT INSTANCE IS WRITTEN: `Sp[T = Car[V = ?]]` binds `T` to any `Car`, so
/// `both(s: Car, o: Car)` ties `o` to the receiver where the spec lets them differ. Passes under
/// parts 50 and 51 by design — a written `?` was any type before them: it guards the reading
/// the interim rule leaves a provision able to write.
#[test]
fn a_binding_naming_the_carrier_at_a_wildcard_is_an_independent_instance() {
    let src = both_program(
        "wi0rp29mr7.indep",
        "Car[V = ?]",
        "operation both(s: Self, o: Self) -> Int64 = 1",
        ("String", "\"s\""),
        "y",
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "parameter 2 (`o: Car[V = V]`)",
            "is THIS instance (the parametricity tie)",
        ],
        "the tie behind a binding written at a wildcard",
    );
}

/// … AND ITS CONTROL: `o` given a type argument of its own takes any `Car`, and the spec call
/// runs over two instances, to 1. Passes either way by design: a member the rule must not
/// refuse.
#[test]
fn a_binding_naming_the_carrier_at_a_wildcard_is_an_independent_instance_control() {
    let ns = "wi0rp29mr7.indep_ok";
    let src = both_program(
        ns,
        "Car[V = ?]",
        "operation both[W](s: Self, o: Car[V = W]) -> Int64 = 1",
        ("String", "\"s\""),
        "y",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(1));
}

/// A SPEC OPERATION'S TYPE PARAMETER IS ANY TYPE: `f[A](s: Sp, x: A)` takes any `x`, so
/// `f(s: Car, x: Int64)` takes less; admitted, `Sp.f(a, "str")` added 1 to a string at run time.
#[test]
fn a_spec_operations_type_parameter_is_any_type() {
    let src = car_program(
        "wi0rp29mr.oparg",
        "operation f[A](s: Self, x: A) -> Int64",
        "Sp[T = V]",
        "operation f(s: Self, x: Int64) -> Int64 = x + 1",
        "\n  operation go() -> Int64 = 0\n",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["parameter 2 (`x: Int64`) takes less than the spec's"],
        "the spec operation's own type parameter",
    );
}

/// … AND ITS CONTROL: a member generic in `x` takes any. Runs to 1. Passes either way by design:
/// a member the rule must not refuse.
#[test]
fn a_spec_operations_type_parameter_is_any_type_control() {
    let ns = "wi0rp29mr.oparg_c";
    let src = car_program(
        ns,
        "operation f[A](s: Self, x: A) -> Int64",
        "Sp[T = V]",
        "operation f[A](s: Self, x: A) -> Int64 = 1",
        r#"
  operation go() -> Int64 =
    let a: Car[V = Int64] = car(v: 40)
    Sp.f(a, "str")
"#,
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(1));
}

/// AN UNWRITTEN SLOT OF A SPEC PARAMETER IS ANY TYPE: `f(s: Sp, x: Option)` takes an option of
/// any element, which `x: Option[T = Int64]` does not. Read as a wildcard it was admitted, and
/// `Sp.f(a, some("str"))` added 1 to a string at run time — while the named spelling
/// `f[A](…, x: Option[T = A])` was refused.
#[test]
fn an_unwritten_slot_of_a_spec_parameter_is_any_type() {
    let src = car_program(
        "wi0rp29mr.slot",
        "operation f(s: Self, x: Option) -> Int64",
        "Sp[T = V]",
        "operation f(s: Self, x: Option[T = Int64]) -> Int64 =\n      match x\n        case some(n) -> n + 1\n        case none() -> 0",
        "\n  operation go() -> Int64 = 0\n",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["parameter 2 (`x: Option[T = Int64]`) takes less than the spec's"],
        "an unwritten slot is any type",
    );
}

/// … AND ITS CONTROL: a member leaving the slot unwritten too takes any. Runs to 7. Passes either
/// way by design: a member the rule must not refuse.
#[test]
fn an_unwritten_slot_of_a_spec_parameter_is_any_type_control() {
    let ns = "wi0rp29mr.slot_c";
    let src = car_program(
        ns,
        "operation f(s: Self, x: Option) -> Int64",
        "Sp[T = V]",
        "operation f(s: Self, x: Option) -> Int64 = 7",
        r#"
  operation go() -> Int64 =
    let a: Car[V = Int64] = car(v: 1)
    let o: Option[T = String] = some("str")
    Sp.f(a, o)
"#,
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(7));
}

// ── which parameters are THIS instance (the fifth /code-review's findings) ────────

/// THE RECEIVED PARAMETER IS FOUND PAST A SIBLING'S PARAMETER TYPED OTHERWISE: `insert(x: T, c:
/// C)` receives on `C` (bound to `Car`), not on `T` (bound to `Int64`). Recorded as the first
/// parameter typed by ANY binding, `T` hid `C`, so `mix`'s `c` was an independent `Car` and the
/// member refused as tying it — while the twin writing `insert(c: C, x: T)` ran. Runs to 7 + 1.
#[test]
fn the_received_parameter_is_found_past_a_sibling_parameter_typed_otherwise() {
    let ns = "wi0rp29mr.recvorder";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Coll
    sort C = ?
    sort T = ?
    operation insert(x: T, c: C) -> Int64
    operation mix(s: Self, c: C) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Coll[C = Self, T = Int64]
    operation insert(x: Int64, c: Self) -> Int64 = x
    operation mix(s: Self, c: Self) -> Int64 = 7
  end
  operation go() -> Int64 =
    let k: Car[V = Int64] = car(v: 3)
    Coll.mix(k, k) + Coll.insert(1, k)
{APP}end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(8));
}

/// TWO RECEIVED PARAMETERS BOUND TO TWO WRITTEN INSTANCES ARE EACH THAT TYPE: at `Rel[A =
/// Car[V = Int64], B = Car[V = String]]`, `mix(s: Rel, a: A, b: B)` takes an `Int64` car and a
/// `String` one beside any receiver, which the member writes exactly. Both bindings were met by
/// the receiver's ONE instance, the second meeting dropped, and the member was refused printing
/// `Car[V = String]` against `Car[V = String]`. Runs to 3.
#[test]
fn two_received_parameters_at_two_written_instances_are_each_that_type() {
    let ns = "wi0rp29mr.tworecv";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Rel
    sort A = ?
    sort B = ?
    operation left(a: A, k: Int64) -> Int64
    operation right(b: B, k: Int64) -> Int64
    operation mix(s: Self, a: A, b: B) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Rel[A = Car[V = Int64], B = Car[V = String]]
    operation left(a: Car[V = Int64], k: Int64) -> Int64 = k
    operation right(b: Car[V = String], k: Int64) -> Int64 = k
    operation mix(s: Self, a: Car[V = Int64], b: Car[V = String]) -> Int64 = a.v
  end
  operation go() -> Int64 =
    let k1: Car[V = Int64] = car(v: 3)
    let k2: Car[V = String] = car(v: "s")
    Rel.mix(k2, k1, k2)
{APP}end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(3));
}

/// The `Holder` provision of the next three rows: `peek(c: C)` receives on `C`, bound to
/// `Box[B = Int64]`, and `touch(s: Holder)` / `mix(s: Holder, c: C)` receive on the spec.
fn holder_program(ns: &str, members: &str, go: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Holder
    sort C = ?
    operation peek(c: C) -> Int64
    operation touch(s: Self) -> Int64
    operation mix(s: Self, c: C) -> Int64
  end
  sort Box
    sort B = ?
    entity box(inner: B)
    provides Holder[C = Box[B = Int64]]
    operation peek(c: Box[B = Int64]) -> Int64 = c.inner
    {members}
  end
  operation go() -> Int64 =
{go}
{APP}end
"#
    )
}

/// A RECEIVED PARAMETER WRITTEN WITH ARGUMENTS DOES NOT NARROW THE SELF-RECEIVER: every `Box`
/// provides `Holder`, so `touch(s: Holder)` receives a `Box[B = String]` too, and `touch(s:
/// Box[B = Int64])` takes less. Met by `C`'s binding, the receiver's instance WAS `Box[B =
/// Int64]`: admitted, and `Holder.touch(box(inner: "s"))` added 1 to a string at run time.
#[test]
fn a_received_parameter_written_with_arguments_does_not_narrow_the_self_receiver() {
    let src = holder_program(
        "wi0rp29mr.selffixed",
        "operation touch(s: Box[B = Int64]) -> Int64 = s.inner + 1\n    operation mix(s: Self, c: Box[B = Int64]) -> Int64 = 1",
        "    let b: Box[B = String] = box(inner: \"s\")\n    Holder.touch(b)",
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "parameter 1 (`s: Box[B = Int64]`)",
            "`s` is the receiver",
            "fixes what the spec leaves open",
        ],
        "a self-receiver narrowed by another parameter's binding",
    );
}

/// … AND THE TIE THROUGH IT: `mix(s: Holder, c: C)` takes a `Box[B = Int64]` for `c` beside a
/// receiver of any `B`, so `mix(s: Box, c: Box)` — `c` THIS instance — takes less. Read through
/// the same meeting, the member was admitted.
#[test]
fn a_received_parameter_written_with_arguments_is_not_this_instance() {
    let src = holder_program(
        "wi0rp29mr.selftie",
        "operation touch(s: Self) -> Int64 = 1\n    operation mix(s: Self, c: Self) -> Int64 = 1",
        "    0",
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "parameter 2 (`c: Box[B = B]`)",
            "is THIS instance (the parametricity tie)",
            "need not be the receiver's instance",
        ],
        "a member tying a parameter the provision writes at its own arguments",
    );
}

/// … AND ITS CONTROL: the receiver at the carrier's own parameters and `c` written as the
/// provision binds it take every argument list the spec does. Runs to 1 + 1. A member the rule
/// must not refuse — and FAILS under ledger part 16 alone (the written binding read as this
/// instance, the member writing it reads as narrower), passing under 16b, where the instance is
/// met by it.
#[test]
fn a_received_parameter_written_with_arguments_control() {
    let ns = "wi0rp29mr.selfok";
    let src = holder_program(
        ns,
        "operation touch(s: Self) -> Int64 = 1\n    operation mix(s: Self, c: Box[B = Int64]) -> Int64 = 1",
        "    let b: Box[B = String] = box(inner: \"s\")\n    let i: Box[B = Int64] = box(inner: 4)\n    Holder.touch(b) + Holder.mix(b, i)",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(2));
}

/// AN OPERATION WITH NO RECEIVER READS THIS INSTANCE THROUGH A RECEIVED PARAMETER: `total(xs:
/// List[T = T])` has no receiver, and `T` — which `combine(a: T, b: T)` receives on, bound to
/// the bare `Car` — is THIS instance, so `total(xs: List[T = Car])` is exactly the spec's. Read
/// as an independent instance beside the member's rigid one, it was refused printing `List[T =
/// Car]` against `List[T = Car]`. Runs to 2 + 40.
#[test]
fn an_operation_with_no_receiver_reads_this_instance_through_a_received_parameter() {
    let ns = "wi0rp29mr.mcat";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  import anthill.prelude.List.{{cons, nil}}
  sort Mon
    sort T = ?
    operation combine(a: T, b: T) -> Int64
    operation total(xs: List[T = T]) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V, n: Int64)
    provides Mon[T = Self]
    operation combine(a: Self, b: Self) -> Int64 = a.n + b.n
    operation total(xs: List[T = Self]) -> Int64 = List.length(xs)
  end
  operation go() -> Int64 =
    let c1: Car[V = Int64] = car(v: 1, n: 1)
    let c2: Car[V = Int64] = car(v: 2, n: 2)
    Mon.total(cons(c1, cons(c2, nil))) + 40
{APP}end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(42));
}

/// … AND THROUGH A SOLE PARAMETER: with `total` the spec's only operation, no operation takes
/// `T` bare, yet a spec that is not self-representing has its sole parameter as its carrier
/// (WI-1102's second rung) and dispatches on it. Runs to 2 + 40.
#[test]
fn an_operation_with_no_receiver_reads_this_instance_through_a_sole_parameter() {
    let ns = "wi0rp29mr.mcat2";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  import anthill.prelude.List.{{cons, nil}}
  sort Mon
    sort T = ?
    operation total(xs: List[T = T]) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V, n: Int64)
    provides Mon[T = Self]
    operation total(xs: List[T = Self]) -> Int64 = List.length(xs)
  end
  operation go() -> Int64 =
    let c1: Car[V = Int64] = car(v: 1, n: 1)
    let c2: Car[V = Int64] = car(v: 2, n: 2)
    Mon.total(cons(c1, cons(c2, nil))) + 40
{APP}end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(42));
}

/// A MEMBER RECEIVER TYPED BY THE SPEC READS THE PROVISION'S BINDINGS: `op(s: Sp[T = V], x: V)`
/// receives the `Sp` this provision makes of the carrier — its `T` is the carrier's `V`.
/// Compared with the GENERIC spec, whose `T` is any type, it was refused as fixing what the spec
/// leaves open. Runs to 7.
#[test]
fn a_member_receiver_typed_by_the_spec_reads_the_provisions_bindings() {
    let ns = "wi0rp29mr.mts";
    let src = car_program(
        ns,
        "operation op(s: Self, x: T) -> Int64",
        "Sp[T = V]",
        "operation op(s: Sp[T = V], x: V) -> Int64 = 7",
        r#"
  operation go() -> Int64 =
    let k: Car[V = Int64] = car(v: 3)
    Sp.op(k, 5)
"#,
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(7));
}

/// … AND A WITNESS'S: `BoxHolder` provides `Holder[C = Box, Element = Int64]`, so its
/// `joinTwo(a: Holder[Element = Int64], b: Holder)` receives every `Holder` it covers. Refused
/// the same way, naming "every `BoxHolder`". Runs to 2.
#[test]
fn a_witness_member_receiver_typed_by_the_spec_reads_the_provisions_bindings() {
    let ns = "wi0rp29mr.wit";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Holder
    sort C = ?
    sort Element = ?
    operation peek(c: C) -> Int64
    operation joinTwo(a: Self, b: Holder[C = ?, Element = ?]) -> Int64
  end
  sort Box
    entity box(n: Int64)
  end
  sort BoxHolder
    import anthill.prelude.Int64
    provides Holder[C = Box, Element = Int64]
    operation peek(c: Box) -> Int64 = 2
    operation joinTwo(a: Holder[Element = Int64], b: Holder) -> Int64 = 3
  end
  operation go() -> Int64 = Holder.peek(box(n: 1))
{APP}end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(2));
}

// ── a generic member wider than its spec ──────────────────────────────────────

/// A GENERIC MEMBER WIDER THAN ITS SPEC FITS — by tuple width (`t: (a: X)` behind `(a: Int64,
/// b: Int64)`), contravariantly (`f: (a: cat) -> R` behind `(a: Animal) -> Int64`) and by order
/// (`t: (b: String, a: X)`). Unification stops at the first difference and left `X` / `R`
/// unbound, and the subtype relation binds nothing, so each was refused where its concrete twin
/// fitted. Each runs to 7.
#[test]
fn a_generic_member_wider_than_its_spec_is_not_narrower() {
    for (tag, spec_op, member, call) in [
        (
            "width",
            "operation op(s: Self, t: (a: Int64, b: Int64)) -> Int64",
            "operation op[X](s: Self, t: (a: X)) -> Int64 = 7",
            "Sp.op(car(v: 1), (a: 41, b: 2))",
        ),
        (
            "contra",
            "operation feed(s: Self, f: (a: Animal) -> Int64) -> Int64",
            "operation feed[R](s: Self, f: (a: cat) -> R) -> Int64 = 7",
            "Sp.feed(car(v: 1), weigh)",
        ),
        (
            "perm",
            "operation op(s: Self, t: (a: Int64, b: String)) -> Int64",
            "operation op[X](s: Self, t: (b: String, a: X)) -> Int64 = 7",
            "Sp.op(car(v: 1), (a: 41, b: \"x\"))",
        ),
    ] {
        let ns = format!("wi0rp29mr.wide_{tag}");
        let src = car_program(
            &ns,
            spec_op,
            "Sp[T = V]",
            member,
            &format!(
                "\n  operation weigh(a: Animal) -> Int64 = 1\n  operation go() -> Int64 = {call}\n"
            ),
        );
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(7), "{tag}");
    }
}

/// … AND ITS CONTROLS: what the relation's decomposition binds is still judged — a generic member
/// demanding a field the spec does not pass (`t: (a: X, c: X)`), and one whose variable the
/// decomposition binds to `Int64` and the next position to `String` (`t: (a: X), y: X` behind
/// `t: (a: Int64, b: Int64), y: String`), are refused: the binding must not make a narrower
/// member fit. The first passes either way by design; the second FAILS under ledger part 20,
/// refused at parameter 2 — without the binding, the wider position itself is refused.
#[test]
fn a_generic_member_wider_than_its_spec_control() {
    let missing = car_program(
        "wi0rp29mr.wide_c1",
        "operation op(s: Self, t: (a: Int64, b: Int64)) -> Int64",
        "Sp[T = V]",
        "operation op[X](s: Self, t: (a: X, c: X)) -> Int64 = 7",
        "\n  operation go() -> Int64 = 0\n",
    );
    assert_refused_naming(
        &load_errors(&missing),
        &["parameter 2 (`t: (a: ?X, c: ?X)`) takes less than the spec's"],
        "a field the spec does not pass",
    );
    let tied = car_program(
        "wi0rp29mr.wide_c2",
        "operation op(s: Self, t: (a: Int64, b: Int64), y: String) -> Int64",
        "Sp[T = V]",
        "operation op[X](s: Self, t: (a: X), y: X) -> Int64 = 7",
        "\n  operation go() -> Int64 = 0\n",
    );
    assert_refused_naming(
        &load_errors(&tied),
        &["parameter 3 (`y: ?X`) takes less than the spec's"],
        "a variable the decomposition bound one way and the next position another",
    );
}

// ── the spec's side is any type at every depth ───────────────────────────────

/// A WRITTEN `?` OUTSIDE THE RECEIVER IS ANY TYPE: `f(s: Sp, x: Option[T = ?])` takes an option
/// of any element, which `x: Option[T = Int64]` does not. The `?` stayed a variable the member
/// bound: admitted, and `Sp.f(a, some("str"))` added 1 to a string at run time.
#[test]
fn a_written_wildcard_outside_the_receiver_is_any_type() {
    let src = car_program(
        "wi0rp29mr.wildp",
        "operation f(s: Self, x: Option[T = ?]) -> Int64",
        "Sp[T = V]",
        "operation f(s: Self, x: Option[T = Int64]) -> Int64 =\n      match x\n        case some(n) -> n + 1\n        case none() -> 0",
        "\n  operation go() -> Int64 = 0\n",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["parameter 2 (`x: Option[T = Int64]`) takes less than the spec's"],
        "a written wildcard",
    );
}

/// A NESTED UNWRITTEN SLOT IS ANY TYPE: `f(s: Sp, x: List[T = Option])` takes a list of options
/// of any element. Only the top-level form was expanded, so the nested `Option` read as the
/// member's `Option[T = Int64]`: admitted, and adding 1 to a string at run time.
#[test]
fn a_nested_unwritten_slot_of_a_spec_parameter_is_any_type() {
    let src = car_program(
        "wi0rp29mr.nslot",
        "operation f(s: Self, x: List[T = Option]) -> Int64",
        "Sp[T = V]",
        "operation f(s: Self, x: List[T = Option[T = Int64]]) -> Int64 = 1",
        "\n  operation go() -> Int64 = 0\n",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["parameter 2 (`x: List[T = Option[T = Int64]]`) takes less than the spec's"],
        "a nested unwritten slot",
    );
}

/// AN OCCURRENCE-CARRIED TYPE'S UNWRITTEN SLOT IS ANY TYPE: `x: Buf[N = 3]` — a type holding a
/// VALUE, so occurrence-carried — leaves `T` open, which `x: Buf[T = Int64, N = 3]` fixes. The
/// expansion skipped any carrier but a term: admitted, and `Sp.f(a, buf(v: "str"))` added 1 to
/// a string, while the `N = Bool` twin was refused.
#[test]
fn an_unwritten_slot_of_a_type_holding_a_value_is_any_type() {
    for n in ["3", "Bool"] {
        let src = format!(
            r#"
namespace wi0rp29mr.nodeslot
  import anthill.prelude.{{Int64, String, List}}
  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end
  sort Sp
    sort T = ?
    operation f(s: Self, x: Buf[N = {n}]) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation f(s: Self, x: Buf[T = Int64, N = {n}]) -> Int64 = x.v + 1
  end
  operation go() -> Int64 = 0
{APP}end
"#
        );
        assert_refused_naming(
            &load_errors(&src),
            &[&format!(
                "parameter 2 (`x: Buf[T = Int64, N = {n}]`) takes less than the spec's"
            )],
            "an unwritten slot beside a value",
        );
    }
}

/// … AND THE MEMBER'S NESTED BARE FOREIGN SORTS ARE TWO: `p: Pair[A = List, B = List]` takes a
/// pair of lists of any two element types. Expanded at the top only, the two `List`s shared
/// `List`'s one `T`, bound `Int64` then `String`, and the member was refused. Runs to 3 + 3.
#[test]
fn a_members_nested_bare_foreign_sorts_are_two() {
    let ns = "wi0rp29mr.nbare";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List, Pair}}
  import anthill.prelude.Pair.{{pair}}
  sort Sp
    sort T = ?
    operation count(s: Self, p: Pair[A = List[T = Int64], B = List[T = String]]) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation count(s: Self, p: Pair[A = List, B = List]) -> Int64 = 3
  end
  operation go() -> Int64 =
    let a: Car[V = Int64] = car(v: 1)
    let xs: List[T = Int64] = [1]
    let ys: List[T = String] = ["s"]
    Sp.count(a, pair(xs, ys)) + Car.count(a, pair(xs, ys))
{APP}end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(6));
}

// ── a projection over this instance ───────────────────────────────────────────

/// A PROJECTION OVER THE RECEIVER IS JUDGED AT DECLARATION: at `T = List[T = Int64]` the spec's
/// `put(s: Sp, k: s.T)` takes a list for `k`, and `put(c: IntCar, k: Int64)` an element. Every
/// projection-typed position was left to the call, and only the WI-606 fallback judged it: the
/// ordinary dispatch ran the member with a list (MEASURED, died at run time). The main file's
/// `an_argument_the_override_refuses_is_refused_control` is the member at `T = V` (`k: c.V`),
/// which reads the instance's `V` on both sides and runs.
#[test]
fn a_projection_over_the_receiver_is_judged_at_declaration() {
    let src = format!(
        r#"
namespace wi0rp29mr.putpair
  import anthill.prelude.{{Int64, String, List}}
  sort Sp
    sort T = ?
    operation put(s: Self, k: s.T) -> Int64
  end
  sort IntCar
    entity intcar(v: Int64)
    provides Sp[T = List[T = Int64]]
    operation put(c: IntCar, k: Int64) -> Int64 = k + 1
  end
  operation go() -> Int64 = 0
{APP}end
"#
    );
    assert_refused_naming(
        &load_errors(&src),
        &["parameter 2 (`k: Int64`) takes less than the spec's"],
        "a projection over the receiver",
    );
}

/// … AND A CALLBACK'S ROW BESIDE ONE: `each[EP](s: Sp, f: (x: s.T) -> Int64 @ {EP})` passes a
/// callback with any effects, which `f: (x: Int64) -> Int64` — pure — does not take. Through the
/// fallback the callback's row went unjudged, and an operation declared pure wrote a cell
/// (MEASURED: the run answered the written 42).
#[test]
fn a_callback_row_beside_a_projection_is_judged_at_declaration() {
    let src = format!(
        r#"
namespace wi0rp29mr.cbrow
  import anthill.prelude.{{Int64, String, List}}
  sort Sp
    sort T = ?
    effects E = ?
    operation each[EP](s: Self, f: (x: s.T) -> Int64 @ {{EP}}) -> Int64 effects {{s.E, EP}}
  end
  sort Car
    effects EC = ?
    entity car(v: Int64)
    provides Sp[T = Int64, E = {{EC}}]
    operation each(c: Self, f: (x: Int64) -> Int64) -> Int64 effects {{EC}} = f(c.v)
  end
  operation go() -> Int64 = 0
{APP}end
"#
    );
    assert_refused_naming(
        &load_errors(&src),
        &["parameter 2 (`f: Int64 -> Int64`) takes less than the spec's"],
        "a callback row beside a projection",
    );
}

// ── the refusal names the repair ─────────────────────────────────────────────

/// A RECEIVER THE SPEC WRITES IS NAMED AS WRITTEN: behind `total(s: Sp[T = Int64], k)` the
/// receiver is every `Car[V = Int64]`, which `total(s: Car[V = String], k)` does not take — the
/// refusal says what the spec's receiver admits, and to type `s` as the spec writes it, not
/// that the member "fixes what the spec leaves open" (the spec fixed it).
#[test]
fn a_receiver_the_spec_writes_is_named_as_written() {
    let src = car_program(
        "wi0rp29mr.recvw",
        "operation total(s: Sp[T = Int64], k: Int64) -> Int64",
        "Sp[T = V]",
        "operation total(s: Car[V = String], k: Int64) -> Int64 = k",
        "\n  operation go() -> Int64 = 0\n",
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "`s` is the receiver",
            "does not take them all; type `s` as the spec writes it",
        ],
        "a receiver narrowed against what the spec writes",
    );
}

// ── the sixth review's fixes ─────────────────────────────────────────────────

/// `src` with `sort App` appended inside its namespace — a program whose last line is `end`.
fn with_app(src: &str) -> String {
    let at = src.rfind("end").expect("a namespace closes with `end`");
    format!("{}{APP}{}", &src[..at], &src[at..])
}

/// THE CARRIER-PARAM RECEIVER'S BINDING IS MET WITH THE INSTANCE, a row slot naming its own row
/// included: `C = Car[EC = {EC, Error[Foo]}]` receives every `Car` whose row holds `Error[Foo]`,
/// which a member written the same way takes. The meeting failed on the occurs check, and the
/// debug loader PANICKED on the `debug_assert!` behind it (MEASURED). Runs to 1.
#[test]
fn a_receiver_binding_naming_its_own_row_meets_the_instance() {
    let src = with_app(
        r#"
namespace wi0rp29mr6.extrow
  import anthill.prelude.{Int64, String, List, Error}
  sort Foo
    entity foo
  end
  sort Holder
    sort C = ?
    operation peek(c: C) -> Int64
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Holder[C = Car[EC = {EC, Error[Foo]}, V = V]]
    operation peek(c: Car[EC = {EC, Error[Foo]}, V = V]) -> Int64 = 1
  end
  operation go() -> Int64 =
    let b: Car[V = Int64, EC = {Error[Foo]}] = car(v: 5)
    Holder.peek(b)
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr6.extrow.go"), Ok(1));
}

/// … AND A DATA SLOT NAMING ITS OWN PARAMETER ADMITS NO INSTANCE: `C = Box[B = List[T = B]]`
/// writes `Box`'s own `B` inside `B`'s slot, and no `Box` is that type — refused at the
/// provision's member, with the repair. It PANICKED the debug loader (MEASURED); the release
/// build refused it printing two identical signatures.
#[test]
fn a_receiver_binding_naming_its_own_data_parameter_is_refused() {
    let src = r#"
namespace wi0rp29mr6.occurs
  import anthill.prelude.{Int64, String, List}
  sort Holder
    sort C = ?
    operation peek(c: C) -> Int64
  end
  sort Box
    sort B = ?
    entity box(inner: B)
    provides Holder[C = Box[B = List[T = B]]]
    operation peek(c: Box[B = List[T = B]]) -> Int64 = 1
  end
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "the provision binds its type to `Box[B = List[T = B]]`",
            "inside its own slot — no `Box` is that type",
            "write that slot as `?`",
        ],
        "a receiver binding circular in its own data slot",
    );
}

/// … THE MEETING READS A PARAMETER NAMED IN ANOTHER SLOT AS THE RECEIVER'S: `C = Car[V = Int64,
/// W = V]` receives a `Car` whose `W` is its `V` (WI-593's reading), so `peek(c: Car[V = Int64,
/// W = Int64])` takes every one. FAILS under ledger part 29 — the meeting reading `V` as a
/// pattern variable of its own (any `W`), which refuses this member — and under no other: it
/// is the row that holds the meeting to WI-593's reading, a control only in being the member
/// the rule must admit.
#[test]
fn a_receiver_binding_naming_its_own_data_parameter_is_refused_control() {
    let src = with_app(
        r#"
namespace wi0rp29mr6.noncirc
  import anthill.prelude.{Int64, String, List}
  sort Holder
    sort C = ?
    operation peek(c: C) -> Int64
  end
  sort Car
    sort V = ?
    sort W = ?
    entity car(v: V, w: W)
    provides Holder[C = Car[V = Int64, W = V]]
    operation peek(c: Car[V = Int64, W = Int64]) -> Int64 = match c case car(v, w) -> v + w
  end
  operation go() -> Int64 =
    let b: Car[V = Int64, W = Int64] = car(v: 3, w: 4)
    Holder.peek(b)
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr6.noncirc.go"), Ok(7));
}

/// A SELF-RECEIVER WRITTEN WITH THE OPERATION'S OWN TYPE PARAMETER BINDS IT FROM THE PROVISION:
/// `pick[U](s: Sp[T = U], x: U)` at `T = String` makes `x` a `String`, which `x: Int64` does not
/// take. Met against `U` made rigid first, the meeting failed and the WHOLE rule was skipped:
/// it loaded, and `Sp.pick(c, "str")` added 1 to a `String` at run time (MEASURED).
#[test]
fn a_self_receiver_written_with_an_operation_type_parameter_binds_it() {
    let src = r#"
namespace wi0rp29mr6.optp
  import anthill.prelude.{Int64, String, List}
  sort Sp
    sort T = ?
    operation pick[U](s: Sp[T = U], x: U) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = String]
    operation pick(s: Self, x: Int64) -> Int64 = x + 1
  end
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "parameter 2 (`x: Int64`) takes less than the spec's",
            "`String`",
        ],
        "x is the provision's String",
    );
}

/// … AND ITS CONTROL: at `T = Int64` the member's `x: Int64` is the spec's `U`, and it runs.
/// Passes either way by design: met against a rigid `U` the rule skipped the member, which then
/// loads — it guards the binding against refusing the member the provision fits.
#[test]
fn a_self_receiver_written_with_an_operation_type_parameter_binds_it_control() {
    let src = with_app(
        r#"
namespace wi0rp29mr6.optp_ok
  import anthill.prelude.{Int64, String, List}
  sort Sp
    sort T = ?
    operation op[U](s: Sp[T = U], x: U) -> Int64
  end
  sort Car
    entity car(v: Int64)
    provides Sp[T = Int64]
    operation op(s: Self, x: Int64) -> Int64 = x + 1
  end
  operation go() -> Int64 =
    let c: Car = car(v: 1)
    Sp.op(c, 5)
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr6.optp_ok.go"), Ok(6));
}

/// A WRITTEN RECEIVER ARGUMENT REACHES A PROVIDER BY ITS DECLARED VARIANCE: with `T`
/// covariant, `s: Sp[T = (a: Int64)]` receives a provider binding `T = (a: Int64, b: Int64)` —
/// so its member is compared, and the tie in `pick(s: Car, x: Car)` behind `U = Car[V = ?]`
/// (any `Car`) refused. Met by equality
/// alone, the provision read as unreachable and the member was skipped (MEASURED: it loaded, and
/// `r.v.length()` ran on an `Int64`).
#[test]
fn a_written_receiver_argument_reaches_a_provider_by_its_variance() {
    let src = r#"
namespace wi0rp29mr6.width
  import anthill.prelude.{Int64, Bool, Option, String, List}
  import anthill.reflect.typing.{Covariant}
  sort Sp
    sort T = ?
    sort U = ?
    fact Covariant(sort: Sp, param: T)
    operation pick(s: Sp[T = (a: Int64), U = U], x: U) -> U
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = (a: Int64, b: Int64), U = Car[V = ?]]
    operation pick(s: Self, x: Self) -> Self = s
  end
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "parameter 2 (`x: Car[V = V]`) takes less than the spec's",
            "THIS instance",
        ],
        "the tie behind a covariant written receiver",
    );
}

/// A WILDCARD SPEC PARAMETER BOUND TO A MEMBER VARIABLE STAYS ONE: the provision leaves `T`
/// unbound, `a: Option[T = T]` binds it to the member's `M`, and `b: List[T = T]` then binds `M`
/// to `Int64`. The spec side made every variable it reached rigid — `M` included — and refused
/// `b` in this order while the swapped one ran (MEASURED). Runs to 3.
#[test]
fn a_wildcard_bound_to_a_member_variable_is_not_frozen() {
    let src = with_app(
        r#"
namespace wi0rp29mr6.wild
  import anthill.prelude.{Int64, Bool, String, List, Option}
  import anthill.prelude.Option.{some, none}
  sort Sp
    sort T = ?
    operation op(s: Self, a: Option[T = T], b: List[T = T]) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp
    operation op[M](s: Self, a: Option[T = M], b: List[T = Int64]) -> Int64 = List.length(b)
  end
  operation go() -> Int64 =
    let c: Car[V = Int64] = car(v: 1)
    Sp.op(c, some(5), [1, 2, 3])
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr6.wild.go"), Ok(3));
}

/// A CALLBACK'S PARAMETER WIDER BY WIDTH FITS, IN EITHER ORDER: `f: (t: (a: X, b: Int64, c:
/// Int64)) -> Int64` takes every `(t: (a: Int64, b: Int64)) -> Int64` callback — contravariant,
/// so the MEMBER's tuple is aligned as the subtype. Walked without the flip, `X` stayed unbound
/// when `f` came before `x`, and it was refused (MEASURED; `x` first ran). Runs to 40 + 2.
#[test]
fn a_callback_parameter_wider_by_width_fits_in_either_order() {
    let src = with_app(
        r#"
namespace wi0rp29mr6.contra
  import anthill.prelude.{Int64, String, List}
  sort Sp
    sort T = ?
    operation fold(s: Self, f: (t: (a: Int64, b: Int64)) -> Int64, x: Int64) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation fold[X](s: Self, f: (t: (a: X, b: Int64, c: Int64)) -> Int64, x: X) -> Int64 = f((a: x, b: 2, c: 0))
  end
  operation go() -> Int64 = Sp.fold(car(v: 1), lambda (t: (a: Int64, b: Int64)) -> t.a + t.b, 40)
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr6.contra.go"), Ok(42));
}

/// … AND A `Contravariant` BINDING TURNS IT TOO: `Sink[T = (a: X, b: Int64, c: Int64)]` takes
/// every `Sink[T = (a: Int64, b: Int64)]`. Refused without the flip (MEASURED). Runs to 7.
#[test]
fn a_contravariant_binding_wider_by_width_fits() {
    let src = with_app(
        r#"
namespace wi0rp29mr6.contrasink
  import anthill.prelude.{Int64, String, List}
  import anthill.reflect.typing.{Contravariant}
  sort Sink
    sort T = ?
    entity sink(n: Int64)
  end
  fact Contravariant(sort: Sink, param: T)
  sort Sp
    sort T = ?
    operation put(s: Self, k: Sink[T = (a: Int64, b: Int64)]) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation put[X](s: Self, k: Sink[T = (a: X, b: Int64, c: Int64)]) -> Int64 = 7
  end
  operation go() -> Int64 = Sp.put(car(v: 1), sink(n: 1))
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr6.contrasink.go"), Ok(7));
}

/// … AND ITS CONTROL: a callback parameter genuinely NARROWER (`(t: (a: X))` behind `(t: (a:
/// Int64, b: Int64))`, which a callback reading `b` cannot be passed) is refused. Passes either
/// way by design: the verdict stays the relation's.
#[test]
fn a_callback_parameter_wider_by_width_fits_control() {
    let src = r#"
namespace wi0rp29mr6.contra_narrow
  import anthill.prelude.{Int64}
  sort Sp
    operation fold(s: Sp, f: (t: (a: Int64, b: Int64)) -> Int64) -> Int64
  end
  sort Car
    entity car(v: Int64)
    provides Sp
    operation fold[X](s: Car, f: (t: (a: X)) -> Int64) -> Int64 = 1
  end
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["parameter 2", "takes less than the spec's"],
        "a narrower callback parameter",
    );
}

/// A PROJECTION OVER A CARRIER-PARAM RECEIVER READS THE ARGUMENT'S TYPE: `put(c: C, k: c.V)` at
/// `C = Car` is the receiver's own `V` on both sides. Read off the spec at the provision, `c.V`
/// was the provision's `V = Int64`, and the member — the spec's own text — was refused printing
/// two identical signatures (MEASURED). Runs to 3.
#[test]
fn a_projection_over_a_carrier_param_receiver_reads_its_type() {
    let src = with_app(
        r#"
namespace wi0rp29mr6.cpproj
  import anthill.prelude.{Int64, Bool, Option, String, List}
  sort Coll
    sort C = ?
    sort V = ?
    operation put(c: C, k: c.V) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Coll[C = Self, V = Int64]
    operation put(c: Self, k: c.V) -> Int64 = 3
  end
  operation go() -> Int64 =
    let k1: Car[V = String] = car(v: "s")
    Coll.put(k1, "t")
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr6.cpproj.go"), Ok(3));
}

/// … AND ITS CONTROL: `k: Int64` there takes only the provision's `V`, where a call passes the
/// receiver's — `Coll.put(k1: Car[V = String], "t")` added 1 to a `String` (MEASURED). Refused.
/// FAILS under ledger part 68 (the carrier's own `V` read as the provision's `V = Int64`: `k:
/// Int64` is then the spec's, and the member loads) — a driving row, a control only in being
/// the wrongly typed twin of the row above.
#[test]
fn a_projection_over_a_carrier_param_receiver_reads_its_type_control() {
    let src = r#"
namespace wi0rp29mr6.cpproj_c
  import anthill.prelude.{Int64, Bool, Option, String, List}
  sort Coll
    sort C = ?
    sort V = ?
    operation put(c: C, k: c.V) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Coll[C = Self, V = Int64]
    operation put(c: Self, k: Int64) -> Int64 = k + 1
  end
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["parameter 2 (`k: Int64`) takes less than the spec's"],
        "k: Int64 behind the receiver's own V",
    );
}

/// `s.Self` IS THE RECEIVER'S TYPE, on both sides: `combine(c: Car, o: c.Self)` behind
/// `combine(s: Sp, o: s.Self)`. Read off the spec, it was refused (MEASURED). Runs to 3.
#[test]
fn a_sort_projection_reads_the_receivers_type() {
    let src = with_app(
        r#"
namespace wi0rp29mr6.sortproj
  import anthill.prelude.{Int64, Bool, Option, String, List}
  sort Sp
    sort T = ?
    operation combine(s: Self, o: s.Self) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation combine(c: Self, o: c.Self) -> Int64 = 3
  end
  operation use(x: Car[V = Int64], y: Car[V = Int64]) -> Int64 = Sp.combine(x, y)
  operation go() -> Int64 =
    let x: Car[V = Int64] = car(v: 1)
    let y: Car[V = Int64] = car(v: 2)
    use(x, y)
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr6.sortproj.go"), Ok(3));
}

/// THE CARRIER'S OWN PARAMETER IS READ BEFORE THE SPEC'S, as the call reads `s.T`: inside
/// `Car { sort T }`, `k: s.T` is the receiver's own `T`, which `k: T` is. Read off the spec it was
/// the provision's `List[T = T]`, and this member was refused (MEASURED). Runs to 3. FAILS
/// under ledger part 68.
#[test]
fn a_projection_reads_the_carriers_own_parameter_first() {
    let src = with_app(
        r#"
namespace wi0rp29mr6.collide
  import anthill.prelude.{Int64, String, List}
  sort Sp
    sort T = ?
    operation put(s: Self, k: s.T) -> Int64
  end
  sort Car
    sort T = ?
    entity car(v: T)
    provides Sp[T = List[T = T]]
    operation put(c: Self, k: T) -> Int64 = 3
  end
  operation go() -> Int64 =
    let c: Car[T = Int64] = car(v: 1)
    Sp.put(c, 5)
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr6.collide.go"), Ok(3));
}

/// A PROJECTION OVER ANY PROVIDER IS ANY TYPE: behind `put(s: Sp, o: Sp, k: o.T)`, `o` may be a
/// `StrCar` and `k` its `String`, so `k: Int64` is narrower. Skipped as "judged at the call", it
/// loaded, and `Sp.put(a, b, "str")` added 1 to a `String` — the ordinary dispatch path judges no
/// argument against the member (MEASURED).
#[test]
fn a_projection_over_any_provider_is_any_type() {
    let src = r#"
namespace wi0rp29mr6.other
  import anthill.prelude.{Int64, List, Bool, Option, String}
  sort Sp
    sort T = ?
    operation put(s: Self, o: Sp[T = ?], k: o.T) -> Int64
  end
  sort IntCar
    entity icar(v: Int64)
    provides Sp[T = Int64]
    operation put(c: IntCar, o: Sp, k: Int64) -> Int64 = k + 1
  end
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["parameter 3 (`k: Int64`) takes less than the spec's"],
        "k: Int64 behind any provider's T",
    );
}

/// A PERMUTED BINDING IS NOT THIS INSTANCE: `C = P2[A = B, B = A]` is not `P2` at its own
/// parameters (slot by slot), so the carrier-param receiver is the binding met with the instance,
/// which a member written as the binding takes. Read as this instance, the restriction was
/// dropped and this member refused printing identical types (MEASURED on the tree the sixth review
/// saw, whose member variables were the instance's). Runs to 1. With the per-slot reading backed
/// out it passes now — the member's variables are bound apart from the spec's side — so it pins the
/// regression, and [`a_permuted_received_binding_is_that_type`] the reading.
#[test]
fn a_permuted_binding_is_not_this_instance() {
    let src = with_app(
        r#"
namespace wi0rp29mr6.swap
  import anthill.prelude.{Int64, String, List}
  sort Holder
    sort C = ?
    operation peek(c: C) -> Int64
  end
  sort P2
    sort A = ?
    sort B = ?
    entity p2(a: A, b: B)
    provides Holder[C = P2[A = B, B = A]]
    operation peek(c: P2[A = B, B = A]) -> Int64 = 1
  end
  operation go() -> Int64 =
    let b: P2[A = Int64, B = String] = p2(a: 5, b: "s")
    Holder.peek(b)
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr6.swap.go"), Ok(1));
}

/// … AND A RECEIVED PARAMETER BOUND SO IS THAT TYPE, not this instance: `mix(s: Coll, c: C)` at
/// `C = P2[A = B, B = A]` passes a swapped instance, which `c: P2` (this one) is not. Read as this
/// instance it loaded, and the call ran a `String` callback on an `Int64` (MEASURED).
#[test]
fn a_permuted_received_binding_is_that_type() {
    let src = r#"
namespace wi0rp29mr6.swap_recv
  import anthill.prelude.{Int64, String, List}
  sort Coll
    sort C = ?
    operation size(c: C) -> Int64
    operation mix(s: Self, c: C) -> Int64
  end
  sort P2
    sort A = ?
    sort B = ?
    entity p2(a: A, b: B, g: (x: A) -> Int64)
    provides Coll[C = P2[A = B, B = A]]
    operation size(c: P2[A = B, B = A]) -> Int64 = 1
    operation mix(s: Self, c: Self) -> Int64 = match s case p2(_, _, g) -> g(c.a)
  end
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["parameter 2 (`c: P2[A = A, B = B]`) takes less than the spec's"],
        "c: P2 behind a swapped instance",
    );
}

/// ONE BINDING IS ONE TYPE WHEREVER IT IS READ: `two(s, a: T, b: T)` at `T = Pair[A = List, B =
/// Int64]` passes one pair type twice (the call ties them), which a member tying their element
/// takes. Expanded per occurrence, `a` and `b` were two `List`s and it was refused (MEASURED; the
/// nested case was new in the fifth pass). Runs to 6.
#[test]
fn one_binding_is_one_type_wherever_it_is_read() {
    let src = with_app(
        r#"
namespace wi0rp29mr6.tie
  import anthill.prelude.{Int64, String, Bool, List, Pair}
  import anthill.prelude.Pair.{pair}
  sort Sp
    sort T = ?
    operation two(s: Self, a: T, b: T) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = Pair[A = List, B = Int64]]
    operation two[W](s: Self, a: Pair[A = List[T = W], B = Int64], b: Pair[A = List[T = W], B = Int64]) -> Int64 =
      match a
        case pair(xs, _) -> 6
  end
  operation go() -> Int64 =
    let c: Car[V = Int64] = car(v: 1)
    let ys: List[T = Int64] = [1, 2]
    let x: Pair[A = List[T = Int64], B = Int64] = pair(fst: ys, snd: 1)
    Sp.two(c, x, x)
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr6.tie.go"), Ok(6));
}

/// … A WITNESS'S TOO: `mix(c: C, d: C)` at `BoxHolder provides Holder[C = Box]` passes one `Box`
/// twice. Refused as two independent ones (MEASURED). Runs to 41 + 2.
#[test]
fn one_binding_is_one_type_for_a_witness() {
    let src = with_app(
        r#"
namespace wi0rp29mr6.wit
  import anthill.prelude.{Int64, String, List}
  sort Holder
    sort C = ?
    operation peek(c: C) -> Int64
    operation mix(c: C, d: C) -> Int64
  end
  sort Box
    sort B = ?
    entity box(inner: B, f: (x: B) -> Int64)
  end
  sort BoxHolder
    import anthill.prelude.Int64
    provides Holder[C = Box]
    operation peek(c: Box) -> Int64 = 2
    operation mix[W](c: Box[B = W], d: Box[B = W]) -> Int64 =
      match c
        case box(_, g) -> g(d.inner)
  end
  operation go() -> Int64 =
    let b1: Box[B = Int64] = box(inner: 3, f: lambda (x: Int64) -> x + 1)
    let b2: Box[B = Int64] = box(inner: 40, f: lambda (x: Int64) -> x + 2)
    Holder.mix(b1, b2) + Holder.peek(b1)
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr6.wit.go"), Ok(43));
}

/// A NESTED TIE IS NAMED AS ONE: `xs: List[T = Car]` behind `xs: List[T = T]` at `T = Car[V =
/// ?]` (any `Car`) ties the element to the receiver; the refusal said "widen the member's
/// parameter to the spec's type", which it already was (MEASURED).
#[test]
fn a_nested_tie_is_named_as_one() {
    let src = car_program(
        "wi0rp29mr6.nested_tie",
        "operation pick(s: Self, xs: List[T = T]) -> Int64",
        "Sp[T = Car[V = ?]]",
        "operation pick(s: Self, xs: List[T = Self]) -> Int64 = List.length(xs)",
        "\n  operation go() -> Int64 = 0\n",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["parameter 2", "is THIS instance (the parametricity tie)"],
        "a tie inside a List",
    );
}

/// A PROJECTION POSITION'S REFUSAL PRINTS THE TYPE COMPARED: behind `put(s: Sp, k: s.T)` at `T =
/// List[T = Int64]` the spec passes a `List[T = Int64]`, and the refusal says so — not the
/// unreduced `s.T` (MEASURED).
#[test]
fn a_projection_refusal_prints_the_type_compared() {
    let src = with_app(
        r#"
namespace wi0rp29mr6.putpair
  import anthill.prelude.{Int64, String, List}
  sort Sp
    sort T = ?
    operation put(s: Self, k: s.T) -> Int64
  end
  sort IntCar
    entity intcar(v: Int64)
    provides Sp[T = List[T = Int64]]
    operation put(c: IntCar, k: Int64) -> Int64 = k + 1
  end
  operation go() -> Int64 = 0
end
"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &["the spec's `List[T = Int64]` admits arguments the member's `Int64` does not"],
        "the projection as read",
    );
}

/// … AND A CALLBACK'S ROW: the two arrows differ only in their rows, which the refusal prints.
#[test]
fn a_callback_refusal_prints_its_row() {
    let src = with_app(
        r#"
namespace wi0rp29mr6.cbrow
  import anthill.prelude.{Int64, String, List}
  sort Sp
    sort T = ?
    effects E = ?
    operation each[EP](s: Self, f: (x: s.T) -> Int64 @ {EP}) -> Int64 effects {s.E, EP}
  end
  sort Car
    effects EC = ?
    entity car(v: Int64)
    provides Sp[T = Int64, E = {EC}]
    operation each(c: Self, f: (x: Int64) -> Int64) -> Int64 effects {EC} = f(c.v)
  end
  operation go() -> Int64 = 0
end
"#,
    );
    assert_refused_naming(&load_errors(&src), &["@ {"], "the callback's row printed");
}

/// A CALLBACK ROW NAMING A PARAMETER BY VALUE IS COMPARED BY THE SPEC'S NAMES: `Modify[p]` names
/// the spec's `p` in the spec and the member's in the member — two symbols — so the member, the
/// spec's own text, was refused printing two identical arrows (MEASURED). Runs to 5.
#[test]
fn a_row_naming_a_parameter_is_compared_by_the_specs_names() {
    let src = with_app(
        r#"
namespace wi0rp29mr6.denoted
  import anthill.prelude.{Int64, String, List, Cell, Modify, Unit}
  sort Sp
    sort T = ?
    operation each[EP](s: Self, p: Cell[V = Int64], f: (x: Int64) -> Int64 @ {EP, Modify[p]}) -> Int64 effects {EP, Modify[p]}
  end
  sort Car
    entity car(v: Int64)
    provides Sp[T = Int64]
    operation each[EP](c: Car, p: Cell[V = Int64], f: (x: Int64) -> Int64 @ {EP, Modify[p]}) -> Int64 effects {EP, Modify[p]} = f(c.v)
  end
  operation go() -> Int64 =
    let k: Car = car(v: 4)
    let c: Cell[V = Int64] = Cell.new(1)
    Sp.each[EP = {}](k, c, lambda (x: Int64) -> x + 1)
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr6.denoted.go"), Ok(5));
}

/// … AND IN THE PER-POSITION COMPARISON: the same with a ground row, which that comparison
/// decides, refused since WI-20260822-1MAGR (MEASURED). Runs to 4.
#[test]
fn a_ground_row_naming_a_parameter_is_compared_by_the_specs_names() {
    let src = with_app(
        r#"
namespace wi0rp29mr6.denoted_ground
  import anthill.prelude.{Int64, String, List, Cell, Modify, Unit}
  sort Sp
    sort T = ?
    operation each(s: Self, p: Cell[V = Int64], f: (x: Int64) -> Int64 @ {Modify[p]}) -> Int64 effects {Modify[p]}
  end
  sort Car
    entity car(v: Int64)
    provides Sp[T = Int64]
    operation each(c: Car, p: Cell[V = Int64], f: (x: Int64) -> Int64 @ {Modify[p]}) -> Int64 effects {Modify[p]} = f(c.v)
  end
  operation go() -> Int64 =
    let k: Car = car(v: 4)
    let c: Cell[V = Int64] = Cell.new(1)
    Sp.each(k, c, lambda (x: Int64) -> let _ = Cell.set(c, x)
      x)
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr6.denoted_ground.go"), Ok(4));
}

/// THE RETURN IS COMPARED WHERE IT HOLDS A PROJECTION: `pick(s: Sp) -> Option[T = s.T]` at `T =
/// List[T = Int64]` promises a list, which `-> Option[T = V]` does not return. Never compared, it
/// loaded, and the caller's `List.length` ran on an `Int64` (MEASURED).
#[test]
fn a_return_holding_a_projection_is_compared() {
    let src = r#"
namespace wi0rp29mr6.ret
  import anthill.prelude.{Int64, Bool, Option, String, List}
  import anthill.prelude.Option.{some, none}
  sort Sp
    sort T = ?
    operation pick(s: Self) -> Option[T = s.T]
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = List[T = Int64]]
    operation pick(c: Self) -> Option[T = V] = some(c.v)
  end
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "the member returns `Option[T = ?V]`",
            "not a subtype of the spec's `Option[T = List[T = Int64]]`",
        ],
        "the return against the spec's",
    );
}

/// … AND ITS CONTROL: `-> Option[T = List[T = Int64]]` is the spec's, and it loads. Passes either
/// way by design: it guards the comparison against reading the spec's return too narrowly.
#[test]
fn a_return_holding_a_projection_is_compared_control() {
    let src = r#"
namespace wi0rp29mr6.ret_ok
  import anthill.prelude.{Int64, Bool, Option, String, List}
  import anthill.prelude.Option.{some, none}
  sort Sp
    sort T = ?
    operation pick(s: Self) -> Option[T = s.T]
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = List[T = Int64]]
    operation pick(c: Self) -> Option[T = List[T = Int64]] = none
  end
end
"#;
    assert!(load_errors(src).is_empty(), "{:?}", load_errors(src));
}

/// `Sp.op(s: Sp, x: Strm[T = Int64, E = {spec_row}])` at `Car provides Sp[T = V]`, the member's
/// `x` typed `Strm[T = Int64, E = {member_row}]` (with `member_binder`, its own type
/// parameters), and `go` calling `Sp.op` over a stream raising `Error[Bool]`, its row spelled
/// as the spec's is (bare, or braced).
fn row_label_program(ns: &str, spec_row: &str, member_binder: &str, member_row: &str) -> String {
    let arg_row = if spec_row.starts_with('{') {
        "{Error[T = Bool]}"
    } else {
        "Error[T = Bool]"
    };
    with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String, List, Error}}
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(v: T)
  end
  sort Sp
    sort T = ?
    operation op(s: Self, x: Strm[T = Int64, E = {spec_row}]) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation op{member_binder}(s: Self, x: Strm[T = Int64, E = {member_row}]) -> Int64 = 7
  end
  operation go() -> Int64 =
    let y: Strm[T = Int64, E = {arg_row}] = strm(v: 1)
    Sp.op(car(v: 1), y)
end
"#
    ))
}

/// A LABEL IN A ROW SLOT IS A SORT APPLICATION, AND ITS UNWRITTEN SLOT ANY TYPE: `x: Strm[T =
/// Int64, E = Error]` — bare, or braced `{Error}` — is a stream raising `Error` at ANY payload,
/// which a spec call passes (the row's own program hands it one raising `Error[Bool]`). So a
/// member taking only `E = Error[T = String]` takes less, in either spelling. The sixth pass
/// kept the label bare on the spec side to agree with the braced spelling, which had always
/// loaded: both met the member's label by binding `Error`'s one canonical `T` (MEASURED: the
/// braced twin reified `Error[String]`, was handed `Error[Bool]`, and a pure `main` ended in
/// "error: true"). FAILS under ledger part 58 (the labels kept as written: each member loads).
#[test]
fn a_label_in_a_row_slot_is_any_payload() {
    for (tag, spec_row, member_row) in [
        ("bare", "Error", "Error[T = String]"),
        ("braced", "{Error}", "{Error[T = String]}"),
    ] {
        let src = row_label_program(
            &format!("wi0rp29mr7.rowlabel_{tag}"),
            spec_row,
            "",
            member_row,
        );
        assert_refused_naming(
            &load_errors(&src),
            &[
                "parameter 2 (`x: Strm[T = Int64, E = ",
                "takes less than the spec's",
            ],
            &format!("a narrower row label, {tag}"),
        );
    }
}

/// … AND ITS CONTROLS: the member written as the spec, in each spelling, and the member whose
/// label takes a payload of its own (`op[W](…, E = Error[T = W])`) take every stream the spec
/// does — each runs through the spec call, to 7. Pass either way by design: members the rule
/// must not refuse.
#[test]
fn a_label_in_a_row_slot_is_any_payload_control() {
    for (tag, spec_row, binder, member_row) in [
        ("bare", "Error", "", "Error"),
        ("braced", "{Error}", "", "{Error}"),
        ("own", "Error", "[W]", "Error[T = W]"),
    ] {
        let ns = format!("wi0rp29mr7.rowlabel_ok_{tag}");
        let src = row_label_program(&ns, spec_row, binder, member_row);
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(7), "{tag}");
    }
}

// ── the seventh review's fixes ───────────────────────────────────────────────

/// `Mon2 { T; U; pair(xs: List[T = T], ys: List[T = U]) }` at `Car provides {provision}` — an
/// operation with NO RECEIVER in a two-parameter spec — with `member` as `Car`'s own `pair`,
/// and `go`'s body.
fn mon2_program(ns: &str, provision: &str, member: &str, go: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  import anthill.prelude.List.{{cons, nil}}
  sort Mon2
    sort T = ?
    sort U = ?
    operation pair(xs: List[T = T], ys: List[T = U]) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V, n: Int64)
    provides {provision}
    {member}
  end
  operation go() -> Int64 =
    {go}
{APP}end
"#
    )
}

/// AN OPERATION WITH NO RECEIVER IS COMPARED: a spec call reaches its member wherever the call
/// fixes the spec's parameters — here by its arguments — so `pair(xs: List[T = Car[V = Int64]],
/// …)` behind `pair(xs: List[T = T], …)` at `T = Car` takes less than the spec. Skipped as "reached
/// by its qualified call alone" (the sixth pass), the member LOADED, and `Mon2.pair` over a
/// `Car[V = String]` died in its body: "type mismatch: expected Int64, got String and Int64"
/// (MEASURED). FAILS when the skip is put back (ledger part 47).
#[test]
fn an_operation_with_no_receiver_is_compared() {
    let src = mon2_program(
        "wi0rp29mr7.norecv",
        "Mon2[T = Self, U = Self]",
        "operation pair(xs: List[T = Car[V = Int64]], ys: List[T = Self]) -> Int64 =\n      \
         match xs\n        case cons(h, t) -> h.v + 1\n        case nil() -> 0",
        "let c1: Car[V = String] = car(v: \"s\", n: 1)\n    Mon2.pair(cons(c1, nil), cons(c1, nil))",
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "parameter 1 (`xs: List[T = Car[V = Int64]]`) takes less than the spec's",
            "widen the member's parameter to the spec's type",
        ],
        "a receiver-less member narrower than its spec",
    );
}

/// … AND ITS CONTROL: behind two independent instances, written `Mon2[T = Car[V = ?], U = Car[V
/// = ?]]`, `ys`'s `Car` given a type argument of its own takes every pair of lists the spec does,
/// and the SPEC CALL runs it — the dispatch the skip said could not happen. Runs to 2 + 2. Passes
/// with the skip too, by design (a member not compared loads): it guards the rule against
/// refusing a member as wide as its spec, pins that `Mon2.pair` reaches the member, and is the
/// tie refusal's first repair. FAILS under ledger part 49 (the member's instance rigid).
#[test]
fn an_operation_with_no_receiver_is_compared_control() {
    let src = mon2_program(
        "wi0rp29mr7.norecv_ok",
        "Mon2[T = Car[V = ?], U = Car[V = ?]]",
        "operation pair[W](xs: List[T = Self], ys: List[T = Car[V = W]]) -> Int64 =\n      \
         List.length(xs) + List.length(ys)",
        "let c1: Car[V = Int64] = car(v: 1, n: 1)\n    let c2: Car[V = Int64] = car(v: 2, n: 2)\n    \
         Mon2.pair(cons(c1, cons(c2, nil)), cons(c2, cons(c1, nil)))",
    );
    assert_eq!(run_int64(&src, "wi0rp29mr7.norecv_ok.go"), Ok(4));
}

/// WITH NO RECEIVER, A BARE BINDING IS STILL THIS INSTANCE: `Mon2[T = Car, U = Car]` written
/// inside `sort Car` binds both parameters to one `Car`, as `pair(xs: List[T = Car], ys: List[T
/// = Car])` reads its own two — the member is exactly the spec's, and `Mon2.pair` runs it at one
/// instance, to 2. Dispatch read the clause that way all along: over two DIFFERENT instances
/// `Mon2.pair` finds no provision ("operation has no body", at run time — the call's type check
/// is not yet held to the clause, WI-20260929-05ZQE). INTERIM (user, 2026-10-01; WI-20261001-80ZV8
/// changes both readings together). The sixth pass skipped this operation, and the seventh's
/// first cut refused the member as tying two independent instances. FAILS under ledger part 50.
#[test]
fn an_operation_with_no_receiver_reads_a_bare_binding_as_this_instance() {
    let src = mon2_program(
        "wi0rp29mr7.norecv_this",
        "Mon2[T = Self, U = Self]",
        "operation pair(xs: List[T = Self], ys: List[T = Self]) -> Int64 = List.length(xs) + List.length(ys)",
        "let c1: Car[V = Int64] = car(v: 1, n: 1)\n    Mon2.pair(cons(c1, nil), cons(c1, nil))",
    );
    assert_eq!(run_int64(&src, "wi0rp29mr7.norecv_this.go"), Ok(2));
}

/// … AND A TIE WITH NO RECEIVER NAMES WHAT IT IS TIED TO: behind two independent instances,
/// written `Mon2[T = Car[V = ?], U = Car[V = ?]]`, the member's two bare `Car`s tie what the
/// spec leaves apart — refused naming the FIRST parameter that took the instance, since there
/// is no receiver. FAILS when the skip is put back (part 47), under part 48 (the wording: "ties
/// `ys` to the receiver") and under part 49 (refused at parameter 1 instead).
#[test]
fn an_operation_with_no_receiver_names_what_a_tie_is_tied_to() {
    let src = mon2_program(
        "wi0rp29mr7.norecv_tie",
        "Mon2[T = Car[V = ?], U = Car[V = ?]]",
        "operation pair(xs: List[T = Self], ys: List[T = Self]) -> Int64 = List.length(xs) + List.length(ys)",
        "let c1: Car[V = Int64] = car(v: 1, n: 1)\n    Mon2.pair(cons(c1, nil), cons(c1, nil))",
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "parameter 2 (`ys: List[T = Car[V = V]]`) takes less than the spec's",
            "ties `ys` to `xs`",
            "is an instance of its own",
        ],
        "two bare carriers tied behind two independent spec parameters",
    );
}

/// … AND THE TIE WRITTEN INTO THE SPEC (the refusal's second repair): `pair(xs: List[T = T], ys:
/// List[T = T])` at `T = Car[V = ?]` — any ONE `Car` — is met by the member that ties them,
/// reached here through a call-site BRACKET (`U` is in no argument). The member's own parameters are bound by the first position that
/// names them, as a call binds them; read as a rigid instance of their own (the fifth pass), a
/// member naming its instance where no receiver fixed it was refused at parameter 1 (MEASURED on
/// the sixth review's tree). Runs to 2 + 2. Passes with the skip too, by design. FAILS under
/// part 49.
#[test]
fn an_operation_with_no_receiver_binds_the_members_instance_by_its_first_position() {
    let src = with_app(
        r#"
namespace wi0rp29mr7.norecv_first
  import anthill.prelude.{Int64, String, List}
  import anthill.prelude.List.{cons, nil}
  sort Mon2
    sort T = ?
    sort U = ?
    operation pair(xs: List[T = T], ys: List[T = T]) -> Int64
    operation other(u: U) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V, n: Int64)
    provides Mon2[T = Car[V = ?], U = Int64]
    operation pair(xs: List[T = Self], ys: List[T = Self]) -> Int64 = List.length(xs) + List.length(ys)
    operation other(u: Int64) -> Int64 = u
  end
  operation go() -> Int64 =
    let c1: Car[V = Int64] = car(v: 1, n: 1)
    let c2: Car[V = Int64] = car(v: 2, n: 2)
    Mon2.pair[U = Int64](cons(c1, cons(c2, nil)), cons(c2, cons(c1, nil)))
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr7.norecv_first.go"), Ok(4));
}

/// `Mon2 { C; T; zap(xs: List[T = T], y: Option) }` at `Car provides Mon2[C = Car, T = Int64]`,
/// reached through an operation-level `requires` DICTIONARY (`C` is in no argument), with
/// `member` as `Car`'s own `zap`.
fn requires_program(ns: &str, member: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List, Option}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.List.{{cons, nil}}
  sort Mon2
    sort C = ?
    sort T = ?
    operation zap(xs: List[T = T], y: Option) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Mon2[C = Self, T = Int64]
    {member}
  end
  operation use[X](x: Int64) -> Int64 requires Mon2[C = X, T = Int64] = Mon2.zap(cons(x, nil), some(7))
  operation go() -> Int64 = use[X = Car](1)
{APP}end
"#
    )
}

/// A `requires` DICTIONARY REACHES AN OPERATION WITH NO RECEIVER TOO: the spec's bare `Option`
/// takes any option, the member's `y: Option[T = String]` only one of strings. Skipped, the
/// member loaded and `use[X = Car](1)` handed it `some(7)`: "type mismatch: expected String, got
/// Int64" (MEASURED). FAILS when the skip is put back (part 47).
#[test]
fn a_requires_dictionary_reaches_an_operation_with_no_receiver() {
    let src = requires_program(
        "wi0rp29mr7.req",
        "operation zap(xs: List[T = Int64], y: Option[T = String]) -> Int64 =\n      \
         match y\n        case some(s) -> String.length(s)\n        case none() -> 0",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["parameter 2 (`y: Option[T = String]`) takes less than the spec's"],
        "a receiver-less member narrower than its spec, reached through a requires dictionary",
    );
}

/// … AND ITS CONTROL: the member written as the spec runs through the dictionary, to 5. Passes
/// either way by design: it pins that the dictionary reaches the member.
#[test]
fn a_requires_dictionary_reaches_an_operation_with_no_receiver_control() {
    let src = requires_program(
        "wi0rp29mr7.req_ok",
        "operation zap(xs: List[T = Int64], y: Option) -> Int64 =\n      \
         match y\n        case some(s) -> 5\n        case none() -> 0",
    );
    assert_eq!(run_int64(&src, "wi0rp29mr7.req_ok.go"), Ok(5));
}

/// A WITNESS providing `Mon[T = Tag]` for a `Tag` it does not declare, `member` its own `total`.
fn witness_program(ns: &str, member: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  import anthill.prelude.List.{{cons, nil}}
  sort Tag
    sort X = ?
    entity tag(x: X)
  end
  sort Mon
    sort T = ?
    operation total(xs: List[T = T]) -> Int64
  end
  sort TagMon
    provides Mon[T = Tag]
    {member}
  end
  operation go() -> Int64 =
    let xs: List[T = Tag[X = String]] = cons(tag(x: "s"), nil)
    Mon.total(xs)
{APP}end
"#
    )
}

/// A WITNESS'S OPERATION WITH NO RECEIVER IS COMPARED: `Mon` dispatches on its sole parameter
/// (WI-1102), which a witness binds to ANOTHER sort — so the sixth pass's "sole parameter bound to
/// the declaring sort" test missed it, and `total(xs: List[T = Tag[X = Int64]])` loaded and died
/// on a `Tag[X = String]` (MEASURED). FAILS when the skip is put back (part 47).
#[test]
fn a_witness_operation_with_no_receiver_is_compared() {
    let src = witness_program(
        "wi0rp29mr7.wit",
        "operation total(xs: List[T = Tag[X = Int64]]) -> Int64 =\n      \
         match xs\n        case cons(h, t) -> h.x + 1\n        case nil() -> 0",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["parameter 1 (`xs: List[T = Tag[X = Int64]]`) takes less than the spec's"],
        "a witness's receiver-less member narrower than its spec",
    );
}

/// … AND ITS CONTROL: `total(xs: List[T = Tag])` — a foreign sort's unwritten slot, any `Tag` —
/// is the spec's, and `Mon.total` runs it over a `Tag[X = String]`, to 7. Passes either way by
/// design: it pins that the spec call reaches the witness's member.
#[test]
fn a_witness_operation_with_no_receiver_is_compared_control() {
    let src = witness_program(
        "wi0rp29mr7.wit_ok",
        "operation total(xs: List[T = Tag]) -> Int64 =\n      \
         match xs\n        case cons(h, t) -> 7\n        case nil() -> 0",
    );
    assert_eq!(run_int64(&src, "wi0rp29mr7.wit_ok.go"), Ok(7));
}

/// `Sp.op(s: Sp[K = List, W = List], k: s.W)` at `Car provides Sp[K = List[T = Int64], W =
/// List[T = String]]`, `Car`'s own `op` taking `k: List[T = {elem}]` and answering `{body}`.
fn two_lists_program(ns: &str, elem: &str, body: &str) -> String {
    with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  import anthill.prelude.List.{{cons, nil}}
  sort Sp
    sort K = ?
    sort W = ?
    operation op(s: Sp[K = List, W = List], k: s.W) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[K = List[T = Int64], W = List[T = String]]
    operation op(s: Self, k: List[T = {elem}]) -> Int64 =
      match k
        case cons(h, t) -> {body}
        case nil() -> 0
  end
  operation go() -> Int64 = Sp.op(car(v: 1), ["abcde"])
end
"#
    ))
}

/// A WRITTEN RECEIVER ARGUMENT'S FOREIGN SORT IS FRESH PER OCCURRENCE: `s: Sp[K = List, W =
/// List]` writes two lists, as the spec's own text reads everywhere (WI-374). Met unexpanded,
/// both bound `List`'s one canonical `T`; this provision's two element types then read as a
/// contradiction, the provision as unreachable, and the operation went uncompared — so `k:
/// List[T = Int64]` behind `k: s.W` (a list of strings) LOADED, and `Sp.op(c, ["abcde"])` died
/// "expected Int64, got String and Int64" (MEASURED; the sixth review's tree refused it). FAILS
/// under ledger part 52.
#[test]
fn a_written_receiver_argument_is_fresh_per_occurrence() {
    assert_refused_naming(
        &load_errors(&two_lists_program("wi0rp29mr7.two_lists", "Int64", "h + 1")),
        &["parameter 2 (`k: List[T = Int64]`) takes less than the spec's"],
        "a member narrower than `s.W` behind two bare lists",
    );
}

/// … AND ITS CONTROL: `k: List[T = String]` is the spec's, and the spec call runs it, to 5.
/// Passes either way by design: it pins that the call reaches this member.
#[test]
fn a_written_receiver_argument_is_fresh_per_occurrence_control() {
    let ns = "wi0rp29mr7.two_lists_ok";
    assert_eq!(
        run_int64(
            &two_lists_program(ns, "String", "String.length(h)"),
            &format!("{ns}.go")
        ),
        Ok(5)
    );
}

/// `Sp.op[U](s: Sp[T = (a: U)], x: U)` with `T` covariant, at `Car provides Sp[T = (a: Int64,
/// b: Int64)]`; `Car`'s own `op` takes `x: {x_ty}`.
fn receiver_variance_program(ns: &str, x_ty: &str, body: &str) -> String {
    with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  import anthill.reflect.typing.{{Covariant}}
  sort Sp
    sort T = ?
    fact Covariant(sort: Sp, param: T)
    operation op[U](s: Sp[T = (a: U)], x: U) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = (a: Int64, b: Int64)]
    operation op(s: Self, x: {x_ty}) -> Int64 = {body}
  end
  operation go() -> Int64 = Sp.op(car(v: 1), 5)
end
"#
    ))
}

/// A WRITTEN RECEIVER ARGUMENT REACHED BY VARIANCE BINDS THE OPERATION'S PARAMETER: `s: Sp[T =
/// (a: U)]` receives a provider at `T = (a: Int64, b: Int64)` (wider, `T` covariant) with `U =
/// Int64`, as the call binds it — so `x: String` behind `x: U` takes less. The relation binds
/// nothing, so with `U` unbound it failed, the provision read as unreachable, and the member
/// LOADED: `Sp.op(c, 5)` died "expected String, got Int64" (MEASURED, on the sixth review's tree
/// too). FAILS under ledger part 53.
#[test]
fn a_receiver_reached_by_variance_binds_the_operations_parameter() {
    assert_refused_naming(
        &load_errors(&receiver_variance_program(
            "wi0rp29mr7.var_bind",
            "String",
            "String.length(x)",
        )),
        &["parameter 2 (`x: String`) takes less than the spec's"],
        "x narrower than the U the receiver binds",
    );
}

/// … AND ITS CONTROL: `x: Int64` is the spec's at this provision, and runs: 5 + 1. Passes
/// either way by design.
#[test]
fn a_receiver_reached_by_variance_binds_the_operations_parameter_control() {
    let ns = "wi0rp29mr7.var_bind_ok";
    assert_eq!(
        run_int64(
            &receiver_variance_program(ns, "Int64", "x + 1"),
            &format!("{ns}.go")
        ),
        Ok(6)
    );
}

/// `Holder.peek(c: C)` at `Box provides Holder[C = Box[B = List]]` — a box of ANY list — with
/// `Box`'s own `peek` taking `c: Box[B = {inner}]`.
fn box_of_list_program(ns: &str, inner: &str, body: &str) -> String {
    with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  import anthill.prelude.List.{{cons, nil}}
  sort Holder
    sort C = ?
    operation peek(c: C) -> Int64
  end
  sort Box
    sort B = ?
    entity box(inner: B)
    provides Holder[C = Box[B = List]]
    operation peek(c: Box[B = {inner}]) -> Int64 =
      match c.inner
        case cons(h, t) -> {body}
        case nil() -> 0
  end
  operation go() -> Int64 = Holder.peek(box(inner: ["s"]))
end
"#
    ))
}

/// A FOREIGN SORT'S UNWRITTEN SLOT IN THE RECEIVER'S BINDING IS ANY TYPE: `C = Box[B = List]`
/// receives a box of any list, so `peek(c: Box[B = List[T = Int64]])` takes less. Met as
/// written, the bare `List` bound its one canonical `T` to the member's `Int64` and the member
/// was admitted — `Holder.peek(box(inner: ["s"]))` died "expected Int64, got String and Int64"
/// (MEASURED on every build), where the same binding written `List[T = ?]` was refused. FAILS
/// under ledger part 54.
#[test]
fn a_receiver_bindings_unwritten_slot_is_any_type() {
    assert_refused_naming(
        &load_errors(&box_of_list_program(
            "wi0rp29mr7.box_list",
            "List[T = Int64]",
            "h + 1",
        )),
        &["parameter 1 (`c: Box[B = List[T = Int64]]`) takes less than the spec's"],
        "a receiver narrower than its binding's bare list",
    );
}

/// … AND ITS CONTROL: `c: Box[B = List]` is the binding's, and runs, to 7. Passes either way
/// by design.
#[test]
fn a_receiver_bindings_unwritten_slot_is_any_type_control() {
    let ns = "wi0rp29mr7.box_list_ok";
    assert_eq!(
        run_int64(&box_of_list_program(ns, "List", "7"), &format!("{ns}.go")),
        Ok(7)
    );
}

/// A RECEIVER BINDING CIRCULAR AROUND ANOTHER PARAMETER ADMITS NO INSTANCE, AND SAYS SO: `C =
/// Graph[N = List[T = E], E = Pair[A = N, B = N]]` asks for an `N` that is a list of pairs of
/// itself. Unification's occurs check reads each binding as written, so the second passed it,
/// and the next deep resolve did not return: the LOADER overflowed its stack (MEASURED, on the
/// sixth review's tree too; only the direct `B = List[T = B]` was refused). FAILS under ledger
/// part 55 — measured with the CLI, since the overflow aborts the whole test binary.
#[test]
fn a_receiver_binding_circular_around_another_parameter_is_refused() {
    let src = r#"
namespace wi0rp29mr7.graph
  import anthill.prelude.{Int64, String, List, Pair}
  sort Holder
    sort C = ?
    operation size(c: C) -> Int64
  end
  sort Graph
    sort N = ?
    sort E = ?
    entity graph(nodes: List[T = N], edges: List[T = E])
    provides Holder[C = Graph[N = List[T = E], E = Pair[A = N, B = N]]]
    operation size(c: Self) -> Int64 = 0
  end
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "parameter 1 (`c: Graph[E = E, N = N]`) is the receiver",
            "which writes one of `Graph`'s own parameters inside its own slot",
        ],
        "a binding circular around another parameter",
    );
}

/// … AND A WRITTEN RECEIVER ARGUMENT THAT ADMITS NO RECEIVER IS NOT REACHED: `s: Sp[T = List[T
/// = U], W = U]` at `T = V, W = List[T = V]` asks for a `V` that is a list of lists of itself,
/// so the provision's member is not compared and the program loads; the spec call is the
/// call's to refuse. The same overflow before (MEASURED). FAILS under ledger part 55, as above.
#[test]
fn a_written_receiver_argument_admitting_no_receiver_is_not_reached() {
    let src = r#"
namespace wi0rp29mr7.cyc_self
  import anthill.prelude.{Int64, String, List}
  sort Sp
    sort T = ?
    sort W = ?
    operation op[U](s: Sp[T = List[T = U], W = U], x: Int64) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V, W = List[T = V]]
    operation op[U](s: Self, x: Int64) -> Int64 = 1
  end
end
"#;
    let errs = load_errors(src);
    assert!(
        errs.is_empty(),
        "an unreachable provision's member is not compared: {errs:#?}"
    );
}

/// A ROW SLOT THAT IS ANOTHER PARAMETER'S ROW IS THAT ROW: `C = Car[EC = {EF}, EF = {EC}]`
/// receives every `Car` whose two rows are one, which the member taking any `Car` covers — it
/// runs, to 1. Bound as a row AROUND the other, the two slots bound each row inside the other:
/// the loader overflowed its stack (MEASURED), and under the cycle check alone the binding is
/// refused as circular. FAILS under ledger part 56.
#[test]
fn a_row_slot_that_is_another_parameters_row_is_that_row() {
    let src = with_app(
        r#"
namespace wi0rp29mr7.row_diag
  import anthill.prelude.{Int64, String, List}
  sort Holder
    sort C = ?
    operation peek(c: C) -> Int64
  end
  sort Car
    sort V = ?
    effects EC = ?
    effects EF = ?
    entity car(v: V)
    provides Holder[C = Car[EC = {EF}, EF = {EC}, V = V]]
    operation peek(c: Self) -> Int64 = 1
  end
  operation go() -> Int64 =
    let c: Car[V = Int64, EC = {}, EF = {}] = car(v: 1)
    Holder.peek(c)
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr7.row_diag.go"), Ok(1));
}

/// `Sp { get(s: Sp) -> s.T; put(s: Sp, k: s.T) }` at `Car provides Sp[T = List[T = Sp.U], U =
/// Int64]` — a binding naming ANOTHER spec parameter — with `Car`'s own `put` taking `k:
/// List[T = {elem}]`; `go` puts what it gets.
fn binding_naming_a_parameter_program(ns: &str, elem: &str, body: &str) -> String {
    with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String, List}}
  import anthill.prelude.List.{{cons, nil}}
  sort Sp
    sort T = ?
    sort U = ?
    operation get(s: Self) -> s.T
    operation put(s: Self, k: s.T) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = List[T = Sp.U], U = Int64]
    operation get(c: Self) -> List[T = Int64] = [5]
    operation put(c: Self, k: List[T = {elem}]) -> Int64 =
      match k
        case cons(h, t) -> {body}
        case nil() -> 0
  end
  operation go() -> Int64 =
    let c: Car[V = Int64] = car(v: 1)
    Sp.put(c, Sp.get(c))
end
"#
    ))
}

/// A SPEC PARAMETER THE PROVISION BINDS IS THAT BINDING WHEREVER ITS VARIABLE IS READ: `T =
/// List[T = Sp.U]` at `U = Int64` is a list of `Int64`, so `put(c: Car, k: List[T = String])`
/// behind `k: s.T` takes less. The binding names `U` by its canonical variable once it is read,
/// which σ — a substitution of references — never saw, so `U` stayed a WILDCARD as an unbound
/// parameter does, and `Sp.put(c, Sp.get(c))` handed the member's `String.length` an `Int64`
/// (MEASURED; the sixth review's tree refused it). The refusal names the type as read. FAILS
/// under ledger part 57.
#[test]
fn a_binding_naming_another_spec_parameter_reads_its_binding() {
    assert_refused_naming(
        &load_errors(&binding_naming_a_parameter_program(
            "wi0rp29mr7.bind_u",
            "String",
            "String.length(h)",
        )),
        &[
            "parameter 2 (`k: List[T = String]`) takes less than the spec's",
            "the spec's `List[T = Int64]`",
        ],
        "k narrower than the list `T` is bound to",
    );
}

/// … AND ITS CONTROL: `k: List[T = Int64]` is the spec's, and the round trip runs: 5 + 1.
/// Passes either way by design.
#[test]
fn a_binding_naming_another_spec_parameter_reads_its_binding_control() {
    let ns = "wi0rp29mr7.bind_u_ok";
    assert_eq!(
        run_int64(
            &binding_naming_a_parameter_program(ns, "Int64", "h + 1"),
            &format!("{ns}.go")
        ),
        Ok(6)
    );
}

/// `Sp.each(s: Sp, f: (x: Int64) -> Int64 @ {E})` — the callback's row the spec's own row
/// PARAMETER — at `Car provides Sp[T = Int64, E = {Error[Foo]}]`, with `Car`'s own `each` taking
/// a callback of row `{row}`; `go` passes one raising `Error[Foo]`.
fn callback_row_tail_program(ns: &str, row: &str) -> String {
    with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Bool, List, Error, Result}}
  import anthill.prelude.Result.{{ok, err}}
  sort Foo
    entity foo(n: Int64)
  end
  sort Bar
    entity bar(n: Int64)
  end
  sort Sp
    sort T = ?
    effects E = ?
    operation each(s: Self, f: (x: Int64) -> Int64 @ {{E}}) -> Int64
  end
  sort Car
    entity car(v: Int64)
    provides Sp[T = Int64, E = {{Error[Foo]}}]
    operation each(c: Car, f: (x: Int64) -> Int64 @ {{{row}}}) -> Int64 =
      match Error.reify[Rho = {{}}](lambda () -> f(1))
        case ok(v) -> v
        case err(b) -> b.n
  end
  operation boom(x: Int64) -> Int64 effects {{Error[Foo]}} = Error.raise(foo(n: 9))
  operation go() -> Int64 = Sp.each(car(v: 1), boom)
end
"#
    ))
}

/// … A CALLBACK ROW'S TAIL INCLUDED: `f: … @ {E}` at `E = {Error[Foo]}` is a callback raising
/// `Error[Foo]`, so a member whose callback may raise only `Error[Bar]` takes less. The tail is
/// the parameter's variable, and stayed a wildcard: the member loaded, reified `Error[Bar]`, and
/// the spec call's `Error[Foo]` left a pure `main` as "error: foo" (MEASURED on every build).
/// FAILS under ledger part 57.
#[test]
fn a_callback_rows_tail_reads_the_provisions_row() {
    assert_refused_naming(
        &load_errors(&callback_row_tail_program(
            "wi0rp29mr7.cb_tail",
            "Error[Bar]",
        )),
        &["parameter 2 (`f: Int64 -> Int64 @ {Error[T = Bar]}`) takes less than the spec's"],
        "a callback row narrower than the provision's `E`",
    );
}

/// … AND ITS CONTROL: the callback row written as the provision's runs — the raised `foo(n: 9)`
/// reified, to 9. Passes either way by design.
#[test]
fn a_callback_rows_tail_reads_the_provisions_row_control() {
    let ns = "wi0rp29mr7.cb_tail_ok";
    assert_eq!(
        run_int64(
            &callback_row_tail_program(ns, "Error[Foo]"),
            &format!("{ns}.go")
        ),
        Ok(9)
    );
}

// ── the seventh review's findings 10, 12 and 15: every return, the projections that do not
//    reduce, and the receiver's declared variance ─────────────────────────────────────────────

/// `Sp.pick(s: Sp) -> Option[T = T]` at `Car provides Sp[T = List[T = Int64]]`, the member
/// returning `ret` by `body`, and `go` reading the length of the list the spec call promises.
fn plain_return_program(ns: &str, ret: &str, body: &str) -> String {
    with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, String, List}}
  import anthill.prelude.Option.{{some, none}}
  sort Sp
    sort T = ?
    operation pick(s: Self) -> Option[T = T]
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = List[T = Int64]]
    operation pick(c: Self) -> {ret} = {body}
  end
  operation go() -> Int64 =
    let k: Car[V = Int64] = car(v: 5)
    match Sp.pick(k) case some(xs) -> List.length(xs) case none -> 0
end
"#
    ))
}

/// EVERY RETURN IS COMPARED, one holding no projection as much as one that does: `pick(s: Sp)
/// -> Option[T = T]` at `T = List[T = Int64]` promises a list, which `-> Option[T = V]` does not
/// return. The rule compared a return only where it held a projection, and left the rest to the
/// per-position comparison, which reads the provision's bindings as written and is undecided
/// wherever a return names a type parameter — so this member loaded, and the caller's
/// `List.length` ran on an `Int64` ("match_failed … scrutinee: 5", MEASURED on every build),
/// while its twin spelled `-> Option[T = s.T]` was refused. FAILS under ledger part 59.
#[test]
fn a_return_holding_no_projection_is_compared() {
    assert_refused_naming(
        &load_errors(&plain_return_program(
            "wi0rp29mr8.ret_plain",
            "Option[T = V]",
            "some(c.v)",
        )),
        &[
            "the member returns `Option[T = ?V]`",
            "not a subtype of the spec's `Option[T = List[T = Int64]]`",
        ],
        "a plain return against the spec's",
    );
}

/// … AND ITS CONTROL: the member returning the spec's type runs, the spec call reading a list
/// of three. Passes either way by design: it guards the comparison against refusing a return
/// that is the spec's.
#[test]
fn a_return_holding_no_projection_is_compared_control() {
    let ns = "wi0rp29mr8.ret_plain_ok";
    let src = plain_return_program(ns, "Option[T = List[T = Int64]]", "some([1, 2, 3])");
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(3));
}

/// `Mon.first(x: T, xs: List[T = T]) -> Pair[A = T, B = List[T = T]]` at `Car provides Mon[T =
/// Car]`, the member returning `ret` by `body`, and `go` reading the `String` the spec call
/// promises of a `Car[V = String]`.
fn carrier_return_program(ns: &str, ret: &str, body: &str) -> String {
    with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String, List, Pair}}
  import anthill.prelude.Pair.{{pair}}
  sort Mon
    sort T = ?
    operation first(x: T, xs: List[T = T]) -> Pair[A = T, B = List[T = T]]
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Mon[T = Self]
    operation first(x: Self, xs: List[T = Self]) -> {ret} = {body}
  end
  operation go() -> Int64 =
    let k: Car[V = String] = car(v: "hello")
    match Mon.first(k, [k]) case pair(a, _) -> String.length(a.v)
end
"#
    ))
}

/// A RETURN AT A BINDING NAMING THE CARRIER IS THIS INSTANCE: `-> Pair[A = T, …]` at `T = Car`
/// promises the receiver's `Car`, as the call types it, which `-> Pair[A = Car[V = Int64], …]`
/// does not return. Read through the provision's bindings as written, a bare `Car` was any
/// instance: the member loaded, and `Mon.first(k, [k])` over a `Car[V = String]` ran
/// `String.length` on an `Int64` (MEASURED on every build). FAILS under ledger part 59.
#[test]
fn a_return_at_a_carrier_binding_is_this_instance() {
    let src = carrier_return_program(
        "wi0rp29mr8.ret_inst",
        "Pair[A = Car[V = Int64], B = List[T = Self]]",
        "pair(fst: car(v: 5), snd: xs)",
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "the member returns `Pair[A = Car[V = Int64], B = List[T = Car[V = ?V]]]`",
            "not a subtype of the spec's",
        ],
        "a return fixing the instance the spec leaves the receiver's",
    );
}

/// … AND ITS CONTROL: `-> Pair[A = Car, B = List[T = Car]]` is the spec's, and the spec call
/// reads the five characters of the receiver's own `String`. Passes either way by design.
#[test]
fn a_return_at_a_carrier_binding_is_this_instance_control() {
    let ns = "wi0rp29mr8.ret_inst_ok";
    let src = carrier_return_program(
        ns,
        "Pair[A = Self, B = List[T = Self]]",
        "pair(fst: x, snd: xs)",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(5));
}

/// `Sp.get[W](s: Sp, w: W) -> Option[T = W]`, the member returning `ret` by `body`, and `go`
/// reading the `String` the spec call promises of a `String` argument.
fn op_param_return_program(ns: &str, ret: &str, body: &str) -> String {
    with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String, List, Option}}
  import anthill.prelude.Option.{{some, none}}
  sort Sp
    sort T = ?
    operation get[W](s: Self, w: W) -> Option[T = W]
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = Int64]
    operation get[W](s: Self, w: W) -> {ret} = {body}
  end
  operation go() -> Int64 =
    let c: Car[V = Int64] = car(v: 1)
    match Sp.get(c, "xyz") case some(s) -> String.length(s) case none -> 0
end
"#
    ))
}

/// … A RETURN NAMING THE OPERATION'S OWN TYPE PARAMETER TOO: `get[W](…) -> Option[T = W]`
/// promises an option of whatever the call passes, which `-> Option[T = Int64]` does not
/// return. The per-position comparison is undecided on a type parameter, so it loaded, and
/// `Sp.get(c, "xyz")` ran `String.length` on an `Int64` (MEASURED on every build). FAILS under
/// ledger part 59.
#[test]
fn a_return_naming_an_operation_type_parameter_is_compared() {
    assert_refused_naming(
        &load_errors(&op_param_return_program(
            "wi0rp29mr8.ret_w",
            "Option[T = Int64]",
            "some(5)",
        )),
        &[
            "the member returns `Option[T = Int64]`",
            "not a subtype of the spec's `Option[T = ?W]`",
        ],
        "a return fixing the operation's type parameter",
    );
}

/// … AND ITS CONTROL: `-> Option[T = W]` is the spec's, and the spec call reads the three
/// characters it passed. Passes either way by design.
#[test]
fn a_return_naming_an_operation_type_parameter_is_compared_control() {
    let ns = "wi0rp29mr8.ret_w_ok";
    let src = op_param_return_program(ns, "Option[T = W]", "some(w)");
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(3));
}

/// `Sp.mk(s: {recv}, n: Int64, j: Int64) -> Buf[T = Int64, N = n]` — a return naming a
/// parameter by VALUE — at `Car provides Sp[T = {t}]`, the member's parameters named `m` and
/// `i` and its return `ret`, with `go`.
fn dependent_return_program(ns: &str, recv: &str, t: &str, ret: &str, go: &str) -> String {
    with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Animal
    entity cat(n: Int64)
    entity dog(n: Int64)
  end
  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end
  sort Sp
    sort T = ?
    operation mk(s: {recv}, n: Int64, j: Int64) -> Buf[T = Int64, N = n]
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = {t}]
    operation mk(c: Self, m: Int64, i: Int64) -> {ret} = buf(v: m)
  end
  operation go() -> Int64 = {go}
end
"#
    ))
}

/// A RETURN NAMING A PARAMETER BY VALUE IS COMPARED BY THE SPEC'S NAMES: `-> Buf[T = Int64, N =
/// m]` behind `-> Buf[T = Int64, N = n]`, `m` the member's name for the spec's `n`, is the
/// spec's return. The rule's parameters were compared so and its returns only beside a
/// projection; the per-position comparison compared the member's own symbol, and refused a
/// member restating its spec, printing one type twice (MEASURED on every build). The spec call
/// runs the member, to 3. FAILS under ledger part 59.
#[test]
fn a_return_naming_a_parameter_by_value_is_compared_by_the_specs_names() {
    let ns = "wi0rp29mr8.ret_dep";
    let go = "match Sp.mk(car(v: 1), 3, 4) case buf(v) -> v";
    let src = dependent_return_program(ns, "Self", "V", "Buf[T = Int64, N = m]", go);
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(3));
}

/// … AND ITS CONTROL: a return naming the OTHER parameter (`N = i`, the spec's `j`) is not the
/// spec's, and is refused — it guards the re-key against renaming whatever it finds. Passes
/// under every part of this pass, each comparing the two values; FAILS under ledger part 45
/// alone, where no return is compared at all.
#[test]
fn a_return_naming_a_parameter_by_value_is_compared_by_the_specs_names_control() {
    let src = dependent_return_program(
        "wi0rp29mr8.ret_dep_c",
        "Self",
        "V",
        "Buf[T = Int64, N = i]",
        "0",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["the member returns `Buf[T = Int64, N ="],
        "a return naming another parameter than the spec's",
    );
}

/// A MEMBER RETURNING A PROVIDER OF THE SPEC'S BARE SORT FITS: `op(x: T) -> Base` promises some
/// `Base`, and `-> Car`, `Car` providing `Base[B = Car]`, returns one. The spec's unwritten slot
/// is a fresh variable to unify with (`Base[B = ?B]`), which a provider is no application of —
/// and the relation, which binds nothing, has no verdict on `Car <: Base[B = ?B]` — so the
/// relation is asked over the spec's return with its slots left unwritten as well. Without that
/// the every-return comparison refused it, a covariant return the per-position comparison had
/// always admitted (MEASURED: `wi347`'s `a_covariant_return_type_still_discharges_the_result_
/// clause` beside this row). The spec call runs the member, its result a `Base`. FAILS under
/// ledger part 65.
///
/// `Base` RECEIVES ON ITSELF (`rank(b: Self)`), which is what makes a `Car` one: a sort that
/// provides a spec over a parameter is that parameter and not the spec, and a member
/// returning it behind `-> Base` returns no `Base` (WI-20261005-KSSA4).
#[test]
fn a_member_returning_a_provider_of_the_specs_bare_sort_fits() {
    let ns = "wi0rp29mr8.ret_provider";
    let src = with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Base
    sort B = ?
    operation rank(b: Self) -> Int64
  end
  sort Sp
    sort T = ?
    operation op(x: T) -> Base
  end
  sort Car
    entity car(id: Int64)
    provides Base[B = Car]
    operation rank(b: Car) -> Int64 = 0
    provides Sp[T = Self]
    operation op(x: Car) -> Car = x
  end
  operation go() -> Int64 =
    let b: Base = Sp.op(car(id: 7))
    7
end
"#
    ));
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(7));
}

/// `Sp.total(s: Sp[T = Animal], k: Int64) -> Int64` at `Car provides Sp[T = cat]`, `T` declared
/// as `variance` says (a `fact` line, or none), the member's receiver typed `recv`, and `go`.
fn receiver_variance_reach_program(
    ns: &str,
    variance: &str,
    recv: &str,
    body: &str,
    go: &str,
) -> String {
    with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  import anthill.reflect.typing.{{Covariant}}
  sort Animal
    entity cat(n: Int64)
    entity dog(n: Int64)
  end
  sort Sp
    sort T = ?
    {variance}
    operation total(s: Sp[T = Animal], k: Int64) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = cat]
    operation total(s: {recv}, k: Int64) -> Int64 = {body}
  end
  operation go() -> Int64 =
    {go}
end
"#
    ))
}

/// A PROVISION THE RECEIVER'S WRITTEN ARGUMENT EXCLUDES IS NOT REACHED, by the parameter's
/// DECLARED variance: `s: Sp[T = Animal]` with `T` invariant receives no provider at `T = cat`
/// — `Sp.total(c, 41)` is refused at the call — so its member is no spec call's to reach and is
/// not compared; its qualified call runs it, to 42. The meeting asked unification, which between
/// two types holding no variable falls back to the subtype relation: `cat` "unified" with
/// `Animal` whatever the variance, the provision read as reached, and the member was refused
/// for a receiver "the spec receives" that no call can send (MEASURED). FAILS under ledger part
/// 60.
#[test]
fn a_provision_an_invariant_parameter_excludes_is_not_reached() {
    let ns = "wi0rp29mr8.var_inv";
    let qualified = "let c: Car[V = Int64] = car(v: 1)\n    Car.total(c, 41)";
    let src = receiver_variance_reach_program(ns, "", "Car[V = Int64]", "s.v + k", qualified);
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(42));
    let through_spec = "let c: Car[V = Int64] = car(v: 1)\n    Sp.total(c, 41)";
    let src = receiver_variance_reach_program(
        "wi0rp29mr8.var_inv_call",
        "",
        "Car[V = Int64]",
        "s.v + k",
        through_spec,
    );
    assert_refused_naming(
        &load_errors(&src),
        &["total.s (op-arg): expected Sp[T = Animal], got Car[V = Int64]"],
        "the spec call over a provision its receiver excludes",
    );
}

/// … AND ITS CONTROL: declared `Covariant`, `T = cat` is received by `Sp[T = Animal]`, so the
/// member IS compared — one fixing its receiver's `V` is refused — and one typed `Car` runs the
/// spec call, to 42. Passes either way by design: it guards the variance reading against
/// leaving a reached member uncompared.
#[test]
fn a_provision_an_invariant_parameter_excludes_is_not_reached_control() {
    let cov = "fact Covariant(sort: Sp, param: T)";
    let src = receiver_variance_reach_program(
        "wi0rp29mr8.var_cov",
        cov,
        "Car[V = Int64]",
        "s.v + k",
        "0",
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "parameter 1 (`s: Car[V = Int64]`) takes less than the spec's",
            "`s` is the receiver",
        ],
        "a covariant parameter's provision is reached",
    );
    let ns = "wi0rp29mr8.var_cov_ok";
    let go = "let c: Car[V = String] = car(v: \"s\")\n    Sp.total(c, 41)";
    let src = receiver_variance_reach_program(ns, cov, "Self", "k + 1", go);
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(42));
}

/// A MEMBER NO SPEC CALL REACHES KEEPS THE PER-POSITION RETURN COMPARISON, by the spec's names:
/// `mk(s: Sp[T = Animal], …)` at `T = cat` is unreached, so the rule compares nothing of it and
/// the comparison at the provision's bindings is its judge — which read the member's return by
/// the member's own parameter names and refused the verbatim `-> Buf[T = Int64, N = m]`,
/// printing `N = m` against `N = n` (MEASURED). The qualified call runs it, to 3; a return of
/// another type is still refused there. FAILS under ledger parts 59, 60 and 61.
#[test]
fn a_member_no_spec_call_reaches_keeps_the_per_position_return() {
    let ns = "wi0rp29mr8.unreached_ret";
    let go = "match Car.mk(car(v: 1), 3, 4) case buf(v) -> v";
    let src = dependent_return_program(ns, "Sp[T = Animal]", "cat", "Buf[T = Int64, N = m]", go);
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(3));
    let src = dependent_return_program(
        "wi0rp29mr8.unreached_ret_c",
        "Sp[T = Animal]",
        "cat",
        "Buf[T = String, N = m]",
        "0",
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "the member returns `Buf[T = String, N = m]`",
            "not a subtype of the spec's `Buf[T = Int64, N = n]`",
        ],
        "an unreached member returning another type",
    );
}

/// `Sp.count(s: Sp, h: Bag) -> Int64` and `Sp.first(s: Sp, h: Bag) -> h.items.T`, `Bag`'s
/// `items` a bare `List` (so the projection reduces nowhere), the member `first` returning
/// `ret` over its own parameter `g`, and a caller forwarding the spec call's result as its own
/// `b.items.T`.
fn field_path_program(ns: &str, ret: &str) -> String {
    with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Bag
    entity bag(items: List, others: List)
  end
  sort Sp
    sort T = ?
    operation count(s: Self, h: Bag) -> Int64
    operation first(s: Self, h: Bag) -> h.items.T
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation count(c: Self, g: Bag) -> Int64 = List.length(g.items)
    operation first(c: Self, g: Bag) -> {ret} = first(c, g)
  end
  operation relay(c: Car[V = Int64], b: Bag) -> b.items.T = Sp.first(c, b)
  operation go() -> Int64 =
    let c: Car[V = Int64] = car(v: 1)
    Sp.count(c, bag(items: [4, 5, 6], others: [])) + 4
end
"#
    ))
}

/// A PROJECTION OFF A FIELD PATH THAT DOES NOT REDUCE IS THE SAME PROJECTION ON BOTH SIDES, by
/// the spec's names: `first(c: Car, g: Bag) -> g.items.T` restates `first(s: Sp, h: Bag) ->
/// h.items.T`. A neutral's receiver was re-keyed only where it was a single reference, so the
/// member's kept its own `g`, the two compared as two projections, and the verbatim member was
/// refused "returns `g.items.T`, which is not a subtype of the spec's `h.items.T`" — while the
/// call left the callee's `h` in a result its caller can only name `b.items.T` (MEASURED: both
/// refused). LOAD VERDICT for `first` and `relay` — nothing builds a value of an abstract
/// `h.items.T` to run them on — and the provision they sit in dispatches `Sp.count`, to 3 + 4.
/// FAILS under ledger part 62.
#[test]
fn a_field_path_projection_is_compared_by_the_specs_names() {
    let ns = "wi0rp29mr8.fpath";
    assert_eq!(
        run_int64(&field_path_program(ns, "g.items.T"), &format!("{ns}.go")),
        Ok(7)
    );
}

/// … AND ITS CONTROL: the projection off ANOTHER field is not the spec's, and is refused — it
/// guards the re-key against equating every neutral. Passes under every part of this pass;
/// FAILS under ledger part 45 alone, where no return is compared at all.
#[test]
fn a_field_path_projection_is_compared_by_the_specs_names_control() {
    assert_refused_naming(
        &load_errors(&field_path_program("wi0rp29mr8.fpath_c", "g.others.T")),
        &["not a subtype of the spec's `h.items.T`"],
        "another field's projection",
    );
}

/// … OVER A FIELD OF ABSTRACT TYPE TOO: `st.provider.K`, `provider` typed by `State`'s own
/// parameter `P` under `State requires DataProvider[P]`. The rule's argument for `st` makes `P`
/// a rigid — any type — and the call's reading looks for the `requires` bound of a PARAMETER,
/// finding none for a rigid: the verbatim member was refused "the spec's `st.provider.K` does
/// not read at this provision" (MEASURED). The provision dispatches `Sp.count`, to 7. FAILS
/// under ledger part 63.
#[test]
fn a_field_path_projection_over_an_abstract_field_is_the_same_projection() {
    let ns = "wi0rp29mr8.fpath_req";
    let src = with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort DataProvider
    sort K = ?
  end
  sort State
    sort P = ?
    requires DataProvider[P]
    entity state(provider: P)
  end
  sort Sp
    sort T = ?
    operation count(s: Self) -> Int64
    operation idk(s: Self, st: State, k: st.provider.K) -> st.provider.K
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation count(s: Self) -> Int64 = 7
    operation idk(c: Self, t: State, k: t.provider.K) -> t.provider.K = k
  end
  operation go() -> Int64 =
    let c: Car[V = Int64] = car(v: 1)
    Sp.count(c)
end
"#
    ));
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(7));
}

/// … AND OFF A CARRIER-PARAM RECEIVER: `put(c: C, k: c.items.T)` at `Car provides Holder[C =
/// Car]`, the member naming its receiver `d`. Refused "the spec's `c.items.T` admits arguments
/// the member's `d.items.T` does not" (MEASURED). The provision dispatches `Holder.size`, to 2
/// + 5. FAILS under ledger part 62.
#[test]
fn a_carrier_param_receivers_field_path_projection_is_compared() {
    let ns = "wi0rp29mr8.fpath_cp";
    let src = with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Holder
    sort C = ?
    operation size(c: C) -> Int64
    operation put(c: C, k: c.items.T) -> Int64
  end
  sort Car
    sort V = ?
    entity car(items: List, v: V)
    provides Holder[C = Self]
    operation size(c: Self) -> Int64 = List.length(c.items) + 5
    operation put(d: Self, k: d.items.T) -> Int64 = 40
  end
  operation go() -> Int64 = Holder.size(car(items: [1, 2], v: "s"))
end
"#
    ));
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(7));
}

/// `Sp.put(s: Sp, k: s.K, j: s.K)` at `Car provides Sp[T = V]` — `K` left UNBOUND, and `Car`
/// declaring none — the member taking `k: Int64` and `j` as `j_ty`, with `go`.
fn unbound_member_program(ns: &str, j_ty: &str, body: &str, go: &str) -> String {
    with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Sp
    sort T = ?
    sort K = ?
    operation put(s: Self, k: s.K, j: s.K) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation put(c: Self, k: Int64, j: {j_ty}) -> Int64 = {body}
  end
  operation go() -> Int64 =
    let c: Car[V = String] = car(v: "s")
    {go}
end
"#
    ))
}

/// A PROJECTION OVER A SPEC MEMBER THE PROVISION LEAVES UNBOUND IS A WILDCARD, as that
/// parameter is in every other position: `k: s.K` at `Car provides Sp[T = V]` is any type, so
/// `k: Int64` fits. Left to the call's reading it was "type 'Car' has no member 'K'", and the
/// member — which no spec call reaches, the call refusing on the same words — was refused as
/// unreadable (MEASURED). Its qualified call runs it, to 40 + 2. FAILS under ledger part 64.
#[test]
fn a_projection_over_a_member_the_provision_leaves_unbound_is_a_wildcard() {
    let ns = "wi0rp29mr8.unbound";
    let src = unbound_member_program(ns, "Int64", "k + j", "Car.put(c, 40, 2)");
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(42));
}

/// … AND ONE WILDCARD IS ONE TYPE: `k: s.K, j: s.K` read `K` once, so a member taking an
/// `Int64` and a `String` there is refused at the second, the spec's side printed as the first
/// made it. FAILS under ledger part 64 (refused at parameter 2 instead, as unreadable) and
/// part 66 (the spec's side printed `?_`).
#[test]
fn a_projection_over_a_member_the_provision_leaves_unbound_is_one_type() {
    let src = unbound_member_program("wi0rp29mr8.unbound_two", "String", "k", "0");
    assert_refused_naming(
        &load_errors(&src),
        &[
            "parameter 3 (`j: String`) takes less than the spec's",
            "the spec's `Int64` admits arguments the member's `String` does not",
        ],
        "two readings of one unbound member",
    );
}

/// … AND ITS CONTROL: the spec call over such a provision is refused at the call, which reads
/// no `K` off a `Car` — so the wildcard admits no member a call could then mis-feed. Passes
/// either way by design.
#[test]
fn a_projection_over_a_member_the_provision_leaves_unbound_is_a_wildcard_control() {
    let src = unbound_member_program(
        "wi0rp29mr8.unbound_call",
        "Int64",
        "k + j",
        "Sp.put(c, 40, 2)",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["has no member 'K'"],
        "the spec call reads no `K`",
    );
}

// ── the eighth review's fixes (the ninth pass) ──────────────────────────────────────────────

/// THE RETURN'S VERDICT IS THE RELATION'S; unification only binds. `reader(k: Car) -> (x: cat)
/// -> Int64` behind `-> (x: Animal) -> Int64` returns a function that takes FEWER arguments
/// than the spec promises — a parameter is contravariant. Unification answered `true` (between
/// two types holding no variable it falls back to the subtype relation in argument order, at
/// every depth), the rule took that for the verdict, and `Sp.reader(car)(dog(n: 3))` loaded and
/// ran a function typed over `cat` on a `dog` (MEASURED: it answered 3). FAILS under ledger
/// part 69.
#[test]
fn a_returned_function_narrower_in_its_parameter_is_refused() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.ret_arrow_narrow
  import anthill.prelude.{Int64, Bool, String, List, Option, Error}
  import anthill.prelude.Option.{some, none}

  sort Animal
    entity cat(n: Int64)
    entity dog(n: Int64)
  end

  sort Sp
    sort T = ?
    operation reader(s: Self) -> (x: Animal) -> Int64
  end

  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation reader(k: Self) -> (x: cat) -> Int64 = lambda (x: cat) -> x.n
  end
  operation go() -> Int64 =
    let f = Sp.reader(car(v: 1))
    f(dog(n: 3))
end
"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "the member returns `cat -> Int64`, which is not a subtype of the spec's `Animal \
             -> Int64`",
        ],
        "a returned function narrower in its parameter",
    );
}

/// … AND AT AN INVARIANT SLOT: `Sink[A = cat]` is no `Sink[A = Animal]` — `A` stands in a
/// callback's parameter — yet the two unified. `feed(Sp.mk(car), dog(…))` ended in "entity has
/// no field 'lives'" (MEASURED). FAILS under ledger part 69.
#[test]
fn a_return_narrower_at_an_invariant_slot_is_refused() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.ret_invariant
  import anthill.prelude.{Int64, String, List}
  sort Animal
    entity cat(lives: Int64)
    entity dog(bark: Int64)
  end
  sort Sink
    sort A = ?
    entity sink(f: (x: A) -> Int64)
  end
  sort Sp
    sort T = ?
    operation mk(s: Self) -> Sink[A = Animal]
  end
  sort Car
    entity car(n: Int64)
    provides Sp[T = Int64]
    operation mk(k: Car) -> Sink[A = cat] = sink(f: lambda (x: cat) -> x.lives)
  end
  operation feed(s: Sink[A = Animal], a: Animal) -> Int64 =
    match s
      case sink(g) -> g(a)
  operation go() -> Int64 = feed(Sp.mk(car(n: 1)), dog(bark: 3))
end
"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "the member returns `Sink[A = cat]`, which is not a subtype of the spec's `Sink[A \
             = Animal]`",
        ],
        "a return narrower at an invariant slot",
    );
}

/// … AND THEIR CONTROL: the function the spec writes, returned as written, fits and runs
/// through the spec call, to 39 + 3. Passes either way by design (equal types).
#[test]
fn a_returned_function_as_the_spec_writes_it_fits_control() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.ret_arrow_same
  import anthill.prelude.{Int64, Bool, String, List, Option, Error}
  sort Animal
    entity cat(n: Int64)
    entity dog(n: Int64)
  end
  sort Sp
    sort T = ?
    operation reader(s: Self) -> (x: Animal) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation reader(k: Self) -> (x: Animal) -> Int64 = lambda (x: Animal) -> 39
  end
  operation go() -> Int64 =
    let f = Sp.reader(car(v: 1))
    f(dog(n: 3)) + 3
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr9.ret_arrow_same.go"), Ok(42));
}

/// THE RELATION IS ASKED WITH THE MEMBER'S VARIABLES BOUND: `mk[W](c: Car) -> (a: List[T = W],
/// b: Int64)` behind `-> (a: List[T = Int64])` is wider by width, and its `W` is `Int64` —
/// which unification, stopping at the two widths, never said. Asked with `W` open the relation
/// refused a sound generic member (MEASURED). Runs to 0 + 40. FAILS under ledger part 70.
#[test]
fn a_generic_members_wider_return_is_bound_along_the_relation() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.ret_generic_wider
  import anthill.prelude.{Int64, Bool, String, List, Option}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.List.{cons, nil}
  sort Animal
    entity cat(lives: Int64)
    entity dog(name: String)
  end
  sort Sp
    sort T = ?
    operation mk(s: Self) -> (a: List[T = Int64])
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation mk[W](c: Self) -> (a: List[T = W], b: Int64) = (a: [], b: 1)
  end

  operation go() -> Int64 =
    let k: Car[V = Int64] = car(v: 5)
    let t = Sp.mk(k)
    List.length(t.a) + 40
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr9.ret_generic_wider.go"), Ok(40));
}

/// AN UNWRITTEN SLOT IN A RETURN BELONGS TO WHOEVER PICKS IT. The member produces the value, so
/// the slot ITS return leaves unwritten is a type it chose and the caller does not know:
/// `items(c: Car) -> List` behind `-> List[T = T]` at `T = V` promises a list of the receiver's
/// `V` and returns a list of anything. Read as the member's to instantiate — as a parameter's
/// slot is — it unified with `V`, and `Sp.items(k)` over a `Car[V = Int64]` handed `["s"]` to
/// `h + 1` (MEASURED, run time). FAILS under ledger part 71.
#[test]
fn a_members_bare_return_is_a_type_the_caller_does_not_know() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.ret_bare
  import anthill.prelude.{Int64, Bool, String, List, Option, Error}
  import anthill.prelude.Option.{some, none}

  sort Animal
    entity cat(n: Int64)
    entity dog(n: Int64)
  end

  sort Sp
    sort T = ?
    operation items(s: Self) -> List[T = T]
  end

  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation items(c: Self) -> List = ["s"]
  end
  operation go() -> Int64 =
    let k: Car[V = Int64] = car(v: 1)
    List.length(Sp.items(k))
end
"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "the member returns `List[T = ?T]`, which is not a subtype of the spec's `List[T \
             = ?V]`",
        ],
        "a member's bare return behind a written one",
    );
}

/// … AND ITS CONTROL, the other way round: behind a spec return left BARE (`-> List`, the
/// member's to pick) a member returning `List[T = Int64]` fits. Runs to 2 + 40. Passes either
/// way by design.
#[test]
fn a_members_bare_return_is_a_type_the_caller_does_not_know_control() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.ret_bare_ctl
  import anthill.prelude.{Int64, Bool, String, List, Option, Error}
  import anthill.prelude.Option.{some, none}

  sort Animal
    entity cat(n: Int64)
    entity dog(n: Int64)
  end

  sort Sp
    sort T = ?
    operation items(s: Self) -> List
  end

  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation items(c: Self) -> List[T = Int64] = [40, 2]
  end
  operation go() -> Int64 =
    let k: Car[V = Int64] = car(v: 1)
    List.length(Sp.items(k)) + 40
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr9.ret_bare_ctl.go"), Ok(42));
}

/// … AND UNDER A RETURNED FUNCTION'S PARAMETER THE TWO TURN OVER: the function the spec returns
/// takes a list of ANY element (`-> (xs: List) -> Int64`), so one taking `List[T = Int64]`
/// takes less. There the spec's slot was read as the member's to pick, and `Sp.eater(k)(["s"])`
/// loaded (MEASURED: the member's body then read a `String` as an `Int64`). FAILS under ledger
/// part 71.
#[test]
fn a_returned_functions_parameter_turns_the_slots_over() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.ret_arrow_param
  import anthill.prelude.{Int64, Bool, String, List, Option, Error}
  import anthill.prelude.Option.{some, none}

  sort Animal
    entity cat(n: Int64)
    entity dog(n: Int64)
  end

  sort Sp
    sort T = ?
    operation eater(s: Self) -> (xs: List) -> Int64
  end

  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation eater(c: Self) -> (xs: List[T = Int64]) -> Int64 = lambda (xs: List[T = Int64]) -> List.length(xs)
  end
  operation go() -> Int64 =
    let k: Car[V = Int64] = car(v: 5)
    let f = Sp.eater(k)
    f(["s"])
end
"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "the member returns `List[T = Int64] -> Int64`, which is not a subtype of the \
             spec's `List[T = ?T] -> Int64`",
        ],
        "a returned function narrower in its parameter's unwritten slot",
    );
}

/// … AND ITS CONTROL: the member returning the function as the spec writes it — its parameter's
/// slot its own to instantiate — fits, and runs over a list of strings, to 2 + 40. Passes
/// either way by design.
#[test]
fn a_returned_functions_parameter_turns_the_slots_over_control() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.ret_arrow_param_ctl
  import anthill.prelude.{Int64, Bool, String, List, Option, Error}
  import anthill.prelude.Option.{some, none}

  sort Animal
    entity cat(n: Int64)
    entity dog(n: Int64)
  end

  sort Sp
    sort T = ?
    operation eater(s: Self) -> (xs: List) -> Int64
  end

  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation eater(c: Self) -> (xs: List) -> Int64 = lambda (xs: List) -> List.length(xs) + 40
  end
  operation go() -> Int64 =
    let k: Car[V = Int64] = car(v: 5)
    let f = Sp.eater(k)
    f(["a", "b"])
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr9.ret_arrow_param_ctl.go"), Ok(42));
}

/// A SLOT THE PROVISION LEAVES UNWRITTEN IS ONE TYPE PER CALL where a parameter reads it: at
/// `State = Box[T = Int64]` a call of `rt(s, x: State) -> State` passing a `Box[U = Int64]`
/// reads its result as one (the call binds a binding once). `rt(s, x: Box[T = Int64]) -> Box[T
/// = Int64]` writes two slots of its own, and returns a box at another `U`: `Store.rt(c, a).u +
/// 1` died "expected Int64, got String" (MEASURED on every build). The refusal's two sides
/// print alike, and it says so. FAILS under ledger part 71 (the member's slot unified with the
/// caller's) and its note under part 82.
#[test]
fn a_provision_slot_a_parameter_reads_ties_the_return() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.slot_param_tied
  import anthill.prelude.{Int64, Bool, List, String}
  sort Box
    sort T = ?
    sort U = ?
    entity box(t: T, u: U)
  end
  sort Store
    sort State = ?
    operation peek(s: Self, x: State) -> Int64
    operation rt(s: Self, x: State) -> State
    operation fresh(s: Self, n: Int64) -> State
  end
  sort Carrier
    entity carrier(k: Int64)
    provides Store[State = Box[T = Int64]]
    operation peek(s: Carrier, x: Box[T = Int64]) -> Int64 = x.t
    operation rt(s: Carrier, x: Box[T = Int64]) -> Box[T = Int64] = box(t: x.t, u: "str")
    operation fresh(s: Carrier, n: Int64) -> Box[T = Int64] = box(t: n, u: "str")
  end
  operation go() -> Int64 =
    let a: Box[T = Int64, U = Int64] = box(t: 1, u: 41)
    let b = Store.rt(carrier(k: 1), a)
    b.u + 1
end
"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "its own member 'rt' does not fit",
            "the member returns `Box[T = Int64, U = ?U]`, which is not a subtype of the \
             spec's `Box[T = Int64, U = ?U]`",
            "The two types compared print alike",
        ],
        "a return slot tied to a parameter's",
    );
}

/// … AND WHERE ONLY THE RETURN READS IT, nothing the caller passes fixes it: `fresh(s, n:
/// Int64) -> State` at `State = Box[T = Int64]` is met by a member returning `Box[T = Int64]`,
/// its own slot as open as the provision's. Made any type there as well, the two unknowns of
/// one name were refused — a fixture of WI-20260924-F3FYJ among them (MEASURED). Runs to 42.
/// FAILS under ledger part 72.
#[test]
fn a_provision_slot_only_the_return_reads_is_the_members_to_pick() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.slot_return_only
  import anthill.prelude.{Int64, Bool, List, String}
  sort Box
    sort T = ?
    sort U = ?
    entity box(t: T, u: U)
  end
  sort Store
    sort State = ?
    operation peek(s: Self, x: State) -> Int64
    operation fresh(s: Self, n: Int64) -> State
  end
  sort Carrier
    entity carrier(k: Int64)
    provides Store[State = Box[T = Int64]]
    operation peek(s: Carrier, x: Box[T = Int64]) -> Int64 = x.t
    operation fresh(s: Carrier, n: Int64) -> Box[T = Int64] = box(t: n, u: "str")
  end
  operation go() -> Int64 =
    let c = carrier(k: 1)
    Store.peek(c, Store.fresh(c, 42))
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr9.slot_return_only.go"), Ok(42));
}

/// … BUT THE MEMBER MAY NOT FIX IT: the caller of the spec reads a slot nothing fixes as it
/// likes (`let x: Strm[T = String, …] = Sp.get(k)` at `T = Strm[E = {Error}]`), so a member
/// returning `Strm[T = Int64, …]` there ends that caller in "expected String" at run time
/// (MEASURED: it loaded where the provision's label was written braced, and was refused where
/// it was not). FAILS under ledger part 73, and under part 78 (a binding holding a braced label
/// dropped out of the template, its slot fresh at the return).
#[test]
fn a_member_fixing_a_slot_the_provision_leaves_open_is_refused() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.tpl_braced_ret
  import anthill.prelude.{Int64, Bool, Option, String, List, Error}
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(v: T)
  end
  sort Sp
    sort T = ?
    operation get(s: Self) -> T
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = Strm[E = {Error}]]
    operation get(c: Self) -> Strm[T = Int64, E = {Error}] = strm(v: 5)
  end
  operation go() -> Int64 =
    let k: Car[V = Int64] = car(v: 1)
    let x: Strm[T = String, E = {Error}] = Sp.get(k)
    match x case strm(v) -> String.length(v)
end
"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "the member returns `Strm[T = Int64, E = {Error[T = ?T]}]`, which is not a \
             subtype of the spec's `Strm[T = ?T, E = {Error[T = ?T]}]`",
        ],
        "a member fixing a slot the provision leaves unwritten",
    );
}

/// A PROVISION IS UNREACHED ONLY WHERE THE CALL CHECKS ITS RECEIVER: `total(s: Sp[T = Animal],
/// k)` at `provides Sp[T = cat, K = Int64]` writes one of the spec's two parameters, so the
/// call does not hold the receiver to that type — it admits a `Car` — and the member runs. The
/// rule had stopped comparing such a member ("no call reaches it"), so `total(s: Car[V =
/// Int64], k)` loaded and `Sp.total(c, 41)` over a `Car[V = String]` added 41 to a string
/// (MEASURED). FAILS under ledger part 74.
#[test]
fn a_receiver_argument_the_call_does_not_check_leaves_the_member_reached() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.recv_open
  import anthill.prelude.{Int64, String, List}
  import anthill.reflect.typing.{Covariant}
  sort Animal
    entity cat(n: Int64)
    entity dog(n: Int64)
  end
  sort Sp
    sort T = ?
    sort K = ?
    operation total(s: Sp[T = Animal, K = K], k: Int64) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = cat, K = Int64]
    operation total(s: Car[V = Int64], k: Int64) -> Int64 = s.v + k
  end
  operation go() -> Int64 =
    let c: Car[V = String] = car(v: "s")
    Sp.total(c, 41)
end
"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "parameter 1 (`s: Car[V = Int64]`) takes less than the spec's",
            "`s` is the receiver",
        ],
        "a receiver narrower than the spec's, behind an argument the call does not check",
    );
}

/// … AND ITS CONTROL: with `T` the spec's ONLY parameter the receiver's type is closed as
/// written, the call checks the receiver against it and refuses the provider — so the member is
/// reached by no spec call, and the rule leaves it alone: the refusal is the call's. Passes
/// either way by design.
#[test]
fn a_receiver_argument_the_call_does_not_check_leaves_the_member_reached_control() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.recv_closed
  import anthill.prelude.{Int64, String, List}
  import anthill.reflect.typing.{Covariant}
  sort Animal
    entity cat(n: Int64)
    entity dog(n: Int64)
  end
  sort Sp
    sort T = ?

    operation total(s: Sp[T = Animal], k: Int64) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = cat]
    operation total(s: Car[V = Int64], k: Int64) -> Int64 = s.v + k
  end
  operation go() -> Int64 =
    let c: Car[V = String] = car(v: "s")
    Sp.total(c, 41)
end
"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &["type mismatch in total.s (op-arg): expected Sp[T = Animal], got Car[V = String]"],
        "the call's own refusal of a provider its closed receiver type excludes",
    );
}

/// A UNIFIER BINDING A VARIABLE INSIDE ITSELF IS NO UNIFIER, and nothing walks it: `put[W](c:
/// Car, a: List[T = W], b: W)` behind `put(s: Sp, a: s.K, b: List[T = s.K])` binds `K ↦
/// List[W]`, then `W ↦ List[K]` — the occurs check reads a binding as written. The deep resolve
/// that followed did not return: the loader's stack overflowed on this member instead of
/// refusing it (MEASURED). Under ledger part 75 the PROCESS dies of that overflow, which fails
/// every row of the binary; under the earlier part 64 (an unbound member left to the call's
/// reading) it is refused another way, as unreadable.
#[test]
fn a_unifier_binding_a_variable_inside_itself_is_refused_not_walked() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.cycle
  import anthill.prelude.{Int64, String, List, Option}
  import anthill.prelude.Option.{some, none}
  sort Pair
    sort A = ?
    sort B = ?
    entity pair(a: A, b: B)
  end
  sort Sp
    sort T = ?
    sort K = ?
    sort J = ?
    operation put(s: Self, a: s.K, b: List[T = s.K]) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation put[W](c: Self, a: List[T = W], b: W) -> Int64 = 1
  end
end
"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &["parameter 3 (`b: ?W`) takes less than the spec's"],
        "a member whose variables solve only through themselves",
    );
}

/// … AND ITS CONTROL: a member reading a projection the provision binds, with no cycle in it,
/// loads and its sibling runs through the spec call, to 1 + 41 — where the same overflow took
/// this program too (MEASURED on the tree the eighth review saw: a clean member died beside the
/// cyclic one's mechanism). Passes under part 75 as well, run in a process of its own: that
/// part's overflow is the cyclic twin's.
#[test]
fn a_unifier_binding_a_variable_inside_itself_is_refused_not_walked_control() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.cycle_ctl
  import anthill.prelude.{Int64, String, List, Option}
  import anthill.prelude.Option.{some, none}
  sort Sp
    sort T = ?
    sort K = ?
    sort J = ?
    sort L = ?
    operation size(s: Self) -> Int64
    operation op(x: Car[V = List[T = K]], y: List[T = K]) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V, J = V]
    operation size(c: Self) -> Int64 = 1
    operation op(x: Car[V = List[T = V]], y: x.J) -> Int64 = 1
  end
  operation go() -> Int64 = Sp.size(car(v: 5)) + 41
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr9.cycle_ctl.go"), Ok(42));
}

/// THE RULE READS A PROJECTED MEMBER FROM THE SPEC ITS RECEIVER IS DECLARED BY, as the call
/// does. `put(c: Car, k: c.E)` declares `c` at the CARRIER, so `c.E` is what `Car`'s own
/// provisions lend — `Other`'s `String` — in the member's signature and its body. The rule
/// answered from the provision under check (`Sp`, which leaves `E` unbound: a wildcard),
/// admitted the member behind `put(s: Sp, k: Int64)`, and `Sp.put(c, 41)` ran `String.length`
/// on 41 (MEASURED). FAILS under ledger part 76.
#[test]
fn the_rule_reads_a_projection_from_the_spec_its_receiver_is_declared_by() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.owner_param
  import anthill.prelude.{Int64, String, List}
  sort Other
    sort E = ?
    operation other(o: Self) -> Int64
  end
  sort Sp
    sort E = ?
    operation put(s: Self, k: Int64) -> Int64
  end
  sort Car
    entity car(v: Int64)
    provides Other[E = String]
    provides Sp
    operation other(c: Car) -> Int64 = 0
    operation put(c: Car, k: c.E) -> Int64 = String.length(k)
  end
  operation go() -> Int64 =
    let c: Car = car(v: 1)
    Sp.put(c, 41)
end
"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "parameter 2 (`k: c.E`) takes less than the spec's",
            "the spec's `Int64` admits arguments the member's `String` does not",
        ],
        "a member's projection read from another spec's provision",
    );
}

/// … AND IN THE RETURN: `get(c: Car) -> c.E` returns `Other`'s `String` behind `-> Int64`;
/// `Sp.get(c) + 1` died adding 1 to a string (MEASURED). FAILS under ledger part 76.
#[test]
fn the_rule_reads_a_projection_from_the_spec_its_receiver_is_declared_by_at_the_return() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.owner_return
  import anthill.prelude.{Int64, String, List}
  sort Other
    sort E = ?
    operation other(o: Self) -> Int64
  end
  sort Sp
    sort E = ?
    operation get(s: Self) -> Int64
  end
  sort Car
    entity car(v: Int64)
    provides Other[E = String]
    provides Sp
    operation other(c: Car) -> Int64 = 0
    operation get(c: Car) -> c.E = "str"
  end
  operation go() -> Int64 =
    let c: Car = car(v: 1)
    Sp.get(c) + 1
end
"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &["the member returns `String`, which is not a subtype of the spec's `Int64`"],
        "a member's returned projection read from another spec's provision",
    );
}

/// … AND THEIR CONTROL: with one provision lending `E`, `c.E` is that binding whichever way it
/// is read; the member fits and runs through the spec call, to 41 + 1. Passes either way by
/// design.
#[test]
fn the_rule_reads_a_projection_from_the_spec_its_receiver_is_declared_by_control() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.owner_ctl
  import anthill.prelude.{Int64, String, List}
  sort Sp
    sort E = ?
    operation put(s: Self, k: s.E) -> Int64
  end
  sort Car
    entity car(v: Int64)
    provides Sp[E = Int64]
    operation put(c: Car, k: c.E) -> Int64 = k + c.v
  end
  operation go() -> Int64 =
    let c: Car = car(v: 1)
    Sp.put(c, 41)
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr9.owner_ctl.go"), Ok(42));
}

/// … AND FOR A WITNESS'S MEMBER: `BoxHolder.get(c: Box, k: c.T)` declares `c` at `Box`, whose
/// own provision lends `T = String`; the witness leaves `Holder`'s `T` unbound. Read as the
/// witness's wildcard, `k` was any type behind `k: Int64`, and `Holder.get(box, 41)` ran
/// `String.length` on 41 (MEASURED). FAILS under ledger part 76.
#[test]
fn a_witness_members_projection_is_read_as_its_receiver_is_declared() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.wit_unbound
  import anthill.prelude.{Int64, String, List}
  sort Other
    sort T = ?
    operation other(o: Self) -> Int64
  end
  sort Holder
    sort C = ?
    sort T = ?
    operation get(c: C, k: Int64) -> Int64
  end
  sort Box
    entity box(n: Int64)
    provides Other[T = String]
    operation other(b: Box) -> Int64 = 0
  end
  sort BoxHolder
    provides Holder[C = Box]
    operation get(c: Box, k: c.T) -> Int64 = String.length(k)
  end
  operation go() -> Int64 = Holder.get(box(n: 1), 41)
end
"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "parameter 2 (`k: c.T`) takes less than the spec's",
            "the spec's `Int64` admits arguments the member's `String` does not",
        ],
        "a witness member's projection read as the witness's wildcard",
    );
}

/// … AND ON THE SPEC'S SIDE: `get2(c: C, b: Box) -> b.T` declares `b` at `Box`, so `b.T` is
/// `Box`'s own `String` — not the witness's `T = Int64`, which the rule read, admitting `->
/// Int64`; the caller's `String.length(Holder.get2(…))` then met an `Int64` (MEASURED). FAILS
/// under ledger part 76.
#[test]
fn a_specs_projection_over_a_carrier_typed_parameter_is_the_carriers_own() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.wit_conc
  import anthill.prelude.{Int64, String, List}
  sort Other
    sort T = ?
    operation other(o: Self) -> Int64
  end
  sort Box
    entity box(n: Int64)
    provides Other[T = String]
    operation other(b: Box) -> Int64 = 0
  end
  sort Holder
    sort C = ?
    sort T = ?
    operation get2(c: C, b: Box) -> b.T
  end
  sort BoxHolder
    provides Holder[C = Box, T = Int64]
    operation get2(c: Box, b: Box) -> Int64 = b.n + 41
  end
  operation go() -> Int64 = String.length(Holder.get2(box(n: 1), box(n: 1)))
end
"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &["the member returns `Int64`, which is not a subtype of the spec's `String`"],
        "the spec's projection read from the witness instead of the receiver's own sort",
    );
}

/// A WITNESS'S BINDING IS READ AT THE RECEIVER PROJECTED, through the witness's carrier view:
/// `get2(c: C, d: D) -> d.U` at `ListHolder[E] provides Holder[C = List[T = E], D = List[T =
/// Int64], U = Option[T = E]]` reads `d.U` at `d`'s own element — `Option[T = Int64]` — as the
/// call does. Read at the operation's receiver (`c`, a list of strings) it was `Option[T =
/// String]`, and the member returning what the call reads was refused (MEASURED). Runs to 5 +
/// 37. FAILS under ledger part 77.
#[test]
fn a_witness_binding_is_read_at_the_receiver_projected() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.wit_view
  import anthill.prelude.{Int64, String, List, Option}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.List.{cons, nil}
  sort Holder
    sort C = ?
    sort D = ?
    sort U = ?
    operation get2(c: C, d: D) -> d.U
  end
  sort ListHolder
    sort E = ?
    provides Holder[C = List[T = E], D = List[T = Int64], U = Option[T = E]]
    operation get2(c: List[T = E], d: List[T = Int64]) -> Option[T = Int64] =
      match d
        case cons(x, _) -> some(x)
        case nil -> none
  end
  operation go() -> Int64 =
    match Holder.get2(["a", "b"], [5, 6])
      case some(v) -> v + 37
      case none -> 0
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr9.wit_view.go"), Ok(42));
}

/// A BINDING IS READ ONCE PER SPEC PARAMETER WHATEVER CARRIER ITS EXPANSION RIDES: `T = Strm[T
/// = Int64, E = {Error}]` holds a braced bare label, whose expansion is an occurrence; the
/// template kept terms only and fell back to the binding unexpanded, fresh per position — so
/// `both[W](c, x: Strm[… E = {Error[T = W]}], y: …)`, tying the two positions as the spec's one
/// `T` does, was refused (MEASURED; the unbraced twin ran). Runs to 7. FAILS under ledger part
/// 78.
#[test]
fn a_binding_holding_a_braced_label_stays_in_the_template() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.tpl_braced
  import anthill.prelude.{Int64, Bool, Option, String, List, Error}
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(v: T)
  end
  sort Sp
    sort T = ?
    operation both(s: Self, x: T, y: T) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = Strm[T = Int64, E = {Error}]]
    operation both[W](c: Self, x: Strm[T = Int64, E = {Error[T = W]}], y: Strm[T = Int64, E = {Error[T = W]}]) -> Int64 = 7
  end
  operation go() -> Int64 =
    let k: Car[V = Int64] = car(v: 1)
    let a: Strm[T = Int64, E = {Error[T = Bool]}] = strm(v: 1)
    let b: Strm[T = Int64, E = {Error[T = Bool]}] = strm(v: 2)
    Sp.both(k, a, b)
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr9.tpl_braced.go"), Ok(7));
}

/// A LABEL STANDING WHERE A ROW DOES IS THE ROW HOLDING IT: `provides Sp[E = Error[Foo]]` binds
/// the row `{Error[Foo]}`. Read through a callback's tail (`f: … @ {E}`) the bare label was no
/// row at all, and EVERY member was refused — the pass's own control, respelled without braces
/// (MEASURED). The raising callback is caught and its payload read: runs to 9. FAILS under
/// ledger part 79.
#[test]
fn an_unbraced_row_binding_is_the_row_holding_it() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.tpl_unbraced_tail
  import anthill.prelude.{Int64, String, Bool, List, Error, Result}
  import anthill.prelude.Result.{ok, err}
  sort Foo
    entity foo(n: Int64)
  end
  sort Bar
    entity bar(n: Int64)
  end
  sort Sp
    sort T = ?
    effects E = ?
    operation each(s: Self, f: (x: Int64) -> Int64 @ {E}) -> Int64
  end
  sort Car
    entity car(v: Int64)
    provides Sp[T = Int64, E = Error[Foo]]
    operation each(c: Car, f: (x: Int64) -> Int64 @ {Error[Foo]}) -> Int64 =
      match Error.reify[Rho = {}](lambda () -> f(1))
        case ok(v) -> v
        case err(b) -> b.n
  end
  operation boom(x: Int64) -> Int64 effects {Error[Foo]} = Error.raise(foo(n: 9))
  operation go() -> Int64 = Sp.each(car(v: 1), boom)
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr9.tpl_unbraced_tail.go"), Ok(9));
}

/// THE LABELS OF AN ARROW'S OWN ROW ARE SORT APPLICATIONS TOO: `x: Box[T = (u: Int64) -> Int64
/// @ {Error}]` takes a callback raising `Error` at any payload, so a member taking `@ {Error[T
/// = String]}` takes less. The walk expanded a row SLOT's labels and not an arrow's row, the
/// two bare `Error`s met as one, and `Sp.op(car, box(v: boom))` over a callback raising
/// `Error[T = Bool]` ended a pure `main` in "error: true" (MEASURED). The two sides print alike
/// — a nested arrow's row is not printed — and the refusal says so. FAILS under ledger part 80,
/// its note under part 82.
#[test]
fn an_arrows_own_row_is_expanded() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.row_arrow
  import anthill.prelude.{Int64, Bool, String, List, Error, Result, Function}
  import anthill.prelude.Result.{ok, err}
  sort Box
    sort T = ?
    entity box(v: T)
  end
  sort Sp
    sort T = ?
    operation op(s: Self, x: Box[T = (u: Int64) -> Int64 @ {Error}]) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation op(s: Self, x: Box[T = (u: Int64) -> Int64 @ {Error[T = String]}]) -> Int64 =
      match x
        case box(f) ->
          match Error.reify[Rho = {}](lambda () -> f(1))
            case ok(v) -> v
            case err(b) -> String.length(b)
  end
  operation boom(u: Int64) -> Int64 effects {Error[T = Bool]} = Error.raise(true)
  operation boomS(u: Int64) -> Int64 effects {Error[T = String]} = Error.raise("abc")
  operation go() -> Int64 =
    let y: Box[T = (u: Int64) -> Int64 @ {Error[T = Bool]}] = box(v: boom)
    Sp.op(car(v: 1), y)
end
"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "parameter 2 (`x: Box[T = Int64 -> Int64]`) takes less than the spec's",
            "The two types compared print alike",
        ],
        "a callback row narrower in its label's payload, nested in a type",
    );
}

/// … AND BEHIND AN ALIAS: `x: AnyErr` with `sort AnyErr = Strm[T = Int64, U = Int64, E =
/// {Error}]` is the type written in place. The alias kept its bare label where the spec's own
/// text was expanded, so the member the spec's text describes was refused "takes less"
/// (MEASURED). Runs to 3 + 4. FAILS under ledger part 81.
#[test]
fn an_aliass_written_row_is_expanded() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.row_alias
  import anthill.prelude.{Int64, Bool, String, List, Error}
  sort Strm
    sort T = ?
    sort U = ?
    effects E = ?
    entity strm(v: T)
  end
  sort AnyErr = Strm[T = Int64, U = Int64, E = {Error}]
  sort Sp
    sort T = ?
    operation op(s: Self, x: Strm[T = Int64, U = Int64, E = {Error}], y: Strm[T = Int64, U = Int64, E = {Error}]) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation op(s: Self, x: AnyErr, y: AnyErr) -> Int64 =
      match x
        case strm(a) ->
          match y
            case strm(b) -> a + b
  end
  operation go() -> Int64 =
    let p: Strm[T = Int64, U = Int64, E = {Error[T = Bool]}] = strm(v: 3)
    let q: Strm[T = Int64, U = Int64, E = {Error[T = String]}] = strm(v: 4)
    Sp.op(car(v: 1), p, q)
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr9.row_alias.go"), Ok(7));
}

/// … AND AT A PARAMETER, where the per-position comparison does not look — behind a
/// projection: `feed(c: Car, k: Sink[A = Animal])` behind `feed(s: Sp, k: Sink[A = s.T])` at
/// `T = cat`. The spec passes a `Sink[A = cat]`, which is no `Sink[A = Animal]` (`A` stands in
/// a callback's parameter), yet the two unified and the member was admitted: its body fed the
/// sink a `dog`, and `Sp.feed(car, k)` ended in "entity has no field 'lives'" (MEASURED on
/// every build). FAILS under ledger part 83.
#[test]
fn a_parameter_narrower_at_an_invariant_slot_is_refused_behind_a_projection() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.par_invariant
  import anthill.prelude.{Int64, String, List}
  sort Animal
    entity cat(lives: Int64)
    entity dog(bark: Int64)
  end
  sort Sink
    sort A = ?
    entity sink(f: (x: A) -> Int64)
  end
  sort Sp
    sort T = ?
    operation feed(s: Self, k: Sink[A = s.T]) -> Int64
  end
  sort Car
    entity car(v: Int64)
    provides Sp[T = cat]
    operation feed(c: Car, k: Sink[A = Animal]) -> Int64 =
      match k
        case sink(g) -> g(dog(bark: 3))
  end
  operation go() -> Int64 =
    let k: Sink[A = cat] = sink(f: lambda (x: cat) -> x.lives)
    Sp.feed(car(v: 1), k)
end
"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "parameter 2 (`k: Sink[A = Animal]`) takes less than the spec's",
            "the spec's `Sink[A = cat]` admits arguments the member's `Sink[A = Animal]` does not",
        ],
        "a parameter narrower at an invariant slot, behind a projection",
    );
}

/// A LABEL IN A ROW SLOT IS ONE ROW HOWEVER IT IS BRACED, wherever the slot stands: the
/// provision writes `T = Strm[T = Int64, E = Error]`, the member `E = {Error[T = W]}`. Only a
/// provision's own row PARAMETER was read as the row its label denotes; inside another binding
/// the bare label met the member's braced row as a label against a row, and the member tying
/// the two positions as the spec's one `T` does was refused (MEASURED). Runs to 7. FAILS under
/// ledger part 85.
#[test]
fn a_label_in_a_row_slot_is_one_row_however_it_is_braced() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.row_mixed
  import anthill.prelude.{Int64, Bool, String, List, Error}
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(v: T)
  end
  sort Sp
    sort T = ?
    operation op(s: Self, x: T, y: T) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = Strm[T = Int64, E = Error]]
    operation op[W](s: Self, x: Strm[T = Int64, E = {Error[T = W]}], y: Strm[T = Int64, E = {Error[T = W]}]) -> Int64 = 7
  end
  operation go() -> Int64 =
    let a: Strm[T = Int64, E = {Error[T = Bool]}] = strm(v: 1)
    let b: Strm[T = Int64, E = {Error[T = Bool]}] = strm(v: 2)
    Sp.op(car(v: 1), a, b)
end
"#,
    );
    assert_eq!(run_int64(&src, "wi0rp29mr9.row_mixed.go"), Ok(7));
}

/// A RETURN THAT UNIFIES ONLY THROUGH ITSELF IS NO FIT: `op[A](c: Car, a: Option[T = A]) ->
/// Option[T = A]` behind `op(s: Sp, a: Option[T = K]) -> Option[T = List[T = K]]`, `K` left
/// unbound, unifies by `A ↦ K` then `K ↦ List[T = K]` — a binding holding its own variable.
/// The return leg took that unifier's `true` for a fit, the member loaded, and a caller reading
/// the promised list met the bare payload (MEASURED: `match_failed` at run time). Under ledger
/// part 86 the PROCESS dies: the cyclic unifier is taken, and the resolve after it walks it.
#[test]
fn a_return_unifying_only_through_itself_is_refused() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.ret_cycle
  import anthill.prelude.{Int64, String, List, Option}
  import anthill.prelude.Option.{some, none}
  sort Sp
    sort T = ?
    sort K = ?
    operation size(s: Self) -> Int64
    operation op(s: Self, a: Option[T = K]) -> Option[T = List[T = K]]
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation size(c: Self) -> Int64 = 1
    operation op[A](c: Self, a: Option[T = A]) -> Option[T = A] = a
  end
  operation go() -> Int64 = Sp.size(car(v: 1))
end
"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "its own member 'op' does not fit",
            "the member returns `Option[T = ?A]`, which is not a subtype of the spec's",
        ],
        "a return that unifies only through a variable holding itself",
    );
}

/// `Car provides Sp[T = Int64, J = V]` — a WITNESS for `Int64`, whose own parameter `V` no
/// receiver fixes — and its member `op`, behind `op(t: T, x: K, {y})`.
fn witness_parameter_program(ns: &str, y: &str, go: &str) -> String {
    with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List, Option}}
  sort Sp
    sort T = ?
    sort K = ?
    sort J = ?
    sort L = ?
    operation op(t: T, x: K, {y}) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = Int64, J = V]
    operation op(t: Int64, x: Car[V = List[T = V]], y: x.J) -> Int64 = t + 1
  end
  operation go() -> Int64 =
    {go}
end
"#
    ))
}

/// A WITNESS'S OWN PARAMETER IS ANY TYPE, WHOEVER READS IT — it is not one of the slots a
/// provision's bindings leave open for the return ([`a_provision_slot_only_the_return_reads_is_the_members_to_pick`]).
/// Left open with them, the `V` of `J = V` was free where the member's own types name it, and
/// `x: Car[V = List[T = V]]` bound it inside itself: the loader's stack overflowed on a member
/// that fits (MEASURED during this pass, and on the two builds before it for another reason).
/// The member runs through its qualified call, to 41 + 1. It passes under ledger parts 87 and
/// 90 each — either keeps `V` from being bound inside itself and walked — and under the two
/// TOGETHER the process dies of that overflow (as under 84 and 90 together);
/// [`a_witness_parameter_is_no_type_a_member_fixes`] is the row part 87 alone fails.
#[test]
fn a_witness_parameter_is_any_type_whoever_reads_it() {
    let ns = "wi0rp29mr9.wit_own";
    let src = witness_parameter_program(
        ns,
        "y: L",
        "let k: Car[V = List[T = Int64]] = car(v: [1])\n    Car.op(41, k, [2])",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(42));
}

/// … AND ITS REFUSAL TWIN: with `y` typed by the spec's `K`, as `x` is, the spec passes `y` a
/// `Car[V = List[…]]`, which the member's `y: x.J` — a list — does not take. Refused, not
/// overflowed. Under parts 87 and 90 as its twin above.
#[test]
fn a_witness_parameter_is_any_type_whoever_reads_it_misfit() {
    let src = witness_parameter_program("wi0rp29mr9.wit_own_bad", "y: K", "0");
    assert_refused_naming(
        &load_errors(&src),
        &["parameter 3 (`y: x.J`) takes less than the spec's"],
        "a member narrower than the spec behind a witness's own parameter",
    );
}

/// … AND NO TYPE A MEMBER FIXES. `Car provides Sp[T = Int64, J = V]` receives an `Int64`, so
/// nothing a call passes says `V`: a caller's `requires Sp[T = Int64, J = Bool]` picks it. The
/// member `op(t: Int64, x: V)` behind `op(t: T, x: String)` then takes a `Bool` where the spec
/// passes a `String` — refused. No spec parameter reads `J`, so left among the provision's open
/// slots `V` was the member's own variable, took the `String`, and the member loaded (the tree
/// the eighth review saw admits it, and runs `Sp.op(n, "s")` under that `requires`; with the
/// member returning its `x` as `-> V` behind `-> J`, the caller's `let b: Bool = Sp.op(n, "s")`
/// ended "type mismatch: expected Bool, got String" before this ticket — MEASURED). FAILS under
/// ledger part 87, and under part 84 (the any-type then not the member's own `V`).
#[test]
fn a_witness_parameter_is_no_type_a_member_fixes() {
    let src = with_app(
        r#"
namespace wi0rp29mr9.wit_fix
  import anthill.prelude.{Int64, String, List, Option}
  sort Sp
    sort T = ?
    sort J = ?
    operation op(t: T, x: String) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = Int64, J = V]
    operation op(t: Int64, x: V) -> Int64 = t + 1
  end
  operation go() -> Int64 = 0
end
"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &["parameter 2 (`x: V`) takes less than the spec's"],
        "a witness's member fixing the witness's own parameter",
    );
}

/// … AND ITS CONTROL: typed by the spec's `J` on both sides, `x` is that `V`, which the spec
/// call's argument says. Runs through the spec call, to 41 + 1. Passes either way by design.
#[test]
fn a_witness_parameter_is_no_type_a_member_fixes_control() {
    let ns = "wi0rp29mr9.wit_fix_j";
    let src = with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List, Option}}
  sort Sp
    sort T = ?
    sort J = ?
    operation op(t: T, x: J) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = Int64, J = V]
    operation op(t: Int64, x: V) -> Int64 = t + 1
  end
  operation go() -> Int64 = Sp.op(41, "s")
end
"#
    ));
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(42));
}

/// `id(s: Sp, x: T) -> T` at `provides Sp[T = Strm[E = {Error}]]` — the binding leaves `Strm`'s
/// `T` and the label's payload unwritten, one type per call since the parameter reads them —
/// with the member `id{tparams}(c: Car, x: Strm[T = W, E = {row}]) -> Strm[T = W, E = {row}] = x`.
fn tied_return_program(ns: &str, tparams: &str, row: &str) -> String {
    with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, String, List, Error}}
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(v: T)
  end
  sort Sp
    sort T = ?
    operation id(s: Self, x: T) -> T
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = Strm[E = {{Error}}]]
    operation id{tparams}(c: Self, x: Strm[T = W, E = {{{row}}}]) -> Strm[T = W, E = {{{row}}}] = x
  end
  operation go() -> Int64 =
    let k: Car[V = Int64] = car(v: 1)
    let a: Strm[T = String, E = {{Error}}] = strm(v: "four")
    match Sp.id(k, a) case strm(v) -> String.length(v) + 38
end
"#
    ))
}

/// A RETURN SLOT THE SPEC TIES TO A PARAMETER'S IS TIED BY THE MEMBER, AND THE REFUSAL SAYS HOW.
/// `id[W](c, x: Strm[T = W, E = {Error}]) -> Strm[T = W, E = {Error}]` writes the label's payload
/// twice, unwritten: a parameter's is the member's to instantiate, the return's a type the
/// member picks and no caller knows — while the spec's one `T` promises the argument's own
/// back. The member's unwritten return slot used to unify with whatever stood across it, so
/// this loaded (MEASURED). The two sides print alike, and the refusal names the repair. FAILS
/// under ledger part 71 (it loads), under part 78 (the binding's braced row out of the
/// template), and its repair hint under part 88.
#[test]
fn a_return_slot_tied_to_a_parameter_is_tied_by_the_member() {
    let src = tied_return_program("wi0rp29mr9.ret_tied", "[W]", "Error");
    assert_refused_naming(
        &load_errors(&src),
        &[
            "its own member 'id' does not fit",
            "The member's return leaves a slot unwritten, which is a type the member picks and \
             no caller knows",
        ],
        "a return leaving unwritten what the spec ties to a parameter",
    );
}

/// … AND ITS CONTROL, the repair the refusal names: the payload named by a type parameter of
/// the member's that its parameter fixes. Runs through the spec call, to 4 + 38. Passes either
/// way by design.
#[test]
fn a_return_slot_tied_to_a_parameter_is_tied_by_the_member_control() {
    let ns = "wi0rp29mr9.ret_tied_ok";
    let src = tied_return_program(ns, "[W, P]", "Error[T = P]");
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(42));
}

/// `Car provides Sp[T = V]`, leaving the spec's second parameter unbound, with the spec
/// operation `rest` and `Car`'s member of it; `go` runs the member by its qualified call.
fn unbound_view_program(
    ns: &str,
    second: &str,
    spec_rest: &str,
    member_rest: &str,
    arg: &str,
) -> String {
    with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List, Option}}
  sort Sp
    sort T = ?
    {second}
    operation size(s: Self) -> Int64
    operation {spec_rest}
  end
  sort Car
    sort V = ?
    entity car(v: V, n: Int64)
    provides Sp[T = V]
    operation size(c: Self) -> Int64 = c.n
    operation {member_rest} = car(v: c.v, n: c.n + 1)
  end
  operation go() -> Int64 = Car.size(Car.rest(car(v: "s", n: 41){arg}))
end
"#
    ))
}

/// A SPEC PARAMETER THE PROVISION LEAVES UNBOUND IS A WILDCARD IN A SPEC VIEW TOO: behind `->
/// Sp[T = s.T, E = s.E]` at `provides Sp[T = V]`, a member returning its own carrier returns a
/// provider of that view, whatever `E` is for it. The relation compares a spec view's bindings
/// with the provider's, and a provider that binds no `E` is no `Sp[E = X]` for any written `X`
/// — so once the return's verdict became the relation's, this was refused (MEASURED during this
/// pass on a fixture of `wi210_dispatch_test`, which loaded before the ticket; the eighth pass
/// admitted it on unification's word alone). Runs to 41 + 1. FAILS under ledger part 89.
#[test]
fn a_member_returning_its_carrier_fits_a_view_over_an_unbound_parameter() {
    let ns = "wi0rp29mr9.wild_view";
    let src = unbound_view_program(
        ns,
        "effects E = ?",
        "rest(s: Self) -> Sp[T = s.T, E = s.E]",
        "rest(c: Self) -> Car[V = V]",
        "",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(42));
}

/// … AND WHERE THE WILDCARD HAS MET A VARIABLE OF THE MEMBER'S: the spec's bare `-> Sp` is this
/// instance, `K` included, and `f: (q: K) -> Int64` beside the member's `f: (q: X) -> Int64`
/// leaves `K` standing as the member's `X` — still open, still nothing a provider binds. Runs to
/// 41 + 1. FAILS under ledger part 89.
#[test]
fn a_member_returning_its_carrier_fits_a_view_whose_wildcard_met_its_own_variable() {
    let ns = "wi0rp29mr9.wild_met";
    let src = unbound_view_program(
        ns,
        "sort K = ?",
        "rest(s: Self, f: (q: K) -> Int64) -> Self",
        "rest[X](c: Self, f: (q: X) -> Int64) -> Car[V = V]",
        ", lambda (q: Int64) -> q",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(42));
}

/// `Car[V]` providing `Sp[T = Int64]` — and `Sq[J = V]`, which lends `J` — with the spec
/// operation `op({spec_rest})` and the member `op{tparams}(t: Int64, x: {x}, {member_rest})`,
/// whose `y` projects `x`.
fn projected_parameter_program(
    ns: &str,
    spec_rest: &str,
    tparams: &str,
    x: &str,
    member_rest: &str,
    go: &str,
) -> String {
    with_app(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List, Option}}
  sort Sp
    sort T = ?
    sort K = ?
    sort L = ?
    operation op(t: T, x: K, {spec_rest}) -> Int64
  end
  sort Sq
    sort J = ?
    operation oq(j: J) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = Int64]
    provides Sq[J = V]
    operation op{tparams}(t: Int64, x: {x}, {member_rest}) -> Int64 = t + 1
    operation oq(j: V) -> Int64 = 1
  end
  operation go() -> Int64 =
    {go}
end
"#
    ))
}

/// A RECEIVER'S ARGUMENTS REPLACE ITS SORT'S PARAMETERS ONCE. `x: Car[V = List[T = V]]`, written
/// inside `Car`, names `Car`'s own `V` inside its own argument — the ENCLOSING instance's, which
/// here nothing fixes. `y: x.J` at `J = V` is then `List[T = V]`, that `V` left as it is. Resolved
/// to a fixpoint, `V ↦ List[T = V]` has none: the loader's stack overflowed (MEASURED during
/// this pass, once the rule read `J` off the provision that lends it). The member runs through
/// its qualified call, to 41 + 1. Under ledger part 90 the PROCESS dies of that overflow; the
/// call file's part 27 FAILS it (the lending provision left out by its parameter's name).
#[test]
fn a_parameter_writing_its_sorts_own_parameter_is_replaced_once() {
    let ns = "wi0rp29mr9.once_lent";
    let src = projected_parameter_program(
        ns,
        "y: L",
        "",
        "Car[V = List[T = V]]",
        "y: x.J",
        "let k: Car[V = List[T = Int64]] = car(v: [1])\n    Car.op(41, k, [2])",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(42));
}

/// … AND ITS REFUSAL TWIN: behind the spec's `y: String` the member's `y: x.J` — a list — takes
/// less. Refused, not overflowed. Under ledger part 90 the process dies; the call file's part
/// 27 fails it as its twin.
#[test]
fn a_parameter_writing_its_sorts_own_parameter_is_replaced_once_misfit() {
    let src = projected_parameter_program(
        "wi0rp29mr9.once_lent_bad",
        "y: String",
        "",
        "Car[V = List[T = V]]",
        "y: x.J",
        "0",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["parameter 3 (`y: x.J`) takes less than the spec's"],
        "a member narrower than the spec behind a projection off its sort's own parameter",
    );
}

/// … AND THROUGH A FIELD: `y: x.v.T` reads the field `v: V` at the same receiver, then `List`'s
/// `T` off it — the enclosing `V` again. The loader's stack overflowed on this one on the tree
/// the eighth review saw as well (MEASURED). Runs to 41 + 1. Under ledger part 90 the process
/// dies.
#[test]
fn a_field_path_off_a_parameter_writing_its_sorts_own_parameter_is_replaced_once() {
    let ns = "wi0rp29mr9.once_field";
    let src = projected_parameter_program(
        ns,
        "y: L",
        "",
        "Car[V = List[T = V]]",
        "y: x.v.T",
        "let k: Car[V = List[T = Int64]] = car(v: [1])\n    Car.op(41, k, 2)",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(42));
}

/// WHAT A PROJECTION READS IS EACH ARGUMENT AS BOUND SO FAR. `op[W](t, x: Car[V = W], y: x.J,
/// z: W)` behind `y: String, z: String`: the positions holding no projection are compared first,
/// so `z` has bound `W` to `String` when `y` is read — and `x.J` at `J = V` is `String`. Read off
/// `x` as recorded when `x` was compared, `W` was still open, the projection stayed neutral, and
/// this member — which fits — was refused (MEASURED). Runs through its qualified call, to 41 + 1.
/// FAILS under ledger part 91, and under the call file's part 27 (the lending provision left out
/// by its parameter's name) — as its three siblings below do.
#[test]
fn a_projection_reads_its_receiver_as_bound_so_far() {
    let ns = "wi0rp29mr9.late_w";
    let src = projected_parameter_program(
        ns,
        "y: String, z: String",
        "[W]",
        "Car[V = W]",
        "y: x.J, z: W",
        "let k: Car[V = String] = car(v: \"a\")\n    Car.op(41, k, \"b\", \"c\")",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(42));
}

/// … AND ITS REFUSAL TWIN names the type read: behind `y: Int64` the member's `y` is the `String`
/// its `z` fixed. FAILS under ledger part 91 (refused all the same, naming the unread `x.J`).
#[test]
fn a_projection_reads_its_receiver_as_bound_so_far_misfit() {
    let src = projected_parameter_program(
        "wi0rp29mr9.late_w_bad",
        "y: Int64, z: String",
        "[W]",
        "Car[V = W]",
        "y: x.J, z: W",
        "0",
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "parameter 3 (`y: x.J`) takes less than the spec's",
            "the spec's `Int64` admits arguments the member's `String` does not",
        ],
        "a member narrower than the spec behind a projection a later position fixes",
    );
}

/// … AND OVER THE SORT'S OWN PARAMETER: `x: Car[V = List[T = V]]`, with `z: V` behind `z: String`
/// fixing the enclosing `V` before `y: x.J` is read as `List[T = String]`. Runs to 41 + 1. FAILS
/// under ledger part 91 (the receiver read as recorded, its `V` open: the neutral projection,
/// refused); passes under part 90 by design — once `V` is bound nothing holds its own parameter.
#[test]
fn a_projection_reads_its_sorts_own_parameter_as_bound_so_far() {
    let ns = "wi0rp29mr9.late_v";
    let src = projected_parameter_program(
        ns,
        "y: List[T = String], z: String",
        "",
        "Car[V = List[T = V]]",
        "y: x.J, z: V",
        "let k: Car[V = List[T = String]] = car(v: [\"a\"])\n    Car.op(41, k, [\"b\"], \"c\")",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(42));
}

/// … AND ITS REFUSAL TWIN: behind `y: List[T = Int64]` the member's `y` is a `List[T = String]`.
/// FAILS under ledger part 91 (refused all the same, naming the unread `x.J`).
#[test]
fn a_projection_reads_its_sorts_own_parameter_as_bound_so_far_misfit() {
    let src = projected_parameter_program(
        "wi0rp29mr9.late_v_bad",
        "y: List[T = Int64], z: String",
        "",
        "Car[V = List[T = V]]",
        "y: x.J, z: V",
        "0",
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "parameter 3 (`y: x.J`) takes less than the spec's",
            "the spec's `List[T = Int64]` admits arguments the member's `List[T = String]` does not",
        ],
        "a member narrower than the spec behind a projection its sort's own parameter fixes",
    );
}
