//! WI-20260929-0RP29 — a type projection NESTED in a type grounds to a type holding a value
//! and is eliminated, as its `N = Bool` twin is; and WI-606's fallback eliminates the
//! overriding operation's own projections instead of threading them.
//!
//! With `xs: List[T = Buf[T = Int64, N = 3]]` the projection `xs.T` is the occurrence-carried
//! `Buf[…, N = 3]` (a type holding a VALUE, WI-477). The elimination had one walk per
//! carrier, and the term walk answered a `TermId`, so wherever that projection sat INSIDE a
//! term-carried type it was refused "type projection resolved to a non-term carrier, which is
//! not yet supported": `List.splitFirst(xs)` and `xs.splitFirst()` (`Option[Pair[A = xs.T,
//! …]]`), a user's `unboxOpt(b: Box) -> Option[T = b.T]`, a requirement written at a
//! projection (`requires Desc[T = x.E]`), and every other form holding one — a named tuple,
//! an arrow, an effect row. The top-level `-> xs.T` ran, and so did every `N = Bool` twin.
//! `Stream.splitFirst(xs)` failed differently: the refusal sent the call to WI-606's
//! fallback, which threaded `List.splitFirst`'s return with ITS `xs.T` in it, so the caller
//! was told "expected Buf[T = Int64, N = 3], got xs.T" — `xs` being the override's own
//! parameter. The elimination is now ONE walk over `extract_type` on any carrier; the
//! fallback eliminates the override's projections against the call.
//!
//! And the fallback types the call against the override it runs — every argument against the
//! parameter at its position (a foreign sort's slot fresh per occurrence), judged by the
//! override's own parameter, a conflict refused as the qualified call refuses it, a receiver
//! passed by name, a `denoted` re-keyed once — and an effect that does not eliminate arms it
//! as a return does; the WI-481 return re-key and a dispatched override's effects read the
//! call's arguments by parameter. (The §3 member tie the fallback once enforced is refused
//! where the member is declared, `wi_0rp29_member_rule_test`.) A rebuilt form is its OCCURRENCE (a spec view excepted, the
//! `TermId` boundary WI-20260829-2NMXA removes), and the printer renders one as it renders its
//! term twin.
//!
//! Every row that can RUNS: an operation answers a number that names what was reached (the
//! element's `v`, a provider's tag), on the value-in-type element AND on its `N = Bool` twin
//! where the row has one, so a row says the two now agree. The rows that assert a LOAD
//! verdict say at their site why nothing can run.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! MEASURED by applying each part's back-out, present but wrong, and running this file's rows
//! (55 of them for parts 1–35) with `wi_0rp29_call_binding_test` (whose own parts its module doc lists),
//! `wi_s8cbv_projection_requirement_test` and `wi_ekwdc_carrier_requires_instantiation_test`:
//!
//!  1. THE WALK — `projection.rs` / `result.rs` at the parent commit (a walk per carrier). 22
//!     FAIL: every row whose projection grounds to the element holding a value — the stdlib
//!     spellings, the user's, the named tuple, the arrow, the effect row, the guard, a
//!     requirement at a projection and one held elsewhere, the fallback's own projection, the
//!     receiver passed by name, the two entity rebuilds, the positional print — refused
//!     "resolved to a non-term carrier" — and the row-atom splice, which holds no value and
//!     fails with a NESTED row instead (the splice is part of the walk backed out). Their
//!     controls fail with them:
//!     [`another_value_is_refused`], [`an_effect_row_holding_a_value_still_counts_it`],
//!     [`a_requirement_no_provider_covers_is_refused`] and
//!     [`a_wrong_value_through_the_fallback_is_refused`] refused for that reason before any
//!     value or label is compared, and [`a_refusal_names_the_same_cause_on_both_twins`], whose
//!     value twin LOADED — the old fallback swallowed that refusal and threaded the override's
//!     empty row.
//!  2. THE SPEC-VIEW ARM — a `SortView` rebuilt as an application, its `sort` slot dropped. 7
//!     FAIL: the three requirement rows here and four `wi_s8cbv` rows, whose requirement then
//!     names no spec (eval dies `__req_desc not bound`).
//!  3. THE SPEC VIEW LOWERED — rebuilt on the loader's carrier instead. 3 FAIL: the three
//!     requirement rows. The `wi_s8cbv` rows' bindings are terms, and pass.
//!  4. THE CARRIER-NEUTRAL `denoted` RE-KEY — occurrences only. 0 FAIL, by design: no program
//!     found puts a term-carried `denoted` naming a parameter into an eliminated type (a
//!     signature's rides the occurrence). The arm is carrier-neutral so that such a one would
//!     not keep the callee's parameter where its occurrence twin is re-keyed.
//!  5. A CHILD GROUNDING TO ITS OWN TERM — counted as a change. 0 FAIL, by design: the parent
//!     is rebuilt as the type it already was; what the check saves is the rebuild.
//!  6. THE PRINTER'S TYPE CHILD — a hash-consed child printed as a data term. 1 FAILS:
//!     [`a_guard_survives_the_rebuild`].
//!  7. THE PRINTER'S TERM GUARD — the guard walk reading entity spines only. 1 FAILS:
//!     [`a_guard_survives_the_rebuild`].
//!  8. THE PRINTER'S VALUE AND POSITIONAL ARMS — `denoted(3)` and `_1:` again. 2 FAIL:
//!     [`a_guard_survives_the_rebuild`], [`a_positional_tuple_and_a_value_print_as_their_term_twin`].
//!  9. THE ENTITY REBUILD PER KIND — sort applications only. 4 FAIL: the two entity rebuilds,
//!     and [`a_rebuilt_row_grounds_a_carriers_row`] with its control.
//! 10. THE JOIN OVER OCCURRENCE BINDINGS — bailing on one again. 1 FAILS:
//!     [`two_branches_carrying_one_rebuilt_arrow_join`].
//! 11. THE ROW-ATOM SPLICE — dropped. 1 FAILS: [`a_projection_written_as_a_row_atom_is_spliced`].
//! 12. THE DECLARATION CHECK — a member taking less than its spec, admitted. 1 FAILS:
//!     [`a_member_tied_tighter_than_its_spec_is_refused`].
//! 13. δ BEFORE σ IN THE FALLBACK — σ applied first. 1 FAILS:
//!     [`the_fallback_over_a_carrier_written_with_its_parameters`].
//! 14. THE FALLBACK KEYED BY POSITION — the receiver's type also keyed to the first
//!     carrier-typed override parameter. 2 FAIL: [`the_fallback_keys_the_override_by_position`]
//!     and its control.
//! 15. THE FALLBACK'S σ OVER EVERY ARGUMENT — over the receiver alone. 4 FAIL:
//!     [`an_overrides_own_type_parameter_is_bound_by_its_argument`] and its control (`W` left
//!     unbound, so the fallback declines), [`a_rotated_self_call_is_rekeyed_once`], and
//!     [`a_conflict_through_the_fallback_is_refused_as_the_qualified_call_refuses_it`], whose
//!     conflict no second argument then reaches.
//! 16. A CONFLICT IS THE CALL'S ERROR — the fallback declining it (the spec's unrelated "no
//!     member E" stands), or threading whichever binding came first. 1 FAILS:
//!     [`a_conflict_through_the_fallback_is_refused_as_the_qualified_call_refuses_it`].
//! 17. THE FALLBACK DECLINES AN UNBOUND OVERRIDE PARAMETER — threading `?X`. 1 FAILS:
//!     [`an_override_type_parameter_no_argument_binds_is_not_threaded`].
//! 18. THE FALLBACK DECLINES ANOTHER ARITY — pairing by position regardless; since the fourth
//!     review the check is in the shared owner (`concrete_self_receiver_override`), so both
//!     WI-606 sites agree. 1 FAILS: [`a_member_of_another_arity_is_not_threaded`].
//! 19. THE RECEIVER BY PARAMETER — the fallback declining a labelled call. 2 FAIL:
//!     [`a_receiver_passed_by_name`], `wi_0rp29_call_binding_test::a_mixed_calls_receiver_…`.
//! 20. THE FALLBACK'S ELIMINATION — the override's return threaded as written. 8 FAIL: the
//!     seven rows whose override's return the call reaches through a projection
//!     ([`the_fallback_eliminates_the_overrides_projection`],
//!     [`a_wrong_value_through_the_fallback_is_refused`], [`a_receiver_passed_by_name`], both
//!     position rows, [`a_rotated_self_call_is_rekeyed_once`],
//!     [`a_conflict_through_the_fallback_is_refused_as_the_qualified_call_refuses_it_control`]) and
//!     `wi_ekwdc…::a_receiver_projection_across_a_hop_is_eliminated`.
//! 21. THE FALLBACK'S DIRECT RE-KEY of a type holding no projection — dropped. 4 FAIL:
//!     [`an_overrides_own_parameter_is_rekeyed`] and its control,
//!     [`a_rotated_self_call_is_rekeyed_once`] on its projection-free twin, and
//!     `wi_0rp29_call_binding_test::an_effect_the_fallback_threads_takes_the_calls_own_rekey`.
//! 22. THE ONE RE-KEY — an eliminated type re-keyed again. 1 FAILS:
//!     [`a_rotated_self_call_is_rekeyed_once`] on its projection twin.
//! 23. THE EFFECT ARMING THE FALLBACK — an effect's failure refusing the call. 6 FAIL:
//!     [`an_effect_that_does_not_eliminate_takes_the_fallback`] and its control, and the four
//!     fallback-effect rows of `wi_0rp29_call_binding_test`.
//! 24. THE RETURN RE-KEY GATE — on the op's projections instead of the return's. 2 FAIL:
//!     [`a_return_beside_a_projected_parameter_is_rekeyed`] and its control.
//! 25. THE DISPATCHED EFFECT'S ARGUMENT — the positional one at the parameter's index. 2 FAIL:
//!     [`a_mixed_calls_override_effect_names_its_argument`] and its control.
//!
//! The fourth review's fix pass (its own measurement, with `wi_0rp29_member_rule_test`'s
//! parts):
//!
//! 26. THE OVERRIDE JUDGES THE ARGUMENTS (`validate_arg_against_param` in the fallback) —
//!     dropped. 1 FAILS: [`an_argument_the_override_refuses_is_refused`].
//! 27. THE OVERRIDE'S FOREIGN SORTS PER OCCURRENCE — unexpanded. 1 FAILS:
//!     [`two_bare_foreign_parameters_of_the_override_are_two`].
//! 28. THE BUILDER TAKES AN ENTITY-CARRIED CHILD (`type_children`) — not converted. 3 FAIL,
//!     PANICKING: [`a_join_over_a_type_holding_a_value_is_its_twins`],
//!     [`a_meet_over_a_type_holding_a_value_is_its_twins`] and
//!     [`a_list_literal_over_a_type_holding_a_value_loads`].
//! 29. A GUARDED ATOM DISTRIBUTES OVER A ROW — kept nested. 2 FAIL:
//!     [`a_guarded_atom_grounding_to_a_row_distributes_over_it`] and its control (a nested row
//!     named where the atom should be).
//! 30. AN ABSENT ATOM DISTRIBUTES OVER A ROW — kept nested. 1 FAILS:
//!     [`an_absent_atom_grounding_to_a_row_distributes_over_it`].
//!
//! MEASURED for the fifth /code-review's fixes, as above:
//!
//! 31. A ROW'S OPEN TAIL FOLLOWED (a bound one is its row, a variable placed as an atom) —
//!     refused. 4 FAIL: [`a_guarded_atom_over_a_braced_row_parameter_distributes`],
//!     [`a_guard_that_holds_over_a_braced_row_parameter_incurs_its_row`],
//!     [`a_guarded_atom_over_a_row_variable_tail_places_the_variable`] and
//!     [`a_guarded_atom_over_the_stdlib_mapped_stream_distributes`].
//! 32. THE OVERRIDE'S OWN PARAMETERS THROUGH THE SPEC'S AT THE CALL — from the raw arguments. 2
//!     FAIL: [`an_overrides_own_type_parameter_bound_twice_takes_the_join`] and its control (the
//!     cat and the dog then conflict on `W`).
//! 32b. … AND THE ARGUMENTS UNEXPANDED — the rule before, both together. 3 FAIL: those two and
//!     [`an_overrides_own_type_parameter_reads_the_spec_parameter_at_the_call`] (the two `nil`s
//!     share `List`'s `T`, and `W` takes `a`'s `Int64`; with either half alone the `w: "boom"`
//!     argument still binds `W` to `String`).
//! 33. … AND THROUGH THE RETURN TYPES — the parameters alone. 2 FAIL:
//!     [`a_call_site_bracket_reaches_the_fallback`] and its contradicted twin (the fallback
//!     declines, and the spec's "no member E" stands).
//! 34. THE FALLBACK SEEDED WITH THEM — an empty σ. 2 FAIL: the same two.
//! 35. THE FALLBACK'S ARGUMENT TYPES EXPANDED PER OCCURRENCE — as written. 1 FAILS:
//!     [`two_nils_through_the_fallback_are_two_lists`].
//! 36. THE FALLBACK'S OVERRIDE PARAMETERS EXPANDED AT EVERY DEPTH — at the top only. 1 FAILS:
//!     [`nested_bare_foreign_sorts_through_the_fallback_are_two`].
//! 37. THE FALLBACK REFUSES A `WrapSome` — a pass. 1 FAILS:
//!     [`the_fallback_refuses_an_argument_the_override_takes_as_an_option`].
//! 38. THE FALLBACK JUDGES A CALLBACK'S ROW — not. 1 FAILS: [`the_fallback_judges_a_callback_row`].
//!
//! MEASURED for the sixth /code-review's fixes, each part backed out present but wrong over the
//! three `wi_0rp29_*` files and `wi_xzmgc_composed_carrier_param_test`:
//!
//! 39. AN ABSENCE OVER A ROW VARIABLE DENIES THE ROW (`lacked_parts`, effects.rs) — read as a
//!     label. 6 FAIL: [`an_absence_over_a_row_variable_denies_the_variable`],
//!     [`an_absence_over_a_rigid_row_variable_refuses_a_label`],
//!     [`a_row_holding_a_variable_it_lacks_is_uninhabitable`],
//!     [`another_rigid_row_variable_beside_a_lacked_one_is_refused`],
//!     [`a_row_variable_stated_to_lack_the_row_is_passed`] and its control.
//! 40. … THE CALLBACK VALIDATOR'S HELD ROW (`@ {R}` against `-R`) — dropped. 1 FAILS:
//!     [`an_absence_over_a_row_variable_denies_the_variable`] (refused, but as "EffP
//!     unconstrained").
//! 41. … ITS LABEL OR RIGID ROW VARIABLE BESIDE A LACKED RIGID ROW (`row_unshown_outside_lacked`)
//!     — dropped. 2 FAIL: [`an_absence_over_a_rigid_row_variable_refuses_a_label`] and
//!     [`another_rigid_row_variable_beside_a_lacked_one_is_refused`]. Re-measured by the eighth
//!     pass, below.
//! 42. … `{R, -R}` UNINHABITABLE — not. 1 FAILS: [`a_row_holding_a_variable_it_lacks_is_uninhabitable`].
//! 43. THE CALLER'S EXPECTED TYPE REACHES THE OVERRIDE (`CallToOverride::expected`) — not. 2 FAIL:
//!     [`the_callers_expected_type_reaches_the_override`] and its control (the refusal then the
//!     spec's own, not the charged `Error[Int64]`).
//! 44. THE SPEC'S PARAMETERS PINNED BY THE THREADED RETURN — not. 2 FAIL: the same two
//!     ("expected a type for 'W'"). Re-measured by the eighth pass, below.
//! 45. THE ARGUMENTS BIND THE OVERRIDE'S OWN PARAMETERS (`override_at_call`'s join and
//!     unification) — the spec's side alone. 6 FAIL: [`an_override_parameter_only_the_receiver_binds_is_bound`],
//!     [`a_row_parameter_only_the_receiver_binds_is_charged`], both own-join rows,
//!     [`an_overrides_own_type_parameter_reads_the_spec_parameter_at_the_call`] and
//!     `wi_0rp29_call_binding_test::an_overrides_own_type_parameter_in_its_effects_is_bound`.
//!     (The unification alone, backed out, fails nothing: the join binds a parameter one argument
//!     fixes.)
//! 46. … BEFORE THE SPEC'S SIDE — after it. 1 FAILS:
//!     [`the_arguments_decide_an_override_parameter_before_the_spec`].
//! 47. THE FALLBACK VALIDATES WHAT THE OVERRIDE RECEIVES (`CallToOverride::passed`) — the raw
//!     argument. 1 FAILS: [`the_fallback_validates_what_the_override_receives`].
//! 48. … ITS CALLBACK ROW TAKES A FIELD PATH'S HEAD — variables only. 1 FAILS:
//!     [`the_fallbacks_callback_row_takes_a_field_paths_head`].
//! 49. … AGAINST THE PARAMETER AS WRITTEN — the deep-expanded copy. 1 FAILS:
//!     [`the_fallback_validates_against_the_parameter_as_written`].
//! 50. ONE SUBSTITUTION PER CALLBACK TYPE — an eliminated type re-keyed again. 1 FAILS:
//!     [`a_self_recursive_callback_row_is_rekeyed_once`].
//! 51. THE DECLARATIONS RELATED WITH PROJECTIONS MASKED — a pair holding one skipped. 3 FAIL:
//!     [`a_bracket_reaches_the_fallback_past_an_unreduced_return`] and both bracket rows.
//! 52. THE ROW RELATION'S OWN JUDGEMENT OF PART 41 — dropped (the validator alone). 1 FAILS:
//!     [`a_field_callback_beside_a_lacked_row_is_refused`] (as measured then; re-measured by
//!     the eighth pass, below — another row fails it now).
//! 53. A CALLBACK'S OWN ABSENCE STATES IT — not read. 2 FAIL:
//!     [`a_row_variable_stated_to_lack_the_row_is_passed`] and
//!     [`a_label_stated_to_lack_the_row_is_passed`].
//!
//! MEASURED for the seventh /code-review's fixes, over the three `wi_0rp29_*` files and
//! `wi_xzmgc_composed_carrier_param_test` (228 rows):
//!
//! 54. THE FALLBACK VALIDATES THE OPTION OF THE ARGUMENT (`CallToOverride::passed`) — the option
//!     the spec declares. 1 FAILS: [`the_fallback_validates_the_option_of_the_argument`].
//! 55. AN ABSENCE OVER A ROW VARIABLE READ THROUGH WHAT IT DENIES where a row is tested against
//!     its own absences (`row_self_contradiction`) — as written. 1 FAILS:
//!     [`a_lacked_row_bound_by_a_later_argument_is_still_enforced`] (its control passes either
//!     way by design).
//!
//! The fixtures binding `T = Car[V = ?, EC = ?]` write the independent instance the seventh
//! pass's interim reading no longer gives a bare `T = Car` (the member-rule file's part 50).
//!
//! MEASURED for the seventh /code-review's findings 11 and 14 (the eighth pass), over the three
//! `wi_0rp29_*` files, `wi_xzmgc_composed_carrier_param_test` and `wi347_override_refinement_test`
//! (318 rows):
//!
//! 56. THE CALLBACK ROW JUDGED OF EVERY ARGUMENT (`validate_callback_effect_row`) — returned for
//!     one that is neither an operation reference nor a lambda. 3 FAIL:
//!     [`a_field_callback_is_held_to_a_lacked_row_however_it_is_passed`],
//!     [`a_field_callback_raising_a_denied_label_is_refused`] and
//!     [`a_field_callback_beside_a_lacked_row_is_refused`] (refused then only as `EffP`
//!     unconstrained).
//! 57. A ROW PARAMETER WRITTEN BARE A TAIL OF THE OPERATION'S OWN ROW
//!     (`check_declared_row_contradiction`) — filed as a label. 1 FAILS:
//!     [`a_row_parameter_held_and_lacked_is_refused_at_its_declaration`].
//! 58. A CALLBACK ROW TESTED AGAINST ITS ABSENCES AS THE CALL READS IT
//!     (`check_signature_self_contradiction` over the eliminated parameter types) — as declared.
//!     2 FAIL: [`a_callback_row_is_tested_against_the_absences_the_call_splices`] and
//!     [`an_absence_over_an_unwritten_row_is_stated_on_the_callbacks_own_row`] — the latter also
//!     with only the check's gate backed out (an operation binding no type parameter of its
//!     own then unchecked).
//! 59. AN ABSENCE OVER A NEUTRAL ROW PROJECTION A LACKED ROW (`lacked_rows`) — a label only. 1
//!     FAILS: [`an_absence_over_an_unwritten_row_denies_that_row`].
//! 60. THE FALLBACK'S RETURN PIN PER SPEC TYPE PARAMETER — committed only whole. 2 FAIL:
//!     [`the_fallbacks_return_pins_each_spec_type_parameter`] and its control (the refusal then
//!     the unconstrained `W`).
//!
//! THREE EARLIER PARTS RE-MEASURED, the eighth pass having changed what they fail:
//!   * part 41 (the validator's refusal of what cannot be shown outside a lacked row, dropped):
//!     5 FAIL — its two rows, [`a_field_callback_beside_a_lacked_row_is_refused`],
//!     [`a_field_callback_is_held_to_a_lacked_row_however_it_is_passed`] and
//!     [`an_absence_over_an_unwritten_row_denies_that_row`];
//!   * part 44 (the spec's parameters pinned by the threaded return — not at all): 4 FAIL —
//!     its two rows and the two of part 60;
//!   * part 52 (the row relation's own judgement of part 41, dropped): the field-callback row
//!     it failed is refused by the validator now (part 56), whatever the relation says, and 1
//!     FAILS — [`a_returned_callback_is_held_to_a_lacked_row_by_the_relation`], the row written
//!     for it: a callback RETURNED, which no validator sees.
//!
//! Every row fails under at least one part but the controls, each passing either way by
//! design (see their sites): [`a_lacked_row_bound_by_a_later_argument_is_still_enforced_control`],
//! [`a_projection_written_as_a_row_atom_is_spliced_control`],
//! [`an_argument_the_override_refuses_is_refused_control`] (the fallback threads a call its
//! member takes), [`an_absent_atom_grounding_to_a_row_distributes_over_it_control`],
//! [`an_absence_over_a_row_variable_control`] and
//! [`a_field_callback_beside_a_lacked_row_is_refused_control`] (pure callbacks). The argument
//! half of [`a_call_site_bracket_reaches_the_fallback_contradicted`] is a sixth, stated at its
//! site. The eighth pass's: [`a_field_callback_raising_a_denied_label_is_refused_control`],
//! [`a_call_result_callback_naming_a_value_is_admitted_where_the_row_admits_it`],
//! [`a_row_parameter_held_and_lacked_is_refused_at_its_declaration_control`],
//! [`a_callback_row_is_tested_against_the_absences_the_call_splices_control`] and
//! [`a_returned_callback_is_held_to_a_lacked_row_by_the_relation_control`] — each a program the
//! widened checks must not refuse — and the first and third assertions of
//! [`an_absence_over_an_unwritten_row_is_stated_on_the_callbacks_own_row`], as its site says.
//!
//! MEASURED for the eighth /code-review's findings 13 and 14 (the ninth pass) — the callback row's
//! validator and the rows it reads — each part backed out present but wrong over the three
//! `wi_0rp29_*` files, `wi_xzmgc_composed_carrier_param_test`, `wi347_override_refinement_test` and
//! `wi_f3fyj_value_in_type_binding_test` (434 rows):
//!
//! 61. A VARIABLE THAT IS NO CALLABLE PLACE SAYS NO BINDERS (`callback_actual_places`) — an empty
//!     list of them, as an operation taking nothing. 4 FAIL:
//!     [`a_binder_at_no_known_position_is_refused_where_the_row_speaks_of_one`],
//!     [`a_callback_bound_by_a_pattern_or_typed_function_is_judged`],
//!     [`a_callback_held_in_a_variable_is_judged`] and
//!     [`a_callback_held_in_a_variable_is_judged_by_the_stdlib`].
//! 62. A `let` KEEPS ITS CALLABLE'S BINDERS (`bind_callable_places`, build.rs) — keeps none. 2
//!     FAIL: [`a_let_bound_lambda_is_aligned_by_its_binders`] and
//!     [`a_let_bound_lambda_is_aligned_by_its_binders_control`].
//! 63. A CALLBACK PARAMETER'S PLACE SAYS ITS OWN POSITION (`callback_binder_position`) — not read.
//!     2 FAIL: [`a_callback_parameters_place_says_its_own_position`] and
//!     [`a_callback_parameters_place_says_its_own_position_control`].
//! 64. A LABEL NAMING A VALUE COMPARED AS IT STANDS WHERE THE BINDERS ARE UNKNOWN — passed over. 4
//!     FAIL: [`a_binder_at_no_known_position_is_refused_where_the_row_speaks_of_one`],
//!     [`a_callback_parameters_place_says_its_own_position`],
//!     [`a_label_naming_a_value_in_scope_is_compared_as_it_stands`] and
//!     [`a_label_naming_a_value_in_scope_is_held_to_a_closed_row`].
//! 65. A BINDER AT NO KNOWN POSITION REFUSED (`unplaced_binder`) — not refused. 1 FAILS:
//!     [`a_binder_at_no_known_position_is_refused_where_the_row_speaks_of_one`].
//! 66. THE CALLBACK'S OWN ROW VARIABLE JUDGED UNDER A CLOSED ROW — not judged. 1 FAILS:
//!     [`a_callbacks_own_row_variable_is_not_admitted_by_a_closed_row`].
//! 67. A CALLBACK STATING AN ABSENCE JUDGED ON WHAT IT PRESENTS — exempt. 2 FAIL:
//!     [`a_callback_stating_an_absence_is_held_to_a_closed_row`] and
//!     [`a_callback_stating_an_absence_is_held_to_a_denied_label`].
//! 68. A `Function[A, B, E]` SLOT'S BARE ROW PARAMETER THE OPEN ROW `{E}` (`canonical_effects_row`,
//!     callable.rs) — flattened as a list. 2 FAIL:
//!     [`a_function_slots_bare_row_parameter_is_an_open_row`] and
//!     [`a_function_slots_bare_row_parameter_takes_a_bracket`].
//! 69. A CLOSED ROW A SUBSET OF ONE WITH A RIGID TAIL — `{} <: {R}`, `{} <: {R, Q}`
//!     (`relate_effect_rows`, effects.rs) — no subset of it. 3 FAIL:
//!     [`a_pure_callback_fits_a_function_slot_whose_row_is_the_callers_own`],
//!     [`a_pure_callback_fits_a_slot_whose_row_is_the_callers_own`] and
//!     [`a_pure_callback_fits_a_slot_whose_row_is_two_of_the_callers_own`]. Said of a LONE rigid
//!     tail only, 1 FAILS ([`a_pure_callback_fits_a_slot_whose_row_is_two_of_the_callers_own`]);
//!     said of every union of tails, flexible ones too,
//!     `typing_test::subtype_rejects_malformed_multi_tail_row` FAILS (MEASURED by the workspace
//!     run).
//!
//! Parts 62 and 63 TOGETHER: 6 FAIL — the four rows of the two parts and
//! [`a_let_over_a_callback_parameter_is_aligned_by_its_places`] with its control, which fail under
//! neither alone (the `let` keeps the parameter's places, and each place says its own position:
//! either reading aligns it).
//!
//! AN EARLIER PART RE-MEASURED, this pass having rewritten the validator's entry:
//!   * part 56 (the callback row judged of every argument — returned for one that says no binders):
//!     11 FAIL — [`a_binder_at_no_known_position_is_refused_where_the_row_speaks_of_one`],
//!     [`a_callback_bound_by_a_pattern_or_typed_function_is_judged`],
//!     [`a_callback_held_in_a_variable_is_judged`],
//!     [`a_callback_held_in_a_variable_is_judged_by_the_stdlib`],
//!     [`a_callback_parameters_place_says_its_own_position`],
//!     [`a_field_callback_beside_a_lacked_row_is_refused`],
//!     [`a_field_callback_is_held_to_a_lacked_row_however_it_is_passed`],
//!     [`a_field_callback_raising_a_denied_label_is_refused`],
//!     [`a_function_slots_bare_row_parameter_is_an_open_row_control`],
//!     [`a_label_naming_a_value_in_scope_is_compared_as_it_stands`] and
//!     [`a_label_naming_a_value_in_scope_is_held_to_a_closed_row`].
//!
//! Of this pass's 26 rows, every one fails under at least one part but the two of parts 62 and 63
//! together and five passing either way by design, as their sites say:
//! [`a_callback_held_in_a_variable_is_judged_control`],
//! [`a_binder_at_no_known_position_is_refused_where_the_row_speaks_of_one_control`],
//! [`a_callbacks_own_row_variable_is_not_admitted_by_a_closed_row_mirror`],
//! [`a_callbacks_own_row_variable_is_not_admitted_by_a_closed_row_control`] and
//! [`a_pure_callback_fits_a_slot_whose_row_is_two_of_the_callers_own_control`].
//! [`a_function_slots_bare_row_parameter_is_an_open_row_control`] fails under the earlier part 56
//! alone.

use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64 as run_src};

/// `Buf[T, N]` (`N` the value-in-type argument), `val` over the element at `N = {n}`, and
/// `Box[T]`. `body` follows.
fn program(ns: &str, n: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, List, Option, Pair, Stream}}
  import anthill.prelude.List.{{cons, nil}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end

  sort Box
    sort T = ?
    entity box(item: T)
  end

  operation val(b: Buf[T = Int64, N = {n}]) -> Int64 = b.v
{body}
end
"#
    )
}

/// `program(ns, n, body(n))`, `ns.go()` run.
fn run(ns: &str, n: &str, body: &dyn Fn(&str) -> String) -> Result<i64, String> {
    run_src(&program(ns, n, &body(n)), &format!("{ns}.go"))
}

/// The value-in-type element (`N = 3`) and its `N = Bool` twin both run to `expected`.
fn runs_as_its_twin(ns: &str, expected: i64, body: impl Fn(&str) -> String) {
    assert_eq!(
        run(&format!("{ns}_bool"), "Bool", &body),
        Ok(expected),
        "{ns}: the N = Bool twin"
    );
    assert_eq!(
        run(&format!("{ns}_value"), "3", &body),
        Ok(expected),
        "{ns}: the element holding a value, N = 3"
    );
}

/// `first` peels a `List` of `Buf`s at `N = {n}` with `peel` and hands the head to `val`.
fn first_op(peel: &str, n: &str) -> String {
    format!(
        "  operation first(xs: List[T = Buf[T = Int64, N = {n}]]) -> Int64 =\n    \
         match {peel}\n      \
         case some(pair(b, _)) -> val(b)\n      \
         case none() -> 0\n"
    )
}

/// [`first_op`], run on a one-element list.
fn list_first(peel: &str, n: &str) -> String {
    format!(
        "{}  operation go() -> Int64 = first(cons(buf(v: 7), nil))",
        first_op(peel, n)
    )
}

// ── the ticket's spellings ────────────────────────────────────────────────────────────

/// `List.splitFirst -> Option[Pair[A = xs.T, B = List[xs.T]]]`, called qualified.
#[test]
fn the_qualified_list_call() {
    runs_as_its_twin("wi0rp29.list_q", 7, |n| {
        list_first("List.splitFirst(xs)", n)
    });
}

/// … and as a dot call.
#[test]
fn the_dot_call() {
    runs_as_its_twin("wi0rp29.list_dot", 7, |n| list_first("xs.splitFirst()", n));
}

/// `Stream.splitFirst -> Option[Pair[A = s.T, B = Stream[T = s.T, E = s.E]]]`, dispatched to
/// `List`'s — the spelling the fallback's leak reached on the parent commit.
#[test]
fn the_stream_spec_call() {
    runs_as_its_twin("wi0rp29.stream", 7, |n| {
        list_first("Stream.splitFirst(xs)", n)
    });
}

/// The TAIL keeps the element too — `B = List[xs.T]`, the return's second projection: handed
/// on to `first`, which takes the value-in-type list, and peeled again.
#[test]
fn the_tail_keeps_the_element() {
    runs_as_its_twin("wi0rp29.tail", 7, |n| {
        format!(
            "{}  operation second(xs: List[T = Buf[T = Int64, N = {n}]]) -> Int64 =\n    \
             match List.splitFirst(xs)\n      \
             case some(pair(_, t)) -> first(t)\n      \
             case none() -> 0\n  \
             operation go() -> Int64 = second(cons(buf(v: 1), cons(buf(v: 7), nil)))",
            first_op("List.splitFirst(xs)", n)
        )
    });
}

/// Not the stdlib's: a user's projection nested in a return, beside the top-level
/// `unbox(b: Box) -> b.T` that always ran.
#[test]
fn a_users_projection_nested_in_a_return() {
    runs_as_its_twin("wi0rp29.box", 7, |n| {
        format!(
            "  operation unboxOpt(b: Box) -> Option[T = b.T] = some(b.item)\n  \
             operation first(x: Box[T = Buf[T = Int64, N = {n}]]) -> Int64 =\n    \
             match unboxOpt(x)\n      \
             case some(b) -> val(b)\n      \
             case none() -> 0\n  \
             operation go() -> Int64 = first(box(buf(v: 7)))"
        )
    });
}

/// THE CONTROL: the element is the type the list holds, value and all — a list at `N = 4`
/// handed to `val` at `N = 3` is refused naming both. A projection that grounded to a
/// wildcard would let it through.
#[test]
fn another_value_is_refused() {
    let body = "  operation first(xs: List[T = Buf[T = Int64, N = 4]]) -> Int64 =\n    \
                match List.splitFirst(xs)\n      \
                case some(pair(b, _)) -> val(b)\n      \
                case none() -> 0";
    assert_refused_naming(
        &load_errors(&program("wi0rp29.other", "3", body)),
        &["Buf[T = Int64, N = 3]", "Buf[T = Int64, N = 4]"],
        "an element at N = 4 where val takes N = 3",
    );
}

/// A REFUSAL THE TWINS SHARE, reached for its own cause: the element holding a value was
/// refused before either program's real fault was looked at ("resolved to a non-term
/// carrier"), and now meets the refusal its `N = Bool` twin does — asserted on both, naming
/// the cause. `Stream.splitFirst` over a `Cnt` whose `E` is `{Error[EmptyStream]}` incurs that
/// row, which `first` does not declare; and the tail it answers over a `List` is a `Stream`,
/// which `List.length` does not take.
#[test]
fn a_refusal_names_the_same_cause_on_both_twins() {
    for n in ["Bool", "3"] {
        let row = format!(
            r#"
namespace wi0rp29.shared_row_{tag}
  import anthill.prelude.{{Int64, Bool, List, Option, Pair, Stream, Error, EmptyStream}}
  import anthill.prelude.List.{{cons, nil}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end

  sort Cnt
    sort T = ?
    effects E = ?
    entity cnt(items: List[T])
    provides Stream[T = T, E = E]
    operation splitFirst(c: Cnt) -> Option[Pair[A = T, B = Cnt[T = T, E = E]]] =
      match List.splitFirst(c.items)
        case none() -> none
        case some(pair(h, t)) -> some(pair(h, cnt(t)))
  end

  operation val(b: Buf[T = Int64, N = {n}]) -> Int64 = b.v
  operation first(x: Cnt[T = Buf[T = Int64, N = {n}], E = {{Error[EmptyStream]}}]) -> Int64 =
    match Stream.splitFirst(x)
      case some(pair(b, _)) -> val(b)
      case none() -> 0
end
"#,
            tag = if n == "3" { "value" } else { "bool" }
        );
        assert_refused_naming(
            &load_errors(&row),
            &["undeclared effect", "Error[T = EmptyStream]"],
            &format!("the row the call incurs, undeclared, at N = {n}"),
        );
        let tail = format!(
            "  operation tailLen(xs: List[T = Buf[T = Int64, N = {n}]]) -> Int64 =\n    \
             match Stream.splitFirst(xs)\n      \
             case some(pair(_, rest)) -> List.length(rest)\n      \
             case none() -> 0"
        );
        let ns = format!(
            "wi0rp29.shared_tail_{}",
            if n == "3" { "value" } else { "bool" }
        );
        assert_refused_naming(
            &load_errors(&program(&ns, n, &tail)),
            &[&format!(
                "expected List[T = ?_], got Stream[T = Buf[T = Int64, N = {n}]"
            )],
            &format!("the Stream tail handed to List.length, at N = {n}"),
        );
    }
}

// ── the other forms a projection can sit in ───────────────────────────────────────────

/// In a named tuple: `(e: b.T, n: Int64)`, answering `v + n`.
#[test]
fn a_named_tuple_holding_the_projection() {
    runs_as_its_twin("wi0rp29.tuple", 8, |n| {
        format!(
            "  operation tag(b: Box) -> Option[T = (e: b.T, n: Int64)] = some((e: b.item, n: 1))\n  \
             operation first(x: Box[T = Buf[T = Int64, N = {n}]]) -> Int64 =\n    \
             match tag(x)\n      \
             case some((e, k)) -> val(e) + k\n      \
             case none() -> 0\n  \
             operation go() -> Int64 = first(box(buf(v: 7)))"
        )
    });
}

/// In an arrow's result: `(u: Int64) -> b.T`, applied.
#[test]
fn an_arrow_holding_the_projection() {
    runs_as_its_twin("wi0rp29.arrow", 7, |n| {
        format!(
            "  operation getter(b: Box) -> Option[T = (u: Int64) -> b.T] = \
             some(lambda (u: Int64) -> b.item)\n  \
             operation first(x: Box[T = Buf[T = Int64, N = {n}]]) -> Int64 =\n    \
             match getter(x)\n      \
             case some(f) -> val(f(0))\n      \
             case none() -> 0\n  \
             operation go() -> Int64 = first(box(buf(v: 7)))"
        )
    });
}

/// In an effect row nested in a type: `relay`'s `E = {s.E, Error[EmptyStream]}`, where `s.E`
/// grounds to `{Modify[p]}` — a row holding a value. `use` declares `declared`.
///
/// A LOAD VERDICT, not a run: `Strm` has no constructor and `Producer` no instance, so
/// nothing here CAN run — what is measured is the typer's verdict on the row, the thing the
/// refusal got wrong.
fn effect_row_program(ns: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Modify, EffectsRuntime, Int64, Error, EmptyStream}}
  sort Strm
    sort T = ?
    effects E = ?
    operation obs(s: Strm) -> Bool effects s.E = true
  end
  sort Producer
    operation eff_stream(p: Producer) -> Strm[T = Int64, E = {{Modify[p]}}]
    operation relay(s: Strm) -> Strm[T = s.T, E = {{s.E, Error[EmptyStream]}}]
  end
  operation use(p: Producer) -> Bool effects {{{declared}}} =
    Strm.obs(Producer.relay(Producer.eff_stream(p)))
end
"#
    )
}

/// Declaring the whole row loads. Refused before the walk, as the non-term carrier.
#[test]
fn an_effect_row_holding_a_value_loads() {
    let errs = load_errors(&effect_row_program(
        "wi0rp29.row",
        "Modify[p], Error[EmptyStream]",
    ));
    assert!(
        errs.is_empty(),
        "the declared row covers the call: {errs:#?}"
    );
}

/// THE CONTROL: the row still carries `Modify[p]` after the rebuild — leaving it undeclared
/// is refused naming it. A rebuild that dropped the label would load this.
#[test]
fn an_effect_row_holding_a_value_still_counts_it() {
    assert_refused_naming(
        &load_errors(&effect_row_program(
            "wi0rp29.row_short",
            "Error[EmptyStream]",
        )),
        &["undeclared effect", "Modify[T = p]"],
        "a row holding Modify[p], declared without it",
    );
}

/// A GUARDED effect keeps its guard through the rebuild: `Error[b.T] :- eq(b, b)`, the label
/// grounding to the value-in-type element. The stamped type is PRINTED by a compile-time
/// macro that raises it as its message — the reader is the `TermPrinter` every query and
/// reflect answer goes through.
///
/// A LOAD VERDICT BY CONSTRUCTION: the macro's raise is how the type reaches a string, so the
/// "refusal" IS the measurement. Asserted on both twins, for the guard's goal.
#[test]
fn a_guard_survives_the_rebuild() {
    for (ns, n) in [("wi0rp29.guard_bool", "Bool"), ("wi0rp29.guard_value", "3")] {
        let src = format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List, Bool, Error, Option}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.reflect.{{NodeOccurrence, occurrence_type, term_to_string}}

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end

  sort Box
    sort T = ?
    entity box(item: T)
  end

  operation mk(b: Box) -> Option[T = (u: Int64) -> Bool @ {{Error[b.T] :- eq(b, b)}}] = none

  operation chk(x: NodeOccurrence) -> NodeOccurrence effects {{Error[String]}} =
    match occurrence_type(x)
      case some(t) -> Error.raise(term_to_string(t))
      case none() -> x

  operation trig[A](x: A) -> Int64 = 0
  rule trig(?x) <=> chk(?x) @[simp]

  operation go(x: Box[T = Buf[T = Int64, N = {n}]]) -> Int64 = trig(mk(x))
end
"#
        );
        assert_refused_naming(
            &load_errors(&src),
            &[&format!("Error[T = Buf[T = Int64, N = {n}]] :- eq(b, b)")],
            &format!("the printed type of `mk(x)` at N = {n}, guard and all"),
        );
    }
}

// ── a requirement written at a projection ─────────────────────────────────────────────

/// `pick`'s requirement is `Desc[T = x.E]`, and `x.E` is the element `outer` holds — the
/// provider at `N = {n}` answers 7, the one at `N = {other}` answers 9. `extra` is added
/// verbatim (another provider, a caller-side requirement).
fn requirement_program(
    ns: &str,
    n: &str,
    other: &str,
    outer_requires: &str,
    extra: &str,
) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String}}

  sort Desc
    sort T = ?
    operation tag() -> Int64
  end

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end

  sort Box
    sort E = ?
    entity box(v: E)
  end

  sort Here
    import anthill.prelude.Int64
    entity here
    provides Desc[T = Buf[T = Int64, N = {n}]]
    operation tag() -> Int64 = 7
  end

  sort There
    import anthill.prelude.Int64
    entity there
    provides Desc[T = Buf[T = Int64, N = {other}]]
    operation tag() -> Int64 = 9
  end
{extra}
  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag()
  operation outer(b: Box[E = Buf[T = Int64, N = {n}]]) -> Int64{outer_requires} = pick(b)
  operation go() -> Int64 = outer(box(v: buf(v: 1)))
end
"#
    )
}

/// THE PROVIDER AT THE ELEMENT'S OWN VALUE answers, of two that differ only in `N`. The
/// requirement's spec is a `SortView(Desc)[T = …]`, whose `Desc` slot the rebuild keeps.
#[test]
fn a_requirement_at_a_projection_holding_a_value() {
    for (ns, n, other) in [
        ("wi0rp29.req_bool", "Bool", "String"),
        ("wi0rp29.req_value", "3", "4"),
    ] {
        assert_eq!(
            run_src(
                &requirement_program(ns, n, other, "", ""),
                &format!("{ns}.go")
            ),
            Ok(7),
            "{ns}: the provider at N = {n}, not the one at N = {other}"
        );
    }
}

/// A CALLER'S REQUIREMENT AT ANOTHER BINDING IS NO COVER: `outer` holds `requires Desc[T =
/// Red]`, and `pick`'s demand at the `Buf` must not be served by it (Red answers 5) — a spec
/// that lost its binding would demand nothing and be covered by it.
#[test]
fn a_requirement_elsewhere_is_no_cover() {
    let red = "\n  sort Red\n    import anthill.prelude.Int64\n    entity red\n    \
               provides Desc[T = Red]\n    operation tag() -> Int64 = 5\n  end\n";
    let ns = "wi0rp29.req_red";
    assert_eq!(
        run_src(
            &requirement_program(ns, "3", "4", " requires Desc[T = Red]", red),
            &format!("{ns}.go")
        ),
        Ok(7)
    );
}

/// … and a requirement at a value NO provider covers is refused, naming it.
#[test]
fn a_requirement_no_provider_covers_is_refused() {
    let src = requirement_program("wi0rp29.req_none", "3", "4", "", "").replace(
        "provides Desc[T = Buf[T = Int64, N = 3]]",
        "provides Desc[T = Buf[T = Int64, N = 5]]",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["Desc[T = wi0rp29.req_none.Buf[T = anthill.prelude.Int64, N = 3]]"],
        "a requirement at N = 3 with providers at N = 5 and N = 4 only",
    );
}

// ── the WI-606 fallback ───────────────────────────────────────────────────────────────

/// A carrier whose `splitFirst` writes its return with projections on ITS OWN parameter
/// (`c.T`), and whose `E` is a row over its own `EC`. With `EC` left to an operation's
/// parameter `R`, `Stream.splitFirst`'s `s.E` does not ground (a non-ground row, WI-484), so
/// the call takes the fallback and threads THIS return — which carried `c.T` through as
/// written.
const CNT: &str = r#"
  sort Cnt
    sort T = ?
    effects EC = ?
    entity cnt(items: List[T])
    provides Stream[T = T, E = {EC}]
    operation splitFirst(c: Cnt) -> Option[Pair[A = c.T, B = Cnt[T = c.T]]] =
      match List.splitFirst(c.items)
        case none() -> none
        case some(pair(h, t)) -> some(pair(h, cnt(t)))
  end
"#;

/// `first` peels a `Cnt` of `Buf`s at `N = {elem}` through `Stream.splitFirst`.
fn cnt_first(elem: &str) -> String {
    format!(
        "{CNT}\n  operation first[R](x: Cnt[T = Buf[T = Int64, N = {elem}], EC = R]) -> Int64 \
         effects R =\n    \
         match Stream.splitFirst(x)\n      \
         case some(pair(b, _)) -> val(b)\n      \
         case none() -> 0\n"
    )
}

/// Refused on BOTH twins before ("expected Buf[T = Int64, N = Bool], got c.T").
#[test]
fn the_fallback_eliminates_the_overrides_projection() {
    runs_as_its_twin("wi0rp29.fallback", 7, |n| {
        format!(
            "{}  operation go() -> Int64 =\n    \
             let c: Cnt[T = Buf[T = Int64, N = {n}], EC = {{}}] = cnt(cons(buf(v: 7), nil))\n    \
             first(c)",
            cnt_first(n)
        )
    });
}

/// THE FALLBACK'S CONTROL: `c.T` grounds to the element the receiver holds — at `N = 4`,
/// handed to `val` at `N = 3`, it is refused naming both.
#[test]
fn a_wrong_value_through_the_fallback_is_refused() {
    assert_refused_naming(
        &load_errors(&program("wi0rp29.fallback_other", "3", &cnt_first("4"))),
        &["Buf[T = Int64, N = 3]", "Buf[T = Int64, N = 4]"],
        "an element at N = 4 through the fallback, where val takes N = 3",
    );
}

/// THE STDLIB'S OWN FALLBACK over a carrier written with its SORT PARAMETERS
/// (`MappedStream.splitFirst -> Option[Pair[A = T, …]]`), on a receiver whose `E` is left to
/// its slot: the override's `T` is tied to the receiver, whose own `T` is the caller's. Refused
/// "MappedStream has no member 'E'" when the fallback eliminated after σ had put the caller's
/// projection into the type.
#[test]
fn the_fallback_over_a_carrier_written_with_its_parameters() {
    let src = r#"
namespace wi0rp29.mapped
  import anthill.prelude.{Int64, List, Option, Pair, Stream, MappedStream}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}

  operation g[EP](s: Stream[T = Int64], f: (x: Int64) -> Int64 @ {EP}) -> Int64 effects {s.E, EP} =
    match Stream.splitFirst(MappedStream.map(s, f))
      case some(pair(h, _)) -> h
      case none() -> 0

  operation go() -> Int64 =
    let xs: List[T = Int64] = cons(3, nil)
    g(xs, lambda (x: Int64) -> x + 4)
end
"#;
    assert_eq!(run_src(src, "wi0rp29.mapped.go"), Ok(7));
}

/// `Sp.pick(x: T, s: Sp)` — the receiver SECOND, the spec operation's body `spec_body` (empty,
/// or a default) — and a carrier `Car` whose override is `pick_decl`, called as `call` from
/// `use`: `a` holds `first` (its element type and value), `b` holds `second`. `use` answers the
/// picked element plus one.
fn car_program(
    ns: &str,
    spec_body: &str,
    pick_decl: &str,
    call: &str,
    first: (&str, &str),
    second: (&str, &str),
) -> String {
    let ((first, first_v), (second, second_v)) = (first, second);
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, Pair, String, List}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}

  sort Sp
    sort T = ?
    effects E = ?
    operation pick(x: T, s: Sp) -> Option[T = Pair[A = s.T, B = Sp[T = s.T, E = s.E]]] effects s.E{spec_body}
  end

  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = Car[V = ?, EC = ?], E = {{EC}}]
    {pick_decl}
  end

  operation use[R](a: Car[V = {first}, EC = R], b: Car[V = {second}, EC = R]) -> Int64 effects {{R}} =
    match {call}
      case some(pair(v, _)) -> v.v + 1
      case none() -> 0

  operation go() -> Int64 =
    let a: Car[V = {first}, EC = {{}}] = car(v: {first_v})
    let b: Car[V = {second}, EC = {{}}] = car(v: {second_v})
    use(a, b)
end
"#
    )
}

/// Both parameters are the bare carrier: inside `sort Car` each is THIS instance (the
/// parametricity tie), so the member demands ONE `V` across them where the spec's `x: T` (`T
/// = Car[V = ?, EC = ?]`, an independent instance WRITTEN — a bare `T = Car` is this instance
/// too since the seventh pass) is any instance.
const TIED_PICK: &str = "operation pick(x: Car, s: Car) -> Option[T = Pair[A = Car[V = x.V, EC = \
                         EC], B = Car[V = x.V, EC = EC]]] effects {EC} = some(pair(x, x))";

/// `x` with type arguments of its own — `W` and `R`, which the first argument alone binds; the
/// receiver `s` is the instance.
const OWN_PARAM_PICK: &str = "operation pick[W, R](x: Car[V = W, EC = R], s: Car) -> Option[T = \
                              Pair[A = Car[V = W, EC = R], B = Car[V = V, EC = EC]]] effects {EC} = \
                              some(pair(x, s))";

/// … with `A = x.V`, off the FIRST parameter — which the receiver is not — read through that
/// argument's own type (δ).
const PROJECTING_PICK: &str = "operation pick[W, R](x: Car[V = W, EC = R], s: Car) -> Option[T = \
                               Pair[A = Car[V = x.V, EC = R], B = Car[V = V, EC = EC]]] effects \
                               {EC} = some(pair(x, s))";

/// A MEMBER NARROWER THAN ITS SPEC IS REFUSED WHERE IT IS DECLARED: `pick(x: Car, s: Car)`
/// ties `x` to the receiver where `Sp.pick` lets them differ, so a call written against the
/// spec could hand it two instances its own signature refuses. It loaded, and a consistent
/// call ran; a conflicting one was refused only if it happened to take the WI-606 fallback.
#[test]
fn a_member_tied_tighter_than_its_spec_is_refused() {
    assert_refused_naming(
        &load_errors(&car_program(
            "wi0rp29.tied",
            "",
            TIED_PICK,
            "Sp.pick(a, b)",
            ("Int64", "41"),
            ("Int64", "99"),
        )),
        &[
            "does not fit",
            "parameter 1 (`x: Car`) takes less than the spec's",
            "THIS instance",
        ],
        "a member tying x to the receiver, where the spec's x is any Car",
    );
}

/// THE OVERRIDE'S PARAMETERS ARE KEYED BY POSITION: `x.V` is the first argument's `Int64`, and
/// the call runs. Keying the receiver's type to the first carrier-typed override parameter as
/// well took `x.V` off the SECOND argument (`String`) and refused this program.
#[test]
fn the_fallback_keys_the_override_by_position() {
    let ns = "wi0rp29.positional";
    assert_eq!(
        run_src(
            &car_program(
                ns,
                "",
                PROJECTING_PICK,
                "Sp.pick(a, b)",
                ("Int64", "41"),
                ("String", "\"str\"")
            ),
            &format!("{ns}.go")
        ),
        Ok(42)
    );
}

/// … AND ITS CONTROL: the first argument holds the `String`, so `v + 1` is refused at load.
/// Keyed by the receiver, it LOADED and failed at run time adding 1 to a `String`.
#[test]
fn the_fallback_keys_the_override_by_position_control() {
    assert_refused_naming(
        &load_errors(&car_program(
            "wi0rp29.positional_wrong",
            "",
            PROJECTING_PICK,
            "Sp.pick(a, b)",
            ("String", "\"str\""),
            ("Int64", "41"),
        )),
        &["expected String, got Int64"],
        "`v` is the first argument's String",
    );
}

/// AN OVERRIDE PARAMETER ONLY A NON-RECEIVER ARGUMENT BINDS: `W` is the first argument's
/// `String`, so `v + 1` is refused at load, as `Car.pick(a, b)` refuses it. Tying the receiver
/// alone left `A = ?W`, which the addition then read as `Int64`: the program LOADED and failed
/// at run time adding 1 to a `String`.
#[test]
fn an_overrides_own_type_parameter_is_bound_by_its_argument() {
    for (ns, call) in [
        ("wi0rp29.own_spec", "Sp.pick(a, b)"),
        ("wi0rp29.own_direct", "Car.pick(a, b)"),
    ] {
        assert_refused_naming(
            &load_errors(&car_program(
                ns,
                "",
                OWN_PARAM_PICK,
                call,
                ("String", "\"str\""),
                ("Int64", "41"),
            )),
            &["expected String, got Int64"],
            &format!("`{call}`: `v` is the first argument's String"),
        );
    }
}

/// … AND ITS CONTROL: the first argument holds the `Int64`, and the call runs — the member,
/// which gives `x` type arguments of its own, is no narrower than its spec, and no tie joins
/// `W` to the receiver's `V`. It guards the rows above against a declaration check or a σ that
/// refused by tying too much, and it passes with the declaration check backed out; with σ over
/// the receiver alone it fails, since `W` is then left unbound and the fallback declines.
#[test]
fn an_overrides_own_type_parameter_is_bound_by_its_argument_control() {
    let ns = "wi0rp29.own_ok";
    assert_eq!(
        run_src(
            &car_program(
                ns,
                "",
                OWN_PARAM_PICK,
                "Sp.pick(a, b)",
                ("Int64", "41"),
                ("String", "\"str\"")
            ),
            &format!("{ns}.go")
        ),
        Ok(42)
    );
}

/// `X` appears in the return and in no parameter: no argument can bind it.
const UNBOUND_PICK: &str = "operation pick[W, R, X](x: Car[V = W, EC = R], s: Car) -> Option[T = \
                            Pair[A = X, B = Car[V = V, EC = EC]]] effects {EC} = none";

/// AN OVERRIDE TYPE PARAMETER NO ARGUMENT BINDS IS NOT THREADED: `A = X` would reach `v + 1` as
/// `?X` and unify with anything, where `Car.pick(a, b)` is refused for it ("expected a type
/// for 'X', got unconstrained"). The fallback declines, and the call keeps the spec's own
/// refusal. It LOADED, threading `?X`.
#[test]
fn an_override_type_parameter_no_argument_binds_is_not_threaded() {
    let errs = load_errors(&car_program(
        "wi0rp29.unbound",
        "",
        UNBOUND_PICK,
        "Sp.pick(a, b)",
        ("Int64", "41"),
        ("Int64", "99"),
    ));
    assert_refused_naming(&errs, &["pick.return"], "the spec's own refusal of `s.E`");
}

/// A CONFLICT THROUGH THE FALLBACK IS REFUSED AS THE QUALIFIED CALL REFUSES IT. With a DEFAULTED
/// spec operation the member-fit check does not compare the member (WI-20260930-FB53M), so the
/// tied `pick(x: Car, s: Car)` loads — and `Sp.pick(a, b)` over a `Car` at `Int64` and one at
/// `String` binds `V` twice. The fallback runs the member, so the conflict is the call's error,
/// worded as `Car.pick(a, b)`'s. Declining left the spec's own unrelated refusal ("Car has no
/// member E"), and before that the member's first binding was threaded.
#[test]
fn a_conflict_through_the_fallback_is_refused_as_the_qualified_call_refuses_it() {
    let conflict =
        "consistent bindings for the sort's shared type parameter (first bound to Int64)";
    for call in ["Sp.pick(a, b)", "Car.pick(a, b)"] {
        let errs = load_errors(&car_program(
            "wi0rp29.undecided",
            " = none",
            TIED_PICK,
            call,
            ("Int64", "41"),
            ("String", "\"str\""),
        ));
        assert_refused_naming(&errs, &[conflict, "got String"], call);
        assert!(
            !errs.iter().any(|e| e.contains("pick.return")),
            "{call}: the conflict, not the spec's `s.E`: {errs:#?}"
        );
    }
}

/// … AND ITS CONTROL: both at `Int64`, σ decides, and the member's return is threaded.
#[test]
fn a_conflict_through_the_fallback_is_refused_as_the_qualified_call_refuses_it_control() {
    let ns = "wi0rp29.decided";
    assert_eq!(
        run_src(
            &car_program(
                ns,
                " = none",
                TIED_PICK,
                "Sp.pick(a, b)",
                ("Int64", "41"),
                ("Int64", "99")
            ),
            &format!("{ns}.go")
        ),
        Ok(42)
    );
}

/// A RECEIVER PASSED BY NAME takes the fallback as a positional one does:
/// `Stream.splitFirst(s: x)`. The fallback read the receiver's type off the POSITIONAL
/// arguments, found none, and declined — the call kept the refusal the fallback exists to lift.
#[test]
fn a_receiver_passed_by_name() {
    runs_as_its_twin("wi0rp29.named", 7, |n| {
        format!(
            "{}  operation go() -> Int64 =\n    \
             let c: Cnt[T = Buf[T = Int64, N = {n}], EC = {{}}] = cnt(cons(buf(v: 7), nil))\n    \
             first(c)",
            cnt_first(n).replace("Stream.splitFirst(x)", "Stream.splitFirst(s: x)")
        )
    });
}

/// `touch`'s RETURN eliminates (`s.T` is the receiver's `Int64`) and only its EFFECT does not
/// (`s.E` over the row parameter `R`, a non-ground row, WI-484). `Car2` holds `elem`.
fn effects_only_program(ns: &str, elem: &str, value: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, String}}
  import anthill.prelude.Option.{{some, none}}

  sort Sp2
    sort T = ?
    effects E = ?
    operation touch(s: Sp2) -> Option[T = s.T] effects {{s.E}}
  end

  sort Car2
    sort V = ?
    effects EC = ?
    entity car2(v: V)
    provides Sp2[T = V, E = {{EC}}]
    operation touch(c: Car2) -> Option[T = V] effects {{EC}} = some(c.v)
  end

  operation use[R](x: Car2[V = {elem}, EC = R]) -> Int64 effects {{R}} =
    match Sp2.touch(x)
      case some(v) -> v
      case none() -> 0

  operation go() -> Int64 =
    let c: Car2[V = {elem}, EC = {{}}] = car2(v: {value})
    use(c)
end
"#
    )
}

/// AN EFFECT THAT DOES NOT ELIMINATE ARMS THE FALLBACK as a return does. Only the return's
/// failure did, and the effect's was the call's refusal.
#[test]
fn an_effect_that_does_not_eliminate_takes_the_fallback() {
    let ns = "wi0rp29.eff_only";
    assert_eq!(
        run_src(&effects_only_program(ns, "Int64", "7"), &format!("{ns}.go")),
        Ok(7)
    );
}

/// … AND ITS CONTROL: what the fallback threads is the override's element — at `String`,
/// answered where `use` returns `Int64`, it is refused naming both. A threaded wildcard would
/// load this.
#[test]
fn an_effect_that_does_not_eliminate_takes_the_fallback_control() {
    assert_refused_naming(
        &load_errors(&effects_only_program(
            "wi0rp29.eff_only_str",
            "String",
            "\"s\"",
        )),
        &["expected Int64, got String"],
        "a String element threaded where use answers Int64",
    );
}

/// `Car.pick3`, whose return names its FIRST parameter in `Modify[a]` beside `A = {a_type}`,
/// calls `Sp.pick3(b, a, s)` — its own `a` and `b` swapped: the call binds the override's `a`
/// to its own `b`. (`a` and `b` share `W`/`R` as the spec's two `T`-typed parameters share
/// `T`, so the member is no narrower than its spec.) The call's type is PRINTED by the
/// annotation it does not meet.
///
/// A LOAD VERDICT BY CONSTRUCTION, as [`a_guard_survives_the_rebuild`] is: which parameter the
/// threaded `Modify` names is decided at load, and the refusal is how it reaches a string.
fn rotated_self_call(ns: &str, a_type: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, Pair, String, List, Modify}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}

  sort Sp
    sort T = ?
    effects E = ?
    operation pick3(a: T, b: T, s: Sp) -> Option[T = Pair[A = s.T, B = Sp[T = s.T, E = s.E]]] effects s.E
  end

  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = Car[V = ?, EC = ?], E = {{EC}}]
    operation pick3[W, R](a: Car[V = W, EC = R], b: Car[V = W, EC = R], s: Car) -> Option[T = Pair[A = {a_type}, B = Car[V = V, EC = {{Modify[a]}}]]] effects {{EC}} =
      let r: Int64 = Sp.pick3(b, a, s)
      none
  end
end
"#
    )
}

/// THE FALLBACK RE-KEYS A `denoted` ONCE: the override's `Modify[a]` is the caller's
/// `Modify[b]`, with a projection beside it (`A = a.V`) as without one (`A = W`). The
/// elimination re-keyed the projection-bearing return and the fallback re-keyed it again, so
/// the swap ran twice and the call's type said `Modify[a]`. The two twins guard the two halves
/// of "once": the projection twin fails when the eliminated type is re-keyed AGAIN, the
/// projection-free twin when the direct re-key is DROPPED — each passes under the other's
/// back-out.
#[test]
fn a_rotated_self_call_is_rekeyed_once() {
    for (ns, a_type) in [("wi0rp29.rot_proj", "a.V"), ("wi0rp29.rot_plain", "W")] {
        assert_refused_naming(
            &load_errors(&rotated_self_call(ns, a_type)),
            &["expected Int64, got Option[", "EC = {Modify[T = b]}"],
            &format!("the rotated call's type, `A = {a_type}`"),
        );
    }
}

/// A RETURN THAT HOLDS NO PROJECTION IS RE-KEYED when another position of the op does:
/// `remix2`'s projection is its PARAMETER `k: s.T`, and its return's `Modify[p]` is the
/// caller's `q`. `u` declares `declared`.
///
/// A LOAD VERDICT: `Strm` has no constructor and `Producer` no instance.
fn remix_program(ns: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Modify, EffectsRuntime, Int64}}
  sort Strm
    sort T = ?
    effects E = ?
    operation obs(s: Strm) -> Bool effects s.E = true
  end
  sort Producer
    operation pure_stream(p: Producer) -> Strm[T = Int64, E = {{}}]
    operation remix2(s: Strm, k: s.T, p: Producer) -> Strm[T = Int64, E = {{Modify[p]}}]
  end
  operation u(p: Producer, q: Producer) -> Bool effects {{{declared}}} =
    Strm.obs(Producer.remix2(Producer.pure_stream(p), 1, q))
end
"#
    )
}

/// Declaring `Modify[q]` loads. The re-key was gated on the op holding no projection
/// ANYWHERE, so this return kept `remix2`'s own `p`: "undeclared effect: Modify[T = p]".
#[test]
fn a_return_beside_a_projected_parameter_is_rekeyed() {
    let errs = load_errors(&remix_program("wi0rp29.remix", "Modify[q]"));
    assert!(
        errs.is_empty(),
        "the caller declares the Modify it incurs: {errs:#?}"
    );
}

/// … AND ITS CONTROL: declaring the caller's `p` instead is refused, naming `q`. Unre-keyed,
/// the refusal named `p` — `remix2`'s.
#[test]
fn a_return_beside_a_projected_parameter_is_rekeyed_control() {
    assert_refused_naming(
        &load_errors(&remix_program("wi0rp29.remix_p", "Modify[p]")),
        &["undeclared effect", "Modify[T = q]"],
        "the incurred Modify names the caller's q",
    );
}

/// A MIXED CALL of a spec op dispatched to an override: `Box.peek(p, q, x: 1)` binds the
/// override's `b` to `p` — the positional arguments rank among the parameters the label left
/// open — so its `Modify[b]` is `Modify[p]`. `use` declares `declared`. The member takes `c` as
/// any `Box`, as the spec's `c: Box` does (the declaration rule: a parameter the spec types by
/// itself, other than the receiver, is any provider).
fn mixed_call_program(ns: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Modify, EffectsRuntime, List, String}}

  sort Box
    effects Effect = ?
    operation peek(x: Int64, b: Box, c: Box) -> Int64 effects Effect
  end

  sort MutBox
    entity mb(fd: Int64)
    provides Box
    operation peek(x: Int64, b: MutBox, c: Box) -> Int64 effects Modify[b] =
      match b
        case mb(v) -> v
  end

  operation use(p: MutBox, q: MutBox) -> Int64 effects {{{declared}}} =
    Box.peek(p, q, x: 1)

  operation go() -> Int64 =
    let p = mb(fd: 10)
    let q = mb(fd: 20)
    use(p, q)
end
"#
    )
}

/// Declaring `Modify[p]` runs, and answers `p`'s 10. The dispatched effect was re-keyed to
/// the positional argument at the parameter's INDEX — `q` — which refused this program.
#[test]
fn a_mixed_calls_override_effect_names_its_argument() {
    let ns = "wi0rp29.mixed";
    assert_eq!(
        run_src(&mixed_call_program(ns, "Modify[p]"), &format!("{ns}.go")),
        Ok(10)
    );
}

/// … AND ITS CONTROL: declaring `Modify[q]` is refused, naming `p`. It LOADED, the effect
/// the call incurs undeclared.
#[test]
fn a_mixed_calls_override_effect_names_its_argument_control() {
    assert_refused_naming(
        &load_errors(&mixed_call_program("wi0rp29.mixed_q", "Modify[q]")),
        &["undeclared effect", "Modify[T = p]"],
        "the incurred Modify names p, the argument the call binds to b",
    );
}

/// An override's `Modify[c]` names ITS OWN parameter; the call incurs it on the caller's
/// argument `x`. `first` declares `declared`.
///
/// A LOAD VERDICT: the question is which parameter the incurred `Modify` names, and it is
/// decided at load; a run would need a place for `x` to modify.
fn rekey_program(ns: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, List, Option, Pair, Stream, Modify}}
  import anthill.prelude.List.{{cons, nil}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}

  sort Cnt
    sort T = ?
    effects EC = ?
    entity cnt(items: List[T])
    provides Stream[T = T, E = {{EC}}]
    operation splitFirst(c: Cnt) -> Option[Pair[A = T, B = Cnt[T = T, EC = {{Modify[c]}}]]] effects {{EC}} =
      match List.splitFirst(c.items)
        case none() -> none
        case some(pair(h, t)) -> some(pair(h, cnt(t)))
  end

  operation first[R](x: Cnt[T = Int64, EC = R]) -> Int64 effects {{{declared}}} =
    match Stream.splitFirst(x)
      case none() -> 0
      case some(pair(_, rest)) ->
        match Stream.splitFirst(rest)
          case some(pair(b, _)) -> b
          case none() -> 0
end
"#
    )
}

/// Declaring `Modify[x]` loads: the override's `c` is re-keyed to the caller's `x`. It was
/// refused "undeclared effect: Modify[T = c]" — the override's own parameter — wherever no
/// projection shared its type.
#[test]
fn an_overrides_own_parameter_is_rekeyed() {
    let errs = load_errors(&rekey_program("wi0rp29.rekey", "R, Modify[x]"));
    assert!(
        errs.is_empty(),
        "the caller declares the Modify it incurs: {errs:#?}"
    );
}

/// … AND ITS CONTROL: without `Modify[x]` it is refused, naming `x`.
#[test]
fn an_overrides_own_parameter_is_rekeyed_control() {
    assert_refused_naming(
        &load_errors(&rekey_program("wi0rp29.rekey_short", "R")),
        &["undeclared effect", "Modify[T = x]"],
        "the incurred Modify names the caller's x",
    );
}

// ── what the rebuilt forms reach ──────────────────────────────────────────────────────

/// AN ENTITY-CARRIED NAMED TUPLE IS REBUILT: σ splices the value-holding element into
/// `wrapt`'s `(e: A, n: Int64)` as an entity spine, and `unboxOpt`'s `b.T` grounds to it.
/// Only a sort application was rebuilt, so the value twin was refused "entity-carried value
/// that is not a sort application" while its `N = Bool` twin ran.
#[test]
fn an_entity_carried_tuple_is_rebuilt() {
    runs_as_its_twin("wi0rp29.ent_tuple", 8, |n| {
        format!(
            "  operation unboxOpt(b: Box) -> Option[T = b.T] = some(b.item)\n  \
             operation wrapt[A](x: A) -> Box[T = (e: A, n: Int64)] = box((e: x, n: 1))\n  \
             operation first(x: Buf[T = Int64, N = {n}]) -> Int64 =\n    \
             match unboxOpt(wrapt(x))\n      \
             case some((e, k)) -> val(e) + k\n      \
             case none() -> 0\n  \
             operation go() -> Int64 = first(buf(v: 7))"
        )
    });
}

/// … and an ENTITY-CARRIED ARROW, `(u: Int64) -> A`.
#[test]
fn an_entity_carried_arrow_is_rebuilt() {
    runs_as_its_twin("wi0rp29.ent_arrow", 7, |n| {
        format!(
            "  operation unboxOpt(b: Box) -> Option[T = b.T] = some(b.item)\n  \
             operation wrapf[A](x: A) -> Box[T = (u: Int64) -> A] = box(lambda (u: Int64) -> x)\n  \
             operation first(x: Buf[T = Int64, N = {n}]) -> Int64 =\n    \
             match unboxOpt(wrapf(x))\n      \
             case some(f) -> val(f(0))\n      \
             case none() -> 0\n  \
             operation go() -> Int64 = first(buf(v: 7))"
        )
    });
}

/// `wrap`'s return row `{Error[s.Fault]}`, rebuilt as an occurrence, binds `Cnt`'s `EC` — and
/// `Cnt provides Stream[T = T, E = {EC}]` then grounds `Stream.tail`'s `s.E` to an entity row
/// around it. NO VALUE IN ANY TYPE: `declare` is what the program declares.
fn carrier_row_program(ns: &str, declare: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, Pair, String, List, Error, Stream, EmptyStream}}
  import anthill.prelude.List.{{cons, nil}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}

  sort Src
    sort T = ?
    sort Fault = ?
    entity src(v: T)
  end

  sort Cnt
    sort T = ?
    effects EC = ?
    entity cnt(items: List[T])
    provides Stream[T = T, E = {{EC}}]
    operation splitFirst(c: Cnt) -> Option[Pair[A = T, B = Cnt[T = T, EC = EC]]] =
      match List.splitFirst(c.items)
        case none() -> none
        case some(pair(h, t)) -> some(pair(h, cnt(t)))
  end

  operation wrap(s: Src) -> Cnt[T = s.T, EC = {{Error[s.Fault]}}] =
    cnt(cons(s.v, cons(s.v, nil)))

  operation viaTail(s: Src[T = Int64, Fault = EmptyStream]) -> Int64{declare} =
    match Stream.splitFirst(Stream.tail(wrap(s)))
      case some(pair(h, _)) -> h + 1
      case none() -> 0

  operation viaSplit(s: Src[T = Int64, Fault = EmptyStream]) -> Int64{declare} =
    match Stream.splitFirst(wrap(s))
      case some(pair(h, _)) -> h + 1
      case none() -> 0

  operation go() -> Int64{declare} =
    let s: Src[T = Int64, Fault = EmptyStream] = src(v: 41)
    viaTail(s) + viaSplit(s) - 42
end
"#
    )
}

/// A ROW REBUILT AS AN OCCURRENCE GROUNDS A CARRIER'S ROW: declaring the row the calls incur,
/// both run. A program with no value in any type, refused ("entity-carried value that is not
/// a sort application") where the parent commit ran it — a closed rebuilt row was a term then.
#[test]
fn a_rebuilt_row_grounds_a_carriers_row() {
    let ns = "wi0rp29.carrier_row";
    assert_eq!(
        run_src(
            &carrier_row_program(ns, " effects {Error[EmptyStream]}"),
            &format!("{ns}.go")
        ),
        Ok(42)
    );
}

/// … AND THE ROW IS COUNTED: declaring nothing is refused, for both calls. Where the carrier
/// overrides `splitFirst`, the refusal above armed the WI-606 fallback, which threaded the
/// override's empty row: `viaSplit` LOADED with its `Error[EmptyStream]` undeclared while the
/// same value, annotated with its own type, was refused.
#[test]
fn a_rebuilt_row_grounds_a_carriers_row_control() {
    let errs = load_errors(&carrier_row_program("wi0rp29.carrier_row_pure", ""));
    for op in ["viaTail.effects", "viaSplit.effects"] {
        assert_refused_naming(
            &errs,
            &[op, "Error[T = EmptyStream]"],
            &format!("{op}: the row the call incurs, undeclared"),
        );
    }
}

/// `mk`'s `B = (x: s.K) -> Int64` is the SAME arrow for a `cat` source and a `dog` one, rebuilt
/// as an occurrence; `A` joins to `Animal`. `pick` is how the two meet.
fn join_program(ns: &str, pick: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, List, Option, Pair, String}}
  import anthill.prelude.Pair.{{pair}}
  import anthill.prelude.List.{{cons, nil}}

  sort Animal
    entity cat(n: Int64)
    entity dog(n: Int64)
  end

  sort Src
    sort T = ?
    sort K = ?
    entity src(v: T, k: K)
  end

  operation mk(s: Src) -> Pair[A = s.T, B = (x: s.K) -> Int64] = pair(s.v, lambda x -> 1)

  operation catSrc() -> Src[T = cat, K = Int64] =
    let c: cat = cat(n: 1)
    src(v: c, k: 5)
  operation dogSrc() -> Src[T = dog, K = Int64] =
    let d: dog = dog(n: 2)
    src(v: d, k: 6)

  operation go() -> Int64 =
{pick}
end
"#
    )
}

/// TWO BRANCHES CARRYING ONE REBUILT ARROW JOIN — through an `if` and through a list literal.
/// The same-base join combined term bindings only, and bailed on the occurrence-carried arrow:
/// "expected Pair[A = cat, B = Int64 -> Int64], got Pair[A = dog, …]", where the pre-ticket
/// tree ran both (1, and a list of 2).
#[test]
fn two_branches_carrying_one_rebuilt_arrow_join() {
    let if_arm = "    let r = if true then mk(catSrc()) else mk(dogSrc())\n    \
                  match r\n      case pair(_, f) -> f(3)";
    let list = "    let xs = [mk(catSrc()), mk(dogSrc())]\n    List.length(xs)";
    for (ns, pick, want) in [
        ("wi0rp29.join_if", if_arm, 1),
        ("wi0rp29.join_list", list, 2),
    ] {
        assert_eq!(
            run_src(&join_program(ns, pick), &format!("{ns}.go")),
            Ok(want),
            "{ns}"
        );
    }
}

/// `relay`'s `E = {s.E, Error[EmptyStream]}` over a stream whose `E` is `{Error[Foo]}`, handed
/// to a parameter / an annotation spelling the row the signature denotes. `row` is that
/// spelling.
fn row_atom_program(ns: &str, row: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Modify, EffectsRuntime, Int64, Error, EmptyStream}}
  sort Foo
    entity foo
  end
  sort Strm
    sort T = ?
    effects E = ?
    operation obs(s: Strm) -> Bool effects s.E = true
  end
  sort Producer
    operation foo_stream(p: Producer) -> Strm[T = Int64, E = {{Error[Foo]}}]
    operation relay(s: Strm) -> Strm[T = s.T, E = {{s.E, Error[EmptyStream]}}]
  end
  operation take(s: Strm[T = Int64, E = {row}]) -> Bool effects {row} =
    Strm.obs(s)
  operation viaParam(p: Producer) -> Bool effects {row} =
    take(Producer.relay(Producer.foo_stream(p)))
  operation viaLet(p: Producer) -> Bool effects {row} =
    let r: Strm[T = Int64, E = {row}] = Producer.relay(Producer.foo_stream(p))
    Strm.obs(r)
end
"#
    )
}

/// A PROJECTION WRITTEN AS A ROW ATOM IS SPLICED: `{s.E, Error[EmptyStream]}` folds as
/// `present(label: s.E)`, and `s.E` grounds to the row `{Error[Foo]}`, which now stands where
/// the atom stood. Kept as the label it nested a row in a row — `{Error[EmptyStream],
/// {Error[Foo]}}` — which unification does not flatten, and both spellings were refused.
/// A LOAD VERDICT: `Strm` has no constructor and `Producer` no instance.
#[test]
fn a_projection_written_as_a_row_atom_is_spliced() {
    let errs = load_errors(&row_atom_program(
        "wi0rp29.row_atom",
        "{Error[Foo], Error[EmptyStream]}",
    ));
    assert!(
        errs.is_empty(),
        "the flat row the signature denotes: {errs:#?}"
    );
}

/// … AND ITS CONTROL: a row missing `Error[Foo]` is still refused, naming it. Passes either
/// way by design — the nested row names `Error[Foo]` too — and guards the splice against
/// dropping the label it lifts.
#[test]
fn a_projection_written_as_a_row_atom_is_spliced_control() {
    assert_refused_naming(
        &load_errors(&row_atom_program(
            "wi0rp29.row_atom_short",
            "{Error[EmptyStream]}",
        )),
        &["Error[T = Foo]"],
        "the spliced row carries Error[Foo]",
    );
}

/// A MEMBER OF ANOTHER ARITY IS NOT THREADED: beside a DEFAULTED spec operation the member-fit
/// check does not compare `Car.peek(s: Car, k: String)` with `Sp.peek(s: Sp)`, and the fallback
/// paired them by position, silently dropping `k` — threading a return (`A = String`) of a
/// member the call cannot run. It declines, and the call keeps the spec's own refusal.
#[test]
fn a_member_of_another_arity_is_not_threaded() {
    let src = r#"
namespace wi0rp29.arity
  import anthill.prelude.{Int64, Bool, Option, Pair, String, List}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}

  sort Sp
    sort T = ?
    effects E = ?
    operation peek(s: Sp) -> Option[T = Pair[A = s.T, B = Sp[T = s.T, E = s.E]]] effects s.E = none
  end

  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = V, E = {EC}]
    operation peek(s: Car, k: String) -> Option[T = Pair[A = String, B = Car[V = V, EC = EC]]] effects {EC} = some(pair(k, s))
  end

  operation use[R](a: Car[V = Int64, EC = R]) -> Int64 effects {R} =
    let r: Int64 = Sp.peek(a)
    0
end
"#;
    let errs = load_errors(src);
    assert_refused_naming(&errs, &["peek.return"], "the spec's own refusal of `s.E`");
    assert!(
        !errs.iter().any(|e| e.contains("A = String")),
        "nothing threaded from the two-parameter member: {errs:#?}"
    );
}

/// A POSITIONAL TUPLE AND A VALUE-IN-TYPE PRINT AS THEIR TERM TWIN DOES: `(b.T, Int64)` over the
/// value-holding element is an occurrence, and it printed `(_1: …, _2: …)` with `N =
/// denoted(3)`, where the same type on the term carrier prints `(…, Int64)` and a type's
/// argument as its value. Printed as [`a_guard_survives_the_rebuild`] prints.
#[test]
fn a_positional_tuple_and_a_value_print_as_their_term_twin() {
    let src = r#"
namespace wi0rp29.print_tuple
  import anthill.prelude.{Int64, String, List, Bool, Error, Option}
  import anthill.prelude.Option.{some, none}
  import anthill.reflect.{NodeOccurrence, occurrence_type, term_to_string}

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end

  sort Box
    sort T = ?
    entity box(item: T)
  end

  operation mk(b: Box) -> Option[T = (b.T, Int64)] = none

  operation chk(x: NodeOccurrence) -> NodeOccurrence effects {Error[String]} =
    match occurrence_type(x)
      case some(t) -> Error.raise(term_to_string(t))
      case none() -> x

  operation trig[A](x: A) -> Int64 = 0
  rule trig(?x) <=> chk(?x) @[simp]

  operation go(x: Box[T = Buf[T = Int64, N = 3]]) -> Int64 = trig(mk(x))
end
"#;
    let errs = load_errors(src);
    assert_refused_naming(
        &errs,
        &["(Buf[T = Int64, N = 3], Int64)"],
        "the printed type of `mk(x)`, positional and valued",
    );
    assert!(
        !errs
            .iter()
            .any(|e| e.contains("_1:") || e.contains("denoted(")),
        "no positional label, no `denoted(`: {errs:#?}"
    );
}

// ── the fallback judges the call by the override it runs ─────────────────────

/// `Sp.put(s: Sp, k: s.T)` over `Car.put(c: Car, k: c.V)` at `provides Sp[T = {t}, E = {EC}]`:
/// at `T = List[T = V]` the member's `k` is an element where the spec's is a list. `use` passes
/// `ks: {ks_ty}`.
fn put_program(ns: &str, t: &str, ks_ty: &str, ks: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, List, Bool, Option, String}}
  import anthill.prelude.List.{{cons, nil}}
  import anthill.prelude.Option.{{some, none}}

  sort Sp
    sort T = ?
    effects E = ?
    operation put(s: Sp, k: s.T) -> Option[T = s.T] effects s.E
  end

  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = {t}, E = {{EC}}]
    operation put(c: Car, k: c.V) -> Option[T = c.V] effects {{EC}} = some(k)
  end

  operation use[R](x: Car[V = Int64, EC = R], ks: {ks_ty}) -> Int64 effects {{R}} =
    match Sp.put(x, ks)
      case some(v) -> v + 1
      case none() -> 0

  operation go() -> Int64 =
    let c: Car[V = Int64, EC = {{}}] = car(v: 1)
    use(c, {ks})
end
"#
    )
}

/// AN ARGUMENT THE OVERRIDE REFUSES IS REFUSED: the spec's `s.E` does not ground over `R`, the
/// fallback runs `Car.put`, and its `k: c.V` — an `Int64` here — refuses the list, as
/// `Car.put(x, ks)` does. The fallback discarded its unifier's `false`, the declaration checks
/// skipped a projection-typed parameter, and the program LOADED and died adding 1 to a list.
/// The declaration now refuses this member too (its `k` reads the instance's `V` where the
/// spec's `s.T` is a list — the member-rule file's projection rows); the fallback's own verdict
/// is asserted here, and the declaration's beside it does not hide it.
#[test]
fn an_argument_the_override_refuses_is_refused() {
    assert_refused_naming(
        &load_errors(&put_program(
            "wi0rp29.put",
            "List[T = V]",
            "List[T = Int64]",
            "cons(5, nil)",
        )),
        &["put.k (op-arg): expected Int64, got List[T = Int64]"],
        "the override's own parameter judges the argument",
    );
}

/// … AND ITS CONTROL: at `T = V` the spec's `k` and the member's agree, the fallback threads the
/// member's return, and the call runs to 5 + 1 — the validation refuses only what the member
/// refuses. Passes either way by design: it guards the validation against over-refusing.
#[test]
fn an_argument_the_override_refuses_is_refused_control() {
    let ns = "wi0rp29.put_ok";
    assert_eq!(
        run_src(&put_program(ns, "V", "Int64", "5"), &format!("{ns}.go")),
        Ok(6)
    );
}

/// TWO BARE FOREIGN PARAMETERS OF THE OVERRIDE ARE TWO: `Car.pick(x: List, y: List, s: Car)`
/// takes lists of two element types, as `Car.pick(xs, ys, a)` does (WI-374 expands each bare
/// `List` fresh). Unified as written, `xs: List[T = Int64]` and `ys: List[T = String]` bound
/// `List`'s one `T` twice, the fallback declined, and the call was refused with the spec's
/// unrelated "Car has no member E". Runs to 41 + 1.
#[test]
fn two_bare_foreign_parameters_of_the_override_are_two() {
    let ns = "wi0rp29.fvar";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, Pair, String, List}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}
  import anthill.prelude.List.{{cons, nil}}

  sort Sp
    sort T = ?
    effects E = ?
    operation pick(x: List, y: List, s: Sp) -> Option[T = Pair[A = s.T, B = Sp[T = s.T, E = s.E]]] effects s.E
  end

  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = V, E = {{EC}}]
    operation pick(x: List, y: List, s: Car) -> Option[T = Pair[A = V, B = Car[V = V, EC = EC]]] effects {{EC}} = some(pair(s.v, s))
  end

  operation use[R](a: Car[V = Int64, EC = R], xs: List[T = Int64], ys: List[T = String]) -> Int64 effects {{R}} =
    match Sp.pick(xs, ys, a)
      case some(pair(v, _)) -> v + 1
      case none() -> 0

  operation go() -> Int64 =
    let a: Car[V = Int64, EC = {{}}] = car(v: 41)
    use(a, cons(1, nil), cons("s", nil))
end
"#
    );
    assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(42));
}

// ── a join, a meet and a list over types holding a value ─────────────────────

/// `mk` answers the value-holding `Foo[…, N = {n}]`; `wrap` and `mkp` are generic, so their
/// answers carry it through σ (an entity-carried type, WI-477). `go` is `body`.
fn value_join_program(ns: &str, n: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, List, Option, Pair, String}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}
  import anthill.reflect.typing.{{Contravariant}}

  sort Animal
    entity cat(n: Int64)
    entity dog(n: Int64)
  end

  sort Foo
    sort T = ?
    sort N = ?
    entity foo(v: T)
  end

  sort Sink
    sort T = ?
    entity sink(n: Int64)
    fact Contravariant(sort: Sink, param: T)
  end

  operation mk(x: Int64) -> Foo[T = Int64, N = {n}] = foo(v: x)
  operation wrap[A](x: A) -> Option[T = A] = some(x)
  operation mkp[X, Y](x: X, y: Y) -> Pair[A = X, B = Y] = pair(x, y)
  operation mkSink[X](x: X) -> Sink[T = X] = sink(n: 1)

  operation go(b: Bool) -> Int64 =
    let c: cat = cat(n: 1)
    let d: dog = dog(n: 2)
{body}

  operation run() -> Int64 = go(true)
end
"#
    )
}

/// A JOIN OVER A TYPE HOLDING A VALUE IS ITS TWIN'S: the two branches' `Pair`s join at `Animal`,
/// their shared entity-carried `Option[T = Foo[…, N = 3]]` crossing unchanged. Handed to the
/// type builder un-rebuilt it PANICKED the loader ("expect_term: … got Value::Entity"), where
/// the pre-ticket tree loaded and ran this annotated program. Runs to 1, as the `N = Bool` twin
/// does (the loop's second program — passing either way by design, the control that the join
/// itself is sound).
#[test]
fn a_join_over_a_type_holding_a_value_is_its_twins() {
    let body = "    let r: Pair[A = Option[T = Foo[T = Int64, N = {n}]], B = Animal] = \
                if b then mkp(wrap(mk(1)), c) else mkp(wrap(mk(2)), d)\n    1";
    for (ns, n) in [("wi0rp29.join_v", "3"), ("wi0rp29.join_b", "Bool")] {
        let src = value_join_program(ns, n, &body.replace("{n}", n));
        assert_eq!(run_src(&src, &format!("{ns}.run")), Ok(1), "N = {n}");
    }
}

/// A MEET OVER A TYPE HOLDING A VALUE IS ITS TWIN'S: `Sink` is contravariant in `T`, so the two
/// branches' `Sink[T = Pair[…, B = cat]]` and `Sink[T = Pair[…, B = dog]]` combine by MEETING
/// their `T`s — the same builder, and the same panic, the pre-ticket tree loaded. The built type
/// is READ: a use of it as an `Int64` is refused naming exactly `Sink[T = Pair[A = Option[T =
/// Foo[T = Int64, N = …]], B = nothing]]`, and the program using it rightly runs to 1 — on the
/// value-in-type element and on its `N = Bool` twin (the loop's second, passing either way by
/// design).
#[test]
fn a_meet_over_a_type_holding_a_value_is_its_twins() {
    let meet =
        "    let r = if b then mkSink(mkp(wrap(mk(1)), c)) else mkSink(mkp(wrap(mk(2)), d))\n";
    for (ns, n) in [("wi0rp29.meet_v", "3"), ("wi0rp29.meet_b", "Bool")] {
        let src = value_join_program(ns, n, &format!("{meet}    let z: Int64 = r\n    z"));
        assert_refused_naming(
            &load_errors(&src),
            &[&format!(
                "expected Int64, got Sink[T = Pair[A = Option[T = Foo[T = Int64, N = {n}]], B = \
                 nothing]]"
            )],
            "the meet's type",
        );
        let src = value_join_program(ns, n, &format!("{meet}    1"));
        assert_eq!(run_src(&src, &format!("{ns}.run")), Ok(1), "N = {n}");
    }
}

/// A LIST LITERAL OVER A GENERIC CALL WHOSE ANSWER HOLDS A VALUE LOADS: its element type reaches
/// the same builder (WI-20260930-FZA6H's program), which PANICKED before and after the ticket
/// alike. The literal is NOT annotated — an annotation decides the element type itself, and the
/// built one never reaches the builder (the annotated twin ran on the pre-ticket build, MEASURED)
/// — and the built type is READ through a use: the head handed to an operation taking `Option[T
/// = Foo[T = Int64, N = …]]`, its `v` answered: 1, on both twins (the `N = Bool` one passing either
/// way by design).
#[test]
fn a_list_literal_over_a_type_holding_a_value_loads() {
    for (ns, n) in [("wi0rp29.listlit_v", "3"), ("wi0rp29.listlit_b", "Bool")] {
        let body = format!(
            "    let xs = [wrap(mk(1))]\n    \
             match List.headOption(xs)\n      case some(o) -> unwrapFoo(o)\n      \
             case none() -> 0\n  operation unwrapFoo(o: Option[T = Foo[T = Int64, N = {n}]]) -> \
             Int64 =\n    match o\n      case some(f) -> f.v\n      case none() -> 0"
        );
        let src = value_join_program(ns, n, &body);
        assert_eq!(run_src(&src, &format!("{ns}.run")), Ok(1), "N = {n}");
    }
}

// ── a guarded or absent atom that grounds to a row distributes over it ───────

/// `Strm.obs(s, d) effects {s.E :- eq(d, 0)}` over `E = {Error[Foo]}` at `d = 0` — the guard
/// holds — called by `use`, which declares `declared`.
fn guarded_row_program(ns: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Int64, Error}}
  import anthill.prelude.PartialEq.{{eq}}
  sort Foo
    entity foo
  end
  sort Strm
    sort T = ?
    effects E = ?
    operation obs(s: Strm, d: Int64) -> Bool effects {{s.E :- eq(d, 0)}} = true
  end
  operation use(s: Strm[T = Int64, E = {{Error[Foo]}}]) -> Bool{declared} = Strm.obs(s, 0)
end
"#
    )
}

/// A GUARDED ATOM THAT GROUNDS TO A ROW DISTRIBUTES OVER IT: `{s.E :- g}` is `{Error[Foo] :-
/// g}`, which `use` declares. Nested, it was the undeclared `{Error[T = Foo]}` — a row in a row.
/// A LOAD VERDICT: the incurred row is decided at load.
#[test]
fn a_guarded_atom_grounding_to_a_row_distributes_over_it() {
    let errs = load_errors(&guarded_row_program(
        "wi0rp29.grow",
        " effects {Error[Foo]}",
    ));
    assert!(errs.is_empty(), "the caller declares Error[Foo]: {errs:#?}");
}

/// … AND ITS CONTROL: a pure caller is refused, naming the ATOM (not a row holding it).
#[test]
fn a_guarded_atom_grounding_to_a_row_distributes_over_it_control() {
    let errs = load_errors(&guarded_row_program("wi0rp29.grow_pure", ""));
    assert_refused_naming(
        &errs,
        &["undeclared effect: Error[T = Foo]"],
        "the guard holds at 0",
    );
    assert!(
        !errs.iter().any(|e| e.contains("{Error[T = Foo]}")),
        "the atom, not a nested row: {errs:#?}"
    );
}

/// `Strm.each[EffP](s, f: (x: Int64) -> Bool @ {EffP, -s.E})` over `E = {Error[Foo]}`, called
/// with a lambda whose body is `lam`.
fn absent_row_program(ns: &str, lam: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Int64, Error}}
  sort Foo
    entity foo
  end
  sort Boom
    operation boom(x: Int64) -> Bool effects {{Error[Foo]}}
  end
  sort Strm
    sort T = ?
    effects E = ?
    operation each[EffP](s: Strm, f: (x: Int64) -> Bool @ {{EffP, -s.E}}) -> Bool effects {{EffP}} = true
  end
  operation use(s: Strm[T = Int64, E = {{Error[Foo]}}], b: Boom) -> Bool effects {{Error[Foo]}} =
    Strm.each(s, lambda (x: Int64) -> {lam})
end
"#
    )
}

/// AN ABSENT ATOM THAT GROUNDS TO A ROW DISTRIBUTES OVER IT: `-s.E` is `-Error[Foo]`, so a
/// callback raising `Error[Foo]` is refused, as `-Error[Foo]` written directly refuses it. Kept
/// as the absence of a ROW, it constrained nothing, and the lambda was admitted.
#[test]
fn an_absent_atom_grounding_to_a_row_distributes_over_it() {
    assert_refused_naming(
        &load_errors(&absent_row_program("wi0rp29.arow", "Boom.boom(x)")),
        &["to lack `Error[T = Foo]`"],
        "the callback raises what it must lack",
    );
}

/// … AND ITS CONTROL: a pure callback loads. Passes either way by design — a pure callback lacks
/// every effect, however the absence is read.
#[test]
fn an_absent_atom_grounding_to_a_row_distributes_over_it_control() {
    let errs = load_errors(&absent_row_program("wi0rp29.arow_ok", "true"));
    assert!(
        errs.is_empty(),
        "a pure callback lacks everything: {errs:#?}"
    );
}

// ── a row parameter inside braces, and a row-variable tail ───────────────────

/// `Car provides Strm[T = V, E = {EC}]` — the provision writes the carrier's row parameter
/// INSIDE braces, which the loader holds as `open(EC)` — and `probe` over a `Car[…, EC =
/// {ec}]` with `body`, it and `go` declaring `declared`.
fn braced_row_program(ns: &str, ec: &str, declared: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Int64, Error, List, String}}
  import anthill.prelude.PartialEq.{{eq}}
  sort Foo
    entity foo
  end
  sort Strm
    sort T = ?
    effects E = ?
    operation obs(s: Strm, d: Int64) -> Bool effects {{s.E :- eq(d, 0)}} = true
    operation each[EffP](s: Strm, f: (x: Int64) -> Bool @ {{EffP, -s.E}}) -> Bool effects {{EffP}} = true
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Strm[T = V, E = {{EC}}]
  end
  operation probe(c: Car[V = Int64, EC = {{{ec}}}]) -> Bool{declared} = {body}
  operation go() -> Int64{declared} =
    let c: Car[V = Int64, EC = {{{ec}}}] = car(v: 1)
    if probe(c) then 7 else 0
end
"#
    )
}

/// A GUARDED OR ABSENT ATOM OVER A BRACED ROW PARAMETER DISTRIBUTES: `s.E` grounds to `{ {} }`
/// — a tail bound to the empty row — and a refuted guard over it incurs nothing, as a pure
/// callback lacks it. Every open tail was refused ("a guarded or absent effect grounded to a row
/// with an open tail"), though the pre-ticket tree ran both, as it runs the unbraced `E = EC`.
/// Each runs to 7.
#[test]
fn a_guarded_atom_over_a_braced_row_parameter_distributes() {
    for (tag, body) in [
        ("refuted", "Strm.obs(c, 1)"),
        ("pure", "Strm.each(c, lambda (x: Int64) -> true)"),
    ] {
        let ns = format!("wi0rp29.braced_{tag}");
        let src = braced_row_program(&ns, "", "", body);
        assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(7), "{tag}");
    }
}

/// … AND A GUARD THAT HOLDS INCURS THE TAIL'S ROW: at `EC = {Error[Foo]}`, `Strm.obs(c, 0)` incurs
/// `Error[Foo]` — loads declaring it, refused naming it otherwise. (Before the distribution the
/// nested `{ {Error[Foo]} }` was refused even where declared, on both binaries.)
#[test]
fn a_guard_that_holds_over_a_braced_row_parameter_incurs_its_row() {
    let declared = braced_row_program(
        "wi0rp29.braced_holds",
        "Error[Foo]",
        " effects {Error[Foo]}",
        "Strm.obs(c, 0)",
    );
    assert_eq!(crate::common::try_load_kb_with(&declared).err(), None);
    let undeclared =
        braced_row_program("wi0rp29.braced_holds_u", "Error[Foo]", "", "Strm.obs(c, 0)");
    assert_refused_naming(
        &load_errors(&undeclared),
        &["got undeclared effect: Error[T = Foo]"],
        "the tail's row, incurred",
    );
}

/// A GUARDED ATOM OVER A ROW-VARIABLE TAIL PLACES THE VARIABLE: over `s: Strm[E = {Error[Foo],
/// R}]` the guard distributes to `Error[Foo] :- g` and `R :- g`, as `E = R` builds `R :- g`. A
/// refuted guard incurs nothing, and one that holds incurs `R`, refused naming `?R` where the
/// caller declares only `Error[Foo]`. The open tail was refused outright.
#[test]
fn a_guarded_atom_over_a_row_variable_tail_places_the_variable() {
    let program = |ns: &str, d: &str, declared: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Bool, Int64, Error}}
  import anthill.prelude.PartialEq.{{eq}}
  sort Foo
    entity foo
  end
  sort Strm
    sort T = ?
    effects E = ?
    operation obs(s: Strm, d: Int64) -> Bool effects {{s.E :- eq(d, 0)}} = true
  end
  operation use[R](s: Strm[T = Int64, E = {{Error[Foo], R}}]) -> Bool effects {{{declared}}} = Strm.obs(s, {d})
end
"#
        )
    };
    assert_eq!(
        crate::common::try_load_kb_with(&program("wi0rp29.rvtail_r", "1", "Error[Foo], R")).err(),
        None
    );
    assert_refused_naming(
        &load_errors(&program("wi0rp29.rvtail_h", "0", "Error[Foo]")),
        &["got undeclared effect: ?R"],
        "the tail variable, incurred",
    );
}

/// … AND THE STDLIB'S OWN BRACED ROWS: `MappedStream provides Stream[E = {ES, EF}]`, so a
/// refuted `s.E :- eq(d, 0)` over a `MappedStream[…, ES = {}, EF = {}]` meets two bound tails.
/// Refused the same way; runs to 7.
#[test]
fn a_guarded_atom_over_the_stdlib_mapped_stream_distributes() {
    let ns = "wi0rp29.mapped";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Int64, List, String, Stream, MappedStream}}
  import anthill.prelude.MappedStream.{{mapped}}
  import anthill.prelude.PartialEq.{{eq}}
  operation inc(x: Int64) -> Int64 = x + 1
  operation obs(s: Stream, d: Int64) -> Bool effects {{s.E :- eq(d, 0)}} = true
  operation mk(xs: List[T = Int64])
    -> MappedStream[Source = List[T = Int64], Src = Int64, T = Int64, ES = {{}}, EF = {{}}] =
    mapped(xs, inc)
  operation probe(m: MappedStream[Source = List[T = Int64], Src = Int64, T = Int64, ES = {{}}, EF = {{}}]) -> Bool =
    obs(m, 1)
  operation go() -> Int64 =
    let xs: List[T = Int64] = [1, 2, 3]
    if probe(mk(xs)) then 7 else 0
end
"#
    );
    assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(7));
}

// ── the override's own type parameters, as the call binds them ────────────────

/// AN OVERRIDE'S OWN TYPE PARAMETER BOUND TWICE TAKES THE JOIN: `Car.op[W](c, a: W, b: W)
/// effects {Error[W]}` behind `Sp.op[U](s, a: U, b: U)` over a cat and a dog charges
/// `Error[Animal]` — the join the call made of `U`, and what `Car.op(x, c1, d1)` charges. Bound
/// from the raw arguments, the FIRST decided it: `Error[cat]` was charged, `via` declaring it
/// loaded, and the raised dog was read as a cat at run time (unsound); the swapped call charged
/// `Error[dog]`.
#[test]
fn an_overrides_own_type_parameter_bound_twice_takes_the_join() {
    for (tag, args) in [("cd", "c1, d1"), ("dc", "d1, c1")] {
        let src = own_join_program(&format!("wi0rp29.ownjoin_{tag}"), "cat", args);
        assert_refused_naming(
            &load_errors(&src),
            &["expected declared: [Error[T = cat]], got undeclared effect: Error[T = Animal]"],
            "the override's own parameter at the join",
        );
    }
}

/// … AND ITS CONTROL: `via` declaring `Error[Animal]` loads, either way round — the join must not
/// be refused. FAILS under ledger part 32 (from the raw arguments the cat and the dog conflict
/// on `W`, refused as the qualified call refuses a conflict), and failed on the tree the fifth
/// review saw, which charged `Error[cat]` (`Error[dog]` the other way round) — not admitted by
/// `Error[Animal]` (MEASURED: "got undeclared effect: Error[T = cat]").
#[test]
fn an_overrides_own_type_parameter_bound_twice_takes_the_join_control() {
    for (tag, args) in [("cd", "c1, d1"), ("dc", "d1, c1")] {
        let src = own_join_program(&format!("wi0rp29.ownjoin_ok_{tag}"), "Animal", args);
        assert_eq!(crate::common::try_load_kb_with(&src).err(), None, "{tag}");
    }
}

/// `Car.op[W](c, a: W, b: W) effects {Error[W]} = Error.raise(b)` behind `Sp.op[U](s, a: U, b:
/// U)`, and `via` — declaring `Error[declared]` — calling `Sp.op(x, args)` over a cat `c1` and
/// a dog `d1`.
fn own_join_program(ns: &str, declared: &str, args: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, String, Error, List}}
  sort Animal
    entity cat(n: Int64)
    entity dog(m: String)
  end
  sort Sp
    sort T = ?
    operation op[U](s: Sp, a: U, b: U) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation op[W](c: Car, a: W, b: W) -> Int64 effects {{Error[W]}} = Error.raise(b)
  end
  operation via(x: Car[V = Int64]) -> Int64 effects {{Error[{declared}]}} =
    let c1: cat = cat(n: 1)
    let d1: dog = dog(m: "woof")
    Sp.op(x, {args})
end
"#
    )
}

/// AN OVERRIDE'S OWN TYPE PARAMETER READS THE SPEC'S PARAMETER AT THE CALL: behind `op[U](s, a:
/// List[T = Int64], b: List[T = U], w: U)`, the override's `b: List[T = W]` relates `W` to `U`,
/// which the call binds to `String` (`w: "boom"`), so `Sp.op(x, nil, nil, "boom")` charges
/// `Error[String]`. Bound from the raw arguments, the two `nil`s shared `List`'s one `T`, `W`
/// took `a`'s `Int64`, and `via` declaring `Error[Int64]` loaded and raised the string at run
/// time (unsound). The control declares `Error[String]` and loads.
#[test]
fn an_overrides_own_type_parameter_reads_the_spec_parameter_at_the_call() {
    let program = |ns: &str, declared: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, String, Error, List}}
  import anthill.prelude.List.{{cons, nil}}
  sort Sp
    sort T = ?
    operation op[U](s: Sp, a: List[T = Int64], b: List[T = U], w: U) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation op[W](c: Car, a: List[T = Int64], b: List[T = W], w: W) -> Int64 effects {{Error[W]}} = Error.raise(w)
  end
  operation via(x: Car[V = Int64]) -> Int64 effects {{Error[{declared}]}} =
    Sp.op(x, nil, nil, "boom")
end
"#
        )
    };
    assert_refused_naming(
        &load_errors(&program("wi0rp29.ownchan", "Int64")),
        &["got undeclared effect: Error[T = String]"],
        "the override's own parameter through the spec's",
    );
    assert_eq!(
        crate::common::try_load_kb_with(&program("wi0rp29.ownchan_ok", "String")).err(),
        None,
        "declared as the call binds it"
    );
}

// ── the WI-606 fallback: the call's arguments, the spec's bracket ────────────

/// TWO `nil`S THROUGH THE FALLBACK ARE TWO LISTS: `Sp.op(x, nil, nil)` over `op(s, a: List[T =
/// Int64], b: List[T = String])` threads the override (`s.E` does not ground over `R`). Its σ
/// met the bare `List` of each `nil` with the override's parameters, and the two shared `List`'s
/// one `T`: refused "consistent bindings for the sort's shared type parameter (first bound to
/// Int64), got String", where `Car.op(x, nil, nil)` and the closed-row spelling ran. Runs to
/// 3 × 20.
#[test]
fn two_nils_through_the_fallback_are_two_lists() {
    let ns = "wi0rp29.nilnil";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, String, List}}
  import anthill.prelude.List.{{cons, nil}}
  import anthill.prelude.Option.{{some, none}}
  sort Sp
    sort T = ?
    effects E = ?
    operation op(s: Sp, a: List[T = Int64], b: List[T = String]) -> Option[T = s.T] effects s.E
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = V, E = {{EC}}]
    operation op(c: Car, a: List[T = Int64], b: List[T = String]) -> Option[T = V] effects {{EC}} = some(c.v)
  end
  operation use[R](x: Car[V = Int64, EC = R]) -> Int64 effects {{R}} =
    match Sp.op(x, nil, nil)
      case some(v) -> v
      case none() -> 0
  operation useq[R](x: Car[V = Int64, EC = R]) -> Int64 effects {{R}} =
    match Car.op(x, nil, nil)
      case some(v) -> v
      case none() -> 0
  operation usec(x: Car[V = Int64, EC = {{}}]) -> Int64 =
    match Sp.op(x, nil, nil)
      case some(v) -> v
      case none() -> 0
  operation go() -> Int64 =
    let c: Car[V = Int64, EC = {{}}] = car(v: 20)
    use(c) + useq(c) + usec(c)
end
"#
    );
    assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(60));
}

/// … AND NESTED BARE FOREIGN SORTS OF THE OVERRIDE ARE TWO: `p: Pair[A = List, B = List]` takes
/// a pair of lists of any two element types. Expanded at the top only, the fallback refused
/// `Sp.pick(a, b, pair(ints, strs))` naming "the sort's shared type parameter" — `List`'s `T`,
/// misnamed. Runs to 41 + 1.
#[test]
fn nested_bare_foreign_sorts_through_the_fallback_are_two() {
    let ns = "wi0rp29.fbnested";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, Pair, String, List}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}
  sort Sp
    sort T = ?
    effects E = ?
    operation pick(x: T, s: Sp, p: Pair[A = List, B = List]) -> Option[T = Pair[A = s.T, B = Sp[T = s.T, E = s.E]]] effects s.E = none
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = Car[V = ?, EC = ?], E = {{EC}}]
    operation pick[W, R](x: Car[V = W, EC = R], s: Car, p: Pair[A = List, B = List]) -> Option[T = Pair[A = W, B = Car[V = V, EC = EC]]] effects {{EC}} = some(pair(x.v, s))
  end
  operation use[R](a: Car[V = Int64, EC = R], b: Car[V = Int64, EC = R]) -> Int64 effects {{R}} =
    let xs: List[T = Int64] = [1]
    let ys: List[T = String] = ["s"]
    match Sp.pick(a, b, pair(xs, ys))
      case some(pair(v, _)) -> v + 1
      case none() -> 0
  operation go() -> Int64 =
    let a: Car[V = Int64, EC = {{}}] = car(v: 41)
    let b: Car[V = Int64, EC = {{}}] = car(v: 99)
    use(a, b)
end
"#
    );
    assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(42));
}

/// `pick2[W](x: T, s: Sp) -> Option[T = Pair[A = s.T, B = W]] effects s.E` and its override
/// (WI-20260930-JPSDH's program), `use` and `useq` calling it through the spec and through the
/// carrier with the bracket `[W = Int64]`, the result let-bound at `annotation` (`None`: matched
/// directly).
fn bracket_program(ns: &str, annotation: Option<&str>) -> String {
    let call = |q: &str| match annotation {
        Some(t) => format!("let r: {t} = {q}.pick2[W = Int64](a, b)\n    7"),
        None => format!(
            "match {q}.pick2[W = Int64](a, b)\n      case some(p) -> 1\n      case none() -> 7"
        ),
    };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, Pair, String, List}}
  import anthill.prelude.Option.{{some, none}}
  sort Sp
    sort T = ?
    effects E = ?
    operation pick2[W](x: T, s: Sp) -> Option[T = Pair[A = s.T, B = W]] effects s.E
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = Car, E = {{EC}}]
    operation pick2[W, U, R](x: Car[V = U, EC = R], s: Car) -> Option[T = Pair[A = Car[V = V, EC = EC], B = W]] effects {{EC}} = none
  end
  operation use[R](a: Car[V = Int64, EC = R], b: Car[V = Int64, EC = R]) -> Int64 effects {{R}} =
    {spec}
  operation useq[R](a: Car[V = Int64, EC = R], b: Car[V = Int64, EC = R]) -> Int64 effects {{R}} =
    {qual}
  operation go() -> Int64 =
    let a: Car[V = Int64, EC = {{}}] = car(v: 1)
    use(a, a) + useq(a, a)
end
"#,
        spec = call("Sp"),
        qual = call("Car"),
    )
}

/// A CALL-SITE BRACKET REACHES THE FALLBACK (WI-20260930-JPSDH): `Sp.pick2[W = Int64](a, b)`
/// threads the override, whose `W` only the bracket binds — related to the spec's `W` through
/// the two RETURN types, position by position, as the call binds the spec's. Built from the
/// arguments alone, the fallback's σ left `W` unbound and declined, so the call was refused
/// "Car has no member E" where `Car.pick2[W = Int64](a, b)` ran. Runs to 7 + 7.
#[test]
fn a_call_site_bracket_reaches_the_fallback() {
    let ns = "wi0rp29.bracket";
    assert_eq!(
        run_src(&bracket_program(ns, None), &format!("{ns}.go")),
        Ok(14)
    );
}

/// … AND A BRACKET THE USE CONTRADICTS IS REFUSED ON BOTH SPELLINGS: the result let-bound at `B
/// = String` against the bracket's `Int64` — through the fallback (`Sp`) as through the carrier
/// (`Car`). The first half — an ARGUMENT binding `W` to a `String` — is a CONTROL that passes
/// either way by design: the call's own argument check against the spec's `w: W` refuses it
/// before any return is eliminated, so the fallback is never reached.
#[test]
fn a_call_site_bracket_reaches_the_fallback_contradicted() {
    let by_argument = r#"
namespace wi0rp29.bracket_a
  import anthill.prelude.{Int64, Bool, Option, Pair, String, List}
  import anthill.prelude.Option.{some, none}
  sort Sp
    sort T = ?
    effects E = ?
    operation pick3[W](x: T, s: Sp, w: W) -> Option[T = Pair[A = s.T, B = W]] effects s.E
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = Car, E = {EC}]
    operation pick3[W, U, R](x: Car[V = U, EC = R], s: Car, w: W) -> Option[T = Pair[A = Car[V = V, EC = EC], B = W]] effects {EC} = none
  end
  operation use[R](a: Car[V = Int64, EC = R], b: Car[V = Int64, EC = R]) -> Int64 effects {R} =
    match Sp.pick3[W = Int64](a, b, "s")
      case some(p) -> 1
      case none() -> 7
  operation useq[R](a: Car[V = Int64, EC = R], b: Car[V = Int64, EC = R]) -> Int64 effects {R} =
    match Car.pick3[W = Int64](a, b, "s")
      case some(p) -> 1
      case none() -> 7
end
"#;
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(by_argument),
        &[
            "pick3.w (op-arg): expected Int64, got String",
            "pick3.w (op-arg): expected Int64, got String",
        ],
    );
    let src = bracket_program(
        "wi0rp29.bracket_x",
        Some("Option[T = Pair[A = Car, B = String]]"),
    );
    let errs = load_errors(&src);
    // The errors carry no operation name, so the two spellings are told apart by count: one
    // annotation refusal each, the bracket's `Int64` against the annotation's `String`.
    assert_eq!(
        errs.iter()
            .filter(|e| e.contains("in r.annotation") && e.contains("B = Int64"))
            .count(),
        2,
        "both spellings refused: {errs:#?}"
    );
}

/// The fallback's two other verdicts: `Sp.put(x, y, k)` / `Sp.each(x, y, f)` thread the
/// override (`s.E` does not ground over `R`) at a projection over ANOTHER argument (`k: o.T`,
/// `f: (x: o.T) -> …`). The spec operation has a DEFAULT body, so the declaration rule does not
/// compare the member (it compares only a sole backing — WI-20260930-FB53M) and the call is its
/// only judge; a member that is the sole backing is refused where it is declared, since `o`
/// is any provider and its `T` any type (the member-rule file's projection rows).
fn fallback_verdict_program(ns: &str, spec_op: &str, member: &str, use_body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, List, Bool, Option, String, Cell, Modify, Unit}}
  import anthill.prelude.Option.{{some, none}}
  sort Sp
    sort T = ?
    effects E = ?
    {spec_op}
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = V, E = {{EC}}]
    {member}
  end
  operation use[R](x: Car[V = Int64, EC = R], y: Car[V = Int64, EC = {{}}], h: Cell[V = Int64]) -> Int64 effects {{R}} =
    {use_body}
end
"#
    )
}

/// THE FALLBACK REFUSES AN ARGUMENT THE OVERRIDE TAKES AS AN OPTION: `Car.put(…, k: Option[T =
/// Int64])` behind `put(s, o: Sp, k: o.T)`. The qualified call wraps the `5` in `some(…)`; a call
/// through the spec was elaborated against the spec's parameter and wraps nothing. The fallback
/// counted the `WrapSome` verdict as a pass, and the override matched a bare `5` (MEASURED, the
/// match failed at run time).
#[test]
fn the_fallback_refuses_an_argument_the_override_takes_as_an_option() {
    let src = fallback_verdict_program(
        "wi0rp29.fbws",
        "operation put(s: Sp, o: Sp, k: o.T) -> Int64 effects s.E = 0",
        "operation put(c: Car, o: Sp, k: Option[T = Int64]) -> Int64 effects {EC} =\n      match k\n        case some(v) -> v + 10\n        case none() -> 3",
        "Sp.put(x, y, 5)",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["put.k (op-arg)", "nothing wraps the argument in `some(…)`"],
        "the override's option, unwrapped",
    );
}

/// THE FALLBACK JUDGES A CALLBACK'S ROW: `Car.each(…, f: (x: Int64) -> Int64)` takes a pure
/// callback, and the lambda writes `h`. The qualified call refuses it ("the closed row does not
/// admit `Modify[h]`"); the fallback ran only the subtype check, and an operation declared pure
/// wrote a cell (MEASURED: the run answered the written value).
#[test]
fn the_fallback_judges_a_callback_row() {
    let src = fallback_verdict_program(
        "wi0rp29.fbcb",
        "operation each[EP](s: Sp, o: Sp, f: (x: o.T) -> Int64 @ {EP}) -> Int64 effects {s.E, EP} = 0",
        "operation each(c: Car, o: Sp, f: (x: Int64) -> Int64) -> Int64 effects {EC} = f(1)",
        "Sp.each[EP = {Modify[h]}](x, y, lambda (z: Int64) -> let _ = Cell.set(h, z + 40)\n      z)",
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "each.f (op-arg)",
            "`Modify[T = h]`, which the closed row does not admit",
        ],
        "the override's closed callback row",
    );
}

// ── the sixth review's fixes: an absence over a row variable, the expected type ──────

/// `Strm.each[EffP](s, f: … @ {EffP, -s.E})` over `s: Strm[E = {e}]` in `use[R]`, called with
/// `g`, typed `g_ty`.
fn absent_rowvar_program(ns: &str, e: &str, g_ty: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Int64, Error}}
  sort Foo
    entity foo
  end
  sort Strm
    sort T = ?
    effects E = ?
    operation each[EffP](s: Strm, f: (x: Int64) -> Bool @ {{EffP, -s.E}}) -> Bool effects {{EffP}} = true
  end
  operation use[R](s: Strm[T = Int64, E = {e}], g: {g_ty}) -> Bool effects {{{declared}}} =
    Strm.each(s, g)
end
"#
    )
}

/// AN ABSENCE OVER A ROW VARIABLE DENIES THE ROW (user decision, 2026-10-01): `-s.E` over `{Error[Foo],
/// R}`, over `{R}` and over a bare `R` each lacks `R`, so a callback raising `R` itself is refused.
/// Spliced as `-R` and read as a label, the variable matched none, and it loaded (MEASURED).
#[test]
fn an_absence_over_a_row_variable_denies_the_variable() {
    for (ns, e) in [
        ("wi0rp29.rv_both", "{Error[Foo], R}"),
        ("wi0rp29.rv_braced", "{R}"),
        ("wi0rp29.rv_bare", "R"),
    ] {
        assert_refused_naming(
            &load_errors(&absent_rowvar_program(
                ns,
                e,
                "(x: Int64) -> Bool @ {R}",
                "R",
            )),
            &["to lack the row `?R`", "raises the row `?R` itself"],
            e,
        );
    }
}

/// … AND A LABEL BESIDE A RIGID ONE CANNOT BE SHOWN OUTSIDE IT: `use`'s `R` is unknown inside
/// `use`, so a callback raising `Error[Foo]` against `-R` is refused (case 2 of the decision).
#[test]
fn an_absence_over_a_rigid_row_variable_refuses_a_label() {
    assert_refused_naming(
        &load_errors(&absent_rowvar_program(
            "wi0rp29.rv_label",
            "{R}",
            "(x: Int64) -> Bool @ {Error[Foo]}",
            "R, Error[Foo]",
        )),
        &[
            "to lack the row `?R`",
            "which cannot be shown outside that row",
        ],
        "a label against a rigid absent row",
    );
}

/// … AND ITS CONTROL: a pure callback lacks every row and loads; and over a ground row (`E =
/// {Error[Foo]}`) a callback raising another label (`Error[Int64]`) loads. Both pass either way
/// by design.
#[test]
fn an_absence_over_a_row_variable_control() {
    let errs = load_errors(&absent_rowvar_program(
        "wi0rp29.rv_pure",
        "{R}",
        "(x: Int64) -> Bool",
        "R",
    ));
    assert!(errs.is_empty(), "a pure callback: {errs:#?}");
    let errs = load_errors(&absent_rowvar_program(
        "wi0rp29.rv_ground",
        "{Error[Foo]}",
        "(x: Int64) -> Bool @ {Error[Int64]}",
        "Error[Int64]",
    ));
    assert!(
        errs.is_empty(),
        "another label beside a ground lacked row: {errs:#?}"
    );
}

/// A ROW HOLDING A VARIABLE IT LACKS IS UNINHABITABLE, as `{e, -e}` is: `use[R = R, EffP = R]`
/// makes `h`'s row `{R, -R}`. Read as a label, `-R` constrained nothing, and it loaded (MEASURED).
#[test]
fn a_row_holding_a_variable_it_lacks_is_uninhabitable() {
    let src = r#"
namespace wi0rp29.rv_self
  import anthill.prelude.{Bool, Int64, Error}
  operation use[R, EffP](g: (x: Int64) -> Bool @ {R}, h: (x: Int64) -> Bool @ {EffP, -R}) -> Bool effects {R} = true
  operation call[R](g: (x: Int64) -> Bool @ {R}) -> Bool effects {R} = use[R = R, EffP = R](g, g)
end
"#;
    assert_refused_naming(&load_errors(src), &["both admit and lack `?R`"], "{R, -R}");
}

/// `pick2[W]` through the WI-606 fallback (the receiver's row a parameter, `R`) with `Error[W]`
/// among its effects, its result let-bound at `B = annotated`, `use` declaring `Error[String]`.
fn expected_program(ns: &str, annotated: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, Pair, String, List, Error}}
  import anthill.prelude.Option.{{some, none}}
  sort Sp
    sort T = ?
    effects E = ?
    operation pick2[W](x: T, s: Sp) -> Option[T = Pair[A = s.T, B = W]] effects {{s.E, Error[W]}}
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = Car, E = {{EC}}]
    operation pick2[W, U, R](x: Car[V = U, EC = R], s: Car) -> Option[T = Pair[A = Car[V = V, EC = EC], B = W]] effects {{EC, Error[W]}} = none
  end
  operation use[R](a: Car[V = Int64, EC = R], b: Car[V = Int64, EC = R]) -> Int64 effects {{R, Error[String]}} =
    let r: Option[T = Pair[A = Car, B = {annotated}]] = Sp.pick2(a, b)
    7
end
"#
    )
}

/// THE CALLER'S EXPECTED TYPE REACHES THE OVERRIDE: a `W` only the annotation binds is `String`
/// in the override the fallback threads, as in `Car.pick2(a, b)` — so `Error[String]` is charged
/// and declared — and it is the SPEC's `W` too, pinned by the threaded return. The annotation never
/// reached the fallback, which declined ("no member E", the tree the sixth review saw and the
/// pre-ticket build); reaching the override alone, the spec's `W` stayed free and the call was
/// refused "expected a type for 'W'" (MEASURED).
#[test]
fn the_callers_expected_type_reaches_the_override() {
    let errs = load_errors(&expected_program("wi0rp29.expected", "String"));
    assert!(errs.is_empty(), "W from the annotation: {errs:#?}");
}

/// … AND ITS CONTROL: annotated at `B = Int64`, `Error[Int64]` is charged, which `use` does not
/// declare — the annotation decides `W` as it decides it in the row above, never admitting a
/// contradicting one. Fails under ledger parts 43 and 44 too, the refusal then the spec's own.
#[test]
fn the_callers_expected_type_reaches_the_override_control() {
    assert_refused_naming(
        &load_errors(&expected_program("wi0rp29.expected_c", "Int64")),
        &["undeclared effect"],
        "Error[Int64] undeclared",
    );
}

// ── the sixth review's fixes: the override's own parameters, and the fallback's verdicts ──

/// AN OVERRIDE PARAMETER ONLY THE RECEIVER BINDS IS BOUND AT THE CALL: `op[W](c: Car[V = W], x)
/// effects {Error[W]}` through `Sp.op(k, 1)` over a `Car[V = String]` charges `Error[String]`, as
/// `Car.op(k, 1)` does. Read off the spec's parameters alone, `W` stayed free and `Error[?W]` was
/// charged — refused as undeclared (MEASURED). The callers declaring `Error[String]` load, and a
/// PURE caller of the spec call is refused naming that very effect — a caller that
/// over-declares loads whatever is charged, the override's effect dropped included, so it is
/// the pure one that shows `Error[String]` charged.
#[test]
fn an_override_parameter_only_the_receiver_binds_is_bound() {
    let program = |ns: &str, declared: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, List, Bool, Option, String, Error}}
  sort Sp
    sort T = ?
    operation op(s: Sp, x: Int64) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation op[W](c: Car[V = W], x: Int64) -> Int64 effects {{Error[W]}} = x
  end
  operation useSpec(k: Car[V = String]) -> Int64{declared} = Sp.op(k, 1)
  operation useDirect(k: Car[V = String]) -> Int64 effects {{Error[String]}} = Car.op(k, 1)
end
"#
        )
    };
    let errs = load_errors(&program("wi0rp29.recv_w", " effects {Error[String]}"));
    assert!(errs.is_empty(), "W from the receiver: {errs:#?}");
    assert_refused_naming(
        &load_errors(&program("wi0rp29.recv_w_pure", "")),
        &["undeclared effect: Error[T = String]"],
        "the override's effect at the receiver's `W`",
    );
}

/// … AND A ROW PARAMETER ONLY THE RECEIVER BINDS: `op[W, R](c: Car[V = W, EC = R], a) effects
/// {R}` over a `Car[…, EC = {Error[Foo]}]` charges `Error[Foo]`, which a pure caller does not
/// declare. Left unbound, the row was dropped as unresolved, the pure caller LOADED, and it raised
/// `Error[Foo]` at run time (MEASURED).
#[test]
fn a_row_parameter_only_the_receiver_binds_is_charged() {
    let src = r#"
namespace wi0rp29.recv_row
  import anthill.prelude.{Int64, Bool, Option, String, Error, List}
  sort Foo
    entity foo
  end
  sort Sp
    sort T = ?
    effects E = ?
    operation op(s: Sp, a: Int64) -> Int64
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V, f: (u: Int64) -> Int64 @ EC)
    provides Sp[T = V, E = {EC}]
    operation op[W, R](c: Car[V = W, EC = R], a: Int64) -> Int64 effects {R} =
      match c
        case car(v, f) -> f(a)
  end
  operation via(x: Car[V = Int64, EC = {Error[Foo]}]) -> Int64 = Sp.op(x, 1)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["undeclared effect: Error[T = Foo]"],
        "the receiver's row charged",
    );
}

/// THE ARGUMENTS DECIDE BEFORE THE SPEC'S TYPE: `op[W](c, a: W) -> Option[T = W]` behind `op(s,
/// a: Animal) -> Option[T = Animal]`, given a `cat`, is `W = cat` — as `Car.op(x, c1)` binds it —
/// so the result is an `Option[T = cat]`. Met with the spec's `Animal` first, `W` widened past the
/// argument and the annotation was refused (MEASURED). Runs to 41 + 1.
#[test]
fn the_arguments_decide_an_override_parameter_before_the_spec() {
    let src = r#"
namespace wi0rp29.own_widen
  import anthill.prelude.{Int64, Bool, Option, String, Error, List}
  import anthill.prelude.Option.{some, none}
  sort Animal
    entity cat(n: Int64)
    entity dog(m: String)
  end
  sort Sp
    sort T = ?
    effects E = ?
    operation op(s: Sp, a: Animal) -> Option[T = Animal] effects s.E
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = V, E = {EC}]
    operation op[W](c: Car, a: W) -> Option[T = W] effects {EC} = some(a)
  end
  operation use[R](x: Car[V = Int64, EC = R]) -> Int64 effects {R} =
    let c1: cat = cat(n: 41)
    let r: Option[T = cat] = Sp.op(x, c1)
    match r
      case some(cat(n)) -> n + 1
      case none() -> 0
  operation go() -> Int64 =
    let x: Car[V = Int64, EC = {}] = car(v: 1)
    use(x)
end
"#;
    assert_eq!(run_src(src, "wi0rp29.own_widen.go"), Ok(42));
}

/// THE FALLBACK VALIDATES WHAT THE OVERRIDE RECEIVES: `k: Option[T = Int64]` on both sides, the
/// call wrapping `5` in `some(…)` against the spec's own option — the override takes what was
/// passed. The raw `5` was validated instead, and refused as an unwrapped option (MEASURED; the
/// tree before the fifth pass ran it). Runs to 5 + 10.
#[test]
fn the_fallback_validates_what_the_override_receives() {
    let src = r#"
namespace wi0rp29.fb_wrapped
  import anthill.prelude.{Int64, List, Bool, Option, String}
  import anthill.prelude.Option.{some, none}
  sort Sp
    sort T = ?
    effects E = ?
    operation put(s: Sp, k: Option[T = Int64]) -> Int64 effects s.E
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = V, E = {EC}]
    operation put(c: Car, k: Option[T = Int64]) -> Int64 effects {EC} =
      match k
        case some(v) -> v + 10
        case none() -> 3
  end
  operation use[R](x: Car[V = Int64, EC = R]) -> Int64 effects {R} = Sp.put(x, 5)
  operation go() -> Int64 =
    let x: Car[V = Int64, EC = {}] = car(v: 1)
    use(x)
end
"#;
    assert_eq!(run_src(src, "wi0rp29.fb_wrapped.go"), Ok(15));
}

/// THE FALLBACK'S CALLBACK ROW TAKES A FIELD PATH'S HEAD: `Sp.apply[EP = {Modify[h]}](x, y,
/// h.cell, λ)` threads an override whose callback row names `Modify[p]`, `p` bound to `h.cell` —
/// the caller's `Modify[h]`. Re-keyed by variables only, the row kept `Modify[p]` and the lambda
/// writing `h.cell` was refused (MEASURED; the tree before the fifth pass loaded it). The spec
/// operation has a default body, so the fallback is this member's only judge.
#[test]
fn the_fallbacks_callback_row_takes_a_field_paths_head() {
    let src = r#"
namespace wi0rp29.fb_head
  import anthill.prelude.{Int64, List, Bool, Option, String, Cell, Modify, Unit}
  sort Holder
    entity holder(cell: Cell[V = Int64])
  end
  sort Sp
    sort T = ?
    effects E = ?
    operation apply[EP](s: Sp, o: Sp, p: Cell[V = Int64], f: (u: o.T) -> Unit @ {EP}) -> Int64 effects {s.E, EP, Modify[p]} = 0
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = V, E = {EC}]
    operation apply(c: Car, o: Sp, p: Cell[V = Int64], f: (u: Int64) -> Unit @ Modify[p]) -> Int64 effects {EC, Modify[p]} =
      let _ = f(5)
      7
  end
  operation use[R](x: Car[V = Int64, EC = R], y: Car[V = Int64, EC = {}], h: Holder) -> Int64 effects {R, Modify[h]} =
    Sp.apply[EP = {Modify[h]}](x, y, h.cell, lambda (u: Int64) -> Cell.set(h.cell, u))
end
"#;
    let errs = load_errors(src);
    assert!(errs.is_empty(), "Modify[h] through the head: {errs:#?}");
}

/// A SELF-RECURSIVE CALL'S CALLBACK ROW IS RE-KEYED ONCE: `apply(h, b, q, h.cell, λ, true)` inside
/// `apply` — the caller's variables are the callee's own parameters, so a second re-key renamed
/// `Modify[q]` → `Modify[p]` → `Modify[h]` and refused the lambda writing `q` (MEASURED).
#[test]
fn a_self_recursive_callback_row_is_rekeyed_once() {
    let src = r#"
namespace wi0rp29.cb_once
  import anthill.prelude.{Int64, Unit, Cell, Modify, Bool, List, String}
  sort Holder
    entity holder(cell: Cell[V = Int64])
  end
  sort Box
    sort T = ?
    entity box(item: T)
  end
  operation apply(h: Holder, b: Box[T = Int64], p: Cell[V = Int64], q: Cell[V = Int64], f: (u: b.T) -> Unit @ Modify[p], stop: Bool) -> Unit effects {Modify[p], Modify[q], Modify[h]} =
    if stop then f(b.item)
    else apply(h, b, q, h.cell, lambda (u: Int64) -> Cell.set(q, u), true)
end
"#;
    let errs = load_errors(src);
    assert!(errs.is_empty(), "Modify[q] once: {errs:#?}");
}

/// A BRACKET REACHES THE FALLBACK PAST A RETURN THAT DOES NOT REDUCE: `pick2[W]`'s spec return
/// holds `Sp[T = s.T, E = s.E]`, which fails to eliminate — the fallback's canonical shape — and
/// still relates `B = W` with each projection masked. Dropping the whole return relation, `W`
/// was unbound and the fallback declined "no member E" (MEASURED). Runs to 7.
#[test]
fn a_bracket_reaches_the_fallback_past_an_unreduced_return() {
    let src = r#"
namespace wi0rp29.bracket_se
  import anthill.prelude.{Int64, Bool, Option, Pair, String, List}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}
  sort Sp
    sort T = ?
    effects E = ?
    operation pick2[W](x: T, s: Sp) -> Option[T = Pair[A = Sp[T = s.T, E = s.E], B = W]] effects s.E
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = Car[V = ?, EC = ?], E = {EC}]
    operation pick2[W, U, R](x: Car[V = U, EC = R], s: Car) -> Option[T = Pair[A = Car[V = V, EC = EC], B = W]] effects {EC} = none
  end
  operation use[R](a: Car[V = Int64, EC = R], b: Car[V = Int64, EC = R]) -> Int64 effects {R} =
    match Sp.pick2[W = Int64](a, b)
      case some(pair(_, w)) -> w + 1
      case none() -> 7
  operation go() -> Int64 =
    let a: Car[V = Int64, EC = {}] = car(v: 1)
    let b: Car[V = Int64, EC = {}] = car(v: 2)
    use(a, b)
end
"#;
    assert_eq!(run_src(src, "wi0rp29.bracket_se.go"), Ok(7));
}

/// THE FALLBACK VALIDATES AGAINST THE PARAMETER AS WRITTEN: a list of `String -> Bool` callables
/// passed where the override takes `List[T = Function[A = Int64, B = Int64]]` is refused. Against
/// the deep-expanded parameter, its fresh slot made the pair non-ground, the groundness gate let it
/// through, and `f(1)` ran a `String` callable (MEASURED). The spec operation has a default body,
/// so the fallback is this member's only judge.
#[test]
fn the_fallback_validates_against_the_parameter_as_written() {
    let src = r#"
namespace wi0rp29.fb_written
  import anthill.prelude.{Int64, List, Bool, Option, String, Function}
  import anthill.prelude.List.{cons, nil}
  sort Sp
    sort T = ?
    effects E = ?
    operation put(s: Sp, o: Sp, k: o.T) -> Int64 effects s.E = 0
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = V, E = {EC}]
    operation put(c: Car, o: Sp, k: List[T = Function[A = Int64, B = Int64]]) -> Int64 effects {EC} =
      match k
        case cons(f, _) -> f(1) + 1
        case nil() -> 0
  end
  operation isEmpty(s: String) -> Bool = true
  operation use[R](x: Car[V = Int64, EC = R], y: Car[V = List[T = (s: String) -> Bool], EC = {}], ks: List[T = (s: String) -> Bool]) -> Int64 effects {R} =
    Sp.put(x, y, ks)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["put.k (op-arg): expected List[T = Function[A = Int64, B = Int64]]"],
        "a wrong nested callable",
    );
}

/// `use[R, Q]` passing its callback `g`, typed `g_ty`, to `Strm.each(s, g)` over `s: Strm[E = {R}]`
/// — `each` requires a callback lacking `s.E`, here the rigid `R` — declaring `declared`, then
/// `rest`.
fn rowvar_constraint_program(ns: &str, g_ty: &str, declared: &str, rest: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Int64, Error}}
  sort Foo
    entity foo
  end
  sort Bar
    entity bar
  end
  sort Strm
    sort T = ?
    effects E = ?
    operation each[EffP](s: Strm, f: (x: Int64) -> Bool @ {{EffP, -s.E}}) -> Bool effects {{EffP}} = true
  end
  operation use[R, Q](s: Strm[T = Int64, E = {{R}}], g: (x: Int64) -> Bool @ {g_ty}) -> Bool effects {{{declared}}} =
    Strm.each(s, g)
  operation bad(x: Int64) -> Bool effects {{Error[Foo]}} = true
  operation good(x: Int64) -> Bool effects {{Error[Bar]}} = true
{rest}end
"#
    )
}

/// ANOTHER RIGID ROW VARIABLE BESIDE A LACKED ONE IS REFUSED (user decision, 2026-10-01): `g`'s row
/// `Q` may share effects with `R`, which `use` cannot know, so passing it where `-R` is required
/// is refused, naming the repair. It loaded (MEASURED), and an instantiation with `Q = R` raised
/// what `each` requires its callback to lack.
#[test]
fn another_rigid_row_variable_beside_a_lacked_one_is_refused() {
    assert_refused_naming(
        &load_errors(&rowvar_constraint_program(
            "wi0rp29.qr_undecl",
            "{Q}",
            "Q",
            "",
        )),
        &[
            "to lack the row `?R`",
            "raises the row `?Q`, which cannot be shown outside that row",
            "`@ {…, -R}`",
        ],
        "Q beside a lacked R",
    );
}

/// … AND STATED ON THE CALLBACK'S OWN ROW IT LOADS: `g: … @ {Q, -R}` lacks `R` by its type, so
/// passing it on is sound, and the type holds `use`'s callers to it — a callback raising a
/// different error than the stream's row is passed. Fails with the exemption backed out (ledger
/// part 53), the stated row then refused as the bare one is.
#[test]
fn a_row_variable_stated_to_lack_the_row_is_passed() {
    let src = rowvar_constraint_program(
        "wi0rp29.qr_decl",
        "{Q, -R}",
        "Q",
        "  operation callOk(s: Strm[T = Int64, E = {Error[Foo]}]) -> Bool effects {Error[Bar]} = use(s, good)\n",
    );
    let errs = load_errors(&src);
    assert!(errs.is_empty(), "{{Q, -R}} lacks R: {errs:#?}");
}

/// … WHICH HOLDS THE CALLERS TO IT: a caller passing a callback raising exactly the stream's
/// `Error[Foo]` is refused at its own call — the constraint moved to where `R` is known, the
/// control that the stated constraint is not a hole. Fails under ledger part 39 (the absence
/// read as a label, the overlap admitted); the builds before this pass refused it only as "Q
/// unconstrained".
#[test]
fn a_row_variable_stated_to_lack_the_row_is_passed_control() {
    let src = rowvar_constraint_program(
        "wi0rp29.qr_decl_bad",
        "{Q, -R}",
        "Q",
        "  operation callBad(s: Strm[T = Int64, E = {Error[Foo]}]) -> Bool effects {Error[Foo]} = use(s, bad)\n",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["use.g (op-arg)", "to lack `Error[T = Foo]`"],
        "the caller's overlap",
    );
}

/// … A LABEL STATED SO TOO: `g: … @ {Error[Foo], -R}` lacks `R` by its type, so its label is
/// passed where `-R` is required. Fails with the exemption backed out (ledger part 53).
#[test]
fn a_label_stated_to_lack_the_row_is_passed() {
    let src = rowvar_constraint_program("wi0rp29.qr_label", "{Error[Foo], -R}", "Error[Foo]", "");
    let errs = load_errors(&src);
    assert!(errs.is_empty(), "the label lacks R by its type: {errs:#?}");
}

/// `use[R, Q]` passing `h.f` — a callback read from a field, which the callback-row validator
/// does not see (it reads an operation reference or a lambda) — to `Strm.each(s, h.f)` over `s:
/// Strm[E = {R}]`, `h` holding a callback of row `row`.
fn field_callback_program(ns: &str, row: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Int64, Error}}
  sort Strm
    sort T = ?
    effects E = ?
    operation each[EffP](s: Strm, f: (x: Int64) -> Bool @ {{EffP, -s.E}}) -> Bool effects {{EffP}} = true
  end
  sort Holder
    effects Q2 = ?
    entity holder(f: (x: Int64) -> Bool @ {{Q2}})
  end
  operation use[R, Q](s: Strm[T = Int64, E = {{R}}], h: Holder[Q2 = {row}]) -> Bool{declared} =
    Strm.each(s, h.f)
end
"#
    )
}

/// … AND A CALLBACK READ FROM A FIELD IS HELD TO IT AS ANY OTHER: `h.f`'s row `Q` beside the
/// lacked `R` is refused in the decision's own words. The row relation refuses it too (it
/// loaded once the open tail was followed, admitted by the relation — MEASURED with ledger part
/// 52 backed out), but its verdict binds nothing and is not reported: the call then said only
/// that `each`'s `EffP` was unconstrained, and writing the bracket that message asks for LOADED
/// the program (MEASURED — the seventh review's finding 11; see
/// [`a_field_callback_is_held_to_a_lacked_row_however_it_is_passed`]). FAILS under ledger parts
/// 41 and 56; part 52 fails it no longer, the validator refusing it whatever the relation says.
#[test]
fn a_field_callback_beside_a_lacked_row_is_refused() {
    let errs = load_errors(&field_callback_program(
        "wi0rp29.qr_field",
        "Q",
        " effects {Q}",
    ));
    assert_refused_naming(
        &errs,
        &[
            "to lack the row `?R`",
            "the argument raises the row `?Q`",
            "cannot be shown outside that row",
        ],
        "h.f's Q beside a lacked R",
    );
}

/// … AND ITS CONTROL: a pure field callback lacks every row and loads. Passes either way by
/// design.
#[test]
fn a_field_callback_beside_a_lacked_row_is_refused_control() {
    let errs = load_errors(&field_callback_program("wi0rp29.qr_field_pure", "{}", ""));
    assert!(errs.is_empty(), "a pure field callback: {errs:#?}");
}

// ── the seventh review's fixes ───────────────────────────────────────────────

/// THE FALLBACK VALIDATES THE OPTION OF THE ARGUMENT, not the option the spec declares: `put(s:
/// Sp, o: Sp, k: Option)` writes no payload, so the call wraps `5` in `some(…)` against a bare
/// `Option` — and the override's `k: Option[T = String]` is handed a `some(5)`. The declared
/// option stood in for what the override receives, so it passed, the call LOADED, and the
/// override's `String.length` ran on an `Int64` (MEASURED; the sixth review's tree refused it).
/// The spec operation has a default body, so the fallback is this member's only judge
/// (WI-20260930-FB53M). FAILS under ledger part 54.
#[test]
fn the_fallback_validates_the_option_of_the_argument() {
    let src = r#"
namespace wi0rp29.fb_bare_option
  import anthill.prelude.{Int64, List, Bool, Option, String}
  import anthill.prelude.Option.{some, none}
  sort Sp
    sort T = ?
    effects E = ?
    operation put(s: Sp, o: Sp, k: Option) -> Int64 effects s.E = 0
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = V, E = {EC}]
    operation put(c: Car, o: Sp, k: Option[T = String]) -> Int64 effects {EC} =
      match k
        case some(v) -> String.length(v)
        case none() -> 3
  end
  operation use[R](x: Car[V = Int64, EC = R], y: Car[V = Int64, EC = {}]) -> Int64 effects {R} =
    Sp.put(x, y, 5)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["put.k (op-arg): expected Option[T = String], got Option[T = Int64]"],
        "a `5` wrapped for an override taking an option of strings",
    );
}

/// `use3[R, EP](h: … @ {EP, -R}, g: … @ {R})` — the callback `h` must lack whatever row `g`
/// raises — and `call`, passing two callbacks as `call_args` writes them.
fn lacked_later_program(ns: &str, h_raises: &str, call_args: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Int64, Error}}
  sort Foo
    entity foo
  end
  sort Bar
    entity bar
  end
  operation use3[R, EP](h: (x: Int64) -> Bool @ {{EP, -R}}, g: (x: Int64) -> Bool @ {{R}}) -> Bool effects {{R, EP}} = true
  operation call(g1: (x: Int64) -> Bool @ {{{h_raises}}}, g2: (x: Int64) -> Bool @ {{Error[Foo]}}) -> Bool effects {{Error[Foo], {h_raises}}} =
    use3{call_args}
end
"#
    )
}

/// A LACKED ROW BOUND BY A LATER ARGUMENT IS STILL ENFORCED: `h`'s row is `{EP, -R}`, and `R`
/// is bound by `g`, the argument AFTER it. While `R` was unbound the absence constrained
/// nothing, and once `g` bound it to `{Error[Foo]}` nothing looked again — the post-solve check
/// compared the `-R` with each label by equality — so a callback raising the lacked label
/// loaded in this order and was refused in the other (MEASURED). The absences are read through
/// what they deny, so the instantiated row `{Error[Foo], -Error[Foo]}` is refused whichever
/// argument comes first, by position or by name, and written in a bracket. FAILS under ledger
/// part 55.
#[test]
fn a_lacked_row_bound_by_a_later_argument_is_still_enforced() {
    for (tag, args) in [
        ("first", "(g1, g2)"),
        ("named", "(g: g2, h: g1)"),
        ("bracket", "[R = {Error[Foo]}, EP = {Error[Foo]}](g1, g2)"),
    ] {
        assert_refused_naming(
            &load_errors(&lacked_later_program(
                &format!("wi0rp29.lack_later_{tag}"),
                "Error[Foo]",
                args,
            )),
            &["use3.h (op-arg)", "lack", "`Error[T = Foo]`"],
            &format!("the lacked label raised, {tag}"),
        );
    }
}

/// … AND ITS CONTROL: a callback raising ANOTHER label beside the lacked row loads in each
/// order. Passes either way by design: it guards the check against refusing every label once
/// the row is bound (the builds before this pass refused these as "EP unconstrained").
#[test]
fn a_lacked_row_bound_by_a_later_argument_is_still_enforced_control() {
    for (tag, args) in [("first", "(g1, g2)"), ("named", "(g: g2, h: g1)")] {
        let errs = load_errors(&lacked_later_program(
            &format!("wi0rp29.lack_later_ok_{tag}"),
            "Error[Bar]",
            args,
        ));
        assert!(errs.is_empty(), "a disjoint label, {tag}: {errs:#?}");
    }
}

// ── the seventh review's findings 11 and 14 ──────────────────────────────────

/// `use[R, Q]` over `s: Strm[T = Int64, E = {R}]` and `h: Holder[Q2 = {holder_row}]`, its body
/// `call` — which passes `Strm.each` a callback that is neither an operation reference nor a
/// lambda: the field `h.f`, or the result of `mk()` (a callback raising `Error[Foo]`).
fn callback_source_program(ns: &str, holder_row: &str, call: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Int64, Error}}
  sort Foo
    entity foo
  end
  sort Strm
    sort T = ?
    effects E = ?
    operation each[EffP](s: Strm, f: (x: Int64) -> Bool @ {{EffP, -s.E}}) -> Bool effects {{EffP}} = true
  end
  sort Holder
    effects Q2 = ?
    entity holder(f: (x: Int64) -> Bool @ {{Q2}})
  end
  operation bad(x: Int64) -> Bool effects {{Error[Foo]}} = true
  operation mk() -> (x: Int64) -> Bool @ {{Error[Foo]}} = bad
  operation use[R, Q](s: Strm[T = Int64, E = {{R}}], h: Holder[Q2 = {holder_row}]) -> Bool{declared} =
    {call}
end
"#
    )
}

/// A CALLBACK IS HELD TO AN ABSENCE OVER A ROW HOWEVER IT IS PASSED — a field, a call's result,
/// with a bracket or without. The validator that refuses a label, or another rigid row variable,
/// beside a lacked rigid row read only an operation reference or a lambda, and returned on
/// anything else; the row relation's refusal binds nothing and is not reported. So `Strm.each(s,
/// h.f)` with `h.f` raising `Error[Foo]` LOADED — a callback raising the very label its stream
/// may raise — where `let g = h.f` then `Strm.each(s, g)` was refused; a callback raising a
/// rigid `Q` was refused only as "`EffP` unconstrained — use `each[EffP = …]`", and LOADED once
/// that bracket was written; `[EffP = {R}]` admitted one raising `R` itself; and a call's result
/// was never looked at (each MEASURED). FAILS under ledger part 56.
///
/// THE `[EffP = {R}]` CASE NO LONGER MEASURES PART 56 (WI-20261001-89WZR): a bracket's `R` is
/// now the operation's own row, so that bracket itself writes the callback's row as `{R, -R}`
/// and is refused as the uninhabitable row it is, before any argument is read — the refusal
/// [`a_row_holding_a_variable_it_lacks_is_uninhabitable`] gives its written twin. While the
/// bracket's `R` was a row variable of its own, the argument was what refused it ("raises the
/// row `?R` itself"); the bracket-less `itself` case still is.
#[test]
fn a_field_callback_is_held_to_a_lacked_row_however_it_is_passed() {
    let lack = "to lack the row `?R`";
    for (tag, holder_row, call, declared, what) in [
        (
            "label",
            "{Error[Foo]}",
            "Strm.each(s, h.f)",
            " effects {Error[Foo]}",
            "the argument declares `Error[T = Foo]`",
        ),
        (
            "bracket",
            "Q",
            "Strm.each[EffP = {Q}](s, h.f)",
            " effects {Q}",
            "cannot be shown outside that row",
        ),
        (
            "itself",
            "R",
            "Strm.each(s, h.f)",
            " effects {R}",
            "the argument raises the row `?R` itself",
        ),
        (
            "call_result",
            "{}",
            "Strm.each(s, mk())",
            " effects {Error[Foo]}",
            "the argument declares `Error[T = Foo]`",
        ),
    ] {
        let src =
            callback_source_program(&format!("wi0rp29.cbsrc_{tag}"), holder_row, call, declared);
        assert_refused_naming(&load_errors(&src), &[lack, what], tag);
    }
    let src = callback_source_program(
        "wi0rp29.cbsrc_itself_bracket",
        "R",
        "Strm.each[EffP = {R}](s, h.f)",
        " effects {R}",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["each.f (op-arg)", "both admit and lack `?R`"],
        "itself_bracket",
    );
}

/// `use(h: Holder[Q2 = {raises}])` passing `h.f` to `call` — `each2`, whose callback row is
/// `{EffP, -Error[Foo]}`, or `each0`, whose callback is pure.
fn field_label_program(ns: &str, raises: &str, call: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Int64, Error}}
  sort Foo
    entity foo
  end
  sort Bar
    entity bar
  end
  sort Holder
    effects Q2 = ?
    entity holder(f: (x: Int64) -> Bool @ {{Q2}})
  end
  operation each2[EffP](f: (x: Int64) -> Bool @ {{EffP, -Error[Foo]}}) -> Bool effects {{EffP}} = true
  operation each0(f: (x: Int64) -> Bool) -> Bool = true
  operation use(h: Holder[Q2 = {{{raises}}}]) -> Bool{declared} = {call}
end
"#
    )
}

/// … AND TO AN ABSENCE OVER A LABEL, AND TO A CLOSED ROW: a field callback raising `Error[Foo]`
/// against `-Error[Foo]` is refused as its parameter twin is. `each2[EffP = {}](h.f)` LOADED on
/// every build — the label check sat below the same return — and without the bracket the call
/// said only that `EffP` was unconstrained. Against a closed row the generic comparison did
/// refuse it, printing one arrow type twice; the row's own words name the label now. FAILS under
/// ledger part 56.
#[test]
fn a_field_callback_raising_a_denied_label_is_refused() {
    for (tag, call, declared, tokens) in [
        (
            "bracket",
            "each2[EffP = {}](h.f)",
            "",
            [
                "to lack `Error[T = Foo]`",
                "the argument declares `Error[T = Foo]`",
            ],
        ),
        (
            "inferred",
            "each2(h.f)",
            " effects {Error[Foo]}",
            [
                "to lack `Error[T = Foo]`",
                "the argument declares `Error[T = Foo]`",
            ],
        ),
        (
            "closed",
            "each0(h.f)",
            "",
            ["a closed row", "the argument declares `Error[T = Foo]`"],
        ),
    ] {
        let src = field_label_program(
            &format!("wi0rp29.fldlab_{tag}"),
            "Error[Foo]",
            call,
            declared,
        );
        assert_refused_naming(&load_errors(&src), &tokens, tag);
    }
}

/// … AND ITS CONTROL: a field callback raising a label the row ADMITS loads, inferred or
/// bracketed. Passes either way by design: it guards the check against refusing every label a
/// field callback carries.
#[test]
fn a_field_callback_raising_a_denied_label_is_refused_control() {
    for (tag, call) in [
        ("inferred", "each2(h.f)"),
        ("bracket", "each2[EffP = {Error[Bar]}](h.f)"),
    ] {
        let src = field_label_program(
            &format!("wi0rp29.fldlab_ok_{tag}"),
            "Error[Bar]",
            call,
            " effects {Error[Bar]}",
        );
        let errs = load_errors(&src);
        assert!(errs.is_empty(), "an admitted label, {tag}: {errs:#?}");
    }
}

/// … AND A LABEL NAMING A VALUE IN SCOPE IS ADMITTED WHERE THE ROW ADMITS IT: a call's result
/// typed `… @ {Modify[p]}` names the caller's own cell, and the slot's `Modify[q]` — at `q = c` —
/// is that label as it stands: `run2(c, mk(c))` runs, the cell at 1 + 41. Passes either way by
/// design: it guards the check against refusing a label it now compares
/// ([`a_label_naming_a_value_in_scope_is_compared_as_it_stands`] is the refusal).
#[test]
fn a_call_result_callback_naming_a_value_is_admitted_where_the_row_admits_it() {
    let src = r#"
namespace wi0rp29.cbsrc_place
  import anthill.prelude.{Int64, String, List, Cell, Modify, Unit}
  operation run2(q: Cell[V = Int64], f: (u: Int64) -> Unit @ {Modify[q]}) -> Unit effects {Modify[q]} = f(41)
  operation mk(p: Cell[V = Int64]) -> (u: Int64) -> Unit @ {Modify[p]} = lambda (u: Int64) -> Cell.set(p, Cell.get(p) + u)
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let _ = run2(c, mk(c))
    Cell.get(c)
end
"#;
    assert_eq!(run_src(src, "wi0rp29.cbsrc_place.go"), Ok(42));
}

/// `relay[R](g: … @ {g_row}, h: … @ {R})` RETURNING `g` as a callback typed `@ {Error[Foo],
/// -R}` — no call, no argument: the row relation alone judges it.
fn returned_callback_program(ns: &str, g_row: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Int64, Error}}
  sort Foo
    entity foo
  end
  operation relay[R](g: (x: Int64) -> Bool @ {{{g_row}}}, h: (x: Int64) -> Bool @ {{R}}) -> (x: Int64) -> Bool @ {{Error[Foo], -R}} = g
end
"#
    )
}

/// WHERE NO ARGUMENT IS PASSED THE ROW RELATION IS THE JUDGE: a callback RETURNED as `@
/// {Error[Foo], -R}` must lack `R`, and one typed `@ {Error[Foo]}` cannot be shown to — the
/// label beside the lacked rigid row, in the relation's own reading of the decision. The
/// callback validator sees arguments only; since the eighth pass it sees every argument, so
/// this is the row that still measures the relation's half. FAILS under ledger part 52.
#[test]
fn a_returned_callback_is_held_to_a_lacked_row_by_the_relation() {
    assert_refused_naming(
        &load_errors(&returned_callback_program("wi0rp29.ret_cb", "Error[Foo]")),
        &["relay.return (op-return)"],
        "a returned callback raising a label beside the lacked R",
    );
}

/// … AND ITS CONTROL: the callback's own row stating `-R` is returned. Passes either way by
/// design.
#[test]
fn a_returned_callback_is_held_to_a_lacked_row_by_the_relation_control() {
    let errs = load_errors(&returned_callback_program(
        "wi0rp29.ret_cb_ok",
        "Error[Foo], -R",
    ));
    assert!(
        errs.is_empty(),
        "the returned callback states it: {errs:#?}"
    );
}

/// A ROW PARAMETER AN OPERATION'S OWN ROW HOLDS AND LACKS IS REFUSED AT ITS DECLARATION, as
/// `{e, -e}` is: `effects {Q, -Q}` admits no call. A row parameter written bare heads as a sort
/// reference and was filed among the row's LABELS, where the denied variable equals none — so
/// the declaration loaded, while `{Error[Foo], -Error[Foo]}` was refused (MEASURED). FAILS under
/// ledger part 57.
#[test]
fn a_row_parameter_held_and_lacked_is_refused_at_its_declaration() {
    let src = r#"
namespace wi0rp29.decl_rr
  import anthill.prelude.{Bool, Int64, Error}
  operation useQ[Q](g: (x: Int64) -> Bool @ {Q}) -> Bool effects {Q, -Q} = g(1)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["declares an effect row that both ADMITS and LACKS `?Q`"],
        "a row parameter held and lacked",
    );
}

/// … AND ITS CONTROL: the row parameter beside an absent LABEL is inhabitable, and loads.
/// Passes either way by design.
#[test]
fn a_row_parameter_held_and_lacked_is_refused_at_its_declaration_control() {
    let src = r#"
namespace wi0rp29.decl_rr_ok
  import anthill.prelude.{Bool, Int64, Error}
  sort Foo
    entity foo
  end
  operation useQ[Q](g: (x: Int64) -> Bool @ {Q}) -> Bool effects {Q, -Error[Foo]} = g(1)
end
"#;
    let errs = load_errors(src);
    assert!(
        errs.is_empty(),
        "a row parameter beside an absent label: {errs:#?}"
    );
}

/// `Strm.each[EffP = {Error[Foo]}](s, pure1)` over a stream raising `stream_row`: the
/// callback's row is `{EffP, -s.E}`, and `-s.E` is an absence the CALL splices.
fn spliced_absence_program(ns: &str, stream_row: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Int64, Error}}
  sort Foo
    entity foo
  end
  sort Bar
    entity bar
  end
  sort Strm
    sort T = ?
    effects E = ?
    operation each[EffP](s: Strm, f: (x: Int64) -> Bool @ {{EffP, -s.E}}) -> Bool effects {{EffP}} = true
  end
  operation pure1(x: Int64) -> Bool = true
  operation use(s: Strm[T = Int64, E = {{{stream_row}}}]) -> Bool effects {{Error[Foo]}} =
    Strm.each[EffP = {{Error[Foo]}}](s, pure1)
end
"#
    )
}

/// A CALLBACK ROW IS TESTED AGAINST ITS OWN ABSENCES AS THE CALL READS IT: `{EffP, -s.E}` at
/// `EffP = {Error[Foo]}` over a stream raising `Error[Foo]` is `{Error[Foo], -Error[Foo]}`. The
/// check read the parameter as declared, where `-s.E` is a projection that denies nothing — so
/// the bracket loaded, on every build, where its written twin (`-Error[Foo]`) was refused. FAILS
/// under ledger part 58.
#[test]
fn a_callback_row_is_tested_against_the_absences_the_call_splices() {
    assert_refused_naming(
        &load_errors(&spliced_absence_program("wi0rp29.splice_abs", "Error[Foo]")),
        &["each.f (op-arg)", "both admit and lack `Error[T = Foo]`"],
        "the bracket instantiates the row the stream denies",
    );
}

/// … AND ITS CONTROL: over a stream raising another label the same bracket loads. Passes
/// either way by design.
#[test]
fn a_callback_row_is_tested_against_the_absences_the_call_splices_control() {
    let errs = load_errors(&spliced_absence_program(
        "wi0rp29.splice_abs_ok",
        "Error[Bar]",
    ));
    assert!(errs.is_empty(), "a disjoint stream row: {errs:#?}");
}

/// `use{binder}(s: Strm[T = Int64], g: … @ {g_row})` — the stream's row UNWRITTEN — passing
/// `g` to `Strm.each(s, g)`, whose callback row is `{EffP, -s.E}`; then `rest`.
fn unwritten_row_program(
    ns: &str,
    binder: &str,
    g_row: &str,
    declared: &str,
    rest: &str,
) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Int64, Error}}
  sort Foo
    entity foo
  end
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(t: T)
    operation each[EffP](s: Strm, f: (x: Int64) -> Bool @ {{EffP, -s.E}}) -> Bool effects {{EffP}} = true
  end
  operation bad(x: Int64) -> Bool effects {{Error[Foo]}} = true
  operation use{binder}(s: Strm[T = Int64], g: (x: Int64) -> Bool @ {{{g_row}}}) -> Bool effects {{{declared}}} =
    Strm.each(s, g)
{rest}end
"#
    )
}

/// AN ABSENCE OVER AN UNWRITTEN ROW DENIES THAT ROW: inside `use(s: Strm[T = Int64], …)` the
/// stream's row is the projection `s.E` — `use`'s own, unknown there, exactly as a rigid `R` is
/// — so `-s.E` is an absence over it, and neither a label nor a rigid row variable can be shown
/// outside it. Read as a label, the projection matched only itself: a callback raising
/// `Error[Foo]`, or a rigid `Q`, was passed, and a caller then handed `use` a stream raising
/// that very label (MEASURED on every build) — where the same operation with its row NAMED (`E
/// = {R}`) was refused. The user's decision of 2026-10-01 gives the reason for a rigid `R` as
/// "the enclosing operation's own row, unknown where the check runs"; an unwritten row is that.
/// FAILS under ledger part 59.
#[test]
fn an_absence_over_an_unwritten_row_denies_that_row() {
    let lack = "to lack the row `s.E`";
    for (tag, binder, g_row, declared, what) in [
        (
            "label",
            "",
            "Error[Foo]",
            "Error[Foo]",
            "declares `Error[T = Foo]`, which cannot be shown outside that row",
        ),
        (
            "rigid",
            "[Q]",
            "Q",
            "Q",
            "raises the row `?Q`, which cannot be shown outside that row",
        ),
        ("itself", "", "s.E", "s.E", "raises the row `s.E` itself"),
    ] {
        let src = unwritten_row_program(
            &format!("wi0rp29.unwritten_{tag}"),
            binder,
            g_row,
            declared,
            "",
        );
        assert_refused_naming(&load_errors(&src), &[lack, what], tag);
    }
}

/// … AND THE CALLBACK'S OWN ROW STATES IT: `g: … @ {Error[Foo], -s.E}` loads, and holds `use`'s
/// callers to it — one passing a stream that raises `Error[Foo]` is refused, the instantiated
/// row being `{Error[Foo], -Error[Foo]}`; one passing a pure stream loads. The first and third
/// pass either way by design (controls: the absence must not refuse what states it, nor every
/// caller); the second FAILS under ledger part 58 (refused then only as two arrows that "render
/// alike").
#[test]
fn an_absence_over_an_unwritten_row_is_stated_on_the_callbacks_own_row() {
    let stated = "Error[Foo], -s.E";
    let errs = load_errors(&unwritten_row_program(
        "wi0rp29.unwritten_stated",
        "",
        stated,
        "Error[Foo]",
        "",
    ));
    assert!(errs.is_empty(), "the callback states it: {errs:#?}");
    let overlapping = "  operation call(s2: Strm[T = Int64, E = {Error[Foo]}]) -> Bool effects {Error[Foo]} = use(s2, bad)\n";
    assert_refused_naming(
        &load_errors(&unwritten_row_program(
            "wi0rp29.unwritten_overlap",
            "",
            stated,
            "Error[Foo]",
            overlapping,
        )),
        &["use.g (op-arg)", "both admit and lack `Error[T = Foo]`"],
        "a caller instantiating the overlap the callback's row denies",
    );
    let disjoint = "  operation call(s2: Strm[T = Int64, E = {}]) -> Bool effects {Error[Foo]} = use(s2, bad)\n";
    let errs = load_errors(&unwritten_row_program(
        "wi0rp29.unwritten_disjoint",
        "",
        stated,
        "Error[Foo]",
        disjoint,
    ));
    assert!(
        errs.is_empty(),
        "a caller outside the denied row: {errs:#?}"
    );
}

/// `Sp.pick2[W](x: T, s: Sp) -> {spec_ret} effects {s.E, Error[W]}` and the override `Car.pick2`
/// returning `member_ret`, called under the annotation `annotated`.
fn pin_program(ns: &str, spec_ret: &str, member_ret: &str, annotated: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, Pair, String, List, Error}}
  import anthill.prelude.Option.{{some, none}}
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(v: T)
  end
  sort Sp
    sort T = ?
    effects E = ?
    operation pick2[W](x: T, s: Sp) -> {spec_ret} effects {{s.E, Error[W]}}
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = Car, E = {{EC}}]
    operation pick2[W, U, R](x: Car[V = U, EC = R], s: Car) -> {member_ret} effects {{EC, Error[W]}} = none
  end
  operation use[R](a: Car[V = Int64, EC = R], b: Car[V = Int64, EC = R]) -> Int64 effects {{R, Error[String]}} =
    let r: {annotated} = Sp.pick2(a, b)
    7
end
"#
    )
}

/// The two shapes the whole-return pin could not unify: the override returning its CARRIER
/// where the spec returns the spec sort, and the spec's return holding a row-slot projection.
/// Each as (tag, spec return, override return, annotation at `W = {w}`).
fn pin_shapes(w: &str) -> [(&'static str, &'static str, &'static str, String); 2] {
    [
        (
            "head",
            "Option[T = Pair[A = W, B = Sp]]",
            "Option[T = Pair[A = W, B = Car[V = V, EC = EC]]]",
            format!("Option[T = Pair[A = {w}, B = Car]]"),
        ),
        (
            "rowslot",
            "Option[T = Pair[A = W, B = Strm[T = Int64, E = s.E]]]",
            "Option[T = Pair[A = W, B = Strm[T = Int64, E = {EC}]]]",
            format!("Option[T = Pair[A = {w}, B = Strm[T = Int64, E = {{R}}]]]"),
        ),
    ]
}

/// THE FALLBACK'S RETURN PINS THE SPEC'S TYPE PARAMETERS ONE BY ONE: a `W` the caller's
/// annotation fixes is the spec's `W` wherever the two returns agree ON IT, whatever else in
/// them differs. The pin was one unification of the whole masked return, committed only whole —
/// so beside the override's carrier in a slot where the spec writes `Sp` (the WI-606 shape
/// itself), or beside a row-slot projection the mask keeps (`E = s.E`), nothing was pinned and
/// the call was refused "expected a type for 'W', got unconstrained" under an annotation that
/// fixes it (MEASURED), where the qualified and the bracketed call loaded. FAILS under ledger
/// part 60.
#[test]
fn the_fallbacks_return_pins_each_spec_type_parameter() {
    for (tag, spec_ret, member_ret, annotated) in pin_shapes("String") {
        let errs = load_errors(&pin_program(
            &format!("wi0rp29.pin_{tag}"),
            spec_ret,
            member_ret,
            &annotated,
        ));
        assert!(errs.is_empty(), "W from the annotation, {tag}: {errs:#?}");
    }
}

/// … AND ITS CONTROL: annotated at `W = Int64`, `Error[Int64]` is charged, which `use` does not
/// declare — so the rows above show `W` pinned to what the annotation says, not dropped. FAILS
/// under ledger part 60 too (the refusal is then the unconstrained `W`, naming no effect).
#[test]
fn the_fallbacks_return_pins_each_spec_type_parameter_control() {
    for (tag, spec_ret, member_ret, annotated) in pin_shapes("Int64") {
        assert_refused_naming(
            &load_errors(&pin_program(
                &format!("wi0rp29.pin_c_{tag}"),
                spec_ret,
                member_ret,
                &annotated,
            )),
            &["undeclared effect", "Error[T = Int64]"],
            tag,
        );
    }
}

// ── the eighth review's fixes (the ninth pass): every callback spelling is judged ─────────────

/// A CALLBACK HELD IN A VARIABLE IS JUDGED AS ANY OTHER. The validator read every variable
/// reference as an operation, whose places it then looked up; a `let`-, pattern- or lambda-
/// bound name, a `Function[…]`-typed parameter and a `const` have none, which "disagreed" in
/// arity with every slot declaring one, and the check returned before its label and closed-row
/// halves. So `let g = mk()` then `two(inc, g)` — `inc` closes the shared row — passed a
/// callback raising `Error[Foo]`, and a `main` typed pure died "error: foo(n: 9)", where
/// `two(inc, mk())` was refused (MEASURED on every build). FAILS under ledger part 61.
#[test]
fn a_callback_held_in_a_variable_is_judged() {
    let src = r#"
namespace wi0rp29.cbv_let
  import anthill.prelude.{Bool, Int64, String, List, Error, Function, Option, Unit}
  sort Foo
    entity foo(n: Int64)
  end
  operation boom(x: Int64) -> Int64 effects {Error[Foo]} = Error.raise(foo(n: 9))
  operation inc(x: Int64) -> Int64 = x + 1
  operation mk() -> (x: Int64) -> Int64 @ {Error[Foo]} = boom
  operation two[EffP](a: (x: Int64) -> Int64 @ {EffP}, b: (x: Int64) -> Int64 @ {EffP}) -> Int64 effects {EffP} = a(1) + b(1)
  operation go() -> Int64 =
    let g = mk()
    two(inc, g)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "callback effects admitted by parameter `b` of `wi0rp29.cbv_let.two` (a closed \
             row)",
            "the callback `g` declares `Error[T = Foo]`, which the closed row does not admit",
        ],
        "a raising callback held in a let",
    );
}

/// … AND ONE BOUND BY A PATTERN, OR A PARAMETER TYPED `Function[…]`: `case holder(g) -> two(inc,
/// g)` and `via(g: Function[A = Int64, B = Int64, E = {Error[Foo]}]) = two(inc, g)` each passed
/// the raising callback, and a `main` typed pure died "error: foo(n: 9)" (MEASURED on the tree
/// the eighth review saw). FAILS under ledger part 61.
#[test]
fn a_callback_bound_by_a_pattern_or_typed_function_is_judged() {
    let shapes = [
        (
            "pat",
            "operation go() -> Int64 =\n    match holder(f: boom)\n      case holder(g) -> two(inc, g)",
        ),
        (
            "fn",
            "operation via(g: Function[A = Int64, B = Int64, E = {Error[Foo]}]) -> Int64 = two(inc, g)\n  \
             operation go() -> Int64 = via(boom)",
        ),
    ];
    for (tag, rest) in shapes {
        let src = format!(
            r#"
namespace wi0rp29.cbv_{tag}
  import anthill.prelude.{{Bool, Int64, String, List, Error, Function, Option, Unit}}
  sort Foo
    entity foo(n: Int64)
  end
  sort Holder
    entity holder(f: (x: Int64) -> Int64 @ {{Error[Foo]}})
  end
  operation boom(x: Int64) -> Int64 effects {{Error[Foo]}} = Error.raise(foo(n: 9))
  operation inc(x: Int64) -> Int64 = x + 1
  operation two[EffP](a: (x: Int64) -> Int64 @ {{EffP}}, b: (x: Int64) -> Int64 @ {{EffP}}) -> Int64 effects {{EffP}} = a(1) + b(1)
  {rest}
end
"#
        );
        assert_refused_naming(
            &load_errors(&src),
            &[
                &format!(
                    "callback effects admitted by parameter `b` of `wi0rp29.cbv_{tag}.two` (a \
                     closed row)"
                ),
                "the callback `g` declares `Error[T = Foo]`, which the closed row does not admit",
            ],
            tag,
        );
    }
}

/// … AND THROUGH THE STDLIB'S OWN HIGHER-ORDER OPERATION: `List.mapElems[EffP = {}]([1, 2],
/// g)`. FAILS under ledger part 61.
#[test]
fn a_callback_held_in_a_variable_is_judged_by_the_stdlib() {
    let src = r#"
namespace wi0rp29.cbv_let_stdlib
  import anthill.prelude.{Bool, Int64, String, List, Error, Function, Option, Unit}
  sort Foo
    entity foo(n: Int64)
  end
  operation boom(x: Int64) -> Int64 effects {Error[Foo]} = Error.raise(foo(n: 9))
  operation mk() -> (x: Int64) -> Int64 @ {Error[Foo]} = boom
  operation go() -> Int64 =
    let g = mk()
    let ys = List.mapElems[EffP = {}]([1, 2], g)
    0
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "callback effects admitted by parameter `f` of `anthill.prelude.List.mapElems` (a \
             closed row)",
            "the callback `g` declares `Error[T = Foo]`",
        ],
        "a raising callback held in a let, into the stdlib's map",
    );
}

/// … AND THEIR CONTROL: a PURE callback held in a `let` conforms to the closed row, and runs to
/// 1 + 41. Passes either way by design.
#[test]
fn a_callback_held_in_a_variable_is_judged_control() {
    let src = r#"
namespace wi0rp29.cbv_let_pure
  import anthill.prelude.{Bool, Int64, String, List, Error, Function, Option, Unit}
  sort Foo
    entity foo(n: Int64)
  end
  operation each3[EffP](f: (x: Int64) -> Int64 @ {EffP}) -> Int64 effects {EffP} = f(1)
  operation inc(x: Int64) -> Int64 = x + 41
  operation mk() -> (x: Int64) -> Int64 = inc
  operation go() -> Int64 =
    let g = mk()
    each3[EffP = {}](g)
end
"#;
    assert_eq!(run_src(src, "wi0rp29.cbv_let_pure.go"), Ok(42));
}

/// A `let` KEEPS THE BINDERS OF THE CALLABLE IT HOLDS. A callback's row names its own binders
/// (`Modify[k]`) and a slot's row names the slot's (`-Modify[x]`); which answers which is
/// positional, and an arrow TYPE does not say its binders — only the expression does. Passed by
/// the name a `let` gave it, a lambda was aligned with nothing: `app[EffP = {}](c, g)` wrote
/// the cell under `-Modify[x]` where the lambda written in place was refused (MEASURED: a pure
/// `go` answered 42). Refused now, by the lacks constraint it violates. FAILS under ledger part
/// 62 (refused then for the unknown position).
#[test]
fn a_let_bound_lambda_is_aligned_by_its_binders() {
    let src = r#"
namespace wi0rp29.cbv_let_lambda_den
  import anthill.prelude.{Bool, Int64, String, List, Error, Function, Option, Unit, Cell, Modify}
  operation app[EffP](q: Cell[V = Int64], f: (x: Cell[V = Int64]) -> Unit @ {EffP, -Modify[x]}) -> Unit effects {EffP} = f(q)
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let g = lambda (k: Cell[V = Int64]) -> Cell.set(k, 42)
    let _ = app[EffP = {}](c, g)
    Cell.get(c)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "to lack `Modify[T = f.x]` (its `-…` lacks-constraint)",
            "the callback `g` declares `Modify[T = k]` on the corresponding parameter",
        ],
        "a let-bound lambda writing the binder the slot denies",
    );
}

/// … AND ITS CONTROL: the same lambda into a slot that ADMITS `Modify[x]` fits by the same
/// alignment, and writes the cell: 42. FAILS under ledger part 62 (no alignment: its binder at
/// no known position).
#[test]
fn a_let_bound_lambda_is_aligned_by_its_binders_control() {
    let src = r#"
namespace wi0rp29.cbv_let_lambda_ok
  import anthill.prelude.{Bool, Int64, String, List, Error, Function, Option, Unit, Cell, Modify}
  operation app[EffP](q: Cell[V = Int64], f: (x: Cell[V = Int64]) -> Unit @ {EffP, Modify[x]}) -> Unit effects {EffP, Modify[q]} = f(q)
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let g = lambda (k: Cell[V = Int64]) -> Cell.set(k, 42)
    let _ = app[EffP = {}](c, g)
    Cell.get(c)
end
"#;
    assert_eq!(run_src(src, "wi0rp29.cbv_let_lambda_ok.go"), Ok(42));
}

/// … AND A `let` OVER A CALLBACK PARAMETER: `let k = g` holds `g`'s registered places.
/// `app[EffP = {}](c, k)` under `-Modify[x]` loaded and wrote the cell (MEASURED). FAILS under
/// ledger parts 62 and 63 TOGETHER and under neither alone: the record aligns it, and where
/// there is no record the place says its position itself.
#[test]
fn a_let_over_a_callback_parameter_is_aligned_by_its_places() {
    let src = r#"
namespace wi0rp29.cbv_let_param_den
  import anthill.prelude.{Bool, Int64, String, List, Error, Function, Option, Unit, Cell, Modify}
  operation app[EffP](q: Cell[V = Int64], f: (x: Cell[V = Int64]) -> Unit @ {EffP, -Modify[x]}) -> Unit effects {EffP} = f(q)
  operation use(c: Cell[V = Int64], g: (y: Cell[V = Int64]) -> Unit @ {Modify[y]}) -> Unit effects {Modify[c]} =
    let k = g
    app[EffP = {}](c, k)
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let _ = use(c, lambda (k: Cell[V = Int64]) -> Cell.set(k, 42))
    Cell.get(c)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "to lack `Modify[T = f.x]` (its `-…` lacks-constraint)",
            "the callback `k` declares `Modify[T = g.y]`",
        ],
        "a let over a callback parameter writing the binder the slot denies",
    );
}

/// … AND ITS CONTROL: into a slot admitting `Modify[x]` it fits; 42. FAILS under ledger parts
/// 62 and 63 together.
#[test]
fn a_let_over_a_callback_parameter_is_aligned_by_its_places_control() {
    let src = r#"
namespace wi0rp29.cbv_let_param_ok
  import anthill.prelude.{Bool, Int64, String, List, Error, Function, Option, Unit, Cell, Modify}
  operation app[EffP](q: Cell[V = Int64], f: (x: Cell[V = Int64]) -> Unit @ {EffP, Modify[x]}) -> Unit effects {EffP, Modify[q]} = f(q)
  operation use(c: Cell[V = Int64], g: (y: Cell[V = Int64]) -> Unit @ {Modify[y]}) -> Unit effects {Modify[c]} =
    let k = g
    app[EffP = {}](c, k)
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let _ = use(c, lambda (k: Cell[V = Int64]) -> Cell.set(k, 42))
    Cell.get(c)
end
"#;
    assert_eq!(run_src(src, "wi0rp29.cbv_let_param_ok.go"), Ok(42));
}

/// A CALLBACK PARAMETER'S PLACE SAYS ITS POSITION ITSELF: that kind of place exists only in the
/// row of its own arrow, so under an `if` over two callback parameters — an expression that
/// says no binders — `Modify[g1.x]` is still this callback's binder 0. It was passed over as "a
/// label naming a value": `app2[EffP = {}](c, if b then g1 else g2)` wrote the cell under
/// `-Modify[y]` (MEASURED: 42). FAILS under ledger part 63 (refused then for the unknown
/// position) and part 64 (it loads: a label naming a value passed over).
#[test]
fn a_callback_parameters_place_says_its_own_position() {
    let src = r#"
namespace wi0rp29.cbv_if_den
  import anthill.prelude.{Int64, String, List, Cell, Modify, Unit, Function, Bool}
  operation app2[EffP](c: Cell[V = Int64], f: (y: Cell[V = Int64]) -> Unit @ {EffP, -Modify[y]}) -> Unit effects {EffP} = f(c)
  operation setit(x: Cell[V = Int64]) -> Unit effects {Modify[x]} = Cell.set(x, 42)
  operation useg(c: Cell[V = Int64], b: Bool, g1: (x: Cell[V = Int64]) -> Unit @ {Modify[x]}, g2: (x: Cell[V = Int64]) -> Unit @ {Modify[x]}) -> Unit = app2[EffP = {}](c, if b then g1 else g2)
  operation use(c: Cell[V = Int64]) -> Unit effects {Modify[c]} = useg(c, true, setit, setit)
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let _ = use(c)
    Cell.get(c)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "to lack `Modify[T = f.y]` (its `-…` lacks-constraint)",
            "the argument declares `Modify[T = g1.x]` on the corresponding parameter",
        ],
        "an `if` over callback parameters writing the binder the slot denies",
    );
}

/// … AND ITS CONTROL: into a slot admitting `Modify[y]`, the same `if` fits and writes the
/// cell: 42. FAILS under ledger part 63.
#[test]
fn a_callback_parameters_place_says_its_own_position_control() {
    let src = r#"
namespace wi0rp29.cbv_if_ok
  import anthill.prelude.{Int64, String, List, Cell, Modify, Unit, Function, Bool}
  operation app1(c: Cell[V = Int64], f: (y: Cell[V = Int64]) -> Unit @ {Modify[y]}) -> Unit effects {Modify[c]} = f(c)
  operation setit(x: Cell[V = Int64]) -> Unit effects {Modify[x]} = Cell.set(x, 42)
  operation useg(c: Cell[V = Int64], b: Bool, g1: (x: Cell[V = Int64]) -> Unit @ {Modify[x]}, g2: (x: Cell[V = Int64]) -> Unit @ {Modify[x]}) -> Unit effects {Modify[c]} = app1(c, if b then g1 else g2)
  operation use(c: Cell[V = Int64]) -> Unit effects {Modify[c]} = useg(c, true, setit, setit)
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let _ = use(c)
    Cell.get(c)
end
"#;
    assert_eq!(run_src(src, "wi0rp29.cbv_if_ok.go"), Ok(42));
}

/// A LABEL NAMING A VALUE IN SCOPE NAMES THAT VALUE, and is compared as it stands. `mk(c)`
/// returns a callback typed `@ {Modify[c]}` — the caller's own cell — and `run3[EffP = {}](c,
/// mk(c))` denies exactly that (`-Modify[q]` at `q = c`). For a callback whose places are
/// unknown every label naming a value was passed over, so a `sneaky` typed PURE wrote the cell
/// (MEASURED: 42 on every build). FAILS under ledger part 64.
#[test]
fn a_label_naming_a_value_in_scope_is_compared_as_it_stands() {
    let src = r#"
namespace wi0rp29.cbv_value_den
  import anthill.prelude.{Int64, String, List, Cell, Modify, Unit}
  operation run3[EffP](q: Cell[V = Int64], f: (u: Int64) -> Unit @ {EffP, -Modify[q]}) -> Unit effects {EffP} = f(41)
  operation mk(p: Cell[V = Int64]) -> (u: Int64) -> Unit @ {Modify[p]} = lambda (u: Int64) -> Cell.set(p, Cell.get(p) + u)

  operation sneaky(c: Cell[V = Int64]) -> Unit = run3[EffP = {}](c, mk(c))
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let _ = sneaky(c)
    Cell.get(c)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "to lack `Modify[T = c]` (its `-…` lacks-constraint)",
            "the argument declares `Modify[T = c]`",
        ],
        "a call's result writing the cell the slot denies",
    );
}

/// … AND AGAINST A CLOSED ROW: a plain pure slot `f: (u: Int64) -> Unit` does not admit it
/// either. FAILS under ledger part 64.
#[test]
fn a_label_naming_a_value_in_scope_is_held_to_a_closed_row() {
    let src = r#"
namespace wi0rp29.cbv_value_closed
  import anthill.prelude.{Int64, String, List, Cell, Modify, Unit, Function, Bool}
  operation run0(q: Cell[V = Int64], f: (u: Int64) -> Unit) -> Unit = f(41)
  operation mk(p: Cell[V = Int64]) -> (u: Int64) -> Unit @ {Modify[p]} = lambda (u: Int64) -> Cell.set(p, Cell.get(p) + u)
  operation sneaky(c: Cell[V = Int64]) -> Unit = run0(c, mk(c))
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let _ = sneaky(c)
    Cell.get(c)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "callback effects admitted by parameter `f` of `wi0rp29.cbv_value_closed.run0` (a \
             closed row)",
            "the argument declares `Modify[T = c]`, which the closed row does not admit",
        ],
        "a call's result writing a cell, into a pure slot",
    );
}

/// A LABEL LEFT NAMING A BINDER AT NO KNOWN POSITION IS REFUSED where the declared row speaks
/// of a binder in the same effect. A lambda taken out of a tuple says no binders: its
/// `Modify[k]` may or may not be the `x` that `-Modify[x]` denies, and nobody states the
/// correspondence — so the call is refused for that, not passed and not refused for a row the
/// callback might satisfy. It LOADED, and wrote the cell under `-Modify[x]` (MEASURED). FAILS
/// under ledger part 65 (refused then as a closed row's — another verdict, on the bracket
/// alone), and under parts 61 and 64 (it loads).
#[test]
fn a_binder_at_no_known_position_is_refused_where_the_row_speaks_of_one() {
    let src = r#"
namespace wi0rp29.cbv_unplaced
  import anthill.prelude.{Int64, String, List, Cell, Modify, Unit, Bool}
  operation app[EffP](q: Cell[V = Int64], f: (x: Cell[V = Int64]) -> Unit @ {EffP, -Modify[x]}) -> Unit effects {EffP} = f(q)
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let (g, n) = (lambda (k: Cell[V = Int64]) -> Cell.set(k, 42), 1)
    let _ = app[EffP = {}](c, g)
    Cell.get(c) + n
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "whose own parameters are known by position",
            "`k` is a parameter of the callback itself, at a position this expression does \
             not say",
        ],
        "a destructured lambda writing its own parameter",
    );
}

/// … AND ITS CONTROL: the same destructured lambda, PURE, names no binder and fits; 41 + 1.
/// Passes either way by design.
#[test]
fn a_binder_at_no_known_position_is_refused_where_the_row_speaks_of_one_control() {
    let src = r#"
namespace wi0rp29.cbv_unplaced_ok
  import anthill.prelude.{Int64, String, List, Cell, Modify, Unit, Bool}
  operation app[EffP](q: Cell[V = Int64], f: (x: Cell[V = Int64]) -> Unit @ {EffP, -Modify[x]}) -> Unit effects {EffP} = f(q)
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(41)
    let (g, n) = (lambda (k: Cell[V = Int64]) -> (), 1)
    let _ = app[EffP = {}](c, g)
    Cell.get(c) + n
end
"#;
    assert_eq!(run_src(src, "wi0rp29.cbv_unplaced_ok.go"), Ok(42));
}

/// A ROW VARIABLE OF THE CALLBACK IS JUDGED UNDER A ROW THAT IS CLOSED once the call's type
/// arguments are applied: a RIGID one — the enclosing operation's own row — cannot be shown
/// empty. The label checks were skipped for every actual row holding a variable, and a
/// callable's row is read by nothing else: `two(pure1, g)` over `g: … @ {Q}` — `pure1` closes
/// the shared row — let `use(boom)` raise out of a `main` typed pure, where `two(g, pure1)` was
/// refused (MEASURED on every build: the verdict turned on the order of the arguments). FAILS
/// under ledger part 66.
#[test]
fn a_callbacks_own_row_variable_is_not_admitted_by_a_closed_row() {
    let src = r#"
namespace wi0rp29.cbv_tail
  import anthill.prelude.{Bool, Int64, Error, List, String}
  sort Foo
    entity foo(n: Int64)
  end
  sort Bar
    entity bar
  end
  operation each2[EffP](f: (x: Int64) -> Bool @ {EffP}) -> Bool effects {EffP} = f(1)
  operation two[EffP](f: (x: Int64) -> Bool @ {EffP}, g: (x: Int64) -> Bool @ {EffP}) -> Bool effects {EffP} = g(1)
  operation closed(f: (x: Int64) -> Bool) -> Bool = f(1)
  operation pure1(x: Int64) -> Bool = true
  operation boom(x: Int64) -> Bool effects {Error[Foo]} = Error.raise(foo(n: 9))
  operation use[Q](g: (x: Int64) -> Bool @ {Q}) -> Bool =
    two(pure1, g)
  operation go() -> Int64 =
    if use(boom) then 1 else 2
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "callback effects admitted by parameter `g` of `wi0rp29.cbv_tail.two` (a closed \
             row)",
            "the callback `g` raises the row `?Q`, the enclosing operation's own and unknown \
             here",
        ],
        "a callback raising the caller's own row into a row an earlier argument closed",
    );
}

/// … AND ITS MIRROR, refused as it always was — the row is then `{Q}`, which the pure `use`
/// does not declare. Passes either way by design: it is the order the earlier builds already
/// refused.
#[test]
fn a_callbacks_own_row_variable_is_not_admitted_by_a_closed_row_mirror() {
    let src = r#"
namespace wi0rp29.cbv_tail_rev
  import anthill.prelude.{Bool, Int64, Error, List, String}
  sort Foo
    entity foo(n: Int64)
  end
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(n: Int64)
  end
  sort Holder
    effects Q2 = ?
    entity holder(f: (x: Int64) -> Bool @ {Q2})
  end
  operation each2[EffP](f: (x: Int64) -> Bool @ {EffP}) -> Bool effects {EffP} = f(1)
  operation two[EffP](f: (x: Int64) -> Bool @ {EffP}, g: (x: Int64) -> Bool @ {EffP}) -> Bool effects {EffP} = g(1)
  operation pure1(x: Int64) -> Bool = true
  operation boom(x: Int64) -> Bool effects {Error[Foo]} = Error.raise(foo(n: 9))
  operation use[Q](g: (x: Int64) -> Bool @ {Q}) -> Bool =
    two(g, pure1)
  operation go() -> Int64 =
    if use(boom) then 1 else 2
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["undeclared effect: ?Q"],
        "the same two arguments in the other order",
    );
}

/// … AND THEIR CONTROL: under a row still OPEN the variable is unification's — `two(g, g)`
/// binds the shared row to `{Q}`, which `use` declares — and runs, to 42. Passes either way by
/// design.
#[test]
fn a_callbacks_own_row_variable_is_not_admitted_by_a_closed_row_control() {
    let src = r#"
namespace wi0rp29.cbv_tail_ok
  import anthill.prelude.{Bool, Int64, Error, List, String}
  operation two[EffP](f: (x: Int64) -> Bool @ {EffP}, g: (x: Int64) -> Bool @ {EffP}) -> Bool effects {EffP} = g(1)
  operation pure1(x: Int64) -> Bool = true
  operation use[Q](g: (x: Int64) -> Bool @ {Q}) -> Bool effects {Q} = two(g, g)
  operation go() -> Int64 =
    if use(pure1) then 42 else 2
end
"#;
    assert_eq!(run_src(src, "wi0rp29.cbv_tail_ok.go"), Ok(42));
}

/// A CALLBACK'S OWN ABSENCES DO NOT SWITCH ITS LABELS OFF. `g: … @ {Error[Foo], -R}` is the
/// very spelling the `-R` refusal asks a forwarder to write; an actual row carrying an absence
/// skipped the label checks whole, so `each2[EffP = {}](g)` passed a callback raising
/// `Error[Foo]` into a closed row and a pure `main` died (MEASURED on every build). FAILS under
/// ledger part 67.
#[test]
fn a_callback_stating_an_absence_is_held_to_a_closed_row() {
    let src = r#"
namespace wi0rp29.cbv_absent_closed
  import anthill.prelude.{Bool, Int64, Error, List, String}
  sort Foo
    entity foo(n: Int64)
  end
  sort Bar
    entity bar
  end
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(n: Int64)
    operation each[EffP](s: Strm, f: (x: Int64) -> Bool @ {EffP, -s.E}) -> Bool effects {EffP} = f(1)
  end
  operation each2[EffP](f: (x: Int64) -> Bool @ {EffP}) -> Bool effects {EffP} = f(1)
  operation noFoo[EffP](f: (x: Int64) -> Bool @ {EffP, -Error[Foo]}) -> Bool effects {EffP} = f(1)
  operation two[EffP](f: (x: Int64) -> Bool @ {EffP}, g: (x: Int64) -> Bool @ {EffP}) -> Bool effects {EffP} = g(1)
  operation pure1(x: Int64) -> Bool = true
  operation boom(x: Int64) -> Bool effects {Error[Foo]} = Error.raise(foo(n: 9))
  operation use[R](s: Strm[T = Int64, E = {R}], g: (x: Int64) -> Bool @ {Error[Foo], -R}) -> Bool =
    each2[EffP = {}](g)
  operation go() -> Int64 =
    let s: Strm[T = Int64, E = {}] = strm(n: 1)
    if use(s, boom) then 1 else 2
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "(a closed row)",
            "the callback `g` declares `Error[T = Foo]`, which the closed row does not admit",
        ],
        "a raising callback that states an absence, into a closed row",
    );
}

/// … AND AGAINST A DENIED LABEL: `noFoo[EffP = {}](g)`, slot `@ {EffP, -Error[Foo]}`. FAILS
/// under ledger part 67.
#[test]
fn a_callback_stating_an_absence_is_held_to_a_denied_label() {
    let src = r#"
namespace wi0rp29.cbv_absent_den
  import anthill.prelude.{Bool, Int64, Error, List, String}
  sort Foo
    entity foo(n: Int64)
  end
  sort Bar
    entity bar
  end
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(n: Int64)
    operation each[EffP](s: Strm, f: (x: Int64) -> Bool @ {EffP, -s.E}) -> Bool effects {EffP} = f(1)
  end
  operation each2[EffP](f: (x: Int64) -> Bool @ {EffP}) -> Bool effects {EffP} = f(1)
  operation noFoo[EffP](f: (x: Int64) -> Bool @ {EffP, -Error[Foo]}) -> Bool effects {EffP} = f(1)
  operation two[EffP](f: (x: Int64) -> Bool @ {EffP}, g: (x: Int64) -> Bool @ {EffP}) -> Bool effects {EffP} = g(1)
  operation pure1(x: Int64) -> Bool = true
  operation boom(x: Int64) -> Bool effects {Error[Foo]} = Error.raise(foo(n: 9))
  operation use[R](s: Strm[T = Int64, E = {R}], g: (x: Int64) -> Bool @ {Error[Foo], -R}) -> Bool =
    noFoo[EffP = {}](g)
  operation go() -> Int64 =
    let s: Strm[T = Int64, E = {}] = strm(n: 1)
    if use(s, boom) then 1 else 2
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "to lack `Error[T = Foo]` (its `-…` lacks-constraint)",
            "the callback `g` declares `Error[T = Foo]`",
        ],
        "a raising callback that states an absence, into a slot denying its label",
    );
}

/// A `Function[A, B, E]` SLOT'S BARE ROW PARAMETER IS THE OPEN ROW `{E}` — the prelude's own
/// spelling. A row binding that is not `effects_rows(…)` was flattened as a legacy list, and a
/// non-list flattens to NOTHING: the slot read as the closed EMPTY row whatever `E` was bound
/// to. Once the validator judged fields and call results, `eachF(h.f)` over a field raising
/// `Error[Foo]` — declared, and inferred for `E` — was refused "(a closed row)" (MEASURED: it
/// ran on every earlier build; an operation or a lambda there was refused on all of them). Runs
/// to 41 + 1. FAILS under ledger part 68.
#[test]
fn a_function_slots_bare_row_parameter_is_an_open_row() {
    let src = r#"
namespace wi0rp29.fn_field
  import anthill.prelude.{Bool, Int64, String, List, Function, Error}
  sort Foo
    entity foo
  end
  sort Holder
    effects Q2 = ?
    entity holder(f: Function[A = Int64, B = Int64, E = {Q2}])
  end
  sort AHolder
    effects Q2 = ?
    entity aholder(f: (x: Int64) -> Int64 @ {Q2})
  end
  operation inc(x: Int64) -> Int64 effects {Error[Foo]} = x + 1
  operation mk() -> (x: Int64) -> Int64 @ {Error[Foo]} = inc
  operation eachF[E](f: Function[A = Int64, B = Int64, E = E]) -> Int64 effects {E} = f(41)
  operation use(h: Holder[Q2 = {Error[Foo]}]) -> Int64 effects {Error[Foo]} = eachF(h.f)
  operation go() -> Int64 effects {Error[Foo]} = use(holder(f: inc))
end
"#;
    assert_eq!(run_src(src, "wi0rp29.fn_field.go"), Ok(42));
}

/// … AND UNDER A BRACKET: `eachF[E = {Error[Foo]}](mk())` reads the row the bracket wrote. Runs
/// to 41 + 1. FAILS under ledger part 68.
#[test]
fn a_function_slots_bare_row_parameter_takes_a_bracket() {
    let src = r#"
namespace wi0rp29.fn_result
  import anthill.prelude.{Bool, Int64, String, List, Function, Error}
  sort Foo
    entity foo
  end
  sort Holder
    effects Q2 = ?
    entity holder(f: Function[A = Int64, B = Int64, E = {Q2}])
  end
  sort AHolder
    effects Q2 = ?
    entity aholder(f: (x: Int64) -> Int64 @ {Q2})
  end
  operation inc(x: Int64) -> Int64 effects {Error[Foo]} = x + 1
  operation mk() -> (x: Int64) -> Int64 @ {Error[Foo]} = inc
  operation eachF[E](f: Function[A = Int64, B = Int64, E = E]) -> Int64 effects {E} = f(41)
  operation use() -> Int64 effects {Error[Foo]} = eachF[E = {Error[Foo]}](mk())
  operation go() -> Int64 effects {Error[Foo]} = use()
end
"#;
    assert_eq!(run_src(src, "wi0rp29.fn_result.go"), Ok(42));
}

/// … AND THEIR CONTROL: `eachF[E = {}](h.f)` from a pure `use` IS a closed row, and the raising
/// field is refused. Passes under every part of this pass — under part 68 for the wrong reason
/// (every such slot read closed) — and FAILS under the earlier part 56 (a field callback not
/// judged at all).
#[test]
fn a_function_slots_bare_row_parameter_is_an_open_row_control() {
    let src = r#"
namespace wi0rp29.fn_closed
  import anthill.prelude.{Bool, Int64, String, List, Function, Error}
  sort Foo
    entity foo
  end
  sort Holder
    effects Q2 = ?
    entity holder(f: Function[A = Int64, B = Int64, E = {Q2}])
  end
  sort AHolder
    effects Q2 = ?
    entity aholder(f: (x: Int64) -> Int64 @ {Q2})
  end
  operation inc(x: Int64) -> Int64 effects {Error[Foo]} = x + 1
  operation mk() -> (x: Int64) -> Int64 @ {Error[Foo]} = inc
  operation eachF[E](f: Function[A = Int64, B = Int64, E = E]) -> Int64 effects {E} = f(41)
  operation use(h: Holder[Q2 = {Error[Foo]}]) -> Int64 = eachF[E = {}](h.f)
  operation go() -> Int64 effects {Error[Foo]} = use(holder(f: inc))
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "(a closed row)",
            "the argument declares `Error[T = Foo]`, which the closed row does not admit",
        ],
        "a raising field callback into a slot the bracket closes",
    );
}

/// A CLOSED ROW THE EXPECTED LABELS COVER IS A SUBSET OF ANY ROW, WHATEVER ITS TAIL STANDS FOR:
/// `{} <: {R}`. The relation answered by BINDING the expected tail, which a rigid one — the
/// caller's own row — refuses: `Strm.each(s, pure1)` over `f: … @ {s.E}` inside `use[R](s:
/// Strm[E = {R}])` was refused, printing two identical arrows (MEASURED: it ran before this
/// ticket read `s.E`). Runs to 1 + 41. FAILS under ledger part 69.
#[test]
fn a_pure_callback_fits_a_slot_whose_row_is_the_callers_own() {
    let src = r#"
namespace wi0rp29.rigid_arrow
  import anthill.prelude.{Int64, Bool, List, Function, Error, String}
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(v: T)
    operation each(s: Strm, f: (x: Int64) -> Int64 @ {s.E}) -> Int64 effects {s.E} = f(1)
  end
  operation pure1(x: Int64) -> Int64 = x + 41
  operation use[R](s: Strm[T = Int64, E = {R}]) -> Int64 effects {R} = Strm.each(s, pure1)
  operation go() -> Int64 =
    let s: Strm[T = Int64, E = {}] = strm(v: 1)
    use(s)
end
"#;
    assert_eq!(run_src(src, "wi0rp29.rigid_arrow.go"), Ok(42));
}

/// … AND THROUGH A `Function` SLOT: `f: Function[A = Int64, B = Int64, E = s.E]`, refused on
/// every build before (MEASURED). Runs to 1 + 41. FAILS under ledger part 69.
#[test]
fn a_pure_callback_fits_a_function_slot_whose_row_is_the_callers_own() {
    let src = r#"
namespace wi0rp29.rigid_fn
  import anthill.prelude.{Int64, Bool, List, Function, Error, String}
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(v: T)
    operation each(s: Strm, f: Function[A = Int64, B = Int64, E = s.E]) -> Int64 effects {s.E} = f(1)
  end
  operation pure1(x: Int64) -> Int64 = x + 41
  operation use[R](s: Strm[T = Int64, E = {R}]) -> Int64 effects {R} = Strm.each(s, pure1)
  operation go() -> Int64 =
    let s: Strm[T = Int64, E = {}] = strm(v: 1)
    use(s)
end
"#;
    assert_eq!(run_src(src, "wi0rp29.rigid_fn.go"), Ok(42));
}

/// `each(s: Strm, f: {slot})` called as `Strm.each(s, {callback})` from `use[R, Q](s: Strm[T =
/// Int64, E = {R, Q}])`, whose row is TWO of the caller's own row parameters.
fn two_own_rows_program(ns: &str, slot: &str, callback: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, List, Function, Error, String}}
  sort Foo
    entity foo(n: Int64)
  end
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(v: T)
    operation each(s: Strm, f: {slot}) -> Int64 effects {{s.E}} = f(1)
  end
  operation pure1(x: Int64) -> Int64 = x + 41
  operation boom(x: Int64) -> Int64 effects {{Error[Foo]}} = Error.raise(foo(n: 9))
  operation use[R, Q](s: Strm[T = Int64, E = {{R, Q}}]) -> Int64 effects {{R, Q}} = Strm.each(s, {callback})
  operation go() -> Int64 =
    let s: Strm[T = Int64, E = {{}}] = strm(v: 1)
    use[R = {{}}, Q = {{}}](s)
end
"#
    )
}

/// … AND WHERE THE CALLER'S OWN ROW IS TWO ROW PARAMETERS: `{} <: {R, Q}`. A union of tails is
/// the multi-tail arm's, which reads no closed actual: both spellings of the slot were refused
/// on the tree the eighth review saw, the arrow's printing two identical arrows (MEASURED). Runs
/// to 1 + 41. FAILS under ledger part 69, and with the shortcut held to a LONE rigid tail.
#[test]
fn a_pure_callback_fits_a_slot_whose_row_is_two_of_the_callers_own() {
    for (tag, slot) in [
        ("arrow", "(x: Int64) -> Int64 @ {s.E}"),
        ("fn", "Function[A = Int64, B = Int64, E = s.E]"),
    ] {
        let ns = format!("wi0rp29.rigid2_{tag}");
        let src = two_own_rows_program(&ns, slot, "pure1");
        assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(42), "{tag}");
    }
}

/// … AND ITS CONTROL: a callback RAISING `Error[Foo]` is no closed row those labels cover, and
/// is refused whatever the tails are. Passes either way by design.
#[test]
fn a_pure_callback_fits_a_slot_whose_row_is_two_of_the_callers_own_control() {
    let src = two_own_rows_program("wi0rp29.rigid2_boom", "(x: Int64) -> Int64 @ {s.E}", "boom");
    assert_refused_naming(
        &load_errors(&src),
        &["type mismatch in each.f (op-arg)"],
        "a raising callback into a slot whose row is the caller's two row parameters",
    );
}
