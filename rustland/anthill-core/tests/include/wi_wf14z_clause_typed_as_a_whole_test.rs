//! WI-20261013-WF14Z (068 C1b) — A CLAUSE IS TYPED AS A WHOLE (068-implementation §6.2,
//! decision 1): one substitution over its variables, from every position that declares a
//! type. Before, only a constructor's application and an operation's or an entity's declared
//! parameters typed a rule variable; the head's written bound, an operation call's result —
//! in a value slot and as the result column of `f(args, ?r)` —, a rule goal's columns and a
//! field read typed nothing, so a dot on the variable they make was data: `rule h1(?a: Int64,
//! ?x) :- ?x <=> ?a.abs()` bound `?x` to the term `-3.abs`.
//!
//! What types a variable, each read after the walk on a copy of the clause's typing and kept
//! only where it fits (`LatePosition`, `settle_late_positions`):
//!
//!   * the head's written bound, the enclosing sort's parameters in it rigid
//!     (`settle_head_bounds`);
//!   * an operation call's result in a slot that declares a type (`CallResult`), a projection
//!     on a parameter read off the argument's type and a type constructor reduced
//!     (`computed_result_type`), the call's written type arguments read (`constrain_application`);
//!   * the result column of `f(args, ?r)` at goal position (`ResultColumn`);
//!   * a rule goal's columns: the callee's, generalized across its clauses and opened fresh
//!     (`rule_goal_columns`), its own head's for a goal on its own relation, nothing for one on
//!     another relation of its cycle (`same_rule_goal_cycle`);
//!   * a dot's value, once its receiver is typed (`DotResult`).
//!
//! Found on the way, and fixed: a typed head's domain check refused a value whose part the
//! bound fixes and the value does not carry (`read_unknowns_from_bound`); a dotted chain on a
//! sigil-free clause parameter was a name, not a field read (`clause_param_field_read`,
//! `clause_param_method_call` in the loader).
//!
//! ## Back-out
//!
//! Each part mutated to a no-op in place under a switch of its own, one build, and this file
//! run under each switch with the modules the change moved (`wi_0rrqp`, `wi_9wvt7`,
//! `wi_p7vp4`, `wi742`, `wi_c7anm`, `wi_9c2pz`, `wi818`, `wi_5g28a`, `wi_x9pb4`, `wi_shed7`,
//! `wi_a3fy2`, `wi_rxt6s`; measured 2026-10-22, the last four rows with this file, `wi_0rrqp`
//! and `wi_9c2pz` only):
//!
//! | backed out | fails |
//! |---|---|
//! | the head's bound (`settle_head_bounds`) | `a_heads_bound_types_its_variable`, `a_field_of_a_head_parameter_is_a_receiver`, `a_field_read_types_the_slot_it_fills`, `a_projection_in_a_result_is_read_off_the_argument`, `a_rule_goal_reads_the_callees_columns`, `wi_0rrqp…::an_inferred_column_is_checked_as_a_written_one`, `wi_p7vp4…::a_member_of_a_sort_that_requires_is_refused_at_rule_variables` |
//! | the enclosing sort's parameter rigid in a bound (`rigidify`) | `wi_0rrqp…::an_inferred_column_is_checked_as_a_written_one` |
//! | a call's result in a value slot (`LatePosition::CallResult`) | `a_calls_result_types_the_slot_it_fills`, `a_projection_in_a_result_is_read_off_the_argument`, `a_rule_goal_reads_the_callees_columns` |
//! | the result column (`LatePosition::ResultColumn`) | `a_calls_result_types_the_slot_it_fills`, four `wi_9wvt7` rows (`a_scoped_kb_does_not_outlive_a_rule_body_call`, `a_clock_read_in_a_rule_body_is_not_performed`, `an_effectful_thunk_leaves_the_goal_undecided`, `the_advised_repairs_answer`) |
//! | a rule goal (`LatePosition::RuleGoal`) | `a_rule_goal_reads_the_callees_columns`, `a_relation_that_calls_itself_reads_its_own_columns`, `a_goal_on_a_relation_of_its_cycle_reads_nothing`, `wi_0rrqp…::a_column_a_rule_goal_types_is_read_at_its_type`, `wi_0rrqp…::a_rule_goal_fixes_what_the_citation_leaves_unfixed`, `wi742…::an_unannotated_column_types_as_its_goal_reads_it`, `wi_c7anm…::the_declared_column_schema_follows_the_written_order` |
//! | a dot's value (`LatePosition::DotResult`) | `a_field_read_types_the_slot_it_fills`, `a_field_of_a_head_parameter_is_a_receiver` |
//! | a call's written type arguments (`constrain_application`) | `a_rule_goal_reads_the_callees_columns`, by `useFr` (`field_access`'s `Name`) |
//! | a projection read off the argument (`computed_result_type`) | `a_projection_in_a_result_is_read_off_the_argument`, `wi818…::sld_head_law_still_proves_once` (the result read as `s.T`, an `eq` refused) |
//! | a type constructor reduced (the same function) | `a_rule_goal_reads_the_callees_columns`, by `useFr` |
//! | a conforming type taking over a call's placeholder (`constrain_var_at`) | `a_projection_in_a_result_is_read_off_the_argument` |
//! | a goal on another relation of the cycle reading nothing (`same_rule_goal_cycle`) | `a_goal_on_a_relation_of_its_cycle_reads_nothing` |
//! | a column that says nothing taking the other clauses' type (`generalize_columns`) | `a_relation_that_calls_itself_reads_its_own_columns`, `a_goal_on_a_relation_of_its_cycle_reads_nothing` |
//! | generalized, the citation's join instead | `two_clauses_that_tie_their_columns_differently_are_generalized` (and github-todo's `open_item`, measured on the first cut) |
//! | a stamp's sort parameter opened per citation (`ClauseTypes::at_citation`) | `wi_0rrqp…::a_head_bound_beside_the_constructor_reads_the_same` |
//! | a value's unknown part read from its bound (`read_unknowns_from_bound`) | `a_typed_head_admits_a_value_whose_part_its_bound_fixes`, `wi_9wvt7_error_reify…::a_generic_boundary_answers_through_a_rule_body` |
//! | the parameter form's field read and method call (`clause_param_field_read`, `clause_param_method_call`), each alone | `a_field_of_a_head_parameter_is_a_receiver` |
//! | the parameter form's bracket refused (`clause_param_method_call`) | `a_bracket_on_a_parameter_forms_method_call_is_refused` |
//! | only a committed goal typing (`collect_occurrence_type_constraints`'s `committed`) | `a_branch_or_a_negation_types_nothing_outside_it` |
//! | a variable a clause types nowhere a fresh column (`clause_goal_columns`) | `a_clause_that_types_a_column_nowhere_says_nothing_of_it` |
//! | a relation being read answering nothing (`rule_goal_columns_in_flight`) | every row: the load overflows the stack |
//! | that set kept apart from the memo, which a stored clause clears | none: no load of `anthill-core`'s suite stores a clause while a relation's columns are read (a panic there under a switch, every row green) |
//!
//! The second part, measured 2026-10-22 with this file, `wi_0rrqp`, `wi_9c2pz`, `wi_s8cbv`,
//! `wi_prva2`, `wi_shed7`, `wi742`, `wi_k4jgc` and `wi_pw9a0` — what a clause's typing recorded
//! then, which the fourth part refuses (a row that recorded nothing loads and answers now),
//! each part backed out alone:
//!
//! | backed out | fails |
//! |---|---|
//! | a column only an unread goal names, told from one nothing names (`GoalColumn::unread`): the old reading, "named by no other column" | `a_column_nothing_in_its_clause_names_is_open` |
//! | the record of a goal that read nothing (`note_unread_goal`) | `a_relation_that_calls_itself_reads_its_own_columns`, `a_goal_on_a_relation_of_its_cycle_reads_nothing`, `a_clause_that_types_a_column_nowhere_says_nothing_of_it` |
//! | a `Term` position typing nothing (`says_nothing_of_a_value`) | `a_term_slot_types_nothing` |
//! | an `Option` parameter the call's placeholder (`constrain_application`) | `an_option_parameter_is_the_calls_placeholder` |
//! | the some-coercion at a placeholder's takeover (`constrain_var_at`'s `WrapSome`) | `an_option_parameter_is_the_calls_placeholder` |
//! | a type written as a term typing nothing (`type_written_as_term`) | `a_bracket_entry_types_nothing` |
//! | a bound naming an unresolved sort read as unwritten; one at a spec (`settle_head_bounds`), each alone | `a_refused_bound_is_read_as_unwritten` |
//! | a position that fits once the sort's parameters vary counted as fixing one (`fits_once_parameters_vary`) | `a_goal_that_fixes_the_sorts_parameter_is_that_class` |
//! | the element a bare value meets an `Option` placeholder as bound to the value's type (`constrain_var_at`) | `what_the_some_coercion_binds_is_the_calls` |
//! | a column of occurrences quoting its argument (`constrain_goal_at_columns`) | `a_column_of_occurrences_quotes_its_argument` |
//! | a collection literal read as its collection, not as the reflect entity it is stored as (`collection_literal_type`) | `a_collection_literal_is_its_collection`: refused at load, `TupleLiteral.x` no such member |
//!
//! The third part, decision 2, measured 2026-10-22 with this file, `wi_jmmhq`, `wi_qhdgc` and
//! `typing_test`, each part backed out alone:
//!
//! | backed out | fails |
//! |---|---|
//! | a construction's argument checked against its field (`argument_fits_field`) | `every_construction_is_typed_against_its_fields` |
//! | a fact's constructions read (`check_fact_constructions`) | `every_construction_is_typed_against_its_fields`, by its fact |
//! | an equation's head not checked as data, in a clause (`walk_clause`) and in the fact sweep (`is_equation`), each alone | `an_equations_head_is_a_rewrite_pattern` (and the first, `an_equations_stored_side_types_nothing`) |
//! | the reflect syntax an equation stores typing nothing (`is_reflect_syntax`) | `an_equations_stored_side_types_nothing` — refused, "contradictory variable types" —, `an_equations_head_is_a_rewrite_pattern` |
//! | a column of no common type of some type (`generalize_columns`) | `a_column_of_no_common_type_is_of_some_type` |
//! | a variable that only demands a type refused there (`demand_only`) | `a_column_of_no_common_type_is_of_some_type` |
//! | `domain` read as a test (`constrain_domain_test`) | `a_column_of_no_common_type_is_of_some_type`, by its `domain` case |
//! | a dot on a value of some type refused (`demands_on_some_type`) | `a_column_of_no_common_type_is_of_some_type`, by its dot |
//! | a parameter of the callee's own type no demand (`constrain_application`) | `a_spec_operations_carrier_takes_a_value_of_some_type` |
//!
//! A goal on its own relation reading the clause's own head was a part too, and no row failed
//! with it backed out: the memo answers nothing for a relation while its clauses are being
//! read, and the relation's columns after, which is the one type the decision asks for. It
//! was removed.
//!
//! The fourth part, decision 3's refusals, measured 2026-10-22 over this file and every module
//! whose rows it rewrote (`wi_0rrqp`, `wi_szkv7`, `wi_shed7`, `wi946`, `wi1096`, `wi936`,
//! `declared_field_type_readers`, `wi742`, `wi_qmfc5`, `wi582`, `wi879`,
//! `resolver_error_channel`, `wi_8y5be`, `wi_jb6rs`, `wi_5g28a_rule_head`, `wi_80zv8`,
//! `wi_m32c2`, `typing_test`, `wi928`, `wi1056`, `wi1104`, `wi_9wvt7`), each part backed out
//! alone:
//!
//! | backed out | fails |
//! |---|---|
//! | a disagreement made a load error (`push_clause_disagreements`) | every refusal row: here `every_construction_is_typed_against_its_fields`, `a_column_of_no_common_type_is_of_some_type`, `a_goal_that_fixes_the_sorts_parameter_is_that_class`, `a_typed_head_admits_a_value_whose_part_its_bound_fixes`; `wi_0rrqp…::a_body_that_fixes_a_sorts_parameter_is_refused`, `…::a_constructor_that_does_not_fit_its_position_is_refused`, `wi_shed7` ×3, `wi1096` ×2, `wi742`, `wi879`, `wi_qmfc5`, `wi_5g28a…::the_tie_refutes_a_mismatched_second_column`, `wi_80zv8` ×2, `declared_field_type_readers…::a_literal_stays_flat_under_a_set_of_a_type_holding_a_value`; the CLI's `resolver_error_render…::the_comparison_written_in_a_clause_is_refused_at_load` and `wi_zz7ph…::one_operation_at_two_carriers_is_two_functions` |
//! | a refusal an earlier check made at a place that holds it reported once (`refused_already`) | `every_construction_is_typed_against_its_fields`, by its three cases an older check refuses too; with the operation's return left out of it (found by /code-review), `a_calls_result_and_a_dot_that_do_not_fit_are_refused`, by WI-1104's spec call |
//! | the fact sweep leaving an entity fact's own fields to the entity-fact check (`check_fact_constructions`) | `wi_szkv7_clause_frontier…::a_refused_files_own_clauses_are_left_alone`, `…::the_clauses_are_what_the_hand_driven_form_of_a_load_hands_the_typer`, `wi_szkv7_later_equality…::a_failed_loads_derived_rows_do_not_refuse_its_corrected_retry` |
//! | a construction read at its position before its fields (`constrain_application`) | `wi_0rrqp…::a_constructor_that_does_not_fit_its_position_is_refused`, `wi_5g28a…::the_tie_refutes_a_mismatched_second_column`, `wi_80zv8` ×2 — each loaded |
//! | a parameter written by its name read as its variable (`parameters_by_their_variable`) | `wi_0rrqp…::a_body_that_fixes_a_sorts_parameter_is_refused`, by `Outer.Inner` |
//! | a rigid parameter taking over a sort's placeholder only by the some-coercion (`constrain_var_at`) | `wi_shed7…::the_parameter_form_of_a_type_variable_bound_is_the_sigil_form`: `Sat.model` loaded |
//! | a disagreement's types read as the whole clause leaves them (`ClauseDisagreement::resolved`) | the same row: `List[T = ?_]` for `List[T = Bit]` |
//! | a sort's parameter named in a message (`parameters_named`) | `a_goal_that_fixes_the_sorts_parameter_is_that_class`, `wi_0rrqp…::a_body_that_fixes_a_sorts_parameter_is_refused`, the same `wi_shed7` row: `expected ?_` |
//! | a namespace-level rule's contradiction reported (`type_rule_bodies`) | `wi_szkv7_clause_frontier…::a_later_calls_namespace_level_rule_gets_the_verdict_one_call_gives_it` |
//! | a refused load's clauses not refused again (`KnowledgeBase::is_clause_of_a_refused_load`; found by /code-review) | `a_refused_loads_clause_does_not_refuse_its_corrected_retry`, by its retry |
//!
//! A field read through the clause's substitution before the provider question
//! (`argument_fits_field`) was found by `wi_m32c2…::control_a_rule_body_call_answers`, refused
//! once the position was read first. The rows rewritten to reach the run time through a goal
//! built at run time, or a value through a `Term` field, pass either way by design: what they
//! drive is the resolver's.
//!
//! The fifth part, decision 1's last row (068-implementation §6.7), measured 2026-10-22 over
//! `wi_0rrqp`, this file, `wi_p7vp4`, `wi_5g28a`, `wi_x9pb4`, `wi_ee0ep`, `wi1094` and
//! `wi_shed7`; its rows are `wi_0rrqp`'s:
//!
//! | backed out | fails |
//! |---|---|
//! | a read a clause variable's named slot states answered by the slot as the citation fixes it (`carried_slot_reading`, then `carried_slot_selection`) | `wi_0rrqp…::a_slot_the_arguments_own_type_says_is_read`, `…::the_slot_is_read_wherever_the_clause_states_its_requirement`, `…::the_arguments_slot_outranks_the_callers_requirement`, `…::each_of_two_slots_on_one_spec_is_read_off_the_argument`, `…::one_provider_or_a_named_parameter_is_read` (by `agree`), `…::a_slot_whose_spec_has_an_element_the_read_leaves_open_is_read` |
//! | the read compared with the slot whole, an element the read leaves open against the slot's (`slot_states_the_read`) | `wi_0rrqp…::a_slot_whose_spec_has_an_element_the_read_leaves_open_is_read`: the citation flounders |
//! | the read's own goal resolved, not the slot's at the citation's types (`carried_slot_selection`) | the same row, the same way |
//! | a slot fixed to the caller's parameter beside one fixed to a witness routing nothing (`carried_slot_selection`'s `undecided`; found by /code-review; refused since the seventh part) | then `two_slots_fixed_to_two_witnesses_route_nothing`, by `twoMixed`; now the seventh part's `TwoProviders` row |
//! | a slot fixed to a witness that does not answer refused at the citation (`settle_citation_routes`; found by /code-review) | `wi_0rrqp…::a_slot_fixed_to_a_witness_that_does_not_answer_is_refused`: the citation loads |
//!
//! Also found by /code-review and driven by no row, passing either way: an element the read
//! leaves open is the read spec's own parameter only (`slot_states_the_read`), and a drift
//! between a sort's declaration order and its chain is a panic, as `carried_slot` makes it.
//!
//! The sixth part, the citation's side of some type and a later load's reading of a woven
//! call (068-implementation §6.8), measured 2026-10-22 over this file, `wi_0rrqp`, `wi741`,
//! `wi_9c2pz` and `wi714`, each part backed out alone:
//!
//! | backed out | fails |
//! |---|---|
//! | a woven call read as its call in the clause walk (`clause_call_parts`) | `a_later_load_reads_a_woven_call_as_its_call` |
//! | two clauses' types with no join a column of some type (`relation_columns_across_clauses`) | `a_column_of_some_type_is_an_unknown_at_each_citation`, `wi741…::wi741_a_genuinely_disjoint_pair_is_still_loud`, `wi741…::wi741_a_concretely_typed_clause_still_out_votes`, `wi_9c2pz…::wi9c2pz_the_inherited_type_reaches_the_published_schema`, `wi714…::wi714_disjoint_concrete_column_types_still_reject` — each refused at the citation, "disjoint types for column" |
//! | a clause's variable of some type making its column one at a citation (`relation_clause_columns`) | `a_column_of_some_type_is_an_unknown_at_each_citation`, by `anyHolds`, which loads |
//! | the same for a rule goal's column (`clause_goal_columns`) | `a_relation_that_passes_a_column_of_some_type_on_is_of_some_type` |
//! | an argument at a column of some type a filter (`relation_reference_type_applied`) | `a_column_of_some_type_is_an_unknown_at_each_citation`, by `mix("a")` |
//! | two clause types of different sorts with no join of some type for a rule goal, a variable in either (`generalize_columns`; found by /code-review) | `two_clauses_of_different_sorts_are_of_some_type_for_a_rule_goal_too` |
//! | a relation at two arities giving its goals no columns (`relation_goal_columns`; found by the typer oracle) | `a_relation_written_at_two_arities_gives_its_goals_no_columns`, by a second refusal; under `ANTHILL_TYPER_ORACLE=1`, `wi_6wvjb…::a_clause_against_an_earlier_loads_clauses_is_refused` |
//!
//! Closing every column whose whole type is a variable, as the nested one is closed, was
//! measured too (the full gate): it refused `wi730…::wi730_negation_over_an_unbound_column_flounders_loudly`,
//! whose column nothing in its clause names and is of every type (§5.3), and — before a woven
//! call was read — `wi_0rrqp…::a_rule_of_an_earlier_load_is_read_by_a_later_one` and
//! `…::a_column_the_citation_gives_no_type_pins_nothing`. 0RRQP's 51 rows of 2026-10-21 refuse
//! nothing now: the clause typing reads a call's result.
//!
//! The seventh part, two slots that may name two providers refused and a dot through another
//! variable's slot (user, 2026-10-22; 068-implementation §6.9), measured 2026-10-22 over
//! `wi_0rrqp`, this file and `wi_ee0ep`, each part backed out alone:
//!
//! | backed out | fails |
//! |---|---|
//! | slots the citation fixes to two providers refused (`carried_slot_reading`'s `TwoProviders`) | `wi_0rrqp…::two_slots_that_may_name_two_providers_are_refused`, by its citations |
//! | an operation body's read through a contested slot refused (`contested_slot_read`) | the same row, by `twoOp` |
//! | a forward of an anonymous requirement through a contested slot refused (`build_dep_projection`) | the same row, by `twoFwd` |
//! | the screen marking the slot it keeps as contested (`op_requires_chain_rc`) | the same row, and `wi_0rrqp…::one_provider_or_a_named_parameter_is_read`, by its message |
//! | a citation of the parameter whose slot the screen dropped refused (`CarriedMisfit::Unheld`) | `wi_0rrqp…::one_provider_or_a_named_parameter_is_read`, by `second`, which loads |
//! | a citation of the parameter whose slot the frame keeps routed to it, contested or not | the same row, by `first`, refused |
//! | a dot through another clause variable's slot dispatched (`find_spec_op_for_clause_slot`) | `wi_0rrqp…::a_dot_through_another_variables_slot_is_the_call`: the term |
//! | the unheld refusal, its other cause a requirement the caller writes (`CarriedMisfit::Unheld`; found by /code-review) | `wi_0rrqp…::a_collision_with_the_callers_requirement_or_a_second_slot_is_refused`, by `Holder`, and `…::one_provider_or_a_named_parameter_is_read`, by `second` |
//! | the body's refusal, at two slots of one parameter's carrier (`contested_slot_read`; found by /code-review) | the same row, by `Semi`, and `…::two_slots_that_may_name_two_providers_are_refused` |
//!
//! Also found by /code-review, and driven by no row of their own: the forward's exemption
//! keyed on the dep being a named slot of the callee's sort, not on the rung alone (an
//! anonymous requirement on a sort that names a slot of the same spec is no argument's); the
//! refusal account keyed on the slot the forward takes; the body check skipped for a frame
//! with no contested slot; the dot rung's chain drift a panic.
//!
//! PASS EITHER WAY, BY DESIGN: `a_constructor_types_its_variable_in_either_goal_order` and
//! `a_dot_on_a_typed_variable_answers_as_its_written_call` (both since WI-20260925-0RRQP),
//! `a_column_nothing_in_its_clause_names_is_read_at_the_type_asked`, and the stated limits at
//! the end of two rows.

const CNT: &str = r#"
  import anthill.prelude.{Int64, Bool, String, List, Option, Result, Error, EmptyStream}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Result.{ok, err}
  import anthill.prelude.Stream.{head}
  sort Cnt
    entity cnt(n: Int64)
    operation bump(c: Cnt) -> Int64 = Int64.add(c.n, 1)
    operation isPos(c: Cnt) -> Bool = true
  end
  import NS.Cnt.{cnt}
  sort Mk
    operation mk4() -> Cnt = cnt(n: 4)
  end
  entity P(t: Int64)
  fact pf(5)
"#;

fn program(ns: &str, body: &str) -> String {
    format!("namespace {ns}\n{CNT}{body}end\n").replace("NS", ns)
}

/// The one definite `Int64` of each unary relation `rules` of `body`'s program.
#[track_caller]
fn ints(ns: &str, body: &str, rules: &[&str]) -> Vec<Option<i64>> {
    let mut kb = crate::common::load_kb_with(&program(ns, body));
    rules
        .iter()
        .map(|r| crate::common::one_definite_int(&mut kb, &format!("{ns}.{r}")))
        .collect()
}

/// CONTROL, PASSES EITHER WAY: a constructor's application typed `?c` before this ticket
/// (WI-20260925-0RRQP), in either goal order.
#[test]
fn a_constructor_types_its_variable_in_either_goal_order() {
    assert_eq!(
        ints(
            "wiwf14z.ctor",
            "  rule a1(?x) :- ?c <=> cnt(n: 4), ?x <=> ?c.bump()\n  \
             rule a2(?x) :- ?x <=> ?c.bump(), ?c <=> cnt(n: 4)\n",
            &["a1", "a2"],
        ),
        [Some(5), Some(5)]
    );
}

/// THE HEAD'S BOUND TYPES ITS VARIABLE: `?a: Int64` makes `?a.abs()` `Int64.abs`, `?c: Cnt`
/// makes `?c.bump()` `Cnt.bump`. Read without the bound, each dot was data: the terms
/// `-3.abs` and `cnt(n: 4).bump`.
#[test]
fn a_heads_bound_types_its_variable() {
    assert_eq!(
        ints(
            "wiwf14z.bound",
            "  rule h1(?a: Int64, ?x) :- ?x <=> ?a.abs()\n  \
             rule q1(?x) :- h1(-3, ?x)\n  \
             rule inner(?c: Cnt, ?x) :- ?x <=> ?c.bump()\n  \
             rule q2(?x) :- inner(cnt(n: 4), ?x)\n",
            &["q1", "q2"],
        ),
        [Some(3), Some(5)]
    );
}

/// A CALL'S RESULT TYPES THE SLOT IT FILLS, in a value slot (`?c <=> Mk.mk4()`: the `T` of
/// `<=>` is `mk4`'s `Cnt`) and as the result column of the goal `Mk.mk4(?c)`. Read without it,
/// `?c.bump()` was the term `cnt(n: 4).bump`.
#[test]
fn a_calls_result_types_the_slot_it_fills() {
    assert_eq!(
        ints(
            "wiwf14z.result",
            "  rule m1(?x) :- ?c <=> Mk.mk4(), ?x <=> ?c.bump()\n  \
             rule m2(?x) :- Mk.mk4(?c), ?x <=> ?c.bump()\n",
            &["m1", "m2"],
        ),
        [Some(5), Some(5)]
    );
}

/// A RULE GOAL READS THE CALLEE'S COLUMNS, typed as its clauses type them — `gen`'s by a
/// constructor, `fr`'s by a field read in a body the dispatch walk has rewritten to
/// `field_access`, whose `FieldOf` result is reduced at the receiver's type. Read without the
/// callee's columns, both dots were data.
#[test]
fn a_rule_goal_reads_the_callees_columns() {
    assert_eq!(
        ints(
            "wiwf14z.goal",
            "  rule gen(?c) :- ?c <=> cnt(n: 4)\n  \
             rule g1(?x) :- gen(?c), ?x <=> ?c.bump()\n  \
             rule fr(?p: P, ?y) :- ?y <=> ?p.t\n  \
             rule useFr(?z) :- fr(P(t: -3), ?y), ?z <=> ?y.abs()\n",
            &["g1", "useFr"],
        ),
        [Some(5), Some(3)]
    );
}

/// A FIELD READ TYPES THE SLOT IT FILLS: `?y <=> ?p.t` makes `?y` the field's `Int64`, in
/// either goal order. Read without it, `?y.abs()` was the term `P(t: -3).t.abs`.
#[test]
fn a_field_read_types_the_slot_it_fills() {
    assert_eq!(
        ints(
            "wiwf14z.field",
            "  rule r1(?p: P, ?x) :- ?y <=> ?p.t, ?x <=> ?y.abs()\n  \
             rule q1(?x) :- r1(P(t: -3), ?x)\n  \
             rule r2(?p: P, ?x) :- ?x <=> ?y.abs(), ?y <=> ?p.t\n  \
             rule q2(?x) :- r2(P(t: -3), ?x)\n",
            &["q1", "q2"],
        ),
        [Some(3), Some(3)]
    );
}

/// A FIELD OF A TYPED HEAD PARAMETER IS A RECEIVER (WI-20261012-RXT6S's note on 7D48J), in
/// the sigil spelling and in the parameter form (kernel-language §5.3, "The parameter form"),
/// where `p.t` reads the field of the variable `p` binds. The sigil-free `(p.t).abs()` was
/// refused, "t.name: expected resolved name", and `p.t.abs()` "names nothing"; the sigil
/// spelling bound the term `P(t: -3).t.abs`.
#[test]
fn a_field_of_a_head_parameter_is_a_receiver() {
    assert_eq!(
        ints(
            "wiwf14z.recv",
            "  rule s1(?p: P, ?x) :- ?x <=> (?p.t).abs()\n  \
             rule s2(p: P, ?x) :- ?x <=> (p.t).abs()\n  \
             rule s3(p: P, ?x) :- ?x <=> p.t.abs()\n  \
             rule s4(p: P, ?x) :- ?y <=> p.t, ?x <=> ?y.abs()\n  \
             rule q1(?x) :- s1(P(t: -3), ?x)\n  \
             rule q2(?x) :- s2(P(t: -3), ?x)\n  \
             rule q3(?x) :- s3(P(t: -3), ?x)\n  \
             rule q4(?x) :- s4(P(t: -3), ?x)\n",
            &["q1", "q2", "q3", "q4"],
        ),
        [Some(3), Some(3), Some(3), Some(3)]
    );
}

/// CONTROL, PASSES EITHER WAY: a dot on a variable a constructor types answers as its
/// written-call twin in a comparison, a goal's argument and as a goal (WI-20261008-A3FY2's
/// note on 7D48J), since WI-20260925-0RRQP.
#[test]
fn a_dot_on_a_typed_variable_answers_as_its_written_call() {
    let ns = "wiwf14z.dot";
    let mut kb = crate::common::load_kb_with(&program(
        ns,
        "  rule e1() :- ?c <=> cnt(n: 4), ?c.bump() = 5\n  \
         rule e2() :- ?c <=> cnt(n: 4), pf(?c.bump())\n  \
         rule e3() :- ?c <=> cnt(n: 4), ?c.isPos()\n",
    ));
    for rule in ["e1", "e2", "e3"] {
        let goal = crate::common::query_pattern_term(&mut kb, &format!("{ns}.{rule}()"));
        let sols = kb.resolve(&[goal], &Default::default());
        assert!(
            sols.len() == 1 && sols[0].is_definite(),
            "{rule}: holds, got {} solutions",
            sols.len()
        );
    }
}

/// A RELATION THAT CALLS ITSELF READS ITS OWN COLUMNS AS ONE TYPE: `reach`'s second clause
/// holds its column at what its own goal reads, so the relation's column is the first
/// clause's `Cnt`. Generalized as a clause that holds at every type, the column typed
/// nothing and `?c.bump()` was data.
#[test]
fn a_relation_that_calls_itself_reads_its_own_columns() {
    assert_eq!(
        ints(
            "wiwf14z.rec",
            "  rule reach(?c) :- ?c <=> cnt(n: 4)\n  \
             rule reach(?c) :- reach(?d), ?c <=> ?d\n  \
             rule useReach(?x) :- reach(?c), ?x <=> ?c.bump()\n",
            &["useReach"],
        ),
        [Some(5)]
    );
}

/// A GOAL ON ANOTHER RELATION OF ITS OWN CYCLE READS NOTHING, so the columns of `ev` and
/// `od` are each read without the other's, whichever is asked first: outside the cycle `ev`'s
/// column is its base clause's `Cnt`, and `od`'s, which only a goal on `ev` fills, is no type.
/// STATED LIMIT: `useOd`'s dot is data. Read through the memo alone, which answers nothing for
/// a relation being typed, each column would depend on which of the two was asked first.
#[test]
fn a_goal_on_a_relation_of_its_cycle_reads_nothing() {
    let ns = "wiwf14z.cycle";
    let mut kb = crate::common::load_kb_with(&program(
        ns,
        "  rule ev(?c) :- ?c <=> cnt(n: 0)\n  \
         rule ev(?c) :- od(?d), ?c <=> ?d\n  \
         rule od(?c) :- ev(?d), ?c <=> ?d\n  \
         rule useEv(?x) :- ev(?c), ?x <=> ?c.bump()\n  \
         rule useOd(?x) :- od(?c), ?x <=> ?c.bump()\n",
    ));
    assert_eq!(
        crate::common::one_definite_int(&mut kb, &format!("{ns}.useEv")),
        Some(1)
    );
    let shown = crate::common::shown_rows(&mut kb, &format!("{ns}.useOd"));
    assert_eq!(
        shown,
        [("cnt(n: 0).bump".to_string(), true)],
        "the dot stays data"
    );
}

/// TWO CLAUSES THAT TIE THEIR COLUMNS DIFFERENTLY ARE GENERALIZED, not joined:
/// `view(some(?d), ?d)` beside `view(none, none)` holds its second column at the first's
/// element in one clause and at an `Option` in the other, so the column is no type, and `desc`
/// answers both of `ob`'s values. Joined as a citation's columns are, the second column was an
/// `Option`, `desc`'s `?d` got that bound, and the `String` was refused — github-todo's
/// `open_item` answered nothing (measured on this ticket's first cut).
#[test]
fn two_clauses_that_tie_their_columns_differently_are_generalized() {
    let ns = "wiwf14z.gen";
    let mut kb = crate::common::load_kb_with(&program(
        ns,
        "  entity ob(v: Option[T = String])\n  \
         fact ob(v: some(\"s\"))\n  \
         fact ob(v: none)\n  \
         rule view(some(?d), ?d) :- true\n  \
         rule view(none, none) :- true\n  \
         rule desc(?d) :- ob(v: ?o), view(?o, ?d)\n",
    ));
    let mut rows: Vec<String> = crate::common::shown_rows(&mut kb, &format!("{ns}.desc"))
        .into_iter()
        .map(|(shown, definite)| {
            assert!(definite, "{shown}: definite");
            shown
        })
        .collect();
    rows.sort();
    assert_eq!(rows, ["\"s\"", "none"]);
}

/// A PROJECTION ON A PARAMETER IN A CALL'S RESULT IS READ OFF THE ARGUMENT'S TYPE: `head(s:
/// Self) -> s.T` at `?l: List[T = Int64]` is an `Int64`. Read as a type of its own the result
/// made `?r` an `s.T`, and an `eq` beside it was refused (`wi818_executable_backing_test`).
///
/// STATED LIMIT, PASSES EITHER WAY: a construction passed where the spec's carrier is
/// declared (`head(cons(7, nil))`) is read at the spec's own parameter, which a `List` does
/// not unify with — so `hd`'s `?r` stays untyped and its dot is data.
#[test]
fn a_projection_in_a_result_is_read_off_the_argument() {
    let ns = "wiwf14z.proj";
    let mut kb = crate::common::load_kb_with(&program(
        ns,
        "  rule hd2(?l: List[T = Int64], ?x) :- ?r <=> head(?l), ?x <=> ?r.abs()\n  \
         rule q(?x) :- hd2(cons(-7, nil), ?x)\n  \
         rule hd(?x) :- ?r <=> head(cons(-7, nil)), ?x <=> ?r.abs()\n",
    ));
    assert_eq!(
        crate::common::one_definite_int(&mut kb, &format!("{ns}.q")),
        Some(7)
    );
    let shown = crate::common::shown_rows(&mut kb, &format!("{ns}.hd"));
    assert_eq!(shown, [("-7.abs".to_string(), true)], "the dot stays data");
}

/// A TYPED HEAD ADMITS A VALUE WHOSE PART ITS BOUND FIXES AND THE VALUE DOES NOT CARRY. Found
/// here: once a call's result column types a column, the column's bound is checked as a
/// written one is, and `Result[T = Int64, E = ?e]` refused `err(error: 5)` — the value says
/// nothing of `T`, and its open type's unknown `T` met `Int64` as a type of its own. The written
/// twins answered nothing before this ticket. CONTROLS: a value its bound does not admit is
/// still refused.
#[test]
fn a_typed_head_admits_a_value_whose_part_its_bound_fixes() {
    let ns = "wiwf14z.dom";
    let mut kb = crate::common::load_kb_with(&program(
        ns,
        "  rule w1(?r: Result[T = Int64, E = ?e]) :- ?r <=> err(error: 5)\n  \
         rule w2(?r: Result[T = ?a, E = Int64]) :- ?r <=> ok(value: 5)\n  \
         rule n1(?r: Result[T = Int64, E = Bool]) :- true\n  \
         rule n2(?r: Result[T = Int64, E = ?e]) :- true\n",
    ));
    for rule in ["w1", "w2"] {
        let rows = crate::common::query_unary(&mut kb, &format!("{ns}.{rule}"));
        assert!(
            rows.len() == 1 && rows[0].1,
            "{rule}: the value, got {rows:?}"
        );
    }
    // A value handed to the head at run time is held to the bound by its check: refused where
    // the bound does not fit it, answered where it does.
    for (rule, value, rows) in [
        ("n1", "err(error: 5)", 0),
        ("n1", "err(error: true)", 1),
        ("n2", "ok(value: \"s\")", 0),
        ("n2", "ok(value: 5)", 1),
    ] {
        let pattern = format!("{ns}.{rule}(anthill.prelude.Result.{value})");
        let goal = crate::common::query_pattern_term(&mut kb, &pattern);
        let got = kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default());
        assert_eq!(got.len(), rows, "{pattern}");
    }
    // The same values a body gives the head are refused at load.
    for (body, says) in [
        (
            "  rule n1(?r: Result[T = Int64, E = Bool]) :- ?r <=> err(error: 5)\n",
            "type mismatch in n1.r (rule-bound): expected Result[E = Bool, T = Int64], got \
             Result[E = Int64, T = ?_]",
        ),
        (
            "  rule n2(?r: Result[T = Int64, E = ?e]) :- ?r <=> ok(value: \"s\")\n",
            "type mismatch in n2.r (rule-bound): expected Result[E = ?e, T = Int64], got \
             Result[E = ?_, T = String]",
        ),
    ] {
        refused(ns, body, says);
    }
}

/// A BRACKET ON A METHOD CALL OF THE PARAMETER FORM IS REFUSED, as on any dot call, which has
/// no channel for one — the refusal the `?p.t.m[…]()` spelling gets. Lowered with its bracket
/// read as an argument, the call could not be built.
#[test]
fn a_bracket_on_a_parameter_forms_method_call_is_refused() {
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program(
            "wiwf14z.bracket",
            "  rule s(p: P, ?x) :- ?x <=> p.t.abs[T = Int64]()\n",
        )),
        &["call-site type arguments are not supported on a dot call"],
        "a bracket on a dot call",
    );
}

/// A BRANCH OR A NEGATION TYPES NOTHING OUTSIDE IT: `pi`'s `Int64` column, read in a `|`
/// branch or under `not`, does not make `?x` an `Int64` for the conjunct beside it, which reads
/// `pc`'s `Cnt`. Read as a conjunct, it typed `?x` first, `pc`'s column disagreed, and the dot
/// was refused as a member `Int64` does not have.
#[test]
fn a_branch_or_a_negation_types_nothing_outside_it() {
    assert_eq!(
        ints(
            "wiwf14z.branch",
            "  fact pi(1)\n  fact pc(cnt(n: 4))\n  \
             rule viaOr(?y) :- (pi(?x) | pc(?x)), pc(?x), ?y <=> ?x.bump()\n  \
             rule viaNot(?y) :- not(pi(?x)), pc(?x), ?y <=> ?x.bump()\n",
            &["viaOr", "viaNot"],
        ),
        [Some(5), Some(5)]
    );
}

/// A CLAUSE THAT TYPES A COLUMN NOWHERE SAYS NOTHING OF IT: `anc`'s second clause names `?e`
/// only in its head and in its goal on `anc`, which reads nothing while `anc` is being read, so
/// the relation's column is the first clause's `Cnt`. Left out of that clause's columns, the
/// slot was dropped from the relation, and `?e.bump()` was data.
#[test]
fn a_clause_that_types_a_column_nowhere_says_nothing_of_it() {
    assert_eq!(
        ints(
            "wiwf14z.ancestry",
            "  entity par(of: Cnt, is: Cnt)\n  \
             fact par(of: cnt(n: 1), is: cnt(n: 2))\n  \
             rule anc(?c, ?e) :- par(of: ?c, is: ?e)\n  \
             rule anc(?c, ?e) :- par(of: ?c, is: ?m), anc(?m, ?e)\n  \
             rule useAnc(?x) :- anc(?a, ?e), ?x <=> ?e.bump()\n",
            &["useAnc"],
        ),
        [Some(3)]
    );
}

/// A COLUMN OF SOME TYPE IS AN UNKNOWN AT EACH CITATION (068-implementation §6.8): a value
/// read from it goes where any type is taken — `takeN(5).length()` counts both solutions, and
/// an argument there is a filter, `mix("a")` holding the one at `"a"` — and a use that asks
/// for one type is refused. A rule that takes `holds`'s column (`anyHolds`) holds its values,
/// and two rule clauses that type `mix`'s at `Int64` and `String` have no join. Before, the
/// first was a variable read at the type its use asked for — `anyHolds.head.x` loaded
/// returned as an `Int64` and answered one of the two values — and the second was refused at the
/// citation, "disjoint types for column `v`". FAILS with the clause's own reading backed out
/// (`some` in `relation_clause_columns`): the `anyHolds` refusal, which loads; with the
/// join's backed out (`relation_columns_across_clauses`): every `mix` citation, refused
/// "disjoint types for column `v`"; with an argument there checked against the unknown
/// (`relation_reference_type_applied`): `mix("a")`, refused "argument binding column `v` has
/// an incompatible type".
#[test]
fn a_column_of_some_type_is_an_unknown_at_each_citation() {
    let ns = "wiwf14z.whole";
    let decls = "  fact holds(1)\n  fact holds(\"a\")\n  rule anyHolds(?x) :- holds(?x)\n  \
                 fact isInt(1)\n  fact isStr(\"a\")\n  \
                 rule mix(?v, ?k) :- isInt(?v), ?k <=> 1\n  rule mix(?v, ?k) :- isStr(?v), ?k <=> 2\n";
    let mut interp = crate::common::interp_for(&program(
        ns,
        &format!(
            "{decls}  \
             operation passed() -> Int64 effects {{Error, Error[EmptyStream]}} = anyHolds.takeN(5).length()\n  \
             operation joined() -> Int64 effects {{Error, Error[EmptyStream]}} = mix.takeN(5).length()\n  \
             operation filtered() -> Int64 effects {{Error, Error[EmptyStream]}} = mix(\"a\").head.k\n"
        ),
    ));
    let at = |interp: &mut anthill_core::eval::Interpreter, op: &str| match interp
        .call(&format!("{ns}.{op}"), &[])
    {
        Ok(anthill_core::eval::Value::Int(n)) => n,
        other => panic!("{op}: {other:?}"),
    };
    assert_eq!(
        [at(&mut interp, "passed"), at(&mut interp, "joined"), at(&mut interp, "filtered")],
        [2, 2, 2]
    );
    for (shape, op, says) in [
        (
            "a rule over a column of some type",
            "anyHolds.head.x",
            "type mismatch in f.return (op-return): expected Int64, got ?x",
        ),
        (
            "two clauses with no join",
            "mix.head.v",
            "type mismatch in f.return (op-return): expected Int64, got ?v",
        ),
    ] {
        let errors = crate::common::load_errors_of(&program(
            ns,
            &format!("{decls}  operation f() -> Int64 effects {{Error, Error[EmptyStream]}} = {op}\n"),
        ));
        assert!(errors.len() == 1 && errors[0].contains(says), "{shape}: {errors:#?}");
    }
}

/// CONTROL, PASSES EITHER WAY: a column nothing in its clause names is of every type (§5.3),
/// and a citation reads it at the type its use asks for — `loose.head.other` returned as a
/// `String` loads and answers the solution's unbound value, and an argument there binds it,
/// `loose(1, "zed")` holding the one solution — where a column of some type is refused.
#[test]
fn a_column_nothing_in_its_clause_names_is_read_at_the_type_asked() {
    let ns = "wiwf14z.every";
    let src = program(
        ns,
        "  fact isInt(1)\n  rule loose(?n, ?other) :- isInt(?n)\n  \
         operation f() -> String effects {Error, Error[EmptyStream]} = loose.head.other\n  \
         operation g() -> Int64 effects {Error, Error[EmptyStream]} = loose(1, \"zed\").takeN(5).length()\n",
    );
    let mut interp = crate::common::interp_for(&src);
    assert!(
        matches!(interp.call(&format!("{ns}.f"), &[]), Ok(anthill_core::eval::Value::Var(_))),
        "the column's value is the solution's unbound variable"
    );
    let mut interp = crate::common::interp_for(&src);
    assert!(matches!(
        interp.call(&format!("{ns}.g"), &[]),
        Ok(anthill_core::eval::Value::Int(1))
    ));
}

// ── The clause typing made exact (068-implementation §6.4) ──────────────────────────────
//
// A position the operation-body typer accepts, and whose clause answers at run time, is
// accepted here too; one it refuses is refused (decision 3, §6.6). Each row below loads and
// answers, or is refused with the one error it names.

/// The one refusal `body`'s program gets, which names `says`.
#[track_caller]
fn refused(ns: &str, body: &str, says: &str) {
    let errors = crate::common::load_errors_of(&program(ns, body));
    assert!(
        errors.len() == 1 && errors[0].contains(says),
        "one refusal naming `{says}`, got {errors:#?}"
    );
}

/// A COLUMN WHOSE VARIABLE NOTHING IN ITS CLAUSE NAMES IS OPEN: `classify`'s second clause
/// takes every `?x`, so `classify(5, ?r)` loads and answers through it. Read as the other
/// clause's `Colour` — what a goal on the relation itself leaves unsaid — the goal was a
/// rule-goal disagreement.
#[test]
fn a_column_nothing_in_its_clause_names_is_open() {
    assert_eq!(
        ints(
            "wiwf14z.open",
            "  sort Colour\n    entity red\n  end\n  \
             rule classify(?x: Colour, ?c) :- ?c <=> 1\n  \
             rule classify(?x, ?c) :- ?c <=> 2\n  \
             rule g(?r) :- classify(5, ?r)\n",
            &["g"],
        ),
        [Some(2)]
    );
}

/// A `Term` SLOT TYPES NOTHING, as an operation's argument converts any value to the `Term`
/// it declares: `takes`'s column is `nonvar`'s parameter, and `5` and an `Int64` variable meet
/// it. Typed `Term`, the variable disagreed with every other position.
#[test]
fn a_term_slot_types_nothing() {
    assert_eq!(
        ints(
            "wiwf14z.term",
            "  rule takes(?g) :- anthill.reflect.nonvar(?g)\n  \
             rule viaLit(?r) :- takes(5), ?r <=> 1\n  \
             rule viaVar(?r) :- takes(?x), ?x <=> -5, ?r <=> Int64.abs(?x)\n",
            &["viaLit", "viaVar"],
        ),
        [Some(1), Some(5)]
    );
}

/// AN `Option` PARAMETER IS THE CALL'S PLACEHOLDER: a bare `Int64` meets it as an operation's
/// argument does, by the some-coercion, and the variable stays the head's `Int64`. Read as
/// the variable's type, the head's bound disagreed with it. The call runs on the bare value —
/// a rule-body call does not wrap it, which is WI-20261013-R1W5A's (C1c types the call as an
/// operation body is); `len` here does not read its argument.
#[test]
fn an_option_parameter_is_the_calls_placeholder() {
    assert_eq!(
        ints(
            "wiwf14z.option",
            "  sort Opt\n    operation len(o: Option[T = Int64]) -> Int64 = 1\n  end\n  \
             rule viaHead(?a: Int64, ?r) :- ?r <=> Opt.len(?a)\n  \
             rule g(?r) :- viaHead(3, ?r)\n",
            &["g"],
        ),
        [Some(1)]
    );
}

/// A BRACKET ENTRY IS NO DATA: `p.E` in `require[Desc[T = p.E]]` is a projection written as a
/// term, and the head parameter in it is not typed at its `value` field (`NodeOccurrence`).
/// Typed there, the head's bound `Box` disagreed with it.
#[test]
fn a_bracket_entry_types_nothing() {
    assert_eq!(
        ints(
            "wiwf14z.bracketentry",
            "  sort Desc\n    sort T = ?\n    operation tag() -> Int64\n  end\n  \
             sort Red\n    import anthill.prelude.Int64\n    entity red\n    \
             provides Desc[T = Red]\n    operation tag() -> Int64 = 7\n  end\n  \
             sort Box\n    sort E = ?\n    entity box(v: E)\n  end\n  \
             rule anchored(p: Box, ?r) :- ?d = require[Desc[T = p.E]], Desc.tag(?r)\n  \
             rule g(?r) :- anchored(box(v: red()), ?r)\n",
            &["g"],
        ),
        [Some(7)]
    );
}

/// A BOUND THE LOADER REFUSES IS READ AS UNWRITTEN: one naming a sort that does not resolve,
/// and one at a spec over its parameter, are each refused once where they are written, and
/// the clause typing reads neither. Read, each disagreed with the column `item` gives the
/// variable.
#[test]
fn a_refused_bound_is_read_as_unwritten() {
    let ns = "wiwf14z.refusedbound";
    for (bound, refusal) in [
        ("NoSuchSortAnywhere", "unresolved name 'NoSuchSortAnywhere'"),
        ("Sizer", "a rule variable is typed `wiwf14z.refusedbound.Sizer`"),
    ] {
        refused(
            ns,
            &format!(
                "  sort Sizer\n    sort T = ?\n    operation size(a: T) -> Int64\n  end\n  \
                 fact item(1)\n  rule f(?x: {bound}) :- item(?x)\n"
            ),
            refusal,
        );
    }
}

/// A BODY THAT FIXES THE SORT'S PARAMETER THROUGH A GOAL is refused naming the parameter, as
/// through a construction: `bx` answers only `Box2[T = Int64]` values, where `pr` holds at
/// every `T`. Refused as a rule-goal disagreement before it was told apart.
#[test]
fn a_goal_that_fixes_the_sorts_parameter_is_that_class() {
    refused(
        "wiwf14z.fixedbygoal",
        "  rule bx(?x) :- ?x <=> NS.Box2.b2(v: 5)\n  \
         sort Box2[T]\n    entity b2(v: T)\n    rule pr(?x: Box2[T = T]) :- bx(?x)\n  end\n",
        "type mismatch in Box2.T (sort-parameter): expected T, got Int64",
    );
}

/// A COLLECTION LITERAL IS ITS COLLECTION: `item`'s facts hold the tuples `(x: 1)` and `(x:
/// true)`, and `f`'s bound `(x: Int64)` reads the one that fits with nothing recorded; `viaBody`
/// builds `(x: 1)` and `viaHead` reads one out of `mk`'s head, each handed to `pair`'s column
/// `(x: Int64)`; `one`'s column is the tuple `(x: Int64)`, so the field read on the value
/// `viaDot` reads out of it is an `Int64`'s, and `abs` answers. Read as the reflect
/// `TupleLiteral` entity a tuple is stored as, the fact's column and `mk`'s each disagreed
/// with the bound, and the field read was refused, a member `TupleLiteral` does not have.
#[test]
fn a_collection_literal_is_its_collection() {
    let ns = "wiwf14z.literal";
    let answers = {
        let mut kb = crate::common::load_kb_with(&program(
            ns,
            "  fact item((x: 1))\n  fact item((x: true))\n  \
             rule f(?x: (x: Int64)) :- item(?x)\n  \
             rule pair(?p: (x: Int64)) :- true\n  \
             rule viaBody(?r) :- ?t <=> (x: 1), pair(?t), ?r <=> 1\n  \
             rule mk((x: ?a)) :- ?a <=> 1\n  \
             rule viaHead(?r) :- mk(?t), pair(?t), ?r <=> 1\n  \
             fact one((x: -3))\n  \
             rule viaDot(?r) :- one(?t), ?r <=> ?t.x.abs()\n",
        ));
        (
            crate::common::query_unary(&mut kb, &format!("{ns}.f")).len(),
            crate::common::one_definite_int(&mut kb, &format!("{ns}.viaBody")),
            crate::common::one_definite_int(&mut kb, &format!("{ns}.viaHead")),
            crate::common::one_definite_int(&mut kb, &format!("{ns}.viaDot")),
        )
    };
    assert_eq!(answers, (1, Some(1), Some(1), Some(3)));
}

/// WHAT THE SOME-COERCION BINDS IS THE CALL'S: `?a: Int64` meets `pick`'s `Option[T = A]`
/// as its element, so `A` is `Int64`, and `?b`, at `A`, is an `Int64` — the dot on it is
/// `Int64.abs`. Kept only as the check's verdict, `A` stayed open and the dot was data.
#[test]
fn what_the_some_coercion_binds_is_the_calls() {
    assert_eq!(
        ints(
            "wiwf14z.coercionbinds",
            "  sort Opt2\n    operation pick[A](x: Option[T = A], y: A) -> A = y\n  end\n  \
             rule viaPick(?a: Int64, ?b, ?r) :- ?c <=> Opt2.pick(?a, ?b), ?r <=> ?b.abs()\n  \
             rule g(?r) :- viaPick(3, -4, ?r)\n",
            &["g"],
        ),
        [Some(4)]
    );
}

/// A COLUMN OF OCCURRENCES QUOTES ITS ARGUMENT (user, 2026-10-22): `synth_int`'s column is
/// `occurrence_term`'s `NodeOccurrence`, and `synth_int(42, ?n)` reads `42`'s occurrence.
/// Met as a type, `42`'s `Int64` disagreed with the column. The operation-body twin, `q(42)`
/// at `e: NodeOccurrence`, stays refused.
#[test]
fn a_column_of_occurrences_quotes_its_argument() {
    assert_eq!(
        ints(
            "wiwf14z.occurrence",
            "  import anthill.reflect.{occurrence_term}\n  \
             import anthill.reflect.Expr.{int_lit}\n  \
             rule synth_int(?e, 1) :- occurrence_term(?e, int_lit(value: ?))\n  \
             rule g(?n) :- synth_int(42, ?n)\n",
            &["g"],
        ),
        [Some(1)]
    );
}

// ── Decision 2: how far data is typed (068-implementation §6.2) ───────────────────────────

/// Decision 2's table fixture: `pt`'s two `Int64` fields, `Hold.holder` over a `pt`, `holds`'
/// three facts of no common type, and `U`'s operations at a value of each.
const DATA: &str = "  import anthill.kernel.{domain}\n  entity pt(x: Int64, y: Int64)\n  entity wrap(v: Int64)\n  \
    sort Hold\n    entity holder(h: pt)\n  end\n  import NS.Hold.{holder}\n  \
    sort U\n    operation ilen(n: Int64) -> Int64 = n\n    operation px(p: pt) -> Int64 = p.x\n  end\n  \
    fact holds(1)\n  fact holds(\"a\")\n  fact holds(pt(x: 1, y: 2))\n";

/// EVERY CONSTRUCTION IS TYPED AGAINST ITS FIELDS, in a fact, a head and a body — each
/// refused naming the field, once. Before, only a fact of the entity itself and a body goal on
/// it were checked: these loaded, and the `<=>` ones bound the ill-typed value. Where an
/// earlier check refuses the field at the construction — a fact of the entity, a body goal
/// on it, an `=` operand — that check's is the one refusal.
#[test]
fn every_construction_is_typed_against_its_fields() {
    for (shape, clause, got) in [
        ("a fact's field", "  fact holder(h: pt(x: \"s\", y: 2))\n", "String"),
        ("a head", "  rule hh(pt(x: \"s\", y: 2)) :- true\n", "String"),
        ("a `<=>` side", "  rule g(?r) :- ?r <=> pt(x: \"s\", y: 2)\n", "String"),
        ("a nested construction", "  rule g(?r) :- ?r <=> pt(x: wrap(v: 1), y: 2)\n", "wrap"),
        ("a relation goal's argument", "  rule g(?a) :- holds(pt(x: \"s\", y: 2)), ?a <=> 1\n", "String"),
        ("a fact of the entity", "  fact pt(x: \"s\", y: 2)\n", "String"),
        ("a body goal on another", "  rule g(?a) :- holder(h: pt(x: \"s\", y: 2)), ?a <=> 1\n", "String"),
        ("an `=` operand", "  rule g(?r) :- ?r = pt(x: \"s\", y: 2)\n", "String"),
    ] {
        let errors = crate::common::load_errors_of(&program(
            "wiwf14z.construction",
            &format!("{DATA}{clause}"),
        ));
        let says = format!("type mismatch in pt.x (entity-field): expected Int64, got {got}");
        assert!(
            errors.len() == 1 && errors[0].contains(&says),
            "{shape}: {errors:#?}"
        );
    }
}

/// CONTROL, PASSES EITHER WAY: a construction that fits loads, the argument conversions
/// included — a bare value at an `Option` field, any value at a `Term` field.
#[test]
fn a_construction_that_fits_loads() {
    crate::common::load_kb_with(&program(
        "wiwf14z.fits",
        &format!(
            "{DATA}  entity maybe(o: Option[T = Int64])\n  \
             entity quoted(t: anthill.reflect.Term)\n  \
             fact holder(h: pt(x: 1, y: 2))\n  \
             rule g(?r) :- ?r <=> pt(x: 1, y: 2)\n  \
             rule m(?r) :- ?r <=> maybe(o: 3)\n  rule q(?r) :- ?r <=> quoted(t: \"s\")\n"
        ),
    ));
}

/// A COLUMN OF NO COMMON TYPE IS OF SOME TYPE: `holds` answers its three values, and a demand
/// on a value read out of it — a call's argument, a dot — is refused until a test narrows it:
/// `domain`, `<=>` against a construction, a head's bound. A column two rule clauses give
/// different types is one too. Before, the column was a variable and every demand read the
/// value at the type it asked for: `ilen` handed back a `String` as an `Int64`.
#[test]
fn a_column_of_no_common_type_is_of_some_type() {
    let ns = "wiwf14z.some";
    // (shape, clause, how many rows `g` answers)
    for (shape, clause, rows) in [
        ("read", "  rule g(?r) :- holds(?r)\n", 3),
        ("narrowed by `domain`", "  rule g(?r) :- holds(?v), domain(?v, Int64), ?r <=> U.ilen(?v)\n", 1),
        ("narrowed by `<=>`", "  rule g(?r) :- holds(?v), ?v <=> pt(x: ?a, y: ?), ?r <=> U.px(?v)\n", 1),
        ("narrowed by a head's bound", "  rule n(?v: Int64, ?r) :- holds(?v), ?r <=> U.ilen(?v)\n  rule g(?r) :- n(?v, ?r)\n", 1),
        ("typed by a later goal", "  fact one(1)\n  rule g(?r) :- holds(?v), one(?v), ?r <=> U.ilen(?v)\n", 1),
    ] {
        let mut kb = crate::common::load_kb_with(&program(ns, &format!("{DATA}{clause}")));
        let got = crate::common::query_unary(&mut kb, &format!("{ns}.g")).len();
        assert_eq!(got, rows, "{shape}");
    }
    let some = "got a value of some type: `holds._1` has no type its clauses share; a test \
                narrows `v` first — `domain`, `<=>` against a construction or a literal, a \
                head's bound";
    for (shape, clause, says) in [
        (
            "a call's argument",
            "  rule g(?r) :- holds(?v), ?r <=> U.ilen(?v)\n".to_string(),
            format!("type mismatch in ilen.n (op-arg): expected Int64, {some}"),
        ),
        (
            "a dot",
            "  rule g(?r) :- holds(?v), ?r <=> ?v.abs()\n".to_string(),
            format!(
                "type mismatch in <dot projection>.abs (dot-projection): expected a receiver \
                 of a known type, {some}"
            ),
        ),
        (
            "two rule clauses",
            "  fact isInt(1)\n  fact isStr(\"a\")\n  \
             rule mix(?v) :- isInt(?v)\n  rule mix(?v) :- isStr(?v)\n  \
             rule g(?r) :- mix(?v), ?r <=> U.ilen(?v)\n"
                .to_string(),
            format!("type mismatch in ilen.n (op-arg): expected Int64, {some}")
                .replace("holds._1", "mix._1"),
        ),
    ] {
        let errors = crate::common::load_errors_of(&program(ns, &format!("{DATA}{clause}")));
        assert!(
            errors.len() == 1 && errors[0].contains(&says),
            "{shape}: {errors:#?}"
        );
    }
}

/// A SPEC OPERATION'S CARRIER TAKES A VALUE OF SOME TYPE: `Desc.describe(?x, ?r)` is
/// dispatched by each value's own sort, so `item`'s `leaf` and `other` answer `7` and `9` — a
/// parameter of the callee's own type is no demand. Read as one, the call was refused as a
/// demand on an un-narrowed value.
#[test]
fn a_spec_operations_carrier_takes_a_value_of_some_type() {
    let ns = "wiwf14z.carrier";
    let rows = {
        let mut kb = crate::common::load_kb_with(&program(
            ns,
            "  sort Desc\n    sort T = ?\n    operation describe(x: T) -> Int64\n  end\n  \
             sort Leaf\n    import anthill.prelude.Int64\n    entity leaf\n    \
             provides Desc[T = Leaf]\n    operation describe(x: Leaf) -> Int64 = 7\n  end\n  \
             sort Other\n    import anthill.prelude.Int64\n    entity other\n    \
             provides Desc[T = Other]\n    operation describe(x: Other) -> Int64 = 9\n  end\n  \
             fact item(leaf())\n  fact item(other())\n  \
             rule g(?r) :- item(?x), Desc.describe(?x, ?r)\n",
        ));
        let mut got: Vec<Option<i64>> = crate::common::query_unary(&mut kb, &format!("{ns}.g"))
            .into_iter()
            .map(|(v, _)| match v {
                anthill_core::eval::Value::Int(i) => Some(i),
                _ => None,
            })
            .collect();
        got.sort();
        got
    };
    assert_eq!(rows, [Some(7), Some(9)]);
}

/// AN EQUATION'S HEAD IS A REWRITE PATTERN, NOT DATA: its sides are stored as the reflect
/// terms that write them, which the construction check does not read — a bodyless `@[simp]`
/// equation and a guarded one, each with a field read on its right, load. Read as data, each
/// was refused inside the stored `?b.v`.
#[test]
fn an_equations_head_is_a_rewrite_pattern() {
    crate::common::load_kb_with(&program(
        "wiwf14z.equation",
        "  sort Box\n    entity box(v: Int64)\n    operation open(b: Box) -> Int64\n    \
         operation peek(b: Box) -> Int64\n    \
         rule open(?b) <=> ?b.v @[simp]\n    \
         rule peek(?b) = ?b.v :- gt(1, 0) @[simp]\n  end\n  \
         import anthill.prelude.PartialOrd.{gt}\n",
    ));
}

/// AN EQUATION'S STORED SIDE TYPES NOTHING: `peek(?b) = ?b.v :- gt(1, 0)` keeps `?b.v` as the
/// reflect `dot_apply(receiver: ?b, …)`, and `?b` is `peek`'s `Box`, not the receiver field's
/// type — so the equation loads and `go()` rewrites to the field, `3`. Read as data, `?b`
/// had two declared types and the rule was refused, "contradictory variable types", on the
/// tree before WF14Z too.
#[test]
fn an_equations_stored_side_types_nothing() {
    let ns = "wiwf14z.storedside";
    assert_eq!(
        ints(
            ns,
            "  import anthill.prelude.PartialOrd.{gt}\n  \
             sort Box\n    entity box(v: Int64)\n    operation peek(b: Box) -> Int64\n    \
             rule peek(?b) = ?b.v :- gt(1, 0) @[simp]\n  end\n  \
             operation go() -> Int64 = Box.peek(Box.box(v: 3))\n  \
             rule r(?x) :- ?x <=> go()\n",
            &["r"],
        ),
        [Some(3)]
    );
}

/// A FIELD'S NAME IS A `String` IN EVERY `FieldInfo` (user, 2026-10-22): `KB.fields` hands
/// one back, and so do the loader's own records — an operation's parameter (`zebra`) and an
/// entity's field (`quokka`), each read by a rule that asks for the name as written; and a
/// clause comparing `KB.fields` with `FieldInfo(name: "x", …)` loads. The loader stored the
/// field's symbol, which no string matches, and `FieldInfo.name` was declared a `Symbol`,
/// which `"x"` does not fit.
#[test]
fn a_fields_name_is_a_string_in_every_field_info() {
    let ns = "wiwf14z.fieldinfo";
    let rows = {
        let mut kb = crate::common::load_kb_with(&program(
            ns,
            "  import anthill.reflect.{FieldInfo, OperationInfo, EntityInfo, KB}\n  \
             entity onlyQ(quokka: Int64)\n  \
             sort Z\n    operation onlyZ(zebra: Int64) -> Int64 = zebra\n  end\n  \
             rule param(?n) :- OperationInfo(name: ?, params: [FieldInfo(name: ?n, type_name: ?)]), ?n <=> \"zebra\"\n  \
             rule field(?n) :- EntityInfo(name: ?, fields: [FieldInfo(name: ?n, type_name: ?)]), ?n <=> \"quokka\"\n  \
             rule listed(1) :- KB.fields(KB.kb(), onlyQ[]) <=> [FieldInfo(name: \"quokka\", type_name: ?)]\n",
        ));
        ["param", "field", "listed"].map(|r| {
            crate::common::query_unary(&mut kb, &format!("{ns}.{r}")).len()
        })
    };
    assert_eq!(rows, [1, 1, 1]);
}

/// A CALL'S RESULT, A RESULT COLUMN AND A DOT THAT DO NOT FIT ARE REFUSED, each once, at the
/// operation's return or the member, as an operation's return is read against what its body
/// gives: `?r: String` beside `sign`'s `Int64`, in a value slot and as the result column, and
/// beside `P.t`. A spec operation's result column is WI-1104's refusal at the call, which the
/// clause typing does not report again. Before, each loaded, the position pinning nothing.
#[test]
fn a_calls_result_and_a_dot_that_do_not_fit_are_refused() {
    let ns = "wiwf14z.results";
    let decls = "  sort U\n    operation sign(a: Int64) -> Int64 = a\n  end\n  \
                 sort Desc\n    sort T = ?\n    operation describe(x: T) -> Int64\n  end\n  \
                 sort Leaf\n    import anthill.prelude.Int64\n    entity leaf\n    \
                 provides Desc[T = Leaf]\n    operation describe(x: Leaf) -> Int64 = 7\n  end\n";
    for (clause, says) in [
        ("rule cr(?r: String) :- ?r <=> U.sign(3)", "sign.return (op-return): expected Int64, got String"),
        ("rule rc(?r: String) :- U.sign(3, ?r)", "sign.return (op-return): expected Int64, got String"),
        ("rule dr(?p: P, ?r: String) :- ?r <=> ?p.t", "<dot projection>.t (dot-projection): expected Int64, got String"),
        ("rule sc(?r) :- Desc.describe(leaf(), \"s\")", "describe.return (op-return): expected Int64, got String"),
    ] {
        refused(ns, &format!("{decls}  {clause}\n"), says);
    }
}

/// A REFUSED LOAD'S CLAUSE DOES NOT REFUSE ITS CORRECTED RETRY, and a later load is held to
/// every other clause as one load over everything is. The refused load's clauses stay in the
/// knowledge base, and the clause typing reads every rule a seal does not hold at each load:
/// read as the later load's, the refused `g` and `bad` refused the retry too, a contradiction
/// of a namespace-level rule included. Kept to the load that asserted it instead, a clause an
/// earlier load typed clean was not refused where a later load's fact made its column of no
/// common type, which one load over both refuses.
#[test]
fn a_refused_loads_clause_does_not_refuse_its_corrected_retry() {
    use crate::common::{load_in_a_later_call, rendered_load_errors};
    let ns = "wiwf14z.retry";
    let mut kb = crate::common::load_kb_with(&program(ns, "  entity pt(x: Int64, y: Int64)\n"));
    let refused = load_in_a_later_call(
        &mut kb,
        &format!(
            "namespace {ns}.bad\n  import anthill.prelude.{{Int64, String}}\n  \
             import {ns}.{{pt}}\n  sort U\n    operation slen(s: String) -> Int64 = 1\n  end\n  \
             rule g(?r) :- ?r <=> pt(x: \"s\", y: 2)\n  \
             rule bad(?r) :- pt(x: ?a, y: 2) <=> ?p, U.slen(?a, ?r)\nend\n"
        ),
        Default::default(),
    );
    let errors = rendered_load_errors(refused.err().expect("the ill-typed clauses fail the load"));
    assert!(
        errors.len() == 2
            && errors[0].contains("type mismatch in pt.x (entity-field)")
            && errors[1].contains("contradictory variable types"),
        "{errors:#?}"
    );
    let retry = load_in_a_later_call(
        &mut kb,
        &format!("namespace {ns}.good\n  import {ns}.{{pt}}\n  rule g(?r) :- ?r <=> pt(x: 1, y: 2)\nend\n"),
        Default::default(),
    );
    assert!(retry.is_ok(), "{:?}", retry.err().map(rendered_load_errors));

    let first = "namespace wiwf14z.later\n  import anthill.prelude.{Int64, String}\n  \
                 sort U\n    operation ilen(n: Int64) -> Int64 = n\n  end\n  \
                 fact holds(1)\n  rule g(?r) :- holds(?v), ?r <=> U.ilen(?v)\nend\n";
    let mut kb = crate::common::load_kb_with(first);
    let later = load_in_a_later_call(
        &mut kb,
        "namespace wiwf14z.later\n  fact holds(\"a\")\nend\n",
        Default::default(),
    );
    let errors = rendered_load_errors(later.err().expect("the later fact changes `g`'s column"));
    assert!(
        errors.len() == 1 && errors[0].contains("type mismatch in ilen.n (op-arg)"),
        "{errors:#?}"
    );
}

// ── The citation's side of some type, and a later load (068-implementation §6.8) ────────

/// A RELATION THAT PASSES A COLUMN OF SOME TYPE ON IS OF SOME TYPE THERE TOO: `anyHolds` holds
/// `holds`'s values, so a demand on a value a goal on it gives is refused until a test
/// narrows it, as one on `holds` is. Read as a column of every type, `ilen` took the
/// `String` and the `pt` as `Int64`s. FAILS with that reading backed out (`some` in
/// `clause_goal_columns`): the refusal, which loads.
#[test]
fn a_relation_that_passes_a_column_of_some_type_on_is_of_some_type() {
    let ns = "wiwf14z.passes";
    let passes = "  rule anyHolds(?x) :- holds(?x)\n";
    refused(
        ns,
        &format!("{DATA}{passes}  rule g(?r) :- anyHolds(?v), ?r <=> U.ilen(?v)\n"),
        "type mismatch in ilen.n (op-arg): expected Int64, got a value of some type: \
         `anyHolds._1` has no type its clauses share",
    );
    let mut kb = crate::common::load_kb_with(&program(
        ns,
        &format!(
            "{DATA}{passes}  rule g(?r) :- anyHolds(?v), domain(?v, Int64), ?r <=> U.ilen(?v)\n"
        ),
    ));
    assert_eq!(crate::common::one_definite_int(&mut kb, &format!("{ns}.g")), Some(1));
}

/// A LATER LOAD READS A WOVEN CALL AS THE CALL IT WAS WRITTEN AS. `sgn`'s goal
/// `WeakOrd.compare(?a, ?b, ?r)` is woven at its own load — a dictionary channel added, an
/// `apply_within` — and a later load reads the stored clause: its result column types `?r`
/// as at the clause's own load, so `sgn(1, 5).head.r` is an `Int64` and a dot on it is the
/// call. Read apart, the column was untyped there: returned as a `String` it loaded and
/// answered the `Int64` `-1`, and `?r.abs()` was data. FAILS with the woven call read apart
/// (`clause_call_parts`).
#[test]
fn a_later_load_reads_a_woven_call_as_its_call() {
    let early = "namespace wiwf14z.early\n  \
                 import anthill.prelude.{Int64, WeakOrd}\n  \
                 rule sgn(?a, ?b, ?r) :- WeakOrd.compare(?a, ?b, ?r)\nend\n";
    let later = |body: &str| {
        let mut kb = crate::common::load_kb_with(early);
        let src = format!(
            "namespace wiwf14z.late\n  \
             import anthill.prelude.{{Int64, String, Error, EmptyStream}}\n  \
             import anthill.prelude.Stream.{{head}}\n  \
             import wiwf14z.early.{{sgn}}\n{body}end\n"
        );
        crate::common::load_in_a_later_call(&mut kb, &src, Default::default())
            .map(|_| kb)
            .map_err(crate::common::rendered_load_errors)
    };
    let errors = later(
        "  operation f() -> String effects {Error, Error[EmptyStream]} = sgn(1, 5).head.r\n",
    )
    .err()
    .expect("an `Int64` column returned as a `String`");
    assert!(
        errors.len() == 1
            && errors[0].contains("type mismatch in f.return (op-return): expected String, got Int64"),
        "{errors:#?}"
    );
    let mut kb = later("  rule q(?x) :- sgn(1, 5, ?r), ?x <=> ?r.abs()\n")
        .unwrap_or_else(|e| panic!("the later load: {e:#?}"));
    assert_eq!(crate::common::one_definite_int(&mut kb, "wiwf14z.late.q"), Some(1));
}

/// TWO CLAUSES OF DIFFERENT SORTS ARE OF SOME TYPE FOR A RULE GOAL TOO, a variable in either:
/// `k(?l) :- ?l <=> nil` beside `k(?l) :- isInt(?l)` holds a `List[T = t]` and an `Int64`,
/// and a demand on a value `k` gives is refused as the citation's read is. Generalized, the
/// column was a variable of every type and `ilen` took the list as an `Int64`. FAILS with that
/// reading backed out (`generalize_columns`): the rule goal loads.
#[test]
fn two_clauses_of_different_sorts_are_of_some_type_for_a_rule_goal_too() {
    let ns = "wiwf14z.apart";
    let decls = "  fact isInt(1)\n  rule k(?l) :- ?l <=> nil\n  rule k(?l) :- isInt(?l)\n  \
                 sort U\n    operation ilen(n: Int64) -> Int64 = n\n  end\n";
    refused(
        ns,
        &format!("{decls}  rule g(?r) :- k(?v), ?r <=> U.ilen(?v)\n"),
        "type mismatch in ilen.n (op-arg): expected Int64, got a value of some type: `k._1` \
         has no type its clauses share",
    );
    refused(
        ns,
        &format!(
            "{decls}  operation f() -> Int64 effects {{Error, Error[EmptyStream]}} = k.head.l\n"
        ),
        "type mismatch in f.return (op-return): expected Int64, got ?l",
    );
}

/// A RELATION WRITTEN AT TWO ARITIES GIVES ITS GOALS NO COLUMNS: a clause of one arity answers
/// no goal of the other, and the load is refused for the two arities, once. Joined slot by
/// slot, `r(1)` beside `r("a", "b")` made the first column of some type and `ilen(?x)` a
/// second refusal; over a library relation it made library bodies read another way, which the
/// typer oracle reports (`wi_6wvjb…::a_clause_against_an_earlier_loads_clauses_is_refused`
/// under `ANTHILL_TYPER_ORACLE=1`). FAILS with the arity test backed out
/// (`relation_goal_columns`): two refusals.
#[test]
fn a_relation_written_at_two_arities_gives_its_goals_no_columns() {
    let errors = crate::common::load_errors_of(&program(
        "wiwf14z.arities",
        "  fact r(1)\n  fact r(\"a\", \"b\")\n  \
         sort U\n    operation ilen(n: Int64) -> Int64 = n\n  end\n  \
         rule g(?y) :- r(?x, ?y), ?z <=> U.ilen(?x)\n",
    ));
    assert!(
        errors.len() == 1 && errors[0].contains("is written at more than one arity"),
        "{errors:#?}"
    );
}
