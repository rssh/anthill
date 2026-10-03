//! WI-20260929-0RP29 — THE NINTH /code-review's REGRESSIONS, fixed by the tenth pass. That review
//! was asked for regressions only: a program the tree it saw (the ninth pass, committed in
//! 2ed85280) does WORSE on than the tree the eighth review saw. Every row below is one of its
//! probes, or the probe of a regression its fix pass found while verifying them, and says at its
//! site what each of the two trees did with it (MEASURED).
//!
//! Every row that can RUNS and names what was reached; a row asserting a LOAD verdict says at its
//! site why nothing runs.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! MEASURED with each part backed out present but wrong, over this file, the three other
//! `wi_0rp29_*` files, `wi_xzmgc_composed_carrier_param_test`, `wi347_override_refinement_test`,
//! `wi_f3fyj_value_in_type_binding_test` and `wi377_effect_row_absent_fold_test` (498 rows). Under
//! part 98 the test PROCESS dies of a stack overflow, so every row was run in a process of its own:
//!
//! 92. A CALLBACK'S WRITTEN ROW IS THE ROW IT DENOTES WHERE IT IS APPLIED
//!     (`callable_effect_present_values`) — flattened as written, a bare row parameter or label
//!     reading as no effect. 2 FAIL:
//!     [`a_raising_callback_in_a_function_slot_is_charged_where_it_is_applied`] and
//!     [`a_function_slot_bound_to_a_bare_label_is_charged_that_label`].
//! 93. A `Function[…]` SLOT JUDGES THE CALLBACK'S ROW, PASSING OVER ITS OWN PLACES ALONE
//!     (`unaligned_own`, and the refusal naming them) — the whole row skipped once the callback
//!     names a place. 3 FAIL: [`a_let_bound_lambda_into_a_function_slot_is_judged`],
//!     [`an_in_place_lambda_into_a_function_slot_is_judged`] and
//!     [`a_function_slot_names_no_parameter_for_a_callbacks_own_place`].
//! 94. A CALLBACK PARAMETER'S PLACE READ BY POSITION ONLY WHERE THE CALLBACK SAYS NO PLACES OF
//!     ITS OWN — for every callback. 2 FAIL:
//!     [`a_lambda_handing_its_callback_another_cell_is_refused`] and
//!     [`a_lambda_swapping_its_callbacks_arguments_is_refused`].
//! 95. WI-408'S WRAP WHERE THE OPTION IS NOT DETERMINED YET (`decidedly_not_an_option`) — the
//!     value left bare. 1 FAILS: [`a_lambda_reading_an_undetermined_options_payload_runs`].
//! 96. A REFUSED WRAP READ AS THE DECLARED OPTION (`some_wrapped_arg_type`) — the raw argument. 1
//!     FAILS: [`a_wrong_argument_for_an_option_parameter_is_named_as_the_option`].
//! 97. THE RECEIVERS TO A FIXPOINT (`projection_receivers`) — one pass in declaration order. 2
//!     FAIL: [`an_option_parameter_declared_before_its_payload_wraps_a_bare_argument`] and
//!     [`a_wrapped_payload_is_what_the_calls_type_reads`].
//! 98. NOT THROUGH A CYCLE (`binds_a_cycle` in `projection_receivers`) — walked. 1 FAILS, its
//!     process killed: [`a_cyclic_call_beside_a_projection_over_a_wrong_argument_is_refused`].
//! 99. A FOREIGN SORT'S UNWRITTEN SLOT ONE VARIABLE PER CALL (`once_per_call`) — expanded per
//!     occurrence. 2 FAIL: [`a_foreign_unwritten_slot_is_one_type_for_a_self_receiver_call`] and
//!     [`a_foreign_unwritten_slot_is_one_type_for_a_carrier_param_call`].
//! 100. THE HINT'S σ BUILT RECEIVER FIRST (`bind_self_receiver_params_for_hint`, then the sibling
//!     pins) — the sibling pins first and no self-receiver binding. 3 FAIL:
//!     [`a_lambda_hint_reads_the_receivers_binding_first`],
//!     [`a_lambda_hint_reads_a_ground_receivers_binding_first`] and
//!     [`a_lambda_reads_a_wider_siblings_field_by_the_receivers_binding`].
//! 101. A SEQUENCE LITERAL HINTED IN THE CALLER'S TERMS (`one_arg_hint`) — the raw parameter type.
//!     2 FAIL: [`a_sequence_literal_is_hinted_in_the_callers_terms`] and
//!     [`a_sequence_literal_through_a_parameters_projection_is_hinted_in_the_callers_terms`].
//! 102. TWO PROVISIONS AGREE ON ONE TYPE AS WRITTEN (`types_agree`) — by mutual compatibility. 2
//!     FAIL: [`two_provisions_binding_permuted_tuples_disagree_in_either_order`] and
//!     [`a_bare_and_a_written_binding_disagree_in_either_order`].
//! 103. A CONSTRUCTOR HEAD REBUILT AS A VARIANT TYPE (`sort_application_value`) — refused, and the
//!     loader panics. 2 FAIL: [`a_constructor_type_beside_a_bare_sort_in_a_provision_loads`] and
//!     [`a_constructor_type_in_a_callback_parameter_of_a_provision_loads`].
//! 104. A RIGID TYPE PROJECTION REBUILT (`entity_type_on_builders`) — refused, and the loader
//!     panics. 1 FAILS: [`a_rigid_type_projection_under_a_rebuilt_binding_does_not_panic`].
//! 105. A RECEIVER-LESS CALL'S OWN PARAMETER TAKES AN OPEN ARGUMENT AS ITS VALUE
//!     (`unify_arg_with_param`) — argument first. 1 FAILS:
//!     [`a_receiverless_call_in_a_lambda_is_typed_by_its_argument`]. And with the reading NOT
//!     restricted to a sort nothing provides, `wi_prva2_pre_existing_defects_test`'s
//!     `a_variable_binds_its_parameters_alike` FAILS (MEASURED: a rule-body spec call bound each
//!     spec parameter to its own argument's variable).
//! 106. A NON-TERM CHAIN ENDING AT A VARIABLE IS THAT VARIABLE (`splice_non_term_bindings`) — the
//!     start kept. 1 FAILS: the same row.
//! 107. A REDUCED RETURN KEEPS WHAT ITS ARGUMENTS PUT IN IT (`SlotPosition::CallResult::held`,
//!     `vars_the_arguments_put`) — every slot opened. 2 FAIL:
//!     [`a_field_of_a_reduced_return_takes_the_callers_annotation`] and
//!     [`a_field_of_another_sorts_reduced_return_takes_the_callers_annotation`] (re-measured on
//!     `held`; the first cut was a `reduced` flag keeping every written variable, see 122).
//!     [`a_receiverless_call_in_a_lambda_runs_on_a_right_argument`] fails under 107 together with
//!     105 or with 106 — either reading alone types `g("s")`'s head — and under no part alone
//!     (measured on the first cut).
//! 108. THE PROVIDER VIEW BINDS ALONG THE RELATION (`bind_along_provider_view`) — not called. 3
//!     FAIL: [`a_member_wider_through_a_spec_its_parameter_provides_fits`],
//!     [`a_member_wider_through_a_user_spec_its_parameter_provides_fits`] and
//!     [`a_member_returning_a_provider_of_the_specs_return_fits`].
//! 109. A NEUTRAL RE-KEYED TO THE ARGUMENT'S VALUE PATH (`arg_paths`) — to its variable. 2 FAIL:
//!     [`a_lambda_hint_through_a_projection_is_the_callers_path`] and
//!     [`a_projection_parameter_takes_a_field_path_argument`].
//! 110. AN EFFECT-ROW BINDING READ AS ITS ROW UNDER VARIANCE (`check_binding_by_variance`) — as
//!     written. 1 FAILS: [`an_unbraced_row_label_in_a_provision_is_the_row_holding_it`].
//! 111. A RETURNED ARROW'S ROW TAKES THE FIELD PATHS' HEADS (`returned_rows`) — not re-keyed. 1
//!     FAILS: [`a_returned_arrows_row_takes_the_field_paths_head`] (measured on the second pass
//!     part 125 folded into one).
//! 112. THE RECEIVER READS THE INSTANCE WHATEVER IT IS TYPED BY (`param_read`) — a receiver typed
//!     by the spec read through the spec's view. 1 FAILS:
//!     [`a_slot_only_the_return_reads_stays_open_on_the_specs_side`].
//! 113. A SLOT ONLY THE RETURN READS STAYS OPEN ON THE SPEC'S SIDE (`kept`) — the spec's own only.
//!     2 FAIL: the same row and [`a_written_wildcard_only_the_return_reads_stays_open`].
//! 114. ONE EXPANSION UNDER A RETURNED ARROW'S PARAMETERS (`want` from `open`) — two. 1 FAILS:
//!     [`a_returned_functions_parameter_is_one_type_on_both_sides`].
//! 115. A CARRIER-PARAMETER RECEIVER IS THE SPEC AT THE PROVISION (`spec_at_provision`) — the
//!     template appended to whatever head it resolves to, as on the tree the ninth review saw. 1
//!     FAILS: [`a_carrier_parameter_type_is_read_at_the_provision`]. And read as the carrier the
//!     parameter is bound to, this pass's first cut, 1 FAILS:
//!     [`a_witness_member_typed_by_the_spec_takes_the_witness_carrier`].
//! 116. "PRINT ALIKE" ONLY WHERE TWO TYPES WERE COMPARED — always. 1 FAILS:
//!     [`a_circular_binding_refusal_does_not_say_two_types_print_alike`].
//! 117. THE UNWRITTEN-SLOT ADVICE ONLY WHERE THAT SLOT IS THE DIFFERENCE
//!     (`agrees_but_for_own_slots`) — wherever the return holds one. 1 FAILS:
//!     [`a_wrong_return_refusal_gives_no_unwritten_slot_advice`].
//! 118. THE WITNESS A BRACKET NAMES LENDS THE MEMBER ALONE (`witnesses_lend_member`) — every
//!     covering witness asked. 3 FAIL: [`a_bracket_naming_a_witness_lends_its_member`],
//!     [`a_bracket_naming_a_witness_dispatches_to_it_over_an_undecided_slot`] and its control,
//!     refused all the same but for the two witnesses' disagreement, not the `String` the named
//!     one returns.
//! 119. AN ALIAS-TYPED SCRUTINEE READ AS ITS TYPE (`build_pattern_subst`) — the bare name. 3 FAIL:
//!     [`a_pattern_binder_over_an_alias_typed_scrutinee_is_the_aliass_type`],
//!     [`a_pattern_binder_over_an_alias_typed_scrutinee_is_checked`] and the member-rule file's
//!     `an_aliass_written_row_is_expanded` (part 105 binds the binder's `T` the other way, so the
//!     two `+` operands are an abstract type there).
//! 120. A PINNED CALL DISPATCHED AT THE NAMED WITNESS'S INSTANCE (`narrowed_to_named_witness`) —
//!     left to the run time. 1 FAILS:
//!     [`a_bracket_naming_a_witness_dispatches_to_it_over_an_undecided_slot`].
//! 121. AN ALIAS LABEL READ AS ITS LABEL IN THE DECLARED-EFFECTS CHECK (op_bodies.rs) — as
//!     written. 1 FAILS: [`an_alias_label_is_the_label_it_stands_for_in_the_declared_row`].
//!
//! THIS PASS'S /simplify — four cleanup reviews over its diff — found seven more defects by probing
//! the code it read and the gate; 122–125 regressions of this pass, 126 and 127 ones on every
//! build, 128 one of 122's first cut. MEASURED
//! the same way, over the same files and `wi_prva2_pre_existing_defects_test` (532 rows):
//!
//! 122. A `?` A REDUCTION BRINGS INTO A REDUCED RETURN IS OPENED (`held`: only what the arguments
//!     put there stays) — every written variable of a reduced return kept, as 107's first cut did.
//!     1 FAILS: [`a_declared_fields_written_wildcard_is_opened`].
//! 123. THE RETURN, ITS EFFECTS AND A CALLBACK'S HINT RE-KEY THROUGH THE CALL'S ONE PATH MAP, ITS
//!     `let` ALIASES READ (`call_arg_paths`) — the return and effects by variable, the hint's paths
//!     as written. 3 FAIL: [`a_returned_projection_names_a_let_aliass_receiver_as_its_parameters_do`],
//!     [`a_returned_projection_through_a_let_alias_meets_its_annotation`] and
//!     [`a_lambda_hint_names_a_let_aliass_receiver_as_the_call_does`].
//! 124. A PARAMETER NAMING THE CALLEE'S OWN PARAMETER AT ANY DEPTH TAKES AN OPEN ARGUMENT AS ITS
//!     VALUE (`unify_arg_with_param`) — at the top only, as 105 first did. 1 FAILS:
//!     [`a_receiverless_call_through_a_callback_is_typed_by_its_argument`].
//! 125. A RETURNED ARROW'S ROW RE-KEYED IN ONE SUBSTITUTION WITH THE REST OF THE RETURN
//!     (`rekeyed_return`, `Discharge::row_syms`) — by the variables, then by the heads. 2 FAIL:
//!     [`a_self_recursive_calls_returned_row_is_renamed_once`] and
//!     [`a_self_recursive_calls_returned_row_is_renamed_once_through_a_projection`].
//! 126. A SEQUENCE LITERAL'S HINT WITHHELD WHILE IT HOLDS A PROJECTION (`one_arg_hint`) — imposed.
//!     1 FAILS: [`a_staged_sequence_literal_is_not_hinted_in_the_callees_names`].
//! 127. A COMPOUND RECEIVER READ AS A PATH ON EITHER CARRIER (`bare_field_access` in
//!     `receiver_path_segs`), found by this /simplify's gate — the occurrence only. 1 FAILS:
//!     [`a_let_annotation_through_an_alias_names_its_target`]; 533 rows.
//! 128. WHAT THE ARGUMENTS PUT INTO A REDUCED RETURN READ OFF THE ARGUMENT TYPES
//!     (`vars_the_arguments_put`) — off what σ added to the declared return, 122's first cut. 1
//!     FAILS: [`a_projection_into_a_reduced_return_keeps_the_arguments_variable`]; the rows of
//!     107 and 122 pass under either reading.
//!
//! THIS PASS'S FIRST CUTS, measured on the way and not in the tree: "print alike" gated on the
//! rule having read a type otherwise than declared, and the advice's agreement comparing rows as
//! written, failed the member-rule file's `an_arrows_own_row_is_expanded` and
//! `a_return_slot_tied_to_a_parameter_is_tied_by_the_member`; counting a receiver's projection in a
//! parameter as reading the provision's slot failed
//! [`a_receivers_projection_in_a_parameter_ties_nothing_to_the_return`], which no part in the tree
//! fails, and no other row needed it. Every other row fails under at least one part but the
//! controls, each passing either way by design (see their sites).
//!
//! The earlier passes' parts 26 and 31 (the wrap), 32 (covering witnesses), 33
//! (`projection_receivers`) and 34 (`types_agree`) name functions this pass rewrote: their rows pass
//! on this tree, and their back-outs were not re-measured.

use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64 as run_src};

// ── a callback's effects where it is applied ─────────────────────────────────────────────────

/// A CALLBACK IN A `Function[…, E = E]` SLOT RAISES THE ROW ITS SLOT IS BOUND TO WHERE IT IS
/// APPLIED. The ninth pass read the slot's row as written at the CALL — `run(boom)` binds `E` to
/// `{Error[String]}` — but the application `f(1)` inside `run` still flattened a bare row
/// parameter to nothing, so `run` declared no effect and raised, and a pure `go` died "error:
/// boom" (MEASURED on the tree the ninth review saw; the tree before it refused the call). The
/// arrow spelling `(x: Int64) -> Int64 @ {E}` was refused at `run`'s declaration on every build;
/// this one is now refused the same way.
/// FAILS under ledger part 92.
#[test]
fn a_raising_callback_in_a_function_slot_is_charged_where_it_is_applied() {
    let src = r#"
namespace wi0rp29r9.fslot_param
  import anthill.prelude.{Int64, String, List, Function, Error}
  operation boom(x: Int64) -> Int64 effects {Error[String]} = Error.raise("boom")
  operation run[E](f: Function[A = Int64, B = Int64, E = E]) -> Int64 = f(1)
  operation go() -> Int64 = run(boom)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["run.effects (op-effects)", "undeclared effect: ?E"],
        "a row parameter applied by an operation declaring nothing",
    );
}

/// … AND A SLOT BOUND TO A BARE LABEL RAISES THAT LABEL: `Function[…, E = Error[String]]` is the
/// row holding it, as `{Error[String]}` is (MEASURED: a pure `go` died "error: boom" on the tree
/// the ninth review saw).
/// FAILS under ledger part 92.
#[test]
fn a_function_slot_bound_to_a_bare_label_is_charged_that_label() {
    let src = r#"
namespace wi0rp29r9.fslot_label
  import anthill.prelude.{Int64, String, List, Function, Error}
  operation boom(x: Int64) -> Int64 effects {Error[String]} = Error.raise("boom")
  operation run(f: Function[A = Int64, B = Int64, E = Error[String]]) -> Int64 = f(1)
  operation go() -> Int64 = run(boom)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["run.effects (op-effects)", "undeclared effect: Error[T = String]"],
        "a bare label applied by an operation declaring nothing",
    );
}

/// CONTROL: an UNWRITTEN slot charges nothing where it is applied, as on every build. Runs to 42
/// either way by design. `Function[A, B]` is effect-polymorphic for now (kernel-language.md §4.4,
/// as corrected 2026-10-03); proposal 069 (WI-20261003-QV5W5) makes its omitted `E` the empty row
/// by `default {}`, and this row then runs for that reason — `inc` is pure.
#[test]
fn an_unwritten_function_slot_charges_nothing_control() {
    let src = r#"
namespace wi0rp29r9.fslot_unwritten
  import anthill.prelude.{Int64, String, List, Function, Error}
  operation inc(x: Int64) -> Int64 = x + 1
  operation ap(f: Function[A = Int64, B = Int64], x: Int64) -> Int64 = f(x)
  operation go() -> Int64 = ap(inc, 41)
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.fslot_unwritten.go"), Ok(42));
}

/// CONTROL: where the applying operation DECLARES the slot's row, its caller is charged what the
/// call binds it to. Refused at `go`'s declaration either way by design.
#[test]
fn a_function_slot_row_the_operation_declares_reaches_its_caller_control() {
    let src = r#"
namespace wi0rp29r9.fslot_declared
  import anthill.prelude.{Int64, String, List, Function, Error}
  operation boom(x: Int64) -> Int64 effects {Error[String]} = Error.raise("boom")
  operation run[E](f: Function[A = Int64, B = Int64, E = E]) -> Int64 effects {E} = f(1)
  operation go() -> Int64 = run(boom)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["go.effects (op-effects)", "undeclared effect: Error[T = String]"],
        "a declared row reaching a caller declaring nothing",
    );
}

/// AN ALIAS LABEL IS THE LABEL IT STANDS FOR where the declared row is compared: `sort Fails =
/// Error[Foo]` and `via(g: … @ {Fails}) effects {Error[Foo]} = g(1)` was refused "undeclared
/// effect: Fails" on every build, in each spelling of the slot — the bare `E = Fails` loaded only
/// because its label was charged as nothing (MEASURED). Runs to 1 + 41, in all three spellings.
/// FAILS under ledger part 121.
#[test]
fn an_alias_label_is_the_label_it_stands_for_in_the_declared_row() {
    for slot in [
        "(x: Int64) -> Int64 @ {Fails}",
        "Function[A = Int64, B = Int64, E = {Fails}]",
        "Function[A = Int64, B = Int64, E = Fails]",
    ] {
        let src = format!(
            r#"
namespace wi0rp29r9.alias_label
  import anthill.prelude.{{Bool, Int64, String, List, Error, Function}}
  sort Foo
    entity foo(n: Int64)
  end
  sort Fails = Error[Foo]
  operation via(g: {slot}) -> Int64 effects {{Error[Foo]}} = g(1)
  operation inc(x: Int64) -> Int64 = x + 41
  operation go() -> Int64 effects {{Error[Foo]}} = via(inc)
end
"#
        );
        assert_eq!(run_src(&src, "wi0rp29r9.alias_label.go"), Ok(42), "slot `{slot}`");
    }
}

// ── a callback into a `Function[…]` slot ────────────────────────────────────────────────────

/// A CALLBACK INTO A `Function[…]` SLOT IS JUDGED, PLACES AND ALL. A `Function[…]` slot names no
/// parameter, so a callback with places "disagreed in arity" with it, and the validator returned
/// for the WHOLE row: a let-bound lambda writing its own parameter and raising `Error[Foo]` passed
/// `eachF[E = {}]`, and a pure `go` died "error: foo(n: 9)" (MEASURED on the tree the ninth review
/// saw; the tree before it refused the call).
/// FAILS under ledger part 93.
#[test]
fn a_let_bound_lambda_into_a_function_slot_is_judged() {
    let src = r#"
namespace wi0rp29r9.fn_let
  import anthill.prelude.{Int64, String, List, Function, Cell, Error}
  sort Foo
    entity foo(n: Int64)
  end
  operation eachF[E](c: Cell[V = Int64], f: Function[A = Cell[V = Int64], B = Int64, E = {E}]) -> Int64 effects {E} = f(c)
  operation sneaky(c: Cell[V = Int64]) -> Int64 =
    let g = lambda (k: Cell[V = Int64]) ->
      let _ = Cell.set(k, 42)
      Error.raise[T = Foo](foo(n: 9))
    eachF[E = {}](c, g)
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    sneaky(c)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "eachF.f (op-arg)",
            "the callback `g` declares `Modify[T = k]`, which the closed row does not admit",
        ],
        "a let-bound lambda raising into a closed Function slot",
    );
}

/// … THE SAME LAMBDA WRITTEN IN PLACE, which no build judged: a pure `go` died "error: foo(n: 9)"
/// on the tree the ninth review saw AND the one before it (MEASURED).
/// FAILS under ledger part 93.
#[test]
fn an_in_place_lambda_into_a_function_slot_is_judged() {
    let src = r#"
namespace wi0rp29r9.fn_inline
  import anthill.prelude.{Int64, String, List, Function, Unit, Cell, Error}
  sort Foo
    entity foo(n: Int64)
  end
  operation eachF[E](c: Cell[V = Int64], f: Function[A = Cell[V = Int64], B = Int64, E = E]) -> Int64 effects {E} = f(c)
  operation sneaky(c: Cell[V = Int64]) -> Int64 =
    eachF[E = {}](c, lambda (k: Cell[V = Int64]) ->
      let _ = Cell.set(k, 42)
      Error.raise[T = Foo](foo(n: 9)))
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    sneaky(c)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["eachF.f (op-arg)", "which the closed row does not admit"],
        "an in-place lambda raising into a closed Function slot",
    );
}

/// A CALLBACK'S OWN PLACE AGAINST A `Function[…]` SLOT IS REFUSED BY NAME: the slot cannot say
/// which value the callback is given, so `Modify[c]` in its row does not admit a lambda writing
/// its own parameter — write the slot as an arrow that names it. The tree the ninth review saw ran
/// this (the bail above); the tree before it refused it with the closed-row sentence (MEASURED).
/// FAILS under ledger part 93.
#[test]
fn a_function_slot_names_no_parameter_for_a_callbacks_own_place() {
    let src = r#"
namespace wi0rp29r9.fn_own_place
  import anthill.prelude.{Int64, String, List, Function, Unit, Cell, Modify}
  operation eachF[E](c: Cell[V = Int64], f: Function[A = Cell[V = Int64], B = Unit, E = {E}]) -> Unit effects {E} = f(c)
  operation honest(c: Cell[V = Int64]) -> Unit effects {Modify[c]} =
    let g = lambda (k: Cell[V = Int64]) -> Cell.set(k, 42)
    eachF[E = {Modify[c]}](c, g)
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let _ = honest(c)
    Cell.get(c)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "a `Function[…]` slot names no parameter",
            "the callback `g` declares `Modify[T = k]` on its own parameter `k`",
            "type the slot as an arrow that names it",
        ],
        "a callback's own place against a Function slot",
    );
}

/// A LAMBDA HANDING ITS CALLBACK PARAMETER ANOTHER CELL WRITES THAT CELL. The ninth pass compared
/// a callback's places BY POSITION against the slot's: `g`'s `y` is its first, `f`'s `x` is its
/// first, so `lambda (k) -> g(d)` was read as writing `x` — and `use`, typed pure, wrote `d` (the
/// cell came back 42; MEASURED on the tree the ninth review saw; the tree before it refused the
/// call). Positions are compared only where the callback's expression names no places of its own.
/// FAILS under ledger part 94.
#[test]
fn a_lambda_handing_its_callback_another_cell_is_refused() {
    let src = r#"
namespace wi0rp29r9.place_other
  import anthill.prelude.{Int64, String, List, Unit, Cell, Modify}
  operation app(q: Cell[V = Int64], f: (x: Cell[V = Int64]) -> Unit @ {Modify[x]}) -> Unit effects {Modify[q]} = f(q)
  operation use(d: Cell[V = Int64], g: (y: Cell[V = Int64]) -> Unit @ {Modify[y]}) -> Unit =
    let c: Cell[V = Int64] = Cell.new(0)
    app(c, lambda (k) -> g(d))
  operation go() -> Int64 =
    let d: Cell[V = Int64] = Cell.new(1)
    let _ = use(d, lambda (x) -> Cell.set(x, 42))
    Cell.get(d)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["app.f (op-arg)", "the lambda argument declares `Modify[T = g.y]`"],
        "a lambda handing its callback another cell",
    );
}

/// … AND ONE SWAPPING ITS CALLBACK'S ARGUMENTS WRITES THE CELL ITS SLOT DENIES: `-Modify[a]` was
/// defeated, and `p` came back written by a `use` declaring `Modify[q]` only (MEASURED on the tree
/// the ninth review saw).
/// FAILS under ledger part 94.
#[test]
fn a_lambda_swapping_its_callbacks_arguments_is_refused() {
    let src = r#"
namespace wi0rp29r9.place_swap
  import anthill.prelude.{Int64, String, List, Unit, Cell, Modify}
  operation app2(p: Cell[V = Int64], q: Cell[V = Int64], f: (a: Cell[V = Int64], b: Cell[V = Int64]) -> Unit @ {Modify[b], -Modify[a]}) -> Unit effects {Modify[q]} = f(p, q)
  operation set2(a: Cell[V = Int64], b: Cell[V = Int64]) -> Unit effects {Modify[b]} = Cell.set(b, 42)
  operation use(p: Cell[V = Int64], q: Cell[V = Int64], g: (y1: Cell[V = Int64], y2: Cell[V = Int64]) -> Unit @ {Modify[y2]}) -> Unit effects {Modify[q]} =
    app2(p, q, lambda (k1, k2) -> g(k2, k1))
  operation go() -> Int64 =
    let p: Cell[V = Int64] = Cell.new(1)
    let q: Cell[V = Int64] = Cell.new(1)
    let _ = use(p, q, set2)
    Cell.get(p)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["app2.f (op-arg)", "the lambda argument declares `Modify[T = g.y2]`"],
        "a lambda swapping its callback's arguments",
    );
}

// ── the `some(…)` wrap of an option parameter ───────────────────────────────────────────────

/// A BARE ARGUMENT FOR AN OPTION PARAMETER IS WRAPPED WHEREVER THE OPTION IS DECLARED. `pick(k:
/// Option[T = h.T], h: Option[T = Int64])` — `k`'s payload is read off a LATER parameter, so when
/// `41` is checked the option is not determined yet, and the ninth pass left it unwrapped: `k.T`
/// then projected off `Int64` ("has no member 'T'") where the swapped declaration ran (MEASURED on
/// the tree the ninth review saw; the tree before it ran this). Runs to 42.
/// FAILS under ledger part 97.
#[test]
fn an_option_parameter_declared_before_its_payload_wraps_a_bare_argument() {
    let src = r#"
namespace wi0rp29r9.wrap_order
  import anthill.prelude.{Int64, String, List, Option}
  import anthill.prelude.Option.{some, none}
  operation pick(k: Option[T = h.T], h: Option[T = Int64]) -> k.T =
    match k
      case some(v) -> v
      case none -> 0
  operation go() -> Int64 = pick(41, 7) + 1
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.wrap_order.go"), Ok(42));
}

/// CONTROL: the same declared the other way round. Runs to 42 either way by design.
#[test]
fn an_option_parameter_declared_before_its_payload_wraps_a_bare_argument_control() {
    let src = r#"
namespace wi0rp29r9.wrap_order_swapped
  import anthill.prelude.{Int64, String, List, Option}
  import anthill.prelude.Option.{some, none}
  operation pick(h: Option[T = Int64], k: Option[T = h.T]) -> k.T =
    match k
      case some(v) -> v
      case none -> 0
  operation go() -> Int64 = pick(7, 41) + 1
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.wrap_order_swapped.go"), Ok(42));
}

/// … AND THE WRAPPED PAYLOAD IS WHAT THE CALL'S TYPE READS: `pick([41], [7])` returns a list, so
/// `+ 1` is refused at the load. The tree the ninth review saw read `k.T` off the raw argument,
/// admitted the call and died "type mismatch: expected Int64, got Entity and Int64" (MEASURED).
/// FAILS under ledger part 97.
#[test]
fn a_wrapped_payload_is_what_the_calls_type_reads() {
    let src = r#"
namespace wi0rp29r9.wrap_payload
  import anthill.prelude.{Int64, String, List, Option}
  operation pick(k: Option[T = h.T], h: Option[T = List[T = Int64]]) -> k.T = [0]
  operation go() -> Int64 = pick([41], [7]) + 1
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["add.b (op-arg): expected List[T = Int64], got Int64"],
        "a list payload added to an Int64",
    );
}

/// … A LAMBDA READING AN UNDETERMINED OPTION'S PAYLOAD: `ap(41, lambda (x) -> x + 1)` — the
/// lambda's `x: k.T` reads the wrapped `41`. Refused on the tree the ninth review saw ("add.b:
/// expected k.T …"); runs to 42.
/// FAILS under ledger part 95.
#[test]
fn a_lambda_reading_an_undetermined_options_payload_runs() {
    let src = r#"
namespace wi0rp29r9.wrap_late
  import anthill.prelude.{Int64, String, List, Option}
  import anthill.prelude.Option.{some, none}
  operation ap[A](k: Option[T = A], w: (x: k.T) -> A) -> Option[T = A] =
    match k
      case some(v) -> some(w(v))
      case none -> none
  operation go() -> Int64 =
    match ap(41, lambda (x) -> x + 1)
      case some(r) -> r
      case none -> 0
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.wrap_late.go"), Ok(42));
}

/// A WRONG ARGUMENT FOR AN OPTION PARAMETER IS NAMED AS THE OPTION: `put("abc", 1)` against `k:
/// Option[T = Int64]` is "put.k: expected Option[T = Int64], got String", as before the ninth
/// pass. On the tree the ninth review saw the wrap's failure left the raw argument, and the
/// refusal was "put.return: … 'String' has no member 'T'" (MEASURED).
/// FAILS under ledger part 96.
#[test]
fn a_wrong_argument_for_an_option_parameter_is_named_as_the_option() {
    let src = r#"
namespace wi0rp29r9.wrap_wrong
  import anthill.prelude.{Int64, String, List, Option}
  operation put(k: Option[T = Int64], d: k.T) -> Int64 = d
  operation go() -> Int64 = put("abc", 1)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["put.k (op-arg): expected Option[T = Int64], got String"],
        "a String for an Option[T = Int64]",
    );
}

/// A CALL WRONG TWICE — `5` for a list whose element a later parameter projects, and two lambdas
/// with no finite typing — IS REFUSED, NOT A STACK OVERFLOW. The receivers' fixpoint walked the
/// cyclic substitution the two lambdas leave and overflowed the loader's stack (MEASURED on the
/// tree the ninth review saw; the tree before it printed this refusal). Nothing runs: the program
/// is wrong.
/// FAILS under ledger part 98 (the process dies).
#[test]
fn a_cyclic_call_beside_a_projection_over_a_wrong_argument_is_refused() {
    let src = r#"
namespace wi0rp29r9.wrap_cycle
  import anthill.prelude.{Int64, List, Option}
  import anthill.prelude.Option.{none}
  operation two[A, B](k: Option[T = A], f: (x: A) -> B, g: (y: B) -> A, h: List[T = Int64], z: h.T) -> Int64 = 1
  operation go() -> Int64 = two(none, lambda (x) -> [x], lambda (y) -> [y], 5, 5)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["two.return (op-return)", "has no member 'T'"],
        "a projection off a wrong argument beside a cyclic pair",
    );
}

// ── a this-instance binding at a call ───────────────────────────────────────────────────────

/// A FOREIGN SORT'S UNWRITTEN SLOT IN A THIS-INSTANCE BINDING IS ONE TYPE FOR THE WHOLE CALL.
/// `provides Sp[T = Box[C = Car]]` leaves `Box`'s `B` unwritten; `both(s: Sp, x: T, y: T)` at a
/// `Car` receiver read each `T` with a slot of its own, so `x: Box[B = Int64]` and `y: Box[B =
/// String]` both passed, and the member applied `x`'s callback to `y`'s payload: "expected Int64,
/// got String" at run time (MEASURED on the tree the ninth review saw; the tree before it refused
/// the call at `both.y`).
/// FAILS under ledger part 99.
#[test]
fn a_foreign_unwritten_slot_is_one_type_for_a_self_receiver_call() {
    let src = r#"
namespace wi0rp29r9.once_self
  import anthill.prelude.{Int64, String, List}
  sort Box
    sort B = ?
    sort C = ?
    entity box(inner: B, f: (x: B) -> Int64, tag: C)
  end
  sort Sp
    sort T = ?
    operation both(s: Sp, x: T, y: T) -> Int64
  end
  sort Car
    entity car(n: Int64)
    provides Sp[T = Box[C = Car]]
    operation both[W](s: Car, x: Box[B = W, C = Car], y: Box[B = W, C = Car]) -> Int64 =
      match x
        case box(_, g, _) -> g(y.inner)
  end
  operation go() -> Int64 =
    let c: Car = car(n: 1)
    let x: Box[B = Int64, C = Car] = box(inner: 3, f: lambda (p: Int64) -> p + 39, tag: c)
    let y: Box[B = String, C = Car] = box(inner: "s", f: lambda (p: String) -> 9, tag: c)
    Sp.both(c, x, y)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["both.y (op-arg): expected Box[C = Car, B = Int64], got Box[C = Car, B = String]"],
        "two instances of one unwritten slot at a self-receiver call",
    );
}

/// … AND AT A CARRIER-PARAMETER CALL, `Rel[A = Car, T = Box[C = Car]]` (MEASURED: the same run-time
/// failure on the tree the ninth review saw).
/// FAILS under ledger part 99.
#[test]
fn a_foreign_unwritten_slot_is_one_type_for_a_carrier_param_call() {
    let src = r#"
namespace wi0rp29r9.once_cp
  import anthill.prelude.{Int64, String, List}
  sort Box
    sort B = ?
    sort C = ?
    entity box(inner: B, f: (x: B) -> Int64, tag: C)
  end
  sort Rel
    sort A = ?
    sort T = ?
    operation both(a: A, x: T, y: T) -> Int64
  end
  sort Car
    entity car(n: Int64)
    provides Rel[A = Car, T = Box[C = Car]]
    operation both[W](a: Car, x: Box[B = W, C = Car], y: Box[B = W, C = Car]) -> Int64 =
      match x
        case box(_, g, _) -> g(y.inner)
  end
  operation go() -> Int64 =
    let c: Car = car(n: 1)
    let x: Box[B = Int64, C = Car] = box(inner: 3, f: lambda (p: Int64) -> p + 39, tag: c)
    let y: Box[B = String, C = Car] = box(inner: "s", f: lambda (p: String) -> 9, tag: c)
    Rel.both(c, x, y)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["both.y (op-arg): expected Box[C = Car, B = Int64], got Box[C = Car, B = String]"],
        "two instances of one unwritten slot at a carrier-param call",
    );
}

/// CONTROL: the two arguments at ONE instance run, 3 + 39. Runs to 42 either way by design.
#[test]
fn a_foreign_unwritten_slot_is_one_type_for_a_self_receiver_call_control() {
    let src = r#"
namespace wi0rp29r9.once_self_same
  import anthill.prelude.{Int64, String, List}
  sort Box
    sort B = ?
    sort C = ?
    entity box(inner: B, f: (x: B) -> Int64, tag: C)
  end
  sort Sp
    sort T = ?
    operation both(s: Sp, x: T, y: T) -> Int64
  end
  sort Car
    entity car(n: Int64)
    provides Sp[T = Box[C = Car]]
    operation both[W](s: Car, x: Box[B = W, C = Car], y: Box[B = W, C = Car]) -> Int64 =
      match x
        case box(_, g, _) -> g(y.inner)
  end
  operation go() -> Int64 =
    let c: Car = car(n: 1)
    let x: Box[B = Int64, C = Car] = box(inner: 3, f: lambda (p: Int64) -> p + 39, tag: c)
    let y: Box[B = Int64, C = Car] = box(inner: 3, f: lambda (p: Int64) -> 9, tag: c)
    Sp.both(c, x, y)
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.once_self_same.go"), Ok(42));
}

// ── a lambda's hint at a spec-operation call ────────────────────────────────────────────────

/// A LAMBDA'S HINT IS READ AS THE CALL BINDS: THE RECEIVER FIRST. `Sp.each(k, lambda (q) -> 42, k)`
/// at `k: Car[V = Int64]` and `provides Sp[T = Option[T = Car]]` — the hint was pinned from the
/// sibling `k` before the receiver bound `T`, and the lambda was refused "each.f: expected
/// Option[T = Car[V = Int64]] …" (MEASURED on the tree the ninth review saw; the tree before it ran
/// this). Runs to 42.
/// FAILS under ledger part 100.
#[test]
fn a_lambda_hint_reads_the_receivers_binding_first() {
    let src = r#"
namespace wi0rp29r9.hint_receiver
  import anthill.prelude.{Int64, String, List, Option}
  sort Sp
    sort T = ?
    operation each(s: Sp, f: (q: T) -> Int64, z: T) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = Option[T = Car]]
    operation each(c: Car, f: (q: Option[T = Car]) -> Int64, z: Option[T = Car]) -> Int64 = f(z)
  end
  operation go() -> Int64 =
    let k: Car[V = Int64] = car(v: 1)
    Sp.each(k, lambda (q) -> 42, k)
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.hint_receiver.go"), Ok(42));
}

/// … AT A GROUND RECEIVER TOO: `k: Car`, no parameter (MEASURED: refused on the tree the ninth
/// review saw). Runs to 42.
/// FAILS under ledger part 100.
#[test]
fn a_lambda_hint_reads_a_ground_receivers_binding_first() {
    let src = r#"
namespace wi0rp29r9.hint_ground
  import anthill.prelude.{Int64, String, List, Option}
  sort Sp
    sort T = ?
    operation each(s: Sp, f: (q: T) -> Int64, z: T) -> Int64
  end
  sort Car
    entity car(n: Int64)
    provides Sp[T = Option[T = Car]]
    operation each(c: Car, f: (q: Option[T = Car]) -> Int64, z: Option[T = Car]) -> Int64 = f(z)
  end
  operation go() -> Int64 =
    let k: Car = car(n: 1)
    Sp.each(k, lambda (q) -> 42, k)
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.hint_ground.go"), Ok(42));
}

/// … AND A WIDER SIBLING DOES NOT NARROW THE LAMBDA: a `(c: Car, a: Int64, extra: Int64)` passed
/// for `T = (c: Car, a: Int64)` pinned the lambda's `q` to the wider tuple, and it was refused
/// "each.f: expected ((c: Car, a: Int64)) -> Int64, got ((c: Car, a: Int64, extra: Int64)) ->
/// Int64" (MEASURED on the tree the ninth review saw). Runs to 1 + 41.
/// FAILS under ledger part 100.
#[test]
fn a_lambda_reads_a_wider_siblings_field_by_the_receivers_binding() {
    let src = r#"
namespace wi0rp29r9.hint_wide
  import anthill.prelude.{Int64, String, List}
  sort Sp
    sort T = ?
    operation each(s: Sp, f: (q: T) -> Int64, z: T) -> Int64
  end
  sort Car
    entity car(n: Int64)
    provides Sp[T = (c: Car, a: Int64)]
    operation each(c: Car, f: (q: (c: Car, a: Int64)) -> Int64, z: (c: Car, a: Int64)) -> Int64 = f(z)
  end
  operation go() -> Int64 =
    let k: Car = car(n: 1)
    let p: (c: Car, a: Int64, extra: Int64) = (c: k, a: 1, extra: 2)
    Sp.each(k, lambda (q) -> q.a + 41, p)
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.hint_wide.go"), Ok(42));
}

/// CONTROL: the sibling at exactly the bound tuple. Runs to 42 either way by design.
#[test]
fn a_lambda_reads_a_wider_siblings_field_by_the_receivers_binding_control() {
    let src = r#"
namespace wi0rp29r9.hint_exact
  import anthill.prelude.{Int64, String, List}
  sort Sp
    sort T = ?
    operation each(s: Sp, f: (q: T) -> Int64, z: T) -> Int64
  end
  sort Car
    entity car(n: Int64)
    provides Sp[T = (c: Car, a: Int64)]
    operation each(c: Car, f: (q: (c: Car, a: Int64)) -> Int64, z: (c: Car, a: Int64)) -> Int64 = f(z)
  end
  operation go() -> Int64 =
    let k: Car = car(n: 1)
    let p: (c: Car, a: Int64) = (c: k, a: 1)
    Sp.each(k, lambda (q) -> 42, p)
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.hint_exact.go"), Ok(42));
}

/// A SEQUENCE LITERAL IS HINTED IN THE CALLER'S TERMS. `op(s: Sp, p: List[T = (a: s.J, b: J)])`
/// at `provides Sp[J = List[T = Car[V = Int64]]]` — the literal `[(a: [k], b: [k])]` is typed BY
/// its hint, and hinted with the callee's raw `s.J`, which no caller names, it was refused
/// against the eliminated slot (MEASURED on the tree the ninth review saw; the tree before it ran
/// this). Runs to 42.
/// FAILS under ledger part 101.
#[test]
fn a_sequence_literal_is_hinted_in_the_callers_terms() {
    let src = r#"
namespace wi0rp29r9.seq_spec
  import anthill.prelude.{Int64, Bool, String, List, Option}
  sort Sp
    sort J = ?
    operation op(s: Sp, p: List[T = (a: s.J, b: J)]) -> Int64
  end
  sort Car
    sort V = ?
    sort W = ?
    entity car(v: V, w: W)
    provides Sp[J = List[T = Car[V = Int64]]]
    operation op(c: Car, p: List[T = (a: c.J, b: List[T = Car[V = Int64]])]) -> Int64 = 42
  end
  operation go() -> Int64 =
    let k: Car[V = Int64, W = String] = car(v: 5, w: "s")
    Sp.op(k, [(a: [k], b: [k])])
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.seq_spec.go"), Ok(42));
}

/// … AND THROUGH A PROJECTION OFF AN ORDINARY OPERATION'S PARAMETER: `f1(k, [(a: 5, b: "s")])`
/// over `p1: List[T = (a: c.T, b: c.J)]` — "list.element 1: expected (a: c.T, b: c.J), got (a:
/// Int64, b: String)" on every build before this pass (MEASURED). Runs to 42.
/// FAILS under ledger part 101.
#[test]
fn a_sequence_literal_through_a_parameters_projection_is_hinted_in_the_callers_terms() {
    let src = r#"
namespace wi0rp29r9.seq_param
  import anthill.prelude.{Int64, Bool, String, List}
  sort Sp
    sort T = ?
    sort J = ?
    operation size(s: Sp) -> Int64
  end
  sort Car
    sort V = ?
    sort W = ?
    entity car(v: V, w: W)
    provides Sp[T = V, J = W]
    operation size(c: Car) -> Int64 = 1
  end
  operation f1(c: Car, p1: List[T = (a: c.T, b: c.J)]) -> Int64 = 42
  operation go() -> Int64 =
    let k: Car[V = Int64, W = String] = car(v: 5, w: "s")
    f1(k, [(a: 5, b: "s")])
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.seq_param.go"), Ok(42));
}

/// … AND A STAGED ONE, HINTED BEFORE THE RECEIVER IT PROJECTS IS TYPED, IS NOT HINTED IN THE
/// CALLEE'S NAMES. `f(mk(), [(a: 2, b: 3)], lambda (x) -> 41)` over `p: List[T = (a: s.J, b:
/// s.J)]`, `g: (x: p.T) -> Int64`: the lambda's hint needs `p`, so `p` is typed first, while
/// `mk()` is not typed yet — and the literal, typed BY its hint, met the callee's `s.J`: "list.element
/// 1: expected (a: s.J, b: s.J), got (a: Int64, b: Int64)" (MEASURED: on every build before this
/// pass's /simplify). A hint still holding a projection is withheld; the call checks the literal
/// against the slot it eliminates. Runs to 42.
/// FAILS under ledger part 126.
#[test]
fn a_staged_sequence_literal_is_not_hinted_in_the_callees_names() {
    let src = r#"
namespace wi0rp29r9.seq_staged
  import anthill.prelude.{Int64, String, List}
  sort Src
    sort J = ?
    entity src(j: J)
  end
  operation mk() -> Src[J = Int64] = src(j: 1)
  operation f(s: Src, p: List[T = (a: s.J, b: s.J)], g: (x: p.T) -> Int64) -> Int64 = 42
  operation go() -> Int64 = f(mk(), [(a: 2, b: 3)], lambda (x) -> 41)
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.seq_staged.go"), Ok(42));
}

/// CONTROL: a wrong element is still refused — by the call's check against the eliminated slot,
/// where the hint used to refuse it as an element. Refused either way by design, naming the wrong
/// element's type either way; nothing runs.
#[test]
fn a_staged_sequence_literal_is_not_hinted_in_the_callees_names_control() {
    let src = r#"
namespace wi0rp29r9.seq_staged_wrong
  import anthill.prelude.{Int64, String, List}
  sort Src
    sort J = ?
    entity src(j: J)
  end
  operation mk() -> Src[J = Int64] = src(j: 1)
  operation f(s: Src, p: List[T = (a: s.J, b: s.J)], g: (x: p.T) -> Int64) -> Int64 = 42
  operation go() -> Int64 = f(mk(), [(a: 2, b: "s")], lambda (x) -> 41)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["got", "(a: Int64, b: String)"],
        "a wrong element in a staged literal",
    );
}

// ── two provisions lending one member ───────────────────────────────────────────────────────

/// TWO PROVISIONS BINDING A MEMBER TO PERMUTED TUPLES DISAGREE, WHATEVER ORDER THEY ARE WRITTEN IN.
/// The ninth pass judged agreement by unification — each side's unwritten slots read as anything,
/// and a tuple compared by its labels' set — so `(a: Int64, b: Int64)` and `(b: Int64, a: Int64)`
/// "agreed", and the first provision lent the member: `f(car, (a: 42, b: 7))` ran to 42 written
/// one way and to 7 the other (MEASURED on the tree the ninth review saw; the tree before it
/// refused both).
/// FAILS under ledger part 102.
#[test]
fn two_provisions_binding_permuted_tuples_disagree_in_either_order() {
    for (first, second) in [
        ("SpA[C = Car, T = (a: Int64, b: Int64)]", "SpB[C = Car, T = (b: Int64, a: Int64)]"),
        ("SpB[C = Car, T = (b: Int64, a: Int64)]", "SpA[C = Car, T = (a: Int64, b: Int64)]"),
    ] {
        let src = format!(
            r#"
namespace wi0rp29r9.agree_tuple
  import anthill.prelude.{{Int64, String, List}}
  sort SpA
    sort C = ?
    sort T = ?
  end
  sort SpB
    sort C = ?
    sort T = ?
  end
  sort Car
    entity car(n: Int64)
    provides {first}
    provides {second}
  end
  operation f(c: Car, k: c.T) -> Int64 =
    match k
      case (x, y) -> x
  operation go() -> Int64 = f(car(n: 1), (a: 42, b: 7))
end
"#
        );
        assert_refused_naming(
            &load_errors(&src),
            &["has a member 'T' by two specs it provides, which bind it differently"],
            "two provisions binding permuted tuples",
        );
    }
}

/// … AND A BARE `List` AGAINST `List[T = Int64]`: written bare first, the bare slot read as
/// anything and `f(car, ["s"])` ran; written second, the call was refused "f.k: expected
/// List[T = Int64], got List[T = String]" (MEASURED on the tree the ninth review saw). Two
/// provisions agree when they bind one type, as written.
/// FAILS under ledger part 102.
#[test]
fn a_bare_and_a_written_binding_disagree_in_either_order() {
    for (first, second) in [
        ("SpB[C = Car, T = List]", "SpA[C = Car, T = List[T = Int64]]"),
        ("SpA[C = Car, T = List[T = Int64]]", "SpB[C = Car, T = List]"),
    ] {
        let src = format!(
            r#"
namespace wi0rp29r9.agree_bare
  import anthill.prelude.{{Int64, String, List}}
  sort SpA
    sort C = ?
    sort T = ?
  end
  sort SpB
    sort C = ?
    sort T = ?
  end
  sort Car
    entity car(n: Int64)
    provides {first}
    provides {second}
  end
  operation f(c: Car, k: c.T) -> Int64 = 42
  operation go() -> Int64 = f(car(n: 1), ["s"])
end
"#
        );
        assert_refused_naming(
            &load_errors(&src),
            &["has a member 'T' by two specs it provides, which bind it differently"],
            "a bare and a written binding",
        );
    }
}

/// A BRACKET NAMING A WITNESS LENDS ITS MEMBER: `Holder.get[Holder = BoxHolderA](box(n: 1))` — two
/// witnesses cover `Box` and disagree on `T`, and the bracket says which one the call reaches. The
/// ninth pass asked every covering witness and refused "covered by two witnesses … that do not
/// agree" (MEASURED on the tree the ninth review saw; the tree before it ran this). Runs to 42.
/// FAILS under ledger part 118.
#[test]
fn a_bracket_naming_a_witness_lends_its_member() {
    let src = r#"
namespace wi0rp29r9.witness_bracket
  import anthill.prelude.{Int64, String, List}
  sort Holder
    sort C = ?
    sort T = ?
    operation get(c: C) -> c.T
  end
  sort Box
    entity box(n: Int64)
  end
  sort BoxHolderA
    provides Holder[C = Box, T = Int64]
    operation get(c: Box) -> Int64 = c.n + 41
  end
  sort BoxHolderB
    provides Holder[C = Box, T = String]
    operation get(c: Box) -> String = "s"
  end
  operation show[A](x: A) -> Int64 = 42
  operation go() -> Int64 = show(Holder.get[Holder = BoxHolderA](box(n: 1)))
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.witness_bracket.go"), Ok(42));
}

/// CONTROL: with no bracket the two witnesses still disagree, and that is the refusal. Refused
/// either way by design.
#[test]
fn a_bracket_naming_a_witness_lends_its_member_control() {
    let src = r#"
namespace wi0rp29r9.witness_nobracket
  import anthill.prelude.{Int64, String, List}
  sort Holder
    sort C = ?
    sort T = ?
    operation get(c: C) -> c.T
  end
  sort Box
    entity box(n: Int64)
  end
  sort BoxHolderA
    provides Holder[C = Box, T = Int64]
    operation get(c: Box) -> Int64 = c.n + 41
  end
  sort BoxHolderB
    provides Holder[C = Box, T = String]
    operation get(c: Box) -> String = "s"
  end
  operation show[A](x: A) -> Int64 = 42
  operation go() -> Int64 = show(Holder.get(box(n: 1)))
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["is covered by two witnesses", "that do not agree on its member 'T'"],
        "two disagreeing witnesses and no bracket",
    );
}

/// … AND THE CALL IS DISPATCHED TO THAT WITNESS where the receiver leaves a slot no type decides:
/// `box(v: none)` is a `Box[V = Option]`, which both witnesses' instances (`Box[V = Option[T =
/// Int64]]`, `[… = String]`) cover. Its type read the named witness's `Int64`, but the dispatch
/// matched no provision as the receiver stands and left the call to the run time, whose
/// value-directed dispatch reads no bracket: "ambiguous dispatch of `Holder.get`" (MEASURED: the
/// tenth pass's first cut; on the tree the eighth review saw likewise, wherever the result was
/// generic). Runs to 42.
/// FAILS under ledger parts 118 and 120.
#[test]
fn a_bracket_naming_a_witness_dispatches_to_it_over_an_undecided_slot() {
    let src = r#"
namespace wi0rp29r9.witness_undecided
  import anthill.prelude.{Int64, String, List, Option}
  import anthill.prelude.Option.{some, none}
  sort Holder
    sort C = ?
    sort T = ?
    operation get(c: C) -> c.T
  end
  sort Box
    sort V = ?
    entity box(v: V)
  end
  sort OptIntBoxH
    provides Holder[C = Box[V = Option[T = Int64]], T = Int64]
    operation get(c: Box[V = Option[T = Int64]]) -> Int64 = 42
  end
  sort OptStrBoxH
    provides Holder[C = Box[V = Option[T = String]], T = String]
    operation get(c: Box[V = Option[T = String]]) -> String = "s"
  end
  operation go() -> Int64 = Holder.get[Holder = OptIntBoxH](box(v: none))
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.witness_undecided.go"), Ok(42));
}

/// CONTROL: naming the OTHER witness reads ITS member, a `String`, where `go` promises an
/// `Int64`. Refused under every part, and FAILS under ledger part 118 by what it names: without
/// the narrowing the projection reads both witnesses and refuses their disagreement instead.
#[test]
fn a_bracket_naming_a_witness_dispatches_to_it_over_an_undecided_slot_control() {
    let src = r#"
namespace wi0rp29r9.witness_undecided_other
  import anthill.prelude.{Int64, String, List, Option}
  import anthill.prelude.Option.{some, none}
  sort Holder
    sort C = ?
    sort T = ?
    operation get(c: C) -> c.T
  end
  sort Box
    sort V = ?
    entity box(v: V)
  end
  sort OptIntBoxH
    provides Holder[C = Box[V = Option[T = Int64]], T = Int64]
    operation get(c: Box[V = Option[T = Int64]]) -> Int64 = 42
  end
  sort OptStrBoxH
    provides Holder[C = Box[V = Option[T = String]], T = String]
    operation get(c: Box[V = Option[T = String]]) -> String = "s"
  end
  operation go() -> Int64 = Holder.get[Holder = OptStrBoxH](box(v: none))
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["go.return (op-return): expected Int64, got String"],
        "the other witness's member",
    );
}

// ── a constructor type in a provision ───────────────────────────────────────────────────────

/// A CONSTRUCTOR TYPE BESIDE A BARE SORT IN A SPEC OPERATION LOADS. `put(s: Sp, x: (a: some[T =
/// T], b: List))` with `Car provides Sp[T = V, E = {Error}]` — a variant type (§8.2) under a
/// rebuilt binding was "a type under `some`, which is not a sort", and the loader PANICKED on a
/// fitting member (MEASURED: exit 101 on the tree the ninth review saw built with debug
/// assertions; the tree before it ran this). Runs to 42.
/// FAILS under ledger part 103.
#[test]
fn a_constructor_type_beside_a_bare_sort_in_a_provision_loads() {
    let src = r#"
namespace wi0rp29r9.ctor_type
  import anthill.prelude.{Int64, String, Bool, List, Option, Error}
  import anthill.prelude.Option.{some, none}
  sort Sp
    sort T = ?
    effects E = ?
    operation size(s: Sp) -> Int64
    operation put(s: Sp, x: (a: some[T = T], b: List)) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V, E = {Error}]
    operation size(c: Car) -> Int64 = 42
    operation put(c: Car, x: (a: some[T = V], b: List)) -> Int64 = 1
  end
  operation go() -> Int64 =
    let k: Car[V = Int64] = car(v: 1)
    Sp.size(k)
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.ctor_type.go"), Ok(42));
}

/// … AND ONE UNDER A CALLBACK'S PARAMETER (MEASURED: the same panic). Runs to 42.
/// FAILS under ledger part 103.
#[test]
fn a_constructor_type_in_a_callback_parameter_of_a_provision_loads() {
    let src = r#"
namespace wi0rp29r9.ctor_callback
  import anthill.prelude.{Int64, String, Bool, List, Option, Error}
  import anthill.prelude.Option.{some, none}
  sort Sp
    sort T = ?
    effects E = ?
    operation size(s: Sp) -> Int64
    operation put(s: Sp, x: (q: some[T = T]) -> List) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V, E = {Error}]
    operation size(c: Car) -> Int64 = 42
    operation put(c: Car, x: (q: some[T = V]) -> List) -> Int64 = 1
  end
  operation go() -> Int64 =
    let k: Car[V = Int64] = car(v: 1)
    Sp.size(k)
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.ctor_callback.go"), Ok(42));
}

/// … AND A RIGID TYPE PROJECTION (`P.Key`) UNDER A REBUILT BINDING: the rebuild had no arm for
/// it, and the loader PANICKED (MEASURED: exit 101 on the tree the ninth review saw). Nothing
/// runs: the provision is refused, as on the tree the eighth review saw — and both its refusals
/// are wrong on every build (the `requires Storage[C = P]` reads `Key` and `Val` unreduced, and
/// the rule compares the spec's `MemStore.Key` unreduced with the member's `String`), a separate
/// question this row pins only as "no panic, the earlier verdict".
/// FAILS under ledger part 104.
#[test]
fn a_rigid_type_projection_under_a_rebuilt_binding_does_not_panic() {
    let src = r#"
namespace wi0rp29r9.rigid_proj
  import anthill.prelude.{Int64, String, Bool, List, Option, Error}
  sort Storage
    sort C = ?
    sort Key = ?
    sort Val = ?
    operation get(s: C, k: Key) -> Val
  end
  sort MemStore
    provides Storage[C = MemStore, Key = String, Val = Int64]
    entity memStore
    operation get(s: MemStore, k: String) -> Int64 = 0
  end
  sort Sp
    sort P = ?
    effects E = ?
    requires Storage[C = P]
    operation size(s: Sp) -> Int64
    operation op(s: Sp, x: (a: P.Key, b: List)) -> Int64
  end
  sort Car
    entity car(n: Int64)
    provides Sp[P = MemStore, E = {Error}]
    operation size(c: Car) -> Int64 = c.n
    operation op(c: Car, x: (a: MemStore.Key, b: List)) -> Int64 = 42
  end
  operation go() -> Int64 =
    let k = car(n: 42)
    Sp.size(k)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["its own member 'op' does not fit"],
        "a rigid type projection under a rebuilt binding",
    );
}

// ── a call with no receiver ─────────────────────────────────────────────────────────────────

/// A CALL WITH NO RECEIVER IS TYPED BY ITS ARGUMENT. `Pair.mk(x: B) -> Pair[A = B, B = Int64]`
/// called as `Pair.mk(o)` inside an unannotated lambda: the call's type named the callee's own
/// `B`, not the lambda's `o`, so `g(7)` passed for a `String` and `String.length` met 7 at run time
/// (MEASURED on the tree the ninth review saw; the tree before it refused "length.s").
/// FAILS under ledger parts 105 and 106.
#[test]
fn a_receiverless_call_in_a_lambda_is_typed_by_its_argument() {
    let src = r#"
namespace wi0rp29r9.recvless_wrong
  import anthill.prelude.{Int64, String, List}
  sort Pair
    sort A = ?
    sort B = ?
    entity pair(l: A, r: B)
    operation mk(x: B) -> Pair[A = B, B = Int64] = pair(l: x, r: 1)
  end
  operation go() -> Int64 =
    let g = lambda (o) -> Pair.mk(o).l
    String.length(g(7)) + 41
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["length.s (op-arg): expected String, got Int64"],
        "a receiverless call's result read at another type",
    );
}

/// … AND RUNS WHERE THE ARGUMENT IS RIGHT: `g("s")`'s head is a `String` (MEASURED: refused on the
/// tree the ninth review saw — the call's type named one variable two ways by carrier). Runs to
/// 1 + 41.
/// FAILS under ledger part 107 together with 105 or 106.
#[test]
fn a_receiverless_call_in_a_lambda_runs_on_a_right_argument() {
    let src = r#"
namespace wi0rp29r9.recvless_right
  import anthill.prelude.{Int64, String, List}
  import anthill.prelude.List.{cons, nil}
  sort Pair
    sort A = ?
    sort B = ?
    entity pair(l: A, r: B)
    operation mk(x: B) -> Pair[A = List[T = B], B = Int64] = pair(l: [x], r: 1)
  end
  operation go() -> Int64 =
    let g = lambda (o) -> Pair.mk(o).l
    match g("s")
      case cons(h, t) -> String.length(h) + 41
      case nil -> 0
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.recvless_right.go"), Ok(42));
}

/// … AND THROUGH A CALLBACK: `Pair.mk(f: (u: Int64) -> B)` called as `Pair.mk(lambda (u) -> o)`
/// meets `o`'s variable one level down, where the argument-first unification bound it to the
/// callee's own `B` and the call's type named nothing of the caller's — so `g(7)` passed for a
/// `String` again and `String.length` met 7 at run time (MEASURED: the tenth pass before its
/// /simplify; the tree the eighth review saw refused it only because it read `.l` as the
/// result's own `Int64`).
/// FAILS under ledger part 124.
#[test]
fn a_receiverless_call_through_a_callback_is_typed_by_its_argument() {
    let src = r#"
namespace wi0rp29r9.recvless_depth
  import anthill.prelude.{Int64, String, List}
  sort Pair
    sort A = ?
    sort B = ?
    entity pair(l: A, r: B)
    operation mk(f: (u: Int64) -> B) -> Pair[A = B, B = Int64] = pair(l: f(1), r: 1)
  end
  operation go() -> Int64 =
    let g = lambda (o) -> Pair.mk(lambda (u) -> o).l
    String.length(g(7)) + 41
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["length.s (op-arg): expected String, got Int64"],
        "a receiverless call's result through a callback read at another type",
    );
}

/// CONTROL: the right argument runs, `g("x")`'s length plus 41. Runs either way by design — the
/// result left unrelated to `o` reads as anything — where the tree the eighth review saw refused
/// it, reading `.l` as `Int64`.
#[test]
fn a_receiverless_call_through_a_callback_is_typed_by_its_argument_control() {
    let src = r#"
namespace wi0rp29r9.recvless_depth_right
  import anthill.prelude.{Int64, String, List}
  sort Pair
    sort A = ?
    sort B = ?
    entity pair(l: A, r: B)
    operation mk(f: (u: Int64) -> B) -> Pair[A = B, B = Int64] = pair(l: f(1), r: 1)
  end
  operation go() -> Int64 =
    let g = lambda (o) -> Pair.mk(lambda (u) -> o).l
    String.length(g("x")) + 41
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.recvless_depth_right.go"), Ok(42));
}

/// A FIELD OF A RETURN A TYPE CONSTRUCTOR REDUCED TAKES THE CALLER'S ANNOTATION. `Pair.mk(1).l` is
/// `List[T = B]` with `B` the call's own, open; the existential opening read that WRITTEN slot as
/// rigid, so `let xs: List[T = Int64] = q.l` was refused (MEASURED on the tree the ninth review
/// saw). Only a slot the reduced return leaves out is opened. Runs to 42.
/// FAILS under ledger part 107.
#[test]
fn a_field_of_a_reduced_return_takes_the_callers_annotation() {
    let src = r#"
namespace wi0rp29r9.reduced_field
  import anthill.prelude.{Int64, String, List, Option, Bool}
  sort Pair
    sort A = ?
    sort B = ?
    entity pair(l: A, r: B)
    operation mk(x: Int64) -> Pair[A = List[T = B], B = Int64] = pair(l: [], r: x)
  end
  operation go() -> Int64 =
    let q = Pair.mk(1)
    let xs: List[T = Int64] = q.l
    42
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.reduced_field.go"), Ok(42));
}

/// … AND OFF ANOTHER SORT'S OPERATION, `Maker.mk` (MEASURED: refused "xs.annotation" on the tree
/// the ninth review saw). Runs to 42.
/// FAILS under ledger part 107.
#[test]
fn a_field_of_another_sorts_reduced_return_takes_the_callers_annotation() {
    let src = r#"
namespace wi0rp29r9.reduced_maker
  import anthill.prelude.{Int64, String, List, Option, Bool}
  sort Pair
    sort A = ?
    sort B = ?
    entity pair(l: A, r: B)
  end
  sort Maker
    sort B = ?
    operation mk(x: Int64) -> Pair[A = List[T = B], B = Int64] = pair(l: [], r: x)
  end
  operation go() -> Int64 =
    let q = Maker.mk(1)
    let xs: List[T = Int64] = q.l
    42
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.reduced_maker.go"), Ok(42));
}

/// A PATTERN BINDER OVER AN ALIAS-TYPED SCRUTINEE IS TYPED BY WHAT THE ALIAS STANDS FOR. `x:
/// IntS` under `sort IntS = Strm[T = Int64]`: `case strm(a)` bound `a` to `Strm`'s own `T`, which
/// the call above then decided — `a + b` over two such binders ran on the tree the ninth review
/// saw only because `T` stayed the callee's variable, and was refused "missing `requires
/// Additive`" once a call without a receiver bound it the other way (MEASURED: the tenth pass's
/// first cut, on `wi_0rp29_member_rule_test`'s alias row). Runs to 40 + 2.
/// FAILS under ledger part 119.
#[test]
fn a_pattern_binder_over_an_alias_typed_scrutinee_is_the_aliass_type() {
    let src = r#"
namespace wi0rp29r9.alias_binder
  import anthill.prelude.{Int64, Bool, String, List, Error}
  sort Strm
    sort T = ?
    entity strm(v: T)
  end
  sort IntS = Strm[T = Int64]
  operation op(x: IntS, y: IntS) -> Int64 =
    match x
      case strm(a) ->
        match y
          case strm(b) -> a + b
  operation go() -> Int64 = op(strm(v: 40), strm(v: 2))
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.alias_binder.go"), Ok(42));
}

/// … AND A WRONG USE OF IT IS REFUSED: `String.length(a)` over an `Int64` payload loaded on every
/// build (MEASURED), the binder typed by nothing. Nothing runs: the program is wrong.
/// FAILS under ledger part 119.
#[test]
fn a_pattern_binder_over_an_alias_typed_scrutinee_is_checked() {
    let src = r#"
namespace wi0rp29r9.alias_binder_wrong
  import anthill.prelude.{Int64, Bool, String, List, Error}
  sort Strm
    sort T = ?
    entity strm(v: T)
  end
  sort IntS = Strm[T = Int64]
  operation op(x: IntS) -> Int64 =
    match x
      case strm(a) -> String.length(a)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["length.s (op-arg): expected String, got Int64"],
        "an Int64 binder passed for a String",
    );
}

/// CONTROL: the alias written out. Runs to 42 either way by design.
#[test]
fn a_pattern_binder_over_an_alias_typed_scrutinee_is_the_aliass_type_control() {
    let src = r#"
namespace wi0rp29r9.alias_binder_written
  import anthill.prelude.{Int64, Bool, String, List, Error}
  sort Strm
    sort T = ?
    entity strm(v: T)
  end
  operation op(x: Strm[T = Int64], y: Strm[T = Int64]) -> Int64 =
    match x
      case strm(a) ->
        match y
          case strm(b) -> a + b
  operation go() -> Int64 = op(strm(v: 40), strm(v: 2))
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.alias_binder_written.go"), Ok(42));
}

/// … AND WHAT AN ARGUMENT BRINGS IN THROUGH A PROJECTION IS THE ARGUMENT'S: `Getter.getl(q)` over
/// `-> FieldOf[T = Pair[A = p.A, B = p.B], Name = "l"]` with `q` of `Pair.mk(1)`'s type. The
/// elimination writes `q`'s own `List[T = B]` into the declared return before σ walks it, and
/// read as the return's own that variable was opened: "xs.annotation: expected List[T = Int64],
/// got List[T = ?T]" (MEASURED: this pass's /simplify, its first reading of what the arguments
/// put there; the tree before it loaded this). The callee is a bodyless spec operation, so
/// nothing runs: the verdict measured is the call's result type meeting the annotation.
/// FAILS under ledger part 128.
#[test]
fn a_projection_into_a_reduced_return_keeps_the_arguments_variable() {
    let src = r#"
namespace wi0rp29r9.reduced_projection
  import anthill.prelude.{Int64, String, List, FieldOf}
  sort Pair
    sort A = ?
    sort B = ?
    entity pair(l: A, r: B)
    operation mk(x: Int64) -> Pair[A = List[T = B], B = Int64] = pair(l: [], r: x)
  end
  sort Getter
    operation getl(p: Pair) -> FieldOf[T = Pair[A = p.A, B = p.B], Name = "l"]
  end
  operation go() -> Int64 =
    let q = Pair.mk(1)
    let xs: List[T = Int64] = Getter.getl(q)
    42
end
"#;
    let errs = load_errors(src);
    assert!(errs.is_empty(), "the call's result met the annotation, got:\n{}", errs.join("\n"));
}

/// CONTROL: a DECLARED field's omitted slot is still a type its holder picked — `h.s` of a
/// `Stream[T = Int64]` field is no pure stream. Refused either way by design; nothing runs.
#[test]
fn a_declared_fields_unwritten_slot_is_still_opened_control() {
    let src = r#"
namespace wi0rp29r9.field_existential
  import anthill.prelude.{Int64, String, List, Stream, Error, FiniteStream}
  sort Holder
    entity holder(s: Stream[T = Int64])
  end
  operation takes_pure(s: Stream[T = Int64, E = {}]) -> Int64 = 1
  operation f(h: Holder) -> Int64 = takes_pure(h.s)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["takes_pure.s (op-arg): expected Stream[T = Int64, E = {}]"],
        "a declared field's unwritten row passed for a pure stream",
    );
}

/// … AND SO IS ONE WRITTEN `?`: `s: Stream[T = Int64, E = ?]` is the same type as the omitted
/// slot. A field read is a reduced return, and the tenth pass kept every written variable of one
/// as the caller's — this `?` among them, a variable the FIELD's declaration brought in — so `h.s`
/// passed for a pure stream (MEASURED: the tenth pass before its /simplify; refused on the tree
/// the eighth review saw). Only what the arguments put there stays. Nothing runs: the program is
/// wrong.
/// FAILS under ledger part 122.
#[test]
fn a_declared_fields_written_wildcard_is_opened() {
    let src = r#"
namespace wi0rp29r9.field_wildcard
  import anthill.prelude.{Int64, String, List, Stream, Error, FiniteStream}
  sort Holder
    entity holder(s: Stream[T = Int64, E = ?])
  end
  operation takes_pure(s: Stream[T = Int64, E = {}]) -> Int64 = 1
  operation f(h: Holder) -> Int64 = takes_pure(h.s)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["takes_pure.s (op-arg): expected Stream[T = Int64, E = {}]"],
        "a declared field's written wildcard passed for a pure stream",
    );
}

// ── the declaration rule, through a provider ────────────────────────────────────────────────

/// A MEMBER WIDER THROUGH A SPEC ITS PARAMETER'S TYPE PROVIDES FITS. `count(c: Car, xs:
/// FiniteCollection[E = {}])` against the spec's `xs: List[T = Int64]` — `List` provides
/// `FiniteCollection`, so every argument the spec admits the member takes; the ninth pass compared
/// the two heads and refused "takes less than the spec's" (MEASURED on the tree the ninth review
/// saw; the tree before it ran this). Runs to 3 + 39.
/// FAILS under ledger part 108.
#[test]
fn a_member_wider_through_a_spec_its_parameter_provides_fits() {
    let src = r#"
namespace wi0rp29r9.wider_stdlib
  import anthill.prelude.{Int64, String, List, FiniteCollection}
  sort Sp
    sort T = ?
    operation count(s: Sp, xs: List[T = T]) -> Int64
  end
  sort Car
    entity car(n: Int64)
    provides Sp[T = Int64]
    operation count(c: Car, xs: FiniteCollection[E = {}]) -> Int64 = FiniteCollection.size(xs) + 39
  end
  operation go() -> Int64 = Sp.count(car(n: 1), [1, 2, 3])
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.wider_stdlib.go"), Ok(42));
}

/// … A USER SPEC: `op(c: Car, x: Describe)` against the spec's `x: Box[T = Int64]`, `Box
/// provides Describe[K = T]` (MEASURED: refused on the tree the ninth review saw). Runs to 41 + 1.
/// FAILS under ledger part 108.
#[test]
fn a_member_wider_through_a_user_spec_its_parameter_provides_fits() {
    let src = r#"
namespace wi0rp29r9.wider_user
  import anthill.prelude.{Int64, String, List}
  sort Describe
    sort K = ?
    operation tag(d: Describe) -> Int64
  end
  sort Box
    sort T = ?
    entity box(t: T)
    provides Describe[K = T]
    operation tag(b: Box) -> Int64 = 41
  end
  sort Sp
    sort T = ?
    operation op(s: Sp, x: Box[T = T]) -> Int64
  end
  sort Car
    entity car(n: Int64)
    provides Sp[T = Int64]
    operation op(c: Car, x: Describe) -> Int64 = Describe.tag(x) + 1
  end
  operation go() -> Int64 = Sp.op(car(n: 1), box(t: 5))
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.wider_user.go"), Ok(42));
}

/// … AND A MEMBER RETURNING A PROVIDER OF THE SPEC'S RETURN: `mk(c: Car) -> Box[T = Int64]`
/// against `mk(s: Sp) -> Describe[K = K]`, `K` unbound (MEASURED: refused "the member returns
/// `Box[T = Int64]`, which is not a subtype of the spec's `Describe[K = ?_]`" on the tree the ninth
/// review saw). Runs to 42.
/// FAILS under ledger part 108.
#[test]
fn a_member_returning_a_provider_of_the_specs_return_fits() {
    let src = r#"
namespace wi0rp29r9.narrower_return
  import anthill.prelude.{Int64, String, List}
  sort Describe
    sort K = ?
    operation tag(d: Describe) -> Int64
  end
  sort Box
    sort T = ?
    entity box(n: Int64, t: T)
    provides Describe[K = T]
    operation tag(b: Box) -> Int64 = b.n
  end
  sort Sp
    sort T = ?
    sort K = ?
    operation mk(s: Sp) -> Describe[K = K]
  end
  sort Car
    entity car(n: Int64)
    provides Sp[T = Int64]
    operation mk(c: Car) -> Box[T = Int64] = box(n: 42, t: 1)
  end
  operation go() -> Int64 = Describe.tag(Sp.mk(car(n: 1)))
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.narrower_return.go"), Ok(42));
}

/// CONTROL: a provider of ANOTHER instance of the spec's return does not fit — `Box[T = Int64]`
/// provides `Describe[K = Int64]`, the spec returns `Describe[K = String]`. Refused either way by
/// design.
#[test]
fn a_member_returning_a_provider_of_the_specs_return_fits_control() {
    let src = r#"
namespace wi0rp29r9.narrower_return_wrong
  import anthill.prelude.{Int64, String, List, Option}
  sort Describe
    sort K = ?
    operation tag(d: Describe) -> Int64
  end
  sort Box
    sort T = ?
    entity box(n: Int64, t: T)
    provides Describe[K = T]
    operation tag(b: Box) -> Int64 = b.n
  end
  sort Sp
    sort T = ?
    operation mk(s: Sp) -> T
  end
  sort Car
    entity car(n: Int64)
    provides Sp[T = Describe[K = String]]
    operation mk(c: Car) -> Box[T = Int64] = box(n: 42, t: 1)
  end
  operation go() -> Int64 = Describe.tag(Sp.mk(car(n: 1)))
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["the member returns `Box[T = Int64]`, which is not a subtype of the spec's `Describe[K = String]`"],
        "a provider of another instance of the spec's return",
    );
}

/// AN UNBRACED ROW LABEL IN A PROVISION IS THE ROW HOLDING IT. `provides Sp[E = Error[String]]`
/// binds the row `{Error[String]}`; the member `tail(s: Car) -> Car` returns the carrier, which
/// provides `Sp` at that row — the variance check compared the bare label with the braced row as
/// two types, and the member was refused "not a subtype of the spec's `Sp[E = {Error[T =
/// String]}]`" (MEASURED on the tree the ninth review saw; the tree before it ran this). Runs to
/// 42.
/// FAILS under ledger part 110.
#[test]
fn an_unbraced_row_label_in_a_provision_is_the_row_holding_it() {
    let src = r#"
namespace wi0rp29r9.row_label
  import anthill.prelude.{Int64, String, List, Error}
  sort Sp
    effects E = ?
    operation size(s: Sp) -> Int64
    operation tail(s: Sp) -> Sp
  end
  sort Car
    entity car(v: Int64)
    provides Sp[E = Error[String]]
    operation size(s: Car) -> Int64 = s.v
    operation tail(s: Car) -> Car = s
  end
  operation go() -> Int64 = Sp.size(Sp.tail(car(v: 42)))
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.row_label.go"), Ok(42));
}

/// CONTROL: the braced spelling. Runs to 42 either way by design.
#[test]
fn an_unbraced_row_label_in_a_provision_is_the_row_holding_it_control() {
    let src = r#"
namespace wi0rp29r9.row_braced
  import anthill.prelude.{Int64, String, List, Error}
  sort Sp
    effects E = ?
    operation size(s: Sp) -> Int64
    operation tail(s: Sp) -> Sp
  end
  sort Car
    entity car(v: Int64)
    provides Sp[E = {Error[String]}]
    operation size(s: Car) -> Int64 = s.v
    operation tail(s: Car) -> Car = s
  end
  operation go() -> Int64 = Sp.size(Sp.tail(car(v: 42)))
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.row_braced.go"), Ok(42));
}

/// A WRITTEN `?` ONLY THE RETURN READS STAYS OPEN ON THE SPEC'S SIDE. `step(s: Sp, k: Option[T =
/// s.T]) -> Sp[T = s.T]` at `provides Sp[T = Car[V = ?]]` — no parameter reads the `?` (`k`'s
/// projection is the binding as written, an instance of its own), so the member returning its own
/// carrier may meet it with anything; made a fixed unknown there, the member was "not a subtype of
/// the spec's `Sp[T = Car[V = ?_]]`" (MEASURED on the tree the ninth review saw; the tree before it
/// ran this). Runs to 42.
/// FAILS under ledger part 113.
#[test]
fn a_written_wildcard_only_the_return_reads_stays_open() {
    let src = r#"
namespace wi0rp29r9.recv_instance
  import anthill.prelude.{Int64, String, List, Option}
  import anthill.prelude.Option.{some, none}
  sort Sp
    sort T = ?
    operation size(s: Sp) -> Int64
    operation step(s: Sp, k: Option[T = s.T]) -> Sp[T = s.T]
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = Car[V = ?]]
    operation size(c: Car) -> Int64 = 42
    operation step(c: Car, k: Option[T = c.T]) -> Car = c
  end
  operation go() -> Int64 =
    let c: Car[V = Int64] = car(v: 1)
    Sp.size(Sp.step(c, none))
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.recv_instance.go"), Ok(42));
}

/// CONTROL: the slot written. Runs to 42 either way by design.
#[test]
fn a_written_wildcard_only_the_return_reads_stays_open_control() {
    let src = r#"
namespace wi0rp29r9.recv_written
  import anthill.prelude.{Int64, String, List, Option}
  import anthill.prelude.Option.{some, none}
  sort Box
    sort B = ?
    entity box(b: B)
  end
  sort Sp
    sort T = ?
    operation size(s: Sp) -> Int64
    operation step(s: Sp, k: Option[T = s.T]) -> Sp[T = s.T]
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = Box[B = Int64]]
    operation size(c: Car) -> Int64 = 42
    operation step(c: Car, k: Option[T = c.T]) -> Car = c
  end
  operation go() -> Int64 =
    let c: Car[V = Int64] = car(v: 1)
    Sp.size(Sp.step(c, none))
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.recv_written.go"), Ok(42));
}

/// A SLOT ONLY THE RETURN READS STAYS OPEN ON THE SPEC'S SIDE. `provides Store[State = Box[T =
/// Int64]]` leaves `Box`'s `U` unwritten; the member returns `Box[T = Int64]` itself, its own `U`
/// the same unwritten slot — and the two printed alike: "`Box[T = Int64, U = ?U]` … not a subtype
/// of the spec's `Box[T = Int64, U = ?U]`" (MEASURED on the tree the ninth review saw; the tree
/// before it ran this). Runs to 42.
/// FAILS under ledger parts 112 and 113.
#[test]
fn a_slot_only_the_return_reads_stays_open_on_the_specs_side() {
    let src = r#"
namespace wi0rp29r9.return_open
  import anthill.prelude.{Int64, String, List}
  sort Box
    sort T = ?
    sort U = ?
    entity box(t: T, u: U)
  end
  sort Store
    sort State = ?
    operation fresh(s: Store, n: Int64) -> State
  end
  sort Carrier
    entity carrier(k: Int64)
    provides Store[State = Box[T = Int64]]
    operation fresh(s: Store, n: Int64) -> Box[T = Int64] = box(t: n, u: "str")
  end
  operation go() -> Int64 =
    let b: Box[T = Int64] = Store.fresh(carrier(k: 1), 42)
    b.t
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.return_open.go"), Ok(42));
}

/// A RETURNED FUNCTION'S PARAMETER IS ONE TYPE ON BOTH SIDES OF THE RULE. `mk(s: Sp) -> (xs: List)
/// -> Base` and the member's `-> (xs: List) -> Carrier`: the bare `List` under the returned
/// arrow's parameter took one variable for the comparison and another for the opening, and the
/// member was refused "returns `List[T = ?T] -> Carrier`, which is not …" (MEASURED on the tree
/// the ninth review saw; the tree before it ran this). Runs to 42.
/// FAILS under ledger part 114.
#[test]
fn a_returned_functions_parameter_is_one_type_on_both_sides() {
    let src = r#"
namespace wi0rp29r9.returned_fn
  import anthill.prelude.{Int64, String, List}
  sort Base
    sort B = ?
    operation tag(b: Base) -> Int64
  end
  sort Carrier
    entity carrier(n: Int64)
    provides Base[B = Int64]
    operation tag(b: Carrier) -> Int64 = b.n
  end
  sort Sp
    sort T = ?
    operation mk(s: Sp) -> (xs: List) -> Base
  end
  sort Car
    entity car(n: Int64)
    provides Sp[T = Int64]
    operation mk(c: Car) -> (xs: List) -> Carrier = lambda (xs) -> carrier(n: 42)
  end
  operation go() -> Int64 =
    let f = Sp.mk(car(n: 1))
    Base.tag(f([1, 2]))
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.returned_fn.go"), Ok(42));
}

/// A CARRIER-PARAMETER TYPE IS READ AT THE PROVISION, NOT AS THE SPEC'S TEMPLATE. `size(y: T)` at
/// `provides Sp[T = Car, E9 = {Error}]` and the member's `size(y: Sp)` — every type in the spec's
/// signature took the spec's template, so `T` read as the bare spec and the member was "parameter
/// 1 (`y: Sp`) takes less than the spec's" (MEASURED on the tree the ninth review saw; the tree
/// before it ran this). Only a type headed by the spec takes the template. Runs to 42.
/// FAILS under ledger part 115.
#[test]
fn a_carrier_parameter_type_is_read_at_the_provision() {
    let src = r#"
namespace wi0rp29r9.cp_at_provision
  import anthill.prelude.{Int64, String, List, Error}
  sort Sp
    sort T = ?
    effects E9 = ?
    operation size(y: T) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = Car, E9 = {Error}]
    operation size(y: Sp) -> Int64 = 42
  end
  operation go() -> Int64 =
    let k: Car[V = Int64] = car(v: 1)
    Sp.size(k)
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.cp_at_provision.go"), Ok(42));
}

/// … AND A WITNESS'S MEMBER TYPED BY THE SPEC: `peek(c: Holder)` behind `peek(c: C)` at
/// `BoxHolder provides Holder[C = Box]` takes any provider of `Holder`, the box among them — the
/// receiver typed by the carrier parameter is the spec at this provision, not the box: read as
/// the box, the relation sees no `Box` providing `Holder` (only the witness says so) and the
/// member was refused as taking less (MEASURED: the tenth pass's first cut; it ran on every build
/// before). Runs to 40 + 2.
/// FAILS under ledger part 115 read as the bound carrier (the first cut).
#[test]
fn a_witness_member_typed_by_the_spec_takes_the_witness_carrier() {
    let src = r#"
namespace wi0rp29r9.byspec_witness
  import anthill.prelude.{Int64, String, List}
  sort Holder
    sort C = ?
    operation peek(c: C) -> Int64
    operation size(h: Holder) -> Int64
  end
  sort Box
    sort B = ?
    entity box(inner: B)
  end
  sort BoxHolder
    import anthill.prelude.Int64
    provides Holder[C = Box]
    operation peek(c: Holder) -> Int64 = 40
    operation size(h: Holder) -> Int64 = 1
  end
  operation go() -> Int64 = Holder.peek(box(inner: 1)) + 2
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.byspec_witness.go"), Ok(42));
}

/// A RECEIVER'S PROJECTION IN A PARAMETER TIES NOTHING TO THE RETURN. `op(s: Sp, x: s.T) -> T` at
/// `provides Sp[T = Box]`: `x: s.T` is the binding as written, an instance of its own (§8.7), so
/// `Box`'s unwritten slot is read by the return only, and the member is the one to leave it open
/// — `op(c: Car, x: Box) -> Box` loads, as on every build before this pass. Counting the
/// projection as reading the slot (the tenth pass's first cut) refused it (MEASURED), and the
/// repair its refusal named was refused on every build. Nothing runs: no call is made.
/// FAILS only under the first cut the ledger names; no part in the tree.
#[test]
fn a_receivers_projection_in_a_parameter_ties_nothing_to_the_return() {
    let src = r#"
namespace wi0rp29r9.proj_untied
  import anthill.prelude.{Int64, String, List}
  sort Box
    sort U = ?
    entity box(u: U)
  end
  sort Sp
    sort T = ?
    operation op(s: Sp, x: s.T) -> T
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = Box]
    operation op(c: Car, x: Box) -> Box = x
  end
end
"#;
    let errs = load_errors(src);
    assert!(errs.is_empty(), "the member leaves open a slot only the return reads: {errs:#?}");
}

// ── a projection off a value path ───────────────────────────────────────────────────────────

/// A LAMBDA'S HINT THROUGH A PROJECTION OFF A PARAMETER IS THE CALLER'S PATH. `each(s: State, k:
/// s.provider.K, f: (x: s.provider.K) -> Int64)` called as `each(st, j, lambda (x) -> 42)` — the
/// hint re-keyed `s` to the argument's VARIABLE, not its path, and the lambda was refused "expected
/// st.provider.K -> Int64, got s.provider.K -> Int64" (MEASURED on the tree the ninth review saw;
/// the tree before it ran this). Runs to 42.
/// FAILS under ledger part 109.
#[test]
fn a_lambda_hint_through_a_projection_is_the_callers_path() {
    let src = r#"
namespace wi0rp29r9.path_lambda
  import anthill.prelude.{Int64, String, List}
  sort DataProvider
    sort P = ?
    sort K = ?
  end
  sort State
    sort P = ?
    requires DataProvider[P = P]
    entity state(provider: P)
  end
  sort MemStore
    entity mem(n: Int64)
    provides DataProvider[P = MemStore, K = Int64]
  end
  operation each(s: State, k: s.provider.K, f: (x: s.provider.K) -> Int64) -> Int64 = f(k)
  operation fwd(st: State, j: st.provider.K) -> Int64 = each(st, j, lambda (x) -> 42)
  operation go() -> Int64 =
    let st: State[P = MemStore] = state(provider: mem(n: 1))
    fwd(st, 41)
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.path_lambda.go"), Ok(42));
}

/// … AND A PARAMETER TYPED BY A PROJECTION TAKES A FIELD-PATH ARGUMENT: `check(w.st, j)` with `j:
/// w.st.provider.K` (MEASURED: refused "check.k: expected s.provider.K, got w.st.provider.K" on the
/// tree the ninth review saw). Runs to 42.
/// FAILS under ledger part 109.
#[test]
fn a_projection_parameter_takes_a_field_path_argument() {
    let src = r#"
namespace wi0rp29r9.path_field
  import anthill.prelude.{Int64, String, List}
  sort DataProvider
    sort P = ?
    sort K = ?
  end
  sort State
    sort P = ?
    requires DataProvider[P = P]
    entity state(provider: P)
  end
  sort MemStore
    entity mem(n: Int64)
    provides DataProvider[P = MemStore, K = Int64]
  end
  sort World
    sort P = ?
    requires DataProvider[P = P]
    entity world(st: State[P = P])
  end
  operation check(s: State, k: s.provider.K) -> Int64 = 42
  operation fwd(w: World, j: w.st.provider.K) -> Int64 = check(w.st, j)
  operation go() -> Int64 =
    let w: World[P = MemStore] = world(st: state(provider: mem(n: 1)))
    fwd(w, 41)
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.path_field.go"), Ok(42));
}

/// CONTROL: a key of ANOTHER world's path is another type. Refused either way by design.
#[test]
fn a_projection_parameter_takes_a_field_path_argument_control() {
    let src = r#"
namespace wi0rp29r9.path_other
  import anthill.prelude.{Int64, String, List, Option}
  sort DataProvider
    sort P = ?
    sort K = ?
    operation key(p: P) -> Int64
  end
  sort State
    sort P = ?
    requires DataProvider[P = P]
    entity state(provider: P)
  end
  sort World
    sort P = ?
    requires DataProvider[P = P]
    entity world(st: State[P = P], n: Int64)
  end
  sort MemStore
    entity mem(n: Int64)
    provides DataProvider[P = MemStore, K = Int64]
    operation key(p: MemStore) -> Int64 = p.n
  end
  operation check(s: State, k: s.provider.K) -> Int64 = 42
  operation fwd(w: World, v: World, j: v.st.provider.K) -> Int64 = check(w.st, j)
  operation go() -> Int64 =
    let w: World[P = MemStore] = world(st: state(provider: mem(n: 1)), n: 1)
    fwd(w, w, 41)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["check.k (op-arg)", "got v.st.provider.K"],
        "another world's key",
    );
}

/// … AND THROUGH A `let` ALIAS THE RETURN NAMES THE RECEIVER AS THE PARAMETERS DO. After `let t =
/// st`, `check(t, get(t, j))`: `check`'s parameter read its receiver's path through the alias,
/// `st.provider.K`, while `get`'s return kept the variable, `t.provider.K`, and the call was
/// refused "check.k: expected st.provider.K, got t.provider.K" — two spellings of one path
/// (MEASURED: the tenth pass before its /simplify; the tree the eighth review saw ran it, both
/// sides saying `t`). Runs to 42.
/// FAILS under ledger part 123.
#[test]
fn a_returned_projection_names_a_let_aliass_receiver_as_its_parameters_do() {
    let src = r#"
namespace wi0rp29r9.alias_return
ALIAS_PRELUDE
  operation get(s: State, k: s.provider.K) -> s.provider.K = k
  operation check(s: State, k: s.provider.K) -> Int64 = 42
  operation fwd(st: State, j: st.provider.K) -> Int64 =
    let t = st
    check(t, get(t, j))
  operation go() -> Int64 =
    let st: State[P = MemStore] = state(provider: mem(n: 1))
    fwd(st, 41)
end
"#
    .replace("ALIAS_PRELUDE", ALIAS_PRELUDE);
    assert_eq!(run_src(&src, "wi0rp29r9.alias_return.go"), Ok(42));
}

/// … AND MEETS AN ANNOTATION WRITTEN THROUGH THE ALIAS'S TARGET: `let x: st.provider.K = get(t, j)`
/// (MEASURED: refused "x.annotation: expected st.provider.K, got t.provider.K" on every build
/// before it). Runs to 42.
/// FAILS under ledger part 123.
#[test]
fn a_returned_projection_through_a_let_alias_meets_its_annotation() {
    let src = r#"
namespace wi0rp29r9.alias_annotation
ALIAS_PRELUDE
  operation get(s: State, k: s.provider.K) -> s.provider.K = k
  operation fwd(st: State, j: st.provider.K) -> Int64 =
    let t = st
    let x: st.provider.K = get(t, j)
    42
  operation go() -> Int64 =
    let st: State[P = MemStore] = state(provider: mem(n: 1))
    fwd(st, 41)
end
"#
    .replace("ALIAS_PRELUDE", ALIAS_PRELUDE);
    assert_eq!(run_src(&src, "wi0rp29r9.alias_annotation.go"), Ok(42));
}

/// … AND A LAMBDA'S HINT DOES TOO: after `let t = st`, `each(t, j, lambda (x) -> 42)` hinted the
/// lambda `t.provider.K -> Int64` against the slot's `st.provider.K -> Int64` (MEASURED: refused
/// "each.f" on the tenth pass before its /simplify; the tree the eighth review saw ran it). Runs
/// to 42.
/// FAILS under ledger part 123.
#[test]
fn a_lambda_hint_names_a_let_aliass_receiver_as_the_call_does() {
    let src = r#"
namespace wi0rp29r9.alias_hint
ALIAS_PRELUDE
  operation each(s: State, k: s.provider.K, f: (x: s.provider.K) -> Int64) -> Int64 = f(k)
  operation fwd(st: State, j: st.provider.K) -> Int64 =
    let t = st
    each(t, j, lambda (x) -> 42)
  operation go() -> Int64 =
    let st: State[P = MemStore] = state(provider: mem(n: 1))
    fwd(st, 41)
end
"#
    .replace("ALIAS_PRELUDE", ALIAS_PRELUDE);
    assert_eq!(run_src(&src, "wi0rp29r9.alias_hint.go"), Ok(42));
}

/// … AND A `let` ANNOTATION THROUGH THE ALIAS NAMES THE ALIAS'S TARGET, ITS RECEIVER COMPOUND:
/// `let k: t.provider.K = get(t, j)`. The annotation reaches the alias reading on the TERM
/// carrier, off its pattern, where a compound receiver read as no path, so it stayed keyed to `t`
/// while the call said `st`: refused "k.annotation: expected t.provider.K, got st.provider.K",
/// and on every build before this pass, where both said `t`, refused at `check(st, k)`
/// (MEASURED). Runs to 42.
/// FAILS under ledger part 127.
#[test]
fn a_let_annotation_through_an_alias_names_its_target() {
    let src = r#"
namespace wi0rp29r9.alias_let
ALIAS_PRELUDE
  operation get(s: State, k: s.provider.K) -> s.provider.K = k
  operation check(s: State, k: s.provider.K) -> Int64 = 42
  operation fwd(st: State, j: st.provider.K) -> Int64 =
    let t = st
    let k: t.provider.K = get(t, j)
    check(st, k)
  operation go() -> Int64 =
    let st: State[P = MemStore] = state(provider: mem(n: 1))
    fwd(st, 41)
end
"#
    .replace("ALIAS_PRELUDE", ALIAS_PRELUDE);
    assert_eq!(run_src(&src, "wi0rp29r9.alias_let.go"), Ok(42));
}

/// The sorts the four `let`-alias rows above share.
const ALIAS_PRELUDE: &str = r#"  import anthill.prelude.{Int64, String, List}
  sort DataProvider
    sort P = ?
    sort K = ?
  end
  sort State
    sort P = ?
    requires DataProvider[P = P]
    entity state(provider: P)
  end
  sort MemStore
    entity mem(n: Int64)
    provides DataProvider[P = MemStore, K = Int64]
  end"#;

/// A RETURNED ARROW'S ROW TAKES THE CALL'S EFFECT RE-KEY. `mk(p) -> (u: Int64) -> Unit @
/// {Modify[p]}` called as `mk(h.c)` — the returned row was re-keyed to the argument's variables,
/// `Modify[h.c]`, where the call's own effects take the field path's HEAD, so `run2(h.c, mk(h.c))`
/// was refused "declares `Modify[T = p]`" (MEASURED on the tree the ninth review saw; the tree
/// before it ran this). Runs to 42.
/// FAILS under ledger part 111.
#[test]
fn a_returned_arrows_row_takes_the_field_paths_head() {
    let src = r#"
namespace wi0rp29r9.maker_head
  import anthill.prelude.{Int64, String, List, Cell, Modify, Unit}
  sort Hold
    entity hold(c: Cell[V = Int64])
  end
  operation run2(q: Cell[V = Int64], f: (u: Int64) -> Unit @ {Modify[q]}) -> Unit effects {Modify[q]} = f(42)
  operation mk(p: Cell[V = Int64]) -> (u: Int64) -> Unit @ {Modify[p]} = lambda (u: Int64) -> Cell.set(p, u)
  operation go() -> Int64 =
    let h = hold(c: Cell.new(1))
    let _ = run2(h.c, mk(h.c))
    Cell.get(h.c)
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.maker_head.go"), Ok(42));
}

/// CONTROL: a maker over ANOTHER holder's cell writes a cell the slot does not admit. Refused
/// either way by design.
#[test]
fn a_returned_arrows_row_takes_the_field_paths_head_control() {
    let src = r#"
namespace wi0rp29r9.maker_other
  import anthill.prelude.{Int64, String, List, Cell, Modify, Unit}
  sort Hold
    entity hold(c: Cell[V = Int64])
  end
  operation run2(q: Cell[V = Int64], f: (u: Int64) -> Unit @ {Modify[q]}) -> Unit effects {Modify[q]} = f(41)
  operation mk(p: Cell[V = Int64]) -> (u: Int64) -> Unit @ {Modify[p]} = lambda (u: Int64) -> Cell.set(p, Cell.get(p) + u)
  operation bump(h: Hold, k: Hold) -> Unit effects {Modify[h]} = run2(h.c, mk(k.c))
  operation go() -> Int64 =
    let h = hold(c: Cell.new(1))
    let k = hold(c: Cell.new(1))
    let _ = bump(h, k)
    Cell.get(k.c)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["run2.f (op-arg)", "which the closed row does not admit"],
        "a maker over another holder's cell",
    );
}

/// A SELF-RECURSIVE CALL'S RETURNED ROW IS RENAMED ONCE. Inside `rec(p, q, h, n)`, the call `rec(q,
/// h.c, h, n - 1)` returns a callback writing `q` — the caller's — which `{Modify[p], Modify[h]}`
/// does not admit. The return was re-keyed in two passes, by the variables and then by the field
/// paths' heads, and its caller's variables are the callee's own parameters: `Modify[p]` became
/// `Modify[q]` and then that `q` became `h`, and `rec` loaded (MEASURED: the tenth pass before its
/// /simplify; refused on the tree the eighth review saw). Nothing runs: the program is wrong.
/// FAILS under ledger part 125.
#[test]
fn a_self_recursive_calls_returned_row_is_renamed_once() {
    let src = r#"
namespace wi0rp29r9.rename_once
  import anthill.prelude.{Int64, String, List, Cell, Modify, Unit}
  sort Hold
    entity hold(c: Cell[V = Int64])
  end
  operation rec(p: Cell[V = Int64], q: Cell[V = Int64], h: Hold, n: Int64) -> (u: Int64) -> Unit @ {Modify[p], Modify[h]} =
    if n > 0 then rec(q, h.c, h, n - 1) else lambda (u: Int64) -> Cell.set(p, u)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["if.rule (rule)"],
        "a recursive callback writing an undeclared cell",
    );
}

/// … AND ONE WHOSE RETURN HOLDS A PROJECTION, which the elimination re-keys — `(u: p.V) -> Unit @
/// {…}` (MEASURED: loaded on the tenth pass before its /simplify, refused on the tree the eighth
/// review saw). Nothing runs: the program is wrong.
/// FAILS under ledger part 125.
#[test]
fn a_self_recursive_calls_returned_row_is_renamed_once_through_a_projection() {
    let src = r#"
namespace wi0rp29r9.rename_once_proj
  import anthill.prelude.{Int64, String, List, Cell, Modify, Unit}
  sort Hold
    entity hold(c: Cell[V = Int64])
  end
  operation rec(p: Cell[V = Int64], q: Cell[V = Int64], h: Hold, n: Int64) -> (u: p.V) -> Unit @ {Modify[p], Modify[h]} =
    if n > 0 then rec(q, h.c, h, n - 1) else lambda (u: Int64) -> Cell.set(p, u)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["if.rule (rule)"],
        "a recursive callback writing an undeclared cell, through a projection",
    );
}

/// CONTROL: declaring `Modify[q]` too, the recursive call's callback is admitted, and runs —
/// `rec(c1, c2, h, 1)` returns a callback writing `c2`. Runs to 42 either way by design.
#[test]
fn a_self_recursive_calls_returned_row_is_renamed_once_control() {
    let src = r#"
namespace wi0rp29r9.rename_once_ok
  import anthill.prelude.{Int64, String, List, Cell, Modify, Unit}
  sort Hold
    entity hold(c: Cell[V = Int64])
  end
  operation rec(p: Cell[V = Int64], q: Cell[V = Int64], h: Hold, n: Int64) -> (u: Int64) -> Unit @ {Modify[p], Modify[q], Modify[h]} =
    if n > 0 then rec(q, h.c, h, n - 1) else lambda (u: Int64) -> Cell.set(p, u)
  operation go() -> Int64 =
    let c1 = Cell.new(1)
    let c2 = Cell.new(2)
    let h = hold(c: Cell.new(3))
    let f = rec(c1, c2, h, 1)
    let _ = f(42)
    Cell.get(c2)
end
"#;
    assert_eq!(run_src(src, "wi0rp29r9.rename_once_ok.go"), Ok(42));
}

// ── what a refusal of the declaration rule says ─────────────────────────────────────────────

/// A REFUSAL SAYS "THE TWO TYPES PRINT ALIKE" ONLY WHERE TWO TYPES WERE COMPARED. A receiver whose
/// binding writes `Box`'s own parameter inside its own slot is refused for that, and no two types
/// were compared — the sentence the ninth pass appended was false there (MEASURED on the tree the
/// ninth review saw). Nothing runs: the provision is refused.
/// FAILS under ledger part 116.
#[test]
fn a_circular_binding_refusal_does_not_say_two_types_print_alike() {
    let src = r#"
namespace wi0rp29r9.says_circular
  import anthill.prelude.{Int64, List}
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
    let errs = load_errors(src);
    assert_refused_naming(
        &errs,
        &["writes one of `Box`'s own parameters inside its own slot"],
        "a binding writing the carrier's parameter in its own slot",
    );
    assert!(
        !errs.join(" | ").contains("print alike"),
        "no two types were compared, so none print alike: {errs:#?}"
    );
}

/// … AND ADVISES WRITING AN UNWRITTEN RETURN SLOT ONLY WHERE THAT IS THE DIFFERENCE. `-> Pair[A =
/// String, B = List]` against the spec's `Pair[A = Int64, B = List]` differs in `A`; writing
/// `List`'s slot repairs nothing, and the advice was given (MEASURED on the tree the ninth review
/// saw). Nothing runs: the member is refused.
/// FAILS under ledger part 117.
#[test]
fn a_wrong_return_refusal_gives_no_unwritten_slot_advice() {
    let src = r#"
namespace wi0rp29r9.says_advice
  import anthill.prelude.{Int64, String, List}
  sort Pair
    sort A = ?
    sort B = ?
    entity pair(a: A, b: B)
  end
  sort Sp
    sort T = ?
    operation op(s: Sp, t: T) -> Pair[A = Int64, B = List]
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation op(s: Car, t: V) -> Pair[A = String, B = List] = pair(a: "x", b: [])
  end
end
"#;
    let errs = load_errors(src);
    assert_refused_naming(
        &errs,
        &["the member returns `Pair[A = String, B = List[T = ?T]]`, which is not a subtype of the spec's `Pair[A = Int64, B = List[T = ?T]]`"],
        "a member returning another pair",
    );
    assert!(
        !errs.join(" | ").contains("leaves a slot unwritten"),
        "the returns differ in a written slot, so writing the unwritten one repairs nothing: {errs:#?}"
    );
}
