//! WI-20260929-0RP29 — A CALL'S ARGUMENTS ARE READ BY THE PARAMETER THEY BIND, and an effect
//! re-keyed onto them is re-keyed as the call's own effects are. Found by that ticket's third
//! /code-review, each reproduced on the pre-ticket tree, and fixed with it.
//!
//! In a MIXED call positional arguments rank among the parameters the labels left open
//! (WI-20260827-1F0QP, `positional_param_indices`), so the argument at index `i` need not be
//! the one bound to parameter `i`. The binding and the argument checks read it that way;
//! several readers did not, and each answered `pos_results.get(i)`: the receiver's carrier
//! (dispatch), a carrier-parameter receiver, a guard's σ and a precondition's σ, the WI-506
//! place maps. They share one owner now (`bound_arg`). And where an effect is re-keyed onto
//! the caller's arguments — a dispatched override's, the WI-606 fallback's, a callback
//! parameter's row — it takes the call's own rules: a field path's head, no placeless
//! argument, the guard σ of the spec's parameters.
//!
//! Every row that can RUNS and names what was reached; the rows asserting a LOAD verdict say
//! at their site why nothing runs.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! MEASURED with the main file's parts (its module doc numbers them), each present but wrong:
//!
//! 1. THE RECEIVER'S CARRIER BY INDEX (`receiver_carrier`). 1 FAILS:
//!    [`a_mixed_calls_receiver_is_the_argument_bound_to_it`] (also the main file's part 19).
//! 2. THE GUARD AND PRECONDITION σ BY INDEX (`build_call_guard_sigma`). 4 FAIL: both guard rows
//!    and both precondition rows.
//! 3. A CARRIER-PARAMETER RECEIVER BY INDEX (`supplied_arg_type`). 2 FAIL: both
//!    carrier-parameter rows.
//! 4. THE PLACE MAPS BY INDEX (apply.rs's WI-506 / WI-20260823-4GBQV maps). 2 FAIL: both
//!    placeless rows.
//! 5. THE FALLBACK'S GUARD σ WITHOUT THE OVERRIDE'S PARAMETERS (since the fourth review,
//!    through `ThreadedOverride::impl_to_spec`). 1 FAILS:
//!    [`a_guard_the_fallback_threads_is_discharged`].
//! 6. THE FALLBACK'S EFFECTS RE-KEYED TO THE CALLER'S ARGUMENTS instead of the spec's
//!    parameters. 1 FAILS: [`an_effect_the_fallback_threads_takes_the_calls_own_rekey`].
//! 7. THE CALLBACK ROW RE-KEY — dropped. 1 FAILS:
//!    [`a_callback_row_naming_another_parameter_is_rekeyed`].
//! 8. THE DISPATCHED HEAD RE-KEY — dropped. 2 FAIL:
//!    [`a_dispatched_overrides_effect_rekeys_a_field_path_to_its_head`] and
//!    [`an_effect_the_fallback_threads_takes_the_calls_own_rekey`].
//!
//!
//! The fourth review's fix pass:
//!
//! 9. A DISPATCHED PROJECTION'S RECEIVER RE-KEYED BY VARIABLES — by the field path's head. 1
//!    FAILS: [`a_projection_effect_through_a_field_path_is_not_the_holders_row`] (it LOADED).
//! 10. THE OVERRIDE'S OWN TYPE PARAMETERS BOUND BY THE ARGUMENTS — unbound. 1 FAILS:
//!    [`an_overrides_own_type_parameter_in_its_effects_is_bound`].
//! 11. A PLACELESS ARGUMENT TO A DISPATCHED `Modify` REFUSED — the override's name left in the
//!    row. 1 FAILS: [`a_placeless_argument_to_a_dispatched_modify_is_refused_as_the_calls_own`].
//! 12. THE CALLBACK ROW TAKES THE CALL'S EFFECT RE-KEY — variables only. 1 FAILS:
//!    [`a_callback_row_over_a_field_path_is_rekeyed_to_its_head`].
//! 13. THE RECEIVER'S NAME BY THE PARAMETER IT BINDS (`carrier_param_receiver`) — by index. 1
//!    FAILS: [`a_mixed_calls_receiver_row_is_the_bound_arguments`] (it LOADED).
//! 14. THE HINT STAGING BY THE RANKING (`param_arg_index`) — by slot. 1 FAILS:
//!    [`a_mixed_call_hints_its_lambda_from_the_bound_sibling`].
//! The fifth review's fix pass:
//!
//! 15. A CALLBACK TYPE THE ELIMINATION REWROTE TAKES THE HEADS — skipped. 1 FAILS:
//!    [`a_callback_row_beside_a_projection_over_a_field_path_is_rekeyed_to_its_head`].
//!
//! The sixth review's fix pass (measured over the three `wi_0rp29_*` files and `wi_xzmgc`):
//!
//! 16. A RECEIVED BARE CARRIER BINDING HELD AT THE CARRIER-PARAM CALL — held to nothing. 1 FAILS:
//!    [`a_received_bare_carrier_binding_is_the_receivers_instance_at_the_call`] (its control passes
//!    either way by design).
//! 17. A GROUND PROVISION BINDING BOUND ONCE PER CALL — as written, expanded per occurrence. 1
//!    FAILS: [`a_written_binding_is_one_type_per_carrier_param_call`].
//!
//! The seventh review's fix pass (measured over the same four files, 206 rows):
//!
//! 18. A BINDING NAMING THE DISPATCH CARRIER READ BY WHERE THE PROVISION IS WRITTEN — this
//!    instance whatever the provider (the sixth pass: decided against the call's dispatch
//!    carrier). 2 FAIL: [`a_witness_binding_naming_its_carrier_is_any_instance`] and
//!    [`a_foreign_carrier_binding_is_any_instance`].
//! 19. A WITNESS'S BARE BINDING KEPT, an instance of its own — dropped. 1 FAILS:
//!    [`a_witness_binding_naming_its_carrier_is_still_a_binding`] (it loads).
//! 20. WHAT AN ARGUMENT LEAVES OPEN IS WHAT THE CALL CHECKED IT AGAINST (`override_at_call`) —
//!    the argument read alone, and separately an empty literal's element left inert. 1 FAILS
//!    under each: [`an_overrides_type_parameter_takes_what_an_open_argument_was_checked_against`].
//! 21. WHAT IS STILL FREE FROM THE SPEC'S TYPES AS THE CALL REDUCES THEM — the override's
//!    variable walked through the masked relation of the declarations (the sixth pass's step
//!    5); the spec's return masked where it reduces. 2 FAIL under each:
//!    [`an_overrides_type_parameter_only_its_return_names_is_bound`] and its control.
//! [`an_overrides_type_parameter_takes_an_unannotated_lambdas_parameter`] passes under parts 20
//! and 21 each, and with the argument not walked through the call's substitution: each of the
//! three reads binds it. With all three backed out it fails beside the three rows above.
//!
//! The seventh review's finding 13 (the eighth pass), measured over the three `wi_0rp29_*`
//! files, `wi_xzmgc` and `wi347_override_refinement_test` (316 rows) — WHICH spec a projected
//! member is read from (`project_via_provided_spec`, projection.rs):
//!
//! 22. THE SPEC THE RECEIVER'S DECLARATION NAMES (`projection_owner_spec`) — not read. 4 FAIL:
//!    [`a_projected_member_is_read_from_the_spec_its_receiver_is_declared_by`], its control
//!    (unnamed, the two provisions meet part 24's agreement and are refused),
//!    [`a_witness_carriers_projected_member_is_the_witnesses_binding`] and
//!    [`a_generic_witnesses_binding_is_read_at_the_receivers_arguments`].
//! 23. A WITNESS'S PROVISION READ FOR ITS CARRIER (`witness_lends_member`) — not looked for. 2
//!    FAIL: the two witness rows.
//! 24. TWO PROVISIONS MUST AGREE — the first lends it. 1 FAILS:
//!    [`a_member_two_provisions_bind_differently_is_refused_where_no_spec_is_named`].
//! 25. A SPEC'S CARRIER PARAMETER NO MEMBER OF ITS PROVIDER — it lends itself. 2 FAIL:
//!    [`a_specs_carrier_parameter_is_no_member_of_its_provider`] and
//!    [`a_member_two_provisions_bind_differently_is_refused_where_no_spec_is_named_control`]
//!    (the derived `Eq[T = Car]` then a rival of the two written provisions).
//! 26. A PROJECTION OVER A WRAPPED ARGUMENT READS THE OPTION (`some_wrapped_arg_type`) — the raw
//!    argument. 2 FAIL: [`a_projection_over_a_wrapped_argument_reads_the_option`] and its
//!    control.
//! With parts 22, 24 and 25 backed out TOGETHER — the reading before this pass, the first
//! provided spec declaring the name — 6 FAIL: the four refusals and runs of parts 22–25 above
//! but the two rows named controls, which that reading passes (the order they are written in
//! happens to suit it), and [`a_member_the_named_specs_provision_leaves_unbound_is_no_member`],
//! which no single part fails (named, the provision lends nothing; unnamed, a derived spec's
//! carrier parameter is no member).
//!
//! The main file's parts 21 and 23 fail this file's fallback-effect rows as well, and the
//! member-rule file's part 50 (a binding's reference to the declaring sort read as an
//! independent instance) fails [`a_carrier_binding_is_the_receivers_instance_whether_or_not_received`]
//! and [`a_received_bare_carrier_binding_is_the_receivers_instance_at_the_call_control`]. Every
//! row fails under at least one part but four controls, each passing either way by design (see
//! their sites): [`a_callback_row_naming_another_parameter_is_rekeyed_control`],
//! [`a_dispatched_overrides_effect_rekeys_a_field_path_to_its_head_control`],
//! [`an_overrides_own_type_parameter_in_its_effects_is_bound_control`] and
//! [`an_overrides_type_parameter_takes_what_an_open_argument_was_checked_against_control`].
//!
//! The eighth review's findings (the ninth pass), measured over the three `wi_0rp29_*` files,
//! `wi_xzmgc`, `wi347_override_refinement_test` and `wi_f3fyj_value_in_type_binding_test` (434
//! rows):
//!
//! 27. A PROVISION LEFT OUT ONLY WHERE IT BINDS THE NAME TO THE PROVIDER ITSELF
//!    (`composed_self_reference`) — by its carrier parameter's name alone. 8 FAIL:
//!    [`a_member_two_specs_lend_differently_is_refused_at_its_own_signature`],
//!    [`a_spec_receiving_on_itself_lends_its_element`] and the member-rule file's
//!    `a_parameter_writing_its_sorts_own_parameter_is_replaced_once`,
//!    `a_parameter_writing_its_sorts_own_parameter_is_replaced_once_misfit`,
//!    `a_projection_reads_its_receiver_as_bound_so_far`,
//!    `a_projection_reads_its_receiver_as_bound_so_far_misfit`,
//!    `a_projection_reads_its_sorts_own_parameter_as_bound_so_far` and
//!    `a_projection_reads_its_sorts_own_parameter_as_bound_so_far_misfit` — the six of the
//!    member-rule file each read a member that a SECOND provision lends, by the name of that
//!    spec's first parameter.
//! 28. A BINDING NAMING THE CARRIER BELOW ITS TOP HOLDS THE CALL TO THIS INSTANCE
//!    (`this_instance_binding_at`) — to nothing. 1 FAILS:
//!    [`a_nested_carrier_binding_holds_a_self_receiver_call_to_this_instance`].
//! 29. THE CARRIER-PARAM BINDER READS A REFERENCE AT ANY DEPTH (`holds_carrier`, carrier.rs) —
//!    gated on a bare one. 2 FAIL:
//!    [`a_carrier_binding_at_its_own_parameters_holds_a_generic_receiver`] and
//!    [`an_alias_of_the_carrier_in_a_binding_is_the_carrier`].
//! 30. AN ALIAS OF THE CARRIER THE CARRIER (`sort_application_parts`) — not the carrier. 1 FAILS:
//!    [`an_alias_of_the_carrier_in_a_binding_is_the_carrier`].
//! 31. THE `some(…)` WRAP THE ARGUMENT CHECK'S VERDICT (`some_wrapped_arg_type`) — decided by the
//!    argument's head. 3 FAIL: [`an_option_alias_is_not_wrapped`],
//!    [`an_option_alias_is_not_wrapped_control`] and
//!    [`an_option_passed_for_an_option_of_options_is_wrapped`].
//! 32. EVERY COVERING WITNESS ASKED, AND THEY AGREE (`witnesses_lend_member`) — the first that
//!    binds the member lends it. 2 FAIL:
//!    [`a_covering_witness_leaving_the_member_unbound_is_not_skipped`] and
//!    [`two_covering_witnesses_binding_a_member_differently_are_refused`].
//! 33. ONE MAP OF RECEIVERS FOR EVERY PROJECTION READER OF A CALL (`projection_receivers`) — the
//!    `requires`, dictionary and hint readers read the raw argument map. 2 FAIL:
//!    [`a_lambda_hint_reads_the_wrapped_receiver`] and
//!    [`an_operation_level_requires_reads_the_wrapped_receiver`] (with the lambda hint's reader
//!    alone backed out, the first).
//! 34. TWO PROVISIONS AGREE ON THE TYPE HOWEVER SPELLED (`types_agree`) — compared by structural
//!    identity. 2 FAIL: [`two_provisions_binding_a_type_and_its_alias_agree`] and
//!    [`two_provisions_binding_one_row_in_two_spellings_agree`].
//! 35. A FIELD PATH DECLARED BY THE `requires` ENTRY LENDING THE MEMBER (`field_path_owner_spec`) —
//!    it names no owner. 1 FAILS:
//!    [`a_field_paths_member_is_lent_by_the_requires_that_declares_it`].
//! 36. A FIELD-PATH PROJECTION PARAMETER DETERMINED, AND SO CHECKED (`expr_is_value_path`,
//!    type_preds.rs) — never determined. 1 FAILS:
//!    [`a_parameter_typed_by_a_field_path_projection_is_checked`].
//! 37. THE RULE-BODY BRIDGE READS THE SAME RECEIVERS (`pin_params_from_args`, bridge.rs) — the raw
//!    argument map. 1 FAILS: [`a_rule_body_call_reads_the_wrapped_receiver`].
//!
//! EARLIER PARTS RE-MEASURED, this pass having rewritten `project_via_provided_spec` and the wrap:
//!   * part 22 (the spec the receiver's declaration names — not read): 9 FAIL —
//!     [`a_covering_witness_leaving_the_member_unbound_is_not_skipped`],
//!     [`a_field_paths_member_is_lent_by_the_requires_that_declares_it`],
//!     [`a_generic_witnesses_binding_is_read_at_the_receivers_arguments`],
//!     [`a_projected_member_is_read_from_the_spec_its_receiver_is_declared_by`],
//!     [`a_projected_member_is_read_from_the_spec_its_receiver_is_declared_by_control`],
//!     [`a_witness_carriers_projected_member_is_the_witnesses_binding`],
//!     [`two_covering_witnesses_binding_a_member_alike_lend_it`],
//!     [`two_covering_witnesses_binding_a_member_differently_are_refused`] and the member-rule
//!     file's `a_witness_binding_is_read_at_the_receiver_projected`.
//!   * part 23 (a witness's provision read for its carrier — not looked for): 6 FAIL —
//!     [`a_covering_witness_leaving_the_member_unbound_is_not_skipped`],
//!     [`a_generic_witnesses_binding_is_read_at_the_receivers_arguments`],
//!     [`a_witness_carriers_projected_member_is_the_witnesses_binding`],
//!     [`two_covering_witnesses_binding_a_member_alike_lend_it`],
//!     [`two_covering_witnesses_binding_a_member_differently_are_refused`] and the member-rule
//!     file's `a_witness_binding_is_read_at_the_receiver_projected`.
//!   * part 24 (two provisions must agree — the first lends it): 2 FAIL —
//!     [`a_member_two_provisions_bind_differently_is_refused_where_no_spec_is_named`] and
//!     [`a_member_two_specs_lend_differently_is_refused_at_its_own_signature`].
//!   * part 25 (a spec's carrier parameter no member of its provider — it lends itself): 4 FAIL —
//!     [`a_member_two_provisions_bind_differently_is_refused_where_no_spec_is_named_control`],
//!     [`a_specs_carrier_parameter_is_no_member_of_its_provider`] and the member-rule file's
//!     `a_specs_projection_over_a_carrier_typed_parameter_is_the_carriers_own` and
//!     `a_witness_members_projection_is_read_as_its_receiver_is_declared`.
//!   * part 26 (a projection over a wrapped argument reads the option — the raw argument): 6 FAIL —
//!     [`a_lambda_hint_reads_the_wrapped_receiver`],
//!     [`a_projection_over_a_wrapped_argument_reads_the_option`],
//!     [`a_projection_over_a_wrapped_argument_reads_the_option_control`],
//!     [`a_rule_body_call_reads_the_wrapped_receiver`],
//!     [`an_operation_level_requires_reads_the_wrapped_receiver`] and
//!     [`an_option_passed_for_an_option_of_options_is_wrapped`].
//!
//! Of this pass's 23 rows, every one fails under at least one part but five: three `_control`s
//! passing either way by design, as their sites say —
//! [`a_nested_carrier_binding_holds_a_self_receiver_call_to_this_instance_control`],
//! [`a_carrier_binding_at_its_own_parameters_holds_a_generic_receiver_control`] and
//! [`a_parameter_typed_by_a_field_path_projection_is_checked_control`] — and the two rows pinning
//! what the interim reading does NOT reach,
//! [`a_projection_of_the_bound_parameter_is_an_instance_of_its_own`] and its `_misfit`, which no
//! part of the three ledgers fails.

use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64 as run_src};

/// THE RECEIVER OF A MIXED CALL IS THE ARGUMENT BOUND TO IT: `Sp.op(o, 2, s: w)` receives on
/// `w`, a `Car`, so `Car.op` runs and answers its element 41. Dispatch read the positional
/// argument at the receiver's INDEX — `o`, an `Other` — and ran `Other.op` (1), while the
/// WI-606 fallback threaded `Car.op`'s return: a `String`-typed call answered an `Int64`
/// (MEASURED on the String twin; this `Int64` one names which override ran).
#[test]
fn a_mixed_calls_receiver_is_the_argument_bound_to_it() {
    let src = r#"
namespace wi0rp29cb.receiver
  import anthill.prelude.{Int64, Bool, Option, Pair, String, List}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}

  sort Sp
    sort T = ?
    effects E = ?
    operation op(s: Sp, a: Other, b: Int64) -> Option[T = Pair[A = s.T, B = Sp[T = s.T, E = s.E]]] effects s.E
  end

  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = V, E = {EC}]
    operation op(s: Car, a: Other, b: Int64) -> Option[T = Pair[A = V, B = Car[V = V, EC = EC]]] effects {EC} = some(pair(s.v, s))
  end

  sort Other
    entity other(n: Int64)
    provides Sp[T = Int64, E = {}]
    operation op(s: Other, a: Other, b: Int64) -> Option[T = Pair[A = Int64, B = Other]] = some(pair(a.n, a))
  end

  operation use[R](w: Car[V = Int64, EC = R], o: Other) -> Int64 effects {R} =
    match Sp.op(o, 2, s: w)
      case some(pair(v, _)) -> v
      case none() -> 0

  operation go() -> Int64 =
    let w: Car[V = Int64, EC = {}] = car(v: 41)
    use(w, other(n: 1))
end
"#;
    assert_eq!(run_src(src, "wi0rp29cb.receiver.go"), Ok(41));
}

/// `chk(w, x, y)` raises `Error[DivisionByZero]` when `x = 0`; `call` is how `use`, which
/// declares nothing, calls it. A LOAD VERDICT: the guard is refuted, or not, at load.
fn guard_program(ns: &str, call: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Error, DivisionByZero}}
  import anthill.prelude.PartialEq.{{eq}}
  import anthill.prelude.Int64.{{div}}

  operation chk(w: Int64, x: Int64, y: Int64) -> Int64 effects {{ Error[DivisionByZero] :- eq(x, 0) }} = div(w, x) + y

  operation use() -> Int64 = {call}
end
"#
    )
}

/// A GUARD READS THE OPERAND A MIXED CALL BINDS: `chk(0, 5, w: 7)` binds `x = 0`, so the effect
/// is incurred and the pure caller is refused. The guard's σ read `x ↦ 5` — the positional at
/// `x`'s index — refuted the guard, and the program loaded and divided by zero at run time.
#[test]
fn a_guard_reads_the_operand_a_mixed_call_binds() {
    assert_refused_naming(
        &load_errors(&guard_program("wi0rp29cb.guard", "chk(0, 5, w: 7)")),
        &["undeclared effect", "DivisionByZero"],
        "x = 0, the guard holds",
    );
}

/// … AND ITS CONTROL: `chk(5, 0, w: 7)` binds `x = 5`, the guard is refuted, and the pure caller
/// loads. The index read bound `x ↦ 0` and refused it.
#[test]
fn a_guard_reads_the_operand_a_mixed_call_binds_control() {
    let errs = load_errors(&guard_program("wi0rp29cb.guard_ok", "chk(5, 0, w: 7)"));
    assert!(errs.is_empty(), "x = 5 refutes the guard: {errs:#?}");
}

/// `needy(w, x, y) requires neq(x, 0)`, called as `call`. A LOAD VERDICT: a precondition is
/// proved, or not, at the call site at load.
fn precondition_program(ns: &str, call: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool}}
  import anthill.prelude.PartialEq.{{neq}}

  operation needy(w: Int64, x: Int64, y: Int64) -> Int64
    requires neq(x, 0)
  =
    w + y

  operation caller() -> Int64 = {call}
end
"#
    )
}

/// A PRECONDITION READS THE OPERAND A MIXED CALL BINDS: `needy(0, 5, w: 7)` binds `x = 0`, and
/// `neq(0, 0)` is refused. It was proved as `neq(5, 0)`, off the positional at `x`'s index.
#[test]
fn a_precondition_reads_the_operand_a_mixed_call_binds() {
    assert_refused_naming(
        &load_errors(&precondition_program("wi0rp29cb.req", "needy(0, 5, w: 7)")),
        &["neq(0, 0)"],
        "x = 0 fails the precondition",
    );
}

/// … AND ITS CONTROL: `needy(5, 0, w: 7)` binds `x = 5`, and loads.
#[test]
fn a_precondition_reads_the_operand_a_mixed_call_binds_control() {
    let errs = load_errors(&precondition_program(
        "wi0rp29cb.req_ok",
        "needy(5, 0, w: 7)",
    ));
    assert!(errs.is_empty(), "x = 5 satisfies it: {errs:#?}");
}

/// `Ctr.pick(c: C, o: Oth) -> E` — a CARRIER-PARAMETER receiver — with `Bag` providing `E =
/// Int64` and `Oth` `E = String`; `use` makes the mixed call `Ctr.pick(x, c: b)`, declaring
/// `ret`.
fn carrier_param_program(ns: &str, ret: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}

  sort Ctr
    sort C = ?
    sort E = ?
    operation pick(c: C, o: Oth) -> E
  end

  sort Bag
    entity bag(v: Int64)
    provides Ctr[C = Bag, E = Int64]
    operation pick(c: Bag, o: Oth) -> Int64 = c.v + 1
  end

  sort Oth
    entity oth(s: String)
    provides Ctr[C = Oth, E = String]
    operation pick(c: Oth, o: Oth) -> String = o.s
  end

  operation use(b: Bag, x: Oth) -> {ret} = Ctr.pick(x, c: b)
  operation go() -> Int64 = use(bag(v: 41), oth(s: "str"))
end
"#
    )
}

/// A CARRIER-PARAMETER RECEIVER IS THE ARGUMENT BOUND TO IT: `c: b`, a `Bag`, so the call is
/// `Int64` and `Bag.pick` answers 42. The receiver was read at `c`'s INDEX — `x`, an `Oth` —
/// so the typer took `Oth`'s `E = String` and refused this program, while its `String` twin
/// loaded and failed at run time.
#[test]
fn a_carrier_param_receiver_is_the_argument_bound_to_it() {
    let ns = "wi0rp29cb.carrier_param";
    assert_eq!(
        run_src(&carrier_param_program(ns, "Int64"), &format!("{ns}.go")),
        Ok(42)
    );
}

/// … AND ITS CONTROL: the `String` twin is refused at load.
#[test]
fn a_carrier_param_receiver_is_the_argument_bound_to_it_control() {
    assert_refused_naming(
        &load_errors(&carrier_param_program(
            "wi0rp29cb.carrier_param_s",
            "String",
        )),
        &["expected String, got Int64"],
        "the call is Bag's Int64",
    );
}

/// `touch(a: Cell, b: Cell) effects Modify[a]`, called as `call` from `use`, which declares
/// `Modify[{place}]`. A LOAD VERDICT: which argument a `Modify` names is decided at load.
fn place_program(ns: &str, holder: &str, call: &str, place: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Modify, EffectsRuntime}}

  sort Cell
    entity cell(v: Int64)
  end

  sort Holder
    entity holder(f: Cell)
  end

  operation touch(a: Cell, b: Cell) -> Int64 effects Modify[a] = 1
  operation mk() -> Cell = cell(v: 0)

  operation use({holder}) -> Int64 effects Modify[{place}] = {call}
end
"#
    )
}

/// THE PLACE MAPS KEY THE PARAMETER A MIXED CALL BINDS: `touch(mk(), a: x)` binds the fresh
/// `mk()` to `b`, and `Modify[a]` is `x`'s. The placeless argument was keyed to `a` — its index —
/// and the program was refused for passing a fresh value where a place is needed.
#[test]
fn a_placeless_argument_keys_the_parameter_it_binds() {
    let errs = load_errors(&place_program(
        "wi0rp29cb.place",
        "x: Cell",
        "touch(mk(), a: x)",
        "x",
    ));
    assert!(errs.is_empty(), "mk() fills b; a is x: {errs:#?}");
}

/// … AND ITS MIRROR: `touch(y.f, a: mk())` passes the fresh `mk()` as `a`, which is refused.
/// The field path `y.f` was keyed to `a` instead, and the program loaded with the `Modify`
/// re-keyed onto `y`.
#[test]
fn a_placeless_argument_keys_the_parameter_it_binds_mirror() {
    assert_refused_naming(
        &load_errors(&place_program(
            "wi0rp29cb.place_mirror",
            "y: Holder",
            "touch(y.f, a: mk())",
            "y",
        )),
        &["naming a PLACE"],
        "a is the fresh mk()",
    );
}

/// `Sp.op` and its override `Car.op` both raise `Error[DivisionByZero] :- eq(d, 0)`; the call
/// passes `d`, over a carrier whose row is the caller's `R`, so the spec's `s.E` does not
/// ground and the WI-606 fallback threads the override's effects. A LOAD VERDICT: which effects
/// the call incurs is decided at load — a refuted guard's atom is absent from the caller's row —
/// and nothing at run time observes the row.
fn fallback_guard_program(ns: &str, d: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, String, Error, DivisionByZero}}
  import anthill.prelude.PartialEq.{{eq}}

  sort Sp
    sort T = ?
    effects E = ?
    operation op(s: Sp, d: Int64) -> Int64 effects {{s.E, Error[DivisionByZero] :- eq(d, 0)}}
  end

  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = V, E = {{EC}}]
    operation op(c: Car, d: Int64) -> Int64 effects {{EC, Error[DivisionByZero] :- eq(d, 0)}} = 1
  end

  operation viaSpec[R](x: Car[V = Int64, EC = R]) -> Int64 effects {{R}} = Sp.op(x, {d})
end
"#
    )
}

/// A GUARD THE FALLBACK THREADS IS DISCHARGED: `Sp.op(x, 2)` refutes `eq(d, 0)`. The override's
/// effects came back in ITS parameters' names while the call's guard σ is keyed by the spec's,
/// so the guard was never refuted and the call was refused an effect it does not incur (and the
/// effects-only arming WI-20260929-0RP29 added sent more calls down that path).
#[test]
fn a_guard_the_fallback_threads_is_discharged() {
    let errs = load_errors(&fallback_guard_program("wi0rp29cb.fb_guard", "2"));
    assert!(errs.is_empty(), "d = 2 refutes the guard: {errs:#?}");
}

/// … AND ITS CONTROL: `Sp.op(x, 0)` incurs it, and the caller's `{R}` does not declare it.
#[test]
fn a_guard_the_fallback_threads_is_discharged_control() {
    assert_refused_naming(
        &load_errors(&fallback_guard_program("wi0rp29cb.fb_guard_zero", "0")),
        &["undeclared effect", "DivisionByZero"],
        "d = 0, the guard holds",
    );
}

/// `apply(p, f)` whose callback row names the OTHER parameter, `@ Modify[p]`; `use` passes `q`
/// for it and a lambda that sets `target`.
fn callback_program(ns: &str, target: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Unit, Cell, Modify, Bool}}

  operation apply(p: Cell[V = Int64], f: (u: Int64) -> Unit @ Modify[p]) -> Unit effects Modify[p] = f(5)

  operation use(q: Cell[V = Int64], r: Cell[V = Int64]) -> Unit effects {{Modify[q], Modify[r]}} =
    apply(q, lambda (u: Int64) -> Cell.set({target}, u))

  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let d: Cell[V = Int64] = Cell.new(2)
    let _ = use(c, d)
    Cell.get(c)
end
"#
    )
}

/// A CALLBACK ROW NAMING ANOTHER PARAMETER IS READ IN THE CALLER'S NAMES: `@ Modify[p]` is
/// `Modify[q]` at `apply(q, …)`, so the lambda setting `q` is admitted and runs (5). It was
/// re-keyed only when the callback's own parameter type happened to hold a projection, and was
/// refused "the lambda argument declares `Modify[q]`".
#[test]
fn a_callback_row_naming_another_parameter_is_rekeyed() {
    let ns = "wi0rp29cb.callback";
    assert_eq!(
        run_src(&callback_program(ns, "q"), &format!("{ns}.go")),
        Ok(5)
    );
}

/// … AND ITS CONTROL: a lambda setting `r` is still refused, naming it. Passes either way by
/// design — un-re-keyed, the row admits `r` no more than it admits `q` — and guards the re-key
/// against admitting more than the argument it names.
#[test]
fn a_callback_row_naming_another_parameter_is_rekeyed_control() {
    assert_refused_naming(
        &load_errors(&callback_program("wi0rp29cb.callback_r", "r")),
        &["Modify[T = r]"],
        "the row admits q, not r",
    );
}

/// `ModifyRuntime.set(h.cell, 1)` — a spec op dispatched to `Cell.set`, whose effect is
/// `Modify[c]` on its own parameter — from `viaSpec`, declaring `declared`.
fn dispatched_head_program(ns: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Unit, Cell, Modify, ModifyRuntime}}

  sort Holder
    entity holder(cell: Cell[V = Int64])
  end

  operation viaSpec(h: Holder) -> Unit{declared} = ModifyRuntime.set(h.cell, 1)
end
"#
    )
}

/// A DISPATCHED OVERRIDE'S EFFECT RE-KEYS A FIELD PATH TO ITS HEAD, as the call's own effects do
/// (WI-506: `Modify[h.cell]` is covered by `Modify[h]`): declaring `Modify[h]` loads. The
/// override's effect was re-keyed to variable arguments only, and `Cell.set`'s own `c` leaked:
/// "undeclared effect: Modify[T = c]", while `Cell.set(h.cell, 1)` loaded. A LOAD VERDICT: what
/// is measured is the row the caller must declare, and `ModifyRuntime.set` needs the `Modify`
/// handler this file's harness does not install.
#[test]
fn a_dispatched_overrides_effect_rekeys_a_field_path_to_its_head() {
    let errs = load_errors(&dispatched_head_program(
        "wi0rp29cb.head",
        " effects {Modify[h]}",
    ));
    assert!(errs.is_empty(), "Modify[h] covers the call: {errs:#?}");
}

/// … AND ITS CONTROL: declaring nothing is refused, naming `h`. Passes either way by design —
/// the spec operation's own effect re-keys to `h` whichever way the override's is — and guards
/// the head re-key against admitting the call without `Modify[h]`.
#[test]
fn a_dispatched_overrides_effect_rekeys_a_field_path_to_its_head_control() {
    assert_refused_naming(
        &load_errors(&dispatched_head_program("wi0rp29cb.head_none", "")),
        &["undeclared effect", "Modify[T = h]"],
        "the incurred Modify names h",
    );
}

/// `Sp.op(s: Sp, t: Cell) effects {s.E, Modify[t]}` and its override `Car.op(c: Car, t: Cell)
/// effects {EC, Modify[t]}`, called with a FIELD PATH for `t` over a carrier whose row is the
/// caller's `R` — so `s.E` does not ground and the WI-606 fallback threads the override's
/// effects. `use` declares `declared`. A LOAD VERDICT: which place the incurred `Modify` names is
/// decided at load, and nothing at run time observes it.
fn fallback_head_program(ns: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Unit, Cell, Modify, Bool, Option}}
  import anthill.prelude.Option.{{some, none}}

  sort Sp
    sort T = ?
    effects E = ?
    operation op(s: Sp, t: Cell[V = Int64]) -> Option[T = s.T] effects {{s.E, Modify[t]}}
  end

  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = V, E = {{EC}}]
    operation op(c: Car, t: Cell[V = Int64]) -> Option[T = V] effects {{EC, Modify[t]}} = some(c.v)
  end

  sort Holder
    entity holder(cell: Cell[V = Int64])
  end

  operation use[R](x: Car[V = Int64, EC = R], h: Holder) -> Int64 effects {declared} =
    match Sp.op(x, h.cell)
      case some(v) -> v
      case none() -> 0
end
"#
    )
}

/// AN EFFECT THE FALLBACK THREADS TAKES THE CALL'S OWN RE-KEY: the override's `Modify[t]` comes
/// back in the SPEC's parameter names, and the call site re-keys it as it re-keys the spec's
/// own — `h.cell`'s HEAD, `h` (WI-506) — so declaring `Modify[h]` loads. Re-keyed straight to
/// the caller's variable arguments, a field path had none, and the override's own `t` leaked:
/// "undeclared effect: Modify[T = t]".
#[test]
fn an_effect_the_fallback_threads_takes_the_calls_own_rekey() {
    let errs = load_errors(&fallback_head_program(
        "wi0rp29cb.fb_head",
        "{R, Modify[h]}",
    ));
    assert!(errs.is_empty(), "Modify[h] covers the call: {errs:#?}");
}

/// … AND ITS CONTROL: declaring the row alone is refused, naming `h`.
#[test]
fn an_effect_the_fallback_threads_takes_the_calls_own_rekey_control() {
    assert_refused_naming(
        &load_errors(&fallback_head_program("wi0rp29cb.fb_head_none", "{R}")),
        &["undeclared effect", "Modify[T = h]"],
        "the incurred Modify names h",
    );
}

// ── a dispatched override's effects, re-keyed as the call's own ──────────────

/// A PROJECTION EFFECT THROUGH A FIELD PATH IS NOT THE HOLDER'S ROW: `Car.op(s: Car, k: Strm)
/// effects {EC, k.E}` called with `h.s` incurs the STREAM's row, which the caller cannot name
/// — refused, as the pre-ticket tree refused it. The field path's HEAD (`h`, WI-506, a rule for
/// `Modify` places) was applied to the projection's receiver, so `k.E` became `h.E` — `Hold`'s
/// own row — and a caller declaring `h.E` LOADED with the stream's error undeclared. A LOAD
/// VERDICT: the incurred row is decided at load. What the refusal NAMES is not asserted: today
/// the override's own `k.E`, a name no caller can write — a diagnostic gap of its own, which a
/// repair must be free to close without this row turning red.
#[test]
fn a_projection_effect_through_a_field_path_is_not_the_holders_row() {
    let src = r#"
namespace wi0rp29cb.dp
  import anthill.prelude.{Int64, Bool, Option, Pair, String, List}
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(v: T)
    operation obs(s: Strm) -> Bool effects s.E = true
  end
  sort Hold
    effects E = ?
    entity hold(s: Strm[T = Int64])
  end
  sort Sp
    sort T = ?
    effects E = ?
    operation op(s: Sp, k: Strm) -> Int64 effects {E, k.E}
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = V, E = {EC}]
    operation op(s: Car, k: Strm) -> Int64 effects {EC, k.E} =
      if Strm.obs(k) then 1 else 0
  end
  operation use_spec[R](c: Car[V = Int64, EC = R], h: Hold) -> Int64 effects {R, h.E} =
    Sp.op(c, h.s)
end
"#;
    let errs = load_errors(src);
    let undeclared: Vec<&str> = errs
        .iter()
        .filter_map(|e| e.split("got undeclared effect: ").nth(1))
        .collect();
    assert!(
        !undeclared.is_empty(),
        "the stream's row is incurred and undeclared: {errs:#?}"
    );
    assert!(
        undeclared.iter().all(|u| !u.starts_with("h.E")),
        "the incurred row is not the holder's: {errs:#?}"
    );
}

/// `Car.op[W](c: Car, w: W) effects {EC, Error[W]}` behind `Sp.op[U](s: Sp, w: U) effects {s.E,
/// Error[U]}`, called with a `String`; `via` declares `declared`.
fn own_type_param_program(ns: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, String, Error}}
  sort Sp
    sort T = ?
    effects E = ?
    operation op[U](s: Sp, w: U) -> Int64 effects {{s.E, Error[U]}}
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = V, E = {{EC}}]
    operation op[W](c: Car, w: W) -> Int64 effects {{EC, Error[W]}} = 1
  end
  operation via[R](x: Car[V = Int64, EC = R]) -> Int64 effects {{R, {declared}}} = Sp.op(x, "str")
end
"#
    )
}

/// AN OVERRIDE'S OWN TYPE PARAMETER IN ITS EFFECTS IS BOUND BY THE ARGUMENTS: `Error[W]` is
/// `Error[String]` at this call, which `via` declares. The dispatched effects were read through
/// the SPEC call's σ, which never binds the override's `W`: refused "undeclared effect:
/// Error[T = ?W]" where `Car.op(x, "str")` loaded (and so before the ticket too). A LOAD
/// VERDICT: the incurred row is decided at load.
#[test]
fn an_overrides_own_type_parameter_in_its_effects_is_bound() {
    let errs = load_errors(&own_type_param_program("wi0rp29cb.oe", "Error[String]"));
    assert!(errs.is_empty(), "Error[W] is Error[String]: {errs:#?}");
}

/// … AND ITS CONTROL: declaring `Error[Int64]` instead is refused, naming `Error[T = String]`.
/// Passes either way by design: the spec operation's own `Error[U]` names the argument's
/// `String` whichever way the override's `W` is read.
#[test]
fn an_overrides_own_type_parameter_in_its_effects_is_bound_control() {
    assert_refused_naming(
        &load_errors(&own_type_param_program("wi0rp29cb.oe_c", "Error[Int64]")),
        &["undeclared effect", "Error[T = String]"],
        "the override's W is the argument's String",
    );
}

/// A PLACELESS ARGUMENT TO A DISPATCHED `Modify` IS REFUSED AS THE CALL'S OWN IS: `Box.peek(mk())`
/// dispatches to `MutBox.peek(b) effects Modify[b]` over a fresh value, which names no place —
/// "expected an argument naming a PLACE … Bind it first", as `MutBox.peek(mk())` says. The
/// dispatched copy of the re-key left the override's own `b` in the caller's row ("undeclared
/// effect: Modify[T = b]", a name no caller can write).
#[test]
fn a_placeless_argument_to_a_dispatched_modify_is_refused_as_the_calls_own() {
    let src = r#"
namespace wi0rp29cb.rk
  import anthill.prelude.{Int64, Modify, EffectsRuntime}
  sort Box
    effects Effect = ?
    operation peek(b: Box) -> Int64 effects Effect
  end
  sort MutBox
    entity mb(fd: Int64)
    provides Box
    operation peek(b: MutBox) -> Int64 effects Modify[b] =
      match b
        case mb(x) -> x
  end
  operation mk() -> MutBox = mb(fd: 1)
  operation read_it() -> Int64 = Box.peek(mk())
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "expected an argument naming a PLACE",
            "MutBox.peek` declares `Modify[b]`",
        ],
        "the call's own refusal",
    );
}

/// A CALLBACK ROW OVER A FIELD PATH IS RE-KEYED TO ITS HEAD: `apply(p: Cell, f: (u: Int64) ->
/// Unit @ Modify[p])` called with `h.cell` admits the lambda's `Modify[h]`, as the call's own
/// `Modify[p]` becomes `Modify[h]` (WI-506). Re-keyed through variables alone, the row kept
/// `apply`'s `p`, and no callback over a field path could be passed. Runs — the lambda sets the
/// cell to 5 — with the `Modify` handler installed.
#[test]
fn a_callback_row_over_a_field_path_is_rekeyed_to_its_head() {
    let ns = "wi0rp29cb.cbhead";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Unit, Cell, Modify, Bool, List, String}}
  sort Holder
    entity holder(cell: Cell[V = Int64])
  end
  operation apply(p: Cell[V = Int64], f: (u: Int64) -> Unit @ Modify[p]) -> Unit effects Modify[p] = f(5)
  operation use(h: Holder) -> Unit effects {{Modify[h]}} =
    apply(h.cell, lambda (u: Int64) -> Cell.set(h.cell, u))
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let h: Holder = holder(cell: c)
    let _ = use(h)
    Cell.get(c)
end
"#
    );
    assert_eq!(run_with_modify(&src, &format!("{ns}.go")), 5);
}

/// `go` run with the `Modify` handler installed, to the `Int64` it answers.
fn run_with_modify(src: &str, entry: &str) -> i64 {
    let mut interp = crate::common::interp_for(src);
    crate::common::register_modify_handler(&mut interp);
    match interp.call(entry, &[]) {
        Ok(anthill_core::eval::Value::Int(v)) => v,
        other => panic!("`{entry}` did not run to an Int64: {other:?}"),
    }
}

/// … AND BESIDE A PROJECTION IN THE CALLBACK'S TYPE: `apply(b: Box, p: Cell, f: (u: b.T) -> Unit @
/// Modify[p])` over `h.cell`. The projection's elimination re-keyed `f`'s type by variables only,
/// and the head re-key then skipped a parameter the elimination had rewritten: refused "the
/// closed row does not admit `Modify[h]`" where the `u: Int64` twin above runs. Runs — the lambda
/// sets the cell to the box's 5.
#[test]
fn a_callback_row_beside_a_projection_over_a_field_path_is_rekeyed_to_its_head() {
    let ns = "wi0rp29cb.cbproj";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Unit, Cell, Modify, Bool, List, String}}
  sort Holder
    entity holder(cell: Cell[V = Int64])
  end
  sort Box
    sort T = ?
    entity box(item: T)
  end
  operation apply(b: Box, p: Cell[V = Int64], f: (u: b.T) -> Unit @ Modify[p]) -> Unit effects Modify[p] = f(b.item)
  operation use(h: Holder, bx: Box[T = Int64]) -> Unit effects {{Modify[h]}} =
    apply(bx, h.cell, lambda (u: Int64) -> Cell.set(h.cell, u))
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let h: Holder = holder(cell: c)
    let bx: Box[T = Int64] = box(item: 5)
    let _ = use(h, bx)
    Cell.get(c)
end
"#
    );
    assert_eq!(run_with_modify(&src, &format!("{ns}.go")), 5);
}

// ── a mixed call's arguments, by the parameter they bind ─────────────────────

/// A MIXED CALL'S RECEIVER ROW IS THE BOUND ARGUMENT'S: `Ctr.pick(o, c: b)` receives on `b`, so
/// the unwritten row it threads (WI-612) is `b.EB` — refused, since `g` declares `o.EB`, as the
/// positional `Ctr.pick(b, o)` is. The receiver's TYPE was read by parameter but its NAME by
/// index — `o` — so the call was charged `o.EB` and LOADED, the receiver's error undeclared
/// (MEASURED to escape at run time with a stored callback). A LOAD VERDICT.
#[test]
fn a_mixed_calls_receiver_row_is_the_bound_arguments() {
    for call in ["Ctr.pick(o, c: b)", "Ctr.pick(b, o)"] {
        let src = format!(
            r#"
namespace wi0rp29cb.cr
  import anthill.prelude.{{Int64, Bool}}
  sort Ctr
    sort C = ?
    effects E = ?
    operation pick(c: C, o: Oth) -> Int64 effects E
  end
  sort Bag
    effects EB = ?
    entity bag(v: Int64)
    provides Ctr[C = Bag, E = EB]
    operation pick(c: Bag, o: Oth) -> Int64 effects EB = c.v
  end
  sort Oth
    effects EB = ?
    entity oth(n: Int64)
  end
  sort Holder
    entity holder(b: Bag)
  end
  operation g(h: Holder, o: Oth) -> Int64 effects o.EB =
    match h
      case holder(b) -> {call}
end
"#
        );
        assert_refused_naming(&load_errors(&src), &["got undeclared effect: b.EB"], call);
    }
}

/// A MIXED CALL HINTS ITS LAMBDA FROM THE BOUND SIBLING: `g(ints, lambda x -> x + 1, a: strs)`
/// binds `ints` to `xs`, so the lambda's `x: xs.T` is an `Int64`. The WI-793 staging keyed the
/// sibling by SLOT — `a`'s `strs` — and refused "expected xs.T, got Int64" where the positional
/// and all-named spellings ran (and so before the ticket). Runs to 41 + 1.
#[test]
fn a_mixed_call_hints_its_lambda_from_the_bound_sibling() {
    let ns = "wi0rp29cb.hint";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, String, List, Pair}}
  import anthill.prelude.List.{{cons, nil}}
  import anthill.prelude.Pair.{{pair}}
  import anthill.prelude.Option.{{some, none}}
  operation g(a: List[T = String], xs: List[T = Int64], f: (x: xs.T) -> Int64) -> Int64 =
    match List.splitFirst(xs)
      case some(pair(h, _)) -> f(h)
      case none() -> 0
  operation go() -> Int64 =
    let strs: List[T = String] = cons("s", nil)
    let ints: List[T = Int64] = cons(41, nil)
    g(ints, lambda x -> x + 1, a: strs)
end
"#
    );
    assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(42));
}

// ── the sixth review's fixes: the carrier-param call holds what the declaration reads ──

/// `Rel { left(a: A); right(b: B); mix(a: A, b: B) }` at `Car provides Rel[A = Car, B = Car]`,
/// the member `mix(a: Car, b: Car)`, and `use` calling `Rel.mix(k1, second)`.
fn rel_program(ns: &str, second_ty: &str, second: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Rel
    sort A = ?
    sort B = ?
    operation left(a: A) -> Int64
    operation right(b: B) -> Int64
    operation mix(a: A, b: B) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V, f: (x: V) -> Int64)
    provides Rel[A = Car, B = Car]
    operation left(a: Car) -> Int64 = 1
    operation right(b: Car) -> Int64 = 2
    operation mix(a: Car, b: Car) -> Int64 = match a case car(_, g) -> g(b.v)
  end
  operation go() -> Int64 =
    let k1: Car[V = Int64] = car(v: 40, f: lambda (x: Int64) -> x + 1)
    let k2: {second_ty} = {second}
    Rel.mix(k1, k2)
  sort App
    entity app
    requires anthill.cli.Main
    operation main(args: List[String]) -> Int64 = go()
  end
end
"#
    )
}

/// A PARAMETER BOUND TO THE BARE CARRIER IS THE RECEIVER'S INSTANCE AT THE CALL, as the
/// declaration reads it (user decision, 2026-10-01 — since the seventh pass whether or not an
/// operation receives on it, see below): `Rel.mix(k1, k2)` over a `Car[V = Int64]`
/// and a `Car[V = String]` is refused. The declaration admitted the tied member and the call held
/// `b` to nothing — it loaded and ran a `Int64` callback on a `String` (MEASURED).
#[test]
fn a_received_bare_carrier_binding_is_the_receivers_instance_at_the_call() {
    assert_refused_naming(
        &load_errors(&rel_program(
            "wi0rp29cb6.rel",
            "Car[V = String]",
            "car(v: \"s\", f: lambda (x: String) -> 9)",
        )),
        &["mix.b (op-arg): expected Car[V = Int64], got Car[V = String]"],
        "b at the receiver's instance",
    );
}

/// … AND ITS CONTROL: two instances at one `V` run (9 + 1). It guards the held binding against
/// refusing the receiver's own instance, passing under this file's parts; it FAILS under the
/// member-rule file's part 50, where the tied member is refused at its declaration.
#[test]
fn a_received_bare_carrier_binding_is_the_receivers_instance_at_the_call_control() {
    let ns = "wi0rp29cb6.rel_ok";
    assert_eq!(
        run_src(
            &rel_program(ns, "Car[V = Int64]", "car(v: 9, f: lambda (x: Int64) -> x)"),
            &format!("{ns}.go")
        ),
        Ok(10)
    );
}

/// A WRITTEN BINDING IS ONE TYPE PER CALL: `both(a: A, x: T, y: T)` at `T = Pair[A = Box, B =
/// Int64]` passes one pair type twice, so `Rel.both(c, x, y)` over two boxes of different element
/// types is refused, as the self-receiver path refuses it. Bound as written and expanded per
/// occurrence, it loaded, and a member tying them crashed (MEASURED).
#[test]
fn a_written_binding_is_one_type_per_carrier_param_call() {
    let src = r#"
namespace wi0rp29cb6.once
  import anthill.prelude.{Int64, String, Bool, List, Pair}
  import anthill.prelude.Pair.{pair}
  sort Box
    sort B = ?
    entity box(inner: B, f: (x: B) -> Int64)
  end
  sort Rel
    sort A = ?
    sort T = ?
    operation left(a: A) -> Int64
    operation both(a: A, x: T, y: T) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Rel[A = Car, T = Pair[A = Box, B = Int64]]
    operation left(a: Car) -> Int64 = 1
    operation both[W](a: Car, x: Pair[A = Box[B = W], B = Int64], y: Pair[A = Box[B = W], B = Int64]) -> Int64 = 5
  end
  operation go() -> Int64 =
    let c: Car[V = Int64] = car(v: 1)
    let b1: Box[B = Int64] = box(inner: 3, f: lambda (x: Int64) -> x + 1)
    let b2: Box[B = String] = box(inner: "s", f: lambda (x: String) -> 9)
    let x: Pair[A = Box[B = Int64], B = Int64] = pair(fst: b1, snd: 1)
    let y: Pair[A = Box[B = String], B = Int64] = pair(fst: b2, snd: 2)
    Rel.both(c, x, y)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["both.y (op-arg): expected Pair[A = Box[B = Int64], B = Int64]"],
        "one pair type per call",
    );
}

// ── the seventh review's fixes: a provision's binding reads a sort's name as an operation does ──

/// `Rel { left(a: A); mix(a: A, b: B) }` — NO operation receives on `B` — at `Car provides
/// Rel[A = Car, B = {binding}]`, the member `mix(a: Car, b: Car)` applying `a`'s function to
/// `b`'s value, and `go` calling `Rel.mix(k1, k2)` over a `Car[V = Int64]` and `k2`.
fn unreceived_rel_program(ns: &str, binding: &str, second_ty: &str, second: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Rel
    sort A = ?
    sort B = ?
    operation left(a: A) -> Int64
    operation mix(a: A, b: B) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V, f: (x: V) -> Int64)
    provides Rel[A = Car, B = {binding}]
    operation left(a: Car) -> Int64 = 1
    operation mix(a: Car, b: Car) -> Int64 = match a case car(_, g) -> g(b.v)
  end
  operation go() -> Int64 =
    let k1: Car[V = Int64] = car(v: 40, f: lambda (x: Int64) -> x + 1)
    let k2: {second_ty} = {second}
    Rel.mix(k1, k2)
  sort App
    entity app
    requires anthill.cli.Main
    operation main(args: List[String]) -> Int64 = go()
  end
end
"#
    )
}

/// A BINDING NAMING THE CARRIER IS THE RECEIVER'S INSTANCE WHETHER OR NOT AN OPERATION RECEIVES
/// ON IT, bare or at the carrier's own parameters: the provision is written inside the carrier,
/// where the name reads as it does in the carrier's own operations (§3's tie; INTERIM, user
/// 2026-10-01 — WI-20261001-80ZV8 changes both readings together). So `mix(a: Car, b: Car)`
/// is the spec's and runs at one instance (9 + 1), and a second instance is refused at the call.
/// Read as an independent instance where nothing received on `B` (the sixth pass), the member
/// was refused at its declaration — printing two identical signatures for the `Car[V = V]`
/// spelling (MEASURED) — while the call tied `b` anyway. FAILS under the member-rule file's
/// ledger part 50.
#[test]
fn a_carrier_binding_is_the_receivers_instance_whether_or_not_received() {
    for (tag, binding) in [("bare", "Car"), ("own", "Car[V = V]")] {
        let ns = format!("wi0rp29cb7.unrecv_{tag}");
        assert_eq!(
            run_src(
                &unreceived_rel_program(
                    &ns,
                    binding,
                    "Car[V = Int64]",
                    "car(v: 9, f: lambda (x: Int64) -> x)"
                ),
                &format!("{ns}.go")
            ),
            Ok(10),
            "{binding}"
        );
        let two = format!("wi0rp29cb7.unrecv_{tag}_two");
        assert_refused_naming(
            &load_errors(&unreceived_rel_program(
                &two,
                binding,
                "Car[V = String]",
                "car(v: \"s\", f: lambda (x: String) -> 9)",
            )),
            &["mix.b (op-arg): expected Car[V = Int64], got Car[V = String]"],
            &format!("a second instance at `B = {binding}`"),
        );
    }
}

/// A WITNESS providing `Rel[A = Tag, B = Tag]` for a `Tag` it does not declare, its own `mix`
/// matching on `b`, and `go` calling `Rel.mix(k1, {second})` over a `Tag[X = Int64]`.
fn witness_rel_program(ns: &str, second_ty: &str, second: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Tag
    sort X = ?
    entity tag(x: X)
  end
  sort Rel
    sort A = ?
    sort B = ?
    operation left(a: A) -> Int64
    operation right(b: B) -> Int64
    operation mix(a: A, b: B) -> Int64
  end
  sort TagRel
    provides Rel[A = Tag, B = Tag]
    operation left(a: Tag) -> Int64 = 1
    operation right(b: Tag) -> Int64 = 2
    operation mix(a: Tag, b: Tag) -> Int64 = match b case tag(_) -> 3
  end
  operation go() -> Int64 =
    let k1: Tag[X = Int64] = tag(x: 1)
    let k2: {second_ty} = {second}
    Rel.mix(k1, k2)
  sort App
    entity app
    requires anthill.cli.Main
    operation main(args: List[String]) -> Int64 = go()
  end
end
"#
    )
}

/// A WITNESS'S BINDING NAMING ITS CARRIER IS ANY INSTANCE: `TagRel provides Rel[A = Tag, B =
/// Tag]` is written inside `TagRel`, where `Tag` is a FOREIGN sort — fresh per reference, as
/// the witness's own `mix(a: Tag, b: Tag)` reads it — so `Rel.mix` takes two `Tag`s of
/// different `X`, as the qualified `TagRel.mix` does. Runs to 3. The sixth pass decided "this
/// instance" against the call's DISPATCH carrier, and refused it "expected Tag[X = Int64], got
/// Tag[X = String]" while the declaration rule refused the member that would tie them (the
/// seventh review, MEASURED). FAILS under ledger part 18.
#[test]
fn a_witness_binding_naming_its_carrier_is_any_instance() {
    let ns = "wi0rp29cb7.wit";
    assert_eq!(
        run_src(
            &witness_rel_program(ns, "Tag[X = String]", "tag(x: \"s\")"),
            &format!("{ns}.go")
        ),
        Ok(3)
    );
}

/// … AND IT IS STILL A BINDING: `Rel.mix(k1, 5)` is refused, `b` being a `Tag`. Dropped — the
/// binding skipped as "ref-shaped, no parameter of the carrier" (the fifth pass) — the call
/// held `b` to nothing, loaded, and died in the member's `match` (MEASURED: `match_failed`).
/// FAILS under ledger part 19.
#[test]
fn a_witness_binding_naming_its_carrier_is_still_a_binding() {
    assert_refused_naming(
        &load_errors(&witness_rel_program("wi0rp29cb7.wit5", "Int64", "5")),
        &["mix.b (op-arg): expected Tag[X = ", "got Int64"],
        "a `5` where the witness binds a `Tag`",
    );
}

/// A PROVISION FOR A FOREIGN CARRIER reads alike: `Car provides Zip[A = List, B = List]`
/// dispatches on a `List`, and its two bare `List`s are two lists — `Zip.both([1, 2], ["x"])`
/// runs to 2 + 1, as `Car`'s own `both[X, Y](a: List[T = X], b: List[T = Y])` takes them.
/// Refused "expected List[T = Int64], got List[T = String]" by the same dispatch-carrier test
/// (MEASURED). FAILS under ledger part 18.
#[test]
fn a_foreign_carrier_binding_is_any_instance() {
    let src = r#"
namespace wi0rp29cb7.zip
  import anthill.prelude.{Int64, Bool, String, List}
  sort Zip
    sort A = ?
    sort B = ?
    operation left(a: A) -> Int64
    operation right(b: B) -> Int64
    operation both(a: A, b: B) -> Int64
  end
  sort Car
    entity car
    provides Zip[A = List, B = List]
    operation left(a: List) -> Int64 = 1
    operation right(b: List) -> Int64 = 2
    operation both[X, Y](a: List[T = X], b: List[T = Y]) -> Int64 = List.length(a) + List.length(b)
  end
  operation go() -> Int64 =
    Zip.both([1, 2], ["x"])
  sort App
    entity app
    requires anthill.cli.Main
    operation main(args: List[String]) -> Int64 = go()
  end
end
"#;
    assert_eq!(run_src(src, "wi0rp29cb7.zip.go"), Ok(3));
}

/// `Sp.op(s: Sp, x: T) effects {Error[T]}` at `Car provides Sp[T = V]`, the override `op[W](s:
/// Car, x: W) effects {Error[W]}`, and `use` over a `Car[V = {v}]` calling `Sp.op(c, {arg})`
/// while declaring `{declared}`.
fn open_argument_program(ns: &str, v: &str, arg: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String, List, Option, Error}}
  import anthill.prelude.Option.{{some, none}}
  sort Sp
    sort T = ?
    operation op(s: Sp, x: T) -> Int64 effects {{Error[T]}}
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation op[W](s: Car, x: W) -> Int64 effects {{Error[W]}} = 1
  end
  operation use(c: Car[V = {v}]) -> Int64 effects {{{declared}}} =
    Sp.op(c, {arg})
end
"#
    )
}

/// WHAT AN ARGUMENT LEAVES OPEN IS WHAT THE CALL CHECKED IT AGAINST: an empty literal's element
/// and a `none`'s payload are decided by the spec's parameter as the call bound it, so the
/// override's `W` — and its `Error[W]` — is `List[T = Int64]`, `Option[T = Int64]`. Read off the
/// argument alone, `W` was a list of nothing and a bare `Option`, and a caller declaring the
/// right row was refused "undeclared effect: Error[T = List[T = ??T]]" (MEASURED; the sixth
/// review's tree loaded both). A LOAD VERDICT: the incurred row is decided at load. FAILS under
/// ledger part 20.
#[test]
fn an_overrides_type_parameter_takes_what_an_open_argument_was_checked_against() {
    for (tag, v, arg) in [
        ("nil", "List[T = Int64]", "[]"),
        ("none", "Option[T = Int64]", "none"),
    ] {
        let ns = format!("wi0rp29cb7.open_{tag}");
        let errs = load_errors(&open_argument_program(&ns, v, arg, &format!("Error[{v}]")));
        assert!(
            errs.is_empty(),
            "`{arg}` is checked against `{v}`: {errs:#?}"
        );
    }
}

/// … AND ITS CONTROL: the same calls declaring `Error[String]` are refused, naming the effect
/// at the type the call checked the argument against. Passes either way by design: the spec
/// operation's own `Error[T]` names it whichever way the override's `W` is read.
#[test]
fn an_overrides_type_parameter_takes_what_an_open_argument_was_checked_against_control() {
    for (tag, v, arg) in [
        ("nil", "List[T = Int64]", "[]"),
        ("none", "Option[T = Int64]", "none"),
    ] {
        let ns = format!("wi0rp29cb7.open_{tag}_c");
        assert_refused_naming(
            &load_errors(&open_argument_program(&ns, v, arg, "Error[String]")),
            &["undeclared effect", &format!("Error[T = {v}]")],
            &format!("`{arg}`'s effect at `{v}`"),
        );
    }
}

/// … AN UNANNOTATED LAMBDA'S PARAMETER TOO: `Sp.apply(c, lambda x -> 1)` checks the lambda
/// against `(x: T) -> Int64` at `T = String`, so the override's `W` is `String`. Refused
/// "undeclared effect: Error[T = ?W]" (MEASURED). Three reads each bind it — the argument
/// walked through the call's substitution, what the call checked it against, and the spec's
/// types at the call — so it passes with any one or two backed out, and FAILS with all three
/// (the ledger's note under part 21).
#[test]
fn an_overrides_type_parameter_takes_an_unannotated_lambdas_parameter() {
    let src = r#"
namespace wi0rp29cb7.open_lambda
  import anthill.prelude.{Int64, Bool, String, List, Option, Error}
  sort Sp
    sort T = ?
    operation apply(s: Sp, f: (x: T) -> Int64) -> Int64 effects {Error[T]}
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation apply[W](s: Car, f: (x: W) -> Int64) -> Int64 effects {Error[W]} = 1
  end
  operation use(c: Car[V = String]) -> Int64 effects {Error[String]} =
    Sp.apply(c, lambda x -> 1)
end
"#;
    let errs = load_errors(src);
    assert!(
        errs.is_empty(),
        "the lambda's parameter is the call's `String`: {errs:#?}"
    );
}

/// `Sp.op(s: Sp, a: Int64) -> Option[T = s.T]` at `Car provides Sp[T = V]`, the override
/// `op[W](c: Car, a: Int64) -> Option[T = W] effects {Error[W]}` — a parameter ONLY its return
/// names — and `use` over a `Car[V = Int64]` declaring `{declared}`.
fn return_only_program(ns: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, List, Bool, Option, String, Error}}
  import anthill.prelude.Option.{{some, none}}
  sort Sp
    sort T = ?
    operation op(s: Sp, a: Int64) -> Option[T = s.T]
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation op[W](c: Car, a: Int64) -> Option[T = W] effects {{Error[W]}} = none
  end
  operation use(k: Car[V = Int64]) -> Int64 effects {{{declared}}} =
    match Sp.op(k, 1)
      case some(v) -> v
      case none() -> 7
end
"#
    )
}

/// A PARAMETER ONLY THE OVERRIDE'S RETURN NAMES TAKES THE SPEC'S RETURN AS THE CALL REDUCES IT:
/// `-> Option[T = W]` behind `-> Option[T = s.T]` over a `Car[V = Int64]` is `W = Int64`, so the
/// override's `Error[W]` is `Error[Int64]`. The declarations were related with each projection
/// MASKED and the override's variable walked through that relation — which led nowhere, the
/// spec's variable having been bound to it — so `W` stayed free: "undeclared effect: Error[T =
/// ?W]" (MEASURED; the sixth review's tree ran it). FAILS under ledger part 21.
#[test]
fn an_overrides_type_parameter_only_its_return_names_is_bound() {
    let errs = load_errors(&return_only_program("wi0rp29cb7.ret_only", "Error[Int64]"));
    assert!(errs.is_empty(), "W is the receiver's Int64: {errs:#?}");
}

/// … AND ITS CONTROL: declaring `Error[String]` is refused, naming `Error[T = Int64]` — the
/// override's effect at the reduced return. FAILS under part 21 too (the effect then names
/// `?W`): it drives that the parameter is bound to the RIGHT type, where the row above only
/// shows it bound.
#[test]
fn an_overrides_type_parameter_only_its_return_names_is_bound_control() {
    assert_refused_naming(
        &load_errors(&return_only_program(
            "wi0rp29cb7.ret_only_c",
            "Error[String]",
        )),
        &["undeclared effect", "Error[T = Int64]"],
        "the override's effect at the reduced return",
    );
}

// ── the seventh review's finding 13: WHICH spec a projected member is read from ──────────────

/// `Car` providing two specs that each declare a member `E` — `first` then `second` — and
/// `Sp.put(s: Sp, k: s.E)`, called with `arg`.
fn two_specs_program(ns: &str, first: &str, second: &str, arg: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Other
    sort E = ?
    operation other(o: Other) -> Int64
  end
  sort Sp
    sort E = ?
    operation put(s: Sp, k: s.E) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides {first}
    provides {second}
    operation other(c: Car) -> Int64 = 0
    operation put(c: Car, k: Int64) -> Int64 = k + 1
  end
  operation go() -> Int64 =
    let c: Car[V = Int64] = car(v: 1)
    Sp.put(c, {arg})
end
"#
    )
}

/// A PROJECTED MEMBER IS READ FROM THE SPEC ITS RECEIVER IS DECLARED BY: `s.E` with `s: Sp` is
/// `Sp`'s `E`, whatever else the argument's sort provides. The call read the member by NAME from
/// the first provided spec that declares one, so with `Other[E = String]` written above `Sp[E =
/// Int64]` it took a `String` for `k` — and the member, which the declaration rule had admitted
/// against THIS provision's `Int64`, added 1 to it at run time (MEASURED on every build), while
/// the `Int64` it does take was refused at the call. Runs to 42, and the `String` is refused.
/// FAILS under ledger part 22.
#[test]
fn a_projected_member_is_read_from_the_spec_its_receiver_is_declared_by() {
    let ns = "wi0rp29cb8.two_specs";
    let src = two_specs_program(ns, "Other[E = String]", "Sp[E = Int64]", "41");
    assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(42));
    let src = two_specs_program(
        "wi0rp29cb8.two_specs_s",
        "Other[E = String]",
        "Sp[E = Int64]",
        "\"x\"",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["put.k (op-arg): expected Int64, got String"],
        "the other spec's `E` passed for `Sp`'s",
    );
}

/// … AND ITS CONTROL: with the two provisions in the other order the first spec declaring `E`
/// IS `Sp`, and it ran to 42 before this pass as now — it pins that the reading no longer
/// turns on that order. Passes on the tree before (ledger parts 22, 24 and 25 together); FAILS
/// under part 22 alone, where no spec is named and the two provisions, disagreeing, are
/// refused.
#[test]
fn a_projected_member_is_read_from_the_spec_its_receiver_is_declared_by_control() {
    let ns = "wi0rp29cb8.two_specs_o";
    let src = two_specs_program(ns, "Sp[E = Int64]", "Other[E = String]", "41");
    assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(42));
}

/// `Holder.get(c: C) -> c.T` and the witness `BoxHolder provides Holder[C = Box, T = Int64]`,
/// with `go`.
fn witness_member_program(ns: &str, go: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Holder
    sort C = ?
    sort T = ?
    operation get(c: C) -> c.T
  end
  sort Box
    entity box(n: Int64)
  end
  sort BoxHolder
    provides Holder[C = Box, T = Int64]
    operation get(c: Box) -> Int64 = c.n + 1
  end
  operation go() -> Int64 =
    {go}
end
"#
    )
}

/// OVER A WITNESS'S CARRIER THE MEMBER IS THE WITNESS'S BINDING: `c.T` with `c: C` in `Holder`
/// is `Holder`'s `T`, which `BoxHolder` binds to `Int64` for a `Box`. A witness's provision is
/// filed under the witness, so the call found no `Holder` among `Box`'s own rows and read `T`
/// from the first spec `Box` does provide that has one — the derived `Eq[T = Box]`: the result
/// was typed `Box`, and the `Int64` the member returns was read as an entity ("field_access:
/// receiver is not an entity (got Int64)", MEASURED on every build). The call types an `Int64`
/// and runs to 2 + 40; annotated `Box`, it is refused. FAILS under ledger part 23.
#[test]
fn a_witness_carriers_projected_member_is_the_witnesses_binding() {
    let ns = "wi0rp29cb8.wit_member";
    let src = witness_member_program(ns, "Holder.get(box(n: 1)) + 40");
    assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(42));
    let src = witness_member_program(
        "wi0rp29cb8.wit_member_b",
        "let r: Box = Holder.get(box(n: 1))\n    r.n + 40",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["r.annotation (let-binding): expected Box, got Int64"],
        "the witness's `T` is an Int64",
    );
}

/// … AT THE RECEIVER'S OWN ARGUMENTS, where the witness is generic: `ListHolder provides
/// Holder[C = List[T = E], U = Option[T = E]]` over a `List[T = Int64]` is `E = Int64`, so
/// `c.U` is `Option[T = Int64]`. It was "type 'List' has no member 'U'" (MEASURED). Runs the
/// witness's member, to the head 5. FAILS under ledger part 23.
#[test]
fn a_generic_witnesses_binding_is_read_at_the_receivers_arguments() {
    let ns = "wi0rp29cb8.wit_generic";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List, Option}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.List.{{cons, nil}}
  sort Holder
    sort C = ?
    sort U = ?
    operation get(c: C) -> c.U
  end
  sort ListHolder
    sort E = ?
    provides Holder[C = List[T = E], U = Option[T = E]]
    operation get(c: List[T = E]) -> Option[T = E] =
      match c
        case cons(x, _) -> some(x)
        case nil -> none
  end
  operation go() -> Int64 =
    match Holder.get([5, 6]) case some(v) -> v case none -> 0
end
"#
    );
    assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(5));
}

/// A free operation `f(c: Car, k: c.{member})` — its receiver declared at the CARRIER, naming
/// no spec — over a `Car` whose `provisions` are written as given, called with `arg`.
fn unnamed_owner_program(ns: &str, member: &str, provisions: &str, arg: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Other
    sort E = ?
    sort T = ?
    operation other(o: Other) -> Int64
  end
  sort Sp
    sort E = ?
    sort T = ?
    operation size(s: Sp) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
{provisions}
    operation other(c: Car) -> Int64 = 0
    operation size(c: Car) -> Int64 = 1
  end
  operation f(c: Car, k: c.{member}) -> Int64 = 1
  operation go() -> Int64 =
    let c: Car[V = String] = car(v: "s")
    f(c, {arg}) + 41
end
"#
    )
}

/// WHERE THE RECEIVER'S DECLARATION NAMES NO SPEC, TWO PROVISIONS BINDING THE MEMBER
/// DIFFERENTLY ARE REFUSED: `c.E` with `c: Car`, `Car` providing `Other[E = String]` and `Sp[E
/// = Int64]`, has two answers and no way to pick. The first provision written used to win, in
/// silence. FAILS under ledger part 24 (the call then takes `Other`'s `String`: "expected
/// String, got Int64").
#[test]
fn a_member_two_provisions_bind_differently_is_refused_where_no_spec_is_named() {
    let provisions =
        "    provides Other[E = String, T = Int64]\n    provides Sp[E = Int64, T = Int64]";
    assert_refused_naming(
        &load_errors(&unnamed_owner_program(
            "wi0rp29cb8.unnamed_two",
            "E",
            provisions,
            "41",
        )),
        &[
            "has a member 'E' by two specs it provides, which bind it differently",
            "`String`",
            "`Int64`",
        ],
        "two provisions, two bindings, no spec named",
    );
}

/// … AND ITS CONTROL: the two agreeing (`T = Int64` in both), the member is that type and the
/// call runs, to 1 + 41 — beside the derived `Eq[T = Car]` every entity sort provides, whose
/// `T` is its CARRIER parameter and no member of the provider. It guards the agreement rule
/// against counting a derived spec as a rival: FAILS under ledger part 25, and passes on the
/// tree before this pass (parts 22, 24 and 25 together), where the first written won.
#[test]
fn a_member_two_provisions_bind_differently_is_refused_where_no_spec_is_named_control() {
    let ns = "wi0rp29cb8.unnamed_agree";
    let provisions =
        "    provides Other[E = String, T = Int64]\n    provides Sp[E = Int64, T = Int64]";
    assert_eq!(
        run_src(
            &unnamed_owner_program(ns, "T", provisions, "41"),
            &format!("{ns}.go")
        ),
        Ok(42)
    );
}

/// A SPEC'S CARRIER PARAMETER IS NO MEMBER OF ITS PROVIDER: a `Car` providing nothing of its
/// own still provides the derived `Eq[T = Car]`, and `c.T` read `Car` off it — a projection
/// naming nothing the sort declares, answered with the sort itself. It is "no member 'T'" now.
/// FAILS under ledger part 24 (the program loads, `f(c, c)` passing a `Car` for `c.T`).
#[test]
fn a_specs_carrier_parameter_is_no_member_of_its_provider() {
    assert_refused_naming(
        &load_errors(&unnamed_owner_program(
            "wi0rp29cb8.unnamed_self",
            "T",
            "",
            "c",
        )),
        &["has no member 'T'"],
        "only derived specs declare a `T`",
    );
}

/// THE SPEC THE RECEIVER NAMES LENDS THE MEMBER OR NOTHING DOES: `k: s.T` with `s: Sp` over a
/// `Car provides Sp` — `T` left unbound — reads no `T`. It read the derived `Eq`'s, `Car`
/// itself, so `Sp.put(c, c)` passed a `Car` to a member taking an `Int64` — a member the
/// declaration rule admits, the unbound `T` being a wildcard there — and died "expected Int64,
/// got Entity" at run time (MEASURED on the builds before the sixth pass, which refused the
/// member by the same misreading). FAILS only with ledger parts 22, 24 and 25 backed out
/// together — the reading before this pass; each alone still refuses it.
#[test]
fn a_member_the_named_specs_provision_leaves_unbound_is_no_member() {
    let src = r#"
namespace wi0rp29cb8.owner_unbound
  import anthill.prelude.{Int64, String, List}
  sort Sp
    sort T = ?
    operation size(s: Sp) -> Int64
    operation put(s: Sp, k: s.T) -> Int64
  end
  sort Car
    entity car(v: Int64)
    provides Sp
    operation size(c: Car) -> Int64 = 1
    operation put(c: Car, k: Int64) -> Int64 = k + 1
  end
  operation go() -> Int64 =
    let c: Car = car(v: 1)
    Sp.put(c, c) + Sp.size(c)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["has no member 'T'"],
        "`Sp`'s `T` is unbound at `Car`",
    );
}

/// `Sp.put(s: Sp, k: Option[T = Int64]) -> Int64 effects {Error[k.T]}` and its verbatim
/// member, called QUALIFIED with a bare `5` — which the call wraps in `some(…)` — from a
/// caller declaring `declared`.
fn wrapped_projection_program(ns: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, List, Bool, Option, String, Error}}
  import anthill.prelude.Option.{{some, none}}
  sort Sp
    sort T = ?
    operation put(s: Sp, k: Option[T = Int64]) -> Int64 effects {{Error[k.T]}}
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    operation put(c: Car, k: Option[T = Int64]) -> Int64 effects {{Error[k.T]}} = 1
  end
  operation use(x: Car[V = Int64]) -> Int64{declared} = Car.put(x, 5)
end
"#
    )
}

/// A PROJECTION OVER AN ARGUMENT THE CALL WRAPS READS WHAT THE PARAMETER RECEIVES: `k:
/// Option[T = Int64]` given a bare `5` receives `some(5)`, so `k.T` is `Int64` and the call
/// charges `Error[Int64]`. The receiver read was the raw argument's `Int64`, which declares no
/// `T` — and was answered anyway by the first spec `Int64` provides, whose carrier parameter
/// happens to be named `T` and bound to `Int64` itself: the right answer by an accident the
/// carrier-parameter reading above removes. FAILS under ledger part 25 ("type 'Int64' has no
/// member 'T'").
#[test]
fn a_projection_over_a_wrapped_argument_reads_the_option() {
    let errs = load_errors(&wrapped_projection_program(
        "wi0rp29cb8.wrapped",
        " effects {Error[Int64]}",
    ));
    assert!(errs.is_empty(), "k.T over a wrapped 5 is Int64: {errs:#?}");
}

/// … AND ITS CONTROL: a pure caller is refused, naming the `Error[Int64]` the call charges —
/// so the row above shows the effect read, not dropped. FAILS under ledger part 25 too (the
/// refusal is then the projection's).
#[test]
fn a_projection_over_a_wrapped_argument_reads_the_option_control() {
    assert_refused_naming(
        &load_errors(&wrapped_projection_program("wi0rp29cb8.wrapped_c", "")),
        &["undeclared effect: Error[T = Int64]"],
        "the effect the wrapped argument's projection names",
    );
}

// ── the eighth review's fixes (the ninth pass) ──────────────────────────────────────────────

/// A PROVISION IS LEFT OUT OF THE AGREEMENT ONLY WHERE IT BINDS THE NAME TO THE PROVIDER
/// ITSELF. The eighth pass left out every spec "whose carrier parameter the name is" — and for
/// a spec that receives on ITSELF that question answers the first parameter an operation takes,
/// its ELEMENT: `Mp.put(m: Mp, key: K, value: W)` made `W` "the carrier", so `f(t: Tbl, v:
/// t.W)` at `Tbl provides Mp[K = String, W = Int64]` was "type 'Tbl' has no member 'W'"
/// (MEASURED: a program that ran; the verdict turned on the order `K` and `W` are declared in).
/// Runs to 41 + 1. FAILS under ledger part 27.
#[test]
fn a_spec_receiving_on_itself_lends_its_element() {
    let src = r#"
namespace wi0rp29cb9.elem
  import anthill.prelude.{Int64, String, List, Bool}
  sort Mp
    sort W = ?
    sort K = ?
    operation put(m: Mp, key: K, value: W) -> Int64
  end
  sort Tbl
    entity tbl(n: Int64)
    provides Mp[K = String, W = Int64]
    operation put(t: Tbl, key: String, value: Int64) -> Int64 = value + 1
  end
  operation f(t: Tbl, v: t.W) -> Int64 = Mp.put(t, "a", v)
  operation go() -> Int64 = f(tbl(n: 1), 41)
end
"#;
    assert_eq!(run_src(src, "wi0rp29cb9.elem.go"), Ok(42));
}

/// … AND WHERE ANOTHER SPEC DECLARES THE NAME TOO, the dropped provision's binding was not
/// merely missing: the OTHER spec's was read in silence. `put(c: Car, k: c.T)` at `Car provides
/// Sp[T = Int64]` and `Other[C = Car, T = String]` took `Other`'s `String`, the member rule
/// compared it against `Sp`'s `Int64` as a wildcard, and `Sp.put(car, 5)` ran `String.length`
/// on 5 (MEASURED). Two lenders that disagree are the loud refusal. FAILS under ledger part 27.
#[test]
fn a_member_two_specs_lend_differently_is_refused_at_its_own_signature() {
    let src = r#"
namespace wi0rp29cb9.two_lenders
  import anthill.prelude.{Int64, String, List, Bool}
  sort Sp
    sort T = ?
    operation put(s: Sp, k: T) -> Int64
  end
  sort Other
    sort C = ?
    sort T = ?
    operation peek(c: C) -> T
  end
  sort Car
    entity car(v: Int64)
    provides Sp[T = Int64]
    provides Other[C = Car, T = String]
    operation peek(c: Car) -> String = "s"
    operation put(c: Car, k: c.T) -> Int64 = String.length(k)
  end
  operation go() -> Int64 = Sp.put(car(v: 1), 5)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "has a member 'T' by two specs it provides, which bind it differently",
            "to `Int64` and",
            "to `String`",
        ],
        "a member two provisions bind differently",
    );
}

/// A BINDING'S REFERENCE TO THE DECLARING SORT IS THIS INSTANCE AT ANY DEPTH — AT THE CALL TOO.
/// The declaration rule reads `T = List[T = Car]` as a list of the receiver's own instance (the
/// interim reading), and so admits `both(s: Car, o: List[T = Car])`, which ties the two. The
/// self-receiver call held only a TOP-LEVEL bare carrier binding to that, so `Sp.both(x, [y])`
/// over a `Car[V = Int64]` and a list of `Car[V = String]` loaded and applied `x`'s function to
/// `y`'s string (MEASURED, run time): one predicate reads the binding for the rule and both
/// binders now. FAILS under ledger part 28.
#[test]
fn a_nested_carrier_binding_holds_a_self_receiver_call_to_this_instance() {
    let src = r#"
namespace wi0rp29cb9.nest_two
  import anthill.prelude.{Int64, String, List, Option}
  import anthill.prelude.List.{cons, nil}
  sort Sp
    sort T = ?
    operation both(s: Sp, o: T) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V, f: (x: V) -> Int64)
    provides Sp[T = List[T = Car]]
    operation both(s: Car, o: List[T = Car]) -> Int64 =
      match s
        case car(_, g) ->
          match o
            case cons(h, _) -> g(h.v)
            case nil -> 0
  end
  operation go() -> Int64 =
    let x: Car[V = Int64] = car(v: 40, f: lambda (n: Int64) -> n + 1)
    let y: Car[V = String] = car(v: "s", f: lambda (k: String) -> 0)
    let z: Car[V = Int64] = car(v: 41, f: lambda (n: Int64) -> 0)
    Sp.both(x, [y])
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "type mismatch in both.o (op-arg): expected List[T = Car[V = Int64]], got List[T \
             = Car[V = String]]",
        ],
        "a second instance behind a nested carrier binding",
    );
}

/// … AND ITS CONTROL: a list of the receiver's own instance is what the binding names; the call
/// runs, to 41 + 1. Passes either way by design.
#[test]
fn a_nested_carrier_binding_holds_a_self_receiver_call_to_this_instance_control() {
    let src = r#"
namespace wi0rp29cb9.nest_one
  import anthill.prelude.{Int64, String, List, Option}
  import anthill.prelude.List.{cons, nil}
  sort Sp
    sort T = ?
    operation both(s: Sp, o: T) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V, f: (x: V) -> Int64)
    provides Sp[T = List[T = Car]]
    operation both(s: Car, o: List[T = Car]) -> Int64 =
      match s
        case car(_, g) ->
          match o
            case cons(h, _) -> g(h.v)
            case nil -> 0
  end
  operation go() -> Int64 =
    let x: Car[V = Int64] = car(v: 40, f: lambda (n: Int64) -> n + 1)
    let y: Car[V = String] = car(v: "s", f: lambda (k: String) -> 0)
    let z: Car[V = Int64] = car(v: 41, f: lambda (n: Int64) -> 0)
    Sp.both(x, [z])
end
"#;
    assert_eq!(run_src(src, "wi0rp29cb9.nest_one.go"), Ok(42));
}

/// … AND AT THE CARRIER-PARAM CALL UNDER A GENERIC RECEIVER: `B = Car[V = V]` is the receiver's
/// instance, and inside `use[W](k1: Car[V = W], k2: Car[V = String])` the receiver's `V` is
/// `use`'s own `W`. The binder's arm was gated on a BARE binding, so the written one was read
/// at fresh slots and `Rel.mix(k1, k2)` loaded, applying a function over `Int64` to a `String`
/// (MEASURED). FAILS under ledger part 29.
#[test]
fn a_carrier_binding_at_its_own_parameters_holds_a_generic_receiver() {
    let src = r#"
namespace wi0rp29cb9.own_gen
  import anthill.prelude.{Int64, String, List}
  sort Rel
    sort A = ?
    sort B = ?
    operation left(a: A) -> Int64
    operation right(b: B) -> Int64
    operation mix(a: A, b: B) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V, f: (x: V) -> Int64)
    provides Rel[A = Car, B = Car[V = V]]
    operation left(a: Car) -> Int64 = 1
    operation right(b: Car) -> Int64 = 2
    operation mix(a: Car, b: Car) -> Int64 = match a case car(_, g) -> g(b.v)
  end
  operation use[W](k1: Car[V = W], k2: Car[V = String]) -> Int64 = Rel.mix(k1, k2)
  operation go() -> Int64 =
    let k1: Car[V = Int64] = car(v: 40, f: lambda (x: Int64) -> x + 1)
    let k2: Car[V = String] = car(v: "s", f: lambda (x: String) -> 0)
    use(k1, k2)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["type mismatch in mix.b (op-arg): expected Car[V = ?W], got Car[V = String]"],
        "a second instance behind a binding written at the carrier's own parameters",
    );
}

/// … AND ITS CONTROL: both arguments at the caller's one `W` are one instance; runs to 40 + 1.
/// Passes either way by design.
#[test]
fn a_carrier_binding_at_its_own_parameters_holds_a_generic_receiver_control() {
    let src = r#"
namespace wi0rp29cb9.own_gen_ok
  import anthill.prelude.{Int64, String, List}
  sort Rel
    sort A = ?
    sort B = ?
    operation left(a: A) -> Int64
    operation right(b: B) -> Int64
    operation mix(a: A, b: B) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V, f: (x: V) -> Int64)
    provides Rel[A = Car, B = Car[V = V]]
    operation left(a: Car) -> Int64 = 1
    operation right(b: Car) -> Int64 = 2
    operation mix(a: Car, b: Car) -> Int64 = match a case car(_, g) -> g(b.v)
  end
  operation use[W](k1: Car[V = W], k2: Car[V = W]) -> Int64 = Rel.mix(k1, k2)
  operation go() -> Int64 =
    let k1: Car[V = Int64] = car(v: 40, f: lambda (x: Int64) -> x + 1)
    let k2: Car[V = Int64] = car(v: 40, f: lambda (x: Int64) -> 0)
    use(k1, k2)
end
"#;
    assert_eq!(run_src(src, "wi0rp29cb9.own_gen_ok.go"), Ok(41));
}

/// AN ALIAS OF THE DECLARING SORT IS THE SORT: `sort MyCar = Car`, `provides Rel[A = Car, B =
/// MyCar]`. Three readers gave the alias three readings — the rule this instance, one binder
/// nothing at all — so `Rel.mix(x, 5)` passed an `Int64` where `B` is a `Car` and died
/// "receiver is not an entity" (MEASURED). FAILS under ledger part 30, and under part 29 (a
/// bare reference to the alias is no bare reference to the carrier).
#[test]
fn an_alias_of_the_carrier_in_a_binding_is_the_carrier() {
    let src = r#"
namespace wi0rp29cb9.alias
  import anthill.prelude.{Int64, String, List}
  sort Rel
    sort A = ?
    sort B = ?
    operation mix(a: A, b: B) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V, n: Int64)
    provides Rel[A = Car, B = MyCar]
    operation mix[W](a: Car, b: Car[V = W]) -> Int64 = b.n + 1
  end
  sort MyCar = Car
  operation go() -> Int64 =
    let x: Car[V = Int64] = car(v: 1, n: 1)
    let y: Car[V = String] = car(v: "s", n: 6)
    Rel.mix(x, 5)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["type mismatch in mix.b (op-arg): expected Car[V = Int64], got Int64"],
        "an argument held to nothing behind an alias of the carrier",
    );
}

/// `pick(s: Sp, o: s.T)` at `Car provides Sp[T = Car]`, with `Car`'s member `member`.
fn projected_bound_parameter_program(ns: &str, member: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Sp
    sort T = ?
    operation pick(s: Sp, o: s.T) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = Car]
    operation {member} -> Int64 = 41
  end
  operation go() -> Int64 = Sp.pick(car(v: 1), car(v: "s")) + 1
end
"#
    )
}

/// WHAT THE READING ABOVE DOES NOT REACH — A PROJECTION OF THE BOUND PARAMETER. `o: s.T` at `T =
/// Car` is no reference to the declaring sort that a binding writes: it reads the binding as
/// written, an instance of its own, in the rule and at the call alike. So the member taking an
/// instance of its own fits, and `Sp.pick(car(v: 1), car(v: "s"))` — two instances — runs to 41
/// + 1; typed by the parameter itself (`o: T`) the same call is refused at its argument
/// ([`a_carrier_binding_is_the_receivers_instance_whether_or_not_received`]). The scope line of
/// the interim reading, which WI-20261001-80ZV8 settles with `Self`. Passes under every part of
/// the three ledgers (MEASURED), by design: it pins what this pass does not reach.
#[test]
fn a_projection_of_the_bound_parameter_is_an_instance_of_its_own() {
    let ns = "wi0rp29cb9.proj_own";
    let src = projected_bound_parameter_program(ns, "pick[W](c: Car, o: Car[V = W])");
    assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(42));
}

/// … AND THE RULE READS IT SO: a member typing `o` by a bare `Car` — THIS instance — takes less
/// than the spec's instance of its own, and is refused as tied. Under every part as its twin.
#[test]
fn a_projection_of_the_bound_parameter_is_an_instance_of_its_own_misfit() {
    let src = projected_bound_parameter_program("wi0rp29cb9.proj_own_bad", "pick(c: Car, o: Car)");
    assert_refused_naming(
        &load_errors(&src),
        &[
            "parameter 2 (`o: Car`) takes less than the spec's",
            "ties `o` to the receiver",
        ],
        "a member tying what a projection of the bound parameter leaves an instance of its own",
    );
}

/// THE `some(…)` WRAP IS THE VALIDATION'S VERDICT. An argument typed by an ALIAS of an option
/// conforms as it is and is not wrapped; decided by the argument's HEAD, `get(m)` over `m:
/// MaybeInt` was read as wrapped — `k.T` then `MaybeInt` — and the bare `Int64` it returns
/// failed `bump`'s `match` at run time (MEASURED). Runs to 41 + 1. FAILS under ledger part 31.
#[test]
fn an_option_alias_is_not_wrapped() {
    let src = r#"
namespace wi0rp29cb9.wrap_alias
  import anthill.prelude.{Int64, Bool, String, List, Option, Error, Result}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Result.{ok, err}
  sort MaybeInt = Option[T = Int64]
  operation get(k: Option[T = Int64]) -> k.T =
    match k
      case some(v) -> v
      case none -> 0
  operation bump(o: Option[T = Int64]) -> Int64 =
    match o
      case some(v) -> v + 1
      case none() -> 0
  operation go() -> Int64 =
    let m: MaybeInt = some(41)
    bump(get(m))
end
"#;
    assert_eq!(run_src(src, "wi0rp29cb9.wrap_alias.go"), Ok(42));
}

/// … AND THE OTHER WAY: an `Option[T = Int64]` passed for an `Option[T = Option[T = Int64]]` IS
/// wrapped, so `k.T` is the option and `d: k.T` takes a bare 7 wrapped in turn. Read as not
/// wrapped (the head is already `Option`), `d` was typed `Int64` and `match d` died on the 7
/// (MEASURED). Runs to 7. FAILS under ledger part 31.
#[test]
fn an_option_passed_for_an_option_of_options_is_wrapped() {
    let src = r#"
namespace wi0rp29cb9.wrap_nested
  import anthill.prelude.{Int64, String, List, Option}
  import anthill.prelude.Option.{some, none}
  operation f(k: Option[T = Option[T = Int64]], d: k.T) -> Int64 =
    match d
      case some(x) -> x
      case none -> 0
  operation go() -> Int64 =
    f(some(5), 7)
end
"#;
    assert_eq!(run_src(src, "wi0rp29cb9.wrap_nested.go"), Ok(7));
}

/// … AND THEIR CONTROL: `orElse(m, m)` passes the option where `d: k.T` is `Int64`. Read as
/// wrapped (`k.T` = `MaybeInt`) it loaded and added an entity to an `Int64` at run time
/// (MEASURED). FAILS under ledger part 31.
#[test]
fn an_option_alias_is_not_wrapped_control() {
    let src = r#"
namespace wi0rp29cb9.wrap_alias_bad
  import anthill.prelude.{Int64, Bool, String, List, Option, Error, Result}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Result.{ok, err}
  sort MaybeInt = Option[T = Int64]
  operation orElse(k: Option[T = Int64], d: k.T) -> Int64 =
    match k
      case some(v) -> v + d
      case none -> d
  operation go() -> Int64 =
    let m: MaybeInt = some(40)
    orElse(m, m)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["type mismatch in orElse.d (op-arg): expected Int64, got MaybeInt"],
        "an option passed where the projected payload is expected",
    );
}

/// EVERY WITNESS COVERING THE RECEIVER MUST AGREE ON THE MEMBER, one that leaves it unbound
/// included. `Holder.get(c: C) -> c.T` over a `Box` two witnesses cover — one binding `T =
/// Int64`, one leaving it unbound and returning a `String`: the unbound one was skipped, the
/// call typed `Int64`, and whichever witness dispatch reached decided the value (MEASURED: `+
/// 40` on a `String`). FAILS under ledger part 32.
#[test]
fn a_covering_witness_leaving_the_member_unbound_is_not_skipped() {
    let src = r#"
namespace wi0rp29cb9.wit_unbound
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
    provides Holder[C = Box]
    operation get(c: Box) -> String = "s"
  end
  sort BoxHolderB
    provides Holder[C = Box, T = Int64]
    operation get(c: Box) -> Int64 = c.n + 1
  end
  operation go() -> Int64 = Holder.get(box(n: 1)) + 40
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "is covered by two witnesses of",
            "that do not agree on its member 'T'",
            "leaves it unbound",
        ],
        "a covering witness that leaves the member unbound",
    );
}

/// … AND TWO THAT BIND IT DIFFERENTLY: the first found used to lend its own, and the refusal a
/// caller got was a neutral `c.T` meeting an `Int64`. FAILS under ledger part 32.
#[test]
fn two_covering_witnesses_binding_a_member_differently_are_refused() {
    let src = r#"
namespace wi0rp29cb9.wit_two
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
    operation get(c: Box) -> Int64 = c.n + 1
  end
  sort BoxHolderB
    provides Holder[C = Box, T = String]
    operation get(c: Box) -> String = "s"
  end
  operation go() -> Int64 = Holder.get(box(n: 1)) + 40
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &[
            "is covered by two witnesses of",
            "binds it to `Int64` and",
            "binds it to `String`",
        ],
        "two covering witnesses that disagree",
    );
}

/// … AND THEIR CONTROL: two witnesses that agree lend the member; the bracket picks which runs,
/// to 2 + 40. Passes under every part of this pass, and FAILS under the earlier parts 22 and 23
/// (no witness read at all).
#[test]
fn two_covering_witnesses_binding_a_member_alike_lend_it() {
    let src = r#"
namespace wi0rp29cb9.wit_agree
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
    operation get(c: Box) -> Int64 = c.n + 1
  end
  sort BoxHolderB
    provides Holder[C = Box, T = Int64]
    operation get(c: Box) -> Int64 = 7
  end
  operation go() -> Int64 = Holder.get[Holder = BoxHolderA](box(n: 1)) + 40
end
"#;
    assert_eq!(run_src(src, "wi0rp29cb9.wit_agree.go"), Ok(42));
}

/// ONE MAP OF RECEIVERS FOR EVERY PROJECTION READER OF A CALL. `pick(k: Option[T = Int64])
/// requires Desc[T = k.T]` given a bare `5`: the parameter types, return and effects read the
/// option the parameter receives, the `requires` reader the raw `Int64` — which has no member
/// `T` — and the call was refused "a requirement suppliable at this call site" (MEASURED: a
/// program that ran before the eighth pass). Runs to 7. FAILS under ledger part 33.
#[test]
fn an_operation_level_requires_reads_the_wrapped_receiver() {
    let src = r#"
namespace wi0rp29cb9.recv_requires
  import anthill.prelude.{Int64, Bool, String, List, Option}
  import anthill.prelude.Option.{some, none}
  sort Desc
    sort T = ?
    operation tag() -> Int64
  end
  sort IntDesc
    provides Desc[T = Int64]
    operation tag() -> Int64 = 7
  end
  operation pick(k: Option[T = Int64]) -> Int64 requires Desc[T = k.T] = Desc.tag()
  operation go() -> Int64 = pick(5)
end
"#;
    assert_eq!(run_src(src, "wi0rp29cb9.recv_requires.go"), Ok(7));
}

/// … AND A LAMBDA'S HINT: `app(5, lambda (x) -> x + 1)` behind `f: (x: k.T) -> Int64` hinted
/// `x` as the neutral `k.T`, and the body's `x + 1` was refused (MEASURED). Runs to 41 + 1.
/// FAILS under ledger part 33.
#[test]
fn a_lambda_hint_reads_the_wrapped_receiver() {
    let src = r#"
namespace wi0rp29cb9.recv_hint
  import anthill.prelude.{Int64, Bool, String, List, Option}
  import anthill.prelude.Option.{some, none}
  operation app(k: Option[T = Int64], f: (x: k.T) -> Int64) -> Int64 = f(41)
  operation go() -> Int64 = app(5, lambda (x) -> x + 1)
end
"#;
    assert_eq!(run_src(src, "wi0rp29cb9.recv_hint.go"), Ok(42));
}

/// TWO PROVISIONS AGREE ON A MEMBER WHERE THEY BIND ONE TYPE, HOWEVER EACH SPELLS IT: `Other[E
/// = EC]` and `Sp[E = {EC}]` bind one row. Compared by structural identity they were "bound
/// differently", and `f(c: Car, g: … @ {c.E})` was refused (MEASURED: it ran before the eighth
/// pass). Runs to 1 + 41. FAILS under ledger part 34.
#[test]
fn two_provisions_binding_one_row_in_two_spellings_agree() {
    let src = r#"
namespace wi0rp29cb9.agree_row
  import anthill.prelude.{Int64, String, List, Bool, Error}
  sort Foo
    entity foo(n: Int64)
  end
  sort Other
    effects E = ?
    operation other(o: Other) -> Int64
  end
  sort Sp
    effects E = ?
    operation size(s: Sp) -> Int64
  end
  sort Car
    effects EC = ?
    entity car(v: Int64)
    provides Other[E = EC]
    provides Sp[E = {EC}]
    operation other(c: Car) -> Int64 = 0
    operation size(c: Car) -> Int64 = 1
  end
  operation pure1(x: Int64) -> Int64 = x + 41
  operation f(c: Car, g: (x: Int64) -> Int64 @ {c.E}) -> Int64 effects {c.E} = g(1)
  operation go() -> Int64 =
    let c: Car[EC = {}] = car(v: 1)
    f(c, pure1)
end
"#;
    assert_eq!(run_src(src, "wi0rp29cb9.agree_row.go"), Ok(42));
}

/// … AND AN ALIAS BESIDE WHAT IT NAMES: `Other[E = MyInt]` and `Sp[E = Int64]`. Runs to 42.
/// FAILS under ledger part 34.
#[test]
fn two_provisions_binding_a_type_and_its_alias_agree() {
    let src = r#"
namespace wi0rp29cb9.agree_alias
  import anthill.prelude.{Int64, String, List, Option}
  sort MyInt = Int64
  sort MyList = List[T = Int64]
  sort Other
    sort E = ?
    operation other(o: Other) -> Int64
  end
  sort Sp
    sort E = ?
    operation size(s: Sp) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Other[E = MyInt]
    provides Sp[E = Int64]
    operation other(c: Car) -> Int64 = 0
    operation size(c: Car) -> Int64 = 1
  end
  operation f(c: Car, k: c.E) -> Int64 = 42
  operation go() -> Int64 =
    let c: Car[V = Int64] = car(v: 1)
    f(c, 41)
end
"#;
    assert_eq!(run_src(src, "wi0rp29cb9.agree_alias.go"), Ok(42));
}

/// A FIELD PATH'S MEMBER IS READ FROM THE SPEC ITS FIELD IS DECLARED BY: `s.provider.K` over
/// `State`, whose `provider: P` is held to `requires DataProvider[P = P]`, is `DataProvider`'s
/// `K`. The path named no owner, so `MemStore`'s two provisions declaring a `K` —
/// `DataProvider[K = Int64]` and `Other[K = String]` — met the agreement and were refused
/// (MEASURED: it ran before the eighth pass). Runs to 42. FAILS under ledger part 35.
#[test]
fn a_field_paths_member_is_lent_by_the_requires_that_declares_it() {
    let src = r#"
namespace wi0rp29cb9.path_requires
  import anthill.prelude.{Int64, String, List}
  sort DataProvider
    sort P = ?
    sort K = ?
    operation key(p: P) -> Int64
  end
  sort Other
    sort K = ?
    operation other(o: Other) -> Int64
  end
  sort State
    sort P = ?
    requires DataProvider[P = P]
    entity state(provider: P)
  end
  sort MemStore
    entity mem(n: Int64)
    provides DataProvider[P = MemStore, K = Int64]
    provides Other[K = String]
    operation key(p: MemStore) -> Int64 = p.n
    operation other(o: MemStore) -> Int64 = 0
  end
  operation check(s: State, k: s.provider.K) -> Int64 = 42
  operation go() -> Int64 =
    let st: State[P = MemStore] = state(provider: mem(n: 1))
    check(st, 41)
end
"#;
    assert_eq!(run_src(src, "wi0rp29cb9.path_requires.go"), Ok(42));
}

/// A PARAMETER TYPED BY A FIELD-PATH PROJECTION IS CHECKED AGAINST ITS ARGUMENT. `check(s:
/// State, k: s.provider.K)` inside `fwd(s: State)` keeps the projection neutral; it was read as
/// "not determined", which withheld the comparison, and the eighth pass's head re-key removed
/// the one refusal such a forwarder met: `check(s, "oops")` loaded and `fwd(st) + 1` added 1 to
/// a string (MEASURED). A neutral over a stable path IS determined. FAILS under ledger part 36.
#[test]
fn a_parameter_typed_by_a_field_path_projection_is_checked() {
    let src = r#"
namespace wi0rp29cb9.path_arg
  import anthill.prelude.{Int64, String, List}
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
  sort MemStore
    entity mem(n: Int64)
    provides DataProvider[P = MemStore, K = Int64]
    operation key(p: MemStore) -> Int64 = p.n
  end
  operation check(s: State, k: s.provider.K) -> s.provider.K = k
  operation fwd(s: State) -> s.provider.K = check(s, "oops")
  operation go() -> Int64 =
    let st: State[P = MemStore] = state(provider: mem(n: 1))
    fwd(st) + 1
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["type mismatch in check.k (op-arg): expected s.provider.K, got String"],
        "an argument of another type for a field-path projection",
    );
}

/// … AND ITS CONTROL: forwarding an argument of the same projection fits, and runs to 41 + 1.
/// Passes either way by design.
#[test]
fn a_parameter_typed_by_a_field_path_projection_is_checked_control() {
    let src = r#"
namespace wi0rp29cb9.path_arg_ok
  import anthill.prelude.{Int64, String, List}
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
  sort MemStore
    entity mem(n: Int64)
    provides DataProvider[P = MemStore, K = Int64]
    operation key(p: MemStore) -> Int64 = p.n
  end
  operation check(s: State, k: s.provider.K) -> s.provider.K = k
  operation fwd(s: State, j: s.provider.K) -> s.provider.K = check(s, j)
  operation go() -> Int64 =
    let st: State[P = MemStore] = state(provider: mem(n: 1))
    fwd(st, 41) + 1
end
"#;
    assert_eq!(run_src(src, "wi0rp29cb9.path_arg_ok.go"), Ok(42));
}

/// … AND A RULE BODY'S CALL, which reaches the requirement through the eval bridge: `rule
/// answer(?r) :- pick(5, ?r)` over the same `pick`. The bridge read the raw `Int64` too, found
/// no member `T`, and residualized — the goal answered "no solutions" with nothing said, where
/// the call in an operation body ran (MEASURED: `?r = 7` before a spec's carrier parameter
/// stopped lending a member). FAILS under ledger part 37.
#[test]
fn a_rule_body_call_reads_the_wrapped_receiver() {
    let src = r#"
namespace wi0rp29cb9.recv_rule
  import anthill.prelude.{Int64, Bool, String, List, Option}
  import anthill.prelude.Option.{some, none}
  sort Desc
    sort T = ?
    operation tag() -> Int64
  end
  sort IntDesc
    provides Desc[T = Int64]
    operation tag() -> Int64 = 7
  end
  operation pick(k: Option[T = Int64]) -> Int64 requires Desc[T = k.T] = Desc.tag()
  rule answer(?r) :- pick(5, ?r)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(
        crate::common::one_definite_int(&mut kb, "wi0rp29cb9.recv_rule.answer"),
        Some(7)
    );
}
