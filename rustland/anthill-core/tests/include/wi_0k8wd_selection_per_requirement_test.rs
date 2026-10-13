//! WI-20261013-0K8WD — a call's selection is kept by the REQUIREMENT it is for, and not by
//! the sort that requirement requires.
//!
//! `Pair2` requires `OK: WeakOrd[T = K]` and `OV: WeakOrd[T = V]`. A call that named a
//! provider for each — `Pair2.both[K = String, V = Int64, OK = ByLength, OV = Descending](…)`
//! — was refused, "two providers are selected for anthill.prelude.WeakOrd … one spec, one
//! witness per call": a selection was `(required sort, provider)`, so the second was a
//! second provider for the first one's key. Written in the value's type the two were refused
//! the same way at the call that took the value, and with one selected the other was handed
//! the first one's provider. A sort with two named requirements on one sort could not be
//! called.
//!
//! What a selection is kept by now, and each is backed out below:
//!
//!   * THE REQUIREMENT'S NAME beside the sort (`SelectedSlot`, `selection_for_slot`): the
//!     walk that fills the callee's frame asks, entry by entry, for the selection of the
//!     requirement that entry is.
//!   * A PROVIDER IS HELD TO ITS OWN REQUIREMENT'S GOAL (`selection_goals`): `ByLength` is
//!     checked against `WeakOrd[T = String]`, and not against `OV`'s `WeakOrd[T = Int64]`.
//!   * A NAME NOBODY WROTE IS INFERRED WITH ITS OWN REQUIREMENT'S SELECTION
//!     (`infer_named_slot_bindings`), which for a requirement of its own is none.
//!
//! A REQUIREMENT IS THE SORT IT REQUIRES AT ITS BINDINGS, UNDER THE NAME IT IS GIVEN. This
//! ticket ended one step short of that: a declaration that states a sort twice at one type
//! — `requires Plus: Mon[T]` beside `requires Times: Mon[T]` — held it once, under two
//! names, and two providers for it were refused. WI-20261013-50ZMN made the two names two
//! requirements (`wi_50zmn_two_requirements_of_one_sort_test`); what this file still holds
//! of the older rule is the case that ticket kept: a line with NO name of its own states the
//! requirement the line beside it names. Two things make that reading hold:
//!
//!   * THE SECOND LINE IS RECORDED AT THE FIRST ONE'S FACT (`place_of_requirement`). It
//!     was recorded at a position of its own, one past the end of the chain, and every
//!     requirement stated after the pair one position late.
//!   * AN OPERATION'S ENTRY TAKES THE KEY OF THE FIRST ENTRY OF ITS FRAME THAT STATES ITS
//!     REQUIREMENT (`slot_key_at`): an operation's own `requires` may restate its sort's,
//!     and those are kept apart in the chain. Two entries state one where no goal tells
//!     them apart (`state_one_requirement`) — a parameter one of them leaves open is no
//!     difference — and they do not each have a name.
//!
//! And one that a selection read back by a name needs, where one read back by the sort did
//! not: THE POSITION A NAMED REQUIREMENT IS RECORDED AT IS THE CHAIN'S
//! (`KnowledgeBase::settle_named_requirement_slots`). It was the source line's, and the
//! chain is not in source order — a requirement with bindings is moved behind one without.
//!
//! ## Back-out
//!
//! Each mechanism mutated in place under a switch of its own, and every row of this file
//! run under every switch with the rows of the older files that select a provider
//! (wi840, wi841, wi844, wi870, wi1091, wi1094, wi_tx0g6, wi_wn9p8, wi_ee0ep, wi_0rrqp and
//! the rest of that family). Measured 2026-10-13 on this ticket's commit, and again on
//! WI-20261013-50ZMN's with the three rows that ticket rewrote
//! ([`a_requirement_stated_again_with_no_name_is_the_same_one`],
//! [`an_operation_that_restates_a_requirement_holds_one`],
//! [`a_requirement_after_a_restated_one_is_found`]) and the one it needed
//! ([`a_selection_at_a_restated_lines_key_is_what_the_name_is_inferred_with`] — with those
//! three rewritten, no row failed where the inference was handed no selection); the table
//! is the second measurement, over 723 rows:
//!
//! | backed out | fails |
//! |---|---|
//! | the name in the key — a selection read back by its sort alone (`selection_for_slot`) | `a_call_selects_a_provider_for_each_requirement`, `a_named_requirement_beside_an_unnamed_one_are_two`, `a_named_requirement_written_before_a_parameterless_one_is_found`, `a_provider_is_held_to_its_own_requirements_goal`, `a_requirement_after_a_restated_one_is_found`, `a_requirement_restated_with_a_parameter_left_open_is_the_same_one`, `a_selection_for_a_requirement_on_the_dispatched_spec_is_not_the_dispatchs`, `an_operations_own_two_requirements_are_selected_by_name`, `one_selected_and_the_other_left_out_is_decided_on_its_own`, `the_two_are_read_on_every_route_that_reads_one`, `the_two_written_in_the_values_type_answer_the_same`, `two_requirements_put_at_one_type_by_a_call_are_still_two`; in `wi_50zmn_two_requirements_of_one_sort_test`: `a_call_through_a_requirements_name_reads_that_requirement`, `a_callees_unnamed_requirement_takes_one_by_its_name`, `a_name_given_at_the_key_of_a_restated_requirement_is_handed_on`, `a_name_is_read_wherever_the_body_is_written`, `a_name_reaches_what_its_requirements_dictionary_holds`, `a_name_reaches_what_its_requirements_dictionary_holds_further_down`, `a_slot_the_arguments_type_binds_to_a_callers_name_is_that_names`, `a_sorts_and_an_operations_under_two_names_are_two`, `a_spec_operation_with_a_body_is_read_through_a_name`, `an_operation_written_above_the_requires_lines_reads_them`, `an_operations_own_two_requirements_are_two`, `each_of_the_two_is_handed_on_under_its_own_name`, `one_selected_and_the_other_left_out_is_decided_on_its_own`, `the_call_written_in_full_is_the_same_call`, `the_two_carried_by_a_values_type_answer_the_same`, `two_requirements_at_two_types_need_no_name`; and `spec_op_requirement_at_member_test::two_requirements_at_one_type_are_two_at_the_member`, `spec_op_requirement_at_member_test::two_requirements_reach_a_member_chosen_when_the_call_runs`, `wi_0rrqp_clause_typed_through_constructor_test::each_clause_reaches_its_own_of_two_requirements_on_one_sort`, `wi_12nkg_arrow_and_tuple_cover_test::two_requirements_at_two_arrows_are_each_read_by_their_own_call`, `wi_wn9p8_forward_soundness_test::a_forward_reaches_its_own_of_two_slots_on_one_sort` |
//! | a provider held to every goal on its sort (`selection_goals`) | `a_call_selects_a_provider_for_each_requirement`, `a_named_requirement_beside_an_unnamed_one_are_two`, `a_requirement_after_a_restated_one_is_found`, `a_requirement_restated_with_a_parameter_left_open_is_the_same_one`, `a_selection_for_a_requirement_on_the_dispatched_spec_is_not_the_dispatchs`, `an_operations_own_two_requirements_are_selected_by_name`, `one_selected_and_the_other_left_out_is_decided_on_its_own`, `the_two_are_read_on_every_route_that_reads_one`, `the_two_written_in_the_values_type_answer_the_same`; and `wi_0rrqp_clause_typed_through_constructor_test::each_clause_reaches_its_own_of_two_requirements_on_one_sort`, `wi_12nkg_arrow_and_tuple_cover_test::two_requirements_at_two_arrows_are_each_read_by_their_own_call` |
//! | the inference of an unwritten name handed any selection on its sort (`infer_named_slot_bindings`) | `one_selected_and_the_other_left_out_is_decided_on_its_own`; in `wi_50zmn_two_requirements_of_one_sort_test`: `one_selected_and_the_other_left_out_is_decided_on_its_own` |
//! | a restated line given a place of its own (`place_of_requirement`) | `a_requirement_after_a_restated_one_is_found`, `a_requirement_stated_again_with_no_name_is_the_same_one`; in `wi_50zmn_two_requirements_of_one_sort_test`: `a_call_that_names_neither_is_refused`, `a_call_through_a_requirements_name_reads_that_requirement`, `a_callees_unnamed_requirement_takes_one_by_its_name`, `a_goal_met_inside_a_resolution_is_not_read_from_the_first_of_two`, `a_line_with_no_name_beside_two_named_ones_is_refused`, `a_line_with_no_name_states_the_named_one_at_a_binding_that_holds_a_value`, `a_name_given_at_the_key_of_a_restated_requirement_is_handed_on`, `a_name_is_read_wherever_the_body_is_written`, `a_name_reaches_what_its_requirements_dictionary_holds`, `a_name_reaches_what_its_requirements_dictionary_holds_further_down`, `a_name_says_which_requirement_and_not_that_it_fits`, `a_parameter_that_writes_neither_slot_is_refused`, `a_provider_selected_against_the_values_type_is_a_type_error`, `a_spec_operation_with_a_body_is_read_through_a_name`, `a_witness_with_two_requirements_takes_a_provider_for_each`, `an_operation_written_above_the_requires_lines_reads_them`, `each_of_the_two_is_handed_on_under_its_own_name`, `one_selected_and_the_other_left_out_is_decided_on_its_own`, `the_call_written_in_full_is_the_same_call`, `the_two_carried_by_a_values_type_answer_the_same`, `which_requirement_a_line_states_does_not_turn_on_how_its_binding_is_written`; and `wi_wn9p8_forward_soundness_test::a_forward_reaches_its_own_of_two_slots_on_one_sort` |
//! | an entry keyed by itself and not by the first that states its requirement (`slot_key_at`) | `a_requirement_restated_with_a_parameter_left_open_is_the_same_one`, `a_selection_at_a_restated_lines_key_is_what_the_name_is_inferred_with`, `an_operation_that_restates_a_requirement_holds_one`; in `wi_50zmn_two_requirements_of_one_sort_test`: `a_name_given_at_the_key_of_a_restated_requirement_is_handed_on`; and `wi841_call_site_selection_test::two_witnesses_for_one_spec_in_one_bracket_are_refused`, `wi844_sorted_set_driver_test::two_witnesses_for_one_requirement_are_refused_whoever_wrote_them` |
//! | two entries compared as written, a parameter left open counted as a difference (`state_one_goal`) | `a_requirement_restated_with_a_parameter_left_open_is_the_same_one`; in `wi_50zmn_two_requirements_of_one_sort_test`: `a_line_with_no_name_beside_two_named_ones_is_refused` |
//! | the dispatch reading any selection on its spec (`pinned_selection_for`) | `a_selection_for_a_requirement_on_the_dispatched_spec_is_not_the_dispatchs` |
//! | the recorded positions left as the source lines' (`settle_named_requirement_slots`) | `a_named_requirement_written_before_a_parameterless_one_is_found`, `a_requirement_after_a_restated_one_is_found`; in `wi_50zmn_two_requirements_of_one_sort_test`: `a_call_through_a_requirements_name_reads_that_requirement`, `a_callees_unnamed_requirement_takes_one_by_its_name`, `a_name_given_at_the_key_of_a_restated_requirement_is_handed_on`, `a_name_is_read_wherever_the_body_is_written`, `a_name_reaches_what_its_requirements_dictionary_holds`, `a_name_reaches_what_its_requirements_dictionary_holds_further_down`, `a_name_says_which_requirement_and_not_that_it_fits`, `a_spec_operation_with_a_body_is_read_through_a_name`, `a_witness_with_two_requirements_takes_a_provider_for_each`, `an_operation_written_above_the_requires_lines_reads_them`, `each_of_the_two_is_handed_on_under_its_own_name`, `one_selected_and_the_other_left_out_is_decided_on_its_own`, `the_call_written_in_full_is_the_same_call`, `the_two_carried_by_a_values_type_answer_the_same`, `which_requirement_a_line_states_does_not_turn_on_how_its_binding_is_written`; and `wi840_named_requires_slot_test::the_sort_level_slot_position_indexes_the_chain`, `wi_wn9p8_forward_soundness_test::a_forward_reaches_its_own_of_two_slots_on_one_sort` |
//! | that inference handed none (`infer_named_slot_bindings`) | `a_selection_at_a_restated_lines_key_is_what_the_name_is_inferred_with` |
//!
//! PASS EITHER WAY, BY DESIGN — the controls: [`one_requirement_selected_is_as_before`],
//! [`a_carriers_two_slots_are_read_through_a_spec`],
//! [`a_short_name_that_picks_out_two_requirements_is_refused`] and
//! [`a_provider_selected_against_the_arguments_type_is_a_type_error`]. Each says why at its
//! site.

use anthill_core::eval::{Interpreter, Value};

/// Providers whose answers differ: `ByLength` orders strings by length where `String`'s
/// own orders them by their text, `Descending` and `Ascending` are opposite orders of
/// `Int64` beside its own, and `Sum` and `Product` are two `Mon[T = Int64]` with no
/// default between them.
const DECLS: &str = r#"
  import anthill.prelude.{Int64, String, Bool, Error, EmptyStream, Relation, Ord, WeakOrd, PartialOrd, PartialEq, Eq}
  import anthill.prelude.Numeric.{sub, add, mul}
  import anthill.prelude.PartialEq.{eq}

  sort ByLength
    provides Ord[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(a.length(), b.length())
  end
  sort Descending
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end
  sort Ascending
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(a, b)
  end

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
"#;

/// The ticket's sort: two named requirements on one sort, at two parameters. `both` is the
/// ticket's `cmp` — the keys, then the values where the keys are equal — in the dot
/// spelling; `keyDirect` and `valDirect` read one requirement each.
const PAIR: &str = r#"
  sort Pair2
    sort K = ?
    sort V = ?
    requires OK: WeakOrd[T = K]
    requires OV: WeakOrd[T = V]
    entity entry(k1: K, k2: K, v1: V, v2: V)
    operation both(p: Self) -> Int64 =
      let c = p.k1.compare(p.k2)
      if eq(c, 0) then p.v1.compare(p.v2) else c
    operation keyDirect(p: Self) -> Int64 = match p case entry(k1, k2, v1, v2) -> WeakOrd.compare(k1, k2)
    operation valDirect(p: Self) -> Int64 = match p case entry(k1, k2, v1, v2) -> WeakOrd.compare(v1, v2)
    operation one(k1: K, k2: K, v1: V, v2: V) -> Self = entry(k1: k1, k2: k2, v1: v1, v2: v2)
  end
"#;

fn program(ns: &str, body: &str) -> String {
    format!("namespace {ns}\n{DECLS}\n{}end\n", body.replace("NS", ns))
}

/// `PAIR` and a `Driver` whose `run` is `expr`, with `ops` written before it.
fn pair_driver(ns: &str, ops: &str, expr: &str) -> String {
    program(
        ns,
        &format!(
            "{PAIR}\n  sort Driver\n    import NS.Pair2.{{entry, keyDirect, valDirect}}\n{ops}    \
             operation run() -> Int64 =\n      {expr}\n  end\n"
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

fn run(ns: &str, ops: &str, expr: &str) -> i64 {
    drive(&pair_driver(ns, ops, expr), &format!("{ns}.Driver.run"))
}

fn refusal(ns: &str, ops: &str, expr: &str) -> Vec<String> {
    crate::common::load_errors_of(&pair_driver(ns, ops, expr))
}

// ── The ticket's rows ────────────────────────────────────────────────

/// THE TICKET'S PROGRAM. Equal keys by length, so the answer is the values' order: `7 - 3`
/// under `Descending`, `3 - 7` under `Ascending`. And each requirement read alone answers
/// by its own provider — `"bob"` against `"amyy"` is `-1` by length.
#[test]
fn a_call_selects_a_provider_for_each_requirement() {
    let entry = r#"entry(k1: "bob", k2: "amy", v1: 3, v2: 7)"#;
    for (ns, ov, expected) in [
        ("wi0k8wd.both.desc", "Descending", 4),
        ("wi0k8wd.both.asc", "Ascending", -4),
    ] {
        assert_eq!(
            run(
                ns,
                "",
                &format!("Pair2.both[K = String, V = Int64, OK = ByLength, OV = {ov}]({entry})")
            ),
            expected,
            "`OK = ByLength, OV = {ov}`",
        );
    }
    let uneven = r#"entry(k1: "bob", k2: "amyy", v1: 3, v2: 7)"#;
    assert_eq!(
        run(
            "wi0k8wd.both.key",
            "",
            &format!("Pair2.keyDirect[K = String, V = Int64, OK = ByLength, OV = Descending]({uneven})")
        ),
        -1,
        "the keys are compared by `OK`",
    );
    assert_eq!(
        run(
            "wi0k8wd.both.val",
            "",
            &format!("Pair2.valDirect[K = String, V = Int64, OK = ByLength, OV = Descending]({uneven})")
        ),
        4,
        "the values are compared by `OV`",
    );
}

/// TWO REQUIREMENTS ARE TWO WHERE A CALL PUTS ONE TYPE IN BOTH PARAMETERS. `K` and `V` are
/// both `Int64` here, so the two goals the call must answer are one text, `WeakOrd[T =
/// Int64]`; the requirements are told apart as they are declared, and the body reads each
/// at its own parameter.
#[test]
fn two_requirements_put_at_one_type_by_a_call_are_still_two() {
    let entry = "entry(k1: 1, k2: 5, v1: 1, v2: 5)";
    for (ns, ok, ov, key, val) in [
        ("wi0k8wd.onetype.da", "Descending", "Ascending", 4, -4),
        ("wi0k8wd.onetype.ad", "Ascending", "Descending", -4, 4),
    ] {
        let bracket = format!("[K = Int64, V = Int64, OK = {ok}, OV = {ov}]");
        assert_eq!(
            run(&format!("{ns}.key"), "", &format!("Pair2.keyDirect{bracket}({entry})")),
            key,
            "the keys, under `OK = {ok}`",
        );
        assert_eq!(
            run(&format!("{ns}.val"), "", &format!("Pair2.valDirect{bracket}({entry})")),
            val,
            "the values, under `OV = {ov}`",
        );
    }
}

/// THE TWO WRITTEN IN THE VALUE'S TYPE answer the same at a call that writes neither: in a
/// result type, in a `let`'s annotation, on the receiver, and on the constructor.
#[test]
fn the_two_written_in_the_values_type_answer_the_same() {
    let ty = |ov: &str| format!("Pair2[K = String, V = Int64, OK = ByLength, OV = {ov}]");
    let fields = r#"k1: "bob", k2: "amy", v1: 3, v2: 7"#;
    for (ov, expected) in [("Descending", 4), ("Ascending", -4)] {
        let lower = ov.to_lowercase();
        let t = ty(ov);
        assert_eq!(
            run(
                &format!("wi0k8wd.intype.result.{lower}"),
                &format!("    operation mk() -> {t} = entry({fields})\n"),
                "Pair2.both(mk())"
            ),
            expected,
            "a result typed `OV = {ov}`",
        );
        assert_eq!(
            run(
                &format!("wi0k8wd.intype.let.{lower}"),
                "",
                &format!("let p: {t} = entry({fields})\n      Pair2.both(p)")
            ),
            expected,
            "a `let` annotated `OV = {ov}`",
        );
        assert_eq!(
            run(
                &format!("wi0k8wd.intype.receiver.{lower}"),
                "",
                &format!("{t}.both(entry({fields}))")
            ),
            expected,
            "the receiver's bracket, `OV = {ov}`",
        );
        assert_eq!(
            run(
                &format!("wi0k8wd.intype.ctor.{lower}"),
                "",
                &format!("Pair2.both(entry[K = String, V = Int64, OK = ByLength, OV = {ov}]({fields}))")
            ),
            expected,
            "the constructor's bracket, `OV = {ov}`",
        );
    }
    // One in the bracket and the other in the argument's type are the two all the same.
    assert_eq!(
        run(
            "wi0k8wd.intype.mixed",
            &format!("    operation mk() -> {} = entry({fields})\n", ty("Descending")),
            "Pair2.both[OV = Descending](mk())"
        ),
        4,
        "`OV` in the bracket, `OK` read off the argument's type",
    );
}

/// EVERY ROUTE THAT READS A SLOT OFF A TYPE reads each of the two: a parameter that leaves
/// both unwritten and takes them from its argument, an operation used as a function value,
/// and a generic signature that forwards each under a name of its own — on an operation
/// and on a sort.
#[test]
fn the_two_are_read_on_every_route_that_reads_one() {
    let mk = |ov: &str| {
        format!(
            "    operation mk() -> Pair2[K = String, V = Int64, OK = ByLength, OV = {ov}] = \
             entry(k1: \"bob\", k2: \"amyy\", v1: 3, v2: 7)\n"
        )
    };
    for (ov, val) in [("Descending", 4), ("Ascending", -4)] {
        let lower = ov.to_lowercase();
        let t = format!("Pair2[K = String, V = Int64, OK = ByLength, OV = {ov}]");
        for (member, expected) in [("valDirect", val), ("keyDirect", -1)] {
            assert_eq!(
                run(
                    &format!("wi0k8wd.routes.unwritten.{lower}.{}", member.to_lowercase()),
                    &format!(
                        "{}    operation any(p: Pair2[K = String, V = Int64]) -> Int64 = \
                         Pair2.{member}(p)\n",
                        mk(ov)
                    ),
                    "any(mk())"
                ),
                expected,
                "a parameter that writes neither slot, `{member}` under `OV = {ov}`",
            );
            assert_eq!(
                run(
                    &format!("wi0k8wd.routes.eta.{lower}.{}", member.to_lowercase()),
                    &format!("{}    operation ap(f: (p: {t}) -> Int64, x: {t}) -> Int64 = f(x)\n", mk(ov)),
                    &format!("ap({member}, mk())")
                ),
                expected,
                "`{member}` as a function value, under `OV = {ov}`",
            );
            assert_eq!(
                run(
                    &format!("wi0k8wd.routes.forward.{lower}.{}", member.to_lowercase()),
                    &format!(
                        "{}    operation relay[K, V, A, B](p: Pair2[K = K, V = V, OK = A, OV = B]) -> Int64\n      \
                         requires A: WeakOrd[T = K], B: WeakOrd[T = V]\n      \
                         = Pair2.{member}(p)\n",
                        mk(ov)
                    ),
                    "relay(mk())"
                ),
                expected,
                "forwarded under an operation's own two names, `{member}` under `OV = {ov}`",
            );
        }
    }
    // A sort's own two names, forwarded — and with one type in both parameters, where a
    // forward by the goal alone could not tell the two apart.
    for (member, expected) in [("keyDirect", 4), ("valDirect", -4)] {
        let ns = format!("wi0k8wd.routes.sortforward.{}", member.to_lowercase());
        let src = program(
            &ns,
            &format!(
                "{PAIR}
  sort Wrap
    sort K = ?
    sort V = ?
    requires A: WeakOrd[T = K]
    requires B: WeakOrd[T = V]
    operation go(p: Pair2[K = K, V = V, OK = A, OV = B]) -> Int64 = Pair2.{member}(p)
  end
  sort Driver
    import NS.Pair2.{{entry}}
    operation mk() -> Pair2[K = Int64, V = Int64, OK = Descending, OV = Ascending] =
      entry(k1: 1, k2: 5, v1: 1, v2: 5)
    operation run() -> Int64 = Wrap.go[K = Int64, V = Int64, A = Descending, B = Ascending](mk())
  end
"
            ),
        );
        assert_eq!(
            drive(&src, &format!("{ns}.Driver.run")),
            expected,
            "forwarded under a sort's own two names, `{member}`",
        );
    }
}

/// A PROVIDER IS HELD TO THE GOAL OF THE REQUIREMENT IT WAS SELECTED FOR, and to no other:
/// the two swapped — an order of `Int64` for the keys, which are strings — is refused
/// naming the provider that does not fit.
#[test]
fn a_provider_is_held_to_its_own_requirements_goal() {
    crate::common::assert_refused_naming(
        &refusal(
            "wi0k8wd.swapped",
            "",
            r#"Pair2.both[K = String, V = Int64, OK = Descending, OV = ByLength](entry(k1: "bob", k2: "amy", v1: 3, v2: 7))"#,
        ),
        &["wi0k8wd.swapped.Descending provides anthill.prelude.WeakOrd, but not at the bindings"],
        "`OK = Descending` where the keys are strings",
    );
}

/// ONE SELECTED AND THE OTHER LEFT OUT. The other is a requirement of its own, so nothing
/// the call selected is its answer, and it is decided as a call that selects nothing
/// decides it.
///
/// Where the call BUILDS the value, the slot nobody wrote is inferred: `String` has an
/// order of its own, and `"bob"` against `"amy"` is `1` by it; `Bool` has none, and the
/// call is refused for it. Where the call TAKES a value whose type does not say the slot,
/// the call is refused as it is with one requirement — the value was built with some
/// provider, and a provider built here would answer for another
/// ([`one_requirement_selected_is_as_before`] holds the one-requirement twin). What the
/// refusal says would be built is the left-out type's own, where it named the provider
/// selected for the OTHER requirement.
#[test]
fn one_selected_and_the_other_left_out_is_decided_on_its_own() {
    let built = r#"let p = Pair2.one[K = Int64, V = String, OK = Descending](1, 5, "bob", "amy")"#;
    assert_eq!(
        run("wi0k8wd.leftout.built.val", "", &format!("{built}\n      Pair2.valDirect(p)")),
        1,
        "`OV` left out where the value is built: `String`'s own order",
    );
    assert_eq!(
        run("wi0k8wd.leftout.built.key", "", &format!("{built}\n      Pair2.keyDirect(p)")),
        4,
        "and `OK` is the one selected",
    );
    crate::common::assert_refused_naming(
        &refusal(
            "wi0k8wd.leftout.none",
            "",
            "let p = Pair2.one[K = Int64, V = Bool, OK = Descending](1, 5, true, false)\n      \
             Pair2.keyDirect(p)",
        ),
        &["anthill.prelude.WeakOrd[T = anthill.prelude.Bool]", "no impl provides anthill.prelude.WeakOrd"],
        "`OV` left out at a type with no order",
    );
    let taken = refusal(
        "wi0k8wd.leftout.taken",
        "",
        r#"Pair2.valDirect[K = Int64, V = String, OK = Descending](entry(k1: 1, k2: 5, v1: "bob", v2: "amy"))"#,
    );
    crate::common::assert_refused_naming(
        &taken,
        &[
            "leaves its named requirement slot `OV: anthill.prelude.WeakOrd` universally quantified",
            "a construction here would answer for anthill.prelude.String",
        ],
        "`OV` left out where the value is taken",
    );
    assert!(
        !taken.iter().any(|e| e.contains("would answer for wi0k8wd.leftout.taken.Descending")),
        "the provider selected for `OK` is not what `OV` would be given: {taken:?}",
    );
}

/// AN OPERATION'S OWN TWO REQUIREMENTS are selected by their names as a sort's are, and at
/// one type in both parameters.
#[test]
fn an_operations_own_two_requirements_are_selected_by_name() {
    let decl = "
  sort Use
    operation cmp2[K, V](k1: K, k2: K, v1: V, v2: V) -> Int64
      requires ok: WeakOrd[T = K], ov: WeakOrd[T = V]
      = let c = WeakOrd.compare(k1, k2)
        if eq(c, 0) then WeakOrd.compare(v1, v2) else c
    operation run() -> Int64 = CALL
  end
";
    for (ns, call, expected) in [
        (
            "wi0k8wd.opnames.two",
            r#"cmp2[K = String, V = Int64, ok = ByLength, ov = Descending]("bob", "amy", 3, 7)"#,
            4,
        ),
        (
            "wi0k8wd.opnames.two.asc",
            r#"cmp2[K = String, V = Int64, ok = ByLength, ov = Ascending]("bob", "amy", 3, 7)"#,
            -4,
        ),
        (
            "wi0k8wd.opnames.onetype",
            "cmp2[K = Int64, V = Int64, ok = Descending, ov = Ascending](1, 1, 3, 7)",
            -4,
        ),
        (
            "wi0k8wd.opnames.onetype.key",
            "cmp2[K = Int64, V = Int64, ok = Descending, ov = Ascending](1, 5, 3, 7)",
            4,
        ),
    ] {
        assert_eq!(
            drive(&program(ns, &decl.replace("CALL", call)), &format!("{ns}.Use.run")),
            expected,
            "`{call}`",
        );
    }
}

/// A NAMED REQUIREMENT BESIDE AN UNNAMED ONE ON THE SAME SORT are two: the unnamed one is
/// selected by the sort's short name, which picks it out alone since the other has a name.
/// On one sort, and with the unnamed one the operation's own.
#[test]
fn a_named_requirement_beside_an_unnamed_one_are_two() {
    let on_sort = "
  sort NU
    sort K = ?
    sort V = ?
    requires WeakOrd[T = K]
    requires OV: WeakOrd[T = V]
    operation cmp2(k1: K, k2: K, v1: V, v2: V) -> Int64 =
      let c = WeakOrd.compare(k1, k2)
      if eq(c, 0) then WeakOrd.compare(v1, v2) else c
  end
  sort Driver
    operation run() -> Int64 = NU.cmp2[K = String, V = Int64, WeakOrd = ByLength, OV = OVP](KEYS, 3, 7)
  end
";
    let on_op = "
  sort NU
    sort K = ?
    requires OK: WeakOrd[T = K]
    operation cmp2[V](k1: K, k2: K, v1: V, v2: V) -> Int64 requires WeakOrd[T = V] =
      let c = WeakOrd.compare(k1, k2)
      if eq(c, 0) then WeakOrd.compare(v1, v2) else c
  end
  sort Driver
    operation run() -> Int64 = NU.cmp2[K = String, V = Int64, OK = ByLength, WeakOrd = OVP](KEYS, 3, 7)
  end
";
    for (tag, decl) in [("sort", on_sort), ("op", on_op)] {
        for (row, ovp, keys, expected, what) in [
            ("desc", "Descending", r#""bob", "amy""#, 4, "the values, by the provider selected for them"),
            ("asc", "Ascending", r#""bob", "amy""#, -4, "the values, by the other"),
            ("keys", "Descending", r#""bob", "amyy""#, -1, "the keys, by length"),
        ] {
            let ns = format!("wi0k8wd.namedunnamed.{tag}.{row}");
            assert_eq!(
                drive(
                    &program(&ns, &decl.replace("OVP", ovp).replace("KEYS", keys)),
                    &format!("{ns}.Driver.run")
                ),
                expected,
                "{what} (the unnamed requirement on the {tag})",
            );
        }
    }
}

// ── A requirement stated again ───────────────────────────────────────

/// `Semi1` states `Mon[T]` twice, once under the name `Times` and once under none, in the
/// order `lines` gives; `Via` hands a requirement on under a name.
fn semi1(ns: &str, lines: &str, call: &str) -> String {
    program(
        ns,
        &format!(
            "
  sort Via
    sort T = ?
    requires M: Mon[T]
    operation via(a: T, b: T) -> T = Mon.combine(a, b)
  end
  sort Semi1
    sort T = ?
{lines}
    operation mulAdd(a: T, b: T, c: T) -> T = Mon.combine(Mon.combine(a, b), c)
    operation byName(a: T, b: T, c: T) -> T = Times.combine(Times.combine(a, b), c)
    operation handedOn(a: T, b: T, c: T) -> T =
      Via.via[T = T, M = Times](Via.via[T = T, M = Times](a, b), c)
  end
  sort Driver
    operation run() -> Int64 = {call}
  end
"
        ),
    )
}

/// A `requires` LINE WITH NO NAME STATES THE REQUIREMENT THE LINE BESIDE IT NAMES: `Semi1`
/// states `Mon[T]` under the name `Times` and again under none, and holds one requirement,
/// `Times`. Its chain has one entry and its dictionary one slot, whichever line is written
/// first.
///
/// A selection under the name is that requirement's — `(2 + 3) + 4` with `Sum`, `(2 * 3) *
/// 4` with `Product` — read by a call that names no requirement, by one written through
/// the name, and by a callee handed it under the name. The sort's short name is no key of
/// it: the requirement has a name. And a call that selects nothing is refused for the two
/// providers there are, under that name.
///
/// (Two lines that EACH have a name are two requirements —
/// `wi_50zmn_two_requirements_of_one_sort_test`. Until WI-20261013-50ZMN they were one,
/// and this row drove `requires Plus: Mon[T]` beside `requires Times: Mon[T]` under one
/// provider.)
#[test]
fn a_requirement_stated_again_with_no_name_is_the_same_one() {
    for (order, lines) in [
        ("named.first", "    requires Times: Mon[T]\n    requires Mon[T]"),
        ("unnamed.first", "    requires Mon[T]\n    requires Times: Mon[T]"),
    ] {
        for (provider, expected) in [("Sum", 9), ("Product", 24)] {
            for member in ["mulAdd", "byName", "handedOn"] {
                let ns = format!(
                    "wi0k8wd.again.{order}.{}.{}",
                    provider.to_lowercase(),
                    member.to_lowercase()
                );
                assert_eq!(
                    drive(
                        &semi1(&ns, lines, &format!("Semi1.{member}[T = Int64, Times = {provider}](2, 3, 4)")),
                        &format!("{ns}.Driver.run")
                    ),
                    expected,
                    "`{member}[Times = {provider}]`, {order}",
                );
            }
        }
        let ns = format!("wi0k8wd.again.{order}.shortname");
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&semi1(&ns, lines, "Semi1.mulAdd[T = Int64, Mon = Sum](2, 3, 4)")),
            &["unknown type-param 'Mon'"],
            "the requirement has a name, and the sort's short name is not a key of it",
        );
        let ns = format!("wi0k8wd.again.{order}.none");
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&semi1(&ns, lines, "Semi1.mulAdd[T = Int64](2, 3, 4)")),
            &[
                "requirement `Times: ",
                "is ambiguous among providers",
                &format!("{ns}.Sum"),
                &format!("{ns}.Product"),
            ],
            "nothing selected, and two providers",
        );
    }
}

/// AN OPERATION'S OWN LINE THAT RESTATES ITS SORT'S REQUIREMENT WITH NO NAME is the same
/// case: the frame keeps the two entries apart and the body reads either by the one goal.
/// One provider is the requirement's, selected under the name the sort gives it or under
/// the sort's short name, which picks out the operation's line; two are refused.
///
/// (An operation's own list that states one requirement under TWO names — `requires plus:
/// Mon[T], times: Mon[T]` — holds two since WI-20261013-50ZMN, and is that ticket's
/// row.)
#[test]
fn an_operation_that_restates_a_requirement_holds_one() {
    let restates = "
  sort Holder
    sort HT = ?
    requires m: Mon[T = HT]
    operation fold3(a: HT, b: HT, c: HT) -> HT requires Mon[T = HT] = Mon.combine(Mon.combine(a, b), c)
  end
  sort Use
    operation run() -> Int64 = Holder.fold3[HT = Int64, BRACKET](2, 3, 4)
  end
";
    for (row, bracket, expected) in [
        ("first", "m = Sum", 9),
        ("second", "Mon = Sum", 9),
        ("second.product", "Mon = Product", 24),
        ("both", "m = Product, Mon = Product", 24),
    ] {
        let ns = format!("wi0k8wd.oprestates.{row}");
        assert_eq!(
            drive(&program(&ns, &restates.replace("BRACKET", bracket)), &format!("{ns}.Use.run")),
            expected,
            "`[{bracket}]`",
        );
    }
    let ns = "wi0k8wd.oprestates.two";
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program(ns, &restates.replace("BRACKET", "m = Sum, Mon = Product"))),
        &[
            "two providers are selected for",
            &format!("{ns}.Sum"),
            &format!("{ns}.Product"),
            "for one requirement",
        ],
        "two providers for the one requirement",
    );
}

/// A PROVIDER SELECTED AT THE KEY OF A RESTATED LINE IS THE NAME'S, WHERE THE SORT HAS A
/// DEFAULT TOO. `Sum` is marked `Mon`'s default at `Int64`; `[Mon = Product]`, written at
/// the operation's line, is the selection for `m`, and `m` — which the call did not write
/// — is inferred with it: `(2 × 3) × 4`.
#[test]
fn a_selection_at_a_restated_lines_key_is_what_the_name_is_inferred_with() {
    let restates = "
  import anthill.reflect.typing.DefaultProvider
  fact DefaultProvider(spec: Mon, provider: Sum)
  sort Holder
    sort HT = ?
    requires m: Mon[T = HT]
    operation fold3(a: HT, b: HT, c: HT) -> HT requires Mon[T = HT] = Mon.combine(Mon.combine(a, b), c)
  end
  sort Use
    operation run() -> Int64 = Holder.fold3[HT = Int64BRACKET](2, 3, 4)
  end
";
    for (row, bracket, expected) in [
        ("selected", ", Mon = Product", 24),
        ("named", ", m = Product", 24),
        ("silent", "", 9),
    ] {
        let ns = format!("wi0k8wd.oprestates.default.{row}");
        assert_eq!(
            drive(&program(&ns, &restates.replace("BRACKET", bracket)), &format!("{ns}.Use.run")),
            expected,
            "`[HT = Int64{bracket}]`, `Sum` the default",
        );
    }
}

/// AN OPERATION RESTATES ITS SORT'S REQUIREMENT WHERE NO GOAL TELLS THE TWO APART, which is
/// weaker than their being written alike. `Two` has two parameters and both lines bind
/// one: the sort's entry is completed with `Two`'s own default for the other and the
/// operation's is not, and a parameter one of them leaves open is no difference between
/// them — the body's `Two.mix(a, b)` is covered by either. Two providers are refused.
///
/// A second line that binds the parameter the first left open, differently, is another
/// requirement, and takes a provider of its own.
#[test]
fn a_requirement_restated_with_a_parameter_left_open_is_the_same_one() {
    let decl = "
  sort Two
    sort A = ?
    sort B = ?
    operation mix(a: A, b: A) -> A
  end
  sort SumS
    provides Two[A = Int64, B = String]
    operation mix(a: Int64, b: Int64) -> Int64 = add(a, b)
  end
  sort ProductS
    provides Two[A = Int64, B = String]
    operation mix(a: Int64, b: Int64) -> Int64 = mul(a, b)
  end
  sort ProductB
    provides Two[A = Int64, B = Bool]
    operation mix(a: Int64, b: Int64) -> Int64 = mul(a, b)
  end
  sort Holder
    sort HT = ?
    requires m: Two[A = HT, B = String]
    operation same(a: HT, b: HT) -> HT requires Two[A = HT] = Two.mix[A = HT, B = String](a, b)
    operation other(a: HT, b: HT) -> HT requires Two[A = HT, B = Bool] = Two.mix[A = HT, B = String](a, b)
  end
  sort Use
    operation run() -> Int64 = CALL
  end
";
    let ns = "wi0k8wd.leftopen.two";
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program(
            ns,
            &decl.replace("CALL", "Holder.same[HT = Int64, m = SumS, Two = ProductS](2, 3)"),
        )),
        &["two providers are selected for", &format!("{ns}.SumS"), &format!("{ns}.ProductS"), "for one requirement"],
        "the operation's `Two[A = HT]` is the sort's `Two[A = HT, B = String]` to any goal",
    );
    let ns = "wi0k8wd.leftopen.other";
    assert_eq!(
        drive(
            &program(
                ns,
                &decl.replace("CALL", "Holder.other[HT = Int64, m = SumS, Two = ProductB](2, 3)"),
            ),
            &format!("{ns}.Use.run")
        ),
        5,
        "`Two[A = HT, B = Bool]` is another requirement: `m` is `SumS`, and the body's \
         call at `B = String` reads `m`",
    );
}

/// A REQUIREMENT STATED AFTER A RESTATED ONE IS FOUND AT ITS OWN ENTRY. `Tri` states
/// `WeakOrd[T]` under the name `A` and again under none, and `WeakOrd[T = U]` once, so its
/// chain has two entries, and `C` is the second. Counted by lines it was the third: a call
/// that selected for it was refused, two providers for one sort, and one that did not,
/// "position … could not be established".
///
/// And after two that EACH have a name (`Tri2`: `A` and `B` at `T`, `C` at `U`) it is the
/// third of three, each read by its own name — `"bob"` against `"amyy"` is `-1` by length
/// and `1` by reverse length.
#[test]
fn a_requirement_after_a_restated_one_is_found() {
    let tri = "
  sort RevLength
    provides Ord[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(b.length(), a.length())
  end
  sort Tri
    sort T = ?
    sort U = ?
    requires A: WeakOrd[T]
    requires WeakOrd[T]
    requires C: WeakOrd[T = U]
    operation tcmp(a: T, b: T) -> Int64 = WeakOrd.compare(a, b)
    operation ucmp(a: U, b: U) -> Int64 = WeakOrd.compare(a, b)
  end
  sort Tri2
    sort T = ?
    sort U = ?
    requires A: WeakOrd[T]
    requires B: WeakOrd[T]
    requires C: WeakOrd[T = U]
    operation acmp(a: T, b: T) -> Int64 = A.compare(a, b)
    operation bcmp(a: T, b: T) -> Int64 = B.compare(a, b)
    operation ucmp(a: U, b: U) -> Int64 = WeakOrd.compare(a, b)
  end
  sort Driver
    operation run() -> Int64 = CALL
  end
";
    let three = "[T = String, U = Int64, A = ByLength, B = RevLength, C = Descending]";
    for (ns, call, expected) in [
        ("wi0k8wd.tri.u.desc", "Tri.ucmp[T = String, U = Int64, A = ByLength, C = Descending](1, 5)".to_string(), 4),
        ("wi0k8wd.tri.u.asc", "Tri.ucmp[T = String, U = Int64, A = ByLength, C = Ascending](1, 5)".to_string(), -4),
        (
            "wi0k8wd.tri.t",
            r#"Tri.tcmp[T = String, U = Int64, A = ByLength, C = Descending]("bob", "amyy")"#.to_string(),
            -1,
        ),
        ("wi0k8wd.tri2.u", format!("Tri2.ucmp{three}(1, 5)"), 4),
        ("wi0k8wd.tri2.a", format!(r#"Tri2.acmp{three}("bob", "amyy")"#), -1),
        ("wi0k8wd.tri2.b", format!(r#"Tri2.bcmp{three}("bob", "amyy")"#), 1),
    ] {
        assert_eq!(
            drive(&program(ns, &tri.replace("CALL", &call)), &format!("{ns}.Driver.run")),
            expected,
            "`{call}`",
        );
    }
}

/// A NAMED REQUIREMENT WRITTEN BEFORE A PARAMETERLESS ONE IS FOUND AT ITS ENTRY. The chain
/// is read off the requirement facts, and loading moves a requirement with bindings behind
/// one without: `Marker` is first in `Box2`'s chain and `O` second, and in `Pair3`'s the
/// two named ones follow it. A selection is read back at the entry its requirement has
/// there, where the slot was recorded by the line it was written on.
#[test]
fn a_named_requirement_written_before_a_parameterless_one_is_found() {
    let decl = "
  sort Marker
  end
  sort Box2
    sort T = ?
    requires O: WeakOrd[T]
    requires Marker
    entity box(a: T, b: T)
    operation directOf(p: Self) -> Int64 = match p case box(a, b) -> WeakOrd.compare(a, b)
  end
  sort Pair3
    sort K = ?
    sort V = ?
    requires OK: WeakOrd[T = K]
    requires Marker
    requires OV: WeakOrd[T = V]
    entity entry(k1: K, k2: K, v1: V, v2: V)
    operation keyDirect(p: Self) -> Int64 = match p case entry(k1, k2, v1, v2) -> WeakOrd.compare(k1, k2)
    operation valDirect(p: Self) -> Int64 = match p case entry(k1, k2, v1, v2) -> WeakOrd.compare(v1, v2)
  end
  sort Driver
    import NS.Box2.{box}
    import NS.Pair3.{entry}
    operation run() -> Int64 = CALL
  end
";
    let pair = "[K = Int64, V = Int64, OK = Descending, OV = Ascending](entry(k1: 1, k2: 5, v1: 1, v2: 5))";
    for (ns, call, expected) in [
        ("wi0k8wd.marker.one.desc", "Box2.directOf[T = Int64, O = Descending](box(a: 1, b: 5))".to_string(), 4),
        ("wi0k8wd.marker.one.asc", "Box2.directOf[T = Int64, O = Ascending](box(a: 1, b: 5))".to_string(), -4),
        ("wi0k8wd.marker.two.key", format!("Pair3.keyDirect{pair}"), 4),
        ("wi0k8wd.marker.two.val", format!("Pair3.valDirect{pair}"), -4),
    ] {
        assert_eq!(
            drive(&program(ns, &decl.replace("CALL", &call)), &format!("{ns}.Driver.run")),
            expected,
            "`{call}`",
        );
    }
}

// ── Controls ─────────────────────────────────────────────────────────

/// CONTROL — passes either way. One named requirement: selected, it answers by the
/// provider; left out where the value is taken, the call is refused, which is the rule
/// [`one_selected_and_the_other_left_out_is_decided_on_its_own`] keeps for the left-out
/// one of two.
#[test]
fn one_requirement_selected_is_as_before() {
    let boxed = "
  sort Box
    sort T = ?
    requires O: WeakOrd[T]
    entity box(a: T, b: T)
    operation directOf(p: Self) -> Int64 = match p case box(a, b) -> WeakOrd.compare(a, b)
  end
  sort Driver
    import NS.Box.{box}
    operation run() -> Int64 = CALL
  end
";
    for (ns, o, expected) in [
        ("wi0k8wd.control.one.desc", "Descending", 4),
        ("wi0k8wd.control.one.asc", "Ascending", -4),
    ] {
        assert_eq!(
            drive(
                &program(
                    ns,
                    &boxed.replace("CALL", &format!("Box.directOf[T = Int64, O = {o}](box(a: 1, b: 5))"))
                ),
                &format!("{ns}.Driver.run")
            ),
            expected,
            "`O = {o}`",
        );
    }
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program(
            "wi0k8wd.control.one.leftout",
            &boxed.replace("CALL", "Box.directOf[T = Int64](box(a: 1, b: 5))"),
        )),
        &[
            "leaves its named requirement slot `O: anthill.prelude.WeakOrd` universally quantified",
            "a construction here would answer for anthill.prelude.Int64",
        ],
        "the one requirement left out where the value is taken",
    );
}

/// CONTROL — passes either way. Through a spec the callee names no slot, and the carrier's
/// two are read off the provision that writes them, each at its own place in the carrier's
/// chain; no selection of the call is involved.
#[test]
fn a_carriers_two_slots_are_read_through_a_spec() {
    let decl = "
  sort Cmp
    sort C = ?
    operation cmpc(p: C) -> Int64
  end
  sort Pair2
    sort K = ?
    sort V = ?
    requires OK: WeakOrd[T = K]
    requires OV: WeakOrd[T = V]
    provides Cmp[C = Pair2[K = K, V = V, OK = OK, OV = OV]]
    entity entry(k1: K, k2: K, v1: V, v2: V)
    operation cmpc(p: Self) -> Int64 = match p case entry(k1, k2, v1, v2) -> WeakOrd.compare(v1, v2)
  end
  sort Driver
    import NS.Pair2.{entry}
    operation mk() -> Pair2[K = String, V = Int64, OK = ByLength, OV = OVP] =
      entry(k1: \"bob\", k2: \"amy\", v1: 3, v2: 7)
    operation run() -> Int64 = Cmp.cmpc(mk())
  end
";
    for (ns, ovp, expected) in [
        ("wi0k8wd.control.spec.desc", "Descending", 4),
        ("wi0k8wd.control.spec.asc", "Ascending", -4),
    ] {
        assert_eq!(
            drive(&program(ns, &decl.replace("OVP", ovp)), &format!("{ns}.Driver.run")),
            expected,
            "`Cmp.cmpc` of a pair typed `OV = {ovp}`",
        );
    }
}

/// CONTROL — passes either way. Two UNNAMED requirements on one sort have no name to be
/// told by, and the sort's short name picks out both: refused where the key is written.
#[test]
fn a_short_name_that_picks_out_two_requirements_is_refused() {
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program(
            "wi0k8wd.control.shortname",
            "
  sort NU
    sort K = ?
    sort V = ?
    requires WeakOrd[T = K]
    requires WeakOrd[T = V]
    operation kcmp(k1: K, k2: K) -> Int64 = WeakOrd.compare(k1, k2)
  end
  sort Driver
    operation run() -> Int64 = NU.kcmp[K = String, V = Int64, WeakOrd = ByLength](\"bob\", \"amy\")
  end
",
        )),
        &["'WeakOrd' names more than one requirement slot"],
        "one short name, two unnamed requirements",
    );
}

/// CONTROL — passes either way. A provider written in the bracket against the one the
/// argument's type says is a type error at the argument: the two write one parameter, so
/// they never reach a selection as two.
#[test]
fn a_provider_selected_against_the_arguments_type_is_a_type_error() {
    crate::common::assert_refused_naming(
        &refusal(
            "wi0k8wd.control.against",
            "    operation mk() -> Pair2[K = String, V = Int64, OK = ByLength, OV = Descending] = \
             entry(k1: \"bob\", k2: \"amy\", v1: 3, v2: 7)\n",
            "Pair2.both[OV = Ascending](mk())",
        ),
        &["expected Pair2[K = String, V = Int64, OK = ByLength, OV = Ascending]", "OV = Descending]"],
        "`OV = Ascending` in the bracket, `OV = Descending` in the argument's type",
    );
}

// ── A requirement on the spec the call dispatches ────────────────────

/// `Desc.pair` and a `Driver` that calls it with a provider selected for its requirement
/// `other`, which is on `req`.
fn own_spec(ns: &str, req: &str) -> String {
    format!(
        "namespace {ns}
  import anthill.prelude.{{Int64, String}}
  import anthill.prelude.Numeric.{{add}}
  sort Tagger
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort Desc
    sort T = ?
    operation tag(x: T) -> Int64
    operation pair[U](x: T, y: U) -> Int64 requires other: {req}[T = U]
  end
  sort Coin
    entity coin(n: Int64)
    provides Desc[T = Coin]
    operation tag(x: Coin) -> Int64 = 1
    operation pair[U](x: Coin, y: U) -> Int64 requires other: {req}[T = U] = add(10, {req}.tag(y))
  end
  sort Quiet
    provides Tagger[T = String]
    provides Desc[T = String]
    operation tag(x: String) -> Int64 = 2
    operation pair[U](x: String, y: U) -> Int64 requires other: {req}[T = U] = add(20, {req}.tag(y))
  end
  sort Loud
    provides Tagger[T = String]
    provides Desc[T = String]
    operation tag(x: String) -> Int64 = 3
    operation pair[U](x: String, y: U) -> Int64 requires other: {req}[T = U] = add(30, {req}.tag(y))
  end
  sort Driver
    import {ns}.Coin.{{coin}}
    operation loud() -> Int64 = Desc.pair[other = Loud](coin(n: 5), \"s\")
  end
end
"
    )
}

/// A PROVIDER SELECTED FOR A REQUIREMENT IS NOT THE DISPATCH'S, where the requirement is on
/// the very spec the call dispatches. `Desc.pair` requires `other: Desc[T = U]` — a second
/// `Desc`, at its second argument — and `[other = Loud]` selects for that. Read by the
/// sort alone the selection was taken for the dispatch of `pair` at `Coin`, and the call
/// was refused: "the call selected `Loud` for Desc, which provides no instance at these
/// bindings", of a provider that was never selected for `Desc[T = Coin]`.
///
/// The call is dispatched to `Coin.pair`, which adds 10 to what `Loud` answers for `"s"`,
/// 3. The second half is the control, the same requirement on `Tagger`: it never was the
/// dispatch's, and passes with the key read by the sort alone. That the member is handed
/// the selection at all is `spec_op_requirement_at_member_test`'s.
#[test]
fn a_selection_for_a_requirement_on_the_dispatched_spec_is_not_the_dispatchs() {
    for (ns, req) in [("wi0k8wd.ownspec.desc", "Desc"), ("wi0k8wd.ownspec.tagger", "Tagger")] {
        assert_eq!(
            drive(&own_spec(ns, req), &format!("{ns}.Driver.loud")),
            13,
            "`Desc.pair[other = Loud]`, `other` a requirement on `{req}`",
        );
    }
}
