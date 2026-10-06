//! WI-20261005-KSSA4 — a value typed at a spec is not a value of the spec's carrier.
//!
//! THE RULE (user, 2026-10-05): providing `F[X]` lets the operations of `F` be used on a
//! value of `X`; it does not make a value of `X` a value of `F`. So `w: Tagger` is not
//! `w: Tagger.C`. A value whose sort provides a spec is usable where a value of a sort
//! that REQUIRES the spec is expected — a type parameter under `requires Tagger[C = P]`,
//! or `Tagger.C` in a signature. A sort that receives on itself is its own carrier: a
//! `List` is a `Stream`, and `s: Stream` takes one.
//!
//! WHAT THE OTHER READING COST, measured on the parent commit with the ticket's sorts:
//! `via(w: Tagger) = Tagger.probe(w)` answered 7, and the same parameter handed to a
//! defaulted operation, to another sort's, or under a `requires` over `w.C`, loaded and
//! died "`__req_tag` not bound in caller frame" — a requirement met by a value that holds
//! no dictionary. Each is refused where the value is passed
//! ([`a_spec_typed_value_is_refused_where_the_carrier_is_expected`]), a provider's value
//! is refused at a parameter typed at the spec
//! ([`a_providers_value_is_refused_at_a_parameter_typed_at_the_spec`]), and the two
//! spellings that ask for a provider run as they did ([`the_member_spelling_runs`],
//! [`the_bound_spelling_runs`]).
//!
//! WHAT HAD TO COME FIRST. The bound spelling did not carry a spec with several
//! parameters: `total(c: FiniteCollection.C) effects FiniteCollection.E = size(c)` and its
//! written twin were both refused. A signature's members of one spec are ONE requirement,
//! a clause DETERMINES the elements it names from the provision at the carrier — at a
//! call, at a construction, and through a calling scope's own clause — and a clause says
//! what its spec itself requires: [`total_in_the_member_spelling_counts`],
//! [`total_in_the_bound_spelling_counts`], [`a_bound_is_passed_on`],
//! [`a_signatures_members_are_of_one_instance`].
//!
//! WHAT THE LIBRARY'S MOVE NEEDED. `MappedStream` and `FilteredStream` hold their source
//! in a field typed by their own `Source` and say `requires Iterable[C = Source, …]` on
//! the sort. A field typed by a parameter says nothing of the carrier, so the clause is
//! what a construction is held to: a value built where no provision could answer the
//! requirement, and the scope does not hold it, is refused where it is built
//! ([`a_lazy_carrier_is_not_built_over_a_source_that_cannot_be_walked`] — with the field
//! so typed and no such check, `mapped(5, f)` loaded and died "`__req_iterable` not bound
//! in caller frame"). A slot the construction leaves open is left to the call that fixes
//! it, and so is a choice between two providers
//! ([`a_slot_the_construction_leaves_open_is_left_to_the_call`],
//! [`a_tie_is_left_to_the_use_that_selects`]). A constant's body is not reached: it is
//! folded to a value, whose typer refuses nothing ([`a_constants_body_is_not_reached`]).
//!
//! The rule in the RULE LANGUAGE — `?x: Summable` and a written `domain(?x, Summable)`
//! refused, `?x: Summable.T` and the introducer taken — is driven in
//! `wi582_typed_rule_pattern_test`, `wi903_typed_bound_dot_rule_test`,
//! `wi_96ztm_two_dictionaries_test` and `wi_ak2aj_written_typed_var_test`; the example's
//! rows are `guardians_test`'s, and the Scala emitter's `BootstrapTest`'s.
//!
//! A refusal row asserts a LOAD verdict naming what is refused; a row that runs asserts
//! the value.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ───────────────────────────────
//!
//! EACH PART backed out present-but-wrong, APPLIED AND RUN over this file's 32 rows and
//! the 840 of the modules the change migrated (872, green before each), and over
//! `guardians_test`'s 67 where the part is the example's. A row of this file is named;
//! another module's is counted. (`wi582`'s row over a member that is not the carrier and
//! `wi_xzmgc`'s rule-bound row were written after that run, and measured over the parts
//! that could move them: 1 and 17–21.)
//!
//! THE RULE, AND THE BOUND SPELLINGS THAT CARRY IT
//!
//!  1. A PROVIDER CONFORMS TO ANY SPEC IT PROVIDES (`provider_conforms_to`). 10 FAIL:
//!     [`a_providers_value_is_refused_at_a_parameter_typed_at_the_spec`],
//!     [`total_typed_at_the_spec_takes_no_list`], and 8 of `n01py`, the capability
//!     matrix, `wi1119`, `wi_0rp29_review9`, `wi_3g1yt`, `wi_gnpg7` and `wi_xzmgc` (2).
//!  2. A SPEC-TYPED VALUE NOT REFUSED WHERE A CARRIER IS EXPECTED
//!     (`spec_typed_value_at_carrier_error`). 6 FAIL:
//!     [`a_spec_typed_value_is_refused_where_the_carrier_is_expected`],
//!     [`total_typed_at_the_spec_takes_no_list`], and 4 of `wi1119`, `wi590_enclosing_
//!     requires`, `wi608` and `wi_3g1yt`.
//!  3. ONE CLAUSE PER MEMBER in the sugar's drain, as it was. 20 FAIL:
//!     [`a_signatures_members_are_of_one_instance`] (refused, but over a second
//!     requirement `Tagger[Out = String]` nothing answers — two instances, not one),
//!     [`total_in_the_member_spelling_counts`], [`a_member_is_named_in_the_body`],
//!     [`a_spec_operation_over_a_member_is_backed_by_restating_it`],
//!     [`a_missing_provision_is_named_and_not_the_element_it_would_say`],
//!     [`the_open_parameter_is_found_by_its_variable`], and 14 of `n01py` (7), `x13yv`
//!     (3), the matrix, `wi_2kv4y`, `wi_3g1yt` and `wi_kxnex`.
//!  4. THE SCOPE'S CLAUSE READ FROM THE SORT HALF ALONE (`scope_clause_at_carrier` without
//!     the operation's own). 23 FAIL: [`total_in_the_bound_spelling_counts`],
//!     [`total_in_the_member_spelling_counts`], [`a_bound_is_passed_on`],
//!     [`a_spec_operation_over_a_member_is_backed_by_restating_it`],
//!     [`what_a_clause_implies_is_read_beside_another_clause_over_the_spec`], and 18 of
//!     `n01py` (5), `wi_pyns2` (4), `x13yv` (2), the matrix, `wi599`, `wi608`, `wi609`,
//!     `wi_2kv4y`, `wi_3g1yt` and `wi_kxnex`.
//!  5. A REQUIREMENT NOT COMPLETED AT ITS CARRIER (`dep_completed_at_carrier`). 11 FAIL:
//!     [`total_in_the_member_spelling_counts`],
//!     [`a_sort_that_provides_nothing_is_refused_beside_a_generic_witness`], and 9 of
//!     `n01py` (5), the matrix, `wi_2kv4y`, `wi_3g1yt` and `wi_gnpg7`.
//!  6. THE SORT'S CLAUSE NOT READ AT A CALL (`bind_sort_params_from_sort_requires`). 8
//!     FAIL, none here: `x13yv` (4), the matrix, `wi599`, `wi_2kv4y` and `wi945
//!     …a_sorts_own_clause_says_its_other_parameters`.
//!  7. THE SORT'S CLAUSE NOT READ AT A CONSTRUCTION
//!     (`bind_sort_params_from_sort_requires_at_construction`). THE STANDARD LIBRARY IS
//!     REFUSED — its own `mapped(iterator(c), f)` leaves `SourceEffects` unsaid — so every
//!     row that loads fails: 521 of the 872, 24 of this file's 32.
//!  8. A CLAUSE NOT READ THROUGH ITS SPEC'S OWN REQUIREMENTS (`requirements_implied_by`).
//!     3 FAIL: [`what_a_clause_implies_is_read_beside_another_clause_over_the_spec`] and
//!     `wi608` (2). Read only where no written clause names the spec, that row alone.
//!  9. A CLAUSE'S CARRIER READ AS ITS SPEC'S FIRST PARAMETER (`clause_carrier_param`). 1
//!     FAILS: [`a_carrier_declared_second_is_the_carrier`].
//! 10. A FOREIGN PARAMETER OF THE SAME NAME READ AS THE OWNER'S (`typaram_ref_vid`). 1
//!     FAILS: [`a_foreign_parameter_of_the_same_name_is_not_the_receivers`].
//! 11. A SPEC'S BODY NOT READING ITS OWN INSTANCE (`scope_own_instance_at_carrier`). 1
//!     FAILS: [`a_specs_default_body_builds_over_its_own_instance`].
//! 12. AN OVERRIDE'S PRECONDITION NOT ALIGNED BY TYPE PARAMETER (`type_param_var_align`).
//!     2 FAIL: [`a_spec_operation_over_a_member_is_backed_by_restating_it`] and `wi_kxnex
//!     …reverting_the_guardians_carrier_bindings_is_refused_at_load`.
//! 13. A MEMBER NOT READ IN THE BODY (`signature_spec_members`). 2 FAIL:
//!     [`a_member_is_named_in_the_body`] and
//!     [`the_library_and_the_examples_type_no_position_at_a_spec`] — the guardians
//!     library names `Llm.E` in a body and does not load.
//! 14. A WITNESS ADMITTING A VALUE AT THE SPEC IT PROVIDES FOR (`witness_provides_
//!     admissibly`). 3 FAIL, none here: `n01py` (2), `wi_0rp29_review9`.
//! 15. A SOLE PROJECTED ROW NOT RECONCILED (`sole_projected_row`). 5 FAIL, none here:
//!     `wi_mdwew` (3), `wi594`, `wi_0rp29_nested`.
//! 16. A FORMER TAKEN BY "GROUND, AND NO SORT" (`former_carrier`). 1 FAILS, not here: the
//!     matrix's `the_row_remainders`.
//!
//! THE RULE LANGUAGE — none of these rows is here; they are `wi582`'s and its neighbours'
//!
//! 17. A RULE VARIABLE TYPED AT A SPEC NOT REFUSED (`check_rule_sort_uses`). 7 FAIL:
//!     `wi582` (6) and `wi_96ztm …a_parameter_typed_at_the_spec_itself_is_refused`. With
//!     a rule body's goal sorts not recorded (`note_written_domain_goal_sorts`), `wi582
//!     …a_written_domain_goal_at_the_spec_is_refused` alone; with a constraint's
//!     (`note_constraint_domain_goal_sorts`), `…a_domain_goal_in_a_constraint_is_refused_
//!     too` alone; with an alias not read through, `…an_alias_of_the_spec_is_refused_as_
//!     the_spec_is` alone; with a head's members not recorded, `…a_member_that_is_not_
//!     the_carrier_is_refused_naming_the_spelling_that_is` alone.
//! 18. A RULE VARIABLE TYPED AT A SPEC'S MEMBER NOT LOWERED (the rule-head arm of the
//!     member sugar). 10 FAIL: `wi582` (8), `wi903`, `wi_ak2aj`. With a member reached
//!     through an alias that fixes others taken as through the spec, `wi582
//!     …a_member_through_an_alias_that_fixes_others_is_refused` alone.
//! 19. A RULE BOUND COMPARED AS A VALUE'S TYPE (`type_bound_verdict_view` without
//!     `spec_as_its_providers`). 11 FAIL: `wi582` (8), `wi_96ztm`, `wi_ak2aj` and
//!     `wi_xzmgc …a_rule_bound_that_writes_the_carrier_reads_the_composed_view`. With the
//!     pin of a bound that has an open slot so compared (`pin_bound`), `wi582
//!     …a_bound_with_a_slot_left_open_still_answers` alone; with a citation's argument
//!     (`relation.rs`), `…a_bounded_column_is_cited_with_a_providers_value` alone.
//! 20. A SPEC WITH NO OPERATION NOT CLASSIFIED BY ITS PROVISIONS (`spec_over_parameter`'s
//!     second leg). 8 FAIL: `wi582` (6), `wi903`, `wi_ak2aj` — `Summable` declares nothing
//!     that receives.
//! 21. EFFECT ROWS WALKED FOR THE SORTS A TYPE WRITES (`collect_sorts_written_as_types`).
//!     3 FAIL: `wi582 …a_row_label_inside_a_bound_is_no_variables_type`, and here
//!     [`the_census_counts_a_parameter_and_a_field`] and
//!     [`the_library_and_the_examples_type_no_position_at_a_spec`] — the census shares the
//!     walker, and counts `Error.reify`'s row label as a position.
//!
//! A CONSTRUCTION OWES ITS SORT'S REQUIREMENT
//!
//! 22. A CONSTRUCTION OWES NOTHING (`construction_meets_sort_requires`). 14 FAIL:
//!     [`a_construction_over_a_non_provider_is_refused_where_it_is_built`],
//!     [`a_construction_over_a_parameter_needs_the_scopes_requirement`],
//!     [`a_lazy_carrier_is_not_built_over_a_source_that_cannot_be_walked`],
//!     [`a_parameter_only_the_expected_type_fixes_is_judged`],
//!     [`a_requirement_fixed_in_full_is_judged_as_asked`],
//!     [`a_requirement_at_other_arguments_of_the_sort_is_refused`],
//!     [`what_a_field_fixed_is_asked_for_and_not_held_against_the_clause`] (its control),
//!     and 7 of `wi599`, `wi869`, `wi_mdwew` (4) and `wi_p5g39`.
//! 23. A CONSTRUCTION ASKED AS A CALL IS — the first cut, nothing left to a later use. 11
//!     FAIL, each a program that ran:
//!     [`a_slot_the_construction_leaves_open_is_left_to_the_call`],
//!     [`a_tie_is_left_to_the_use_that_selects`], and 9 of `wi_0rp29_review9` (6),
//!     `wi_0rp29_call_binding` (2) and `wi_wbhtm`.
//! 24. A TIE TAKEN AS THE SEARCH'S VERDICT. 3 FAIL: the same two rows and `wi_wbhtm
//!     …a_self_parameter_binds_the_value_in_type` — two providers at a slot no field
//!     fixed are a tie, and the call that fixes the slot picks.
//! 25. A REQUIREMENT FIXED IN FULL LEFT TO THE ROW CENSUS (`dep_leaves_something_open`). 1
//!     FAILS: [`what_a_field_fixed_is_asked_for_and_not_held_against_the_clause`] — its
//!     control loads, the census reading each element of a row by itself.
//! 26. TWO INSTANCES OF ONE SORT COMPARED BY HEAD IN THE ROW CENSUS
//!     (`row_binding_could_answer`). 1 FAILS:
//!     [`a_requirement_at_other_arguments_of_the_sort_is_refused`] (its open half loads).
//! 27. A ROW OVER ITS PROVIDER'S PARAMETERS NOT EXCLUDED AT ANOTHER SORT (the same
//!     function's other leg). 8 FAIL:
//!     [`a_sort_that_provides_nothing_is_refused_beside_a_generic_witness`] (loads),
//!     [`a_lazy_carrier_is_not_built_over_a_source_that_cannot_be_walked`] (loads),
//!     [`a_missing_provision_is_named_and_not_the_element_it_would_say`], and 5 of
//!     `n01py` (2), the matrix (2) and `x13yv`.
//! 28. A SCOPE PARAMETER READ AS A SORT IN THE ROW CENSUS (`ElementAt::ScopeParam`). 2
//!     FAIL, none here: `wi599 …free_op_clause_about_another_param_does_not_license` and
//!     `wi_mdwew …ambient_requires_clause_about_another_param_does_not_license` — the
//!     construction passes, and the program is refused a step later by its return type.
//! 29. THE CONSTRUCTION ASKED BEFORE THE EXPECTED TYPE IS READ. 1 FAILS:
//!     [`a_parameter_only_the_expected_type_fixes_is_judged`] (loads).
//!
//! WHAT IS SAID WHERE A REQUIREMENT CANNOT BE SUPPLIED
//!
//! 30. AN OPEN PARAMETER REPORTED AS UNCONSTRAINED (`unconstrained_for_want_of_a_
//!     provision`). 5 FAIL:
//!     [`a_missing_provision_is_named_and_not_the_element_it_would_say`],
//!     [`the_open_parameter_is_found_by_its_variable`], `n01py`, the matrix and `x13yv`.
//!     With a written clause's carrier read as written (its symbol, not its variable),
//!     the first of them alone — its bound half. With the parameter found by its name, or
//!     with a partial requirement pasted after "declare `provides`", the second alone.
//!     With the rows not read (`some_row_could_answer`),
//!     [`a_generic_witness_leaves_the_element_to_the_call`] alone.
//! 31. AN ELEMENT OPEN FOR WANT OF A PROVISION REPORTED AS THE ELEMENT
//!     (`sort_carrier_providing_nothing`). 1 FAILS:
//!     [`a_lazy_carrier_is_not_built_over_a_source_that_cannot_be_walked`], refused naming
//!     the element.
//!
//! THE EXAMPLE — none of the 872; rows of `guardians_test`
//!
//! 32. THE EFFECT LEG SWITCHED OFF BY THE SPEC OPERATION'S OWN ROW PARAMETER
//!     (`OwnTypeParams`). 2 FAIL: `capability_widening_is_refused_by_the_row` and
//!     `a_modify_target_the_spec_never_granted_is_refused_by_the_row`.
//! 33. A DENIED CAPABILITY NOT COVERING ITS PROVIDERS (`permission_entails` without
//!     `spec_as_its_providers`). 1 FAILS:
//!     `a_sub_capability_mint_is_refused_by_the_downward_closed_denial`.
//!
//! THE FACT READER's rows are `typing_test`'s (`spec_field_…`, `parameterized_spec_…`,
//! `conditional_spec_…`), each with its own back-out at its site.
//!
//! PASS UNDER EVERY PART THAT LEAVES THE LIBRARY LOADING, by design:
//! [`the_member_spelling_runs`] and [`the_bound_spelling_runs`], which ran on the parent
//! commit and must still; [`a_list_at_a_stream_parameter_loads_as_before`], the control
//! that the refusal is about specs over a parameter; [`a_constants_body_is_not_reached`],
//! which records a gap; and the two programs of
//! [`what_a_field_fixed_is_asked_for_and_not_held_against_the_clause`] that run, which pin
//! a verdict this change's first cut made and its final one does not.

use crate::common::{
    assert_refused_naming, collect_anthill_files, examples_dir, load_errors_of, run_int64,
    try_load_kb_untyped_with_files,
};
use anthill_core::kb::typing::positions_typed_at_a_spec_over_a_parameter;

// ── the ticket's programs ─────────────────────────────────────────────────────────────

/// The ticket's sorts: `Tag`; `Tagger` over its parameter `C`, which requires `Tag` of it
/// and has one body-less and one defaulted operation; a provider `B`; and `Box`, which
/// requires `Tag` of its own parameter. `body` follows.
fn ticket(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}

  sort Tag
    sort T = ?
    operation tagOf(x: T) -> Int64
  end

  sort Tagger
    sort C = ?
    requires Tag[T = C]
    operation probe(x: C) -> Int64
    operation tagIn(x: C) -> Int64 = Tag.tagOf(x)
  end

  sort B
    entity b(k: Int64)
    provides Tag[T = B]
    operation tagOf(x: B) -> Int64 = 2
    provides Tagger[C = B]
    operation probe(x: B) -> Int64 = 7
  end

  sort Box
    sort T = ?
    requires Tag[T = T]
    operation tagOf(v: T) -> Int64 = Tag.tagOf(v)
  end
{body}
end
"#
    )
}

/// THE TICKET'S FOUR PROGRAMS, each declaration alone: a `w: Tagger` handed to an operation
/// that receives a `Tagger.C` (the body-less `probe`, the defaulted `tagIn`), to another
/// sort's operation over its own parameter (`Box.tagOf`), and the defaulted one again under
/// a `requires` over `w.C`. (1) answered 7 and (2), (3), (4) loaded and died "`__req_tag`
/// not bound in caller frame". Each is refused where the value is passed, naming the
/// parameter's type and the argument's.
#[test]
fn a_spec_typed_value_is_refused_where_the_carrier_is_expected() {
    for (name, decl, param) in [
        (
            "bodyless",
            "operation via(w: Tagger) -> Int64 = Tagger.probe(w)",
            "probe.x (op-arg): expected {ns}.Tagger.C",
        ),
        (
            "defaulted",
            "operation via(w: Tagger) -> Int64 = Tagger.tagIn(w)",
            "tagIn.x (op-arg): expected {ns}.Tagger.C",
        ),
        (
            "other_sort",
            "operation via(w: Tagger) -> Int64 = Box.tagOf(w)",
            "tagOf.v (op-arg): expected {ns}.Box.T",
        ),
        (
            "projected",
            "operation via(w: Tagger) -> Int64 requires Tag[T = w.C] = Tagger.tagIn(w)",
            "tagIn.x (op-arg): expected {ns}.Tagger.C",
        ),
    ] {
        let ns = format!("kssa4.spec_typed.{name}");
        let errs = load_errors_of(&ticket(&ns, &format!("\n  {decl}\n")));
        assert_refused_naming(
            &errs,
            &[
                &param.replace("{ns}", &ns),
                "got Tagger[C = w.C]",
                "a value typed at it is not a value of a sort that provides it",
                &format!("Type the value `{ns}.Tagger.C`"),
            ],
            name,
        );
    }
}

/// THE OTHER DIRECTION: a `B` provides `Tagger`, and is not one. A parameter typed at the
/// spec takes no provider's value, whatever its body does with it — here nothing. Loaded
/// before, the reading every program above started from.
#[test]
fn a_providers_value_is_refused_at_a_parameter_typed_at_the_spec() {
    let ns = "kssa4.provider_at_spec";
    let errs = load_errors_of(&ticket(
        ns,
        "\n  operation takes(w: Tagger) -> Int64 = 0\n  \
         operation go() -> Int64 = takes(b(k: 0))\n",
    ));
    assert_refused_naming(
        &errs,
        &[
            "takes.w (op-arg): expected Tagger, got B",
            &format!("`{ns}.Tagger` is a spec over its parameter `C`"),
            &format!("that does not make the value a `{ns}.Tagger`"),
            &format!("Type this position `{ns}.Tagger.C`"),
        ],
        "a provider's value at a parameter typed at the spec",
    );
}

/// The three consumers at `spelling`, each entered with a `B`.
fn spelled(ns: &str, spelling: &str) -> String {
    ticket(
        ns,
        &format!(
            "{spelling}\n  \
             operation d() -> Int64 = defaulted(b(k: 0))\n  \
             operation o() -> Int64 = otherSort(b(k: 0))\n  \
             operation p() -> Int64 = bodyless(b(k: 0))\n"
        ),
    )
}

/// The defaulted operation and the other sort's answer the provider's `Tag` (2); the
/// body-less one the provider's own `probe` (7).
#[track_caller]
fn assert_answers_2_2_7(ns: &str, spelling: &str) {
    let src = spelled(ns, spelling);
    assert_eq!(run_int64(&src, &format!("{ns}.d")), Ok(2), "the defaulted operation");
    assert_eq!(run_int64(&src, &format!("{ns}.o")), Ok(2), "the other sort's operation");
    assert_eq!(run_int64(&src, &format!("{ns}.p")), Ok(7), "the body-less operation");
}

/// THE MEMBER SPELLING — `w: Tagger.C`, a value of a sort of which `Tagger` is required.
#[test]
fn the_member_spelling_runs() {
    assert_answers_2_2_7(
        "kssa4.member",
        "\n  operation defaulted(w: Tagger.C) -> Int64 = Tagger.tagIn(w)\n  \
         operation otherSort(w: Tagger.C) -> Int64 = Box.tagOf(w)\n  \
         operation bodyless(w: Tagger.C) -> Int64 = Tagger.probe(w)",
    );
}

/// THE BOUND SPELLING — the same requirement written out.
#[test]
fn the_bound_spelling_runs() {
    assert_answers_2_2_7(
        "kssa4.bound",
        "\n  operation defaulted[P](w: P) -> Int64 requires Tagger[C = P] = Tagger.tagIn(w)\n  \
         operation otherSort[P](w: P) -> Int64 requires Tagger[C = P] = Box.tagOf(w)\n  \
         operation bodyless[P](w: P) -> Int64 requires Tagger[C = P] = Tagger.probe(w)",
    );
}

// ── a spec with several parameters: the library's consumer ────────────────────────────

/// `total` at `signature`, counted over a list and over a mapped stream of it; `more`
/// follows.
fn consumer(ns: &str, signature: &str, more: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, List, FiniteCollection, Stream}}
  import anthill.prelude.FiniteCollection.{{size}}

  operation {signature} = size(c)

  operation rows() -> List[T = Int64] = [1, 2, 3, 4]
  operation overList() -> Int64 = total(rows())
  operation overMapped() -> Int64 = total(rows().map(lambda n -> n * 2))
{more}
end
"#
    )
}

const MEMBER_TOTAL: &str = "total(c: FiniteCollection.C) -> Int64 effects FiniteCollection.E";
const BOUND_TOTAL: &str = "total[P, El, R](c: P) -> Int64 effects R \
                           requires FiniteCollection[C = P, Element = El, E = R]";

#[track_caller]
fn assert_counts_four(ns: &str, signature: &str) {
    let src = consumer(ns, signature, "");
    assert_eq!(run_int64(&src, &format!("{ns}.overList")), Ok(4), "over a list");
    assert_eq!(run_int64(&src, &format!("{ns}.overMapped")), Ok(4), "over a mapped stream");
}

/// `size(c)` fixes `FiniteCollection`'s carrier from its argument and nothing else: the
/// element and the effect are the ones the signature's own requirement names, and
/// `FiniteCollection`'s requirement of `Iterable` is supplied through it. Refused before
/// ("expected a type for 'E', got unconstrained").
#[test]
fn total_in_the_member_spelling_counts() {
    assert_counts_four("kssa4.total_member", MEMBER_TOTAL);
}

/// The written bound. Refused before: "`Iterable[C = FiniteCollection.C, …]` cannot be
/// supplied for call to `size`: element `Element = …`, `E = …` is unconstrained".
#[test]
fn total_in_the_bound_spelling_counts() {
    assert_counts_four("kssa4.total_bound", BOUND_TOTAL);
}

/// A BOUND IS PASSED ON: `outer` requires the collection of its own `Q` and calls `total`,
/// which requires it of `P`. The caller's clause is what answers `total`'s.
#[test]
fn a_bound_is_passed_on() {
    let ns = "kssa4.relay";
    let src = consumer(
        ns,
        BOUND_TOTAL,
        "  operation outer[Q, E2, R2](c: Q) -> Int64 effects R2 \
           requires FiniteCollection[C = Q, Element = E2, E = R2] = total(c)\n  \
           operation relayed() -> Int64 = outer(rows())",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.relayed")), Ok(4));
}

/// THE SPELLING THAT LOADED, `total(c: FiniteCollection) -> Int64 effects c.E`: a list is
/// not a `FiniteCollection`, and a `FiniteCollection` is not what `size` receives.
#[test]
fn total_typed_at_the_spec_takes_no_list() {
    let errs = load_errors_of(&consumer(
        "kssa4.total_spec",
        "total(c: FiniteCollection) -> Int64 effects c.E",
        "",
    ));
    assert_refused_naming(
        &errs,
        &[
            "total.c (op-arg): expected FiniteCollection, got List",
            "`anthill.prelude.FiniteCollection` is a spec over its parameter `C`",
            "size.c (op-arg): expected anthill.prelude.FiniteCollection.C, got FiniteCollection",
        ],
        "a list at a parameter typed at the spec, and that parameter at `size`",
    );
}

/// WHAT A CLAUSE IMPLIES IS READ BESIDE ANOTHER CLAUSE OVER THE SAME SPEC. `requires
/// FiniteCollection[C = P, …]` says `P` is iterable too, and `requires Iterable[C = Q, …]`
/// is about `Q`. Read only where no written clause named `Iterable` at all, the second
/// clause hid what the first implies of `P`, and `Iterable.iterator(a)` was refused
/// "cannot project 'Element' off an abstract receiver" — where the one-clause twin loaded.
///
/// FAILS with the implied requirements read only where no clause names the spec
/// (`scope_clause_at_carrier`): the program is refused.
#[test]
fn what_a_clause_implies_is_read_beside_another_clause_over_the_spec() {
    let ns = "kssa4.implied";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, List, FiniteCollection, Iterable, Stream}}

  operation firstIsEmpty[P, El, R, Q, El2, R2](a: P, b: Q) -> Bool effects R
    requires FiniteCollection[C = P, Element = El, E = R]
    requires Iterable[C = Q, Element = El2, E = R2] =
    Stream.isEmpty(Iterable.iterator(a))

  operation rows() -> List[T = Int64] = [1, 2, 3, 4]
  operation nothing() -> List[T = Int64] = []
  operation full() -> Int64 = if firstIsEmpty(rows(), rows()) then 1 else 0
  operation empty() -> Int64 = if firstIsEmpty(nothing(), rows()) then 1 else 0
end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.full")), Ok(0), "a list of four");
    assert_eq!(run_int64(&src, &format!("{ns}.empty")), Ok(1), "an empty list");
}

/// A CARRIER DECLARED SECOND IS THE CARRIER. `Sp3`'s operation receives on `C`, its second
/// parameter, and `requires Sp3[A = X, C = P, B = El]` is read at what the call makes of
/// `P`: `Bar`'s provision says `B`. Read at the spec's first parameter — every reader of a
/// clause once took that for the carrier — the call was asked about `Foo`, the `A`, and
/// refused; the missing-provision diagnostic then said "`Foo` provides no `Sp3`".
///
/// FAILS with the clause's carrier read as the first parameter (`clause_carrier_param`):
/// the program is refused.
#[test]
fn a_carrier_declared_second_is_the_carrier() {
    let ns = "kssa4.carrier_second";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}

  sort Sp3
    sort A = ?
    sort C = ?
    sort B = ?
    operation run(c: C) -> Int64
  end

  sort Foo
    entity foo
  end

  sort Bar
    entity bar
    provides Sp3[A = Foo, C = Bar, B = Int64]
    operation run(c: Bar) -> Int64 = 3
  end

  operation f[X, P, El](x: X, c: P) -> Int64 requires Sp3[A = X, C = P, B = El] = Sp3.run(c)
  operation go() -> Int64 = f(foo(), bar())
end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(3));
}

/// A FOREIGN PARAMETER OF THE SAME NAME IS NOT THE RECEIVER'S. `Seq provides Walk[C = Self,
/// Element = Foreign.Elem]` names another sort's parameter, which says nothing of this
/// `Seq`; `Mapped`'s `Src` is then whatever the expected type writes. Joined by its local
/// name it was read as `Seq`'s own `Elem`, and the construction over a `Seq[Elem = Bool]`
/// was held to an element of `Bool` — where the twin written `Foreign.X` was not.
///
/// FAILS with the occurrence resolved by local name alone (`typaram_ref_vid`): the
/// colliding spelling is refused, the provision's element read as the receiver's own.
#[test]
fn a_foreign_parameter_of_the_same_name_is_not_the_receivers() {
    let ns = "kssa4.foreign_param";
    let program = |foreign: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool}}

  sort Foreign
    sort Elem = ?
    sort X = ?
  end

  sort Walk
    sort C = ?
    sort Element = ?
    operation first(c: C) -> Int64
  end

  sort Seq
    sort Elem = ?
    entity seq(x: Elem)
    provides Walk[C = Self, Element = Foreign.{foreign}]
    operation first(s: Self) -> Int64 = 1
  end

  sort Mapped
    sort Source = ?
    sort Src = ?
    requires Walk[C = Source, Element = Src]
    entity mk(source: Source)
    operation firstOf(m: Self) -> Int64 =
      match m
        case mk(s) -> Walk.first(s)
  end

  operation build() -> Mapped[Source = Seq[Elem = Bool], Src = Int64] = mk(seq(true))
  operation go() -> Int64 = Mapped.firstOf(build())
end
"#
        )
    };
    assert_eq!(run_int64(&program("X"), &format!("{ns}.go")), Ok(1), "another name");
    assert_eq!(run_int64(&program("Elem"), &format!("{ns}.go")), Ok(1), "the same name");
}

// ── a sort that receives on itself ────────────────────────────────────────────────────

/// `Stream` RECEIVES ON ITSELF, so it is its own carrier and a `List` is a `Stream`: the
/// parameter takes a list as it always did. Passes with the change and without it, by
/// design — the control that the refusal is about specs over a parameter.
#[test]
fn a_list_at_a_stream_parameter_loads_as_before() {
    let ns = "kssa4.own_carrier";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, List, Stream}}

  operation firstOr(s: Stream, d: Int64) -> Int64 effects s.E =
    match Stream.isEmpty(s)
      case true -> d
      case false -> 1
  operation count(s: Stream[T = Int64, E = {{}}]) -> Int64 = Stream.takeN(s, 2).size()

  operation rows() -> List[T = Int64] = [1, 2, 3, 4]
  operation first() -> Int64 = firstOr(rows(), 0)
  operation two() -> Int64 = count(rows())
end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.first")), Ok(1));
    assert_eq!(run_int64(&src, &format!("{ns}.two")), Ok(2));
}

// ── the member sugar ──────────────────────────────────────────────────────────────────

/// ONE SIGNATURE'S MEMBERS OF A SPEC ARE OF ONE INSTANCE. `via(w: Tagger.C) -> Tagger.Out`
/// returns the `Out` of the `Tagger` its argument's sort provides, so over a `B` — which
/// provides it at `Out = Int64` — the result is no `String`. Read as two requirements, one
/// per mention, the result was whatever the caller expected, and the program loaded.
#[test]
fn a_signatures_members_are_of_one_instance() {
    let ns = "kssa4.one_instance";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}

  sort Tag
    sort T = ?
    sort K = ?
    operation tagOf(x: T) -> K
  end

  sort Tagger
    sort C = ?
    sort Out = ?
    requires Tag[T = C, K = Out]
    operation tagIn(x: C) -> Out = Tag.tagOf(x)
  end

  sort B
    entity b(k: Int64)
    provides Tag[T = B, K = Int64]
    operation tagOf(x: B) -> Int64 = 2
    provides Tagger[C = B, Out = Int64]
  end

  operation via(w: Tagger.C) -> Tagger.Out = Tagger.tagIn(w)
  operation right() -> Int64 = via(b(k: 0))
{{wrong}}
end
"#
    );
    assert_eq!(
        run_int64(&src.replace("{wrong}", ""), &format!("{ns}.right")),
        Ok(2)
    );
    let errs = load_errors_of(&src.replace(
        "{wrong}",
        "  operation wrong() -> String = via(b(k: 0))",
    ));
    assert_refused_naming(
        &errs,
        &["wrong", "expected String, got Int64"],
        "the member a result is typed by is the argument's instance's",
    );
}

/// A SPEC'S OPERATION OVER ANOTHER SPEC'S MEMBER IS BACKED BY RESTATING IT: `Job.run(self:
/// C, t: Tagger.C) effects {Tagger.E}` and a provider that writes the same signature. The
/// two operations each have their own requirement of `Tagger`; aligned by position, the
/// provider's is the spec's. Refused before as "strengthens the precondition".
#[test]
fn a_spec_operation_over_a_member_is_backed_by_restating_it() {
    let ns = "kssa4.restated";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  import anthill.prelude.Numeric.{{add}}

  sort Tagger
    sort C = ?
    effects E = ?
    operation tag(self: C) -> Int64 effects {{E}}
  end

  sort Job
    sort C = ?
    operation run(self: C, t: Tagger.C) -> Int64 effects {{Tagger.E}}
  end

  sort A
    entity a
    operation tag(self: A) -> Int64 = 7
    provides Tagger[C = A, E = {{}}]
  end

  sort J
    entity j
    operation run(self: J, t: Tagger.C) -> Int64 effects {{Tagger.E}} = add(t.tag(), 1)
    provides Job[C = J]
  end

  operation go(w: Job.C, t: Tagger.C) -> Int64 effects {{Tagger.E}} = w.run(t)
  operation through() -> Int64 = go(j(), a())
  operation direct() -> Int64 = j().run(a())
end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.through")), Ok(8));
    assert_eq!(run_int64(&src, &format!("{ns}.direct")), Ok(8));
}

/// A MEMBER IS NAMED IN THE BODY TOO: `mapElems[EffP = {Tagger.E, Error}]` inside an
/// operation whose signature says `t: Tagger.C` names that signature's `Tagger.E`. Refused
/// before as a name that resolves to nothing.
#[test]
fn a_member_is_named_in_the_body() {
    let ns = "kssa4.body_member";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, List, Error}}
  import anthill.prelude.Numeric.{{add}}
  import anthill.prelude.List.{{mapElems}}

  sort Tagger
    sort C = ?
    effects E = ?
    operation tag(self: C) -> Int64 effects {{E, Error}}
  end

  sort A
    entity a
    operation tag(self: A) -> Int64 effects {{Error}} = 7
    provides Tagger[C = A, E = {{}}]
  end

  operation tagged(t: Tagger.C, xs: List[T = Int64]) -> Int64 effects {{Tagger.E, Error}} =
    match mapElems[EffP = {{Tagger.E, Error}}](xs, lambda x -> add(x, t.tag()))
      case cons(h, rest) -> h
      case nil() -> 0
  operation go() -> Int64 effects {{Error}} = tagged(a(), [1, 2])
end
"#
    )
    .replace(
        "import anthill.prelude.List.{mapElems}",
        "import anthill.prelude.List.{mapElems, cons, nil}",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(8));
}

// ── what is said where a requirement cannot be supplied ───────────────────────────────

/// A SORT THAT PROVIDES NOTHING IS REFUSED BESIDE A WITNESS OVER ANOTHER SORT. `Any provides
/// Cap[C = Wrap[S = S]]` answers at every `Wrap`, and at no `Opaque`. Read as "a row that
/// names parameters is not provably excluded", it kept `sink(opaque(…))` admitted: a clean
/// load, then "`__req_cap` not bound". The control is the same call over a `Wrap`.
#[test]
fn a_sort_that_provides_nothing_is_refused_beside_a_generic_witness() {
    let ns = "kssa4.beside_witness";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}

  sort Cap
    sort C = ?
    sort Element = ?
    operation tag(c: C) -> Int64
  end

  sort Opaque
    entity opaque(v: Int64)
  end

  sort Wrap
    sort S = ?
    entity wrap(inner: S)
  end

  sort Any
    sort S = ?
    provides Cap[C = Wrap[S = S], Element = S]
    operation tag(w: Wrap[S = S]) -> Int64 = 5
  end

  operation sink(c: Cap.C) -> Int64 = Cap.tag(c)
  operation wrapped() -> Int64 = sink(wrap(inner: opaque(v: 7)))
{{bare}}
end
"#
    );
    assert_eq!(
        run_int64(&src.replace("{bare}", ""), &format!("{ns}.wrapped")),
        Ok(5)
    );
    let errs = load_errors_of(&src.replace(
        "{bare}",
        "  operation bare() -> Int64 = sink(opaque(v: 7))",
    ));
    assert_refused_naming(
        &errs,
        &[
            &format!("`{ns}.Cap[C = {ns}.Opaque"),
            &format!("cannot be supplied for call to `{ns}.sink`"),
        ],
        "a sort no provision answers at",
    );
}

/// A MISSING PROVISION IS WHAT IS REPORTED, not the element it would have said. `Nats`
/// provides `Stream` and no `FiniteCollection`; `total(from(1))` leaves `total`'s element
/// and effect open because no provision says them. Reported before as "expected a type for
/// 'E', got unconstrained — use `total[E = …](…)`", a repair that cannot work. The same in
/// both spellings: a written clause names its carrier by symbol and a minted one by its
/// variable, and the first was read as written (this change's first cut — the bound
/// spelling kept the old message).
#[test]
fn a_missing_provision_is_named_and_not_the_element_it_would_say() {
    for (name, signature) in [("member", MEMBER_TOTAL), ("bound", BOUND_TOTAL)] {
        let ns = format!("kssa4.missing_provision.{name}");
        let errs = load_errors_of(&consumer(
            &ns,
            signature,
            "  import anthill.prelude.{Option, Pair}\n  \
             import anthill.prelude.Option.{some}\n  \
             import anthill.prelude.Pair.{pair}\n  \
             sort Nats\n    entity from(n: Int64)\n    \
             provides Stream[T = Int64, E = {}]\n    \
             operation splitFirst(s: Nats) \
             -> Option[Pair[A = Int64, B = Stream[T = Int64, E = {}]]] =\n      \
             match s\n        case from(n) -> some(pair(n, from(n + 1)))\n  end\n  \
             operation endless() -> Int64 = total(from(1))",
        ));
        assert_refused_naming(
            &errs,
            &[
                "`anthill.prelude.FiniteCollection[C = Nats]`",
                &format!("cannot be supplied for call to `{ns}.total`"),
                "no provision of `anthill.prelude.FiniteCollection` answers at `Nats`",
                &format!("`{ns}.Nats` provides no `anthill.prelude.FiniteCollection`"),
            ],
            name,
        );
    }
}

/// A GENERIC WITNESS ANSWERS AT EVERY CARRIER, AND LEAVES THE ELEMENT TO THE CALL. `AnyCap
/// provides Cap[C = S, Element = Int64]` covers an `Opaque` as it covers any sort, so what
/// `sink(opaque(…))` lacks is the element, and writing it loads and answers. The readers
/// keyed on the carrier see no row for `Opaque`: asked alone, they told the author
/// "`Opaque` provides no `Cap` — declare `provides …`" (this change's first cut).
///
/// FAILS with the rows not read (`some_row_could_answer` out of `unconstrained_for_want_
/// of_a_provision`): the bare call is told to declare a provision.
#[test]
fn a_generic_witness_leaves_the_element_to_the_call() {
    let ns = "kssa4.generic_witness";
    let program = |call: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64}}

  sort Cap
    sort C = ?
    sort Element = ?
    operation tag(c: C) -> Int64
  end

  sort Opaque
    entity opaque(v: Int64)
  end

  sort AnyCap
    sort S = ?
    provides Cap[C = S, Element = Int64]
    operation tag(c: S) -> Int64 = 5
  end

  operation sink[P, El](c: P) -> Int64 requires Cap[C = P, Element = El] = Cap.tag(c)
  operation go() -> Int64 = {call}
end
"#
        )
    };
    assert_eq!(
        run_int64(&program("sink[El = Int64](opaque(v: 7))"), &format!("{ns}.go")),
        Ok(5)
    );
    let errs = load_errors_of(&program("sink(opaque(v: 7))"));
    assert_refused_naming(
        &errs,
        &["expected a type for 'El', got unconstrained", "use `sink[El = …](…)`"],
        "the element is what the call has not said",
    );
    assert!(
        !errs.iter().any(|e| e.contains("provides no")),
        "a carrier a generic witness covers is not told to declare a provision: {errs:#?}"
    );
}

/// THE OPEN PARAMETER IS FOUND BY ITS VARIABLE. The member sugar mints one parameter per
/// member, so `both(x: Tagger.C, y: Other.C) effects {Tagger.E, Other.E}` has two called
/// `E`. `Plain` provides no `Other`, and it is `Other`'s `E` that stays open — the refusal
/// names that requirement at `Plain`. Found by name, the first `E` was `Tagger`'s, whose
/// carrier does provide it, and the author was told "expected a type for 'E', got
/// unconstrained — use `both[E = …](…)`".
///
/// FAILS with the parameter looked up by name: that message is what comes back.
#[test]
fn the_open_parameter_is_found_by_its_variable() {
    let ns = "kssa4.two_members";
    let errs = load_errors_of(&format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}

  sort Tagger
    sort C = ?
    effects E = ?
    operation tag(self: C) -> Int64 effects {{E}}
  end

  sort Other
    sort C = ?
    effects E = ?
    operation oth(self: C) -> Int64 effects {{E}}
  end

  sort A
    entity a
    provides Tagger[C = A, E = {{}}]
    operation tag(self: A) -> Int64 = 7
  end

  sort Plain
    entity plain
  end

  operation both(x: Tagger.C, y: Other.C) -> Int64 effects {{Tagger.E, Other.E}} = 1
  operation go() -> Int64 = both(a(), plain())
end
"#
    ));
    assert_refused_naming(
        &errs,
        &[
            &format!("`{ns}.Other[C = Plain]` cannot be supplied for call to `{ns}.both`"),
            &format!("`{ns}.Plain` provides no `{ns}.Other`"),
            &format!("declare a `provides {ns}.Other[…]` for it, each element of `{ns}.Other` written"),
        ],
        "the requirement whose member is open",
    );
}

// ── a construction owes its sort's requirement ────────────────────────────────────────

/// A sort whose values are built over any provider of `Shown`: the field is typed by the
/// sort's own parameter and the clause says what is required of it — and `vacant` has no
/// field, so only an expected type says which `Hold` it is. `Leaf` provides `Shown` and
/// `Other` does not. `body` follows.
fn holder(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}

  sort Shown
    sort T = ?
    operation show(x: T) -> Int64
  end

  sort Leaf
    entity leaf
    provides Shown[T = Leaf]
    operation show(x: Leaf) -> Int64 = 7
  end

  sort Other
    entity other
  end

  sort Hold
    sort E = ?
    requires Shown[T = E]
    entity hold(inner: E)
    entity vacant
    operation read(h: Self) -> Int64 =
      match h
        case hold(i) -> Shown.show(i)
        case vacant() -> 0
  end
{body}
end
"#
    )
}

/// The refusal of a `hold` built over `over`.
#[track_caller]
fn assert_no_hold_over(errs: &[String], ns: &str, over: &str, why: &str) {
    assert_refused_naming(
        errs,
        &[
            &format!("`{ns}.Shown[T = {over}]` of `{ns}.Hold`"),
            &format!("cannot be supplied for the construction `{ns}.Hold.hold`"),
        ],
        why,
    );
}

/// THE VALUE IS BUILT WHERE THE REQUIREMENT HOLDS. Over a `Leaf` it is, and the operation
/// that reads the requirement answers; over an `Other` nothing can supply it, and the
/// construction is refused where it is written — unused, as here, or not. Loaded before.
#[test]
fn a_construction_over_a_non_provider_is_refused_where_it_is_built() {
    let ns = "kssa4.built";
    let good = holder(ns, "  operation go() -> Int64 = Hold.read(hold(leaf()))");
    assert_eq!(run_int64(&good, &format!("{ns}.go")), Ok(7));
    let errs = load_errors_of(&holder(
        ns,
        "  operation go() -> Int64 =\n    let h = hold(other())\n    0",
    ));
    assert_no_hold_over(&errs, ns, &format!("{ns}.Other"), "a construction nothing uses");
    assert_refused_naming(
        &errs,
        &[
            &format!("`{ns}.Other` provides no `{ns}.Shown`"),
            "or build the value over a sort that provides it",
        ],
        "the repair is the provision, or another sort",
    );
}

/// OVER A PARAMETER OF THE SCOPE the requirement is the scope's to hold: `keep[P](p: P)
/// requires Shown[T = P] = hold(p)` builds, and reads 7 over a `Leaf`; with no clause the
/// same construction is refused — nothing says a `P` is shown, and no provision answers at
/// a parameter. Loaded before, on a `P` the callers could put anything in.
#[test]
fn a_construction_over_a_parameter_needs_the_scopes_requirement() {
    let ns = "kssa4.over_param";
    let licensed = holder(
        ns,
        "  operation keep[P](p: P) -> Int64 requires Shown[T = P] = Hold.read(hold(p))\n  \
         operation go() -> Int64 = keep(leaf())",
    );
    assert_eq!(run_int64(&licensed, &format!("{ns}.go")), Ok(7));
    let errs = load_errors_of(&holder(
        ns,
        "  operation keep[P](p: P) -> Int64 =\n    let h = hold(p)\n    0",
    ));
    assert_no_hold_over(
        &errs,
        ns,
        &format!("{ns}.Hold.E"),
        "a construction over a parameter nothing is required of",
    );
}

/// THE INSTANCE IS WHAT THE EXPECTED TYPE SAYS TOO. `vacant()` has no field, so its `E` is
/// whatever the position it stands in expects: at a return type of `Hold[E = Leaf]` it is
/// built, and at `Hold[E = Other]` refused. Asked before the expectation is read, `E` is
/// open, a provision could still answer it, and the second loads.
#[test]
fn a_parameter_only_the_expected_type_fixes_is_judged() {
    let ns = "kssa4.expected";
    let good = holder(
        ns,
        "  operation mk() -> Hold[E = Leaf] = vacant()\n  \
         operation go() -> Int64 = Hold.read(mk())",
    );
    assert_eq!(run_int64(&good, &format!("{ns}.go")), Ok(0));
    let errs = load_errors_of(&holder(
        ns,
        "  operation mk() -> Hold[E = Other] = vacant()",
    ));
    assert_refused_naming(
        &errs,
        &[
            &format!("`{ns}.Shown[T = {ns}.Other]` of `{ns}.Hold`"),
            &format!("cannot be supplied for the construction `{ns}.Hold.vacant`"),
        ],
        "a parameter the return type writes at a sort that provides nothing",
    );
}

/// THE STANDARD LIBRARY'S LAZY CARRIER, whose field is its own `Source`. `mapped(5, f)` is
/// refused over an `Int64`, with every parameter left to inference and with every one
/// written by the return type — the second loaded, was admitted at `s: Stream`, and died
/// "`__req_iterable` not bound in caller frame (running `MappedStream.splitFirst`)". Over a
/// list the same construction is a stream of two.
#[test]
fn a_lazy_carrier_is_not_built_over_a_source_that_cannot_be_walked() {
    let ns = "kssa4.lazy";
    let program = |body: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, List, MappedStream, Stream}}
  import anthill.prelude.MappedStream.{{mapped}}
{body}
end
"#
        )
    };
    let over_list = program(
        "  operation go() -> Int64 =\n    \
         let m = mapped([1, 2, 3], lambda (x: Int64) -> x + 1)\n    \
         Stream.takeN(m, 2).size()",
    );
    assert_eq!(run_int64(&over_list, &format!("{ns}.go")), Ok(2));
    let refused = [
        "cannot be supplied for the construction `anthill.prelude.MappedStream.mapped`",
        "`anthill.prelude.Int64` provides no `anthill.prelude.Iterable`",
    ];
    let inferred = load_errors_of(&program(
        "  operation go() -> Int64 =\n    let m = mapped(5, lambda (x: Int64) -> x)\n    0",
    ));
    assert_refused_naming(&inferred, &refused, "every parameter left to inference");
    let written = load_errors_of(&program(
        "  operation mk() -> MappedStream[Source = Int64, SourceElement = Int64, T = Int64, \
         SourceEffects = {}, TransformEffects = {}] =\n    \
         mapped(5, lambda (x: Int64) -> x)\n  \
         operation go() -> Int64 = Stream.takeN(mk(), 2).size()",
    ));
    assert_refused_naming(&written, &refused, "every parameter written by the return type");
}

/// `wi_wbhtm_value_in_type_call_test`'s fixture — `Buf[T, N]`, whose `N` is in no value,
/// and `Store` provided at `N = 3` and at `N = 4` — with `User`, built over a state `Store`
/// is required of. `body` follows.
fn slotted(ns: &str, body: &str) -> String {
    use crate::wi_wbhtm_value_in_type_call_test::{by_value, program};
    let user = "
  sort User
    sort S = ?
    requires Store[State = S]
    entity user(s: S)
    operation via(u: Self) -> Int64 =
      match u
        case user(s) -> Store.peek(s)
  end
";
    program(ns, &format!("{}{user}{body}", by_value()))
}

/// A SLOT THE CONSTRUCTION LEAVES OPEN IS LEFT TO THE CALL THAT FIXES IT. `user(buf(v: 1))`
/// is typed before the parameter it is passed to says `N`, and two providers could answer;
/// the call fixes `N` and supplies the requirement there. Asked as a call is asked, the
/// construction was refused as a tie (this change's first cut).
#[test]
fn a_slot_the_construction_leaves_open_is_left_to_the_call() {
    let ns = "kssa4.open_slot";
    let src = slotted(
        ns,
        "  operation run3(u: User[S = Buf[T = Int64, N = 3]]) -> Int64 = User.via(u)\n  \
         operation run4(u: User[S = Buf[T = Int64, N = 4]]) -> Int64 = User.via(u)\n  \
         operation three() -> Int64 = run3(user(buf(v: 1)))\n  \
         operation four() -> Int64 = run4(user(buf(v: 1)))",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.three")), Ok(31));
    assert_eq!(run_int64(&src, &format!("{ns}.four")), Ok(41));
}

/// …AND A REQUIREMENT THE CONSTRUCTION FIXES IN FULL IS JUDGED AS ASKED. Over a `b: Buf[T =
/// Int64, N = 5]` nothing is open, no provider is at `N = 5`, and no later use can say
/// otherwise: the search has asked the whole question and its answer stands. FAILS with a
/// construction owing nothing (part 22).
#[test]
fn a_requirement_fixed_in_full_is_judged_as_asked() {
    let ns = "kssa4.fixed";
    let errs = load_errors_of(&slotted(
        ns,
        "  operation go() -> Int64 =\n    \
         let b: Buf[T = Int64, N = 5] = buf(v: 1)\n    \
         let u = user(b)\n    0",
    ));
    assert_refused_naming(
        &errs,
        &[
            &format!("`{ns}.Store[State = {ns}.Buf[T = anthill.prelude.Int64, N = 5]]`"),
            &format!("cannot be supplied for the construction `{ns}.User.user`"),
        ],
        "a state no provider is at",
    );
}

/// A SPEC'S DEFAULT BODY BUILDS OVER ITS OWN INSTANCE. `Coll.wrap(c: C) = hold(c)` under
/// `Holder requires Coll[C = X, E = XE]`: at the body's own carrier the instance is the one
/// the body runs at, so `XE` is `Coll`'s own `E` and the requirement is the frame's. Refused
/// by this change's first cut ("element `E = Holder.XE` is unconstrained at this
/// construction") — no clause says a spec's own instance, since a sort does not require
/// itself.
#[test]
fn a_specs_default_body_builds_over_its_own_instance() {
    let ns = "kssa4.own_instance";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}

  sort Coll
    sort C = ?
    effects E = ?
    operation size(c: C) -> Int64 effects E
    operation wrap(c: C) -> Int64 =
      let h = hold(c)
      1
  end

  sort Holder
    sort X = ?
    effects XE = ?
    requires Coll[C = X, E = XE]
    entity hold(x: X)
  end

  sort L
    entity l(n: Int64)
    provides Coll[C = L, E = {{}}]
    operation size(c: L) -> Int64 = c.n
  end

  operation go() -> Int64 = Coll.wrap(l(n: 3))
end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(1));
}

/// A REQUIREMENT AT OTHER ARGUMENTS OF THE SORT IS REFUSED, whatever it leaves open. The one
/// provider of `Shown2` is at `Buf[T = Int64, N = 3]` and leaves the spec's other element
/// to a parameter of its own, so a `hold` over that `Buf` has an element nothing says yet
/// and is built — the use that fixes it supplies the requirement. Over a `Buf[T = String,
/// N = 3]` the same element is open and no provider is at any such `Buf`: nothing a later
/// use says could make one answer. Compared by head, as dispatch's coarse match compares a
/// ground binding, the provider at `Buf` "could answer" and that construction loaded.
///
/// THE SAME WITH NOTHING OPEN is the search's own verdict: `user(buf(v: "s"))` over
/// `Store` provided at `Buf[T = Int64, …]` alone.
///
/// FAILS with two instances of one sort compared by head (`row_binding_could_answer`): the
/// `hold` over the `Buf` of `String` loads. The `user` half fails with a construction
/// owing nothing (part 22).
#[test]
fn a_requirement_at_other_arguments_of_the_sort_is_refused() {
    let ns = "kssa4.other_arguments";
    let open = |body: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end

  sort Shown2
    sort T = ?
    sort Extra = ?
    operation show(x: T) -> Int64
  end

  sort C3
    sort K = ?
    provides Shown2[T = Buf[T = Int64, N = 3], Extra = K]
    operation show(x: Buf[T = Int64, N = 3]) -> Int64 = 3
  end

  sort Hold2
    sort E = ?
    sort X = ?
    requires Shown2[T = E, Extra = X]
    entity hold(inner: E)
  end

  operation ints() -> Buf[T = Int64, N = 3] = buf(v: 1)
  operation strs() -> Buf[T = String, N = 3] = buf(v: "s")
{body}
end
"#
        )
    };
    let built = open("  operation go() -> Int64 =\n    let h = hold(ints())\n    1");
    assert_eq!(run_int64(&built, &format!("{ns}.go")), Ok(1));
    let errs = load_errors_of(&open(
        "  operation go() -> Int64 =\n    let h = hold(strs())\n    0",
    ));
    assert_refused_naming(
        &errs,
        &[
            &format!("`{ns}.Shown2[T = {ns}.Buf[T = anthill.prelude.String, N = 3], Extra ="),
            &format!("cannot be supplied for the construction `{ns}.Hold2.hold`"),
        ],
        "an instance no provider could be at, whatever its open element",
    );
    let errs = load_errors_of(&slotted(
        ns,
        "  operation go() -> Int64 =\n    let u = user(buf(v: \"s\"))\n    0",
    ));
    assert_refused_naming(
        &errs,
        &[
            &format!("`{ns}.Store[State = {ns}.Buf[T = anthill.prelude.String,"),
            &format!("cannot be supplied for the construction `{ns}.User.user`"),
        ],
        "a state no provider is at",
    );
}

/// A TIE IS LEFT TO THE USE THAT SELECTS. Two providers that both answer are two
/// dictionaries a use may be handed, and a construction selects neither: `acc(seed: 3)`
/// is built with `AddM` and `MulM` both providing `Monoid[T = Int64]`, and the call that
/// names one runs; `single("zz")` is built where its type's named slot says which. Both
/// ran before a construction owed anything, and the first cut refused both, "ambiguous
/// among providers".
///
/// FAILS with a tie taken as the search's verdict at a construction: the program is
/// refused where the values are built.
#[test]
fn a_tie_is_left_to_the_use_that_selects() {
    let ns = "kssa4.tie";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}

  sort Monoid
    sort T = ?
    operation unit() -> T
    operation join(a: T, b: T) -> T
  end

  sort AddM
    provides Monoid[T = Int64]
    operation unit() -> Int64 = 0
    operation join(a: Int64, b: Int64) -> Int64 = a + b
  end

  sort MulM
    provides Monoid[T = Int64]
    operation unit() -> Int64 = 1
    operation join(a: Int64, b: Int64) -> Int64 = a * b
  end

  sort Folder
    sort FT = ?
    requires Monoid[T = FT]
    entity acc(seed: FT)
    operation twice(f: Self) -> FT =
      match f
        case acc(s) -> Monoid.join(s, s)
  end

  sort Ranked
    sort T = ?
    operation rank(x: T) -> Int64
  end

  sort ByLength
    provides Ranked[T = String]
    operation rank(x: String) -> Int64 = 1
  end

  sort Alphabetical
    provides Ranked[T = String]
    operation rank(x: String) -> Int64 = 2
  end

  sort MySet
    sort T = ?
    requires O: Ranked[T]
    entity single(elem: T)
    operation rankOf(s: Self) -> Int64 =
      match s
        case single(e) -> Ranked.rank(e)
  end

  operation added() -> Int64 = Folder.twice[Monoid = AddM](acc(seed: 3))
  operation multiplied() -> Int64 = Folder.twice[Monoid = MulM](acc(seed: 3))
  operation seed() -> MySet[T = String, O = Alphabetical] = single("zz")
  operation ranked() -> Int64 = MySet.rankOf(seed())
end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.added")), Ok(6));
    assert_eq!(run_int64(&src, &format!("{ns}.multiplied")), Ok(9));
    assert_eq!(run_int64(&src, &format!("{ns}.ranked")), Ok(2));
}

/// `Bag` and `Res` provide `Walk` at their own element, and `Seeded` / `Mapped` are built
/// over a source `Walk` is required of — one with a field typed by the element, one with a
/// callback over it. `body` follows.
fn walked(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Option}}
  import anthill.prelude.Option.{{some, none}}

  sort Walk
    sort C = ?
    sort Element = ?
    operation first(c: C) -> Int64
  end

  sort Bag
    sort T = ?
    entity bag(x: T)
    provides Walk[C = Self, Element = T]
    operation first(b: Self) -> Int64 = 41
  end

  sort Res
    sort E = ?
    sort T = ?
    entity ok(v: T)
    entity err(e: E)
    provides Walk[C = Self, Element = T]
    operation first(r: Self) -> Int64 = 9
  end

  sort Seeded
    sort Src = ?
    sort El = ?
    requires Walk[C = Src, Element = El]
    entity seeded(source: Src, seed: El)
    operation firstOf(s: Self) -> Int64 =
      match s
        case seeded(src, _) -> Walk.first(src) + 1
  end

  sort Mapped
    sort Source = ?
    sort Src = ?
    requires Walk[C = Source, Element = Src]
    entity mk(source: Source, fn: (Src) -> Int64)
    operation firstOf(m: Self) -> Int64 =
      match m
        case mk(s, _) -> Walk.first(s)
  end
{body}
end
"#
    )
}

/// WHAT A FIELD FIXED IS ASKED FOR, AND NOT HELD AGAINST THE CLAUSE. `seed: none` fixes
/// `El` at an `Option` of nothing yet, where the source's provision says `Option[T =
/// Int64]`; `err("x")` leaves the source's `T` open, where the callback takes an `Int64`.
/// Each value conforms, and each construction is built and read. The first cut compared
/// what the field fixed with what the clause says by identity of the two types, and
/// refused both — naming a field the entity does not have.
///
/// THE CONTROL is a callback over an element the source does not walk: the requirement at
/// that instance has no provision, and that is what refuses it.
///
/// PASSES under every part of this change, by design: it pins a verdict the change no
/// longer makes. The control FAILS with a construction owing nothing (part 22), and loads
/// with a requirement fixed in full left to the row census (part 25).
#[test]
fn what_a_field_fixed_is_asked_for_and_not_held_against_the_clause() {
    let ns = "kssa4.field_fixed";
    let src = walked(
        ns,
        "  operation opts() -> Bag[T = Option[T = Int64]] = bag(some(1))\n  \
         operation seededOne() -> Int64 = Seeded.firstOf(seeded(source: opts(), seed: none))\n  \
         operation mappedOne() -> Int64 =\n    \
         Mapped.firstOf(mk(source: err(\"x\"), fn: lambda (n: Int64) -> n))",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.seededOne")), Ok(42));
    assert_eq!(run_int64(&src, &format!("{ns}.mappedOne")), Ok(9));
    let errs = load_errors_of(&walked(
        ns,
        "  operation go() -> Int64 =\n    \
         let m = mk(source: bag(1), fn: lambda (s: String) -> 0)\n    0",
    ));
    assert_refused_naming(
        &errs,
        &[
            &format!(
                "`{ns}.Walk[C = {ns}.Bag[T = anthill.prelude.Int64], Element = \
                 anthill.prelude.String]` of `{ns}.Mapped`"
            ),
            &format!("cannot be supplied for the construction `{ns}.Mapped.mk`"),
            &format!("`{ns}.Bag` does provide `{ns}.Walk`, but no row of it answers"),
        ],
        "a callback over an element the source does not walk",
    );
}

/// A CONSTANT'S BODY IS NOT REACHED — a gap, recorded so that closing it is noticed. A
/// constant is folded to a value and typed as one, by a reader with no refusal to give, so
/// the `Hold` over an `Other` that an operation body may not build is built here. The same
/// on the parent commit. When a constant's body is typed as an operation's is, this row
/// becomes the refusal [`a_construction_over_a_non_provider_is_refused_where_it_is_built`]
/// asserts.
#[test]
fn a_constants_body_is_not_reached() {
    let ns = "kssa4.constant";
    let errs = load_errors_of(&holder(
        ns,
        "  const bad: Hold[E = Other] = hold(other())\n  operation go() -> Int64 = 0",
    ));
    assert!(
        errs.is_empty(),
        "THE GAP HAS CLOSED, or moved — a constant built over a sort that provides nothing \
         is now refused. If the refusal is the construction's, assert it here and delete \
         this row's account of the gap: {errs:#?}"
    );
}

// ── the census ────────────────────────────────────────────────────────────────────────

/// The positions `sources` type at a spec over a parameter, read off their declarations —
/// loaded with the standard library and without the typer, so a fixture the typer refuses
/// on purpose is counted like any other. `Err` where the LOADER refuses them: there are
/// then no declarations to read.
fn try_census(sources: &[String]) -> Result<Vec<String>, Vec<String>> {
    let refs: Vec<&str> = sources.iter().map(String::as_str).collect();
    try_load_kb_untyped_with_files(&refs).map(|mut kb| positions_typed_at_a_spec_over_a_parameter(&mut kb))
}

#[track_caller]
fn census(what: &str, sources: &[String]) -> Vec<String> {
    try_census(sources).unwrap_or_else(|errs| panic!("{what} must load to be counted: {errs:#?}"))
}

fn sources_under(dir: &std::path::Path) -> Vec<String> {
    collect_anthill_files(dir)
        .iter()
        .map(|p| std::fs::read_to_string(p).unwrap_or_else(|e| panic!("{}: {e}", p.display())))
        .collect()
}

/// THE READER READS: a parameter and a field typed at `Tagger`, one at the top and one
/// inside a `List`, are each counted, and a parameter typed `Tagger.C` is not. Without this
/// the census below would pass on a reader that finds nothing.
#[test]
fn the_census_counts_a_parameter_and_a_field() {
    let ns = "kssa4.census";
    let found = census(
        "the fixture",
        &[ticket(
            ns,
            "\n  import anthill.prelude.{List}\n  \
             operation at(w: Tagger) -> Int64 = 0\n  \
             operation member(w: Tagger.C) -> Int64 = 0\n  \
             sort Kept\n    entity kept(all: List[T = Tagger])\n  end\n",
        )],
    );
    assert_eq!(
        found,
        vec![
            format!("{ns}.Kept.kept.all: {ns}.Tagger"),
            format!("{ns}.at.w: {ns}.Tagger"),
        ]
    );
}

/// NO SIGNATURE OF THE STANDARD LIBRARY OR OF AN EXAMPLE TYPES A PARAMETER OR A FIELD AT A
/// SPEC OVER ITS PARAMETER — the ticket's acceptance, counted. Each example is read with
/// the library; the guardians agents are read one at a time over their own library, the
/// refused ones included, since each is a program of its own.
#[test]
fn the_library_and_the_examples_type_no_position_at_a_spec() {
    assert_eq!(census("the standard library", &[]), Vec::<String>::new());
    let examples = examples_dir();
    for example in ["classic-mini", "github-todo", "sql-store", "webots-modelling"] {
        let dir = examples.join(example);
        let mut sets: Vec<(String, Vec<String>)> = Vec::new();
        if example == "classic-mini" {
            // One program per directory.
            for entry in std::fs::read_dir(&dir).expect("classic-mini") {
                let sub = entry.expect("entry").path();
                if sub.is_dir() {
                    sets.push((sub.display().to_string(), sources_under(&sub)));
                }
            }
        } else {
            sets.push((example.to_string(), sources_under(&dir)));
        }
        assert!(!sets.is_empty(), "{example}: nothing to count");
        for (what, sources) in sets {
            assert!(!sources.is_empty(), "{what}: no sources");
            assert_eq!(census(&what, &sources), Vec::<String>::new(), "{what}");
        }
    }
    let guardians = examples.join("guardians");
    let lib = sources_under(&guardians.join("lib"));
    assert!(!lib.is_empty(), "guardians: no library");
    assert_eq!(census("guardians/lib", &lib), Vec::<String>::new());
    let agents = collect_anthill_files(&guardians.join("fixtures"));
    assert!(agents.len() >= 20, "guardians: {} fixtures", agents.len());
    // A fixture the LOADER refuses has no declarations to read — four do, each forging or
    // relabelling an entity internal to the library, which is what it is a fixture of. They
    // are named here with the refusal each is a fixture of, and read as text below: the
    // list is the whole of what the reader above does not count, and a fixture the loader
    // refuses for another reason is not on it.
    let mut unread: Vec<(String, String, Vec<String>)> = Vec::new();
    for agent in agents {
        let text = std::fs::read_to_string(&agent).expect("fixture");
        let mut sources = lib.clone();
        sources.push(text.clone());
        let name = agent.file_name().expect("name").to_string_lossy().into_owned();
        match try_census(&sources) {
            Ok(found) => assert_eq!(found, Vec::<String>::new(), "{name}"),
            Err(errs) => unread.push((name, text, errs)),
        }
    }
    unread.sort();
    let refused_for = [
        ("forged_llm.anthill", "'fake_llm' is internal to 'guardians.FakeLlm'"),
        ("forged_source.anthill", "'source' is internal to 'guardians.Source'"),
        ("match_relabel.anthill", "'text' is internal to 'guardians.Text'"),
        ("relabel.anthill", "'text' is internal to 'guardians.Text'"),
    ];
    assert_eq!(
        unread.iter().map(|(n, _, _)| n.as_str()).collect::<Vec<_>>(),
        refused_for.map(|(name, _)| name),
        "fixtures the loader refuses",
    );
    for ((name, _, errs), (_, why)) in unread.iter().zip(refused_for) {
        assert!(
            matches!(errs.as_slice(), [only] if only.contains(why)),
            "{name} is refused for the forgery it is a fixture of, and nothing else: {errs:#?}"
        );
    }
    // The library's specs over a parameter, by name: a position typed `: Llm` and not
    // `: Llm.C` is the spelling the census counts.
    for (name, text, _) in &unread {
        for spec in ["Llm", "Harness", "Checker", "Triage"] {
            let typed_at = format!(": {spec}");
            for (at, _) in text.match_indices(&typed_at) {
                let next = text[at + typed_at.len()..].chars().next();
                assert!(
                    next.is_some_and(|c| c == '.' || c.is_alphanumeric() || c == '_'),
                    "{name}: a position typed at `{spec}` itself",
                );
            }
        }
    }
}
