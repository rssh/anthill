//! WI-20260925-0RRQP — a rule's variable is typed through a constructor, so a condition of
//! the clause witnessed by it is met from the citing operation's own `requires`.
//!
//! `rule order(?p, ?c) :- ?p <=> box(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)`, written in
//! `sort Box` which `requires O: WeakOrd[T]`, calls `compare` at a carrier not known at load,
//! so the call's requirement is a condition of the clause (WI-20260925-P7VP4). A citation
//! fills a condition from the types it gives the clause's columns — and `?x` is no column.
//! The clause's typing said nothing of `?x` that a citation could read: `?p` was the bare
//! `T` of `<=>`, and `?x` a variable of its own. So `Box.orderOf[T = Int64, O = Descending]`
//! answered `Int64`'s own `-1` where the member operation beside it answered `4`.
//!
//! Three things make the tie, and each is backed out below:
//!
//!   * THE CONSTRUCTOR'S SORT REACHES THE POSITION IT FILLS (`constrain_constructed`): an
//!     application of `box` is a `Box[T = t]` over fields typed `t`, and that type is unified
//!     with the declared type of the position — here the `T` of `<=>`, which `?p` shares.
//!   * THE COLLECTED TYPES ARE RESOLVED TO THE END (`collect_rule_var_types`): `?p`'s
//!     `Box[T = t]` and `?x`'s type are one variable only once `t`'s own later binding is
//!     followed.
//!   * THE CITATION READS THE CLAUSE'S OWN TYPING for a witness that is no column
//!     (`ClauseTypes`): `?x`'s stamped type, with the clause's variables bound by what the
//!     citation gives `?p`.
//!
//! And two that the first one needs, since it types columns that had no type:
//!
//!   * A CONSTRUCTOR WITH NO FIELD is written as its name and is of its sort the same way
//!     (`constrain_constant_constructor`).
//!   * TWO CLAUSES' TYPES FOR ONE COLUMN MEET THROUGH THE VARIABLES EACH LEFT IN ITS OWN
//!     (`join_column_types`): two clauses that take one parametric sort apart were refused
//!     at a citation, "disjoint types for column".
//!
//! ## Back-out
//!
//! Each mechanism mutated to a no-op in place under a switch of its own, and every row of
//! this file run under every switch, with the three older rows named below (measured
//! 2026-10-13):
//!
//! | backed out | fails |
//! |---|---|
//! | the constructor's sort unified with its position (`constrain_constructed`) | the eleven routed rows, and `a_column_typed_by_a_constructor_is_checked_at_its_citation`, `a_variable_the_citation_leaves_unfixed_is_an_unknown` (re-measured 2026-10-21, at its `wrap(?y)` and `none` spellings respectively), `a_constructor_in_a_head_field_types_its_variables`, `a_dot_on_a_variable_typed_through_a_constructor_is_the_call`, `a_call_at_a_variable_the_clause_types_is_decided_at_load` |
//! | that unification made in place, not on a copy | `a_constructor_that_does_not_fit_its_position_pins_nothing` (since WI-20261013-WF14Z's fourth part `a_constructor_that_does_not_fit_its_position_is_refused`, the program refused; not measured again) |
//! | a constant constructor read as its sort (`constrain_constant_constructor`) | `a_column_typed_by_a_constructor_is_checked_at_its_citation`, `a_variable_the_citation_leaves_unfixed_is_an_unknown`, `a_constructor_in_a_head_field_types_its_variables`, and `wi_5g28a_paren_less_citation_test::a_bracketed_chain_followed_by_a_projection_is_a_citation` |
//! | the resolve to the end, made one step (`collect_rule_var_types`) | the eleven routed rows, `a_column_typed_by_a_constructor_is_checked_at_its_citation`, and the paren-less row above |
//! | the citation's reading of the clause's typing (`ClauseTypes`) | the eleven routed rows |
//! | the skip of a column the citation has no type for (`ClauseTypes::at_citation`) | `a_column_the_citation_gives_no_type_pins_nothing` |
//! | the meeting of two clauses' types (`join_column_types`, after `join_types`) | `a_typed_clause_meets_one_bound_at_the_sorts_parameter`, `each_clause_of_a_relation_is_met_on_its_own`, `two_clauses_that_take_a_sort_apart_are_one_relation` |
//! | the position handed to a head term's arguments (`collect_term_type_constraints`) | `a_constructor_in_a_head_field_types_its_variables` |
//! | a head term's constant read as its sort (the same function's `Term::Ref` arm) | `a_constructor_in_a_head_field_types_its_variables`, by its second half |
//! | the test that each parameter of the sort has a variable (`constrain_constructed`) | `wi1000_secondary_entry_content_test::a_dotted_declaration_name_is_not_the_entrys_content` and `wi_2kv4y_unfixed_carrier_test::a_sort_the_loader_has_refused_is_not_opened`, each by a panic |
//! | a citation's unfixed clause variable opened as an unknown (`close_unfixed_clause_vars`; measured 2026-10-21) | `a_variable_the_citation_leaves_unfixed_is_an_unknown` (its three spellings with a bound's written variable or unwritten slot, which load; the other four are refused either way, at the first call that reads the citation), `the_citation_whole_is_refused_at_a_written_instance` |
//! | the clause's inferred column type installed as its bound (`install_inferred_column_bounds`; measured 2026-10-21, each below alone over this file, `wi_5g28a_rule_dictionary_test` and `wi_x9pb4_require_dictionary_element_test`) | `an_inferred_column_is_checked_as_a_written_one`, `a_value_whose_element_nothing_fixes_answers_conditionally`, `a_free_part_at_a_fixed_instance_is_filled_from_its_domain` |
//! | a written bound unified with its variable's inferred type at a citation (`unified_column_types` in `relation_clause_columns`) | `an_inferred_column_is_checked_as_a_written_one`, by `p2` |
//! | a sort's parameter the body would fix read as before (`unified_column_types`' `return None`) | `a_body_that_fixes_a_sorts_parameter_is_read_as_before`, by `Box3` (since WF14Z's fourth part the clause is refused, `a_body_that_fixes_a_sorts_parameter_is_refused`) |
//! | the same for a parameter written by its name (`collect_param_refs`) | `a_body_that_fixes_a_sorts_parameter_is_read_as_before`, by `Outer.Inner` (likewise) |
//! | a written variable kept as the representative of the body's (`unified_column_types`' `back`) | `a_variable_the_citation_leaves_unfixed_is_an_unknown`, by its refusal naming `?t` |
//! | only a data sort's type installed (`sort_has_constructors`) | `a_variable_passed_to_a_spec_operation_gets_no_bound`, `wi_x9pb4_require_dictionary_element_test::a_self_representing_spec_receives_its_dictionary_too` |
//! | an inferred type keyed as a written one (`with_written_binding_keys`) | `a_column_the_citation_gives_no_type_pins_nothing`, `a_rule_of_an_earlier_load_is_read_by_a_later_one`, each by the later load's refusal "expands only now" |
//!
//! THE ELEVEN ROUTED ROWS: `a_clause_typed_through_a_constructor_reads_its_sorts_requires`,
//! `a_typed_clause_meets_one_bound_at_the_sorts_parameter`,
//! `a_head_bound_beside_the_constructor_reads_the_same`,
//! `the_tie_is_the_constructors_outside_any_sort`,
//! `the_constructor_ties_on_either_side_and_at_any_depth`,
//! `each_clause_of_a_relation_is_met_on_its_own`,
//! `two_citations_in_one_body_are_two_readings`,
//! `an_operations_own_requires_reached_through_a_constructor_is_filled`,
//! `a_rule_of_an_earlier_load_is_read_by_a_later_one`,
//! `a_column_the_citation_gives_no_type_pins_nothing` and
//! `a_citation_outside_the_sort_reads_the_slot_its_argument_carries`.
//!
//! PASS EITHER WAY, BY DESIGN: `a_member_operation_and_an_uncited_clause_answer_as_before`,
//! `where_an_argument_fixes_it_the_other_instances_are_dropped`,
//! `a_bound_at_the_callers_parameter_is_checked_through_its_domain_only`,
//! and the stated limits at
//! the end of the file. Each says why at its site.
//!
//! WI-20261013-WF14Z's rows here, where a rule goal now types its arguments by the callee's
//! columns: `a_column_a_rule_goal_types_is_read_at_its_type` (the stated limit that was
//! `a_column_nothing_types_is_read_at_any_type`) and
//! `a_rule_goal_fixes_what_the_citation_leaves_unfixed` (two spellings that were rows of
//! `a_variable_the_citation_leaves_unfixed_is_an_unknown`).
//!
//! ## The second row
//!
//! A SORT WITH TWO REQUIREMENTS ON ONE SORT, each clause's condition reaching its own, was
//! a stated limit here until WI-20261013-0K8WD: a call could not name a provider for each,
//! so no caller could show which requirement a condition reached.
//! [`each_clause_reaches_its_own_of_two_requirements_on_one_sort`] drives it. Measured
//! with that ticket's key backed out (a selection kept by the required sort alone), it
//! fails by the call's refusal, "two providers are selected".
//!
//! ## A slot the argument's type says
//!
//! A stated limit here until WI-20261013-WF14Z's fifth part: cited with an argument whose
//! own type says a named slot (`mk() -> Box[T = Int64, O = Ascending]`), from an operation
//! that holds no requirement, the clause's read derived `Int64`'s own. It is read off the
//! argument now, as a call reads it (`carried_slot_selection`):
//! [`a_slot_the_arguments_own_type_says_is_read`],
//! [`the_slot_is_read_wherever_the_clause_states_its_requirement`],
//! [`the_arguments_slot_outranks_the_callers_requirement`],
//! [`each_of_two_slots_on_one_spec_is_read_off_the_argument`],
//! [`a_slot_whose_spec_has_an_element_the_read_leaves_open_is_read`], and `agree` in
//! [`one_provider_or_a_named_parameter_is_read`] — each FAILS with the reading backed
//! out, by `-1`, or by the caller's `W`'s `4` for the third. Slots that may name two
//! providers are refused, at the citation and in an operation body alike
//! ([`two_slots_that_may_name_two_providers_are_refused`]), and a dot through another
//! variable's slot is the spec's call ([`a_dot_through_another_variables_slot_is_the_call`]).
//!
//! ## Stated limits
//!
//! Four, each a row at the end of the file:
//!
//!   * A SLOT AT THE CITING OPERATION'S OWN TYPE PARAMETER is refused for a call and not
//!     for a citation. Passes either way.
//!   * A DRIVER RUN AS A RULE'S GOAL answers `Int64`'s own. So the rows are driven through
//!     the interpreter, as P7VP4's are. Passes either way.
//!   * A SLOT THE CLAUSE'S BOUND WRITES is not read off the argument, as the operation-body
//!     twin does not read it. Passes either way.
//!   * A CALL IN A VALUE SLOT — the dot's, and its written twin — answers by the values and
//!     is not routed through the slot: WI-20261013-RYDNV's. The other half of the dot's row.

use anthill_core::eval::{self, Interpreter, Value};

/// WI-870's pair of opposite `Ord[Int64]` rivals beside `Int64`'s own provision, so the
/// three answers to `compare(1, 5)` differ: `Descending` gives `4`, `Ascending` `-4`, and
/// `Int64`'s own `-1`.
const ORD: &str = r#"
  import anthill.prelude.{Int64, String, Error, EmptyStream, Relation, List, Option, Ord, WeakOrd, PartialOrd, PartialEq, Eq}

  sort Ascending
    import anthill.prelude.Numeric.{sub}
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(a, b)
  end

  sort Descending
    import anthill.prelude.Numeric.{sub}
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end
"#;

fn program(ns: &str, body: &str) -> String {
    format!("namespace {ns}\n{ORD}\n{}end\n", body.replace("NS", ns))
}

/// Call a nullary operation on a FRESH interpreter — a trapped call poisons later calls on
/// a shared one, and `interp_for` panics on a dirty load, so a value here is also a
/// clean-load assertion.
fn drive(src: &str, entry: &str) -> i64 {
    call_int(&mut crate::common::interp_for(src), entry)
}

fn call_int(interp: &mut Interpreter, entry: &str) -> i64 {
    match interp.call(entry, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{entry}: expected an Int64, got {other:?}"),
    }
}

/// The ticket's fixture, with `p: Self` where it wrote `p: Box` (its 2026-10-05 note).
const BOX: &str = r#"
  sort Box
    sort T = ?
    requires O: WeakOrd[T]
    entity box(a: T, b: T)
    rule order(?p, ?c) :- ?p <=> box(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)
    rule orderPos(?p, ?c) :- ?p <=> box(?x, ?y), WeakOrd.compare(?x, ?y, ?c)
    operation orderOf(p: Self) -> Int64 effects {Error, Error[EmptyStream]} = order(p).head.c
    operation orderPosOf(p: Self) -> Int64 effects {Error, Error[EmptyStream]} = orderPos(p).head.c
    operation directOf(p: Self) -> Int64 = match p case box(a, b) -> WeakOrd.compare(a, b)
  end
"#;

const BOX_DRIVER: &str = r#"
  sort Driver
    import NS.Box.{box}
    operation ordDesc() -> Int64 effects {Error, Error[EmptyStream]} =
      Box.orderOf[T = Int64, O = Descending](box(a: 1, b: 5))
    operation ordAsc() -> Int64 effects {Error, Error[EmptyStream]} =
      Box.orderOf[T = Int64, O = Ascending](box(a: 1, b: 5))
    operation posDesc() -> Int64 effects {Error, Error[EmptyStream]} =
      Box.orderPosOf[T = Int64, O = Descending](box(a: 1, b: 5))
    operation dirDesc() -> Int64 = Box.directOf[T = Int64, O = Descending](box(a: 1, b: 5))
    operation dirAsc() -> Int64 = Box.directOf[T = Int64, O = Ascending](box(a: 1, b: 5))
  end
  rule uncited(?c) :- Box.order(Box.box(a: 1, b: 5), ?c)
"#;

fn box_program(ns: &str) -> String {
    program(ns, &format!("{BOX}{BOX_DRIVER}"))
}

/// THE CASE. `orderOf` holds `O` and its caller chose the rival; `order` reaches the
/// compared values through `<=>` and a constructor. The clause's condition is routed to
/// `orderOf`'s `O`.
#[test]
fn a_clause_typed_through_a_constructor_reads_its_sorts_requires() {
    let ns = "wi0rrqp.bx";
    let src = box_program(ns);
    assert_eq!(
        (drive(&src, &format!("{ns}.Driver.ordDesc")), drive(&src, &format!("{ns}.Driver.ordAsc"))),
        (4, -4),
        "`order`'s condition is filled by the provider `orderOf`'s caller chose",
    );
    assert_eq!(
        drive(&src, &format!("{ns}.Driver.posDesc")),
        4,
        "the constructor's fields written by position",
    );
}

/// CONTROLS — pass either way, BY DESIGN. A member operation reads the selection itself,
/// and a clause no operation cites derives its dictionary from the values: `Int64`'s own.
#[test]
fn a_member_operation_and_an_uncited_clause_answer_as_before() {
    let ns = "wi0rrqp.ctl";
    let src = box_program(ns);
    assert_eq!(
        (drive(&src, &format!("{ns}.Driver.dirDesc")), drive(&src, &format!("{ns}.Driver.dirAsc"))),
        (4, -4),
        "`directOf` dispatches through `O`",
    );
    let mut kb = crate::common::load_kb_with(&src);
    assert_eq!(
        crate::common::one_definite_int(&mut kb, &format!("{ns}.uncited")),
        Some(-1),
        "a rule goal hands `order` no dictionary",
    );
}

/// A CLAUSE THAT TYPES THE COLUMN BESIDE ONE THAT BOUNDS IT AT THE SORT'S OWN PARAMETER.
/// `bound`'s first clause types `?p` by the constructor, at a variable of its own; its
/// second writes `?p: Self`. The two meet, the sort's parameter stays the sort's, and the
/// first clause's condition is still routed: one row answers `4`, one `0`.
#[test]
fn a_typed_clause_meets_one_bound_at_the_sorts_parameter() {
    let ns = "wi0rrqp.bnd";
    let src = program(
        ns,
        r#"
  sort Box
    sort T = ?
    requires O: WeakOrd[T]
    entity box(a: T, b: T)
    rule bound(?p, ?c) :- ?p <=> box(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)
    rule bound(?p: Self, ?c) :- ?c <=> 0
    operation boundOf(p: Self, c: Int64) -> Int64 effects {Error} = bound(p, c).takeN(5).length()
  end
  sort Driver
    import NS.Box.{box}
    operation four() -> Int64 effects {Error} = Box.boundOf[T = Int64, O = Descending](box(a: 1, b: 5), 4)
    operation zero() -> Int64 effects {Error} = Box.boundOf[T = Int64, O = Descending](box(a: 1, b: 5), 0)
  end
"#,
    );
    assert_eq!(
        (drive(&src, &format!("{ns}.Driver.four")), drive(&src, &format!("{ns}.Driver.zero"))),
        (1, 1),
        "the constructor's clause answers through `Descending`, the bounded one beside it",
    );
}

/// A rule outside any sort over a parametric sort with no `requires`, cited by a generic
/// operation that holds the requirement.
const PR_DECLS: &str = r#"
  sort Pr[T]
    entity pr(a: T, b: T)
  end
  sort Outer[U]
    entity outer(inner: Pr[T = U])
  end
  import NS.Pr.{pr}
  import NS.Outer.{outer}

  rule ordPr(?p, ?c) :- ?p <=> pr(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)
  rule ordLeft(?p, ?c) :- pr(a: ?x, b: ?y) <=> ?p, WeakOrd.compare(?x, ?y, ?c)
  rule ordNested(?o, ?c) :- ?o <=> outer(inner: pr(a: ?x, b: ?y)), WeakOrd.compare(?x, ?y, ?c)
  rule ordTwoStep(?o, ?c) :- ?o <=> outer(inner: ?p), ?p <=> pr(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)
"#;

const PR_DRIVER: &str = r#"
  sort Driver
    operation via[A](p: Pr[T = A]) -> Int64 effects {Error, Error[EmptyStream]}
      requires WeakOrd[T = A] = ordPr(p).head.c
    operation viaLeft[A](p: Pr[T = A]) -> Int64 effects {Error, Error[EmptyStream]}
      requires WeakOrd[T = A] = ordLeft(p).head.c
    operation viaNested[A](o: Outer[U = A]) -> Int64 effects {Error, Error[EmptyStream]}
      requires WeakOrd[T = A] = ordNested(o).head.c
    operation viaTwoStep[A](o: Outer[U = A]) -> Int64 effects {Error, Error[EmptyStream]}
      requires WeakOrd[T = A] = ordTwoStep(o).head.c
    operation viaTwo[A](p: Pr[T = A], q: Pr[T = Int64]) -> Int64 effects {Error, Error[EmptyStream]}
      requires WeakOrd[T = A] = Int64.add(ordPr(p).head.c, ordPr(q).head.c)

    operation desc() -> Int64 effects {Error, Error[EmptyStream]} =
      via[A = Int64, WeakOrd = Descending](pr(a: 1, b: 5))
    operation asc() -> Int64 effects {Error, Error[EmptyStream]} =
      via[A = Int64, WeakOrd = Ascending](pr(a: 1, b: 5))
    operation left() -> Int64 effects {Error, Error[EmptyStream]} =
      viaLeft[A = Int64, WeakOrd = Descending](pr(a: 1, b: 5))
    operation nested() -> Int64 effects {Error, Error[EmptyStream]} =
      viaNested[A = Int64, WeakOrd = Descending](outer(inner: pr(a: 1, b: 5)))
    operation twoStep() -> Int64 effects {Error, Error[EmptyStream]} =
      viaTwoStep[A = Int64, WeakOrd = Descending](outer(inner: pr(a: 1, b: 5)))
    operation two() -> Int64 effects {Error, Error[EmptyStream]} =
      viaTwo[A = Int64, WeakOrd = Descending](pr(a: 1, b: 5), pr(a: 1, b: 5))
    -- a caller that holds NO dictionary
    operation plain() -> Int64 effects {Error, Error[EmptyStream]} = ordPr(pr(a: 1, b: 5)).head.c
  end
"#;

fn pr(ns: &str, entry: &str) -> i64 {
    drive(&program(ns, &format!("{PR_DECLS}{PR_DRIVER}")), &format!("{ns}.Driver.{entry}"))
}

/// THE TIE IS THE CONSTRUCTOR'S, not the enclosing sort's: `ordPr` is written in no sort,
/// and `via` holds the requirement at its own `A`. `plain` holds none and is the control
/// inside the row — `Int64`'s own, either way.
#[test]
fn the_tie_is_the_constructors_outside_any_sort() {
    let ns = "wi0rrqp.pr";
    assert_eq!((pr(ns, "desc"), pr(ns, "asc")), (4, -4), "`via`'s caller chose the provider");
    assert_eq!(pr(ns, "plain"), -1, "no dictionary to hand in: `Int64`'s own");
}

/// The constructor on the LEFT of `<=>`; a constructor in a FIELD of a constructor, typed
/// at the field's declared type; and the inner value named first and taken apart by a
/// second `<=>`.
#[test]
fn the_constructor_ties_on_either_side_and_at_any_depth() {
    let ns = "wi0rrqp.depth";
    assert_eq!(
        (pr(ns, "left"), pr(ns, "nested"), pr(ns, "twoStep")),
        (4, 4, 4),
        "left of `<=>`, nested in a field, and through a variable between two `<=>`",
    );
}

/// EACH CLAUSE IS MET ON ITS OWN. `ordBoth`'s clauses compare the two fields in opposite
/// orders, each through a condition of its own; under `Descending` one answers `4` and the
/// other `-4`. Both are filled: a row for each value.
#[test]
fn each_clause_of_a_relation_is_met_on_its_own() {
    let ns = "wi0rrqp.both";
    let src = program(
        ns,
        r#"
  sort Pr[T]
    entity pr(a: T, b: T)
  end
  import NS.Pr.{pr}
  rule ordBoth(?p, ?c) :- ?p <=> pr(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)
  rule ordBoth(?p, ?c) :- ?p <=> pr(a: ?x, b: ?y), WeakOrd.compare(?y, ?x, ?c)
  sort Driver
    operation viaBoth[A](p: Pr[T = A], c: Int64) -> Int64 effects {Error}
      requires WeakOrd[T = A] = ordBoth(p, c).takeN(5).length()
    operation four() -> Int64 effects {Error} =
      viaBoth[A = Int64, WeakOrd = Descending](pr(a: 1, b: 5), 4)
    operation minusFour() -> Int64 effects {Error} =
      viaBoth[A = Int64, WeakOrd = Descending](pr(a: 1, b: 5), -4)
  end
"#,
    );
    assert_eq!(
        (drive(&src, &format!("{ns}.Driver.four")), drive(&src, &format!("{ns}.Driver.minusFour"))),
        (1, 1),
        "one clause answers 4 and the other -4, both through the caller's `Descending`",
    );
}

/// TWO CITATIONS IN ONE BODY ARE TWO READINGS of the clause's typing. `viaTwo` cites
/// `ordPr` at its own `A` and at `Int64`: the first is filled from `viaTwo`'s requirement,
/// the second from `Int64`'s own provision — `4 + -1`.
#[test]
fn two_citations_in_one_body_are_two_readings() {
    assert_eq!(pr("wi0rrqp.two", "two"), 3, "`Descending` for `A`, `Int64`'s own at `Int64`");
}

/// A RULE OF AN EARLIER LOAD, cited by an operation of a later one: the clause's typing is
/// read where the earlier load left it.
#[test]
fn a_rule_of_an_earlier_load_is_read_by_a_later_one() {
    let early = "wi0rrqp.early";
    let mut kb = crate::common::load_kb_with(&program(early, PR_DECLS));
    let later = format!(
        "namespace wi0rrqp.late\n  \
         import anthill.prelude.{{Int64, Error, EmptyStream, WeakOrd}}\n  \
         import {early}.{{Pr, Outer, Descending, Ascending, ordPr, ordLeft, ordNested, ordTwoStep}}\n  \
         import {early}.Pr.{{pr}}\n  \
         import {early}.Outer.{{outer}}\n{PR_DRIVER}end\n"
    );
    if let Err(errs) = crate::common::load_in_a_later_call(&mut kb, &later, Default::default()) {
        panic!("the later load: {:?}", crate::common::rendered_load_errors(errs));
    }
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp).expect("register standard eval builtins");
    assert_eq!(
        (
            call_int(&mut interp, "wi0rrqp.late.Driver.desc"),
            call_int(&mut interp, "wi0rrqp.late.Driver.asc"),
            call_int(&mut interp, "wi0rrqp.late.Driver.nested"),
        ),
        (4, -4, 4),
        "the later load's citations of the earlier load's rules",
    );
}

/// A COLUMN THE CITATION GIVES NO TYPE PINS NOTHING. `mixed`'s column `n` is typed by
/// `Util.mix`'s parameter and by nothing else, and `mix` owes a requirement, so its call
/// is woven. Cited from a later load the clause's body no longer holds that call as an
/// application: the citation has no type for `n`, while the clause's own typing says
/// `Int64`. A variable is not an `Int64`, and read as a disagreement it left the whole
/// clause unread — `compare`'s condition unfilled, `Int64`'s own `-1`.
#[test]
fn a_column_the_citation_gives_no_type_pins_nothing() {
    let early = "wi0rrqp.mixearly";
    let mut kb = crate::common::load_kb_with(&program(
        early,
        r#"
  sort Pr[T]
    entity pr(a: T, b: T)
  end
  import NS.Pr.{pr}
  sort Util
    operation mix[A](x: A, n: Int64) -> Int64 requires WeakOrd[T = A] = n
  end
  rule seven(?n) :- ?n <=> 7
  rule mixed(?p, ?n, ?c) :-
    ?p <=> pr(a: ?x, b: ?y), seven(?n), Util.mix(?x, ?n, ?m), WeakOrd.compare(?x, ?y, ?c)
"#,
    ));
    let later = format!(
        "namespace wi0rrqp.mixedlate\n  \
         import anthill.prelude.{{Int64, Error, EmptyStream, WeakOrd}}\n  \
         import {early}.{{Pr, Descending, mixed}}\n  \
         import {early}.Pr.{{pr}}\n  \
         operation via[A](p: Pr[T = A]) -> Int64 effects {{Error, Error[EmptyStream]}}\n    \
         requires WeakOrd[T = A] = mixed(p).head.c\n  \
         operation desc() -> Int64 effects {{Error, Error[EmptyStream]}} =\n    \
         via[A = Int64, WeakOrd = Descending](pr(a: 1, b: 5))\nend\n"
    );
    if let Err(errs) = crate::common::load_in_a_later_call(&mut kb, &later, Default::default()) {
        panic!("the later load: {:?}", crate::common::rendered_load_errors(errs));
    }
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp).expect("register standard eval builtins");
    assert_eq!(call_int(&mut interp, "wi0rrqp.mixedlate.desc"), 4, "`compare` through `Descending`");
}

const WRAP: &str = r#"
  sort Colour
    entity red
    entity green
  end
  sort Wrap[T]
    entity wrap(v: T)
  end
  sort Holder[E]
    entity holder(h: Wrap[T = E])
  end
  sort Pinned
    entity pinned(h: Wrap[T = Int64], n: Int64)
  end
  import NS.Wrap.{wrap}
  import NS.Holder.{holder}
  import NS.Pinned.{pinned}
  import anthill.prelude.Option.{none}
  import anthill.prelude.List.{nil, cons}
  rule gen(?y) :- ?y <=> red
"#;

fn wrap_errors(ns: &str, body: &str) -> Vec<String> {
    crate::common::load_errors_of(&program(ns, &format!("{WRAP}{body}")))
}

/// A COLUMN TYPED BY A CONSTRUCTOR IS CHECKED AT ITS CITATION. The column had no type, so
/// an argument of any type bound it and its value was returned at any type.
///
/// A constructor with no field is written as its name and types the same way, as an
/// argument of a constructor (`wrap(red)`) and on its own (`?x <=> red`).
#[test]
fn a_column_typed_by_a_constructor_is_checked_at_its_citation() {
    const TAG: &str = "  rule tag(?x, ?y) :- ?x <=> wrap(?y)\n";
    crate::common::assert_refused_naming(
        &wrap_errors(
            "wi0rrqp.arg",
            &format!("{TAG}  operation f() -> Int64 effects {{Error}} = tag(5).takeN(3).length()\n"),
        ),
        &["argument binding column `x` has an incompatible type"],
        "an `Int64` for a column the clause types `Wrap`",
    );
    assert!(
        wrap_errors(
            "wi0rrqp.argok",
            &format!("{TAG}  operation f() -> Int64 effects {{Error}} = tag(wrap(red)).takeN(3).length()\n"),
        )
        .is_empty(),
        "a `Wrap` binds it",
    );
    let returned = |ns: &str, rule: &str, ret: &str| {
        wrap_errors(
            ns,
            &format!(
                "  rule tag(?x) :- {rule}\n  \
                 operation f() -> {ret} effects {{Error, Error[EmptyStream]}} = tag.head.x\n"
            ),
        )
    };
    assert!(returned("wi0rrqp.c1", "?x <=> wrap(red)", "Wrap[T = Colour]").is_empty());
    crate::common::assert_refused_naming(
        &returned("wi0rrqp.c2", "?x <=> wrap(red)", "Wrap[T = Int64]"),
        &["expected Wrap[T = Int64], got Wrap[T = Colour]"],
        "the field's constant says which `Wrap`",
    );
    assert!(returned("wi0rrqp.c3", "?x <=> red", "Colour").is_empty());
    crate::common::assert_refused_naming(
        &returned("wi0rrqp.c4", "?x <=> red", "Int64"),
        &["expected Int64, got Colour"],
        "a constant constructor on its own",
    );
}

/// TWO CLAUSES THAT TAKE ONE PARAMETRIC SORT APART ARE ONE RELATION. Each clause types the
/// column at a variable of its own, and the two types have no join as written. `fieldTwice`
/// is the shape that was refused before this ticket — a column typed by an entity field at
/// its sort's parameter; `ctorTwice` and `kind` are the shapes the constructor's typing
/// would have added to it.
#[test]
fn two_clauses_that_take_a_sort_apart_are_one_relation() {
    let ns = "wi0rrqp.join";
    let src = program(
        ns,
        &format!(
            "{WRAP}  fact holder(h: wrap(red))\n  \
             rule fieldTwice(?x) :- holder(h: ?x)\n  \
             rule fieldTwice(?x) :- holder(h: ?x), gen(?y)\n  \
             rule ctorTwice(?x) :- gen(?y), ?x <=> wrap(?y)\n  \
             rule ctorTwice(?x) :- gen(?y), ?x <=> wrap(?y), gen(?z)\n  \
             rule kind(?l, ?k) :- ?l <=> nil, ?k <=> 0\n  \
             rule kind(?l, ?k) :- ?l <=> cons(head: ?h, tail: ?t), ?k <=> 1\n  \
             sort Driver\n    \
             operation fields() -> Int64 effects {{Error}} = fieldTwice.takeN(5).length()\n    \
             operation ctors() -> Int64 effects {{Error}} = ctorTwice.takeN(5).length()\n    \
             operation kindOf(xs: List[T = Int64]) -> Int64 effects {{Error, Error[EmptyStream]}} =\n      \
             kind(xs).head.k\n    \
             operation empty() -> Int64 effects {{Error, Error[EmptyStream]}} = kindOf([])\n    \
             operation full() -> Int64 effects {{Error, Error[EmptyStream]}} = kindOf([1, 2])\n  \
             end\n"
        ),
    );
    let at = |entry: &str| drive(&src, &format!("{ns}.Driver.{entry}"));
    assert_eq!((at("fields"), at("ctors")), (2, 2), "a row from each clause");
    assert_eq!((at("empty"), at("full")), (0, 1), "the clause the list's own shape selects");
}

/// The two solutions `tag` has in every row below, at two instances of `Wrap`.
const TWO_INSTANCES: &str = "  fact holder(h: wrap(1))\n  fact holder(h: wrap(red))\n";

/// A VARIABLE OF THE CLAUSE THAT A CITATION LEAVES UNFIXED IS AN UNKNOWN (user decision
/// 2026-10-21). `tag`'s solutions stand at two instances of `Wrap` — `wrap(1)` and
/// `wrap(red)`, each `?t` read off its value — so what the citation's arguments do not fix
/// is some `Wrap`: `tag.head.x` loads where nothing asks for its element and is refused
/// returned as a `Wrap[T = Colour]`, in each way the clause can leave the element open. The
/// bound's written variable and unwritten slot loaded, and `f` answered `wrap(v: 1)`
/// whenever that solution came first (they come in no fixed order); the other spellings were
/// refused only because the first call reading the citation (`.head`) opened a variable
/// named like a written `?`.
///
/// Two spellings this row held are no unknown since WI-20261013-WF14Z: `gen(?y)` types `?y`
/// by `gen`'s column, a `Colour`, so `rule tag(?x) :- gen(?y), ?x <=> wrap(?y)` — and its head
/// bound `?x: Wrap` — read back as a `Wrap[T = Colour]` load and as a `Wrap[T = Int64]` are
/// refused, naming `Colour` ([`a_rule_goal_fixes_what_the_citation_leaves_unfixed`]).
#[test]
fn a_variable_the_citation_leaves_unfixed_is_an_unknown() {
    let spellings = [
        ("wi0rrqp.u1", "rule tag(?x: Wrap[T = ?t]) :- holder(h: ?x)", "Wrap"),
        ("wi0rrqp.u2", "rule tag(?x: Wrap) :- holder(h: ?x)", "Wrap"),
        ("wi0rrqp.u3", "rule tag(?x: Wrap[T = ?]) :- holder(h: ?x)", "Wrap"),
        ("wi0rrqp.u4", "rule tag(?x) :- holder(h: ?x)", "Wrap"),
        ("wi0rrqp.u6", "rule tag(?x) :- ?x <=> none", "Option"),
    ];
    for (ns, rule, sort) in spellings {
        let read_back = |ns: &str, ret: &str| {
            program(
                ns,
                &format!(
                    "{WRAP}{TWO_INSTANCES}  {rule}\n  \
                     operation f() -> {ret} effects {{Error, Error[EmptyStream]}} = tag.head.x\n"
                ),
            )
        };
        let errs = crate::common::load_errors_of(&read_back(ns, &format!("{sort}[T = Colour]")));
        assert_eq!(errs.len(), 1, "`{rule}`: one refusal, got {errs:?}");
        crate::common::assert_refused_naming(
            &errs,
            &["f.return", &format!("expected {sort}[T = Colour], got {sort}[T = ?")],
            &format!("`{rule}` read back as a `{sort}[T = Colour]`"),
        );
        // The bound's written variable is named as written, where the body's unification
        // met it with a variable of its own (`holder`'s field).
        if rule.contains("?t") {
            crate::common::assert_refused_naming(
                &errs,
                &["got Wrap[T = ?t]"],
                "the author's `?t`, not the body's variable",
            );
        }
        let ns = format!("{ns}ok");
        let mut interp = crate::common::interp_for(&read_back(&ns, sort));
        let out = interp
            .call(&format!("{ns}.f"), &[])
            .unwrap_or_else(|e| panic!("`{rule}` read back as a `{sort}`: {e:?}"));
        let printer = anthill_core::persistence::print::TermPrinter::new(interp.kb());
        let rendered = match &out {
            Value::Node(occ) => printer.print_occurrence(occ),
            Value::Term { id, .. } => printer.print_term(*id),
            other => format!("{other:?}"),
        };
        assert!(
            rendered.contains("wrap") || rendered.contains("none"),
            "`{rule}` read back as a `{sort}`: one of its solutions, got `{rendered}`"
        );
    }
}

/// A RULE GOAL'S COLUMN FIXES WHAT A CITATION WOULD LEAVE UNFIXED (068-implementation §6.2,
/// decision 1). `gen`'s column is a `Colour`, so `tag`'s `?x <=> wrap(?y)` is a
/// `Wrap[T = Colour]`, its bound's unwritten slot included: read back as one it loads and
/// answers `wrap(v: red)`, and as a `Wrap[T = Int64]` it is refused. Read at no type, the
/// element was an unknown both ways. FAILS with the rule goal read as no position
/// (`LatePosition::RuleGoal`).
#[test]
fn a_rule_goal_fixes_what_the_citation_leaves_unfixed() {
    for (ns, rule) in [
        ("wi0rrqp.g5", "rule tag(?x) :- gen(?y), ?x <=> wrap(?y)"),
        ("wi0rrqp.g7", "rule tag(?x: Wrap) :- gen(?y), ?x <=> wrap(?y)"),
    ] {
        let read_back = |ns: &str, ret: &str| {
            program(
                ns,
                &format!(
                    "{WRAP}  {rule}\n  \
                     operation f() -> {ret} effects {{Error, Error[EmptyStream]}} = tag.head.x\n"
                ),
            )
        };
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&read_back(ns, "Wrap[T = Int64]")),
            &["f.return", "expected Wrap[T = Int64], got Wrap[T = Colour]"],
            &format!("`{rule}` read back as a `Wrap[T = Int64]`"),
        );
        let ns = format!("{ns}ok");
        let mut interp = crate::common::interp_for(&read_back(&ns, "Wrap[T = Colour]"));
        let out = interp
            .call(&format!("{ns}.f"), &[])
            .unwrap_or_else(|e| panic!("`{rule}` read back as a `Wrap[T = Colour]`: {e:?}"));
        let printer = anthill_core::persistence::print::TermPrinter::new(interp.kb());
        let rendered = match &out {
            Value::Node(occ) => printer.print_occurrence(occ),
            Value::Term { id, .. } => printer.print_term(*id),
            other => format!("{other:?}"),
        };
        assert!(rendered.contains("red"), "`{rule}`: `wrap(v: red)`, got `{rendered}`");
    }
}

/// The citation itself, returned whole or passed at a written instance, is refused as its
/// rows are: `.head` reads nothing the citation did not already say. Both loaded, and
/// `r().head.x` was `wrap(v: 1)`. Passed at `Relation[T = (x: Wrap), …]` it loads and holds
/// both solutions.
#[test]
fn the_citation_whole_is_refused_at_a_written_instance() {
    let whole = |ns: &str, body: &str| {
        wrap_errors(ns, &format!("{TWO_INSTANCES}  rule tag(?x) :- holder(h: ?x)\n{body}"))
    };
    crate::common::assert_refused_naming(
        &whole(
            "wi0rrqp.w1",
            "  operation r() -> Relation[T = (x: Wrap[T = Colour]), E = {Error}] = tag\n",
        ),
        &[
            "r.return",
            "expected Relation[T = (x: Wrap[T = Colour]), E = {Error}], got Relation[T = (x: Wrap[T = ?",
        ],
        "returned whole",
    );
    crate::common::assert_refused_naming(
        &whole(
            "wi0rrqp.w2",
            "  operation take(r: Relation[T = (x: Wrap[T = Colour]), E = {Error}]) -> Int64 effects {Error} =\n    \
             r.takeN(5).length()\n  \
             operation f() -> Int64 effects {Error} = take(tag)\n",
        ),
        &["take.r", "expected Relation[T = (x: Wrap[T = Colour]), E = {Error}], got Relation[T = (x: Wrap[T = ?"],
        "passed to a parameter at a written instance",
    );
    let ns = "wi0rrqp.w3";
    let src = program(
        ns,
        &format!(
            "{WRAP}{TWO_INSTANCES}  rule tag(?x) :- holder(h: ?x)\n  \
             operation take(r: Relation[T = (x: Wrap), E = {{Error}}]) -> Int64 effects {{Error}} =\n    \
             r.takeN(5).length()\n  \
             operation f() -> Int64 effects {{Error}} = take(tag)\n"
        ),
    );
    assert_eq!(drive(&src, &format!("{ns}.f")), 2, "both solutions, at no written instance");
}

/// WHERE AN ARGUMENT FIXES IT, the citation reads the solutions at that instance, and the
/// others are not its solutions: the typed head's domain check is handed the dictionary of
/// `Wrap[T = Colour]` the citation built (060-implementation §7.3 S3a). `[]` holds no element,
/// so no value fixes `?t` at run time; reached as a rule goal, where nothing hands the check
/// a dictionary, the same rule answers both. PASSES EITHER WAY, BY DESIGN: the control that
/// the unknown is minted only for what the citation leaves unfixed.
#[test]
fn where_an_argument_fixes_it_the_other_instances_are_dropped() {
    let ns = "wi0rrqp.a1";
    let src = program(
        ns,
        &format!(
            "{WRAP}{TWO_INSTANCES}  rule tag3(?w: List[T = Wrap[T = ?t]], ?x: Wrap[T = ?t]) :- holder(h: ?x)\n  \
             rule q(?n) :- tag3([], ?x), ?n <=> 1\n  \
             operation f(e: List[T = Wrap[T = Colour]]) -> Int64 effects {{Error}} = tag3(e).takeN(5).length()\n  \
             operation g() -> Int64 effects {{Error}} = f([])\n  \
             operation viaGoal() -> Int64 effects {{Error}} = q.takeN(5).length()\n"
        ),
    );
    let mut interp = crate::common::interp_for(&src);
    assert_eq!(call_int(&mut interp, &format!("{ns}.g")), 1, "the solution at `Colour`");
    assert_eq!(call_int(&mut interp, &format!("{ns}.viaGoal")), 2, "both, through a rule goal");
}

/// A COLUMN A RULE GOAL FILLS IS READ AT ITS TYPE (068-implementation §6.2, decision 1):
/// `untyped(?x) :- tag(?x)` reads `?x` at `tag`'s column, a `Wrap`, so `untyped.head.x`
/// returned as an `Int64` is refused. Read at no type — a rule goal typed none of its
/// arguments — it loaded, and `f` answered a `wrap`. FAILS with the rule goal read as no
/// position (`LatePosition::RuleGoal`).
#[test]
fn a_column_a_rule_goal_types_is_read_at_its_type() {
    let errs = wrap_errors(
        "wi0rrqp.l1",
        &format!(
            "{TWO_INSTANCES}  rule tag(?x) :- holder(h: ?x)\n  rule untyped(?x) :- tag(?x)\n  \
             operation f() -> Int64 effects {{Error, Error[EmptyStream]}} = untyped.head.x\n"
        ),
    );
    crate::common::assert_refused_naming(
        &errs,
        &["f.return", "expected Int64, got Wrap[T = ?"],
        "a `Wrap` column returned as an `Int64`",
    );
}

/// `Same` ties its two fields' types: a clause that builds `same(a: ?w, b: ?x)` says `?w` and
/// `?x` are of one type, whatever the head writes.
const SAME: &str = "  sort Same[T]\n    entity same(a: T, b: T)\n  end\n  import NS.Same.{same}\n";

/// ONCE A CLAUSE IS TYPED, INFERENCE AND WRITING MAKE NO DIFFERENCE (user, 2026-10-21). Over
/// `tag`'s two instances, the citation `p(wrap(red))` fixes `?x`'s element at `Colour`
/// through `same`'s shared `T`, and reads the one solution there whether `?x`'s type is
/// inferred (`p1`), written while `?w`'s is inferred (`p2`), or written for both (`p3`). The
/// inferred column was read with no check — both solutions under a type that says `Colour`
/// — and `p2`'s written `?e` was a variable the body's tie never reached, so `h2` was refused,
/// 'expected Wrap[T = Colour], got Wrap[T = ?e]'. A rule of a sort with parameters reads the
/// same at an expected type (`n4`), over `bx`'s two instances: it read both. (Its `bx` built
/// a `b2(v: 5)` once, which fixed `Box2`'s `T` in `pr`'s body, now refused —
/// `a_body_that_fixes_a_sorts_parameter_is_refused`.)
#[test]
fn an_inferred_column_is_checked_as_a_written_one() {
    let ns = "wi0rrqp.i1";
    let src = program(
        ns,
        &format!(
            "{WRAP}{TWO_INSTANCES}{SAME}  \
             rule p1(?w, ?x) :- holder(h: ?x), ?z <=> same(a: ?w, b: ?x)\n  \
             rule p2(?w, ?x: Wrap[T = ?e]) :- holder(h: ?x), ?z <=> same(a: ?w, b: ?x)\n  \
             rule p3(?w: Wrap[T = ?e], ?x: Wrap[T = ?e]) :- holder(h: ?x), ?z <=> same(a: ?w, b: ?x)\n  \
             operation n1() -> Int64 effects {{Error}} = p1(wrap(red)).takeN(5).length()\n  \
             operation n2() -> Int64 effects {{Error}} = p2(wrap(red)).takeN(5).length()\n  \
             operation n3() -> Int64 effects {{Error}} = p3(wrap(red)).takeN(5).length()\n  \
             operation h2() -> Wrap[T = Colour] effects {{Error, Error[EmptyStream]}} = p2(wrap(red)).head.x\n  \
             fact bx(NS.Box2.b2(v: 5))\n  fact bx(NS.Box2.b2(v: \"s\"))\n  \
             sort Box2[T]\n    entity b2(v: T)\n    rule pr(?x: Box2[T = T], ?y) :- bx(?x), holder(h: ?y)\n  end\n  \
             operation n4() -> Int64 effects {{Error}} =\n    \
             let r: Relation[T = (x: Box2[T = Int64], y: Wrap[T = Colour]), E = {{Error}}] = Box2[T = Int64].pr\n    \
             r.takeN(5).length()\n"
        ),
    );
    let mut interp = crate::common::interp_for(&src);
    for entry in ["n1", "n2", "n3", "n4"] {
        assert_eq!(call_int(&mut interp, &format!("{ns}.{entry}")), 1, "{entry}: the solution at `Colour`");
    }
}

/// STATED LIMIT, PASSES EITHER WAY: a bound filled at the caller's own type parameter is
/// checked only where the caller holds that parameter's `SortDomain`. `at[A = Colour]([])`
/// reads both of `tag3`'s solutions; under `requires SortDomain[T = A]`, the one at `Colour`.
#[test]
fn a_bound_at_the_callers_parameter_is_checked_through_its_domain_only() {
    let ns = "wi0rrqp.l2";
    let src = program(
        ns,
        &format!(
            "{WRAP}{TWO_INSTANCES}  \
             rule tag3(?w: List[T = Wrap[T = ?t]], ?x: Wrap[T = ?t]) :- holder(h: ?x)\n  \
             operation at[A](e: List[T = Wrap[T = A]]) -> Int64 effects {{Error}} = tag3(e).takeN(5).length()\n  \
             operation atHeld[A](e: List[T = Wrap[T = A]]) -> Int64 effects {{Error}}\n    \
             requires anthill.reflect.SortDomain[T = A] = tag3(e).takeN(5).length()\n  \
             operation open() -> Int64 effects {{Error}} = at[A = Colour]([])\n  \
             operation held() -> Int64 effects {{Error}} = atHeld[A = Colour]([])\n"
        ),
    );
    let mut interp = crate::common::interp_for(&src);
    assert_eq!(call_int(&mut interp, &format!("{ns}.open")), 2, "no SortDomain held: both");
    assert_eq!(call_int(&mut interp, &format!("{ns}.held")), 1, "SortDomain held: the one at `Colour`");
}

/// A VALUE WITH A FREE PART, AT AN INSTANCE THE CITATION FIXES, STANDS FOR ITS INSTANCES
/// (user, 2026-10-21: a typed expression is read at its type). `mk` builds `?x <=> wrap(v:
/// ?y)` with `?y` free, and `mk(wrap(red))` fixes `?x`'s element at `Colour` through `same`:
/// the column's check fills `?y` from `Colour`'s domain, `wrap(red)` and `wrap(green)`. With no
/// check the citation read the one value `wrap(v: ?y)`.
#[test]
fn a_free_part_at_a_fixed_instance_is_filled_from_its_domain() {
    let ns = "wi0rrqp.e1";
    let src = program(
        ns,
        &format!(
            "{WRAP}{SAME}  import NS.Colour.{{green}}\n  \
             rule mk(?w, ?x) :- ?x <=> wrap(v: ?y), ?z <=> same(a: ?w, b: ?x)\n  \
             operation n() -> Int64 effects {{Error}} = mk(wrap(red)).takeN(5).length()\n"
        ),
    );
    assert_eq!(drive(&src, &format!("{ns}.n")), 2, "`wrap(red)` and `wrap(green)`");
}

/// A VALUE WHOSE ELEMENT NOTHING FIXES ANSWERS CONDITIONALLY (user, 2026-10-21: it loads).
/// `gen` builds `?w <=> wrap(inner: ?i)`, a `Wrap[E = e]`, and `elemOfSum` reaches `gen` as a
/// rule goal and never reads `?w`: nothing fixes `e`, so the column's check cannot fill `?i`
/// and the answer `Sum` stands on it. It was definite while the column had no check.
#[test]
fn a_value_whose_element_nothing_fixes_answers_conditionally() {
    let src = r#"
namespace wi0rrqp.g1
  import anthill.prelude.Int64
  import anthill.realization.runtime.Dictionary
  sort Zeroable
    sort T = ?
    operation zero() -> Int64
    operation tag(x: T) -> Int64 = 0
  end
  sort Sum
    import anthill.prelude.Int64
    entity sum
    provides Zeroable[T = Sum]
    operation zero() -> Int64 = 3
    operation tag(x: Sum) -> Int64 = 1
  end
  sort Wrap
    import anthill.prelude.Int64
    sort E = ?
    entity wrap(inner: E)
    provides Zeroable[T = Self] :- Zeroable[E] where
      operation zero() -> Int64 = Int64.add(Zeroable.zero[T = E](), 100)
      operation tag(x: Self) -> Int64 = 9
    end
  end
  import wi0rrqp.g1.Sum.{sum}
  import wi0rrqp.g1.Wrap.{wrap}
  rule get(?x, ?d) :- ?d = require[Zeroable[?]], Zeroable.tag(?x, ?t)
  rule gen(?w, ?d, ?ed) :- ?ed <=> Dictionary.sub(?d, 0), ?w <=> wrap(inner: ?i)
  rule elemOfSum(?s) :- get(wrap(inner: sum()), ?d), gen(?w, ?d, ?ed), ?s <=> Dictionary.impl(?ed)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let all = crate::common::query_unary(&mut kb, "wi0rrqp.g1.elemOfSum");
    assert_eq!(all.len(), 1, "one answer, got {all:?}");
    assert!(!all[0].1, "conditional on `?w`'s check, got {all:?}");
}

/// A VARIABLE PASSED TO A SPEC'S OPERATION GETS NO BOUND. `Bag.first(?x, ?r)` reads `?x` as
/// `Bag[E = e]`, which says `?x`'s sort provides `Bag`; as a bound it is a type the value
/// has, and `domain(?x, Bag[E = ?e])` refuses an `intBag(n: 1)` — no nominal spec is read as
/// its providers there, as the written head `?x: Bag[E = ?e]` shows. Installed, `viaDict` and
/// `answer` answered nothing.
#[test]
fn a_variable_passed_to_a_spec_operation_gets_no_bound() {
    let src = r#"
namespace wi0rrqp.b1
  import anthill.prelude.{Int64}
  sort Bag
    sort E = ?
    operation first(b: Self) -> Int64 = 0
  end
  sort IntBag
    sort N = ?
    entity intBag(n: N)
    provides Bag[E = N]
    operation first(b: Self) -> Int64 = 7
  end
  rule dict(?x, ?d) :- ?d = require[Bag[?]], Bag.first(?x, ?r)
  rule answer(?d) :- dict(intBag(n: 1), ?d)
  rule dict2(?x, ?r) :- Bag.first(?x, ?r)
  rule viaDict(?r) :- dict2(intBag(n: 1), ?r)
  rule written(?x: Bag[E = ?e], ?r) :- Bag.first(?x, ?r)
  rule viaWritten(?r) :- written(intBag(n: 1), ?r)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let via = crate::common::query_unary(&mut kb, "wi0rrqp.b1.viaDict");
    assert!(
        via.len() == 1 && via[0].1 && crate::common::scalar_int(&kb, &via[0].0) == Some(7),
        "`IntBag`'s `first`, got {via:?}"
    );
    assert_eq!(crate::common::query_unary(&mut kb, "wi0rrqp.b1.answer").len(), 1, "the dictionary");
    assert!(
        crate::common::query_unary(&mut kb, "wi0rrqp.b1.viaWritten").is_empty(),
        "the written twin, refused by its check"
    );
}

/// A BODY THAT FIXES A SORT'S PARAMETER IS REFUSED (068-implementation §6.2, decision 3):
/// the enclosing sort's parameter is rigid in a clause, as in an operation body. `Box3`'s
/// `pr` says `?x` is a `b3(v: 5)` at every `T`, and `Outer.Inner`'s `r` a `wrap(1)` at every
/// outer `T`. Read through the body, `T` was `Int64`, and each loaded and read both of
/// `holder`'s solutions where a written bound's would read one. The repair, a bare `Box3` —
/// an open slot (070) — loads, a relation of `Box3[T = Int64]` values.
#[test]
fn a_body_that_fixes_a_sorts_parameter_is_refused() {
    let ns = "wi0rrqp.c9";
    let errs = wrap_errors(
        ns,
        &format!(
            "{TWO_INSTANCES}  \
             sort Box3[T]\n    entity b3(v: T)\n    rule pr(?x: Box3[T = T], ?y) :- ?x <=> b3(v: 5), holder(h: ?y)\n  end\n  \
             sort Outer[T]\n    entity outer(v: T)\n    sort Inner\n      \
             rule r(?x: Wrap[T = T]) :- ?x <=> wrap(1)\n    end\n  end\n"
        ),
    );
    assert!(
        errs.len() == 2
            && errs[0].contains("type mismatch in Box3.T (sort-parameter): expected T, got Int64")
            && errs[1].contains("type mismatch in Outer.T (sort-parameter): expected T, got Int64"),
        "{errs:#?}"
    );
    let mut kb = crate::common::load_kb_with(&program(
        ns,
        "  sort Box3[T]\n    entity b3(v: T)\n    rule pr(?x: Box3) :- ?x <=> b3(v: 5)\n  end\n",
    ));
    let rows = crate::common::query_unary(&mut kb, &format!("{ns}.Box3.pr"));
    assert!(
        rows.len() == 1 && rows[0].1,
        "the bare sort's clause answers its `b3(v: 5)`: {rows:?}"
    );
}

/// A CONSTRUCTOR IN A FIELD OF THE HEAD types its variables at the field. `pinned`'s head
/// is the entity's, whose `h` is a `Wrap[T = Int64]`: `?x` is an `Int64`, and the dot on it
/// is the call. Read as a variable of no type the dot is data, and `?n` is the term
/// `-3.abs`.
///
/// A constant constructor in a head field says the same: `same(l: warm, r: ?r, n: ?n)`
/// over `entity same(l: T, r: T, n: Int64)` makes `?r` a `Tone`, and `?r.code()` its call.
#[test]
fn a_constructor_in_a_head_field_types_its_variables() {
    let ns = "wi0rrqp.head";
    let mut kb = crate::common::load_kb_with(&program(
        ns,
        &format!(
            "{WRAP}  sort Tone\n    entity warm\n    operation code(t: Tone) -> Int64 = 7\n  end\n  \
             sort Same[T]\n    entity same(l: T, r: T, n: Int64)\n  end\n  \
             import NS.Tone.{{warm}}\n  \
             import NS.Same.{{same}}\n  \
             rule src(?v) :- ?v <=> -3\n  \
             rule pinned(h: wrap(?x), n: ?n) :- src(?x), ?n <=> ?x.abs()\n  \
             rule q(?n) :- pinned(h: ?h, n: ?n)\n  \
             rule tone(?t) :- ?t <=> warm\n  \
             rule same(l: warm, r: ?r, n: ?n) :- tone(?r), ?n <=> ?r.code()\n  \
             rule qSame(?n) :- same(l: ?l, r: ?r, n: ?n)\n"
        ),
    ));
    assert_eq!(
        crate::common::one_definite_int(&mut kb, &format!("{ns}.q")),
        Some(3),
        "`?x.abs()` at `Int64`",
    );
    assert_eq!(
        crate::common::one_definite_int(&mut kb, &format!("{ns}.qSame")),
        Some(7),
        "`?r.code()` at `Tone`, the sort of the constant beside it in the head",
    );
}

/// AN ORDINARY OPERATION'S OWN `requires`, reached through a constructor. `sign` declares
/// `requires WeakOrd[T = A]`; its call at `?x` is a condition of the clause for that entry
/// (a slot read), and it is filled as `compare`'s is.
#[test]
fn an_operations_own_requires_reached_through_a_constructor_is_filled() {
    let ns = "wi0rrqp.slot";
    let src = program(
        ns,
        &format!(
            "{PR_DECLS}  sort Util\n    \
             operation sign[A](x: A, y: A) -> Int64 requires WeakOrd[T = A] = WeakOrd.compare(x, y)\n  \
             end\n  \
             rule signPr(?p, ?c) :- ?p <=> pr(a: ?x, b: ?y), Util.sign(?x, ?y, ?c)\n  \
             sort Driver\n    \
             operation viaSign[A](p: Pr[T = A]) -> Int64 effects {{Error, Error[EmptyStream]}}\n      \
             requires WeakOrd[T = A] = signPr(p).head.c\n    \
             operation desc() -> Int64 effects {{Error, Error[EmptyStream]}} =\n      \
             viaSign[A = Int64, WeakOrd = Descending](pr(a: 1, b: 5))\n    \
             operation asc() -> Int64 effects {{Error, Error[EmptyStream]}} =\n      \
             viaSign[A = Int64, WeakOrd = Ascending](pr(a: 1, b: 5))\n  \
             end\n"
        ),
    );
    assert_eq!(
        (drive(&src, &format!("{ns}.Driver.desc")), drive(&src, &format!("{ns}.Driver.asc"))),
        (4, -4),
        "`sign`'s slot through the caller's provider",
    );
}

/// A HEAD BOUND BESIDE THE CONSTRUCTOR. The ticket measured `rule order(?p: Self, ?c)` and
/// `rule order(?p: Box[T = T], ?c)` over the same body at `-1` under both providers: the
/// bound types the column and said nothing of `?x`. The column is the bound's and the
/// witness the clause's own, and the two meet.
#[test]
fn a_head_bound_beside_the_constructor_reads_the_same() {
    let ns = "wi0rrqp.hb";
    let src = program(
        ns,
        r#"
  sort Box
    sort T = ?
    requires O: WeakOrd[T]
    entity box(a: T, b: T)
    rule orderSelf(?p: Self, ?c) :- ?p <=> box(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)
    rule orderAtT(?p: Box[T = T], ?c) :- ?p <=> box(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)
    operation selfOf(p: Self) -> Int64 effects {Error, Error[EmptyStream]} = orderSelf(p).head.c
    operation atTOf(p: Self) -> Int64 effects {Error, Error[EmptyStream]} = orderAtT(p).head.c
  end
  sort Driver
    import NS.Box.{box}
    operation selfDesc() -> Int64 effects {Error, Error[EmptyStream]} =
      Box.selfOf[T = Int64, O = Descending](box(a: 1, b: 5))
    operation selfAsc() -> Int64 effects {Error, Error[EmptyStream]} =
      Box.selfOf[T = Int64, O = Ascending](box(a: 1, b: 5))
    operation atTDesc() -> Int64 effects {Error, Error[EmptyStream]} =
      Box.atTOf[T = Int64, O = Descending](box(a: 1, b: 5))
    operation atTAsc() -> Int64 effects {Error, Error[EmptyStream]} =
      Box.atTOf[T = Int64, O = Ascending](box(a: 1, b: 5))
  end
"#,
    );
    let at = |entry: &str| drive(&src, &format!("{ns}.Driver.{entry}"));
    assert_eq!((at("selfDesc"), at("selfAsc")), (4, -4), "`?p: Self`");
    assert_eq!((at("atTDesc"), at("atTAsc")), (4, -4), "`?p: Box[T = T]`");
}

/// A DOT ON A VARIABLE THE CLAUSE TYPES THROUGH A CONSTRUCTOR IS THE CALL. `?c <=> cnt(n:
/// 4)` makes `?c` a `Cnt`, and `?c.bump()` its member's call, as a dot on a variable an
/// entity field types already was. Read at no type the dot was data: `?x` was the term
/// `cnt(n: 4).bump`, and a member `Cnt` does not have loaded.
#[test]
fn a_dot_on_a_variable_typed_through_a_constructor_is_the_call() {
    const CNT: &str = "  sort Cnt\n    entity cnt(n: Int64)\n    \
                       operation bump(c: Cnt) -> Int64 = Int64.add(c.n, 1)\n  end\n  \
                       import NS.Cnt.{cnt}\n";
    let ns = "wi0rrqp.dot";
    let mut kb = crate::common::load_kb_with(&program(
        ns,
        &format!("{CNT}  rule bumped(?x) :- ?c <=> cnt(n: 4), ?x <=> ?c.bump()\n"),
    ));
    assert_eq!(
        crate::common::one_definite_int(&mut kb, &format!("{ns}.bumped")),
        Some(5),
        "`Cnt.bump` of `cnt(n: 4)`",
    );
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program(
            "wi0rrqp.nodot",
            &format!("{CNT}  rule bad(?x) :- ?c <=> cnt(n: 4), ?x <=> ?c.nosuch()\n"),
        )),
        &["Cnt.nosuch", "no such member (dot dispatch)"],
        "a member `Cnt` does not have",
    );
}

/// A CALL AT A VARIABLE THE CLAUSE TYPES AT A SORT IS DECIDED AT LOAD, by that sort, as a
/// call at a literal is (kernel-language §5.3: "a call whose arguments' types are known at
/// load is decided there, by its carrier, and has no condition"). `viaCtor` says `?p` is a
/// `Pt`: `describe` is `Pt`'s own whoever cites it, and a sort that provides no `Desc` is a
/// load error. With `?p` at no type the call was a condition, and the citing operation's
/// `Loud` reached it — as it reaches `viaVar`, which says nothing of `?p` and passes either
/// way.
#[test]
fn a_call_at_a_variable_the_clause_types_is_decided_at_load() {
    const DESC: &str = r#"
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Pt
    entity pt(x: Int64, y: Int64)
    provides Desc[T = Pt]
    operation describe(p: Pt) -> Int64 = 1
  end
  sort Loud
    provides Desc[T = Pt]
    operation describe(p: Pt) -> Int64 = 9
  end
  sort Q
    entity q(z: Int64)
  end
  import NS.Pt.{pt}
  import NS.Q.{q}
"#;
    let ns = "wi0rrqp.fire";
    let src = program(
        ns,
        &format!(
            "{DESC}  rule viaCtor(?p, ?s) :- ?p <=> pt(x: 1, y: 2), Desc.describe(?p, ?s)\n  \
             rule viaVar(?p, ?s) :- Desc.describe(?p, ?s)\n  \
             sort Driver\n    \
             operation cite(p: Pt) -> Int64 effects {{Error, Error[EmptyStream]}}\n      \
             requires Desc[T = Pt] = viaCtor(p).head.s\n    \
             operation citeVar(p: Pt) -> Int64 effects {{Error, Error[EmptyStream]}}\n      \
             requires Desc[T = Pt] = viaVar(p).head.s\n    \
             operation ctor() -> Int64 effects {{Error, Error[EmptyStream]}} =\n      \
             cite[Desc = Loud](pt(x: 1, y: 2))\n    \
             operation var() -> Int64 effects {{Error, Error[EmptyStream]}} =\n      \
             citeVar[Desc = Loud](pt(x: 1, y: 2))\n  \
             end\n"
        ),
    );
    assert_eq!(drive(&src, &format!("{ns}.Driver.ctor")), 1, "`Pt`'s own: the clause says `Pt`");
    assert_eq!(drive(&src, &format!("{ns}.Driver.var")), 9, "CONTROL: a condition, and `Loud`");
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program(
            "wi0rrqp.nofire",
            &format!("{DESC}  rule noProvider(?p, ?s) :- ?p <=> q(z: 1), Desc.describe(?p, ?s)\n"),
        )),
        &["Q` provides no `", "Desc"],
        "`Q` provides no `Desc`",
    );
}

/// A CONSTRUCTOR THAT DOES NOT FIT ITS POSITION IS REFUSED, at the field
/// (068-implementation §6.2, decision 3). `h`'s field is a `W2[A = E, B = Int64]`, which a
/// construction there is read at, as an operation body reads it; the clause writes a `w2`
/// whose `b` is a `String`. It loaded before, the construction pinning nothing, and its
/// fields were checked at parameters of their own. The twin whose `b` is `5` loads.
#[test]
fn a_constructor_that_does_not_fit_its_position_is_refused() {
    let at = |b: &str| {
        wrap_errors(
            "wi0rrqp.misfit",
            &format!(
                "  sort W2[A, B]\n    entity w2(a: A, b: B)\n  end\n  \
                 sort H[E]\n    entity h(inner: W2[A = E, B = Int64])\n  end\n  \
                 import NS.W2.{{w2}}\n  \
                 import NS.H.{{h}}\n  \
                 rule r(?q, ?x) :- ?q <=> h(inner: w2(a: ?x, b: {b}))\n  \
                 operation f(q: H[E = Colour]) -> Int64 effects {{Error}} = r(q, red).takeN(3).length()\n"
            ),
        )
    };
    let errs = at("\"s\"");
    assert!(
        errs.len() == 1
            && errs[0].contains("type mismatch in w2.b (entity-field): expected Int64, got String"),
        "{errs:#?}"
    );
    assert!(at("5").is_empty(), "the twin loads: {:?}", at("5"));
}

/// A citation from OUTSIDE the sort, of a `Box` whose `O` the signature leaves out: the
/// slot is the argument's (`b.O`), and the clause's condition reaches it as the member
/// operation's call does.
const OUTSIDE: &str = r#"
  sort Out
    import NS.Box.{box}
    operation mk() -> Box[T = Int64, O = Ascending] = box(a: 1, b: 5)
    operation cite[A](b: Box[T = A]) -> Int64 effects {Error, Error[EmptyStream]} = Box.order(b).head.c
    operation call[A](b: Box[T = A]) -> Int64 = Box.directOf(b)
    operation cited() -> Int64 effects {Error, Error[EmptyStream]} = cite(mk())
    operation called() -> Int64 = call(mk())
    -- the argument's own type says the slot
    operation citedAtItsType() -> Int64 effects {Error, Error[EmptyStream]} = Box.order(mk()).head.c
    operation calledAtItsType() -> Int64 = Box.directOf(mk())
  end
"#;

#[test]
fn a_citation_outside_the_sort_reads_the_slot_its_argument_carries() {
    let ns = "wi0rrqp.out";
    let src = program(ns, &format!("{BOX}{OUTSIDE}"));
    let at = |entry: &str| drive(&src, &format!("{ns}.Out.{entry}"));
    assert_eq!(at("cited"), -4, "`order`'s condition through `b.O`, which is `Ascending`");
    assert_eq!(at("called"), -4, "CONTROL, either way: the member operation's call");
}

/// A SLOT THE ARGUMENT'S OWN TYPE SAYS IS READ, by a citation from an operation that holds no
/// requirement, as the member operation's call reads it: `mk()`'s `Box[T = Int64, O =
/// Ascending]` answers `-4` both ways. The clause's typing says `?p` is a `Box[T = t, O = o]`
/// and its read is `WeakOrd[T = t]`, which is what `O` states at those bindings, so the read is
/// answered by `o` as the citation fixes it (`carried_slot_selection`; WI-20261013-WF14Z,
/// 068-implementation §6.7). FAILS with that reading backed out: the citation derived
/// `Int64`'s own `-1` from the values.
#[test]
fn a_slot_the_arguments_own_type_says_is_read() {
    let ns = "wi0rrqp.own";
    let src = program(ns, &format!("{BOX}{OUTSIDE}"));
    let at = |entry: &str| drive(&src, &format!("{ns}.Out.{entry}"));
    assert_eq!(
        (at("citedAtItsType"), at("calledAtItsType")),
        (-4, -4),
        "the citation and the call both read the value's `Ascending`",
    );
}

/// The clause and the citation in the other shapes the slot is read through, each beside the
/// operation-body twin it answers as. `compare(1, 5)` is `-4` under `Ascending`, `4` under
/// `Descending`, `-1` for `Int64`'s own.
const CARRIED: &str = r#"
  sort CBox
    sort T = ?
    requires O: WeakOrd[T]
    entity cbox(a: T, b: T)
    rule order(?p, ?c) :- ?p <=> cbox(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)
    rule atLiterals(?p, ?c) :- ?p <=> cbox(a: ?x, b: ?y), WeakOrd.compare(1, 5, ?c)
    rule atColumn(?p, ?x, ?c) :- ?p <=> cbox(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)
    rule boundSelf(?p: Self, ?c) :- ?p <=> cbox(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)
    rule positional(?p, ?c) :- ?p <=> cbox(?x, ?y), WeakOrd.compare(?x, ?y, ?c)
    rule written(?p: CBox[T = Int64, O = Descending], ?c) :- ?p <=> cbox(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)
    operation direct(p: Self) -> Int64 = match p case cbox(a, b) -> WeakOrd.compare(a, b)
    operation directAtLiterals(p: Self) -> Int64 = match p case cbox(a, b) -> WeakOrd.compare(1, 5)
  end
  sort AscBox = CBox[T = Int64, O = Ascending]
  sort Cite
    import NS.CBox.{cbox}
    operation asc() -> CBox[T = Int64, O = Ascending] = cbox(a: 1, b: 5)
    operation desc() -> CBox[T = Int64, O = Descending] = cbox(a: 1, b: 5)
    operation aliased() -> AscBox = cbox(a: 1, b: 5)
    operation atLiterals() -> Int64 effects {Error, Error[EmptyStream]} = CBox.atLiterals(asc()).head.c
    operation atLiteralsCalled() -> Int64 = CBox.directAtLiterals(asc())
    operation atColumn() -> Int64 effects {Error, Error[EmptyStream]} = CBox.atColumn(asc(), 1).head.c
    operation atColumnFree() -> Int64 effects {Error, Error[EmptyStream]} = CBox.atColumn(asc()).head.c
    operation boundSelf() -> Int64 effects {Error, Error[EmptyStream]} = CBox.boundSelf(asc()).head.c
    operation positional() -> Int64 effects {Error, Error[EmptyStream]} = CBox.positional(asc()).head.c
    operation alias() -> Int64 effects {Error, Error[EmptyStream]} = CBox.order(aliased()).head.c
    operation aliasCalled() -> Int64 = CBox.direct(aliased())
    operation viaLet() -> Int64 effects {Error, Error[EmptyStream]} =
      let b = desc()
      CBox.order(b).head.c
    operation param(b: CBox[T = Int64, O = Descending]) -> Int64 effects {Error, Error[EmptyStream]} =
      CBox.order(b).head.c
    operation viaParam() -> Int64 effects {Error, Error[EmptyStream]} = param(desc())
    operation paramCalled(b: CBox[T = Int64, O = Descending]) -> Int64 = CBox.direct(b)
    operation viaParamCalled() -> Int64 = paramCalled(desc())
    operation written() -> Int64 effects {Error, Error[EmptyStream]} = CBox.written(desc()).head.c
    operation writtenOp(p: CBox[T = Int64, O = Descending]) -> Int64 =
      match p case cbox(a, b) -> WeakOrd.compare(a, b)
    operation writtenCalled() -> Int64 = writtenOp(desc())
  end
  sort Holder
    import NS.Cite.{asc}
    requires W: WeakOrd[T = Int64]
    operation cited() -> Int64 effects {Error, Error[EmptyStream]} = CBox.order(asc()).head.c
    operation called() -> Int64 = CBox.direct(asc())
  end
  sort HolderDriver
    operation cited() -> Int64 effects {Error, Error[EmptyStream]} = Holder.cited[W = Descending]()
    operation called() -> Int64 = Holder.called[W = Descending]()
  end
"#;

/// The slot is read where the clause's own typing says the read is its requirement, wherever
/// the variable stands and however the argument's type is written: the witness a column, a
/// `Self` bound, positional fields, a type alias, a `let`, a parameter. A read at another type
/// (`compare(1, 5, ?c)`) is not the slot's, as in the member operation. FAILS with the reading
/// backed out: `atColumn`, `atColumnFree`, `boundSelf`, `positional`, `alias`, `viaLet` and
/// `viaParam`, each `-1`; the operation-body twins and `atLiterals` pass either way.
#[test]
fn the_slot_is_read_wherever_the_clause_states_its_requirement() {
    let ns = "wi0rrqp.carried";
    let src = program(ns, CARRIED);
    let at = |entry: &str| drive(&src, &format!("{ns}.Cite.{entry}"));
    for (entry, twin, answer) in [
        ("atLiterals", "atLiteralsCalled", -1),
        ("atColumn", "aliasCalled", -4),
        ("atColumnFree", "aliasCalled", -4),
        ("boundSelf", "aliasCalled", -4),
        ("positional", "aliasCalled", -4),
        ("alias", "aliasCalled", -4),
        ("viaLet", "viaParamCalled", 4),
        ("viaParam", "viaParamCalled", 4),
    ] {
        assert_eq!((at(entry), at(twin)), (answer, answer), "`{entry}` beside `{twin}`");
    }
}

/// THE ARGUMENT'S SLOT OUTRANKS THE CALLER'S REQUIREMENT, as a call's does: `Holder` holds
/// `W: WeakOrd[T = Int64]`, selected `Descending`, and the argument's type says `Ascending`.
/// FAILS with the reading backed out: the citation answered through `W`, `4`.
#[test]
fn the_arguments_slot_outranks_the_callers_requirement() {
    let ns = "wi0rrqp.holder";
    let src = program(ns, CARRIED);
    let at = |entry: &str| drive(&src, &format!("{ns}.HolderDriver.{entry}"));
    assert_eq!((at("cited"), at("called")), (-4, -4));
}

/// TWO SLOTS ON ONE SPEC, read off one argument by a citation from outside the sort: each
/// clause's read is its own slot's, `OK`'s for the keys and `OV`'s for the values, at one
/// element type and at two, and in one clause that reads both. FAILS with the reading backed
/// out: every answer `-1` (`String`'s own for `"a"`, `"b"`).
#[test]
fn each_of_two_slots_on_one_spec_is_read_off_the_argument() {
    let ns = "wi0rrqp.pairout";
    let src = program(
        ns,
        r#"
  sort StrSeven
    provides Ord[T = String]
    operation compare(a: String, b: String) -> Int64 = 7
  end
  sort Pair2
    sort K = ?
    sort V = ?
    requires OK: WeakOrd[T = K]
    requires OV: WeakOrd[T = V]
    entity entry(k1: K, k2: K, v1: V, v2: V)
    rule keyOrder(?p, ?c) :- ?p <=> entry(k1: ?a, k2: ?b, v1: ?, v2: ?), WeakOrd.compare(?a, ?b, ?c)
    rule valOrder(?p, ?c) :- ?p <=> entry(k1: ?, k2: ?, v1: ?a, v2: ?b), WeakOrd.compare(?a, ?b, ?c)
    rule both(?p, ?c, ?d) :- ?p <=> entry(k1: ?a, k2: ?b, v1: ?u, v2: ?v), WeakOrd.compare(?a, ?b, ?c), WeakOrd.compare(?u, ?v, ?d)
  end
  sort Driver
    import NS.Pair2.{entry}
    operation ints() -> Pair2[K = Int64, V = Int64, OK = Descending, OV = Ascending] =
      entry(k1: 1, k2: 5, v1: 1, v2: 5)
    operation mixed() -> Pair2[K = Int64, V = String, OK = Descending, OV = StrSeven] =
      entry(k1: 1, k2: 5, v1: "a", v2: "b")
    operation key() -> Int64 effects {Error, Error[EmptyStream]} = Pair2.keyOrder(ints()).head.c
    operation val() -> Int64 effects {Error, Error[EmptyStream]} = Pair2.valOrder(ints()).head.c
    operation bothKey() -> Int64 effects {Error, Error[EmptyStream]} = Pair2.both(ints()).head.c
    operation bothVal() -> Int64 effects {Error, Error[EmptyStream]} = Pair2.both(ints()).head.d
    operation mixedVal() -> Int64 effects {Error, Error[EmptyStream]} = Pair2.valOrder(mixed()).head.c
  end
"#,
    );
    let at = |entry: &str| drive(&src, &format!("{ns}.Driver.{entry}"));
    assert_eq!(
        [at("key"), at("val"), at("bothKey"), at("bothVal"), at("mixedVal")],
        [4, -4, 4, -4, 7]
    );
}

/// STATED LIMIT — passes either way. A slot written at the citing operation's own type
/// parameter (`b: Box[T = A, O = P]`) is refused for the member operation's call — nothing
/// in scope holds a dictionary for `P` — and the citation beside it loads and derives
/// `Int64`'s own.
#[test]
fn a_slot_at_the_citers_own_parameter_is_refused_for_a_call_and_not_for_a_citation() {
    let outside = |ns: &str, op: &str| {
        program(
            ns,
            &format!(
                "{BOX}  sort Out\n    import NS.Box.{{box}}\n    \
                 operation mk() -> Box[T = Int64, O = Ascending] = box(a: 1, b: 5)\n    {op}\n  end\n"
            ),
        )
    };
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&outside(
            "wi0rrqp.pcall",
            "operation call[A, P](b: Box[T = A, O = P]) -> Int64 = Box.directOf(b)",
        )),
        &["named slot `O`", "nothing in the enclosing scope holds a dictionary FOR `P`"],
        "the call is refused",
    );
    let ns = "wi0rrqp.pcite";
    let src = outside(
        ns,
        "operation cite[A, P](b: Box[T = A, O = P]) -> Int64 effects {Error, Error[EmptyStream]} =\n      \
         Box.order(b).head.c\n    \
         operation cited() -> Int64 effects {Error, Error[EmptyStream]} = cite(mk())",
    );
    assert_eq!(drive(&src, &format!("{ns}.Out.cited")), -1, "the citation loads, and derives");
}

/// A driver run as a rule's GOAL: the selection `desc` writes in its own body for an
/// operation-level `requires` reaches the citation under it, as it does when the
/// interpreter runs the driver (`the_tie_is_the_constructors_outside_any_sort`) — `4`.
/// Until WI-20261013-GFS6A the resolver bridged the selected call with its argument values
/// only, re-derived the requirement at `Int64`, and the clause answered `Int64`'s own `-1`.
/// FAILS with the call's own stamps not carried to the bridge (`WovenDispatch::Stamped`).
#[test]
fn a_driver_run_as_a_rules_goal_reads_its_selection() {
    let ns = "wi0rrqp.goal";
    let mut kb = crate::common::load_kb_with(&program(
        ns,
        &format!("{PR_DECLS}{PR_DRIVER}  rule q(?r) :- ?r <=> Driver.desc()\n"),
    ));
    assert_eq!(
        crate::common::one_definite_int(&mut kb, &format!("{ns}.q")),
        Some(4),
        "`Driver.desc()` as a goal",
    );
}

/// THE TICKET'S SECOND ROW. `Pair2` requires `OK: WeakOrd[T = K]` and `OV: WeakOrd[T = V]`,
/// and each of its two clauses calls `compare` at a variable typed through the constructor:
/// `keyOrder` at the keys, `valOrder` at the values. Cited from member operations, each
/// clause's condition is filled from the requirement at its own parameter and not from
/// either by the order they are declared in — with the two parameters at two types, and
/// at one, where the two conditions are one text, `WeakOrd[T = Int64]`.
///
/// `compare(1, 5)` is `4` under `Descending` and `-4` under `Ascending`; `StrSeven`
/// answers `7` for any two strings.
#[test]
fn each_clause_reaches_its_own_of_two_requirements_on_one_sort() {
    let pair = r#"
  sort StrSeven
    provides Ord[T = String]
    operation compare(a: String, b: String) -> Int64 = 7
  end
  sort Pair2
    sort K = ?
    sort V = ?
    requires OK: WeakOrd[T = K]
    requires OV: WeakOrd[T = V]
    entity entry(k1: K, k2: K, v1: V, v2: V)
    rule keyOrder(?p, ?c) :- ?p <=> entry(k1: ?a, k2: ?b, v1: ?, v2: ?), WeakOrd.compare(?a, ?b, ?c)
    rule valOrder(?p, ?c) :- ?p <=> entry(k1: ?, k2: ?, v1: ?a, v2: ?b), WeakOrd.compare(?a, ?b, ?c)
    operation keyOf(p: Self) -> Int64 effects {Error, Error[EmptyStream]} = keyOrder(p).head.c
    operation valOf(p: Self) -> Int64 effects {Error, Error[EmptyStream]} = valOrder(p).head.c
  end
  sort Driver
    import NS.Pair2.{entry}
    operation key() -> Int64 effects {Error, Error[EmptyStream]} = Pair2.keyOf[BRACKET](ENTRY)
    operation val() -> Int64 effects {Error, Error[EmptyStream]} = Pair2.valOf[BRACKET](ENTRY)
  end
"#;
    let ints = "entry(k1: 1, k2: 5, v1: 1, v2: 5)";
    let mixed = r#"entry(k1: 1, k2: 5, v1: "a", v2: "b")"#;
    for (ns, bracket, entry, key, val) in [
        ("wi0rrqp.pair.da", "K = Int64, V = Int64, OK = Descending, OV = Ascending", ints, 4, -4),
        ("wi0rrqp.pair.ad", "K = Int64, V = Int64, OK = Ascending, OV = Descending", ints, -4, 4),
        ("wi0rrqp.pair.twotypes", "K = Int64, V = String, OK = Descending, OV = StrSeven", mixed, 4, 7),
    ] {
        let src = program(ns, &pair.replace("BRACKET", bracket).replace("ENTRY", entry));
        assert_eq!(drive(&src, &format!("{ns}.Driver.key")), key, "`keyOrder`, under `[{bracket}]`");
        assert_eq!(drive(&src, &format!("{ns}.Driver.val")), val, "`valOrder`, under `[{bracket}]`");
    }
}

/// A SLOT WHOSE SPEC HAS AN ELEMENT THE READ LEAVES OPEN is read too: `Conv.conv(?x, ?c)`
/// decides `A` from its argument and leaves `B`, and `requires C: Conv[A = T, B = Int64]`
/// states both, so the read is the slot's and is resolved as the slot states it — `PlusTen`'s
/// `11`, as the member operation answers. FAILS, the citation floundering between `PlusOne`
/// and `PlusTen`, with the reading backed out and with each of two halves of it: the read
/// compared with the slot whole, its open `B` against the slot's `Int64`
/// (`slot_states_the_read`), and the read's own goal resolved, whose open `B` the provision's
/// `Int64` refuses (`carried_slot_selection`'s goal).
#[test]
fn a_slot_whose_spec_has_an_element_the_read_leaves_open_is_read() {
    let ns = "wi0rrqp.conv";
    let src = program(
        ns,
        r#"
  sort Conv
    sort A = ?
    sort B = ?
    operation conv(a: A) -> B
  end
  sort PlusOne
    import anthill.prelude.Numeric.{add}
    provides Conv[A = Int64, B = Int64]
    operation conv(a: Int64) -> Int64 = add(a, 1)
  end
  sort PlusTen
    import anthill.prelude.Numeric.{add}
    provides Conv[A = Int64, B = Int64]
    operation conv(a: Int64) -> Int64 = add(a, 10)
  end
  sort Box
    sort T = ?
    requires C: Conv[A = T, B = Int64]
    entity box(a: T)
    rule r(?p, ?c) :- ?p <=> box(a: ?x), Conv.conv(?x, ?c)
    operation direct(p: Self) -> Int64 = match p case box(a) -> Conv.conv(a)
  end
  sort Out
    import NS.Box.{box}
    operation mk() -> Box[T = Int64, C = PlusTen] = box(a: 1)
    operation cited() -> Int64 effects {Error, Error[EmptyStream]} = Box.r(mk()).head.c
    operation called() -> Int64 = Box.direct(mk())
  end
"#,
    );
    let at = |entry: &str| drive(&src, &format!("{ns}.Out.{entry}"));
    assert_eq!((at("cited"), at("called")), (11, 11));
}

/// A DOT THROUGH ANOTHER VARIABLE'S SLOT IS THE CALL (user, 2026-10-22): in `orderDot`, `?x`
/// is typed `t` and `?p`'s `O` states `WeakOrd[T = t]`, so `?x.compare(?y)` is
/// `WeakOrd.compare(?x, ?y)`, as `a.compare(b)` is in a member of `Box`. It was data, and the
/// citation handed back the term `1.compare(5)` declared an `Int64`. STATED LIMIT, the other
/// half: in a value slot the call answers as its written twin `orderVal` there does, by the
/// values, `Int64`'s own `-1` where the goal-position `order` answers `-4`; weaving a value
/// slot's call through the clause's condition is WI-20261013-RYDNV's. FAILS with the dot's
/// reading backed out (`find_spec_op_for_clause_slot`): `dotOutside` is the term.
#[test]
fn a_dot_through_another_variables_slot_is_the_call() {
    let ns = "wi0rrqp.dot";
    let src = program(
        ns,
        &format!(
            "{BOX}  sort Dots\n    import NS.Box.{{box}}\n    \
             rule orderDot(?p, ?c) :- ?p <=> box(a: ?x, b: ?y), ?c <=> ?x.compare(?y)\n    \
             rule orderVal(?p, ?c) :- ?p <=> box(a: ?x, b: ?y), ?c <=> WeakOrd.compare(?x, ?y)\n    \
             operation mk() -> Box[T = Int64, O = Ascending] = box(a: 1, b: 5)\n    \
             operation dotOutside() -> Int64 effects {{Error, Error[EmptyStream]}} = orderDot(mk()).head.c\n    \
             operation valOutside() -> Int64 effects {{Error, Error[EmptyStream]}} = orderVal(mk()).head.c\n    \
             operation goalOutside() -> Int64 effects {{Error, Error[EmptyStream]}} = Box.order(mk()).head.c\n  \
             end\n"
        ),
    );
    let at = |entry: &str| drive(&src, &format!("{ns}.Dots.{entry}"));
    assert_eq!(
        [at("dotOutside"), at("valOutside"), at("goalOutside")],
        [-1, -1, -4]
    );
}

/// STATED LIMIT — passes either way. A slot the clause's bound writes is not read off the
/// argument: `written`'s `?p: CBox[T = Int64, O = Descending]` makes the read `Int64`'s own,
/// `-1`, as the operation-body twin with the same parameter type answers.
#[test]
fn a_slot_the_clause_writes_is_not_read_off_the_argument() {
    let ns = "wi0rrqp.writtenslot";
    let src = program(ns, CARRIED);
    let at = |entry: &str| drive(&src, &format!("{ns}.Cite.{entry}"));
    assert_eq!((at("written"), at("writtenCalled")), (-1, -1));
}

/// Two `CBox` values in one clause, or two `CBox` parameters of one operation: a read at
/// their shared element is stated by both values' `O`, and is refused where they may name two
/// providers (user, 2026-10-22).
const TWO_BOXES: &str = r#"
  sort CBox
    sort T = ?
    requires O: WeakOrd[T]
    entity cbox(a: T, b: T)
    rule two(?p, ?q, ?c) :- ?p <=> cbox(a: ?x, b: ?y), ?q <=> cbox(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)
    rule order(?p, ?c) :- ?p <=> cbox(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)
    operation direct(p: Self) -> Int64 = match p case cbox(a, b) -> WeakOrd.compare(a, b)
  end
  sort Util
    operation cmp[A](x: A, y: A) -> Int64 requires WeakOrd[T = A] = WeakOrd.compare(x, y)
  end
  sort Cite
    import NS.CBox.{cbox}
    operation asc() -> CBox[T = Int64, O = Ascending] = cbox(a: 1, b: 5)
    operation desc() -> CBox[T = Int64, O = Descending] = cbox(a: 1, b: 5)
    OPS
  end
"#;

/// TWO SLOTS THAT MAY NAME TWO PROVIDERS ARE REFUSED, in every spelling of the read: the
/// citation whose arguments fix the two to two witnesses, or to a witness and the caller's
/// own parameter; the operation body that reads one goal through two parameters' slots, by
/// a call to the spec operation and by a call that forwards the requirement. Before, the
/// citation answered `Int64`'s own (`-1`) and the body the first parameter's (`-4`, `q`'s
/// values compared by `p`'s order). FAILS with each refusal backed out: the citation's
/// (`carried_slot_reading`), the body read's (`contested_slot_read`), the forward's
/// (`build_dep_projection`).
#[test]
fn two_slots_that_may_name_two_providers_are_refused() {
    let at = |ns: &str, ops: &str| {
        crate::common::load_errors_of(&program(ns, &TWO_BOXES.replace("OPS", ops)))
    };
    let two_witnesses = "fix two requirement slots that state it, to `wi0rrqp.twocite.Ascending` \
                         and to `wi0rrqp.twocite.Descending`, and the read names neither";
    let mixed = "to `wi0rrqp.twomixed.Ascending` and to the caller's `?P`";
    let body = "`p`'s slot `O` and `q`'s answer it, two parameters of one carrier, and the read \
                names neither";
    let forward = "the frame's slots for `anthill.prelude.WeakOrd[T = \
                   wi0rrqp.twofwd.Util.cmp.A]`: `p`'s slot `O` and `q`'s answer it, two \
                   parameters of one carrier, and the read names neither";
    for (ns, ops, says) in [
        (
            "wi0rrqp.twocite",
            "operation cited() -> Int64 effects {Error, Error[EmptyStream]} = \
             CBox.two(asc(), desc()).head.c",
            two_witnesses,
        ),
        (
            "wi0rrqp.twomixed",
            "operation mixed[P](q: CBox[T = Int64, O = P]) -> Int64 effects {Error, \
             Error[EmptyStream]} = CBox.two(asc(), q).head.c",
            mixed,
        ),
        (
            "wi0rrqp.twobody",
            "operation twoOp[A](p: CBox[T = A], q: CBox[T = A]) -> Int64 =\n      \
             match q case cbox(a, b) -> WeakOrd.compare(a, b)",
            body,
        ),
        (
            "wi0rrqp.twofwd",
            "operation twoFwd[A](p: CBox[T = A], q: CBox[T = A]) -> Int64 =\n      \
             match q case cbox(a, b) -> Util.cmp(a, b)",
            forward,
        ),
    ] {
        let errors = at(ns, ops);
        assert!(errors.len() == 1 && errors[0].contains(says), "{ns}: {errors:#?}");
    }
}

/// THE OTHER TWO COLLISIONS of the spec's rule (kernel-language §5.2: a slot another entry of
/// the frame already covers is refused rather than guessed), each refused with what collides:
/// a cited parameter whose slot a requirement the caller writes covers (`Holder`'s `W`), and
/// a read two slots of ONE parameter's carrier state at one type (`Semi`'s `OA` and `OB`).
/// Both loaded before, answering from the caller's `W` and from `OA`. Found by /code-review,
/// which also found their first wording naming one parameter twice. FAILS with the
/// citation's refusal of an unheld slot backed out (`CarriedMisfit::Unheld`), by `Holder`,
/// and with the body's (`contested_slot_read`), by `Semi`.
#[test]
fn a_collision_with_the_callers_requirement_or_a_second_slot_is_refused() {
    let holder = crate::common::load_errors_of(&program(
        "wi0rrqp.holderslot",
        &format!(
            "{BOX}  sort Holder\n    import NS.Box.{{box}}\n    requires W: WeakOrd[T = Int64]\n    \
             operation cited(b: Box[T = Int64]) -> Int64 effects {{Error, Error[EmptyStream]}} = \
             Box.order(b).head.c\n  end\n"
        ),
    ));
    assert!(
        holder.len() == 1
            && holder[0].contains(
                "expected the caller's slot `b.O`, whose requirement a read of the clause is, got \
                 a requirement the caller writes answers it"
            ),
        "{holder:#?}"
    );
    let semi = crate::common::load_errors_of(&program(
        "wi0rrqp.semislots",
        "  sort Semi\n    sort T = ?\n    requires OA: WeakOrd[T]\n    requires OB: WeakOrd[T]\n    \
         entity semi(a: T, b: T)\n  end\n  sort User\n    import NS.Semi.{semi}\n    \
         operation readA(s: Semi[T = Int64]) -> Int64 = match s case semi(a, b) -> WeakOrd.compare(a, b)\n  \
         end\n",
    ));
    assert!(
        semi.len() == 1
            && semi[0].contains("`s`'s slots `OA` and `OB` answer it, two slots of one carrier at one type"),
        "{semi:#?}"
    );
}

/// CONTROLS, beside the refusals: two slots fixed to one witness route it; a call or a
/// citation that names one of two parameters reads that parameter's slot, and one whose slot
/// the frame holds for the other is refused, as such a call is (EE0EP's
/// `two_parameters_of_one_carrier_are_refused`). FAILS with the citation's reading backed out,
/// by `agree` (`-1`), and with a parameter's own slot taken as contested, by `first`.
#[test]
fn one_provider_or_a_named_parameter_is_read() {
    let ns = "wi0rrqp.twoone";
    let src = program(
        ns,
        &TWO_BOXES.replace(
            "OPS",
            "operation agree() -> Int64 effects {Error, Error[EmptyStream]} = \
             CBox.two(asc(), asc()).head.c\n    \
             operation first[A](b1: CBox[T = A], b2: CBox[T = A]) -> Int64 effects {Error, \
             Error[EmptyStream]} = CBox.order(b1).head.c\n    \
             operation runFirst() -> Int64 effects {Error, Error[EmptyStream]} = first(asc(), desc())\n    \
             operation viaP[A](p: CBox[T = A], q: CBox[T = A]) -> Int64 = CBox.direct(p)\n    \
             operation runViaP() -> Int64 = viaP(desc(), asc())",
        ),
    );
    let at = |entry: &str| drive(&src, &format!("{ns}.Cite.{entry}"));
    assert_eq!([at("agree"), at("runFirst"), at("runViaP")], [-4, -4, 4]);
    let errors = crate::common::load_errors_of(&program(
        "wi0rrqp.twosecond",
        &TWO_BOXES.replace(
            "OPS",
            "operation second[A](b1: CBox[T = A], b2: CBox[T = A]) -> Int64 effects {Error, \
             Error[EmptyStream]} = CBox.order(b2).head.c",
        ),
    ));
    assert!(
        errors.len() == 1
            && errors[0].contains("expected the caller's slot `b2.O`, whose requirement a read \
                                   of the clause is, got the frame holds one slot for it and \
                                   `b1.O`, two parameters of one carrier"),
        "{errors:#?}"
    );
}

/// A SLOT FIXED TO A WITNESS THAT DOES NOT ANSWER THE READ IS REFUSED, at the citation, as the
/// member operation's call is: `mk() -> Box[T = String, O = Descending]` names a witness of
/// `WeakOrd[T = Int64]` only. FAILS with the refusal backed out (`settle_citation_routes`):
/// the citation loads and the read derives `String`'s own.
#[test]
fn a_slot_fixed_to_a_witness_that_does_not_answer_is_refused() {
    let at = |ns: &str, op: &str| {
        crate::common::load_errors_of(&program(
            ns,
            &format!(
                "{BOX}  sort Out\n    import NS.Box.{{box}}\n    \
                 operation mk() -> Box[T = String, O = Descending] = box(a: \"x\", b: \"y\")\n    \
                 {op}\n  end\n"
            ),
        ))
    };
    for (ns, op, callee) in [
        (
            "wi0rrqp.misfitcite",
            "operation cited() -> Int64 effects {Error, Error[EmptyStream]} = Box.order(mk()).head.c",
            "order",
        ),
        ("wi0rrqp.misfitcall", "operation called() -> Int64 = Box.directOf(mk())", "directOf"),
    ] {
        let errors = at(ns, op);
        let says = format!(
            "Descending provides anthill.prelude.WeakOrd, but not at the bindings this call to \
             {ns}.Box.{callee} needs"
        );
        assert!(errors.len() == 1 && errors[0].contains(&says), "{callee}: {errors:#?}");
    }
}
