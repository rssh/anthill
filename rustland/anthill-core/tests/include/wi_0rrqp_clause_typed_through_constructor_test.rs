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
//! | the constructor's sort unified with its position (`constrain_constructed`) | the eleven routed rows, and `a_column_typed_by_a_constructor_is_checked_at_its_citation`, `a_parameter_nothing_in_the_clause_says_is_an_open_slot`, `a_constructor_in_a_head_field_types_its_variables`, `a_dot_on_a_variable_typed_through_a_constructor_is_the_call`, `a_call_at_a_variable_the_clause_types_is_decided_at_load` |
//! | that unification made in place, not on a copy | `a_constructor_that_does_not_fit_its_position_pins_nothing` |
//! | a constant constructor read as its sort (`constrain_constant_constructor`) | `a_column_typed_by_a_constructor_is_checked_at_its_citation`, `a_parameter_nothing_in_the_clause_says_is_an_open_slot`, `a_constructor_in_a_head_field_types_its_variables`, and `wi_5g28a_paren_less_citation_test::a_bracketed_chain_followed_by_a_projection_is_a_citation` |
//! | the resolve to the end, made one step (`collect_rule_var_types`) | the eleven routed rows, `a_column_typed_by_a_constructor_is_checked_at_its_citation`, and the paren-less row above |
//! | the citation's reading of the clause's typing (`ClauseTypes`) | the eleven routed rows |
//! | the skip of a column the citation has no type for (`ClauseTypes::at_citation`) | `a_column_the_citation_gives_no_type_pins_nothing` |
//! | the meeting of two clauses' types (`join_column_types`, after `join_types`) | `a_typed_clause_meets_one_bound_at_the_sorts_parameter`, `each_clause_of_a_relation_is_met_on_its_own`, `two_clauses_that_take_a_sort_apart_are_one_relation` |
//! | the position handed to a head term's arguments (`collect_term_type_constraints`) | `a_constructor_in_a_head_field_types_its_variables` |
//! | a head term's constant read as its sort (the same function's `Term::Ref` arm) | `a_constructor_in_a_head_field_types_its_variables`, by its second half |
//! | the test that each parameter of the sort has a variable (`constrain_constructed`) | `wi1000_secondary_entry_content_test::a_dotted_declaration_name_is_not_the_entrys_content` and `wi_2kv4y_unfixed_carrier_test::a_sort_the_loader_has_refused_is_not_opened`, each by a panic |
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
//! and the four stated limits at the end of the file. Each says why at its site.
//!
//! ## Stated limits
//!
//! Four, each a row at the end of the file that passes either way:
//!
//!   * A SORT WITH TWO REQUIREMENTS ON ONE SORT is the ticket's second row and is not
//!     driven: a call cannot name a provider for each (`TypeError::ConflictingSelection` —
//!     selections are kept by the required sort alone), so no caller can show which
//!     requirement a condition reached. `wi_wn9p8_forward_soundness_test` records the same
//!     shape.
//!   * A SLOT THE ARGUMENT'S OWN TYPE SAYS is not read by a citation from an operation
//!     that holds no requirement.
//!   * A SLOT AT THE CITING OPERATION'S OWN TYPE PARAMETER is refused for a call and not
//!     for a citation.
//!   * A DRIVER RUN AS A RULE'S GOAL answers `Int64`'s own. So the rows are driven through
//!     the interpreter, as P7VP4's are.

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

/// A PARAMETER NOTHING IN THE CLAUSE SAYS IS AN OPEN SLOT. `wrap(?y)` over a `?y` only a
/// rule goal produces is a `Wrap` of an element the clause does not say, and so is `none`:
/// read back from a citation at a written instance, each is refused as a column typed by
/// an entity field at its sort's parameter is — `viaField`, which passes either way. The
/// column had no type and was returned at any.
///
/// THE REPAIR, RUN: the head says the column is a `Wrap`, and a bound's unwritten slot is
/// a variable the reader may fix.
#[test]
fn a_parameter_nothing_in_the_clause_says_is_an_open_slot() {
    let returned = |ns: &str, rule: &str, ret: &str| {
        wrap_errors(
            ns,
            &format!(
                "  fact holder(h: wrap(red))\n  {rule}\n  \
                 operation f() -> {ret} effects {{Error, Error[EmptyStream]}} = tag.head.x\n"
            ),
        )
    };
    crate::common::assert_refused_naming(
        &returned("wi0rrqp.o1", "rule tag(?x) :- holder(h: ?x)", "Wrap[T = Colour]"),
        &["expected Wrap[T = Colour], got Wrap[T = ?T]"],
        "typed by a field at its sort's parameter",
    );
    crate::common::assert_refused_naming(
        &returned("wi0rrqp.o2", "rule tag(?x) :- gen(?y), ?x <=> wrap(?y)", "Wrap[T = Colour]"),
        &["expected Wrap[T = Colour], got Wrap[T = ?T]"],
        "typed by a constructor over an element only a rule goal produces",
    );
    crate::common::assert_refused_naming(
        &returned("wi0rrqp.o3", "rule tag(?x) :- ?x <=> none", "Option[T = Int64]"),
        &["expected Option[T = Int64], got Option[T = ?T]"],
        "a constant constructor of a parametric sort",
    );
    let ns = "wi0rrqp.o4";
    let src = program(
        ns,
        &format!(
            "{WRAP}  rule tag(?x: Wrap) :- gen(?y), ?x <=> wrap(?y)\n  \
             operation f() -> Wrap[T = Colour] effects {{Error, Error[EmptyStream]}} = tag.head.x\n"
        ),
    );
    let mut interp = crate::common::interp_for(&src);
    let out = interp.call(&format!("{ns}.f"), &[]).expect("the bounded column is returned");
    let rendered = match &out {
        Value::Node(occ) => {
            anthill_core::persistence::print::TermPrinter::new(interp.kb()).print_occurrence(occ)
        }
        other => format!("{other:?}"),
    };
    assert!(rendered.contains("red"), "the first row, `wrap(red)`, got `{rendered}`");
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

/// A CONSTRUCTOR THAT DOES NOT FIT ITS POSITION PINS NOTHING. `h`'s field is a `W2[A = E,
/// B = Int64]` and the clause writes a `w2` whose `b` is a `String`. The two agree on `A`
/// before they disagree on `B`; kept, that agreement tied `?x` to `h`'s `E`, and `r(q, 5)`
/// over a `q: H[E = Colour]` was refused for an `Int64` where a `Colour` was owed.
#[test]
fn a_constructor_that_does_not_fit_its_position_pins_nothing() {
    let errs = wrap_errors(
        "wi0rrqp.misfit",
        "  sort W2[A, B]\n    entity w2(a: A, b: B)\n  end\n  \
         sort H[E]\n    entity h(inner: W2[A = E, B = Int64])\n  end\n  \
         import NS.W2.{w2}\n  \
         import NS.H.{h}\n  \
         rule r(?q, ?x) :- ?q <=> h(inner: w2(a: ?x, b: \"s\"))\n  \
         operation f(q: H[E = Colour]) -> Int64 effects {Error} = r(q, 5).takeN(3).length()\n",
    );
    assert!(errs.is_empty(), "`?x` is tied to nothing: {errs:?}");
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

/// STATED LIMIT — passes either way. Cited with an argument whose OWN type says the slot,
/// from an operation that holds no requirement, the clause's condition is read at the
/// element's type alone: `Int64`'s own `-1`, where the member operation called on the same
/// value answers through the value's `Ascending`. The clause's typing says `?p` is a
/// `Box[T = t, O = o]` and its condition is `WeakOrd[T = t]`; nothing says that `o` is what
/// answers it.
#[test]
fn a_slot_the_arguments_own_type_says_is_not_read() {
    let ns = "wi0rrqp.own";
    let src = program(ns, &format!("{BOX}{OUTSIDE}"));
    let at = |entry: &str| drive(&src, &format!("{ns}.Out.{entry}"));
    assert_eq!(
        (at("citedAtItsType"), at("calledAtItsType")),
        (-1, -4),
        "the citation derives `Int64`'s own; the call reads the value's `Ascending`",
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

/// STATED LIMIT — passes either way. A driver run as a rule's GOAL: the selection `desc`
/// writes in its own body for an operation-level `requires` does not reach the citation
/// under it, and the clause derives `Int64`'s own. Run by the interpreter the same driver
/// answers `4` (`the_tie_is_the_constructors_outside_any_sort`).
#[test]
fn a_driver_run_as_a_rules_goal_derives() {
    let ns = "wi0rrqp.goal";
    let mut kb = crate::common::load_kb_with(&program(
        ns,
        &format!("{PR_DECLS}{PR_DRIVER}  rule q(?r) :- ?r <=> Driver.desc()\n"),
    ));
    assert_eq!(
        crate::common::one_definite_int(&mut kb, &format!("{ns}.q")),
        Some(-1),
        "`Driver.desc()` as a goal",
    );
}

/// STATED LIMIT — passes either way, and why the ticket's second row is not driven. A sort
/// with two requirements on one sort cannot be given a provider for each, at different
/// types and by name: the member operation's own call is refused.
#[test]
fn two_requirements_on_one_sort_cannot_each_be_given_a_provider() {
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program(
            "wi0rrqp.pair",
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
    operation keyDirect(p: Self) -> Int64 = match p case entry(k1, k2, v1, v2) -> WeakOrd.compare(k1, k2)
  end
  sort Driver
    import NS.Pair2.{entry}
    operation go() -> Int64 =
      Pair2.keyDirect[K = Int64, V = String, OK = Descending, OV = StrSeven](entry(k1: 1, k2: 5, v1: "a", v2: "b"))
  end
"#,
        )),
        &["two providers are selected for anthill.prelude.WeakOrd"],
        "a provider for `OK` and another for `OV`",
    );
}
