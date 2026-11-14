//! WI-20261105-CBRD2 — proposal 073 §6.2: A REQUIREMENT NO CALLER PASSES IS REFUSED, and a
//! query is typed where it is read.
//!
//! A rule's guard reads its dictionary from what its caller passes: a rule-body goal's route,
//! an operation body's citation, a query's own types. Nothing is read from a value when the goal
//! runs. Where nothing fixes the type a requirement is at — a variable the clause's body binds,
//! which no head column reaches, or a query's variable — it is refused at load, naming the
//! requirement and where it is open.
//!
//! A value at a sort with abstract values is an instance in a rule as in an operation (073 §2):
//! a column the clause types at such a sort holds instances, a goal, a query or an operation
//! body's citation that passes a provider's value there pairs it with the provider's dictionary
//! at load, and so does a rule body's call at a parameter of that type. A query's variable there
//! is refused: a query has no caller to pass the instance. A variable `<=>` makes a
//! construction is of the construction's type where it fits the variable's other positions, so
//! a call on it is decided at load.
//!
//! ## What fails with each part backed out
//!
//! Measured with temporary switches in one build, then removed. The control is every switch
//! unset: every row passes.
//!
//! * the query's routing (`route_query_goals` handing the query back unrouted):
//!   [`a_query_is_typed_where_it_is_read`],
//!   [`a_composed_dictionary_answers_a_list_and_refuses_an_open_element`],
//!   [`a_querys_bracket_fixes_the_type_parameter`],
//!   [`a_bracket_on_a_relation_that_declares_nothing_is_refused`] and the query half of
//!   [`a_goal_no_load_typed_is_an_error_when_it_runs`];
//! * a goal at a type nothing fixes left unrouted, as before (`GuardRoute::Open` not refused):
//!   [`a_goal_at_a_variable_no_head_column_reaches_is_refused`],
//!   [`a_query_is_typed_where_it_is_read`] and
//!   [`a_composed_dictionary_answers_a_list_and_refuses_an_open_element`];
//! * the guard's read at run time with nothing supplied fetching from the value again:
//!   [`a_goal_no_load_typed_is_an_error_when_it_runs`];
//! * the citation's carrier not bound when the clause opens (the marker's `carrier_` entries
//!   unread): [`a_querys_bracket_fixes_the_type_parameter`] and
//!   [`a_rule_bodys_bracket_fixes_the_type_parameter`] — `keep[A = Int64](?x, ?t)` answers the
//!   `Bool` row too;
//! * the query's goals not typed together (`stamp_query_variable_types` off):
//!   [`a_query_types_a_variable_across_its_goals`];
//! * a call in a rule body at a variable no head column reaches woven as before:
//!   [`a_call_at_a_variable_no_head_column_reaches_is_refused`];
//! * an operation body's citation leaving a requirement open left unrouted:
//!   [`a_citation_from_an_operation_leaving_a_requirement_open_is_refused`].
//!
//! * the bridge entering a spec call's member with no stamps for its own `requires`, the member
//!   deriving them from the values: [`a_member_is_handed_the_calls_dictionaries`];
//! * the bridge ignoring the dictionary the typer built for a call into another sort, deriving
//!   the frame from the values: [`a_call_into_another_sort_enters_through_its_built_dictionary`].
//!
//! * a variable `<=>` makes a construction's left at its other positions' type
//!   (`narrow_to_construction` off): [`a_call_at_a_variable_the_clause_types_is_decided_at_load`]
//!   and the later-binding half of [`a_goal_pairs_a_value_at_a_column_that_holds_instances`],
//!   with GFS6A's four rows that bind `?s <=> car(n: 1)` after the call;
//! * a goal's or a query's value at a column that holds instances left unpaired
//!   (`pack_instance_arguments` answering nothing): [`a_goal_pairs_a_value_at_a_column_that_holds_instances`],
//!   [`a_value_with_no_instance_at_the_column_is_refused`], the query half of
//!   [`a_value_no_load_paired_is_an_error_when_it_runs`], and eight GFS6A rows;
//! * a rule body's call left unpaired (`pack_call_arguments` answering nothing):
//!   [`a_rule_bodys_call_pairs_its_argument_at_load`];
//! * an operation body's citation of such a column left unpaired (the instance walk's relation
//!   arm off): GFS6A's `an_operation_citing_the_clause_answers`;
//! * the read of a value no load paired deriving its dictionary again:
//!   [`a_value_no_load_paired_is_an_error_when_it_runs`];
//! * a typed head's type test reading the pair, not the value it holds: GFS6A's two
//!   typed-head rows, QMFC5's and X9PB4's self-representing rows;
//! * the dictionary built by the guard's fetch, which takes `Cap`'s one parameter for its
//!   carrier, not by the operation body's goal: QMFC5's `Cap[P = Int64]` row.
//! * a later load typing again a body that holds a paired value (`occ_holds_instance_pair`
//!   off): [`a_paired_body_is_not_typed_again_by_a_later_load`];
//! * a query's variable at a column that holds instances passed as it is (decided with the
//!   user 2026-11-14: refused): [`a_query_variable_at_a_column_that_holds_instances_is_refused`]
//!   and GFS6A's `a_dictionary_never_bound_is_a_conditional_answer`;
//! * a query's two columns, one at the abstract sort and one at a provider, not met at the
//!   provider (`stamp_query_variable_types`): the `carSrc` half of
//!   [`a_query_variable_at_a_column_that_holds_instances_is_refused`];
//! * each of three fixes /code-review found, alone:
//!   [`values_from_calls_and_a_later_receiver_reach_the_instance`] — a call's result of a
//!   provider at a column of the abstract sort unified with it (`provides_the_slot` off), a
//!   result handed to a rule opened to its carrier's value (`carried_for_host` in the bridge),
//!   the read's witness taken from the first argument.
//!
//! * a `<=>` not handing the clause's type of its variable to the other side
//!   (`unify_side_hint` off): [`a_result_only_call_at_the_type_the_clause_gives_is_decided_at_load`]
//!   and the `?t: Float` spelling of [`a_result_only_call_at_a_type_nothing_provides_is_refused`];
//! * a rule body's call of a member with no argument at the spec's carrier left to the rule-body
//!   check, as before (`judged_at_the_call` reading an evaluated body alone):
//!   [`a_result_only_call_at_a_type_nothing_provides_is_refused`] and 9WVT7's
//!   `the_bracketed_call_in_a_rule_body_is_refused_where_nothing_provides_it`;
//! * such a call at a type nothing fixes left to the clause (`open_result_only_call` answering
//!   nothing): [`a_result_only_call_at_a_type_nothing_fixes_is_refused`];
//! * a guard of the spec at any type taken as the call's (`at_the_guard` answering yes), and the
//!   `<=>` not handing a clause type parameter's variable to the call (`is_rule_type_variable`
//!   off), each alone: the `?t: B` beside `Z[A]` spelling of
//!   [`a_result_only_call_at_a_type_nothing_fixes_is_refused`].
//!
//! * a query's spec-op calls not typed where it is read (`typed_spec_op_calls` typing nothing):
//!   [`a_querys_spec_op_call_at_a_type_nothing_provides_or_fixes_is_refused`], WI-1044's two
//!   query-refusal rows, NAR1X's and CYNPE's query refusals;
//! * a query's call left open by its typing let through (`calls_left_to_a_clause` answering
//!   nothing): the one-provider half of
//!   [`a_querys_spec_op_call_at_a_type_nothing_provides_or_fixes_is_refused`];
//! * a query's call held to a rule body's effect refusal (the `RuleBodyEffect` filter off):
//!   [`an_effectful_call_in_a_query_keeps_its_run_time_verdict`];
//! * a `--match` browse typed as a query (`convert_patterns_untyped` not used for it): the CLI's
//!   `wi1044_query_supplier_tie_test::a_two_supplier_browse_is_not_refused`;
//! * found by /code-review, each measured on the tree before its fix: a query variable bound in
//!   the env by a name another shares (the anonymous `?`) — the anonymous half of
//!   [`a_querys_spec_op_call_at_a_type_nothing_provides_or_fixes_is_refused`], which answered
//!   conditionally.
//! * a defaulted member of a spec something provides read as owing no instance, as before
//!   (`defaulted_member_owes_an_instance` reading the abstract member alone):
//!   [`a_defaulted_member_at_an_open_carrier_is_refused`], and the rows of WI-1037, WI-1040 and
//!   WI-1044 that a decision of the user (2026-11-14) moved to the refusal (GP8JC's, whose
//!   clauses now guard each column, pass either way);
//! * a rule body's defaulted call that names no carrier left to run its default
//!   (`open_defaulted_call` answering nothing): measured, before the static rule, on the
//!   `Desc.dflt()` half of [`a_defaulted_member_at_an_open_carrier_is_refused`], QMFC5's two
//!   nullary rows, its refining row's second refusal, and 96ZTM's two bare twins. A static
//!   operation with a body is the spec's own since (decided with the user 2026-11-14): those
//!   rows now call a body-less member, or run the body, and what this part refuses is measured
//!   in `wi_cbrd2_static_operation_test`, with the rest of that rule.
//!
//! * a comparison at a type the clause leaves open left unclassified, as before (its hand-off to
//!   the clause off in `check_apply_call`): [`an_untyped_comparison_in_a_rule_body_is_refused`],
//!   [`an_untyped_comparison_in_a_query_is_refused_where_it_is_read`] and SM910's
//!   `an_untyped_comparison_is_refused_and_a_declared_one_answers`;
//! * the call's dictionary built for such a comparison all the same: the query row above,
//!   refused in other words (`PartialEq` at the operand's placeholder type, ambiguous among
//!   providers);
//! * a query's comparison left untyped (`owes_an_instance` excluding an operation with a
//!   primitive, as before): the query row above, and WI-879's
//!   `a_cross_sort_literal_pair_is_undecided_and_diagnosed`;
//! * an untyped query variable's placeholder type read as fixing a requirement
//!   (`own_requirements_fixed_at` without its `type_mentions_type_var` leg): the query row above;
//! * a query's guard read off its first column alone (`guard_carrier_at_goal` taking a
//!   variable's type): [`a_querys_guard_is_at_the_type_any_column_fixes`], and SM910's row
//!   above, whose `related(?x, 3)` was refused.
//!
//! [`a_declared_or_typed_comparison_answers`] passes under each of the last five, by design: it
//! is what the comparison rule leaves as it was.
//!
//! [`a_querys_spec_op_call_is_typed_where_it_is_read`] passes with the query typing backed out,
//! by design: the value its call reached at run time is the one its typing decides, and the row
//! says the typing keeps it.
//!
//! [`a_concrete_goal_in_a_rule_body_passes_its_dictionary`] passes under each, by design: it is
//! the route the rows above are measured against. So does
//! [`a_guard_the_sorts_requires_or_the_bracket_supplies_a_result_only_call`], what supplies a
//! result-only call the three parts above leave alone.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// 073 §6.2's first program: `Marker` with an operation, a `src` holding an `Int64` and a
/// `Bool`, `keep` declaring `Marker[A]`, and `Int64` and `Bool` providing it at 1 and 2.
/// `tail` is written at the end of the namespace.
fn marker(tail: &str) -> String {
    format!(
        r#"namespace p.q2
  import anthill.prelude.{{Int64, Bool}}
  sort Marker
    sort T = ?
    operation tag(x: T) -> Int64
  end
  fact src(1)
  fact src(true)
  rule keep[A](?x: A, ?t) :- src(?x), Marker[A], Marker.tag(?x, ?t)
{tail}end
namespace anthill.prelude.Int64
  import p.q2.Marker
  provides Marker[T = Int64]
  operation tag(x: Int64) -> Int64 = 1
end
namespace anthill.prelude.Bool
  import p.q2.Marker
  provides Marker[T = Bool]
  operation tag(x: Bool) -> Int64 = 2
end
"#
    )
}

/// 073 §6.2's second program: `ListShow` provides `Show` at a list under `Show` at its
/// element, `Int64` provides it at 1.
fn list_show(tail: &str) -> String {
    format!(
        r#"namespace c
  import anthill.prelude.{{Int64, List}}
  sort Show
    sort T = ?
    operation show(x: T) -> Int64
  end
  sort ListShow
    import c.Show
    sort E = ?
    requires Show[T = E]
    provides Show[T = List[T = E]]
    operation show(x: List[T = E]) -> Int64 = match x case nil -> 100 case cons(h, t) -> Show.show(h) + 10
  end
  fact src([1, 2])
  fact src([])
  rule keep[A](?x: A, ?t) :- src(?x), Show[A], Show.show(?x, ?t)
{tail}end
namespace anthill.prelude.Int64
  import c.Show
  provides Show[T = Int64]
  operation show(x: Int64) -> Int64 = 1
end
"#
    )
}

/// The definite integer answers of `pattern` at its last argument.
fn ints(kb: &mut KnowledgeBase, pattern: &str) -> Vec<i64> {
    crate::common::pattern_last_ints(kb, pattern)
}

/// `pattern` is refused where the query is read, naming each of `tokens`.
fn refused(kb: &mut KnowledgeBase, pattern: &str, tokens: &[&str]) {
    crate::common::assert_refused_naming(&crate::common::query_pattern_refusals(kb, pattern), tokens, pattern);
}

/// `answer(?t) :- keep(?x, ?t)` is refused at load: `?x` is an `Int64` in one `src` fact and a
/// `Bool` in the other, a type no head column of `answer` reaches, so no caller can pass `keep`
/// its `Marker[A]`. It answered `1` and `2`, each read from the value.
#[test]
fn a_goal_at_a_variable_no_head_column_reaches_is_refused() {
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&marker("  rule answer(?t) :- keep(?x, ?t)\n")),
        &["answer.body", "`Marker` at `keep`'s `A`", "no head column reaches"],
        "a goal at a variable no head column reaches",
    );
}

/// A query is typed where it is read, as a rule body's goal is: `keep(1, ?t)` is a call at
/// `A = Int64` and passes `Int64`'s `Marker`, `keep(true, ?t)` `Bool`'s, and `keep(?x, ?t)`
/// leaves `A` open and is refused naming it. A type nothing provides at is refused too.
#[test]
fn a_query_is_typed_where_it_is_read() {
    let mut kb = crate::common::load_kb_with(&marker(""));
    assert_eq!(ints(&mut kb, "p.q2.keep(1, ?t)"), [1]);
    assert_eq!(ints(&mut kb, "p.q2.keep(true, ?t)"), [2]);
    refused(&mut kb, "p.q2.keep(?x, ?t)", &["`Marker` at `keep`'s `A`", "a query has no caller"]);
    refused(&mut kb, "p.q2.keep(1.5, ?t)", &["p.q2.Marker[T = anthill.prelude.Float]"]);
}

/// The goals of one query, typed together where they are read: `Err` with the refusals, or the
/// definite integer answers at the last goal's last argument.
fn conjunction(kb: &mut KnowledgeBase, patterns: &[&str]) -> Result<Vec<i64>, Vec<String>> {
    use anthill_core::kb::load;
    use anthill_core::kb::term_view::{TermView, ViewHead};
    let src: String = patterns.iter().map(|p| format!("fact {p}\n")).collect();
    let parsed = anthill_core::parse::parse(&src).expect("parse the query");
    let errs = load::scan_query_definitions(kb, &[&parsed]);
    assert!(errs.is_empty(), "{errs:?}");
    let ids: Vec<_> = parsed
        .items
        .iter()
        .filter_map(|item| match item {
            anthill_core::parse::ir::Item::Fact(f) => Some(f.term),
            _ => None,
        })
        .collect();
    let scope = kb.global_scope();
    let mut var_map = std::collections::HashMap::new();
    let goals = load::convert_query_terms(kb, &parsed, &ids, scope, &mut var_map)
        .map_err(|errs| errs.iter().map(|e| e.to_string()).collect::<Vec<_>>())?;
    let last = load::query_goal_as_written(kb, goals.last().expect("a goal"));
    let ViewHead::Functor { pos_arity, .. } = TermView::head(&last, kb) else {
        panic!("the last goal is an application");
    };
    let t = TermView::pos_arg(&last, kb, pos_arity - 1).expect("an argument").to_value();
    let mut out: Vec<i64> = kb
        .resolve(&goals, &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .map(|s| {
            let v = kb.reify_value(&t, &s.subst);
            crate::common::scalar_int(kb, &v).expect("an integer")
        })
        .collect();
    out.sort_unstable();
    Ok(out)
}

/// A query's goals are typed together, as a rule body's are: in `src(?x), keep(?x, ?t)` over a
/// `src` of `Int64`s, `?x` is an `Int64` where `keep` reads it, and the query answers `1` per
/// row, as `rule both(?t) :- src(?x), keep(?x, ?t)` does. Over 073 §6.2's `src`, an `Int64` and
/// a `Bool`, `?x` has no one type, and the conjunction is refused naming `A`.
#[test]
fn a_query_types_a_variable_across_its_goals() {
    let ints = marker("  fact num(1)\n  fact num(2)\n  rule keepAny[A](?x: A, ?t) :- Marker[A], Marker.tag(?x, ?t)\n");
    let mut kb = crate::common::load_kb_with(&ints);
    assert_eq!(conjunction(&mut kb, &["p.q2.num(?x)", "p.q2.keepAny(?x, ?t)"]), Ok(vec![1, 1]));
    let refused = conjunction(&mut kb, &["p.q2.src(?x)", "p.q2.keepAny(?x, ?t)"]).expect_err("`?x` has no one type");
    crate::common::assert_refused_naming(&refused, &["`Marker` at `keepAny`'s `A`"], "the mixed `src`");
}

/// A query's bracket binds what the relation declares (060.1 §2) and fixes the clause's `A`:
/// `keep[A = Int64](?x, ?t)` answers `1`, the `Int64` row alone — the `Bool` row is no value of
/// the `A` the citation fixed. It answered both rows where it was a rule body's goal, the
/// citation's dictionary passed but the clause's `A` read from each value.
#[test]
fn a_querys_bracket_fixes_the_type_parameter() {
    let mut kb = crate::common::load_kb_with(&marker(""));
    assert_eq!(ints(&mut kb, "p.q2.keep[A = Int64](?x, ?t)"), [1]);
    assert_eq!(ints(&mut kb, "p.q2.keep[A = anthill.prelude.Bool](?x, ?t)"), [2]);
}

/// The same bracket on a rule body's goal: `viaInt(?t) :- keep[A = Int64](?x, ?t)` answers `1`
/// alone. On the tree before (bf311200) it answered `1` and `2`.
#[test]
fn a_rule_bodys_bracket_fixes_the_type_parameter() {
    let mut kb = crate::common::load_kb_with(&marker("  rule viaInt(?t) :- keep[A = Int64](?x, ?t)\n"));
    assert_eq!(ints(&mut kb, "p.q2.viaInt(?t)"), [1]);
}

/// The control: a rule body's goal at a concrete type builds its callee's dictionary at load
/// (060.1 §1), and answers. Passes with each part backed out, by design.
#[test]
fn a_concrete_goal_in_a_rule_body_passes_its_dictionary() {
    let mut kb = crate::common::load_kb_with(&marker("  rule viaOne(?t) :- keep(1, ?t)\n"));
    assert_eq!(ints(&mut kb, "p.q2.viaOne(?t)"), [1]);
}

/// A conditional provision is composed at load (060.1 §1): `keep([1, 2], ?t)` passes `ListShow`'s
/// dictionary over `Int64`'s and answers `11`. `keep([], ?t)` leaves the element open and is
/// refused; written with the dictionary the citation passes, `keep[A = List[T = Int64]](?x,
/// ?t)`, the `[]` row answers `100`. `answer(?t) :- keep(?x, ?t)` is refused at load, `?x`'s
/// type `List[T = ?]` open where it is written; it answered `11` and failed the `[]` row in
/// silence.
#[test]
fn a_composed_dictionary_answers_a_list_and_refuses_an_open_element() {
    let mut kb = crate::common::load_kb_with(&list_show(""));
    assert_eq!(ints(&mut kb, "c.keep([1, 2], ?t)"), [11]);
    refused(&mut kb, "c.keep([], ?t)", &["`Show` at `keep`'s `A`"]);
    assert_eq!(
        ints(&mut kb, "c.keep[A = anthill.prelude.List[T = anthill.prelude.Int64]](?x, ?t)"),
        [11, 100]
    );
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&list_show("  rule answer(?t) :- keep(?x, ?t)\n")),
        &["answer.body", "`Show` at `keep`'s `A`"],
        "a goal whose argument's type is open",
    );
}

/// A bracket on a query goal of a relation that declares nothing for it to bind is refused by
/// name, as on a rule body's goal: `src[A = Int64](?x)`.
#[test]
fn a_bracket_on_a_relation_that_declares_nothing_is_refused() {
    let mut kb = crate::common::load_kb_with(&marker(""));
    refused(&mut kb, "p.q2.src[A = anthill.prelude.Int64](?x)", &["p.q2.src.type_arg", "a callee with no type-parameter list"]);
}

/// A call in a rule body at a variable no head column reaches is refused at load, as a goal
/// there is: `Marker.tag(?x, ?t)` after `src(?x)`, `?x` an `Int64` and a `Bool`. It was
/// dispatched by each value's sort.
#[test]
fn a_call_at_a_variable_no_head_column_reaches_is_refused() {
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&marker("  rule tags(?t) :- src(?x), Marker.tag(?x, ?t)\n")),
        &["tags.body", "a requirement of `Marker`", "no head column of the clause reaches"],
        "a call at a variable no head column reaches",
    );
}

/// An operation body's citation that leaves a cited guard's type open has no caller to pass it,
/// and is refused at load: `length(keep.takeN(5))` reads every row of `keep`, an `Int64` and a
/// `Bool`. `keep(1)` fixes it and answers.
#[test]
fn a_citation_from_an_operation_leaving_a_requirement_open_is_refused() {
    let ops = "  import anthill.prelude.{List, Error}\n  import anthill.prelude.List.{length}\n  \
               operation cited() -> Int64 effects Error = length(keep(1).takeN(5))\n";
    assert_eq!(crate::common::run_int64(&marker(ops), "p.q2.cited"), Ok(1));
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&marker(&format!(
            "{ops}  operation whole() -> Int64 effects Error = length(keep.takeN(5))\n"
        ))),
        &["`p.q2.Marker[T = ?]`", "the citation leaves the type it is at open"],
        "a citation reading every row",
    );
}

/// A goal no load typed — built by the host and handed to the resolver — that reaches a guard is
/// passed nothing: an error when it runs, naming the requirement, never a dictionary read from
/// the value. The same goal asked as a query answers.
#[test]
fn a_goal_no_load_typed_is_an_error_when_it_runs() {
    use anthill_core::kb::term::{Literal, Term};
    use smallvec::SmallVec;
    let mut kb = crate::common::load_kb_with(&marker(""));
    let keep = kb.try_resolve_symbol("p.q2.keep").expect("keep");
    let one = kb.alloc(Term::Const(Literal::Int(1)));
    let t = kb.intern("t");
    let t = kb.fresh_var(t);
    let t = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(t)));
    let goal = kb.alloc(Term::Fn {
        functor: keep,
        pos_args: SmallVec::from_slice(&[one, t]),
        named_args: SmallVec::new(),
    });
    let (sols, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    assert!(sols.iter().all(|s| !s.is_definite()), "no definite answer: {} row(s)", sols.len());
    assert!(
        stats.errors.iter().any(|e| e.message.contains("`p.q2.Marker` of a clause was passed by no caller")),
        "{:?}",
        stats.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
    assert_eq!(ints(&mut kb, "p.q2.keep(1, ?t)"), [1], "asked as a query");
}

// ── the SLD bridge: a rule body's call carries what the typer built ──────────────

/// A spec call whose member has `requires` of its own: `Desc.pair(Coin.coin(n: 5), Mk.ints())`
/// in a rule body runs `Coin.pair`, and the member's `Tagger[T = U]` at `U = List[T = Int64]` is
/// the dictionary the typer built for the spec operation's own `requires`, handed to the member
/// under its names, as an operation body's call is: `110`, `ListTag`'s 100 plus 10. The value
/// `[]` carries `List[T = ?]`, so the bridge's derivation from it found no `Tagger` and the goal
/// failed in silence.
#[test]
fn a_member_is_handed_the_calls_dictionaries() {
    let mut kb = crate::common::load_kb_with(MEMBER);
    assert_eq!(ints(&mut kb, "mm.viaEmpty(?r)"), [110]);
    assert_eq!(crate::common::run_int64(MEMBER, "mm.opEmpty"), Ok(110), "the operation body's twin");
}

/// A call into another sort's operation at a concrete instance enters through the dictionary the
/// typer built for it: `Holder[T = Leaf, D = Rival].show(leaf())` in a rule body answers `9`,
/// the witness its bracket names, as the operation body's twin does. The bridge derived the
/// frame from the value instead, which names no witness, and the goal was left undecided.
#[test]
fn a_call_into_another_sort_enters_through_its_built_dictionary() {
    let mut kb = crate::common::load_kb_with(BUNDLE);
    assert_eq!(ints(&mut kb, "bb.viaRival(?x)"), [9]);
    assert_eq!(crate::common::run_int64(BUNDLE, "bb.opRival"), Ok(9), "the operation body's twin");
}

// ── a sort with abstract values: its column holds instances ─────────────────────────────

/// 073 §2's abstract sort: `Sp` receives on itself and has no constructors, `Car` provides it
/// with members of its own, `Van` provides nothing, and `dflted` reads `Sp.dflt` at its column,
/// behind a read of `Sp`'s dictionary. `tail` is written at the end of the namespace.
fn sp(tail: &str) -> String {
    format!(
        "namespace p.sp\n  import anthill.prelude.{{Int64}}\n  \
         sort Sp\n    operation size(s: Sp) -> Int64\n    operation dflt(s: Sp) -> Int64 = 7\n    \
         operation pick(k: Int64, s: Sp) -> Int64\n  end\n  \
         sort Car\n    entity car(n: Int64)\n    provides Sp\n    \
         operation size(c: Car) -> Int64 = 42\n    operation dflt(c: Car) -> Int64 = 43\n    \
         operation pick(k: Int64, c: Car) -> Int64 = 44\n  end\n  \
         sort Van\n    entity van(n: Int64)\n  end\n  \
         rule dflted(?s, ?x) :- Sp.dflt(?s, ?x)\n{tail}end\n"
    )
}

/// A call at a variable the clause's typing makes a `Car` is decided at load, as an operation
/// body's call on a `Car` is: in `late(?r) :- Sp.dflt(?s, ?r), ?s <=> car(n: 1)`, `?s` is at
/// `Sp` where the call takes it and a `Car` where `<=>` builds it, so it is a `Car`, and the call
/// is `Car`'s, with no read before it. It was woven behind a read that took `Car`'s dictionary
/// from the value once `?s` was bound.
#[test]
fn a_call_at_a_variable_the_clause_types_is_decided_at_load() {
    let mut kb = crate::common::load_kb_with(&sp("  rule late(?r) :- Sp.dflt(?s, ?r), ?s <=> car(n: 1)\n"));
    assert!(
        crate::common::body_calls(&kb, "p.sp.late")
            .iter()
            .all(|(callee, _, _)| callee != "find_dictionary"),
        "no read: {:?}",
        crate::common::body_calls(&kb, "p.sp.late"),
    );
    assert_eq!(ints(&mut kb, "p.sp.late(?r)"), [43]);
}

/// A column a clause types at a sort with abstract values holds instances: a goal that passes a
/// `Car` there pairs it with `Car`'s dictionary of `Sp` at load, as an operation body passing it
/// at a parameter typed `Sp` does, and the clause's read takes the instance's. So `dflted(car(n:
/// 1), ?r)` answers `43` as a rule body's goal, as a query, and with the `Car` bound by a later
/// goal (`dflted(?s, ?r), ?s <=> car(n: 1)`); the read took `Car`'s dictionary from the value.
#[test]
fn a_goal_pairs_a_value_at_a_column_that_holds_instances() {
    let mut kb = crate::common::load_kb_with(&sp(
        "  rule viaCar(?r) :- dflted(car(n: 1), ?r)\n  \
         rule viaVar(?r) :- dflted(?s, ?r), ?s <=> car(n: 1)\n",
    ));
    assert_eq!(ints(&mut kb, "p.sp.viaCar(?r)"), [43]);
    assert_eq!(ints(&mut kb, "p.sp.viaVar(?r)"), [43]);
    assert_eq!(ints(&mut kb, "p.sp.dflted(p.sp.Car.car(n: 1), ?r)"), [43], "asked as a query");
}

/// A value whose sort has no instance of `Sp` at the column is refused where the goal is read: a
/// `Van`, as a rule body's goal and as a query. It failed when the goal ran.
#[test]
fn a_value_with_no_instance_at_the_column_is_refused() {
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&sp("  rule viaVan(?r) :- dflted(van(n: 1), ?r)\n")),
        &["dflted", "Sp", "Van"],
        "a `Van` at a column of `Sp`",
    );
    let mut kb = crate::common::load_kb_with(&sp(""));
    refused(&mut kb, "p.sp.dflted(p.sp.Van.van(n: 1), ?r)", &["dflted", "Sp", "Van"]);
}

/// A query's variable at a column that holds instances is refused where the query is read: a
/// query has no caller to pass the instance, and another of its goals that would bind it is no
/// caller either — `dflted(?s, ?r)` alone, and after `src(?s)`, whose column is an `Sp` too. A
/// variable another goal types at a provider is paired as its value is: after `carSrc(?s)`, a
/// `Car`, the conjunction answers `43`, whichever column is read first. The first two answered
/// conditionally.
#[test]
fn a_query_variable_at_a_column_that_holds_instances_is_refused() {
    let mut kb = crate::common::load_kb_with(&sp(
        "  sort Mk\n    operation mkSp() -> Sp = car(n: 2)\n  end\n  \
         rule src(?s) :- ?s <=> Mk.mkSp()\n  \
         fact carSrc(car(n: 1))\n",
    ));
    refused(&mut kb, "p.sp.dflted(?s, ?r)", &["dflted", "a variable of the query", "Sp"]);
    let both = conjunction(&mut kb, &["p.sp.src(?s)", "p.sp.dflted(?s, ?r)"]).expect_err("refused");
    crate::common::assert_refused_naming(&both, &["dflted", "a variable of the query"], "after src");
    assert_eq!(conjunction(&mut kb, &["p.sp.carSrc(?s)", "p.sp.dflted(?s, ?r)"]), Ok(vec![43]));
    assert_eq!(
        conjunction(&mut kb, &["p.sp.dflted(?s, ?r)", "p.sp.carSrc(?s)", "p.sp.dflted(?s, ?r)"]),
        Ok(vec![43]),
        "the abstract column read first",
    );
}

/// Values that reach a column of `Sp` from a call: `Mk.mkCar()`, a `Car`, fits the column as a
/// provider's value does and is paired at load; `Mk.mkSp()` answers an `Sp`, an instance, which
/// the bridge hands the rule as it is. And a call whose receiver is its second parameter reads
/// the instance there: `Sp.pick(1, ?s, ?r)`. Each answers `Car`'s member. Before, the first
/// was refused at load (`expected Car, got Sp`), the second's instance was opened to the bare
/// `car(n: 2)`, and the third's read took the literal `1` for its witness.
#[test]
fn values_from_calls_and_a_later_receiver_reach_the_instance() {
    let mut kb = crate::common::load_kb_with(&sp(
        "  sort Mk\n    operation mkCar() -> Car = car(n: 1)\n    operation mkSp() -> Sp = car(n: 2)\n  end\n  \
         rule viaMkCar(?r) :- dflted(Mk.mkCar(), ?r)\n  \
         rule viaMkSp(?r) :- dflted(Mk.mkSp(), ?r)\n  \
         rule picked(?s, ?r) :- Sp.pick(1, ?s, ?r)\n  \
         rule viaPick(?r) :- picked(car(n: 1), ?r)\n",
    ));
    assert_eq!(ints(&mut kb, "p.sp.viaMkCar(?r)"), [43]);
    assert_eq!(ints(&mut kb, "p.sp.viaMkSp(?r)"), [43]);
    assert_eq!(ints(&mut kb, "p.sp.viaPick(?r)"), [44]);
}

/// A goal no load typed that passes a value of a provider at such a column passes no instance:
/// an error when the clause's read meets it, never a dictionary read from the value. The same
/// goal asked as a query answers.
#[test]
fn a_value_no_load_paired_is_an_error_when_it_runs() {
    use anthill_core::kb::term::{Literal, Term};
    use smallvec::SmallVec;
    let mut kb = crate::common::load_kb_with(&sp(""));
    let dflted = kb.try_resolve_symbol("p.sp.dflted").expect("dflted");
    let car = kb.try_resolve_symbol("p.sp.Car.car").expect("car");
    let n = kb.try_resolve_symbol("p.sp.Car.car.n").expect("car's field");
    let one = kb.alloc(Term::Const(Literal::Int(1)));
    let value = kb.alloc(Term::Fn {
        functor: car,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(n, one)]),
    });
    let r = kb.intern("r");
    let r = kb.fresh_var(r);
    let r = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(r)));
    let goal = kb.alloc(Term::Fn {
        functor: dflted,
        pos_args: SmallVec::from_slice(&[value, r]),
        named_args: SmallVec::new(),
    });
    let (sols, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    assert!(sols.iter().all(|s| !s.is_definite()), "no definite answer: {} row(s)", sols.len());
    assert!(
        stats.errors.iter().any(|e| e.message.contains("a value at `p.sp.Sp` that is no instance")),
        "{:?}",
        stats.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
    assert_eq!(ints(&mut kb, "p.sp.dflted(p.sp.Car.car(n: 1), ?r)"), [43], "asked as a query");
}

/// A rule body's call passes a value at a parameter typed by a sort with abstract values as an
/// operation body's does: paired at load with the dictionary of the type the clause gives it.
/// `total(Bag.bag(x: 1))` at `total(s: Sp)` passes `Bag[T = Int64]`'s `Sp`, which holds where
/// `Tagger[T = Int64]` does, and answers `40`, as `opTotal` does. The SLD bridge paired the
/// value by its sort, `Bag` at no `T`, where the provision's condition is not decided, and a
/// debug build aborted.
#[test]
fn a_rule_bodys_call_pairs_its_argument_at_load() {
    let mut kb = crate::common::load_kb_with(CONDITIONAL);
    assert_eq!(ints(&mut kb, "p.bag.viaTotal(?r)"), [40]);
    assert_eq!(crate::common::run_int64(CONDITIONAL, "p.bag.opTotal"), Ok(40), "the operation body's twin");
}

/// A body that holds a value paired at load was typed by that load: a later load does not type
/// it again, and `viaTotal` still answers `40` after one, as does the goal of `p.sp` paired at a
/// column, `viaCar`. Typed again, the later load was refused: the pair's dictionary is spliced
/// in, `expected surface expression, got bottom / post-elaboration form`.
#[test]
fn a_paired_body_is_not_typed_again_by_a_later_load() {
    let mut kb = crate::common::load_kb_with(CONDITIONAL);
    let later = "namespace p.later\n  import anthill.prelude.{Int64}\n  rule one(1) :- true\nend\n";
    crate::common::expect_loaded(crate::common::load_in_a_later_call(&mut kb, later, Default::default()));
    assert_eq!(ints(&mut kb, "p.bag.viaTotal(?r)"), [40]);
    let mut kb = crate::common::load_kb_with(&sp("  rule viaCar(?r) :- dflted(car(n: 1), ?r)\n"));
    crate::common::expect_loaded(crate::common::load_in_a_later_call(&mut kb, later, Default::default()));
    assert_eq!(ints(&mut kb, "p.sp.viaCar(?r)"), [43]);
}

const CONDITIONAL: &str = r#"namespace p.bag
  import anthill.prelude.{Int64}
  sort Tagger
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort Sp
    operation dflt(s: Sp) -> Int64 = 7
  end
  sort Bag
    sort T = ?
    entity bag(x: T)
    requires Tagger[T = T]
    provides Sp
    operation dflt(b: Bag) -> Int64 = 40
  end
  operation total(s: Sp) -> Int64 = Sp.dflt(s)
  rule viaTotal(?r) :- ?r <=> total(Bag.bag(x: 1))
  operation opTotal() -> Int64 = total(Bag.bag(x: 1))
end
namespace anthill.prelude.Int64
  import p.bag.Tagger
  provides Tagger[T = Int64]
  operation tag(x: Int64) -> Int64 = 1
end
"#;

const MEMBER: &str = r#"namespace mm
  import anthill.prelude.{Int64, List}
  import anthill.prelude.Numeric.{add}
  sort Tagger
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort ListTag
    sort E = ?
    requires Tagger[T = E]
    provides Tagger[T = List[T = E]]
    operation tag(x: List[T = E]) -> Int64 = 100
  end
  sort Desc
    sort T = ?
    operation pair[U](x: T, y: U) -> Int64 requires Tagger[T = U]
  end
  sort Coin
    entity coin(n: Int64)
    provides Desc[T = Coin]
    operation pair[U](x: Coin, y: U) -> Int64 requires Tagger[T = U] = add(10, Tagger.tag(y))
  end
  sort Mk
    operation ints() -> List[T = Int64] = []
  end
  rule viaEmpty(?r) :- ?r <=> Desc.pair(Coin.coin(n: 5), Mk.ints())
  operation opEmpty() -> Int64 = Desc.pair(Coin.coin(n: 5), Mk.ints())
end
namespace anthill.prelude.Int64
  import mm.Tagger
  provides Tagger[T = Int64]
  operation tag(x: Int64) -> Int64 = 1
end
"#;

const BUNDLE: &str = r#"namespace bb
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation label(x: T) -> Int64
  end
  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation label(x: Leaf) -> Int64 = 7
  end
  sort Rival
    provides Desc[T = Leaf]
    operation label(x: Leaf) -> Int64 = 9
  end
  sort Holder[T]
    requires D: Desc[T = T]
    operation show(x: T) -> Int64 = Desc.label(x)
  end
  rule viaRival(?x) :- ?x <=> Holder[T = Leaf, D = Rival].show(leaf())
  operation opRival() -> Int64 = Holder[T = Leaf, D = Rival].show(leaf())
end
"#;

/// A member that names its spec in its result alone: `Z.zz()` has no argument at `Z`'s
/// carrier, so its instance is the one its bracket, or the type expected of its result, names.
/// `Int64` provides `Z` at `0` and `Tag`; `Holder` requires `Z` at its `H`; `src` holds an
/// `Int64`.
/// `tail` is written at the end of the namespace.
fn zz(tail: &str) -> String {
    format!(
        r#"namespace p.zz
  import anthill.prelude.{{Int64, Float}}
  sort Z
    sort T = ?
    operation zz() -> T
  end
  sort Tag
    sort T = ?
    operation tg(x: T) -> Int64
  end
  sort Holder
    import p.zz.Z
    sort H = ?
    requires Z[T = H]
    rule held(?t: H) :- ?t <=> Z.zz()
  end
  fact src(1)
{tail}end
namespace anthill.prelude.Int64
  import p.zz.{{Z, Tag}}
  provides Z[T = Int64]
  operation zz() -> Int64 = 0
  provides Tag[T = Int64]
  operation tg(x: Int64) -> Int64 = 5
end
"#
    )
}

use crate::common::pattern_answer_counts as answers;

/// A rule body's call of a member with no argument at the spec's carrier is judged as an
/// operation body's is: at a type its bracket or the clause gives it, a type nothing provides is
/// refused at load — `Z[T = Float].zz()` as a value and as the goal it is, `Z.zz()` at a head
/// column typed `Float`, under `not(…)`. Each loaded and answered conditionally: the rule-body
/// requirement check reads a carrier off the call's arguments, and this call has none.
#[test]
fn a_result_only_call_at_a_type_nothing_provides_is_refused() {
    for rule in [
        "rule r(?t) :- ?t <=> Z[T = Float].zz()",
        "rule r(?t) :- Z[T = Float].zz(?t)",
        "rule r(?t: Float) :- ?t <=> Z.zz()",
        "rule r() :- src(?x), not(?x <=> Z[T = Float].zz())",
    ] {
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&zz(&format!("  {rule}\n"))),
            &["p.zz.Z.zz", "`anthill.prelude.Float` provides no `p.zz.Z`"],
            rule,
        );
    }
}

/// At a type nothing fixes, where the clause supplies none — no guard of `Z` at the call's type,
/// no `requires` of the sort it is written in — the call is refused naming the instance to
/// write, as an operation body's `let x = Z.zz()` is: `?t <=> Z.zz()` with `?t` untyped, the call
/// in a lambda's body, a comparison's operand, which the other operand types in neither body,
/// and a call at `B` beside a guard of `Z` at `A`. Each loaded; the first answered
/// conditionally, and the last `A`'s `0` at `B`.
#[test]
fn a_result_only_call_at_a_type_nothing_fixes_is_refused() {
    for rule in [
        "rule r(?t) :- ?t <=> Z.zz()",
        "rule r(?r) :- ?f <=> lambda () -> Z.zz(), ?r <=> 1",
        "rule r() :- src(?x), ?x = Z.zz()",
        "rule r[A, B](?a: A, ?t: B) :- Z[A], Tag[B], ?t <=> Z.zz()",
    ] {
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&zz(&format!("  {rule}\n"))),
            &["p.zz.Z.zz", "the instance written at the call, `Z[T = …].zz(…)`"],
            rule,
        );
    }
}

/// A `<=>` expects of the side opposite a rule variable the type the clause gives the variable,
/// so the call there is decided at load, as `operation o() -> Int64 = Z.zz()` is: at a head
/// column typed `Int64`, at `?t = 0` after it, beside a guard, at `src`'s `Int64` (whose `1` is
/// no `0`), under `not(…)`. Each answered conditionally, `unify(?_, zz)` left over.
#[test]
fn a_result_only_call_at_the_type_the_clause_gives_is_decided_at_load() {
    let mut kb = crate::common::load_kb_with(&zz(
        "  rule head(?t: Int64) :- ?t <=> Z.zz()\n  \
         rule later(?t) :- ?t <=> Z.zz(), ?t = 0\n  \
         rule guarded(?t: Int64) :- Z[T = Int64], ?t <=> Z.zz()\n  \
         rule fromSrc(?t) :- src(?t), ?t <=> Z.zz()\n  \
         rule negated() :- src(?x), not(?x <=> Z.zz())\n",
    ));
    assert_eq!(ints(&mut kb, "p.zz.head(?t)"), [0]);
    assert_eq!(ints(&mut kb, "p.zz.later(?t)"), [0]);
    assert_eq!(ints(&mut kb, "p.zz.guarded(?t)"), [0]);
    assert_eq!(answers(&mut kb, "p.zz.fromSrc(?t)"), (0, 0), "`1` is no `0`");
    assert_eq!(answers(&mut kb, "p.zz.negated()"), (1, 1));
}

/// CONTROL, passing either way by design: what supplies the call where its type is open — the
/// clause's guard of `Z` at its type parameter, cited at `A = Int64`; the `requires` of the sort
/// the rule is written in, cited at `H = Int64`; the bracket.
#[test]
fn a_guard_the_sorts_requires_or_the_bracket_supplies_a_result_only_call() {
    let mut kb = crate::common::load_kb_with(&zz(
        "  rule viaGuard[A](?t: A) :- Z[A], ?t <=> Z.zz()\n  \
         rule viaGuardGoal[A](?t: A) :- Z[A], Z.zz(?t)\n  \
         rule viaHolder(?t) :- Holder[H = Int64].held(?t)\n  \
         rule viaBracket(?t) :- ?t <=> Z[T = Int64].zz()\n",
    ));
    assert_eq!(ints(&mut kb, "p.zz.viaGuard[A = Int64](?t)"), [0]);
    assert_eq!(ints(&mut kb, "p.zz.viaGuardGoal[A = Int64](?t)"), [0]);
    assert_eq!(ints(&mut kb, "p.zz.viaHolder(?t)"), [0]);
    assert_eq!(ints(&mut kb, "p.zz.viaBracket(?t)"), [0]);
}

/// A query's call of a spec operation is typed where the query is read, as a rule body's goal
/// is: at a type a provider answers it is decided there, as the member it reaches —
/// `Marker.tag(1, ?t)` is `Int64.tag` and `Marker.tag(true, ?t)` `Bool.tag`, as a goal and as
/// the right of `<=>`.
#[test]
fn a_querys_spec_op_call_is_typed_where_it_is_read() {
    let mut kb = crate::common::load_kb_with(&marker(""));
    assert_eq!(ints(&mut kb, "p.q2.Marker.tag(1, ?t)"), [1]);
    assert_eq!(ints(&mut kb, "p.q2.Marker.tag(true, ?t)"), [2]);
    assert_eq!(ints(&mut kb, "anthill.kernel.unify(p.q2.Marker.tag(1), ?t)"), [1]);
}

/// …and at a type nothing provides, or a type nothing fixes, it is refused where the query is
/// read, a query having no caller to pass the instance and nothing reading it from a value when
/// the goal runs: `Marker.tag(1.5, ?t)` (`Float` provides no `Marker`); `Marker.tag(?x, ?t)`
/// beside two providers, which the call selects none of, and so with an anonymous `?` beside
/// another one a goal types; and beside one, `Tag.tg(?x, ?r)`, `?r
/// <=> Tag.tg(?x)` and `not(Tag.tg(?x, 3))`, which the one provider does not answer for an `?x`
/// nothing types; and over a member that names its spec in its result alone, `Z.zz(?t)`. Each
/// answered conditionally.
#[test]
fn a_querys_spec_op_call_at_a_type_nothing_provides_or_fixes_is_refused() {
    let mut kb = crate::common::load_kb_with(&marker(""));
    refused(
        &mut kb,
        "p.q2.Marker.tag(1.5, ?t)",
        &["p.q2.Marker.tag", "`anthill.prelude.Float` provides no `p.q2.Marker`"],
    );
    // An anonymous `?` is no other's: the one `src` types does not type the call's.
    for open in ["p.q2.Marker.tag(?x, ?t)", "anthill.kernel.and(p.q2.src(?), p.q2.Marker.tag(?, ?t))"] {
        refused(&mut kb, open, &["ambiguous dispatch of `p.q2.Marker.tag`", "the call selects none"]);
    }
    let mut kb = crate::common::load_kb_with(&zz(""));
    for open in [
        "p.zz.Tag.tg(?x, ?r)",
        "anthill.kernel.unify(?r, p.zz.Tag.tg(?x))",
        "not(p.zz.Tag.tg(?x, 3))",
    ] {
        refused(&mut kb, open, &["p.zz.Tag.tg", "a query has no caller"]);
    }
    refused(&mut kb, "p.zz.Z.zz(?t)", &["p.zz.Z.zz", "`Z[T = …].zz(…)`"]);
}

/// CONTROL, passing either way by design: a query's equality is not typed by this pass (the
/// equality index's row of this ticket), and a structural browse is not typed at all
/// (`wi1044_query_supplier_tie_test::a_two_supplier_browse_is_not_refused`). `?t = 1` beside a
/// call whose type the query fixes answers.
#[test]
fn an_equality_beside_a_typed_call_is_not_typed_as_a_call() {
    let mut kb = crate::common::load_kb_with(&marker(""));
    assert_eq!(
        crate::common::pattern_answer_counts(
            &mut kb,
            "anthill.kernel.and(p.q2.Marker.tag(1, ?t), ?t = 1)"
        ),
        (1, 1)
    );
}

/// What a query's call may perform is not this typing's question: a spec operation's call
/// that performs `Clock`, at a type its provider answers, is not refused where the query is
/// read, as a rule body's call is ("a rule body performs no effect"), and answers nothing, as
/// it did before the query was typed.
#[test]
fn an_effectful_call_in_a_query_keeps_its_run_time_verdict() {
    let src = r#"namespace p.eff
  import anthill.prelude.Int64
  import anthill.prelude.Time.Clock
  sort Clk
    sort T = ?
    operation stamp(x: T) -> Int64 effects {Clock}
  end
end
namespace anthill.prelude.Int64
  import p.eff.Clk
  import anthill.prelude.Time.Clock
  provides Clk[T = Int64]
  operation stamp(x: Int64) -> Int64 effects {Clock} = 3
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let pattern = "p.eff.Clk.stamp(1, ?r)";
    assert!(crate::common::query_pattern_refusals(&mut kb, pattern).is_empty(), "not refused");
    assert_eq!(answers(&mut kb, pattern), (0, 0));
}

/// A defaulted member of a spec something provides, at a carrier nothing types, owes the
/// instance there as its body-less twin does (decided with the user 2026-11-14): refused where the
/// query is read, and in a rule body at a type no head column reaches; at a known carrier it
/// answers the carrier's member. It answered conditionally, and the rule body by value. A member
/// that names no carrier at all (`Desc.dflt()`) is the spec's own, which no provider overrides
/// (decided with the user 2026-11-14), and runs its body at no instance.
#[test]
fn a_defaulted_member_at_an_open_carrier_is_refused() {
    let src = |tail: &str| {
        format!(
            r#"namespace p.dflt
  import anthill.prelude.Int64
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
    operation dflt() -> Int64 = 2
  end
  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
  sort Twig
    entity twig
    provides Desc[T = Twig]
    operation describe(x: Twig) -> Int64 = 5
  end
  fact pick(leaf())
  fact pick(twig())
{tail}end
"#
        )
    };
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&src("  rule answer(?r) :- pick(?x), Desc.describe(?x, ?r)\n")),
        &["answer.body", "`Desc`", "no head column of the clause reaches"],
        "a rule body's call at a type no head column reaches",
    );
    // A member that names no carrier at all is the spec's own (no provider overrides a static
    // operation with a body), and in a spec that requires nothing and has no abstract member it
    // runs at no instance: `2`, unbracketed or at `Leaf`, as a value and as the goal it is.
    let mut kb = crate::common::load_kb_with(&src(
        "  rule nullary(?v) :- ?v <=> Desc.dflt()\n  \
         rule nullaryGoal(?v) :- Desc.dflt(?v)\n  \
         rule bracketed(?v) :- ?v <=> Desc[T = Leaf].dflt()\n",
    ));
    refused(&mut kb, "p.dflt.Desc.describe(?x, ?r)", &["p.dflt.Desc.describe", "a query has no caller"]);
    assert_eq!(ints(&mut kb, "p.dflt.Desc.describe(p.dflt.Leaf.leaf(), ?r)"), [7]);
    for rel in ["nullary", "nullaryGoal", "bracketed"] {
        assert_eq!(ints(&mut kb, &format!("p.dflt.{rel}(?v)")), [2], "{rel}");
    }
}

/// Comparisons (item 4): `typed[A]` declares `PartialOrd` at its parameter, `H` requires `Ord`
/// of its `T`; `tail` is written at the end of the namespace.
fn ordering(tail: &str) -> String {
    format!(
        r#"namespace p.ord
  import anthill.prelude.{{Int64, Bool, PartialOrd, Ord}}
  import anthill.prelude.PartialOrd.{{gte, gt, lt}}
  fact mixed(1)
  fact mixed(true)
  rule typed[A](?a: A, ?b: A) :- PartialOrd[T = A], gte(?a, ?b)
  sort H
    sort T = ?
    requires Ord[T = T]
    rule big(?a: T, ?b: T) :- gt(?a, ?b)
  end
{tail}end
"#
    )
}

/// A comparison at a type the clause leaves open and declares nothing for is a call of its spec's
/// member, and is refused at load as one is (decided with the user 2026-11-09): written as a
/// call, as an operator, under `not`, in an `if`, in a branch of `|`, and at a variable no head
/// column reaches, and at the `T` of a sort that requires nothing. Each loaded and was read at the
/// type its values carried when the goal ran.
#[test]
fn an_untyped_comparison_in_a_rule_body_is_refused() {
    for (rule, said) in [
        ("rule related(?a, ?b) :- gte(?a, ?b)", "a rule takes no dictionary it does not declare"),
        ("rule infix(?a, ?b) :- ?a < ?b", "a rule takes no dictionary it does not declare"),
        ("rule negated(?a, ?b) :- not(gte(?a, ?b))", "a rule takes no dictionary it does not declare"),
        ("rule iff(?a, ?b, ?c) :- ?c <=> (if gte(?a, ?b) then 1 else 0)", "a rule takes no dictionary"),
        ("rule branch(?a, ?b) :- (gte(?a, ?b) | lt(?a, ?b))", "a rule takes no dictionary it does not declare"),
        ("rule hidden() :- mixed(?a), mixed(?b), gte(?a, ?b)", "no head column of the clause reaches"),
        ("sort N\n    sort T = ?\n    rule big(?a: T, ?b: T) :- gt(?a, ?b)\n  end", "a rule takes no dictionary"),
    ] {
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&ordering(&format!("  {rule}\n"))),
            &["`PartialOrd`", said],
            rule,
        );
    }
}

/// CONTROL, passing either way by design: the repairs the refusal names answer at each citation's
/// type — a clause that declares `PartialOrd` at its parameter, and a rule of a sort that requires
/// `Ord` — and a comparison its operands type is decided where it is written.
#[test]
fn a_declared_or_typed_comparison_answers() {
    let mut kb = crate::common::load_kb_with(&ordering(
        "  rule ints() :- typed(3, 1)\n  rule floats() :- typed(1.5, 2.5)\n  \
         rule viaSort() :- H[T = Int64].big(3, 1)\n  rule lit() :- gte(3, 1)\n",
    ));
    for (relation, want) in [("ints", (1, 1)), ("floats", (0, 0)), ("viaSort", (1, 1)), ("lit", (1, 1))] {
        assert_eq!(answers(&mut kb, &format!("p.ord.{relation}()")), want, "{relation}");
    }
}

/// A query is typed where it is read, its comparisons too: one at a type nothing fixes is refused,
/// a query having no caller to pass `PartialOrd` (`gte(?a, ?b)`, `?a < ?b`, under `not`), and a
/// cross-sort literal pair is refused as a type mismatch, as in a clause. One the query's types fix
/// is decided where it is read and waits on an unbound operand (`?a < 2`). Each was read at the
/// type its values carried when it ran: the open ones answered conditionally, `1 < 1.5`
/// undecided with a warning.
#[test]
fn an_untyped_comparison_in_a_query_is_refused_where_it_is_read() {
    let mut kb = crate::common::load_kb_with(&ordering(""));
    for open in ["anthill.prelude.PartialOrd.gte(?a, ?b)", "?a < ?b", "not(?a < ?b)"] {
        refused(&mut kb, open, &["`PartialOrd`", "a query has no caller"]);
    }
    refused(&mut kb, "1 < 1.5", &["expected Int64, got Float"]);
    assert_eq!(answers(&mut kb, "anthill.prelude.PartialOrd.gte(3, 1)"), (1, 1));
    assert!(crate::common::query_pattern_refusals(&mut kb, "?a < 2").is_empty(), "`?a < 2` is at Int64");
    assert_eq!(answers(&mut kb, "?a < 2"), (0, 1), "it waits on `?a`");
}

/// A query's goal of a relation that declares a requirement at its parameter is at the type any
/// column fixes, whichever column the typed argument stands in: `typed(?x, 3)` is at `Int64`, as
/// `typed(3, ?x)` is, and `typed(?x, 3.5)` at `Float`; `typed(?x, ?y)` is refused. The first
/// column alone was read, and `typed(?x, 3)` was refused, "at a type nothing fixes", where the same
/// citation in a rule body loads.
#[test]
fn a_querys_guard_is_at_the_type_any_column_fixes() {
    let mut kb = crate::common::load_kb_with(&ordering("  rule viaRule(?x) :- typed(?x, 3)\n"));
    for at in ["p.ord.typed(?x, 3)", "p.ord.typed(3, ?x)", "p.ord.typed(?x, 3.5)"] {
        assert!(crate::common::query_pattern_refusals(&mut kb, at).is_empty(), "`{at}` is decided");
        assert_eq!(answers(&mut kb, at), (0, 1), "`{at}` waits on `?x`");
    }
    assert_eq!(answers(&mut kb, "p.ord.typed(7, 3)"), (1, 1));
    refused(&mut kb, "p.ord.typed(?x, ?y)", &["`PartialOrd` at `typed`'s `A`", "a query has no caller"]);
}
