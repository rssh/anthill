//! WI-20261105-CBRD2 — proposal 073 §6.2: A REQUIREMENT NO CALLER PASSES IS REFUSED, and a
//! query is typed where it is read.
//!
//! A rule's guard reads its dictionary from what its caller passes: a rule-body goal's route,
//! an operation body's citation, a query's own types. Nothing is read from a value when the goal
//! runs. Where nothing fixes the type a requirement is at — a variable the clause's body binds,
//! which no head column reaches, or a query's variable — it is refused at load, naming the
//! requirement and where it is open.
//!
//! ## What fails with each part backed out
//!
//! Measured with temporary switches in one build (a small binary including this file), then
//! removed. The control is every switch unset: all thirteen pass.
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
//! [`a_concrete_goal_in_a_rule_body_passes_its_dictionary`] passes under each, by design: it is
//! the route the rows above are measured against.

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
