//! WI-20261122-517Y5 — AN OPERATION'S CONTRACT AS WRITTEN.
//!
//! `OperationInfo.requires` / `.ensures` hold one `Value` per clause, and a ground clause is a
//! hash-consed term: it has no location (`kb.term_span` answered `None` for every clause
//! measured), and two goals written alike are one term. The clauses the loader appends —
//! WI-320's `EffectsRuntime[Effects = E]`, WI-201's `Spec[Member = ?P]` — ride in the same
//! list, told apart only by a `pub(super)` reader that knows the first by its functor and the
//! second not at all. Now the loader records, where it converts them,
//! `KnowledgeBase::operation_contract(op)`: each written clause with its site, the stored
//! clause and its goals' occurrences, each at the span the goal is written over — the
//! parser's `ContractGoal::written`, parentheses and a named slot's binder included; and
//! apart from them the clauses it added, with the rule that added each.
//! `KnowledgeBase::source_text(site)` reads the text a site covers.
//!
//! BACK-OUT, measured 2026-11-22 one part at a time over this file (10 rows, green on the
//! change):
//!  * [M] goal occurrences materialized from the term (`materialize_from_handle`, the
//!    `term_spans` side-table) instead of at the goal's written span — 5 fail:
//!    `each_written_clause_reads_as_written`, `a_named_slot_is_read_from_its_binder`,
//!    `a_parenthesized_goal_reads_with_its_parentheses`,
//!    `a_binding_through_an_alias_keeps_its_occurrence` (a goal has no text: the table has no
//!    entry for the term, and the node is at `0..0`) and
//!    `a_goal_written_in_two_clauses_has_two_sites` (both at `0..0`);
//!  * [C] a clause's site from its first goal only — 4 fail: `each_written_clause_reads_as_written`,
//!    `a_named_slot_is_read_from_its_binder`, `a_parenthesized_goal_reads_with_its_parentheses`,
//!    `a_binding_through_an_alias_keeps_its_occurrence` (the clause cut after its first goal);
//!  * [W] the loader locating goals and clauses by their TERMS' spans, not the written ones —
//!    2 fail: `a_parenthesized_goal_reads_with_its_parentheses` (`x > 0), y > 0`) and
//!    `a_named_slot_is_read_from_its_binder` (`Show[T = A], b > 0`) — what the first version
//!    of this item did, found by the second `/code-review`;
//!  * [P] the parser giving a goal its term's span (`ContractGoal::written`) — 1 fails:
//!    `a_parenthesized_goal_reads_with_its_parentheses`;
//!  * [B] the parser giving a slot's goal its type's span, not the binder's — 1 fails:
//!    `a_named_slot_is_read_from_its_binder`;
//!  * [N] a binding's occurrence wrapped in a node of the recorded goal's own (spliced, so it
//!    reads the same through the view) — 2 fail: `a_binding_through_an_alias_keeps_its_occurrence`
//!    and `a_copy_of_the_kb_keeps_the_contract`;
//!  * [A] every added clause recorded as `EffectsRow` — 1 fails: `the_loaders_clauses_are_apart`;
//!  * [R] a written clause headed by `EffectsRuntime` taken for the loader's (dropped from the
//!    written ones, as a reader by functor would) — 1 fails: `the_loaders_clauses_are_apart`;
//!  * [D] the deep copy dropping the record — 1 fails: `a_copy_of_the_kb_keeps_the_contract`;
//!  * [O] `OperationInfo.requires` built with the loader's clauses before the written ones —
//!    1 fails: `the_stored_clauses_are_operation_infos`;
//!  * [E] `source_text` answering an empty span with `Some("")` — 1 fails:
//!    `an_empty_span_has_no_text`.
//! CONTROL, passing either way by design: `only_a_converted_declaration_has_a_contract`.

use crate::common::load_kb_with;
use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::node_occurrence::Expr;
use anthill_core::kb::op_info::{lookup_operation_info, AddedBy, OperationContract, WrittenClause};
use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::term_view::views_structurally_equal;
use anthill_core::kb::KnowledgeBase;

const SRC: &str = r#"
namespace test.y5
  import anthill.prelude.{Int64, Bool, EffectsRuntime}

  sort Store
    sort State = ?
    operation peek(s: State) -> Bool = true
  end

  fact pair(1, 2)
  fact pair(3, 4)

  sort Box
    entity box(n: Int64)
  end

  sort Money = Int64
  sort Show[T]
    operation show(x: T) -> Int64
  end
  sort IntShow
    entity intshow
    provides Show[T = Int64]
    operation show(x: Int64) -> Int64 = x + 1
  end

  sort Ops
    effects E = ?
    operation step(x: Int64) -> Int64
      requires x > 0
      requires pair(x, ?k), x != ?k
      ensures pair(x, ?k), result > ?k
      effects E
  end

  sort Views
    operation look(s: Store.State) -> Bool
      requires pair(1, 2)
  end

  sort Asks
    operation ask(x: Int64) -> Int64
      requires Show[T = Money], x > 0
    operation pick[A](a: A, b: Int64) -> Int64
      requires s: Show[T = A], b > 0
    operation pickLater[A](a: A, b: Int64) -> Int64
      requires b > 0
      requires s: Show[T = A]
  end

  sort Parens
    operation both(x: Int64, y: Int64) -> Int64
      requires (x > 0), y > 0
      ensures (result = x)
  end

  sort Runs
    effects E = ?
    operation run(x: Int64) -> Int64
      requires EffectsRuntime[Effects = E]
      requires x > 0
      effects E
  end
end
"#;

const OPS: [&str; 7] = [
    "test.y5.Ops.step",
    "test.y5.Views.look",
    "test.y5.Asks.ask",
    "test.y5.Asks.pick",
    "test.y5.Asks.pickLater",
    "test.y5.Parens.both",
    "test.y5.Runs.run",
];

fn sym(kb: &KnowledgeBase, name: &str) -> Symbol {
    kb.try_resolve_symbol(name)
        .unwrap_or_else(|| panic!("`{name}` names nothing"))
}

fn contract<'k>(kb: &'k KnowledgeBase, op: &str) -> &'k OperationContract {
    kb.operation_contract(sym(kb, op))
        .unwrap_or_else(|| panic!("`{op}` has no recorded contract"))
}

fn term(v: &Value) -> TermId {
    match v {
        Value::Term { id, .. } => *id,
        other => panic!("expected a term, got {other:?}"),
    }
}

fn clause_text<'k>(kb: &'k KnowledgeBase, clause: &WrittenClause) -> &'k str {
    kb.source_text(clause.site)
        .unwrap_or_else(|| panic!("no text under {:?}", clause.site))
}

fn goal_texts<'k>(kb: &'k KnowledgeBase, clause: &WrittenClause) -> Vec<&'k str> {
    clause
        .goals
        .iter()
        .map(|g| {
            kb.source_text(g.span)
                .unwrap_or_else(|| panic!("no text under {:?}", g.span))
        })
        .collect()
}

fn texts<'k>(kb: &'k KnowledgeBase, clauses: &[WrittenClause]) -> Vec<&'k str> {
    clauses.iter().map(|cl| clause_text(kb, cl)).collect()
}

/// The goals the stored clause holds: the clause itself for a clause of one goal, the
/// arguments of its `conjunction(…)` otherwise — on whichever carrier it is stored.
fn stored_goals(kb: &KnowledgeBase, clause: &WrittenClause) -> Vec<Value> {
    if clause.goals.len() == 1 {
        return vec![clause.stored.clone()];
    }
    match &clause.stored {
        Value::Term { id, .. } => match kb.get_term(*id) {
            Term::Fn { functor, pos_args, .. } if kb.local_name_of(*functor) == "conjunction" => {
                pos_args.iter().map(|t| Value::term(*t)).collect()
            }
            other => panic!("a clause of several goals is not a conjunction: {other:?}"),
        },
        Value::Entity { functor, pos, .. } if kb.local_name_of(*functor) == "conjunction" => pos.to_vec(),
        other => panic!("a clause of several goals is not a conjunction: {other:?}"),
    }
}

fn head_name(kb: &KnowledgeBase, t: TermId) -> String {
    match kb.get_term(t) {
        Term::Fn { functor, .. } => kb.qualified_name_of(*functor).to_string(),
        other => panic!("not an application: {other:?}"),
    }
}

/// Every written clause, and every goal in it, reads back as the text it is written as; the
/// clauses are in source order, requires and ensures apart; and the site is the clause's
/// place in its file, as a message names it.
#[test]
fn each_written_clause_reads_as_written() {
    let kb = load_kb_with(SRC);
    let c = contract(&kb, "test.y5.Ops.step");
    assert_eq!(texts(&kb, &c.requires), ["x > 0", "pair(x, ?k), x != ?k"]);
    assert_eq!(texts(&kb, &c.ensures), ["pair(x, ?k), result > ?k"]);
    assert_eq!(goal_texts(&kb, &c.requires[0]), ["x > 0"]);
    assert_eq!(goal_texts(&kb, &c.requires[1]), ["pair(x, ?k)", "x != ?k"]);
    assert_eq!(goal_texts(&kb, &c.ensures[0]), ["pair(x, ?k)", "result > ?k"]);

    let (line, text) = SRC
        .lines()
        .enumerate()
        .find(|(_, l)| l.contains("requires pair(x, ?k)"))
        .expect("the fixture writes it");
    let col = text.find("pair(x, ?k)").expect("on that line") + 1;
    let rendered = kb.render_site(c.requires[1].site);
    let mut parts = rendered.rsplit(':');
    let (at_col, at_line) = (parts.next(), parts.next());
    assert_eq!(
        (at_line, at_col),
        (Some((line + 1).to_string().as_str()), Some(col.to_string().as_str())),
        "{rendered}"
    );
}

/// The record lines up with `OperationInfo` by position: its `requires` is the written
/// clauses' stored values and then the loader's, its `ensures` the written ones'; and each
/// goal's occurrence is the goal the stored clause holds at that position. Compared through
/// the view, so a clause stored as an application over a binding's occurrence (`ask`'s)
/// is compared as one.
#[test]
fn the_stored_clauses_are_operation_infos() {
    let kb = load_kb_with(SRC);
    for op in OPS {
        let info = lookup_operation_info(&kb, sym(&kb, op)).expect("an operation");
        let c = contract(&kb, op);
        let recorded: Vec<&Value> = c
            .requires
            .iter()
            .map(|cl| &cl.stored)
            .chain(c.added_requires.iter().map(|a| &a.stored))
            .collect();
        let ensures: Vec<&Value> = c.ensures.iter().map(|cl| &cl.stored).collect();
        for (kind, held, ours) in [("requires", &info.requires, recorded), ("ensures", &info.ensures, ensures)] {
            assert_eq!(held.len(), ours.len(), "{op} {kind}");
            for (i, (h, o)) in held.iter().zip(ours).enumerate() {
                assert!(views_structurally_equal(&kb, h, o), "{op} {kind}[{i}]");
            }
        }
        for clause in c.requires.iter().chain(&c.ensures) {
            let stored = stored_goals(&kb, clause);
            assert_eq!(clause.goals.len(), stored.len(), "{op}: `{}`", clause_text(&kb, clause));
            for (goal, held) in clause.goals.iter().zip(&stored) {
                assert!(
                    views_structurally_equal(&kb, goal, held),
                    "{op}: the goal at `{}` is not the one the stored clause holds",
                    kb.source_text(goal.span).unwrap_or("?")
                );
            }
        }
    }
}

/// THE TRAP `term_spans` CANNOT MEET: `pair(x, ?k)` is written in a requires and in an
/// ensures of one operation, with one `?k` (one variable per operation), so both are one
/// hash-consed term. The record gives each its own site.
#[test]
fn a_goal_written_in_two_clauses_has_two_sites() {
    let kb = load_kb_with(SRC);
    let c = contract(&kb, "test.y5.Ops.step");
    let in_requires = &c.requires[1].goals[0];
    let in_ensures = &c.ensures[0].goals[0];
    // CONTROL: the two are one term, so nothing keyed by the term can tell them apart.
    assert_eq!(
        term(&stored_goals(&kb, &c.requires[1])[0]),
        term(&stored_goals(&kb, &c.ensures[0])[0]),
        "the fixture must write one goal twice"
    );
    assert_ne!(in_requires.span, in_ensures.span);
    assert!(in_requires.span.start() < c.requires[1].goals[1].span.start());
    assert!(c.requires[1].site.start() < c.ensures[0].site.start());
}

/// A goal written as a named requirement slot is converted from its type alone (WI-840);
/// its written text, and its clause's, begin at the binder — first in its clause, or in a
/// later clause than the first (the slot's index runs over all of the operation's goals).
#[test]
fn a_named_slot_is_read_from_its_binder() {
    let kb = load_kb_with(SRC);
    let c = contract(&kb, "test.y5.Asks.pick");
    assert_eq!(texts(&kb, &c.requires), ["s: Show[T = A], b > 0"]);
    assert_eq!(goal_texts(&kb, &c.requires[0]), ["s: Show[T = A]", "b > 0"]);
    let later = contract(&kb, "test.y5.Asks.pickLater");
    assert_eq!(texts(&kb, &later.requires), ["b > 0", "s: Show[T = A]"]);
}

/// A parenthesized goal converts to its inner term; it is written with its parentheses, and
/// so is the clause it opens or closes — the shape of a spec's frame conditions,
/// `(s.a = result.a), (s.b = result.b)`.
#[test]
fn a_parenthesized_goal_reads_with_its_parentheses() {
    let kb = load_kb_with(SRC);
    let c = contract(&kb, "test.y5.Parens.both");
    assert_eq!(texts(&kb, &c.requires), ["(x > 0), y > 0"]);
    assert_eq!(goal_texts(&kb, &c.requires[0]), ["(x > 0)", "y > 0"]);
    assert_eq!(texts(&kb, &c.ensures), ["(result = x)"]);
}

/// An empty span is how a node with no location is marked; it has no text.
#[test]
fn an_empty_span_has_no_text() {
    let kb = load_kb_with(SRC);
    let site = contract(&kb, "test.y5.Ops.step").requires[0].site;
    let empty = anthill_core::span::SourceSpan::new(site.source, site.start(), site.start());
    assert_eq!(kb.source_text(empty), None);
}

/// A binding written through a type alias (`Show[T = Money]`, `sort Money = Int64`) is held
/// by the stored goal on the occurrence that keeps the name; the recorded goal holds THAT
/// occurrence, not a copy made from the type's term, and reads as written.
#[test]
fn a_binding_through_an_alias_keeps_its_occurrence() {
    let kb = load_kb_with(SRC);
    let c = contract(&kb, "test.y5.Asks.ask");
    assert_eq!(texts(&kb, &c.requires), ["Show[T = Money], x > 0"]);
    assert_eq!(goal_texts(&kb, &c.requires[0]), ["Show[T = Money]", "x > 0"]);

    let stored = stored_goals(&kb, &c.requires[0]);
    let Value::Entity { named, .. } = &stored[0] else {
        panic!("the goal over an alias is stored as an application: {:?}", stored[0]);
    };
    let [(t_key, Value::Node(held))] = &named[..] else {
        panic!("one binding, on its occurrence: {named:?}");
    };
    let Some(Expr::Apply { named_args, .. }) = c.requires[0].goals[0].as_expr() else {
        panic!("the recorded goal is an application");
    };
    let [(key, ours)] = &named_args[..] else {
        panic!("the recorded goal has the one binding: {named_args:?}");
    };
    assert_eq!(key, t_key);
    assert!(std::rc::Rc::ptr_eq(ours, held), "the binding's own occurrence");
}

/// The loader's clauses are not read as written: each is listed apart, by the rule that
/// added it, after the written ones.
#[test]
fn the_loaders_clauses_are_apart() {
    let kb = load_kb_with(SRC);

    let step = contract(&kb, "test.y5.Ops.step");
    let by: Vec<AddedBy> = step.added_requires.iter().map(|a| a.by).collect();
    assert_eq!(by, [AddedBy::EffectsRow], "`effects E` over a row variable");
    assert_eq!(
        head_name(&kb, term(&step.added_requires[0].stored)),
        "anthill.prelude.EffectsRuntime"
    );

    let look = contract(&kb, "test.y5.Views.look");
    assert_eq!(texts(&kb, &look.requires), ["pair(1, 2)"]);
    let by: Vec<AddedBy> = look.added_requires.iter().map(|a| a.by).collect();
    assert_eq!(by, [AddedBy::BareSpecMember], "a bare `Store.State` parameter");
    assert_eq!(head_name(&kb, term(&look.added_requires[0].stored)), "test.y5.Store");
    assert!(look.ensures.is_empty());

    // A clause the author writes with the functor the loader's carries is the author's: a
    // reader that told them apart by the clause's functor (`is_effects_runtime_clause`)
    // would take both for the loader's.
    let run = contract(&kb, "test.y5.Runs.run");
    assert_eq!(texts(&kb, &run.requires), ["EffectsRuntime[Effects = E]", "x > 0"]);
    let written_head = match &run.requires[0].stored {
        Value::Term { id, .. } => head_name(&kb, *id),
        Value::Entity { functor, .. } => kb.qualified_name_of(*functor).to_string(),
        other => panic!("a clause on an unexpected carrier: {other:?}"),
    };
    assert_eq!(written_head, "anthill.prelude.EffectsRuntime", "CONTROL: one functor for both");
    let by: Vec<AddedBy> = run.added_requires.iter().map(|a| a.by).collect();
    assert_eq!(by, [AddedBy::EffectsRow], "the loader's own, beside the written one");
}

/// A copy of the KB (the test suites' shared base is one) carries the record over whole.
#[test]
fn a_copy_of_the_kb_keeps_the_contract() {
    let kb = load_kb_with(SRC);
    let copy = kb.deep_clone().expect("the KB copies");
    for op in OPS {
        let (a, b) = (contract(&kb, op), contract(&copy, op));
        let read = |kb: &KnowledgeBase, c: &OperationContract| {
            c.requires
                .iter()
                .chain(&c.ensures)
                .map(|cl| {
                    (
                        clause_text(kb, cl).to_string(),
                        cl.goals.iter().map(|g| g.span).collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(read(&kb, a), read(&copy, b), "{op}");
        let ours = |c: &OperationContract| -> Vec<Value> {
            c.requires
                .iter()
                .chain(&c.ensures)
                .map(|cl| cl.stored.clone())
                .chain(c.added_requires.iter().map(|x| x.stored.clone()))
                .collect()
        };
        let (sa, sb) = (ours(a), ours(b));
        assert_eq!(sa.len(), sb.len(), "{op}");
        for (x, y) in sa.iter().zip(&sb) {
            assert!(views_structurally_equal(&kb, x, y), "{op}: a stored clause");
        }
        let by = |c: &OperationContract| c.added_requires.iter().map(|x| x.by).collect::<Vec<_>>();
        assert_eq!(by(a), by(b), "{op}");
    }
    // In the copy, the goal over an alias still holds the very occurrence its stored clause
    // holds: the copier keeps sharing within the copy.
    let c = contract(&copy, "test.y5.Asks.ask");
    let stored = stored_goals(&copy, &c.requires[0]);
    let Value::Entity { named, .. } = &stored[0] else {
        panic!("the goal over an alias is stored as an application in the copy");
    };
    let [(_, Value::Node(held))] = &named[..] else {
        panic!("one binding, on its occurrence: {named:?}");
    };
    let Some(Expr::Apply { named_args, .. }) = c.requires[0].goals[0].as_expr() else {
        panic!("the recorded goal is an application in the copy");
    };
    assert!(std::rc::Rc::ptr_eq(&named_args[0].1, held), "one occurrence in the copy");
}

/// A symbol that names no operation has no record. A derived member has one, and it is empty:
/// its derivation's text is converted as a declaration, and writes no clause (measured — the
/// first version of this row expected `None` here and failed).
#[test]
fn only_a_converted_declaration_has_a_contract() {
    let kb = load_kb_with(SRC);
    assert!(kb.operation_contract(sym(&kb, "test.y5.Ops")).is_none(), "a sort");
    assert!(kb.operation_contract(sym(&kb, "test.y5.pair")).is_none(), "a relation");
    let derived = sym(&kb, "test.y5.Box.eq");
    assert!(
        lookup_operation_info(&kb, derived).is_some(),
        "the entity's derived `eq` is an operation"
    );
    let c = kb
        .operation_contract(derived)
        .expect("the derived `eq` was converted as a declaration");
    assert!(
        c.requires.is_empty() && c.ensures.is_empty() && c.added_requires.is_empty(),
        "the derived `eq` writes no clause: {c:?}"
    );
}
