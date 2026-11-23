//! WI-20261123-5MMGP — THE REFUTATION OF A TYPED QUERY WHOSE VARIABLES ARE ITS OWN:
//! `KnowledgeBase::refute_typed_logical_query_with(q, options)`, proof mode outside the crate.
//!
//! Before: the search in proof mode was crate-private, and a client reached a refutation only
//! through `SLDProof.of(!g, ?p)`, which waits while `g` has an unbound variable (kernel-language
//! §8.3). A lookup by an entity pattern that leaves a field out — the loader fills it with a
//! fresh variable — and two goals joined by a variable had no refutation to give. In a query
//! nothing outside can bind the variables, so a complete search with no answer IS one: the
//! entry gives it as `Refuted`, a definite answer as `Answered`, and anything else as
//! `Undecided` with its cause.
//!
//! Every row is driven from outside the crate: a `LogicalQuery` value is built, handed to the
//! entry, and its verdict read.
//!
//! BACK-OUTS: measured, listed at the end of this file.

use anthill_core::eval::{HostValue, Interpreter, Value};
use anthill_core::intern::Symbol;
use anthill_core::kb::execute::{ExecuteOptions, LowerError, Refutation, RefutationOutcome, Undecided};
use anthill_core::kb::load::QueryPattern;
use anthill_core::kb::resolve::{SearchFailure, SearchLimit, SearchStream, Solution};
use anthill_core::kb::term::TermId;
use anthill_core::kb::term_view::{TermView, ViewHead};
use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::print::TermPrinter;

use crate::common::{interp_for, query_goals};

const SRC: &str = r#"
namespace mmgp
  import anthill.prelude.{Int64, Bool, PartialEq, List}
  import anthill.prelude.List.{cons, nil}
  import anthill.reflect.{SLDProof, LogicalQuery, as_term, make_fn}
  import anthill.reflect.LogicalQuery.{pattern_query}

  enum Status
    entity open
    entity closed
  end
  entity E(id: Int64, status: Status)
  entity S(es: List[T = E])

  -- Membership over the cons spine: a miss reaches `nil`, where no clause's head matches.
  fact isIn(?x, cons(head: ?x, tail: ?))
  rule isIn(?x, cons(head: ?, tail: ?t)) :- isIn(?x, ?t)
  rule has_e(S(es: ?l), ?e) :- isIn(?e, ?l)

  fact col(1)
  fact col(2)
  rule pos(?x) :- ?x > 0
  rule big(?x) :- ?x > 5
  rule good(?x) :- pos(?x), big(?x)

  rule q(?x) :- ?x > 0
  rule notq(?x) :- !q(?x)

  rule div_ok(?x) :- 10 / ?x > 1

  -- The language's own refutations, for the control rows.
  rule refute_good1(?p) :- SLDProof.of(!good(1), ?p)
  rule refute_closed2(?p) :- SLDProof.of(!has_e(S(es: [E(id: 1, status: open), E(id: 3, status: closed)]), E(id: 2, status: closed)), ?p)
  rule refute_open2(?p) :- SLDProof.of(!has_e(S(es: [E(id: 1, status: open), E(id: 3, status: closed)]), E(id: 2)), ?p)

  -- A query the typer refuses: an `Int64` compared with an `E`.
  operation refused() -> LogicalQuery =
    pattern_query(term: make_fn("anthill.prelude.PartialEq.eq", [as_term(E(id: 1, status: open)), as_term(1)]))
end
"#;

/// The store both lookups ask: ids 1 and 3, no 2.
const STORE: &str = "mmgp.S(es: [mmgp.E(id: 1, status: mmgp.Status.open), mmgp.E(id: 3, status: mmgp.Status.closed)])";

fn sym(kb: &KnowledgeBase, qn: &str) -> Symbol {
    kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("`{qn}` resolves"))
}

fn entity(kb: &mut KnowledgeBase, qn: &str, fields: Vec<(&str, Value)>) -> Value {
    let functor = sym(kb, qn);
    let named: Vec<(Symbol, Value)> = fields.into_iter().map(|(f, v)| (kb.intern(f), v)).collect();
    Value::Entity {
        functor,
        pos: Vec::new().into(),
        named: named.into(),
    }
}

/// The `LogicalQuery` of `patterns`, one `pattern_query` per goal joined by `conjunction`, the
/// goals converted as one query's (they share their variables).
fn query(kb: &mut KnowledgeBase, patterns: &[&str]) -> (Value, Vec<QueryPattern>) {
    let goals = query_goals(kb, patterns);
    let mut parts: Vec<Value> = goals
        .iter()
        .map(|g| entity(kb, "anthill.reflect.LogicalQuery.pattern_query", vec![("term", Value::Node(g.clone()))]))
        .collect();
    let mut q = parts.pop().expect("a query has a goal");
    while let Some(left) = parts.pop() {
        q = entity(
            kb,
            "anthill.reflect.LogicalQuery.conjunction",
            vec![("left", left), ("right", q)],
        );
    }
    (q, goals)
}

fn refute(kb: &mut KnowledgeBase, patterns: &[&str], options: &ExecuteOptions) -> RefutationOutcome {
    let (q, _) = query(kb, patterns);
    kb.refute_typed_logical_query_with(&q, options)
        .unwrap_or_else(|e| panic!("{patterns:?} types: {e}"))
}

fn print(kb: &mut KnowledgeBase, t: TermId) -> String {
    TermPrinter::new(kb).print_term(t)
}

/// `proof` with each clause label's derived hash written `#` — `some(value: big-#)` — so a row
/// pins the clause by its name and not by the hash its text derives (as G8E02's rows do).
fn unhashed(proof: &str) -> String {
    const AT: &str = "some(value: ";
    let mut out = String::new();
    let mut rest = proof;
    while let Some(i) = rest.find(AT) {
        let (head, tail) = rest.split_at(i + AT.len());
        out.push_str(head);
        let end = tail.find(')').expect("a label closes");
        let label = &tail[..end];
        match label.rfind('-') {
            Some(dash) => {
                out.push_str(&label[..=dash]);
                out.push('#');
            }
            None => out.push_str(label),
        }
        rest = &tail[end..];
    }
    out.push_str(rest);
    out
}

fn print_value(kb: &mut KnowledgeBase, v: &Value) -> String {
    match v {
        Value::Term { id, .. } => print(kb, *id),
        Value::Node(occ) => TermPrinter::new(kb).print_occurrence(occ),
        other => {
            let t = kb.alloc_from_value(other).expect("a value lowers to a term");
            print(kb, t)
        }
    }
}

/// The refutation `outcome` gives, printed; any other verdict fails the row.
fn refuted(kb: &mut KnowledgeBase, what: &str, outcome: &RefutationOutcome) -> String {
    match &outcome.verdict {
        Refutation::Refuted(p) => unhashed(&print(kb, *p)),
        other => panic!("{what} is refuted, got {other:?}"),
    }
}

/// The one definite answer of the one-goal query `pattern` through
/// `execute_typed_logical_query_with`: its last argument, as a term.
fn last_arg_of_answer(kb: &mut KnowledgeBase, pattern: &str) -> TermId {
    let (q, goals) = query(kb, &[pattern]);
    let mut stream = kb
        .execute_typed_logical_query_with(&q, &ExecuteOptions::default())
        .expect("the query types");
    let sol = match stream.next_solution(kb) {
        Ok(Some(sol)) if sol.is_definite() => sol,
        other => panic!("`{pattern}` has a definite answer, got {other:?}"),
    };
    let written = anthill_core::kb::load::query_goal_as_written(kb, &goals[0]);
    let last = match TermView::head(&written, kb) {
        ViewHead::Functor { pos_arity, .. } if pos_arity > 0 => TermView::pos_arg(&written, kb, pos_arity - 1)
            .expect("the last argument is readable")
            .to_value(),
        other => panic!("`{pattern}` is no application with an argument: {other:?}"),
    };
    let v = kb.reify_value(&last, &sol.subst);
    kb.alloc_from_value(&v).expect("a proof is a term")
}

/// (1) A lookup by a PARTIAL entity pattern — `E(id: 2)`, its `status` left out and filled by
/// the loader with a fresh variable — that matches no element is refuted, down to the lookup's
/// refutation at `nil`, where no clause's head matches. `SLDProof.of(!g, ?p)` waits on that
/// variable, and its search ends with the negation unanswered (the control at the end).
///
/// FAILS WHEN BACKED OUT [P] (no proof mode: `Undecided(Faulted)`, "not made in proof mode");
/// passes under [R] by design (one goal reads its own root).
#[test]
fn a_partial_entity_pattern_that_matches_nothing_is_refuted_down_to_nil() {
    let mut interp = interp_for(SRC);
    let kb = interp.kb_mut();
    let lookup = format!("mmgp.has_e({STORE}, mmgp.E(id: 2))");
    let outcome = refute(kb, &[&lookup], &ExecuteOptions::default());
    let proof = refuted(kb, &lookup, &outcome);
    // A cell's step is the recursive clause's alone: the fact's head names another element.
    let at = |rest: &str| format!("isIn(E(id: 2, status: ?status), {rest})");
    let (both, last) = (
        "[E(id: 1, status: open), E(id: 3, status: closed)]",
        "[E(id: 3, status: closed)]",
    );
    let (store, cells, cell, end) = (
        "S(es: [E(id: 1, status: open), E(id: 3, status: closed)])",
        at(both),
        at(last),
        at("nil"),
    );
    assert_eq!(
        proof,
        format!(
            "refuted(goal: has_e({store}, E(id: 2, status: ?status)), steps: [Step(clause: some(value: \
             has_e-#), failing: {cells}, because: refuted(goal: {cells}, steps: [Step(clause: \
             some(value: isIn-#), failing: {cell}, because: refuted(goal: {cell}, steps: \
             [Step(clause: some(value: isIn-#), failing: {end}, because: refuted(goal: {end}, \
             steps: nil))]))]))])"
        ),
        "the leaf is the lookup's refutation at nil, where no clause's head matches"
    );
    assert!(!outcome.stats.truncated && !outcome.stats.out_of_fuel, "the search was complete");
    assert!(outcome.stats.steps > 0, "the steps it took are counted");

    // The control: the language's own form waits on the filled variable, so it has no answer.
    let (q, _) = query(kb, &["mmgp.refute_open2(?p)"]);
    let mut stream = kb
        .execute_typed_logical_query_with(&q, &ExecuteOptions::default())
        .expect("the query types");
    match stream.next_solution(kb) {
        Ok(Some(sol)) => assert!(!sol.is_definite(), "`SLDProof.of(!g, ?p)` waits on `g`'s variable"),
        other => panic!("`SLDProof.of(!g, ?p)` answers conditionally, got {other:?}"),
    }
}

/// (2) THE CONTROL: for a GROUND goal the entry gives the term `SLDProof.of(!g, ?p)` binds `?p`
/// to — the same term, not one printed alike. A rule broken in one conjunct of its body, and a
/// ground lookup that misses.
///
/// FAILS WHEN BACKED OUT [P]; passes under [R] by design (one goal reads its own root).
#[test]
fn a_ground_goal_is_refuted_as_its_negation_is() {
    let mut interp = interp_for(SRC);
    let kb = interp.kb_mut();
    let lookup = format!("mmgp.has_e({STORE}, mmgp.E(id: 2, status: mmgp.Status.closed))");
    for (goal, negation) in [
        ("mmgp.good(1)".to_string(), "mmgp.refute_good1(?p)"),
        (lookup, "mmgp.refute_closed2(?p)"),
    ] {
        let outcome = refute(kb, &[&goal], &ExecuteOptions::default());
        let ours = match outcome.verdict {
            Refutation::Refuted(p) => p,
            other => panic!("`{goal}` is refuted, got {other:?}"),
        };
        let theirs = last_arg_of_answer(kb, negation);
        let (o, t) = (print(kb, ours), print(kb, theirs));
        assert_eq!(ours, theirs, "`{goal}`: the entry and `SLDProof.of(!g, ?p)` agree\n  ours:   {o}\n  theirs: {t}");
    }
}

/// (3) Two goals sharing a variable — `col(?c)` with two answers, `big(?c)` failing for each —
/// are refuted with a step per branch: on each, the goal the branch failed at, as it was asked
/// there. The goal is the conjunction `!(col(?c), big(?c))` writes.
///
/// FAILS WHEN BACKED OUT [P] and [R] (the first goal's record read alone: it never failed, so
/// `Undecided(Faulted)`, "no failed attempt of the goal").
#[test]
fn two_goals_joined_by_a_variable_are_refuted_with_a_step_per_branch() {
    let mut interp = interp_for(SRC);
    let kb = interp.kb_mut();
    let outcome = refute(kb, &["mmgp.col(?c)", "mmgp.big(?c)"], &ExecuteOptions::default());
    let proof = refuted(kb, "col(?c), big(?c)", &outcome);
    let step = |n: i64| {
        format!(
            "Step(clause: none, failing: big({n}), because: refuted(goal: big({n}), steps: [Step(clause: \
             some(value: big-#), failing: quoted(term: gt({n}, 5)), because: builtin_false(goal: \
             quoted(term: gt({n}, 5))))]))"
        )
    };
    assert_eq!(
        proof,
        format!(
            "refuted(goal: quoted(term: and(col(?c), big(?c))), steps: [{}, {}])",
            step(1),
            step(2)
        ),
    );
}

/// (4) A query with a definite answer is `Answered`, with the answer; the search stops at it.
///
/// Passes under every back-out by design: no refutation is asked for.
#[test]
fn a_query_with_an_answer_is_answered() {
    let mut interp = interp_for(SRC);
    let kb = interp.kb_mut();
    let (q, goals) = query(kb, &["mmgp.col(?c)", "mmgp.pos(?c)"]);
    let outcome = kb.refute_typed_logical_query_with(&q, &ExecuteOptions::default()).expect("types");
    let Refutation::Answered(sol) = &outcome.verdict else {
        panic!("`col(?c), pos(?c)` is answered, got {:?}", outcome.verdict);
    };
    let first = kb.reify_value(&Value::Node(goals[0].clone()), &sol.subst);
    assert_eq!(print_value(kb, &first), "col(1)", "the first answer");
}

/// (5) A step budget too small is `Undecided(Limit(Steps))`, naming the caller's budget; a depth
/// budget too small `Undecided(Limit(Depth))`; a goal whose search faults (a zero divisor)
/// `Undecided(Faulted)`, with the fault; a negation of an unbound variable, which waits, gives
/// conditional answers only, `Undecided(Conditional)`.
///
/// The step and depth rows pass under every back-out by design; the conditional row fails
/// backed out [C] (a conditional answer read as `Answered`).
#[test]
fn an_incomplete_search_is_undecided_with_its_cause() {
    let mut interp = interp_for(SRC);
    let kb = interp.kb_mut();
    let lookup = format!("mmgp.has_e({STORE}, mmgp.E(id: 2))");
    let small = ExecuteOptions {
        max_steps: 3,
        ..ExecuteOptions::default()
    };
    let outcome = refute(kb, &[&lookup], &small);
    match outcome.verdict {
        Refutation::Undecided(Undecided::Limit(SearchLimit::Steps { max_steps: 3 })) => {}
        other => panic!("at 3 steps the lookup is cut by its fuel, got {other:?}"),
    }
    assert!(outcome.stats.out_of_fuel && outcome.stats.truncated, "the stats say so");
    assert_eq!(outcome.stats.steps, 3, "the steps taken are the budget");

    let shallow = ExecuteOptions {
        max_depth: 1,
        ..ExecuteOptions::default()
    };
    match refute(kb, &[&lookup], &shallow).verdict {
        Refutation::Undecided(Undecided::Limit(SearchLimit::Depth { max_depth: 1 })) => {}
        other => panic!("at depth 1 the lookup is cut by its depth, got {other:?}"),
    }

    match refute(kb, &["mmgp.div_ok(0)"], &ExecuteOptions::default()).verdict {
        Refutation::Undecided(Undecided::Faulted(fault)) => assert!(
            fault.error.message.contains("division_by_zero"),
            "the fault is the zero divisor: {}",
            fault.error.message
        ),
        other => panic!("`div_ok(0)` faults, got {other:?}"),
    }

    match refute(kb, &["mmgp.notq(?x)"], &ExecuteOptions::default()).verdict {
        Refutation::Undecided(Undecided::Conditional(answers)) => {
            assert_eq!(answers.len(), 1, "one conditional answer");
            assert!(!answers[0].is_definite());
        }
        other => panic!("`notq(?x)` is answered conditionally only, got {other:?}"),
    }
}

/// (6) A query the typer refuses is refused as `execute_typed_logical_query_with` refuses it,
/// before any search: `QueryRefused`, with the same words.
///
/// Passes under every back-out by design.
#[test]
fn a_query_the_typer_refuses_is_refused() {
    let mut interp = interp_for(SRC);
    let q = refused_query(&mut interp);
    let kb = interp.kb_mut();
    let ours = match kb.refute_typed_logical_query_with(&q, &ExecuteOptions::default()) {
        Err(LowerError::QueryRefused(detail)) => detail,
        Err(other) => panic!("the query is refused by the typer, got {other}"),
        Ok(outcome) => panic!("the query is refused before any search, got {:?}", outcome.verdict),
    };
    let theirs = match kb.execute_typed_logical_query_with(&q, &ExecuteOptions::default()) {
        Err(LowerError::QueryRefused(detail)) => detail,
        Err(other) => panic!("the typed execute refuses it too, got {other}"),
        Ok(_) => panic!("the typed execute refuses it too"),
    };
    assert_eq!(ours, theirs, "one refusal, in the same words");
}

fn refused_query(interp: &mut Interpreter) -> Value {
    interp
        .call("mmgp.refused", &HostValue::all(&[]))
        .map(|h| h.value)
        .unwrap_or_else(|e| panic!("`refused()` builds the query: {e:?}"))
}

/// (7) THE CONTROL: the entry's search IS `execute_typed_logical_query_with`'s. Each query is run
/// twice at one budget — pulled from the typed execute's stream as the entry pulls it, to its
/// first definite answer or its end, and handed to the entry — and the two take the same steps,
/// give the same answers, and reach the same end.
///
/// The steps and the answers read the SEARCH, which proof mode must not change: a hook of proof
/// mode that moved a step or dropped a candidate breaks this row, which no row reading a
/// verdict would notice. The end reads the entry's verdict too, so the row also fails backed
/// out [P] and [R] (at the end: a refutation becomes a fault) and [C] (at the steps: the pull
/// stops at the conditional answer).
#[test]
fn the_refutation_takes_the_steps_and_gives_the_answers_of_the_typed_execute() {
    let mut interp = interp_for(SRC);
    let kb = interp.kb_mut();
    let miss = format!("mmgp.has_e({STORE}, mmgp.E(id: 2))");
    let hit = format!("mmgp.has_e({STORE}, mmgp.E(id: 3))");
    let small = ExecuteOptions {
        max_steps: 3,
        ..ExecuteOptions::default()
    };
    let cases: Vec<(Vec<&str>, ExecuteOptions)> = vec![
        (vec![&miss], ExecuteOptions::default()),
        (vec![&hit], ExecuteOptions::default()),
        (vec!["mmgp.good(1)"], ExecuteOptions::default()),
        (vec!["mmgp.col(?c)", "mmgp.big(?c)"], ExecuteOptions::default()),
        (vec!["mmgp.col(?c)", "mmgp.pos(?c)"], ExecuteOptions::default()),
        (vec!["mmgp.notq(?x)"], ExecuteOptions::default()),
        (vec!["mmgp.div_ok(0)"], ExecuteOptions::default()),
        (vec![&miss], small),
    ];
    for (patterns, options) in cases {
        let (q, goals) = query(kb, &patterns);
        let mut stream = kb.execute_typed_logical_query_with(&q, &options).expect("types");
        let plain = pull_as_the_entry_does(kb, &mut stream, &goals);
        let outcome = kb.refute_typed_logical_query_with(&q, &options).expect("types");
        assert_eq!(outcome.stats.steps, stream.stats().steps, "{patterns:?}: the same steps");
        let ours = match &outcome.verdict {
            Refutation::Refuted(_) => "end".to_string(),
            Refutation::Answered(sol) => format!("answered {}", answer(kb, &goals, sol)),
            Refutation::Undecided(Undecided::Conditional(answers)) => format!("{} conditional", answers.len()),
            Refutation::Undecided(Undecided::Limit(limit)) => format!("cut by {limit:?}"),
            Refutation::Undecided(Undecided::Faulted(fault)) => format!("faulted: {}", fault.error.message),
        };
        assert_eq!(ours, plain, "{patterns:?}: the same answers and the same end");
    }
}

/// The query's goals under `sol`, printed.
fn answer(kb: &mut KnowledgeBase, goals: &[QueryPattern], sol: &Solution) -> String {
    let printed: Vec<String> = goals
        .iter()
        .map(|g| {
            let v = kb.reify_value(&Value::Node(g.clone()), &sol.subst);
            print_value(kb, &v)
        })
        .collect();
    printed.join(", ")
}

/// The typed execute's stream pulled as the entry pulls it: to its first definite answer or its
/// end, counting the conditional answers before it.
fn pull_as_the_entry_does(kb: &mut KnowledgeBase, stream: &mut SearchStream, goals: &[QueryPattern]) -> String {
    let mut conditional = 0;
    loop {
        match stream.next_solution(kb) {
            Ok(Some(sol)) if sol.is_definite() => return format!("answered {}", answer(kb, goals, &sol)),
            Ok(Some(_)) => conditional += 1,
            Ok(None) if conditional > 0 => return format!("{conditional} conditional"),
            Ok(None) => return "end".to_string(),
            Err(SearchFailure::Truncated { limit }) => return format!("cut by {limit:?}"),
            Err(SearchFailure::Faulted(fault)) => return format!("faulted: {}", fault.error.message),
        }
    }
}

// BACK-OUTS, measured on a selected run of this file (2026-11-23), each restored after:
//
// * [P] the entry's stream made WITHOUT proof mode (`resolve_lazy_goals` for
//   `resolve_lazy_goals_with_proof`): 4 fail — (1), (2), (3) and (7), each refutation an
//   `Undecided(Faulted)`, "the search was not made in proof mode".
// * [R] `SearchStream::query_refutation` reading the first query goal's record alone
//   (`roots[..1]`): 2 fail — (3) and (7), "the record holds no failed attempt of the goal"
//   (`col(?c)` never failed). (1) and (2) pass by design: one goal is its own root.
// * [C] a conditional answer read as `Answered` (the `is_definite` guard taken out): 2 fail —
//   (5), `notq(?x)` answered, and (7), at the steps.
// * Pass under every back-out by design: (4), no refutation asked for; (6), refused before
//   any search.
