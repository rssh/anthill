//! WI-20261012-KF2SD — the emitter's side of a call several clauses can answer: what
//! the entry points return, as a caller of this crate reads them.
//!
//! What a PROOF is told is driven through the binary
//! (`anthill-cli/tests/include/wi_kf2sd_several_clauses_test.rs`). These rows hold what
//! that does not reach: what a call several clauses can answer is to each entry point —
//! since WI-20261013-1KF32 the disjunction of their worlds in a proof's document, and
//! still an `Err` of an obligation, whose document is not split by them; the dependency set of a call read by a fact; that a LIFT, which reads no call, is
//! not refused one; and the arity check behind the loader's, which only a KB the loader
//! refused can reach.
//!
//! WHAT FAILS WHEN THE CHANGE IS BACKED OUT (measured; part by part in
//! `docs/measurements/test-infrastructure/several-clauses-2026-10-13.txt` §4). With the
//! emitter as it was, four of these six rows FAIL: the refusal of several (now the
//! disjunction, which fails with WI-20261013-1KF32 backed out as well), the two checks
//! behind the loader's, and the obligation. Two PASS EITHER WAY, by design and
//! said at each: `a_call_read_by_a_fact_depends_on_the_predicate` and
//! `a_lift_states_a_predicate_of_several_clauses_and_reads_none` — what a call one
//! clause answers depends on and is read as, and what a lift (which reads none) states.

use super::common::{load_kb_with, load_kb_with_lenient};
use anthill_smt_gen::{
    emit_obligation, emit_satisfiability_check, emit_satisfiability_check_with_deps, lift_rule,
    Obligation, ProofConfig,
};

const SOURCE: &str = r#"
namespace test.kf2sd.emit
  import anthill.prelude.PartialOrd.{gte, lte}

  sort Drone
    entity Leader
    entity Follower
  end

  rule related(?a, ?b) :- gte(?a, ?b)
  rule related(?a, ?b) :- lte(?a, ?b)

  rule read: gte(?a, ?b) :- related(?a, ?b)

  rule lemma: gte(?a, ?b + 1.0) :- related(?a, ?b), lte(?a, 10.0)

  fact speed_of(Leader, 5.0)
  fact speed_of(Follower, 50.0)

  rule fast: gte(?v, 10.0) :- speed_of(Follower, ?v)

  fact start(5.0)
  fact start(-1.0)
  rule top(?d) :- start(?d)
end
"#;

/// A CALL SEVERAL CLAUSES CAN ANSWER IS THEIR DISJUNCTION IN A PROOF'S DOCUMENT, AND AN
/// `Err` OF AN OBLIGATION. `read` came back `Ok`, the body of the first clause for its
/// hypothesis — `(assert (>= var_1 var_0))` — which the conclusion follows from, and a
/// solver handed it answers `unsat`; KF2SD made it an `Err`. WI-20261013-1KF32 reads it
/// in a world for each clause, so the second's `(<= var_1 var_0)` is a world where the
/// conclusion fails. An obligation bounds ONE term, and its document is not split by
/// choices: there the call is refused still.
#[test]
fn a_call_several_clauses_can_answer_is_a_disjunction_and_an_obligations_error() {
    let kb = load_kb_with(SOURCE);
    let smt = emit_satisfiability_check(&kb, "test.kf2sd.emit.read")
        .expect("a call two clauses can answer is read in two worlds");
    assert!(
        smt.contains(
            "(assert (or\n  ; 1: `test.kf2sd.emit.related/2` (0 fact(s), 2 with a body) is \
             answered by its clause 1 of 2\n  (and (>= var_1 var_0) (not (>= var_1 var_0)))\n  \
             ; 2: `test.kf2sd.emit.related/2` (0 fact(s), 2 with a body) is answered by its \
             clause 2 of 2\n  (and (<= var_1 var_0) (not (>= var_1 var_0)))\n))"
        ),
        "{smt}"
    );
    let err = emit_obligation(
        &kb,
        &Obligation {
            rule_qn: "test.kf2sd.emit.top".to_owned(),
            upper_bound: 10.0,
        },
    )
    .expect_err("an obligation reads a call by one clause");
    assert!(
        err.message.contains(
            "the call of `test.kf2sd.emit.start/1` can be answered by 2 clauses of the \
             predicate (2 fact(s), 0 with a body), and an obligation bounds ONE term"
        ),
        "{}",
        err.message
    );
}

/// A CALL READ BY A FACT IS OF ITS PREDICATE'S DEPENDENCY SET — an edit to the fact
/// must stale the proof — and is read by the fact its ground argument selects, the
/// second here. Passes with the change and without it, by design: the three readings
/// were made one, and what a call one clause answers depends on and is read as is what
/// that must not move.
#[test]
fn a_call_read_by_a_fact_depends_on_the_predicate() {
    let kb = load_kb_with(SOURCE);
    let (smt, deps) = emit_satisfiability_check_with_deps(
        &kb,
        "test.kf2sd.emit.fast",
        &ProofConfig::default(),
    )
    .expect("one fact answers");
    assert!(smt.contains("(assert (not (>= 50.0 10.0)))"), "{smt}");
    assert_eq!(
        deps,
        vec![
            "test.kf2sd.emit.fast".to_owned(),
            "test.kf2sd.emit.speed_of".to_owned()
        ]
    );
}

/// A LIFT READS NO CALL, AND IS REFUSED NONE: a cited lemma's premise is the relation of
/// the predicate's name (WI-20261012-CDHSQ), whatever its clauses. Passes with the
/// change and without it, by design — the refusal is of a READING.
#[test]
fn a_lift_states_a_predicate_of_several_clauses_and_reads_none() {
    let kb = load_kb_with(SOURCE);
    let lifted = lift_rule(&kb, "test.kf2sd.emit.lemma").expect("the lemma lifts");
    assert_eq!(
        lifted.clauses,
        vec![
            "(assert (forall ((var_0 Real) (var_1 Real)) \
             (=> (and (test.kf2sd.emit.related/2 var_1 var_0) (<= var_1 10.0)) \
             (>= var_1 (+ var_0 1.0)))))"
                .to_owned()
        ]
    );
}

/// THE ARITY CHECK BEHIND THE LOADER'S. A call written at an arity its predicate has no
/// clause of is refused at LOAD ("expected a term a clause of … can match"), for every
/// consumer; this is the backstop for a KB assembled some other way, and both are
/// asserted, in that order, as `unresolved_functor_is_a_loud_error` does for a name.
#[test]
fn a_call_at_an_arity_no_clause_has_is_a_loud_error() {
    let (kb, load_errs) = load_kb_with_lenient(
        r#"
namespace test.kf2sd.arity
  import anthill.prelude.PartialOrd.{gte, lte}

  rule only3(?a, ?b, ?c) :- gte(?b, ?a), gte(?c, ?b)

  rule wrong: gte(?b, ?a) :- only3(?a, ?b)
end
"#,
    );
    assert!(
        load_errs
            .iter()
            .any(|e| e.contains("only3") && e.contains("can match (3 positional)")),
        "the LOADER refuses the call first, got: {load_errs:?}"
    );
    let err = emit_satisfiability_check(&kb, "test.kf2sd.arity.wrong")
        .expect_err("a call at an arity no clause has is not read");
    assert!(
        err.message.contains(
            "rule call arity mismatch for 'test.kf2sd.arity.only3': the call has 2 \
             argument(s), and its clauses have 3"
        ),
        "{}",
        err.message
    );
}

/// AND THE ONE BEHIND IT FOR A HEAD WRITTEN BY NAME. A positional call of a predicate
/// whose clause names its arguments is refused at load too; behind that, the clause is
/// of the call's arity and nothing rules it out — there is no order to compare by — so
/// it answers, and is not read: the readings bind a head by position.
#[test]
fn a_positional_call_of_a_head_written_by_name_is_a_loud_error() {
    let (kb, load_errs) = load_kb_with_lenient(
        r#"
namespace test.kf2sd.named
  import anthill.prelude.PartialOrd.{gte, lte}

  rule ranked(low: ?a, high: ?b) :- gte(?b, ?a)

  rule by_pos: gte(?y, ?x) :- ranked(?x, ?y)
end
"#,
    );
    assert!(
        load_errs
            .iter()
            .any(|e| e.contains("ranked") && e.contains("got 2 positional")),
        "the LOADER refuses the call first, got: {load_errs:?}"
    );
    let err = emit_satisfiability_check(&kb, "test.kf2sd.named.by_pos")
        .expect_err("a head written by name is not read by position");
    assert!(
        err.message.contains(
            "the clause of 'test.kf2sd.named.ranked' that answers this call must have only \
             pos args in head"
        ),
        "{}",
        err.message
    );
}

/// AN OBLIGATION IS OF ONE CLAUSE TOO (/code-review). `emit_obligation` bounds the
/// result of `<rule>(?r)`, read off the rule's body — the FIRST clause's, where the name
/// was several: `cap(?d)` by `2.0 + 3.0` beside `cap(?d)` by `100.0` was bounded by 5. It
/// goes by the door the proof's own rule does (`collect_rule`), which the binary's rows
/// reach only through a satisfiability check.
#[test]
fn an_obligation_on_a_rule_of_several_clauses_is_refused() {
    let kb = load_kb_with(
        r#"
namespace test.kf2sd.oblig
  import anthill.prelude.PartialOrd.{gte, lte}

  rule cap(?d) :- ?d = 2.0 + 3.0
  rule cap(?d) :- ?d = 100.0

  rule one(?d) :- ?d = 2.0 + 3.0
end
"#,
    );
    let bound = |rule: &str| Obligation {
        rule_qn: format!("test.kf2sd.oblig.{rule}"),
        upper_bound: 10.0,
    };
    let err = emit_obligation(&kb, &bound("cap"))
        .expect_err("a rule of two clauses is not bounded by its first");
    assert!(
        err.message.contains("the rule 'test.kf2sd.oblig.cap' is 2 clauses"),
        "{}",
        err.message
    );
    // The control: one clause is bounded as it was.
    let smt = emit_obligation(&kb, &bound("one")).expect("one clause is read");
    assert!(smt.contains("(+ 2.0 3.0)"), "{smt}");
}
