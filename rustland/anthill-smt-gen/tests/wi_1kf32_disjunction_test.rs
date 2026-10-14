//! WI-20261013-1KF32 — the emitter's side of a body read in several worlds: what the
//! entry points return, as a caller of this crate reads them.
//!
//! What a PROOF is told is driven through the binary
//! (`anthill-cli/tests/include/wi_1kf32_disjunction_test.rs`). These rows hold what that
//! does not reach: the dependency set of a body read in several worlds, which is every
//! world's; a function-like head, whose result each world equates where one world
//! defines it; and a LIFT, which is not split by the facts of an entity its premise reads.
//! (An OBLIGATION, which is not split either, is KF2SD's row
//! `a_call_several_clauses_can_answer_is_a_disjunction_and_an_obligations_error`.)
//!
//! WHAT FAILS WHEN THE CHANGE IS BACKED OUT (measured; part by part in
//! `docs/measurements/test-infrastructure/disjunction-2026-10-14.txt` §4). With the
//! emitter as it was (79a6703f), all four rows FAIL; none passes either way. Alone: the
//! dependency set of the first world only fails `the_dependency_set_is_every_worlds`; the
//! result's equation left out, `a_function_like_head_is_equated_in_each_world`; the
//! entity's rows read as its constants, `a_lift_is_not_split_by_an_entitys_facts` and
//! `a_field_that_is_no_number_is_no_constant`; the field left at 0.0 in the harvest, the
//! second of those.

use super::common::load_kb_with;
use anthill_smt_gen::{emit_satisfiability_check_with_deps, lift_rule, ProofConfig};

const SOURCE: &str = r#"
namespace test.kf32.emit
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte, lte}

  fact start(5.0)
  fact start(-1.0)
  rule top(?d) :- start(?d)

  fact low(1.0)
  fact high(9.0)
  rule bound(?x) :- low(?x)
  rule bound(?x) :- high(?x)
  rule bounded: lte(?x, 9.0) :- bound(?x)

  entity Limit(cap: Float)
  fact Limit(cap: 5.0)
  fact Limit(cap: -1.0)
  rule capped: gte(?c, -1.0) :- Limit(cap: ?c)

  entity Lone(cap: Float)
  fact Lone(cap: ?any)
  rule lone: gte(?c, 0.0) :- Lone(cap: ?c)
end
"#;

/// THE DEPENDENCY SET IS EVERY WORLD'S. A proof's cache key observes the rules it
/// visited, and the worlds visit different ones: `bound`'s first clause reads `low`, its
/// second `high`. An edit to either must stale the proof; the first world alone would
/// leave `high` out.
#[test]
fn the_dependency_set_is_every_worlds() {
    let kb = load_kb_with(SOURCE);
    let (smt, deps) = emit_satisfiability_check_with_deps(
        &kb,
        "test.kf32.emit.bounded",
        &ProofConfig::default(),
    )
    .expect("two worlds");
    assert!(smt.contains("(assert (or\n"), "{smt}");
    assert_eq!(
        deps,
        [
            "test.kf32.emit.bound",
            "test.kf32.emit.bounded",
            "test.kf32.emit.high",
            "test.kf32.emit.low"
        ]
    );
}

/// A FUNCTION-LIKE HEAD'S RESULT IS EQUATED IN EACH WORLD. One world defines it
/// (`(define-fun var_0 () Real 5.0)`); of two, it is one constant of the document, and
/// each world says what it is there.
#[test]
fn a_function_like_head_is_equated_in_each_world() {
    let kb = load_kb_with(SOURCE);
    let (smt, _) = emit_satisfiability_check_with_deps(
        &kb,
        "test.kf32.emit.top",
        &ProofConfig::default(),
    )
    .expect("two worlds");
    assert!(smt.contains("(declare-const var_0 Real)\n"), "{smt}");
    assert!(!smt.contains("define-fun var_0"), "{smt}");
    assert!(
        smt.contains(
            "(assert (or\n  ; 1: `test.kf32.emit.start/1` (2 fact(s), 0 with a body) is \
             answered by its clause 1 of 2\n  (= var_0 5.0)\n  ; 2: `test.kf32.emit.start/1` \
             (2 fact(s), 0 with a body) is answered by its clause 2 of 2\n  \
             (= var_0 (- 1.0))\n))"
        ),
        "{smt}"
    );
}

/// A LIFT IS NOT SPLIT BY THE FACTS OF AN ENTITY ITS PREMISE READS: a cited lemma is an
/// implication spliced into its consumer, whose fields it names as the consumer's
/// constants, and one of several facts has none. It is refused, as KF2SD refused it,
/// where the proof of the same rule is a world for each fact.
#[test]
fn a_lift_is_not_split_by_an_entitys_facts() {
    let kb = load_kb_with(SOURCE);
    let err = lift_rule(&kb, "test.kf32.emit.capped").expect_err("the lift reads one fact");
    assert!(
        err.message.contains(
            "the entity `test.kf32.emit.Limit` has several facts, and a premise here reads \
             its fields off ONE"
        ) && err.message.contains("a cited lemma's lift and an obligation are not split by them"),
        "{}",
        err.message
    );
    let (smt, _) = emit_satisfiability_check_with_deps(
        &kb,
        "test.kf32.emit.capped",
        &ProofConfig::default(),
    )
    .expect("the proof is a world for each fact");
    assert!(smt.contains("(not (>= (- 1.0) (- 1.0)))"), "{smt}");
}

/// A FIELD THAT IS NO NUMBER IS NO CONSTANT, in a lift either (/code-review). The one fact
/// of `Lone` has a variable for its `cap`, and the constant `cap` was left at the 0.0 it
/// was made with: on 79a6703f the proof of `lone` PROVED `gte(?c, 0.0)`. A proof reads it
/// by its row, the slot free; a lift, which names the constant, refuses it.
#[test]
fn a_field_that_is_no_number_is_no_constant() {
    let kb = load_kb_with(SOURCE);
    let err = lift_rule(&kb, "test.kf32.emit.lone").expect_err("no constant for a variable");
    assert!(
        err.message.contains(
            "the premise `test.kf32.emit.Lone` reads the field `cap` of the entity's fact, \
             whose value there is no number, as a constant of the document"
        ),
        "{}",
        err.message
    );
    let (smt, _) = emit_satisfiability_check_with_deps(
        &kb,
        "test.kf32.emit.lone",
        &ProofConfig::default(),
    )
    .expect("the proof reads the row");
    assert!(
        smt.contains("(declare-const var_0 Real)") && !smt.contains("define-fun cap"),
        "{smt}"
    );
}
