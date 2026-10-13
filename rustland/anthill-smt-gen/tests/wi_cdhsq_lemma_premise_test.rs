//! WI-20261012-CDHSQ — the emitter's side of a cited lemma's premise that is a rule's
//! predicate: what `lift_rule` hands back, and what a body states under it.
//!
//! The documents a PROOF gets are driven through the binary
//! (`anthill-cli/tests/include/wi_cdhsq_lemma_premise_test.rs`). These rows hold what
//! that does not reach: the declarations a lift returns, as a caller of this crate reads
//! them; the two doors a lift is taken by; and `emit_satisfiability_check_with`, the
//! entry point that returns no dependency set.
//!
//! What fails when a part is backed out:
//! `docs/measurements/test-infrastructure/lemma-premise-2026-10-12.txt` §4.

use super::common::load_kb_with;
use anthill_smt_gen::{
    emit_satisfiability_check_with, lift_rule, lift_rule_to_implication_clause, ProofConfig,
};

const SOURCE: &str = r#"
namespace test.cdhsq.emit
  import anthill.prelude.PartialOrd.{gte, lte}

  rule related(?a, ?b) :- gte(?a, ?b)

  rule lemma: gte(?a, ?b + 1.0) :- related(?a, ?b), lte(?a, 10.0)

  rule plain: gte(?a, 3.0) :- gte(?a, 5.0)

  rule holds: gte(?x, ?y + 1.0) :- related(?x, ?y), lte(?x, 10.0)
end
"#;

const RELATION: &str = "test.cdhsq.emit.related/2";

/// A LIFT KEEPS THE PREMISE AND SAYS WHAT IT DECLARED. The premise stands where it was
/// written, among the others, and the relation it is written with is among the lift's
/// declarations by its name — which is what a consumer is asked by. A lemma with no
/// such premise declares none.
#[test]
fn a_lift_keeps_the_premise_and_declares_its_relation() {
    let kb = load_kb_with(SOURCE);
    let lifted = lift_rule(&kb, "test.cdhsq.emit.lemma").expect("the lemma lifts");
    assert_eq!(
        lifted.clauses,
        vec![format!(
            "(assert (forall ((var_0 Real) (var_1 Real)) \
             (=> (and ({RELATION} var_1 var_0) (<= var_1 10.0)) (>= var_1 (+ var_0 1.0)))))"
        )]
    );
    assert_eq!(
        lifted.declarations.predicates().collect::<Vec<_>>(),
        vec![RELATION]
    );

    let plain = lift_rule(&kb, "test.cdhsq.emit.plain").expect("the lemma lifts");
    assert!(plain.declarations.is_empty());
    assert_eq!(plain.declarations.predicates().count(), 0);
}

/// THE CLAUSES ALONE ARE NOT HANDED OUT WHERE THEY NEED A DECLARATION.
/// `lift_rule_to_implication_clause` returns a lift's clauses and drops what they use: a
/// caller that splices them gets a relation its document never declares, and — not told
/// of it — never states its own call, so the premise is never discharged (/code-review).
/// A lemma that declares nothing goes through that door as it did.
#[test]
fn the_clauses_alone_are_refused_where_they_need_a_declaration() {
    let kb = load_kb_with(SOURCE);
    let refused = lift_rule_to_implication_clause(&kb, "test.cdhsq.emit.lemma")
        .expect_err("the lemma's clause names a relation");
    assert!(
        refused
            .message
            .contains("uses what its consumer's document must declare"),
        "{}",
        refused.message
    );
    assert_eq!(
        lift_rule_to_implication_clause(&kb, "test.cdhsq.emit.plain").expect("the lemma lifts"),
        vec!["(assert (forall ((var_0 Real)) (=> (>= var_0 5.0) (>= var_0 3.0))))"]
    );
}

/// A BODY STATES ITS CALL UNDER WHAT A CITE DECLARED, AND NOT OTHERWISE — through the
/// entry point that returns no dependency set. Under the lemma's declarations the call
/// is asserted, beside its body where the body is read and alone where it is not
/// (`abstract_body`); under none the document names no relation, in either mode.
#[test]
fn a_body_states_its_call_under_what_a_cite_declared_and_not_otherwise() {
    let kb = load_kb_with(SOURCE);
    let lifted = lift_rule(&kb, "test.cdhsq.emit.lemma").expect("the lemma lifts");
    let stated = format!("(assert ({RELATION} var_1 var_0))");
    let declared = format!("(declare-fun {RELATION} (Real Real) Bool)");
    let body_of_the_call = "(assert (>= var_1 var_0))";
    let document = |cited: bool, abstract_body: bool| {
        let mut config = ProofConfig {
            abstract_body,
            ..ProofConfig::default()
        };
        if cited {
            config.assumptions = lifted.clauses.clone();
            config.declarations = lifted.declarations.clone();
        }
        emit_satisfiability_check_with(&kb, "test.cdhsq.emit.holds", &config)
            .expect("the proof's document")
    };
    let has = |document: &str, line: &str| document.lines().any(|l| l == line);

    let read = document(true, false);
    assert!(has(&read, &declared), "{read}");
    assert!(has(&read, &stated), "{read}");
    assert!(has(&read, body_of_the_call), "{read}");
    assert!(has(&read, "(set-logic UFLRA)"), "{read}");

    let skipped = document(true, true);
    assert!(has(&skipped, &declared), "{skipped}");
    assert!(has(&skipped, &stated), "{skipped}");
    assert!(!has(&skipped, body_of_the_call), "{skipped}");

    // THE CONTROL: no cite, no relation — the documents these were.
    for abstract_body in [false, true] {
        let alone = document(false, abstract_body);
        assert!(!alone.contains("test.cdhsq.emit.related"), "{alone}");
        assert!(has(&alone, "(set-logic LRA)"), "{alone}");
        assert_eq!(has(&alone, body_of_the_call), !abstract_body, "{alone}");
    }
}
