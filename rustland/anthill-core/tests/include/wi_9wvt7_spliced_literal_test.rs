//! WI-20260908-9WVT7 (found by its reviews) — a COLLECTION LITERAL SPLICED INTO A RULE-BODY
//! LAMBDA is the value the rule bound.
//!
//! `rule h(?e, ?r) :- callIt(lambda () -> okIt(?e), ?r)` evaluated as `h((1, 2), ?r)` panicked
//! a debug build ("unhandled Expr variant in eval") and faulted a release one: when the call is
//! evaluated, the binding of `?e` — a rule term's own literal — is spliced into the lambda's
//! body, and it reached the evaluator as `Expr::TupleLit` / `SetLit` / `ListLit`, which only
//! the typer's reading turns into a constructor. A binding is already a value (068 §1.2), so
//! the evaluator now delivers it as the term the rule holds. The first repair BUILT it again
//! instead, and that was a second value — a tuple with no functor, a set with its duplicates
//! dropped, a by-name `ListLiteral` turned into a `cons` spine — none of which unifies with the
//! rule's own literal: `holder(p: ?p), not(roundTrips(?p))` proved the falsehood definitely.
//!
//! WHAT FAILS UNDER WHICH BACK-OUT — MEASURED, in one build:
//!
//!   * the literal arm put back to BUILDING the constructor → `a_spliced_literal_round_trips`
//!     and `nothing_is_lost_in_the_round_trip` (the identity callback changes the value);
//!   * put back to `Internal` → those two and `a_spliced_tuple_reads_as_its_components` (the
//!     debug assertion in `bridge_op_to_eval` fires).
//!
//! PASSES EITHER WAY BY DESIGN: `the_controls_answer_either_way` — a scalar binding, and a
//! tuple written inside the lambda, which the typer reads at load.

use anthill_core::eval::Value;

const PROGRAM: &str = r#"
namespace test.splice
  import anthill.prelude.{Int64, String}

  sort Holder
    entity holder(p: (Int64, Int64))
  end
  fact holder(p: (1, 2))

  fact keepSet({1, 1, 2})

  operation okIt[E](e: E) -> E = e
  operation callIt[A](f: () -> A) -> A = f()

  rule h(?e, ?r) :- callIt(lambda () -> okIt(?e), ?r)

  rule tuple(?r) :- h((1, 2), ?r)
  rule tupleBack(?p) :- holder(p: ?p), h(?p, ?r), holder(p: ?r)
  rule setBack(?s) :- keepSet(?s), h(?s, ?r), keepSet(?r)
  rule nestedBack(?b) :- holder(p: ?p), ?b <=> holder(p: ?p), h(?b, ?r), ?r <=> holder(p: ?p)
  rule roundTrips(?p) :- h(?p, ?r), holder(p: ?r)
  rule lost(?p) :- holder(p: ?p), not(roundTrips(?p))
  rule scalar(?r) :- h(5, ?r)
  rule written(?r) :- callIt(lambda () -> (1, 2), ?r)
end
"#;

/// The two components of a pair, read through the carrier-neutral view.
#[track_caller]
fn pair(kb: &anthill_core::kb::KnowledgeBase, v: &Value) -> (i64, i64) {
    let at = |k: usize| {
        let label = anthill_core::intern::positional_label(k);
        let c = crate::common::entity_field(kb, v, &label, k);
        crate::common::scalar_int(kb, &c).unwrap_or_else(|| panic!("an Int64 at {k}: {v:?}"))
    };
    (at(0), at(1))
}

/// A tuple a rule term holds, spliced into the lambda, reads as its two components.
#[test]
fn a_spliced_tuple_reads_as_its_components() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    let r = crate::common::one_definite(&mut kb, "test.splice.tuple");
    assert_eq!(pair(&kb, &r), (1, 2));
}

/// THE DEFECT. What the identity callback hands back is the value it was given: it matches
/// the fact it came from — a tuple, a set with a duplicate, a tuple inside an entity.
#[test]
fn a_spliced_literal_round_trips() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    for qn in ["test.splice.tupleBack", "test.splice.setBack", "test.splice.nestedBack"] {
        let rows = crate::common::query_unary(&mut kb, qn);
        assert!(
            matches!(rows.as_slice(), [(_, true)]),
            "{qn}: one definite answer, got {rows:?}"
        );
    }
}

/// And the negation of the round trip proves nothing: no binding is lost on the way.
#[test]
fn nothing_is_lost_in_the_round_trip() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    let rows = crate::common::query_unary(&mut kb, "test.splice.lost");
    assert!(rows.is_empty(), "no lost binding: {rows:?}");
}

/// PASSES EITHER WAY BY DESIGN: nothing here is a spliced literal.
#[test]
fn the_controls_answer_either_way() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    assert_eq!(crate::common::one_definite_int(&mut kb, "test.splice.scalar"), Some(5));
    let r = crate::common::one_definite(&mut kb, "test.splice.written");
    assert_eq!(pair(&kb, &r), (1, 2));
}
