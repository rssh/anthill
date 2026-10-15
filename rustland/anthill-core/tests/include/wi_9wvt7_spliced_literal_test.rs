//! WI-20260908-9WVT7 (found by its review) — a COLLECTION LITERAL SPLICED INTO A RULE-BODY
//! LAMBDA.
//!
//! `rule h(?e, ?r) :- callIt(lambda () -> okIt(?e), ?r)` evaluated as `h((1, 2), ?r)`
//! panicked a debug build ("unhandled Expr variant in eval") and faulted a release one. When
//! the call is evaluated, the binding of `?e` — a rule term's own tuple literal — is spliced
//! into the lambda's body, and no typer saw it there, so it reached the evaluator as
//! `Expr::TupleLit`, which only the typer's reading (`typing::literal_as_constructor`) turns
//! into a constructor. The evaluator now reads it the same way, and builds it by the arm the
//! typed one takes. A set literal took the same road; a list literal is a `cons` spine in a
//! rule's term and never reached it.
//!
//! WHAT FAILS UNDER THE BACK-OUT — MEASURED: the evaluator's literal arm put back to its
//! `Internal` → `a_spliced_tuple_literal_is_built`,
//! `a_spliced_set_literal_is_the_set_an_operation_body_builds` and
//! `a_tuple_inside_a_spliced_entity_is_built` (the debug assertion in `bridge_op_to_eval`
//! fires). PASSES EITHER WAY BY DESIGN: `the_controls_answer_either_way` — a scalar binding,
//! and a tuple written inside the lambda, which the typer reads at load.

use anthill_core::eval::Value;

const PROGRAM: &str = r#"
namespace test.splice
  import anthill.prelude.{Int64, String, Set}

  sort Holder
    entity holder(p: (Int64, Int64))
  end
  fact holder(p: (1, 2))

  operation okIt[E](e: E) -> E = e
  operation callIt[A](f: () -> A) -> A = f()
  operation aSet() -> Set[T = Int64] = {1, 2}

  rule h(?e, ?r) :- callIt(lambda () -> okIt(?e), ?r)

  rule tuple(?r) :- h((1, 2), ?r)
  rule fromFact(?r) :- holder(p: ?p), h(?p, ?r)
  rule set(?r) :- h({1, 2}, ?r)
  rule setViaOp(?r) :- aSet(?r)
  rule nested(?r) :- h(holder(p: (3, 4)), ?r)
  rule scalar(?r) :- h(5, ?r)
  rule written(?r) :- callIt(lambda () -> (1, 2), ?r)
end
"#;

/// The two components of a pair, read through the carrier-neutral view.
#[track_caller]
fn pair(kb: &anthill_core::kb::KnowledgeBase, v: &Value) -> (i64, i64) {
    let at = |k| {
        let c = crate::common::entity_field(kb, v, &format!("_{}", k + 1), k);
        crate::common::scalar_int(kb, &c).unwrap_or_else(|| panic!("an Int64 at {k}: {v:?}"))
    };
    (at(0), at(1))
}

/// THE DEFECT. A tuple a rule term holds, and one a fact holds, each spliced into the lambda.
#[test]
fn a_spliced_tuple_literal_is_built() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    let r = crate::common::one_definite(&mut kb, "test.splice.tuple");
    assert_eq!(pair(&kb, &r), (1, 2));
    let r = crate::common::one_definite(&mut kb, "test.splice.fromFact");
    assert_eq!(pair(&kb, &r), (1, 2));
}

/// A set literal is built as the set an operation body builds from the same literal.
#[test]
fn a_spliced_set_literal_is_the_set_an_operation_body_builds() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    let spliced = crate::common::one_definite(&mut kb, "test.splice.set");
    let typed = crate::common::one_definite(&mut kb, "test.splice.setViaOp");
    assert!(
        anthill_core::kb::term_view::views_structurally_equal(&kb, &spliced, &typed),
        "the spliced set {spliced:?} is the operation body's {typed:?}"
    );
}

/// A tuple inside an entity the rule spliced in.
#[test]
fn a_tuple_inside_a_spliced_entity_is_built() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    let r = crate::common::one_definite(&mut kb, "test.splice.nested");
    assert_eq!(
        crate::common::entity_functor_qn(&kb, &r).as_deref(),
        Some("test.splice.Holder.holder")
    );
    let p = crate::common::entity_field(&kb, &r, "p", 0);
    assert_eq!(pair(&kb, &p), (3, 4));
}

/// PASSES EITHER WAY BY DESIGN: nothing here is a spliced literal.
#[test]
fn the_controls_answer_either_way() {
    let mut kb = crate::common::load_kb_with(PROGRAM);
    assert_eq!(crate::common::one_definite_int(&mut kb, "test.splice.scalar"), Some(5));
    let r = crate::common::one_definite(&mut kb, "test.splice.written");
    assert_eq!(pair(&kb, &r), (1, 2));
}
