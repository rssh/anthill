//! WI-20260904-EMVCB — an ANSWER is a value; `Value::Node` is the ACCEPTING carrier.
//!
//! THE DEFECT. A rule-body lambda whose result IS its argument handed back the
//! argument's occurrence: `?r <=> apply1(lambda x -> x, 2)` answered
//! `Node(Expr::Const(Int(2)))` where the operation-body twin answered `Int(2)`. The
//! ticket read that as a lambda leak. It is not — MEASURED while repairing it, a bare
//! `?r <=> 2` does exactly the same, and so does `?r <=> takes_int(2)`. The occurrence
//! carrier reaches an answer whenever the answer IS a written operand, however it got
//! there; the lambda only made it easy to notice.
//!
//! THE RULE THIS PINS, in the user's words: `Value::Node` exists so a consumer can be
//! HANDED a compile-time expression on the carrier the resolver proved it on
//! (WI-20260827-3ZNBC hands every bridged operand that way). It was never an EMITTING
//! carrier. So at the boundary where resolution hands a binding out, a `Const`
//! occurrence — which denotes a literal, and a literal already has a native carrier —
//! is folded to its scalar. Everything else keeps its carrier.
//!
//! WHERE THE FOLD IS, and why not deeper. `KnowledgeBase::answer_binding`, whose every
//! caller is an emit site: `materialize_solution`'s relation column, `Substitution.lookup`
//! answering anthill code what a var is bound to, and the CLI's query printer.
//! `reify` / `reify_value` were REFUSED as sites even though they look more central:
//! `bridge_op_to_eval` walks its operands through `reify_value`, so folding there
//! reaches the ACCEPT side and undoes WI-20260827-3ZNBC. `reify`'s own doc says "an
//! answer stays on the carrier it was proved on"; that sentence is now narrowed by
//! exactly this one case, and says so at its site.
//!
//! ── CONTROL ─────────────────────────────────────────────────────────────
//!
//! WHICH ROWS FAIL ON A BACK-OUT. Two independent halves, and each has its own:
//!
//!   * replace `Some(Self::fold_const_occurrences(reified))` with `Some(reified)` in
//!     `answer_binding` and FOUR fail: `the_lambda_row_answers_the_value`,
//!     `a_bare_eq_answers_the_value`, `a_relation_column_answers_the_value`,
//!     `a_const_nested_in_an_entity_answers_the_value`;
//!   * delete only the `Entity`/`Tuple` arms of `fold_const_occurrences` (keeping the
//!     top-level `Const` fold) and exactly ONE fails:
//!     `a_const_nested_in_an_entity_answers_the_value`. Measured — without that row the
//!     recursion would be a branch nothing drives.
//!
//! PASS EITHER WAY, BY DESIGN — the two the ticket names as its controls, and one more:
//!   * `the_operation_body_twin_is_unmoved` — never crossed the resolver boundary;
//!   * `a_computed_result_is_unmoved` — `x + x` answers 4, a value the builtin computed,
//!     which has no occurrence to keep. A repair that moved EITHER would have shifted
//!     the boundary rather than normalized across it, which is the ticket's own test;
//!   * `a_non_const_occurrence_is_not_folded` — this is the one that says the fold is
//!     `Const`-ONLY rather than "no occurrence may be an answer". A too-broad repair
//!     passes every other row here and fails this one.

use crate::common::{definite_unary, interp_for, try_load_kb_with};
use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;

/// The ticket's own fixture: a higher-order operation to hand a lambda to, plus an
/// operation that returns its own parameter (the second way to reach the same leak).
const PRE: &str = "  import anthill.prelude.{Int64, Function}\n  \
   operation apply1(f: Function[A = Int64, B = Int64], n: Int64) -> Int64 = f(n)\n  \
   operation takes_int(n: Int64) -> Int64 = n\n";

fn load(ns: &str, body: &str) -> KnowledgeBase {
    let src = format!("namespace {ns}\n{PRE}{body}end\n");
    try_load_kb_with(&src).unwrap_or_else(|errs| panic!("{ns} must load:\n{}", errs.join("\n")))
}

/// The sole definite answer of `qn(?r)`, asserted to be the NATIVE `Int64` carrier.
///
/// Asserts the CARRIER on purpose, which a `scalar_int` read would not: the carrier IS
/// this ticket's subject, and reading carrier-neutrally here would pass with the fold
/// backed out (`literal_int64` reads a `Const` occurrence perfectly well —
/// WI-20260827-14EV6 is what made it do so). This is the one place in the corpus where
/// naming the variant is the point rather than a mistake.
///
/// SCOPED TO THE `<=>` SPELLING, and that is a real limit rather than a convenience:
/// the same query written as a FACT MATCH answers a hash-consed `Value::Term`, which
/// this fold does not touch, so this helper would panic on it. See
/// `a_fact_matched_literal_keeps_its_hash_consed_carrier`, which pins exactly that and
/// carries the measurement behind the decision.
fn sole_native_int(kb: &mut KnowledgeBase, qn: &str) -> i64 {
    let vs = definite_unary(kb, qn);
    match vs.as_slice() {
        [Value::Int(n)] => *n,
        other => panic!("`{qn}` must answer ONE native Value::Int; got {other:?}"),
    }
}

/// **THE ROW THE TICKET WAS OPENED ON.** Fails on a back-out.
#[test]
fn the_lambda_row_answers_the_value() {
    let mut kb = load(
        "emvcb.lam",
        "  rule value(?r) :- ?r <=> apply1(lambda x -> x, 2)\n",
    );
    assert_eq!(sole_native_int(&mut kb, "emvcb.lam.value"), 2);
}

/// The same leak with NO lambda and NO bridged call — which is what says the ticket's
/// "a rule-body lambda" framing named a symptom rather than the mechanism. Fails on a
/// back-out.
#[test]
fn a_bare_eq_answers_the_value() {
    let mut kb = load("emvcb.bare", "  rule value(?r) :- ?r <=> 2\n");
    assert_eq!(sole_native_int(&mut kb, "emvcb.bare.value"), 2);

    let mut kb = load("emvcb.viaop", "  rule value(?r) :- ?r <=> takes_int(2)\n");
    assert_eq!(sole_native_int(&mut kb, "emvcb.viaop.value"), 2);
}

/// THE PRODUCT PATH: a relation column, reaching the consumer through
/// `materialize_solution` -> `answer_binding`. The rows above go through
/// `common::query_unary`, which this ticket also pointed at `answer_binding`; this one
/// needs no test helper at all and would still fail if that repointing were reverted.
/// Fails on a back-out.
#[test]
fn a_relation_column_answers_the_value() {
    let src = format!(
        "namespace emvcb.rel\n{PRE}  \
         import anthill.prelude.{{Error, EmptyStream}}\n  \
         rule value(?r) :- ?r <=> apply1(lambda x -> x, 2)\n  \
         operation firstRow() -> (r: Int64) effects {{Error, Error[T = EmptyStream]}} =\n    \
         value.head\n\
         end\n"
    );
    let mut interp = interp_for(&src);
    let row = interp
        .call("emvcb.rel.firstRow", &[])
        .expect("the relation must drain one row");
    let col = crate::common::sole_column(&row);
    assert!(
        matches!(col, Value::Int(2)),
        "a relation column is the VALUE its rule answered, not the occurrence it was \
         written as; got {col:?}"
    );
}

/// AN ANSWER IS VALUE-SHAPED ALL THE WAY DOWN. `rule mk(pt(x: ?v)) :- ?v <=> 2` binds
/// the head's field to the occurrence, so the answer is an `Entity` CARRIER holding a
/// `Node(Const)` child — the shape that drives `fold_const_occurrences`' recursion, and
/// the only row that fails when that recursion alone is backed out.
///
/// Note it is NOT reached by `?r <=> some(2)`: that answers ONE occurrence whose expr is
/// `Apply{some, x: Const(2)}`, so the nested literal lives inside the occurrence's own
/// `Expr` tree rather than in a `Value` child. That case is deliberately NOT folded —
/// an `Apply` occurrence denotes structure a reader may still want to walk, and only a
/// `Const` denotes a literal. Recorded so the gap is a decision rather than an oversight.
#[test]
fn a_const_nested_in_an_entity_answers_the_value() {
    let mut kb = load(
        "emvcb.nest",
        "  sort D\n    entity pt(x: Int64)\n  end\n  \
         rule mk(pt(x: ?v)) :- ?v <=> 2\n  \
         rule value(?r) :- mk(?r)\n",
    );
    let vs = definite_unary(&mut kb, "emvcb.nest.value");
    let child = match vs.as_slice() {
        [Value::Entity { named, .. }] if named.len() == 1 => named[0].1.clone(),
        other => panic!("expected one `pt` entity answer with one field; got {other:?}"),
    };
    assert!(
        matches!(child, Value::Int(2)),
        "a Const occurrence nested in an answer's carrier folds too; got {child:?}"
    );
}

/// THE CONTROL THE TICKET NAMES FIRST: the operation-body twin. It never crosses the
/// resolver's answer boundary, so it answered 2 before this change and must still.
/// Passes either way by design.
#[test]
fn the_operation_body_twin_is_unmoved() {
    let src = format!(
        "namespace emvcb.op\n{PRE}  \
         operation w() -> Int64 = apply1(lambda x -> x, 2)\n\
         end\n"
    );
    let mut interp = interp_for(&src);
    let got = interp.call("emvcb.op.w", &[]).expect("w must evaluate");
    assert!(
        matches!(got, Value::Int(2)),
        "the operation-body spelling answered 2 before this ticket and must not move; \
         got {got:?}"
    );
}

/// THE CONTROL THE TICKET NAMES SECOND: a result a BUILTIN computed. `x + x` has no
/// occurrence to keep — `4` is written nowhere — so it was already native and must
/// stay so. Passes either way by design.
#[test]
fn a_computed_result_is_unmoved() {
    let mut kb = load(
        "emvcb.plus",
        "  rule value(?r) :- ?r <=> apply1(lambda x -> x + x, 2)\n",
    );
    assert_eq!(sole_native_int(&mut kb, "emvcb.plus.value"), 4);

    let mut kb = load(
        "emvcb.minus",
        "  rule value(?r) :- ?r <=> apply1(lambda x -> 0 - x, 2)\n",
    );
    assert_eq!(sole_native_int(&mut kb, "emvcb.minus.value"), -2);
}

/// THE ROW THAT BOUNDS THE REPAIR. A nullary constructor answers a `Ref` occurrence,
/// not a `Const` one, and must ride through untouched — the fold is "a literal has a
/// native carrier", NOT "an answer may not be an occurrence". A repair that folded
/// every occurrence, or promoted answers to terms, passes every other row in this file
/// and fails this one. Passes either way by design (the fold never touched it).
#[test]
fn a_non_const_occurrence_is_not_folded() {
    let mut kb = load(
        "emvcb.ref",
        "  sort C\n    entity green\n  end\n  rule value(?r) :- ?r <=> green\n",
    );
    let vs = definite_unary(&mut kb, "emvcb.ref.value");
    assert!(
        matches!(vs.as_slice(), [Value::Node(_)]),
        "a non-Const occurrence keeps its carrier; got {vs:?}"
    );
}

/// THE OTHER HALF OF "AN ANSWER IS A VALUE", PINNED AS THE DECISION IT IS.
///
/// A literal answer has two non-native carriers. This ticket folds the `Value::Node`
/// occurrence; a FACT-matched column rides a hash-consed `Value::Term` over
/// `Term::Const` and is left alone — so the contract holds for `?r <=> 2` and not for
/// the fact spelling of the same query. /code-review named the asymmetry, and it is
/// real.
///
/// FOLDING IT TOO WAS BUILT AND MEASURED, not argued: 9 of 6531 fail, and the first one
/// is why this row asserts the CURRENT behaviour instead of the symmetric one —
/// `wi863_operator_arithmetic_test::float_division_computes` has `6.0 / 2.0` print
/// `?r = 3` rather than `3.0`, because `TermPrinter` renders `Term::Const(Float)` with
/// its decimal point and a native `Value::Float` renders through Rust's `Display`,
/// which drops it. The hash-consed carrier holds a printable form the native one does
/// not reproduce. The rest were stale carrier-enumerating helpers (`wi999`, `wi936`,
/// `wi1034`, `wi_gmg6n`) — the `wi_p9y67` shape again.
///
/// So this row is a SCOPE MARKER: it fails the day someone closes that half, which is
/// when they should be reading the float-rendering note above. Passes either way under
/// this ticket's own back-outs, by design.
#[test]
fn a_fact_matched_literal_keeps_its_hash_consed_carrier() {
    let mut kb = load(
        "emvcb.fact",
        "  sort C\n    entity code(n: Int64)\n  end\n  \
         fact code(n: 7)\n  \
         rule value(?r) :- code(n: ?r)\n",
    );
    let vs = definite_unary(&mut kb, "emvcb.fact.value");
    assert!(
        matches!(vs.as_slice(), [Value::Term { .. }]),
        "a fact-matched literal is NOT folded — see this row's doc for the measurement \
         behind that decision; got {vs:?}"
    );
}
