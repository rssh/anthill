//! WI-787 — spreading a NAME-keyed tuple across an eta'd OPERATION's parameters.
//!
//! `spread_eta_args` (eval/eval.rs) read `Value::Tuple.pos` alone and compared its
//! length against the operation's arity. A name-keyed tuple carries all of its
//! components in `named` and none in `pos`, so it presented as ZERO components,
//! the tuple spread never fired, and the call raised `ArityMismatch` — on a
//! program that loaded clean. Same defect WI-785 fixed in `match_tuple_pattern`,
//! left unfixed in the sibling reader ~900 lines up the same file. Both now read
//! through `Value::tuple_components`, which owns the `pos ++ named` invariant.
//!
//! ## Why these fixtures go through a POLYMORPHIC hop
//!
//! The ticket's original fixtures — a two-parameter operation handed straight to a
//! `(a: Int64, b: Int64) -> Int64` / `Function[A = (a: …, b: …), B = …]` slot — no
//! longer reach eval at all: WI-791 made arity a child of the arrow, so a
//! one-parameter slot whose parameter is a TUPLE is no longer satisfied by a
//! genuinely two-parameter operation, and those spellings are now refused at LOAD.
//! Routing through `apT[T](f: Function[A = T, B = Int64], t: T)` puts a type
//! VARIABLE in the callback's parameter position, so the tuple's keying is not
//! visible to the conformance check and the program loads — which is precisely
//! when this runtime reader is the only thing standing between a correct program
//! and a spurious trap.
//!
//! `relation_row_*` is the non-contrived shape: a relation ROW is built all-named
//! (its field order IS the relation schema), so this is what mapping a
//! two-parameter operation over rows actually hits.
//!
//! The load-bearing consequence is that an OPERATION and a LAMBDA were not
//! interchangeable as function values: `spread_eta_args` is the operation half of
//! the pair whose lambda half is `gather_closure_arg` (WI-784), and a caller
//! cannot see which one its callee will take.

use crate::common::{interp_for, list_ints};

/// A FRESH interpreter per call: reusing one after a trapped call returns a bogus
/// `Internal("deliver: parent frame had no awaiting state")` on every later call,
/// which reads as an unrelated second failure.
fn run(src: &str, op: &str) -> anthill_core::eval::Value {
    let mut interp = interp_for(src);
    interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}"))
}

fn run_int(src: &str, op: &str) -> i64 {
    match run(src, op) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

fn poly_src(ns: &str, literal: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Function}}
  operation sub2(p: Int64, q: Int64) -> Int64 = p - q
  operation apT[T](f: Function[A = T, B = Int64], t: T) -> Int64 = f(t)
  operation drive() -> Int64 = apT(sub2, {literal})
end
"#
    )
}

/// THE regression. Each of these loaded clean and raised
/// `ArityMismatch { expected: 2, got: 1 }` at eval.
///
/// `_x`/`_01`/`_2` are USER labels — only `_1`, `_2`, … at their OWN source index
/// are synthetic (WI-790), so `(_2: 3, _1: 10)` keeps both components NAMED
/// (`_2` at index 0 is not that index's label). WI-786 narrowing
/// `classify_ctor_arg` to respect that is what turned this latent half-read into
/// a live regression for these three spellings.
#[test]
fn named_tuple_spreads_across_eta_operation() {
    for (ns, literal) in [
        ("test.wi787a", "(acc: 3, x: 10)"),
        ("test.wi787b", "(_x: 3, _y: 10)"),
        ("test.wi787c", "(_2: 3, _1: 10)"),
        ("test.wi787d", "(_01: 3, _02: 10)"),
    ] {
        assert_eq!(
            run_int(&poly_src(ns, literal), &format!("{ns}.drive")),
            -7,
            "literal {literal}",
        );
    }
}

/// The positional spelling — WI-275's original case, which always worked and is
/// the CONTROL that makes the test above a keying claim rather than a
/// does-anything-work claim. Pre-fix this returned -7 while every literal above
/// trapped, the two differing only in whether the components are named.
#[test]
fn positional_tuple_still_spreads() {
    assert_eq!(run_int(&poly_src("test.wi787pos", "(3, 10)"), "test.wi787pos.drive"), -7);
}

/// Components spread in SOURCE order. Labels are spelled `x, acc` so that any
/// re-ordering — canonicalizing the tuple like a record, or reversing it — flips
/// the result to +7 while every other test here still passes. Same guard
/// `wi785_named_tuple_destructuring_test::binds_in_source_order` puts on the
/// lambda half.
#[test]
fn spreads_in_source_order() {
    assert_eq!(
        run_int(&poly_src("test.wi787order", "(x: 3, acc: 10)"), "test.wi787order.drive"),
        -7,
        "p must take the FIRST WRITTEN component (x = 3); any re-ordering gives +7",
    );
}

/// A tuple mixing positional and named components — which would exercise the
/// concatenation itself rather than either pure half — is NOT constructible: the
/// parser refuses the literal outright, and no other producer mints one. Pinned
/// here because it is the reason this file cannot test the prefix rule directly,
/// and because if that refusal is ever lifted, the mixed shape becomes reachable
/// and wants a spread test alongside `wi786_tuple_component_order_test`.
#[test]
fn mixed_keying_tuple_literal_is_refused_by_the_parser() {
    // The refusal is at PARSE, ahead of the load-error channel, so go to the
    // parser directly rather than through `try_load_kb_with` (which panics).
    let errs = anthill_core::parse::parse(&poly_src("test.wi787split", "(3, x: 10)"))
        .expect_err("a tuple literal may not mix positional and named components");
    assert!(
        errs.iter().any(|e| e.message.contains("cannot mix positional and named")),
        "expected the mixing refusal, got {errs:?}",
    );
}

/// Arity strictness must survive the widening: presenting named components
/// alongside positional ones must not let an N-component tuple spread across M
/// parameters. A 3-component tuple against a 2-parameter operation stays a loud
/// `ArityMismatch`, not a silent take-two-and-drop-one.
#[test]
fn arity_mismatch_still_raises() {
    let src = poly_src("test.wi787arity", "(a: 1, b: 2, c: 3)");
    let mut interp = interp_for(&src);
    let err = interp.call("test.wi787arity.drive", &[]).expect_err(
        "a 3-component tuple must not spread across 2 parameters",
    );
    assert!(
        format!("{err:?}").contains("ArityMismatch"),
        "expected a loud ArityMismatch, got {err:?}",
    );
}

const RELATION_SRC: &str = r#"
namespace test.wi787rel
  import anthill.prelude.{Int64, List, Function, Error}
  sort Rec
    entity Rec(a: Int64, b: Int64)
  end
  fact Rec(a: 3, b: 10)
  rule pr(?x, ?y) :- Rec(a: ?x, b: ?y)
  operation sub2(p: Int64, q: Int64) -> Int64 = p - q
  operation apT[T](f: Function[A = T, B = Int64], t: T) -> Int64 = f(t)
  operation viaOp() -> List[T = Int64] effects Error
    = pr.takeN(5).mapElems(lambda r -> apT(sub2, r))
  operation viaLambda() -> List[T = Int64] effects Error
    = pr.takeN(5).mapElems(lambda r -> apT(lambda (p: Int64, q: Int64) -> p - q, r))
end
"#;

/// The non-contrived path, and the acceptance the ticket names: mapping a
/// two-parameter OPERATION over relation rows. A row is built ALL-NAMED, so this
/// hit the `pos`-only read on ordinary usage — it loaded clean and trapped
/// `ArityMismatch` while the byte-identical LAMBDA spelling evaluated.
///
/// Asserting the two spellings AGREE (rather than each against a literal) is the
/// point: `spread_eta_args` and `gather_closure_arg` are the two halves of
/// function-value application, and the same source program must not have two
/// verdicts depending only on the callee's kind.
#[test]
fn relation_row_operation_and_lambda_spellings_agree() {
    let via_op = run(RELATION_SRC, "test.wi787rel.viaOp");
    let via_lambda = run(RELATION_SRC, "test.wi787rel.viaLambda");
    assert_eq!(
        list_ints(&via_op),
        list_ints(&via_lambda),
        "operation and lambda spellings over the same relation rows must agree",
    );
    assert_eq!(list_ints(&via_op), vec![-7], "row (x: 3, y: 10) maps to 3 - 10");
}
