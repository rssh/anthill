//! A DOTTED NAME OF A NULLARY OPERATION IN A RULE BODY IS ITS CALL — `?y <=> Box.zero`
//! binds what `?y <=> Box.zero()` and the one-segment `?y <=> seven` bind (§5.4, *The two
//! readings of a bare operation name*; WI-20260902-CZJ2N gave the one-segment spelling
//! that reading). Decided with the user 2026-09-23: `<=>` is structural unification, and
//! an operation call written in a rule is reduced BEFORE it — so the operand is the value.
//!
//! BEFORE, measured on a CLI built from `7fab2c40`: the dotted spelling was the one left
//! out. `?y <=> Box.zero` bound the operation's NAME (the chain reduced to `Ref(Box.zero)`
//! by sort-component access, then never called — a nullary term carrier is not folded),
//! `0 <=> Box.zero` and `0 === Box.zero` answered nothing, and `0 = Box.zero` was a LOAD
//! ERROR ("Box.name / zero.name: expected resolved name") where `7 = seven` holds.
//!
//! THE TERM IS UNTOUCHED. In a data slot the chain stays the chain — the term `fact
//! f(Box.zero)` stores (WI-20260901-719FJ, WI-20260902-4NEKZ) — and the call is made
//! where the chain is REDUCED as an operand (`Resolver::reduce_dot_value`), with the typer
//! giving it the matching type (`dotted_citation_nullary_op`). So a goal argument still
//! matches its fact, which `the_term_still_matches_its_fact` pins.
//!
//! BACK-OUT, measured one axis at a time:
//!  * [R] the resolver rung in `reduce_dot_value` removed: RED — `a_dotted_nullary_
//!    operation_binds_its_value`, `every_path_spelling_calls`, `a_bound_side_compares_
//!    against_the_call`, `an_eq_operand_is_typed_and_run_as_the_call` (it loads, and
//!    answers 0 rows).
//!  * [T] the typer rung (`dotted_citation_nullary_op`) removed: RED —
//!    `an_eq_operand_is_typed_and_run_as_the_call` only (a load error), because the
//!    resolver rows sit in a fixture with no `=` operand and still load.
//!  * [G] its `in_rule_body()` gate removed: NOTHING reddens, measured. The gate is
//!    redundant with provenance today — only the rule-body walk marks a written dot, so
//!    an operation body never reaches the rung — and is kept as the statement of scope
//!    (see its site). `an_operation_body_is_not_widened` therefore pins the OBSERVABLE
//!    (an operation body stays refused), not the gate.
//!
//! PASS EITHER WAY, BY DESIGN: the one-segment and applied controls inside
//! `a_dotted_nullary_operation_binds_its_value`, `the_term_still_matches_its_fact`,
//! `a_non_nullary_member_stays_its_name` and `an_operation_body_is_not_widened` — they pin
//! what the change must NOT move.
//!
//! NOT IN SCOPE, and uniform across spellings rather than a dotted-name gap: a QUERY
//! pattern calls nothing (`?y <=> pc.Box.zero()` binds the term there too — a pattern is
//! data); arithmetic in a rule is not evaluated (`?z <=> 3 + 1` suspends); and a call in a
//! goal ARGUMENT is matched as a term (`:- factV(seven())` misses `fact factV(7)`).

use anthill_core::kb::KnowledgeBase;

/// One `Int64` answer per rule, read as a consumer does — `definite_unary`, so a
/// suspended row is not counted as an answer.
fn sole_int(kb: &mut KnowledgeBase, rel: &str) -> Option<i64> {
    let rows = crate::common::definite_unary(kb, rel);
    assert_eq!(rows.len(), 1, "{rel}: one definite row, got {rows:?}");
    crate::common::scalar_int(kb, &rows[0])
}

const RESOLVER: &str = "namespace zzdnc
  import anthill.prelude.{Int64}
  operation seven() -> Int64 = 7
  sort Box
    entity box(v: Int64)
    operation zero() -> Int64 = 0
    operation two() -> Int64 = 1 + 1
    operation succ(n: Int64) -> Int64 = n + 1
    sort Inner
      entity inner
      operation one() -> Int64 = 1
    end
  end
  fact stored(Box.zero)
  rule dotted(?y) :- ?y <=> Box.zero
  rule applied(?y) :- ?y <=> Box.zero()
  rule oneSegment(?y) :- ?y <=> seven
  rule nested(?y) :- ?y <=> Box.Inner.one
  rule qualified(?y) :- ?y <=> zzdnc.Box.zero
  rule absolute(?y) :- ?y <=> ..zzdnc.Box.zero
  rule complex(?y) :- ?y <=> Box.two
  rule boundUnify(1) :- 0 <=> Box.zero
  rule boundStruct(1) :- 0 === Box.zero
  rule matchesFact(1) :- stored(Box.zero)
  rule nonNullary(?y) :- ?y <=> Box.succ
end
";

#[test]
fn a_dotted_nullary_operation_binds_its_value() {
    let mut kb = crate::common::load_kb_with(RESOLVER);
    // CONTROLS — the two spellings that already called, unchanged by design.
    assert_eq!(sole_int(&mut kb, "zzdnc.oneSegment"), Some(7));
    assert_eq!(sole_int(&mut kb, "zzdnc.applied"), Some(0));
    assert_eq!(
        sole_int(&mut kb, "zzdnc.dotted"),
        Some(0),
        "`?y <=> Box.zero` must bind the call's value, as `Box.zero()` does — not the name",
    );
}

#[test]
fn every_path_spelling_calls() {
    // The reading belongs to the NAME, however it is spelled: two segments deep, fully
    // qualified, absolute — and a body the fold cannot collapse (`1 + 1`) reaches the same
    // bridge the one-segment call does.
    let mut kb = crate::common::load_kb_with(RESOLVER);
    for (rel, want) in [
        ("zzdnc.nested", 1),
        ("zzdnc.qualified", 0),
        ("zzdnc.absolute", 0),
        ("zzdnc.complex", 2),
    ] {
        assert_eq!(sole_int(&mut kb, rel), Some(want), "{rel}");
    }
}

#[test]
fn a_bound_side_compares_against_the_call() {
    // `<=>` unifies and `===` tests, but both reduce their operands first — so the value
    // is what the bound side meets. Both answered NOTHING before.
    let mut kb = crate::common::load_kb_with(RESOLVER);
    for rel in ["zzdnc.boundUnify", "zzdnc.boundStruct"] {
        assert_eq!(
            crate::common::definite_unary(&mut kb, rel).len(),
            1,
            "{rel}: `0` must meet the call's value",
        );
    }
}

#[test]
fn the_term_still_matches_its_fact() {
    // CONTROL — passes with the change backed out, BY DESIGN. The call is made where the
    // chain is REDUCED; a goal argument is matched, not reduced, so it must still be the
    // chain the fact stored. Collapsing the term in the rule body alone is the regression
    // 4NEKZ measured and refused.
    let mut kb = crate::common::load_kb_with(RESOLVER);
    assert_eq!(crate::common::definite_unary(&mut kb, "zzdnc.matchesFact").len(), 1);
}

#[test]
fn a_non_nullary_member_stays_its_name() {
    // CONTROL — passes either way, BY DESIGN. A zero-argument call is an arity error for
    // `succ(n)`, so there is no call to make; the one-segment `succ` is not elaborated
    // either (`nullary_op_call_or_ref` is arity-0 only).
    let mut kb = crate::common::load_kb_with(RESOLVER);
    let rows = crate::common::definite_unary(&mut kb, "zzdnc.nonNullary");
    assert_eq!(rows.len(), 1);
    assert_eq!(crate::common::scalar_int(&kb, &rows[0]), None, "not a value: {:?}", rows[0]);
}

#[test]
fn an_eq_operand_is_typed_and_run_as_the_call() {
    // Its own fixture, so backing out the TYPER rung reddens this row and no other.
    let mut kb = crate::common::load_kb_with(
        "namespace zzdnce
  import anthill.prelude.{Int64}
  sort Box
    entity box(v: Int64)
    operation zero() -> Int64 = 0
  end
  rule eqZero(1) :- 0 = Box.zero
  rule eqOne(1) :- 1 = Box.zero
  rule below(1) :- Box.zero < 1
end
",
    );
    assert_eq!(crate::common::definite_unary(&mut kb, "zzdnce.eqZero").len(), 1);
    assert_eq!(
        crate::common::definite_unary(&mut kb, "zzdnce.eqOne").len(),
        0,
        "the call is compared, not merely accepted",
    );
    assert_eq!(crate::common::definite_unary(&mut kb, "zzdnce.below").len(), 1);
}

#[test]
fn an_operation_body_is_not_widened() {
    // The reading is a RULE-BODY one. In an operation body the bare `Box.zero` names no
    // operation, and `Box[T = …].zero` is refused on that premise
    // (`LoadError::ParenLessCitationOfNonRule`) — so it must stay refused here.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(
            "namespace zzdnco
  import anthill.prelude.{Int64}
  sort Box
    entity box(v: Int64)
    operation zero() -> Int64 = 0
  end
  operation go() -> Int64 = Box.zero
end
",
        ),
        &["zero.name: expected resolved name"],
    );
}
