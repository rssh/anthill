//! A constructor's qualified name is the reference its one-segment name is (user, 2026-10-17:
//! "it should be no difference between reference to red as qualified name or as name, which
//! should be reference to symbol"). `Colour.red`, `Colour.method.sketch` and the whole
//! qualified name, written without `()`, parse as a `field_access` chain (§6.7), and the chain
//! was kept as written: in a fact it was a term of its own that the goal `holds(red)` did not
//! find, in a rule body's `=` a load error naming "a defect in the walk", and in an operation
//! body a refusal — `field_access.field: expected String, got Colour`, or, past a nested sort,
//! `sketch.name: expected resolved name`. Found by WI-20260908-9WVT7's seventh review.
//!
//! WHAT FAILS UNDER WHICH BACK-OUT — MEASURED, each walk's reading switched off alone in one
//! build, over the whole `wi_tests` binary, where each moves only the rows named:
//!
//!   * the clause term walk (facts, rule heads) → [`a_fact_holds_the_constructors_symbol`],
//!     [`a_constructor_with_fields_is_one_term_too`], [`a_query_writes_the_qualified_name_as_the_constructor`]
//!     (its patterns meet facts that walk wrote), and
//!     `wi_vnwaw_dotted_goal_readings_test::a_data_slot_keeps_the_dotted_reference_on_both_sides_of_a_match`
//!     (the three walks stop agreeing);
//!   * the rule-body walk → the fixture does not load (`?x = Colour.red`: "a defect in the walk
//!     that built this occurrence"), so every row over it, and the vnwaw row; and
//!     `wi_4nekz_dotted_equation_operand_test::the_five_other_name_kinds_still_agree_with_the_operation_body`
//!     (the constructor and the free-standing entity stop pairing);
//!   * the query walk → [`a_query_writes_the_qualified_name_as_the_constructor`] and the vnwaw
//!     row;
//!   * the operation-body walk → [`an_operation_body_passes_the_constructor`].
//!
//! PASSES EITHER WAY, BY DESIGN: the one-segment and applied spellings inside each row, and a
//! dotted nullary OPERATION in an operation body, which stays refused
//! (`dotted_nullary_op_call_test::an_operation_body_is_not_widened`).

use anthill_core::kb::resolve::ResolveConfig;

use crate::common::{load_kb_with, query_pattern_term, run_int64};

const COLOURS: &str = r#"
namespace test.qc
  import anthill.prelude.{Int64}
  sort Colour
    entity red
    entity green
    entity shade(n: Int64)
    sort method
      entity sketch
      entity lemma(k: Int64)
    end
  end
  fact holds(Colour.red)
  fact holdsM(Colour.method.sketch)
  fact plain(red)
  fact plainM(Colour.method.sketch())
  fact holdsS(Colour.shade)
  fact plainS(shade)
  rule byShort :- holds(red)
  rule byQualified :- plain(Colour.red)
  rule byWhole :- holds(test.qc.Colour.red)
  rule byApplied :- holds(Colour.red())
  rule nestedByApplied :- holdsM(Colour.method.sketch())
  rule nestedByWhole :- holdsM(test.qc.Colour.method.sketch)
  rule nestedByQualified :- plainM(Colour.method.sketch)
  rule sameTerm(?x) :- holds(?x), plain(?x)
  rule sameTermS(?x) :- holdsS(?x), plainS(?x)
  rule eqQualified(?x) :- plain(?x), ?x = Colour.red
  rule unifyNested(?x) :- ?x <=> Colour.method.sketch, plainM(?x)
end
"#;

fn answers(kb: &mut anthill_core::kb::KnowledgeBase, pattern: &str) -> usize {
    let goal = query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// A FACT HOLDS THE CONSTRUCTOR'S SYMBOL, whichever spelling wrote it: `fact holds(Colour.red)`
/// is found by a goal writing `red`, `Colour.red()` or the whole qualified name, and
/// `fact plain(red)` by one writing `Colour.red` — at a nested sort's constructor too, whose
/// one-segment name is not in scope here, against its applied spelling.
///
/// FAILS with the clause term walk's reading backed out: the goals writing `red` and the
/// applied spelling find nothing, and `sameTerm` has no answer.
#[test]
fn a_fact_holds_the_constructors_symbol() {
    let mut kb = load_kb_with(COLOURS);
    for rule in [
        "byShort",
        "byQualified",
        "byWhole",
        "byApplied",
        "nestedByApplied",
        "nestedByQualified",
        "nestedByWhole",
        "sameTerm(?x)",
    ] {
        assert_eq!(answers(&mut kb, &format!("test.qc.{rule}")), 1, "{rule}");
    }
}

/// A CONSTRUCTOR WITH FIELDS IS ONE TERM TOO: `fact holdsS(Colour.shade)` and `fact
/// plainS(shade)` hold the same reference to the constructor.
///
/// FAILS with the clause term walk's reading backed out: `sameTermS` has no answer.
#[test]
fn a_constructor_with_fields_is_one_term_too() {
    let mut kb = load_kb_with(COLOURS);
    assert_eq!(answers(&mut kb, "test.qc.sameTermS(?x)"), 1);
}

/// A RULE BODY READS THE QUALIFIED NAME AS THE CONSTRUCTOR: `?x = Colour.red` beside
/// `plain(?x)` holds, and `?x <=> Colour.method.sketch` binds what `plainM` holds. The `=` was a
/// load error naming "a defect in the walk that built this occurrence".
///
/// FAILS with the rule-body walk's reading backed out: the program does not load.
#[test]
fn a_rule_body_reads_the_qualified_name_as_the_constructor() {
    let mut kb = load_kb_with(COLOURS);
    assert_eq!(answers(&mut kb, "test.qc.eqQualified(?x)"), 1);
    assert_eq!(answers(&mut kb, "test.qc.unifyNested(?x)"), 1);
}

/// A QUERY WRITES THE QUALIFIED NAME AS THE CONSTRUCTOR: the pattern `plain(test.qc.Colour.red)`
/// finds `fact plain(red)`, and `holds(test.qc.Colour.red())` finds `fact holds(Colour.red)`.
///
/// FAILS with the query walk's reading backed out: the first pattern finds nothing.
#[test]
fn a_query_writes_the_qualified_name_as_the_constructor() {
    let mut kb = load_kb_with(COLOURS);
    assert_eq!(answers(&mut kb, "test.qc.plain(test.qc.Colour.red)"), 1);
    assert_eq!(answers(&mut kb, "test.qc.plainM(test.qc.Colour.method.sketch)"), 1);
    assert_eq!(answers(&mut kb, "test.qc.holds(test.qc.Colour.red())"), 1);
}

/// AN OPERATION BODY PASSES THE CONSTRUCTOR: `Colour.red`, the whole qualified name of a nested
/// sort's `sketch` and `Colour.green` as arguments and through a `let`, beside the applied
/// `Colour.method.lemma(k: 7)` — 1, 4, 2 and 7.
///
/// FAILS with the operation-body walk's reading backed out: the program does not load
/// (`field_access.field: expected String, got Colour`).
#[test]
fn an_operation_body_passes_the_constructor() {
    let src = r#"
namespace test.qco
  import anthill.prelude.{Int64}
  sort Colour
    entity red
    entity green
    sort method
      entity sketch
      entity lemma(k: Int64)
    end
  end
  operation pc(c: Colour) -> Int64 =
    match c
      case red -> 1
      case green -> 2
  operation pm(p: Colour.method) -> Int64 =
    match p
      case sketch -> 4
      case lemma(k) -> k
  operation go() -> Int64 =
    let c = Colour.red
    let m = test.qco.Colour.method.sketch
    pc(c) * 1000 + pm(m) * 100 + pc(Colour.green) * 10 + pm(Colour.method.lemma(k: 7))
end
"#;
    assert_eq!(run_int64(src, "test.qco.go"), Ok(1427));
}
