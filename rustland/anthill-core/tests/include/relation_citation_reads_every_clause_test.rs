//! A RELATION CITATION READS EVERY CLAUSE — a head slot that is no column (a constant in the
//! clauses' heads) opens to an anonymous variable in the citation's query, so each clause's
//! own constant filters that clause alone (`Interpreter::build_relation_value`).
//!
//! THE DEFECT (found 2026-10-21 while designing WI-20261013-GGXCX): the query was the FIRST
//! clause's head with its constants riding verbatim, so every clause was filtered by the first
//! one's constant. Over `rule mixed(1, ?y) :- ?y <=> 10` and `rule mixed(2, ?y) :- ?y <=> 20`
//! the citation read one row and dropped the other, silently; `mixed(y: 20)` read none; over
//! three ground facts the membership relation (`Unit`, one row per proof — proposal 052) read
//! one proof.
//!
//! BACK-OUT, measured: with the ground slot riding verbatim again, every row here fails except
//! `a_column_slot_and_a_bodyless_head_read_as_before`, which passes either way by design.

const PROGRAM: &str = r#"
namespace relcite
  import anthill.prelude.{Relation, Int64, Option}

  rule mixed(1, ?y) :- ?y <=> 10
  rule mixed(2, ?y) :- ?y <=> 20

  fact holds(1)
  fact holds(2)
  fact holds(3)

  fact pair(1, 10)
  fact pair(2, 20)

  rule viaVar(?x) :- holds(?x)
  rule flag() :- true
  rule flag() :- true

  operation nMixed() -> Int64 effects {Error} = mixed.takeN(5).length()
  operation sumY() -> Int64 effects {Error} =
    let rows = mixed.takeN(5)
    let first = match rows.nth(0)
      case some(r) -> r.y
      case none -> 0
    let second = match rows.nth(1)
      case some(r) -> r.y
      case none -> 0
    first + second
  operation nApplied() -> Int64 effects {Error} = mixed(y: 20).takeN(5).length()
  operation nHolds() -> Int64 effects {Error} = holds.takeN(5).length()
  operation nPair() -> Int64 effects {Error} = pair.takeN(5).length()
  operation nVar() -> Int64 effects {Error} = viaVar.takeN(5).length()
  operation nFlag() -> Int64 effects {Error} = flag.takeN(5).length()
end
"#;

/// The `Int64` each operation answers, from one load of the program.
fn calls<const N: usize>(qns: [&str; N]) -> [i64; N] {
    let mut interp = crate::common::interp_for(PROGRAM);
    qns.map(|qn| {
        let v = interp.call(qn, &[]).unwrap_or_else(|e| panic!("{qn}: {e:?}"));
        crate::common::scalar_int(interp.kb(), &v)
            .unwrap_or_else(|| panic!("{qn}: not an Int64, {v:?}"))
    })
}

#[test]
fn each_clause_of_a_relation_answers_its_own_row() {
    let [n, sum] = calls(["relcite.nMixed", "relcite.sumY"]);
    assert_eq!(n, 2, "both clauses");
    assert_eq!(sum, 30, "each clause's row, in whatever order");
}

#[test]
fn an_applied_citation_binds_its_column_across_every_clause() {
    let [n] = calls(["relcite.nApplied"]);
    assert_eq!(n, 1, "`mixed(2, 20)`, from the second clause");
}

/// Proposal 052: zero columns is `Unit`, one row per proof.
#[test]
fn a_membership_relation_counts_every_proof() {
    assert_eq!(calls(["relcite.nHolds", "relcite.nPair"]), [3, 2]);
}

/// CONTROL, PASSES EITHER WAY: a slot that is a column, and a head with no argument.
#[test]
fn a_column_slot_and_a_bodyless_head_read_as_before() {
    assert_eq!(calls(["relcite.nVar", "relcite.nFlag"]), [3, 2]);
}
