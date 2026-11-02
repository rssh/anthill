//! A DOTTED NAME IS ONE TERM WHEREVER IT IS WRITTEN (kernel-language §6.7, "The member of the
//! chain is read as a name … never as what that name denotes where the chain is written").
//!
//! WI-20260902-TBZ4T — a dotted nullary operation in a rule-body value slot, `?v <=>
//! zzf1.inner.seven`, bound the symbol `seven` where `?v <=> seven2`, `?v <=> seven2()` and `?v
//! <=> zzf1.inner.seven()` computed 7 (measured 2026-09-02). Measured again on d6f92d5f, before
//! this file: all four compute, closed by the later dotted-call work (§6.7's "in a rule body,
//! when it names a nullary operation, that operation's CALL"). The ticket's four rows and its
//! three controls are pinned here, and pass either way.
//!
//! What was still open, found driving those rows from other namespaces: a written chain's
//! MEMBER was held as the symbol the word resolves to where the chain is written. `fact
//! holds(zzf1.inner.seven)` written in `zzf1.outer` held `inner` as the namespace `zzf1.inner`;
//! written in `zzf2`, where `inner` names nothing, as the bare word. So the same goal met its
//! fact only from the fact's own namespace — not from another, not where `seven` is imported,
//! and not from a query — and a sort member (`tbz.inner.S.eight`) did not where `eight` is
//! imported. Measured on d6f92d5f with the CLI: each `*_from_*` row below answered nothing. The
//! member is now the word it spells, interned bare as a name that resolves to nothing is
//! (`Loader::member_name`), in the term walk a fact rides, in the rule-body walk, and in the
//! query walk (its member arm in `convert_query_term_expecting`); scaland's `reallocTerm` the
//! same (`DottedMemberOneTermTest`).
//!
//! ## Back-out
//!
//! Each walk's member reading backed out on its own, this file run under each (measured
//! 2026-11-02, one build, a temporary switch):
//!
//! | backed out | fails |
//! |---|---|
//! | the term walk (a fact, a rule head) | `a_goal_meets_the_fact_from_another_namespace`, `a_namespace_name_is_met_from_another_namespace`, `a_query_meets_the_fact_from_its_namespace`, `the_tickets_controls_hold` |
//! | the rule-body walk | `a_goal_meets_the_fact_from_another_namespace`, `a_member_imported_where_the_goal_is_written_meets_the_fact`, `the_tickets_controls_hold` |
//! | the query walk | `a_query_importing_the_member_meets_the_fact` |
//! | all three | every row but the three below |
//!
//! PASS EITHER WAY, BY DESIGN: `the_four_spellings_of_the_ticket_compute` and
//! `a_member_spelled_like_a_clause_parameter_is_the_field`, under every back-out, and
//! `the_tickets_controls_hold` with all three backed out — what the change must not move.
//! The controls fail with ONE of the term and rule-body walks backed out: a goal and the fact
//! it searches for, written in one namespace, are then built by two readings.

use crate::common::{definite_unary, load_kb_with, query_pattern_term, shown_rows, supply_invocation_imports};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

const SRC: &str = "
namespace tbz.inner
  import anthill.prelude.Int64
  operation seven() -> Int64 = 7
  fact flag(1)
  rule isFlag(?n) :- flag(?n)
  sort S
    operation eight() -> Int64 = 8
  end
end
namespace tbz.one
  import anthill.prelude.Int64
  operation seven2() -> Int64 = 7
  rule oBind(?v) :- ?v <=> seven2
  rule oBindP(?v) :- ?v <=> seven2()
end
namespace tbz.outer
  rule dBind(?v) :- ?v <=> tbz.inner.seven
  rule dBindP(?v) :- ?v <=> tbz.inner.seven()
  fact holds(tbz.inner.seven)
  fact holdsNs(tbz.inner)
  rule via(1) :- holds(tbz.inner.seven)
  rule relSlot(?r) :- ?r <=> tbz.inner.isFlag
  rule predSlot(?r) :- ?r <=> tbz.inner.flag
end
namespace tbz2
  import tbz.outer.{holds, holdsNs}
  rule viaOther(1) :- holds(tbz.inner.seven)
  rule viaNs(1) :- holdsNs(tbz.inner)
  fact holdsS(tbz.inner.S.eight)
  fact holds2(tbz.inner.seven)
end
namespace tbz.sib
  import tbz2.holds2
  rule viaSibling(1) :- holds2(tbz.inner.seven)
end
namespace tbz.imp
  import tbz.inner.seven
  import tbz.outer.holds
  rule viaImported(1) :- holds(tbz.inner.seven)
end
namespace tbz3
  import tbz2.holdsS
  import tbz.inner.S.eight
  rule viaMemberImported(1) :- holdsS(tbz.inner.S.eight)
  fact holdsS3(tbz.inner.S.eight)
end
namespace tbz.par
  import anthill.prelude.Int64
  entity person(age: Int64, rank: Int64)
  fact person(age: 30, rank: 2)
  rule ageOf(age: Int64) :- person(age: ?a, rank: ?r), ?p <=> person(age: ?a, rank: ?r), age <=> ?p.age
  rule rankOf(age: Int64) :- person(age: ?a, rank: ?r), ?p <=> person(age: ?a, rank: ?r), age <=> ?p.rank
end
";

/// The relation's rows, shown, each with whether it is definite.
fn rows(kb: &mut KnowledgeBase, relation: &str) -> Vec<(String, bool)> {
    shown_rows(kb, relation)
}

fn one(shown: &str) -> Vec<(String, bool)> {
    vec![(shown.to_owned(), true)]
}

/// How many definite answers the query `pattern` has.
fn query_answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = query_pattern_term(kb, pattern);
    let (solutions, _) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    solutions.iter().filter(|s| s.residual.is_empty()).count()
}

/// The ticket's four spellings: each computes 7.
#[test]
fn the_four_spellings_of_the_ticket_compute() {
    let mut kb = load_kb_with(SRC);
    for rel in ["tbz.one.oBind", "tbz.one.oBindP", "tbz.outer.dBind", "tbz.outer.dBindP"] {
        assert_eq!(rows(&mut kb, rel), one("7"), "{rel}");
    }
}

/// The ticket's controls: a goal meets the fact holding a dotted operation name in its own
/// namespace; a dotted rule name in a value slot is the relation; a dotted predicate there is
/// its name.
#[test]
fn the_tickets_controls_hold() {
    let mut kb = load_kb_with(SRC);
    assert_eq!(definite_unary(&mut kb, "tbz.outer.via").len(), 1, "one namespace");
    assert_eq!(rows(&mut kb, "tbz.outer.relSlot"), one("isFlag"));
    assert_eq!(rows(&mut kb, "tbz.outer.predSlot"), one("flag"));
}

/// A member spelled like a clause parameter (§2.1) is the field it names, not the parameter: the
/// rule-body walk reads the member before the parameter. A control: `?p.age` answered 30 before
/// too, read by the projection whatever the member was built as.
#[test]
fn a_member_spelled_like_a_clause_parameter_is_the_field() {
    let mut kb = load_kb_with(SRC);
    assert_eq!(rows(&mut kb, "tbz.par.ageOf"), one("30"));
    assert_eq!(rows(&mut kb, "tbz.par.rankOf"), one("2"));
}

/// The goal written in another namespace meets the fact: one where `inner` names nothing, a
/// sibling where it names the namespace and the fact was written where it did not, and one
/// that imports the member.
#[test]
fn a_goal_meets_the_fact_from_another_namespace() {
    let mut kb = load_kb_with(SRC);
    for rel in ["tbz2.viaOther", "tbz.sib.viaSibling", "tbz.imp.viaImported"] {
        assert_eq!(definite_unary(&mut kb, rel).len(), 1, "{rel}");
    }
}

/// The bare namespace name is one term too.
#[test]
fn a_namespace_name_is_met_from_another_namespace() {
    let mut kb = load_kb_with(SRC);
    assert_eq!(definite_unary(&mut kb, "tbz2.viaNs").len(), 1);
}

/// A sort member imported where the goal is written is still the word it spells.
#[test]
fn a_member_imported_where_the_goal_is_written_meets_the_fact() {
    let mut kb = load_kb_with(SRC);
    assert_eq!(definite_unary(&mut kb, "tbz3.viaMemberImported").len(), 1);
}

/// A query meets each fact: written in a namespace where the receiver's segment names
/// something, the bare namespace, and a member imported where the fact is written.
#[test]
fn a_query_meets_the_fact_from_its_namespace() {
    let mut kb = load_kb_with(SRC);
    for pattern in [
        "tbz.outer.holds(tbz.inner.seven)",
        "tbz.outer.holdsNs(tbz.inner)",
        "tbz3.holdsS3(tbz.inner.S.eight)",
    ] {
        assert_eq!(query_answers(&mut kb, pattern), 1, "{pattern}");
    }
}

/// A query that imports the member reads it as the word it spells: it built the call `eight()`
/// there.
#[test]
fn a_query_importing_the_member_meets_the_fact() {
    let mut kb = load_kb_with(SRC);
    assert_eq!(query_answers(&mut kb, "tbz2.holdsS(tbz.inner.S.eight)"), 1, "control: no import");
    supply_invocation_imports(&mut kb, &["tbz.inner.S.eight"]);
    assert_eq!(query_answers(&mut kb, "tbz2.holdsS(tbz.inner.S.eight)"), 1);
}
