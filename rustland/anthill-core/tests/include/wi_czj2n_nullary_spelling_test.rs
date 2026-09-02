//! WI-20260902-CZJ2N — A BARE NAME IN A LOGICAL POSITION **IS** THE NULLARY
//! APPLICATION, AND THE POSITION DECIDES.
//!
//! `rule holds :- b(1)` and `rule holds() :- b(1)` were TWO TERMS, so a predicate
//! written one way was not queryable the other — while §5.3/§8.6 said the opposite in
//! words ("a PAREN-LESS nullary head is an application of arity 0 … exactly as `rule
//! holds()` is", WI-20260821-P85Z7). P85Z7 delivered the SCOPING half and left the TERM
//! half; WI-20260901-719FJ found the same split under a dot and declined it as
//! spelling-independent. This is that half.
//!
//! ── THE FIVE KINDS THE SPLIT REACHED, AS MEASURED ON THE DELIVERED 719FJ TREE ──
//!
//! | kind | before | after |
//! |---|---|---|
//! | nullary PREDICATE | `aa` 1, `ab` 0, `ba` 0, `bb` 1 — each spelling answers its own | all four answer |
//! | nullary Bool OP as a goal | `:- flag` fails SILENTLY, and `not(flag)` **SUCCEEDS** | `:- flag` runs; `not(flag)` fails |
//! | nullary OP in a rule-body data slot | `?v <=> seven` binds the SYMBOL | binds 7, like `seven()` |
//! | `[simp]` HEAD | `rule tau <=> 7 [simp]` fires nothing | defines, like `tau()` |
//! | an UNDECLARED equation subject | bare: refused "names nothing"; paren: mints | both mint |
//!
//! Two of those five are WRONG ANSWERS rather than missing ones — `not(flag)` proving a
//! goal that could not run, and a data slot binding a name where the paren spelling
//! computes — which is what makes this a defect rather than an ergonomic gap.
//!
//! ── WHERE THE MERGE IS, AND WHERE IT DELIBERATELY IS NOT ─────────────────────
//!
//! The merge is at the STORE: [`KnowledgeBase::nullary_canon`] rewrites `Fn{f, [], []}`
//! to `Ref(f)`, and `term_view::functor_view_head` no longer gives a bare name a second
//! HEAD. Together those make the four term converters the ticket first named converge
//! with no per-site edit.
//!
//! IT IS GATED ON TYPE-HOOD, not on constructor-hood, and that is a correction the
//! ticket's own plan needed. Removing the gate outright — which the plan said to do —
//! makes the STDLIB FAIL TO LOAD: 792 symbols change spelling, and for a SORT §8.3 /
//! WI-391 / WI-387 make `Ref(S)` the dispatch WILDCARD and a nullary `Fn{S}` the
//! CONCRETE spec identity. So a name with a type reading keeps both spellings and the
//! SLOT decides; a name without one — a predicate, an operation, an equation functor, a
//! namespace, a sort-nested constructor — has one term. That subsumes WI-511's gate.
//!
//! AN OPERATION NEEDS ONE MORE THING, because a predicate goal is answered by MATCHING
//! and an operation goal by REDUCING: `Loader::nullary_op_call_or_ref` builds the same
//! `Expr::Apply` node for both spellings in a rule body. MEASURED with the storage canon
//! in and that elaboration out: the WI-580 relational hook fired IDENTICALLY for `:-
//! flag` and `:- flag()` (same functor, `declared_arity == Some(0)`,
//! `bare_bodied_bool_relation == true`) and the two still answered 0 and 1 — the whole
//! divergence was the node shape.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! **1 — THE STORAGE CANON.** Restore the `is_constructor_symbol` gate in
//! `KnowledgeBase::nullary_canon`. Fells [`the_nullary_predicate_2x2_is_all_ones`],
//! [`a_nullary_simp_head_defines_in_both_spellings`], and — outside this file —
//! `wi_719fj_dotted_paren_less_citation_test::the_two_nullary_spellings_are_one_term`,
//! `…::a_predicate_assembled_from_both_spellings_answers_from_either` (2 of its 4 rows),
//! `wi_p85z7_paren_less_nullary_head_test::a_bare_equation_subject_defines_…`,
//! `wi881_float_arithmetic_test::a_bare_nullary_simp_head_fires_…`,
//! `kb::term_view::nullary_head_tests::a_nullary_non_constructor_is_one_term_…`,
//! `kb::discrim::tests::a_nullary_application_matches_its_bare_spelling_for_any_symbol`
//! (its `plain` arm only). [`a_bare_nullary_op_goal_runs_and_its_negation_fails`] and
//! [`a_bare_nullary_op_in_a_data_slot_is_a_call`] pass EITHER WAY — their axis is 2 —
//! which is what says the two changes are separable rather than one change with two
//! names.
//!
//! **2 — THE NODE ELABORATION.** Make `Loader::nullary_op_call_or_ref` always answer
//! `Expr::Ref`. Fells [`a_bare_nullary_op_goal_runs_and_its_negation_fails`] (its `r1`
//! and `r3` rows) and [`a_bare_nullary_op_in_a_data_slot_is_a_call`] (its `c1` row).
//! The 2x2 passes either way — it is a PREDICATE, answered by matching.
//!
//! **3 — THE `[simp]` LHS READ.** Drop `simp_rewrite::stored_eq_operand_functor`'s
//! `Term::Ref` arm. Fells [`a_nullary_simp_head_defines_in_both_spellings`] on BOTH
//! arms — including the PARENTHESISED one, which is what makes it a regression guard
//! and not a second reading of axis 1: with the canon in and this arm out, `rule tau()
//! <=> 7 [simp]` stopped firing too.
//!
//! **4 — THE MINT.** Restore `if introduced_by == RuleIntroduction::Predicate` on
//! `load::head_subject_name`'s `Term::Ident` arm. Fells
//! `wi_p85z7_paren_less_nullary_head_test::a_bare_equation_subject_mints_…` on its
//! `bare` arm. Nothing here sees it.

use anthill_core::eval::Value;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::{ClauseKind, KnowledgeBase};
use anthill_core::persistence::file_store::{FileConvention, FileStore};
use anthill_core::persistence::Store;

/// DEFINITE solutions only — a `.len()` counts a FLOUNDERED one as an answer
/// (WI-20260822-WZX6B), and this file's `<=>` fixtures produce exactly that shape when
/// the change is backed out: `?v <=> seven` residualizes rather than failing.
fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

/// The single DEFINITE value a unary goal `p(?v)` produces — so a row asserts the
/// VALUE and not merely that something answered. `None` when there is no definite
/// solution; panics on more than one, since every fixture here has exactly one clause.
fn only_value(kb: &mut KnowledgeBase, qn: &str) -> Option<Value> {
    let mut vs = crate::common::definite_unary(kb, qn);
    assert!(vs.len() <= 1, "{qn}: expected at most one answer, got {vs:?}");
    vs.pop()
}

/// **A — THE TICKET'S OWN 2×2**, inverted from `1 0 0 1` to `1 1 1 1`. No dot in it:
/// the split is spelling-independent, which is why 719FJ could pin it and not fix it.
#[test]
fn the_nullary_predicate_2x2_is_all_ones() {
    const SRC: &str = "\
fact bczj(1)
namespace zzczj.sp
  rule tgtA :- bczj(1)
  rule tgtB() :- bczj(1)
  rule aa(1) :- tgtA
  rule ab(1) :- tgtA()
  rule ba(1) :- tgtB
  rule bb(1) :- tgtB()
end
";
    let mut kb = crate::common::load_kb_with(SRC);
    for (goal, why) in [
        ("aa", "paren-less head, paren-less goal"),
        ("ab", "paren-less head, APPLIED goal"),
        ("ba", "applied head, paren-less goal"),
        ("bb", "applied head, applied goal"),
    ] {
        assert_eq!(
            answers(&mut kb, &format!("zzczj.sp.{goal}(?x)")),
            1,
            "zzczj.sp.{goal}: {why} — one predicate, reachable in both spellings"
        );
    }
}

/// **B — A NULLARY BOOL OPERATION AS A GOAL**, and the WRONG ANSWER this removes.
///
/// `r3` is the row that matters: before this ticket `:- flag` could not run, so
/// negation-as-failure read its failure as a PROOF and `not(flag)` SUCCEEDED against a
/// `flag` whose body is `true`. §6.6 says resolution is "by syntactic position"; that
/// was it being false for one spelling.
///
/// The four rows are two PAIRS, so a regression shows up as the spellings disagreeing
/// rather than as an absolute count. `flag` is body-BACKED and rule-LESS, which is
/// WI-580's relational-view gate.
#[test]
fn a_bare_nullary_op_goal_runs_and_its_negation_fails() {
    const SRC: &str = "\
namespace zzczj.b
  import anthill.prelude.Bool
  operation flag() -> Bool = true
  rule r1(1) :- flag
  rule r2(1) :- flag()
  rule r3(1) :- not(flag)
  rule r4(1) :- not(flag())
end
";
    let mut kb = crate::common::load_kb_with(SRC);
    for (goal, want, why) in [
        ("r1", 1, "the BARE goal runs the operation's relational view"),
        ("r2", 1, "…and so does the applied one — the control"),
        (
            "r3",
            0,
            "not(flag) must FAIL: before this it SUCCEEDED, proving a goal that \
             could not run",
        ),
        ("r4", 0, "…as not(flag()) already did — the control"),
    ] {
        assert_eq!(
            answers(&mut kb, &format!("zzczj.b.{goal}(?x)")),
            want,
            "zzczj.b.{goal}: {why}"
        );
    }
}

/// **C — A NULLARY OPERATION IN A RULE-BODY DATA SLOT IS A CALL**, matching §5.4's
/// op-body rule (`typing::check_bare_ref` already gives a bare nullary op the
/// zero-arg-call TYPE; this is the resolver catching up).
///
/// ASSERTS THE VALUE, not the count: before this ticket `?v <=> seven` answered ONE
/// definite solution with `?v` bound to the SYMBOL `seven`, so a count-only row would
/// have been green on the defect. The two spellings must both bind `7`.
///
/// THE CENSUS SAID ZERO. A sweep of stdlib/, examples/, rustland/ tests and
/// anthill-todo/ found no rule-body slot naming a nullary op bare, so the population
/// this moves is new code only; the stdlib's own bare nullary ops
/// (`Additive.zero`, `Multiplicative.one`, `BoundedLattice.top`/`bottom`, `Map.empty`)
/// all sit in EQUATION HEADS, where they are patterns and unaffected.
#[test]
fn a_bare_nullary_op_in_a_data_slot_is_a_call() {
    const SRC: &str = "\
namespace zzczj.c
  import anthill.prelude.Int64
  operation seven() -> Int64 = 7
  rule c1(?v) :- ?v <=> seven
  rule c2(?v) :- ?v <=> seven()
end
";
    let mut kb = crate::common::load_kb_with(SRC);
    for (goal, why) in [
        ("c1", "the BARE slot calls the operation"),
        ("c2", "…as the applied one already did — the control"),
    ] {
        let v = only_value(&mut kb, &format!("zzczj.c.{goal}"));
        assert_eq!(
            v.as_ref().and_then(|v| crate::common::scalar_int(&kb, v)),
            Some(7),
            "zzczj.c.{goal}: {why} (before this ticket `c1` bound the SYMBOL `seven`); \
             got {v:?}"
        );
    }
}

/// **D — A `[simp]` HEAD IN BOTH SPELLINGS.** §5.3 called a bare one a TRAP ("a nullary
/// head must carry its parentheses"); that sentence is deleted with this row.
///
/// Driven through EVAL, because a `[simp]` law's whole observable is the inlining: the
/// operation is body-LESS, so an un-fired law leaves `drive` with nothing to run and
/// the call answers `OperationBodyMissing` rather than a wrong number.
#[test]
fn a_nullary_simp_head_defines_in_both_spellings() {
    for (label, head) in [("bare", "tau"), ("parens", "tau()")] {
        let src = format!(
            "namespace zzczj.d{label}\n  import anthill.prelude.Int64\n  \
             operation tau() -> Int64\n  rule {head} <=> 7 [simp]\n  \
             operation drive(n: Int64) -> Int64 = tau()\nend\n"
        );
        let mut interp = crate::common::interp_for(&src);
        match interp.call(&format!("zzczj.d{label}.drive"), &[Value::Int(0)]) {
            Ok(Value::Int(7)) => {}
            other => panic!("{label}: the law must inline and answer 7; got {other:?}"),
        }
    }
}

/// **F — A BARE FIELDED ENTITY IN A LOGICAL POSITION IS §8.3's ALL-FIELDS-FRESH
/// PATTERN.** `fact account` IS `fact account()`; `:- account` searches what
/// `:- account()` searches.
///
/// CHOSEN OVER keeping the phantom `account/0` atom (which nothing could query — it was
/// invisible to `:- account()` and there was no other spelling that reached it) and over
/// refusing: §8.3 already applies the expansion "whenever the functor is a registered
/// entity", and one level up the spec already reads a bare SPEC name that way (`fact
/// Monoid` IS `fact Monoid[?]`). F2 makes the value level match the type level.
///
/// FIVE POSITIONS, and each is a separate call site — `Loader::convert_subject_term` is
/// the funnel for the rule head, the fact head and the proof step; `convert_query_term`
/// and `build_body_atom_occurrence_inner`'s goal arm are the other two. BACKED OUT at
/// ANY ONE of them, exactly that position's row fails:
///   * the funnel → `bare_fact_head` (the `fact account` half)
///   * the goal arm → `bare_goal`
///   * the query converter → `bare_query_pattern`
///
/// AND THE DATA-SLOT CONTROL IS THE POINT OF THE SPLIT: `?t <=> account` still binds the
/// REFERENCE, because a data slot holds a term whose spelling is its identity (WI-756)
/// and `Ref(WorkItem)` is the sort-as-value `facts_of(kb(), WorkItem)` reads. It passes
/// either way BY DESIGN — it is what says the expansion is position-directed and not a
/// blanket rewrite of every bare entity name.
#[test]
fn a_bare_fielded_entity_in_a_logical_position_is_the_pattern() {
    const SRC: &str = "\
namespace zzczj.f
  import anthill.prelude.{Int64, String}
  entity account(id: Int64, name: String)
  fact account(id: 1, name: \"a\")
  rule bare_goal(1) :- account
  rule applied_goal(1) :- account()
  rule data_slot(?t) :- ?t <=> account
end
";
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        answers(&mut kb, "zzczj.f.bare_goal(?x)"),
        1,
        "a bare entity GOAL is the pattern `account()` — it answered 0 before"
    );
    assert_eq!(
        answers(&mut kb, "zzczj.f.applied_goal(?x)"),
        1,
        "…as the applied spelling already did — the control"
    );

    // THE CONTROL for position-directedness: a DATA slot keeps the reference.
    let bound = only_value(&mut kb, "zzczj.f.data_slot");
    assert!(
        bound.is_some_and(|v| kb.value_symbol(&v).is_some()),
        "a bare entity in a DATA slot still binds the NAME, not a fresh pattern"
    );

    // THE FACT HEAD: `fact account` is the universal claim, so a specific goal finds it.
    const BARE_FACT: &str = "\
namespace zzczj.fb
  import anthill.prelude.{Int64, String}
  entity account(id: Int64, name: String)
  fact account
  rule found(1) :- account(id: 5, name: ?)
end
";
    let mut kb = crate::common::load_kb_with(BARE_FACT);
    assert_eq!(
        answers(&mut kb, "zzczj.fb.found(?x)"),
        1,
        "`fact account` is `fact account()` — the universal fact, which a specific \
         goal matches; it answered 0 before"
    );

    // THE QUERY PATTERN, through the converter the CLI uses. Asserting the BINDINGS,
    // not just that something answered: a pattern that expanded to the wrong shape
    // would still count 1 against a universal fact.
    let mut kb = crate::common::load_kb_with(SRC);
    let goal = crate::common::query_pattern_term(&mut kb, "zzczj.f.account");
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    let definite: Vec<_> = sols.iter().filter(|s| s.is_definite()).collect();
    assert_eq!(
        definite.len(),
        1,
        "the bare query pattern `account` searches what `account()` searches"
    );
    // The VALUES, not a count: the pattern must have bound `id` to 1 and `name` to
    // "a", which a nullary atom that merely matched could not do.
    let subst = definite[0].subst.clone();
    let mut bound: Vec<String> = subst
        .iter_terms()
        .map(|(_, t)| format!("{:?}", kb.get_term(t)))
        .collect();
    bound.sort();
    assert_eq!(
        bound,
        vec![
            "Const(Int(1))".to_string(),
            "Const(String(\"a\"))".to_string()
        ],
        "…and it binds BOTH declared fields — the all-fields-fresh pattern, not a \
         nullary atom that happens to match"
    );
}

/// **THE PERSISTENCE ROUND TRIP.** The nullary canon changes which TERM a name on disk
/// reloads to, so the writer and the reader have to be checked as a PAIR — a spelling
/// change has a writer population and a reader population, and the retract key is where
/// they meet (`FileStore::retract` matches a fact by its PRINTED text).
///
/// A HAND-WRITTEN `p()` IS THE FIXTURE, not one this run printed: the point is a store
/// written by an OLDER printer, or by a person. `persistence::print` has always written a
/// nullary term bare — its generic tail omits the parentheses for an argument-less term —
/// so `p()` on disk is the shape only a hand edit produces, and it must still be
/// retractable by the key `p`.
///
/// WHAT THIS SHOWS ABOUT THE CHANGE: the round trip was BROKEN before and is closed now.
/// `p` on disk reloaded as `Term::Ref(p)` while the KB held `Fn{p, [], []}` for the same
/// name, so the two sides of the content-addressed comparison were two terms. They are
/// one now, which is why this row can be written at all.
#[test]
fn a_hand_written_nullary_fact_is_retractable_by_its_bare_key() {
    let dir = tempfile::tempdir().expect("temp dir");
    std::fs::write(
        dir.path().join("facts.anthill"),
        "fact pczj()\nfact survivorczj()\n",
    )
    .unwrap();

    let mut store = FileStore::new(dir.path().to_path_buf(), FileConvention::Flat);
    let mut kb = KnowledgeBase::new();
    let sort = ClauseKind::Fact;
    let domain = kb.intern("test");

    // The KB's own term for the name — built the ordinary way, i.e. through the canon.
    let p = kb.make_name_term("pczj");
    let p_id = kb.assert_fact(p, sort, domain, None);

    store.retract(&kb, p_id).unwrap();
    kb.retract(p_id);
    store.flush(&kb).unwrap();

    let after = std::fs::read_to_string(dir.path().join("facts.anthill")).unwrap();
    assert!(
        !after.contains("pczj"),
        "the hand-written `pczj()` must be retracted by the KB's bare `pczj` key; \
         file is now: {after:?}"
    );
    // NOT `keepczj`: that CONTAINS `pczj`, so the `!after.contains("pczj")` row above
    // would have read the survivor as the retracted fact and passed for the wrong
    // reason — measured, it failed with the file already correct.
    assert!(
        after.contains("survivorczj"),
        "…and its neighbour must survive — the control that says the retract is \
         keyed and not a truncation; file is now: {after:?}"
    );
}
