//! WI-20260901-719FJ — A DOTTED PAREN-LESS CITATION IS THE NAME IT SPELLS, IN EVERY
//! LOGICAL POSITION.
//!
//! `nsx.tgt` written without a trailing `(…)` has no application to hang a functor on,
//! so the converter folds it into a MINTED `field_access(nsx, Ident(tgt))` chain (§6.7:
//! a name with no application is dot projection). That chain is what the spelling lowers
//! to EVERYWHERE, and until this ticket only ONE of its positions had been decided:
//! proposal 052 §6.7 reads it in an operation body as the `Relation[T]` VALUE
//! (`Queen.find.map(…)`, WI-714). Every other one was silent —
//!
//! | position | before | after |
//! |---|---|---|
//! | rule head `rule nsx.tgt :- b(1)` | clause filed under `field_access`; the rule DROPPED | joins the predicate `nsx.tgt` |
//! | fact head `fact nsx.tgt` | same | same |
//! | body goal `:- nsx.tgt` | a `field_access` goal with no clauses — answers nothing, and `not(…)` of it SUCCEEDS | the nullary goal |
//! | query pattern `nsx.tgt` | `conditional / residual: eq(field_access(nsx, tgt), true)` | a definite answer |
//! | proof step `rule nsx.tgt :- nsx.tgt by …` | the record the prover dispatches on named `field_access` | names the predicate |
//! | operation body `nsx.tgt` | the `Relation[T]` value | UNCHANGED |
//!
//! THE TICKET NAMED THREE POSITIONS; THE CENSUS FOUND SIX. The head, the goal and the
//! operation body are its own; a `fact` head, a QUERY PATTERN and a structured PROOF
//! STEP are the same defect at three more converters, and each was found by asking which
//! sites convert a term that states a PROPOSITION rather than by reading the ticket's
//! list. A `fact` head is NOT §6.1's "a fact head introduces no scoped name" question,
//! which is about INTRODUCING: a dotted head REFERENCES, and the reference was being
//! dropped.
//!
//! THE RULE THAT DECIDES IS THE POSITION, NEVER THE QUALIFICATION, and that is the whole
//! of this ticket. The ONE-SEGMENT spelling already worked that way: `person_row` is a
//! relation VALUE in an operation body (WI-714) and a nullary GOAL in a rule body
//! (WI-20260821-P85Z7). The dotted spelling had only the value half. So every row below
//! is written as the PAIR that says so — the dotted spelling beside the one-segment or
//! parenthesised twin of the same program — rather than as an absolute nobody can rank.
//!
//! WHAT THIS DELIBERATELY DOES NOT CHANGE, and why each is a different question:
//!
//!  * A **DATA SLOT** keeps the chain. `fact holds(nsx.tgt)` and the query
//!    `holds(nsx.tgt)` must build ONE term — a term's spelling is its identity, and
//!    normalizing one side of a match is never a repair (WI-756, and the regression
//!    WI-20260825-P9Y67 measured from the other side). Only a SUBJECT is collapsed.
//!  * The **PAREN-LESS / PARENTHESISED TERM SHAPE** stays split, for the dotted spelling
//!    exactly as for the one-segment one: a paren-less subject is a `Ref` leaf and a
//!    parenthesised one a zero-argument `Fn`, and the two do not unify. That split is
//!    SPELLING-INDEPENDENT, predates this ticket and is WI-20260902-CZJ2N's —
//!    [`the_two_nullary_spellings_are_still_two_terms`] pins it with the ONE-segment
//!    fixture that has no dot in it at all. It is why the ticket's own mixed fixture
//!    (`rule tgt()` inside, `rule nsx.tgt` outside) lands two clauses that no single
//!    goal spelling reaches; written in ONE spelling, as
//!    [`a_dotted_paren_less_head_joins_the_predicate_it_names`] writes it, the goal
//!    answers both.
//!  * A **CONSTRAINT** body is the one proposition-shaped position NOT reached — see
//!    [`a_constraint_body_is_inert_for_every_spelling`], which measures why: a denial is
//!    stored as an inert fact and registered as no guard, so a goal there decides
//!    nothing whatever it names, dotted or not.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! NINE AXES AND TWELVE LEGS — three of the axes are written at TWO call sites each, and
//! a leg that is not backed out on its own is a leg nothing measures. Each back-out is
//! PRESENT-BUT-WRONG rather than deleted, and each was APPLIED AND RUN over the WHOLE
//! `wi_tests` binary — 4 020 rows run (3 more are `#[ignore]`d), not a hand-picked
//! neighbourhood — so each list below is EXHAUSTIVE over that population: every row not
//! named passed, anywhere in the suite.
//!
//! **A — THE RULE HEAD.** `load_rule`'s head loop back to `convert_term`. **2 ROWS:**
//! [`a_dotted_paren_less_head_joins_the_predicate_it_names`],
//! [`a_dotted_paren_less_head_lands_where_the_applied_spelling_lands`].
//!
//! **B — THE FACT HEAD.** `load_fact`'s term build back to `convert_term`. **1 ROW:**
//! [`a_dotted_paren_less_fact_head_asserts_on_the_name`].
//!
//! **C — THE BODY GOAL.** `build_body_atom_occurrence_inner`'s `at_goal` collapse made
//! to answer `None`. **2 ROWS:** [`a_dotted_paren_less_body_goal_runs_the_predicate`],
//! [`a_negated_dotted_paren_less_goal_is_not_a_free_proof`].
//!
//! **D — THE QUERY PATTERN.** `convert_query_term`'s entry collapse made to answer
//! `None`. **3 ROWS:** [`a_dotted_paren_less_query_pattern_answers_definitely`],
//! [`a_dotted_paren_less_head_joins_the_predicate_it_names`] (whose goal spelling is
//! itself a dotted citation, as its own comment says), and
//! `wi_p85z7_paren_less_nullary_head_test::a_bare_nullary_clause_is_indexed_under_the_scoped_symbol`
//! — the P85Z7 row whose "and the goal reaches them" assertion was passing on a RESIDUAL
//! until this ticket, and now measures.
//!
//! **E — THE CLAUSE CENSUS, TWO LEGS.** `head_subject_name`'s chain arm (the `rule`
//! head) and `fact_head_subject_name`'s (the `fact` head) are separate walks over one
//! question. **EACH FELLS 1 ROW, THE SAME ONE:**
//! [`a_dotted_paren_less_main_entry_clause_reaches_the_secondary_entry_census`], on its
//! `rule-bare` arm and its `fact-bare` arm respectively. The `fact` leg was MISSED on the
//! first cut — the suite was green with the census still under-counting a clause that had
//! started landing — and was found by re-reading the diff.
//!
//! **F — THE DIAGNOSTIC'S HEAD READING.** `bodyless_declares_nothing_detail`'s chain
//! arm. **1 ROW:** [`a_body_less_dotted_paren_less_head_reads_as_a_qualified_name`], on
//! its BARE arm; its PARENS arm and its `?x.f` control pass either way.
//!
//! **G — THE HEAD'S WRITTEN NAME, TWO LEGS.** `head_name_as_written`'s CHAIN arm, which
//! is what lets WI-1075's marked-absolute refusal see a folded path; and the FACT site's
//! head walk, which reads all three shapes where it used to read `Term::Fn` alone.
//! **EACH FELLS 1 ROW, THE SAME ONE:**
//! [`a_marked_absolute_dotted_paren_less_head_that_names_nothing_is_refused`] — the chain
//! leg on its `*-bare` dotted arms, the fact-shape leg on its `fact-1seg` arm. The second
//! leg shipped in an earlier cut as an unmeasured "no-op" under a comment that was FALSE
//! (`/code-review` found it, and measured `fact ..zznosuch` loading clean without it): a
//! ONE-segment marked path is a `Term::Ident`, so the fact side had been missing WI-1075's
//! refusal that the rule side got at P85Z7.
//!
//! **H — THE PROOF STEP, TWO LEGS.** `encode_proof_step`'s HEAD conversion and its BODY
//! conversion are separate lines, so they are separate back-outs. **EACH FELLS 1 ROW,
//! THE SAME ONE:** [`a_proof_step_reads_the_dotted_citation_as_the_name_too`]. An earlier
//! cut of that row wrote the citation only in the step's BODY, and the HEAD-leg back-out
//! then PASSED — half the change measured. The fixture writes it in both, and the row
//! counts `tgt` twice for exactly that reason.
//!
//! **I — THE SORT-BODY PRE-SCAN.** `scan_sort_carrier_bindings`' fact head back to
//! `convert_term`. **1 ROW:**
//! [`a_dotted_paren_less_fact_head_in_a_sort_body_is_reported_once`]. It fells NOTHING
//! else, and that is worth saying: the pre-scan and `load_fact` read one parse node, and
//! the second reading is invisible until a name in it is AMBIGUOUS — then it is a second
//! report about a root segment the author never wrote.
//!
//! **PASS UNDER ALL TWELVE, BY DESIGN** — the rows that say what must not move:
//! [`an_operation_body_still_reads_the_dotted_citation_as_the_relation_value`] (052
//! §6.7), [`a_data_slot_still_stores_the_chain_on_both_sides_of_a_match`],
//! [`a_hand_written_field_access_is_still_a_call_in_both_positions`] (the mint gate's own
//! fixture), [`a_dotted_equation_subject_still_fires_nothing`],
//! [`the_two_nullary_spellings_are_still_two_terms`] (the PIN), and
//! [`a_constraint_body_is_inert_for_every_spelling`] (the boundary).
//!
//! STDLIB LOADS: TWO —
//! [`an_operation_body_still_reads_the_dotted_citation_as_the_relation_value`] and
//! [`a_dotted_equation_subject_still_fires_nothing`] need an interpreter. Every other row
//! uses `try_load_kb_with` / `load_kb_with`.

use anthill_core::eval::Value;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// DEFINITE solutions only. A residual is the subject of half this file — the query
/// pattern `nsx.tgt` used to come back `conditional / residual: eq(field_access(nsx,
/// tgt), true)` — and `resolve(..).len()` counts a floundered "solution" as an answer
/// (WI-20260822-WZX6B, `common::definite_unary`'s doc). Counting them here would make
/// every row below pass against the defect it exists to measure.
fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&goal_slice(goal), &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

fn goal_slice(goal: anthill_core::kb::term::TermId) -> [anthill_core::kb::term::TermId; 1] {
    [goal]
}

/// EVERY solution, definite or not — the instrument for the one row whose subject IS the
/// residual.
fn all_and_definite(kb: &mut KnowledgeBase, pattern: &str) -> (usize, usize) {
    let goal = crate::common::query_pattern_term(kb, pattern);
    let sols = kb.resolve(&goal_slice(goal), &ResolveConfig::default());
    (sols.len(), sols.iter().filter(|s| s.is_definite()).count())
}

/// The clauses stored under the symbol `qn` names — `None` when NOTHING is named `qn`.
/// Shape-agnostic (`rules_by_functor` keys on `head_functor`, which reads `Fn`, `Ref` and
/// `Ident` alike), so it answers "did the clause land on this predicate" without also
/// answering "which goal spelling reaches it".
fn clauses(kb: &KnowledgeBase, qn: &str) -> Option<usize> {
    let sym = kb.try_resolve_symbol(qn)?;
    Some(kb.rules_by_functor(sym).len())
}

// ══════════════════════════════════════════════════════════════════════════════
// THE FOUR LOGICAL POSITIONS
// ══════════════════════════════════════════════════════════════════════════════

/// AXIS A — THE RULE HEAD. `rule zz719.hd.tgt :- b719(1)` joins the predicate it names.
///
/// The fixture is INVERTED so a dropped clause is a visible `0` rather than an agreement:
/// the namespace's OWN clause is FALSE, so `readsIt` answers only if the dotted head's
/// clause landed AND is reachable. Pre-fix it answered 0 and `zz719.hd.tgt` held ONE
/// clause; the whole rule went to a `field_access` nothing can cite.
///
/// WRITTEN IN ONE SPELLING ON BOTH SIDES, which is what makes "the goal answering both"
/// true here: the paren-less and parenthesised nullary subjects are different TERMS
/// (`Ref` vs a zero-argument `Fn`) and that split is spelling-independent — see
/// [`the_two_nullary_spellings_are_still_two_terms`], which pins it with no dot in it.
#[test]
fn a_dotted_paren_less_head_joins_the_predicate_it_names() {
    const SRC: &str = "\
fact b719(1)
namespace zz719.hd
  rule tgt :- b719(999)
  rule readsIt(1) :- tgt
end
rule zz719.hd.tgt :- b719(1)
";
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        clauses(&kb, "zz719.hd.tgt"),
        Some(2),
        "the dotted paren-less head lands its clause on the predicate it names — \
         pre-fix `zz719.hd.tgt` held ONE clause and the rule was dropped in silence"
    );
    assert_eq!(
        answers(&mut kb, "zz719.hd.readsIt(?x)"),
        1,
        "and the clause is REACHED: the namespace's own clause is FALSE, so this answers \
         only from the dotted head's"
    );
    assert_eq!(
        answers(&mut kb, "zz719.hd.tgt"),
        1,
        "and the goal reaches it: the namespace's own clause is FALSE, so the ONE answer \
         is the dotted head's (this arm needs axis D too, since the pattern is itself a \
         dotted paren-less citation)"
    );

    // "THE GOAL ANSWERING BOTH", measured as REACHABILITY rather than as a count: a
    // nullary goal binds nothing, so two derivations carry the same (empty) substitution
    // and the solution set does not distinguish them. So the pair is run twice with the
    // TRUTH swapped — only the inner clause provable, then only the dotted head's — and
    // the goal must answer in BOTH programs. A clause that landed on the symbol but that
    // the goal cannot reach fails whichever arm owns it, while `clauses` still reads 2.
    for (label, inner, outer) in [
        (
            "only the namespace's own clause is true",
            "b719(1)",
            "b719(999)",
        ),
        (
            "only the dotted head's clause is true",
            "b719(999)",
            "b719(1)",
        ),
    ] {
        let src = format!(
            "fact b719(1)\nnamespace zz719.hd2\n  rule tgt :- {inner}\nend\n\
             rule zz719.hd2.tgt :- {outer}\n"
        );
        let mut kb = crate::common::load_kb_with(&src);
        assert_eq!(
            clauses(&kb, "zz719.hd2.tgt"),
            Some(2),
            "{label}: two clauses"
        );
        assert_eq!(
            answers(&mut kb, "zz719.hd2.tgt"),
            1,
            "{label}: the goal reaches it — pre-fix the second arm answered 0 and the \
             predicate held one clause"
        );
    }

    // THE CONTROL — its own fixture, parenthesised throughout. It says the machinery
    // works at all, and passes either way.
    const PARENS: &str = "\
fact b719(1)
namespace zz719.hdp
  rule tgt() :- b719(999)
  rule readsIt(1) :- tgt()
end
rule zz719.hdp.tgt() :- b719(1)
";
    let mut kb = crate::common::load_kb_with(PARENS);
    assert_eq!(clauses(&kb, "zz719.hdp.tgt"), Some(2));
    assert_eq!(
        answers(&mut kb, "zz719.hdp.readsIt(?x)"),
        1,
        "the parenthesised spelling of the same program — the control"
    );
}

/// AXIS C — THE RULE-BODY GOAL. `:- zz719.gl.tgt` runs the predicate.
#[test]
fn a_dotted_paren_less_body_goal_runs_the_predicate() {
    const SRC: &str = "\
fact b719(1)
namespace zz719.gl
  rule tgt :- b719(1)
  rule pgt() :- b719(1)
end
rule readerDot719(1) :- zz719.gl.tgt
rule readerCtl719(1) :- zz719.gl.pgt()
";
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        answers(&mut kb, "readerDot719(?x)"),
        1,
        "the dotted paren-less goal names the predicate — pre-fix it was a `field_access` \
         application with no clauses, so it answered NOTHING in silence"
    );
    // THE CONTROL — the APPLIED dotted spelling, which already worked. Passes either
    // way, and is what says a dotted goal can reach a namespace's predicate at all.
    assert_eq!(
        answers(&mut kb, "readerCtl719(?x)"),
        1,
        "the applied dotted goal is the control"
    );
}

/// AXIS C, THE SOUNDNESS HALF — a goal that cannot be reached is not a proof of its
/// negation. `not(zz719.nf.holds)` USED TO SUCCEED: negation-as-failure read the broken
/// `field_access` goal's failure as a refutation of a predicate that holds.
#[test]
fn a_negated_dotted_paren_less_goal_is_not_a_free_proof() {
    const SRC: &str = "\
fact b719(1)
namespace zz719.nf
  rule holds :- b719(1)
  rule never :- b719(999)
end
rule notHolds719(1) :- not(zz719.nf.holds)
rule notNever719(1) :- not(zz719.nf.never)
";
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        answers(&mut kb, "notHolds719(?x)"),
        0,
        "`zz719.nf.holds` HOLDS, so its negation must not — pre-fix this answered 1"
    );
    // THE CONTROL — the same wrapper over a predicate that really is empty. Passes
    // either way, and without it the row above could be passed by breaking NAF outright.
    assert_eq!(
        answers(&mut kb, "notNever719(?x)"),
        1,
        "`zz719.nf.never` is empty, so its negation holds — NAF still works"
    );
}

/// AXIS D — THE QUERY PATTERN. Its subject IS the residual, so this row counts BOTH
/// totals: pre-fix `anthill query 'zz719.qp.tgt'` came back `conditional / residual:
/// eq(field_access(zz719.qp, tgt), true)` — ONE "solution" that decides nothing, and
/// which a `.len()` counts as an answer.
#[test]
fn a_dotted_paren_less_query_pattern_answers_definitely() {
    const SRC: &str = "\
fact b719(1)
namespace zz719.qp
  rule tgt :- b719(1)
  rule pgt() :- b719(1)
end
";
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        all_and_definite(&mut kb, "zz719.qp.tgt"),
        (1, 1),
        "one solution and it DECIDES — pre-fix (1, 0): the same count, and not an answer"
    );
    // THE CONTROL — the applied spelling of the same question, on its own predicate.
    // Passes either way.
    assert_eq!(
        all_and_definite(&mut kb, "zz719.qp.pgt()"),
        (1, 1),
        "the applied pattern is the control — it was always definite"
    );
}

/// AXIS B — THE FACT HEAD. `fact zz719.ft.tgt` asserts on the name, exactly as
/// `fact zz719.ft.tgt()` does. §6.1 makes a fact head unscoped — it introduces no name —
/// but a DOTTED head REFERENCES, and the reference was landing under `field_access`.
#[test]
fn a_dotted_paren_less_fact_head_asserts_on_the_name() {
    const SRC: &str = "\
fact b719(1)
namespace zz719.ft
  rule tgt :- b719(999)
  rule readsIt(1) :- tgt
end
fact zz719.ft.tgt
";
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        clauses(&kb, "zz719.ft.tgt"),
        Some(2),
        "the fact joins the predicate its head names"
    );
    assert_eq!(
        answers(&mut kb, "zz719.ft.readsIt(?x)"),
        1,
        "and is REACHED — the rule's own clause is false, so this answers from the fact"
    );

    // THE CONTROL — its own fixture, parenthesised throughout.
    const PARENS: &str = "\
fact b719(1)
namespace zz719.ftp
  rule tgt() :- b719(999)
  rule readsIt(1) :- tgt()
end
fact zz719.ftp.tgt()
";
    let mut kb = crate::common::load_kb_with(PARENS);
    assert_eq!(clauses(&kb, "zz719.ftp.tgt"), Some(2));
    assert_eq!(answers(&mut kb, "zz719.ftp.readsIt(?x)"), 1);
}

// ══════════════════════════════════════════════════════════════════════════════
// THE DIAGNOSTICS THAT HAVE TO READ THE HEAD THE SAME WAY
// ══════════════════════════════════════════════════════════════════════════════

/// AXIS F — a BODY-LESS dotted paren-less head declares nothing, and must SAY the reason
/// its parenthesised twin says. This is P85Z7's axis D one spelling over: that ticket
/// made `..nosuchxyz` and `..nosuchxyz()` share the qualified sentence, and noted at its
/// site that a MULTI-SEGMENT `nsx.tgt` still got the DESUGARING sentence instead, because
/// the chain is minted. One head, one verdict, two sentences.
#[test]
fn a_body_less_dotted_paren_less_head_reads_as_a_qualified_name() {
    for (label, head) in [("bare", "zz719.dn.tgt"), ("parens", "zz719.dn.tgt()")] {
        let errs = crate::common::try_load_kb_with(&format!(
            "namespace zz719.dn{label}\n  rule {head}\nend\n"
        ))
        .err()
        .unwrap_or_else(|| panic!("{label}: a body-less qualified head declares nothing"));
        assert!(
            errs.iter().any(|e| e.contains("is a QUALIFIED name")),
            "{label}: the refusal must EXPLAIN itself by the qualified spelling, the same \
             way for both spellings of one head; got {errs:#?}"
        );
    }

    // THE CONTROL — the shape that still earns the DESUGARING sentence: a VALUE-rooted
    // dot, whose chain has a variable at the root and so spells no name. Passes either
    // way, and without it the row above could be passed by deleting that sentence.
    let errs = crate::common::try_load_kb_with("namespace zz719.dnv\n  rule ?x.f\nend\n")
        .err()
        .expect("a body-less value-rooted dot head declares nothing");
    assert!(
        errs.iter().any(|e| e.contains("DESUGARING")),
        "a `?x.f` head really does carry the accessor's functor and must keep saying so: \
         {errs:#?}"
    );
}

/// AXIS G — WI-1075's refusal, reached by the DOTTED paren-less spelling. A marked head
/// that names nothing must not fall to the WI-476 bare intern and store a clause under a
/// symbol nothing can cite; the chain escaped it because it has no functor symbol to
/// read — `head_name_as_written` now spells the name the author wrote.
#[test]
fn a_marked_absolute_dotted_paren_less_head_that_names_nothing_is_refused() {
    for (label, item, named) in [
        ("rule-bare", "rule ..nosuch719.tgt :- b719(1)", "..nosuch719.tgt"),
        ("rule-parens", "rule ..nosuch719.tgt() :- b719(1)", "..nosuch719.tgt"),
        ("fact-bare", "fact ..nosuch719.tgt", "..nosuch719.tgt"),
        ("fact-parens", "fact ..nosuch719.tgt()", "..nosuch719.tgt"),
        // THE ONE-SEGMENT MARKED FACT HEAD, which is the arm this ticket's widening of
        // `load_fact`'s head walk to `Term::Ident` actually closes — `..zz` is a
        // ONE-segment path, so the converter builds it as a `Term::Ident` carrying the
        // marker, and reading only `Term::Fn` there let `fact ..nosuch719` load CLEAN and
        // assert under a symbol nothing can cite. WI-1075's own defect on the `fact`
        // side; the RULE side got the `Term::Ident` arm at P85Z7 and the fact side did
        // not. Found by `/code-review`, which measured a comment here claiming the
        // widening was a no-op.
        ("fact-1seg", "fact ..nosuch719", "..nosuch719"),
        ("rule-1seg", "rule ..nosuch719 :- b719(1)", "..nosuch719"),
    ] {
        let errs = crate::common::try_load_kb_with(&format!("fact b719(1)\n{item}\n"))
            .err()
            .unwrap_or_else(|| {
                panic!("{label}: a marked head naming nothing must be refused, not bare-interned")
            });
        crate::common::assert_refused_naming(
            &errs,
            &[named],
            "the refusal must name the path the author wrote",
        );
    }

    // THE CONTROL — the SAME marked spelling, RESOLVABLE, in both spellings. It must keep
    // landing its clause on the predicate it names; the refusal is about naming nothing,
    // never about the marker.
    for (label, head) in [("bare", "..tgt719ok"), ("parens", "..tgt719ok()")] {
        let kb = crate::common::load_kb_with(&format!(
            "fact b719(1)\nrule tgt719ok :- b719(1)\nnamespace zz719.ok{label}\n  \
             rule {head} :- b719(1)\nend\n"
        ));
        assert_eq!(
            clauses(&kb, "tgt719ok"),
            Some(2),
            "{label}: a resolvable marked head joins the predicate it names"
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// WHAT MUST NOT MOVE
// ══════════════════════════════════════════════════════════════════════════════

/// PROPOSAL 052 §6.7 — THE VALUE POSITION IS UNCHANGED. The same spelling in an
/// OPERATION BODY is the `Relation[T]` value, which is what makes `Person.rows.isEmpty`
/// a zero-arg member call on a relation rather than a nullary goal. Driven end to end
/// through the interpreter, because "it loads clean" would keep passing if the citation
/// silently became a name here.
///
/// GREEN BEFORE AND AFTER. It is the row that says the split this ticket introduces is
/// between POSITIONS and not between spellings.
#[test]
fn an_operation_body_still_reads_the_dotted_citation_as_the_relation_value() {
    const SRC: &str = r#"
namespace zz719.rel
  import anthill.prelude.{String, Int64, Bool}

  sort Person
    entity person(name: String, age: Int64)
    -- EMPTY: no fact has age 999.
    rule rows(?name, ?age) :- person(name: ?name, age: 999)
    -- NON-EMPTY.
    rule all(?name, ?age) :- person(name: ?name, age: ?age)
  end
  fact person(name: "alice", age: 30)

  operation emptyOne() -> Bool effects Error = Person.rows.isEmpty
  operation fullOne() -> Bool effects Error = Person.all.isEmpty
end
"#;
    let mut interp = crate::common::interp_for(SRC);
    for (path, want) in [("zz719.rel.emptyOne", true), ("zz719.rel.fullOne", false)] {
        match interp.call(path, &[]) {
            Ok(Value::Bool(b)) if b == want => {}
            other => panic!(
                "{path} must answer {want}: a bare `Sort.rule` in an operation body is the \
                 relation VALUE (052 §6.7), consumed through the Stream API; got {other:?}"
            ),
        }
    }
}

/// A DATA SLOT KEEPS THE CHAIN, ON BOTH SIDES OF A MATCH. The fact stores it and the
/// query and the rule body find it — one term, three walks. Collapsing a data slot in one
/// walk and not another is the regression WI-20260825-P9Y67 measured from the other side
/// (`fact holdsN(not(true))` stopped matching `rule viaN() :- holdsN(not(true))`), and it
/// is why every position here asks the question only of its SUBJECT.
///
/// GREEN BEFORE AND AFTER.
#[test]
fn a_data_slot_still_stores_the_chain_on_both_sides_of_a_match() {
    const SRC: &str = "\
fact b719(1)
namespace zz719.ds
  rule tgt :- b719(1)
end
fact holds719(zz719.ds.tgt)
rule viaBody719(1) :- holds719(zz719.ds.tgt)
";
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        answers(&mut kb, "holds719(zz719.ds.tgt)"),
        1,
        "a QUERY's data slot spells the same term the fact's does"
    );
    assert_eq!(
        answers(&mut kb, "viaBody719(?x)"),
        1,
        "and so does a RULE BODY's — the third walk"
    );
}

/// THE TWO NULLARY SPELLINGS ARE STILL TWO TERMS, and this fixture has NO DOT IN IT: a
/// paren-less subject is a `Ref` leaf, a parenthesised one a zero-argument `Fn`, and they
/// do not unify. §8.3 makes that distinction for entity terms (`account()` is the
/// all-fields-fresh pattern, bare `account` a reference); for a nullary PREDICATE it has
/// no content and §8.6 says the opposite in words — "a PAREN-LESS nullary head is an
/// application of arity 0 … exactly as `rule holds()` is".
///
/// GREEN BEFORE AND AFTER, deliberately: it is a MEASUREMENT, not a claim that this is
/// right. It is here because it is the reason this ticket's own fixture has to be written
/// in ONE spelling to have "the goal answering both", and because the gap is
/// spelling-independent — it is not something the dotted citation introduces, and closing
/// it is a decision about which of the two shapes a nullary proposition is, taken in four
/// term converters at once and against §8.3's entity rule. WI-20260902-CZJ2N owns it, and
/// this 2×2 is the control it must move.
#[test]
fn the_two_nullary_spellings_are_still_two_terms() {
    const SRC: &str = "\
fact b719(1)
namespace zz719.sp
  rule tgtA :- b719(1)
  rule tgtB() :- b719(1)
  rule aa(1) :- tgtA
  rule ab(1) :- tgtA()
  rule ba(1) :- tgtB
  rule bb(1) :- tgtB()
end
";
    let mut kb = crate::common::load_kb_with(SRC);
    for (goal, want, why) in [
        (
            "aa",
            1,
            "paren-less head, paren-less goal — one term, and it answers",
        ),
        (
            "ab",
            0,
            "paren-less head, APPLIED goal — two terms, so nothing matches",
        ),
        (
            "ba",
            0,
            "applied head, paren-less goal — the same split, mirrored",
        ),
        (
            "bb",
            1,
            "applied head, applied goal — one term, and it answers",
        ),
    ] {
        assert_eq!(
            answers(&mut kb, &format!("zz719.sp.{goal}(?x)")),
            want,
            "zz719.sp.{goal}: {why}"
        );
    }
}

/// THE READING IS THE APPLIED SPELLING'S, whatever the name turns out to denote. A
/// qualified head REFERENCES (§"A rule-introduced functor is scoped where it is
/// written"), and where it lands is the ladder's answer, not this ticket's — so the two
/// spellings are asserted AGAINST EACH OTHER over the three kinds of target a dotted head
/// can hit, rather than against a number this file would have to justify.
///
/// It is what says the fix is "the chain is the name" and not "the chain is a rule": the
/// LABEL and OPERATION rows land on symbols a goal cannot reach, and they land there in
/// BOTH spellings, which is exactly the parity being claimed.
#[test]
fn a_dotted_paren_less_head_lands_where_the_applied_spelling_lands() {
    for (kind, target, name) in [
        (
            "a rule's head functor",
            "namespace {ns}\n  rule tgt() :- b719(1)\nend\n",
            "tgt",
        ),
        (
            "a rule LABEL",
            "namespace {ns}\n  rule lbl: tgt() :- b719(1)\nend\n",
            "lbl",
        ),
        (
            "an OPERATION",
            "namespace {ns}\n  sort S\n    import anthill.prelude.Int64\n    \
             operation m() -> Int64 = 1\n  end\nend\n",
            "S.m",
        ),
        (
            "NOTHING at all (WI-476's bare intern)",
            "namespace {ns}\n  rule other() :- b719(1)\nend\n",
            "nosuch",
        ),
    ] {
        let mut counts = Vec::new();
        for (label, head) in [("bare", ""), ("parens", "()")] {
            let ns = format!("zz719.lands{label}");
            let src = format!(
                "fact b719(1)\n{}rule {ns}.{name}{head} :- b719(1)\n",
                target.replace("{ns}", &ns)
            );
            let kb = crate::common::load_kb_with(&src);
            counts.push(clauses(&kb, &format!("{ns}.{name}")));
        }
        assert_eq!(
            counts[0], counts[1],
            "a dotted paren-less head naming {kind} must land where the applied spelling \
             lands — got bare {:?} vs parens {:?}",
            counts[0], counts[1]
        );
    }
}

/// WI-20260901-92VA4's CONTROL — PROVENANCE, NOT SPELLING. A HAND-WRITTEN
/// `field_access(q, x)` is a call to whatever that name denotes at that scope, never the
/// desugaring of a dot, so this ticket's collapse must not reach it. Without the
/// `is_minted` gate a written head would silently become the name `q.x`, and a written
/// goal would stop being the loud "names nothing" it is.
///
/// GREEN BEFORE AND AFTER — it is the gate's fixture, and it fails only if the gate goes.
#[test]
fn a_hand_written_field_access_is_still_a_call_in_both_positions() {
    let kb = crate::common::load_kb_with(
        "fact b719(1)\nnamespace zz719.hw\n  rule field_access(q, x) :- b719(1)\nend\n",
    );
    assert_eq!(
        clauses(&kb, "zz719.hw.field_access"),
        Some(1),
        "a written `field_access(q, x)` HEAD introduces its own predicate and files its \
         clause there — it is not the accessor and not the name `q.x`"
    );

    let errs = crate::common::try_load_kb_with(
        "fact b719(1)\nnamespace zz719.hw2\n  rule r(1) :- field_access(q, x)\nend\n",
    )
    .err()
    .expect("a written `field_access` GOAL names nothing in this scope and must be refused");
    crate::common::assert_refused_naming(
        &errs,
        &["field_access", "names nothing"],
        "the written goal keeps WI-1034's refusal — collapsing it would make it a name",
    );
}

/// THE FIFTH POSITION, NAMED RATHER THAN LEFT UNSAID: a `constraint` body. It is NOT
/// reached by this ticket, and the reason is that the position is inert for EVERY
/// spelling — a denial is stored as an inert `Constraint(head:, guard:)` fact and is not
/// registered as a guard (`load_constraint`, and the stdlib depends on that), so a goal
/// there decides nothing whatever it names.
///
/// DRIVEN so the claim is not an inherited justification: the third arm names a namespace
/// that DOES NOT EXIST, and loads just as clean as the two that do. A citation the loader
/// cannot resolve at all being silent there is the position's own property, not the
/// dotted spelling's — which is what makes this somebody else's ticket rather than a
/// fourth hole left open here.
#[test]
fn a_constraint_body_is_inert_for_every_spelling() {
    for (label, src) in [
        (
            "dotted paren-less",
            "fact b719(1)\nnamespace zz719.ct\n  rule tgt :- b719(1)\nend\n\
             constraint cx719\n  :- zz719.ct.tgt, zz719.ct.tgt\n",
        ),
        (
            "applied",
            "fact b719(1)\nnamespace zz719.ctp\n  rule tgt() :- b719(1)\nend\n\
             constraint cy719\n  :- zz719.ctp.tgt(), zz719.ctp.tgt()\n",
        ),
        (
            "a namespace that does not exist",
            "fact b719(1)\nconstraint cz719\n  :- zz719.nope.tgt, zz719.nope.tgt\n",
        ),
    ] {
        assert!(
            crate::common::try_load_kb_with(src).is_ok(),
            "{label}: a denial constraint's body is inert at load — if this ever refuses, \
             the constraint position has acquired a reading and this ticket's boundary \
             has to move with it"
        );
    }
}

/// THE CLAUSE CENSUS SEES IT TOO — 059 R3's condition (2), which refuses a SECONDARY
/// ENTRY's rule when a clause of the same predicate is written in the main entry
/// (WI-20260827-APXSS: "a qualified head introduces nothing AND STILL LANDS A CLAUSE").
///
/// The census walks `head_subject_name` for a `rule` head and `fact_head_subject_name`
/// for a `fact` one, and BOTH answered `None` for a folded chain — so a dotted PAREN-LESS
/// main-entry clause was invisible to it. That was harmless while the clause did not land
/// either; the moment it lands, a census that cannot see it under-counts, which is the
/// "many producers, one rule" failure APXSS's own ticket is about. Both halves move
/// together or neither does — and there really are two halves, which is why both keywords
/// are driven here: the `fact` walk was missed on the first cut and found by re-reading
/// the diff, not by the suite.
#[test]
fn a_dotted_paren_less_main_entry_clause_reaches_the_secondary_entry_census() {
    // BOTH HEAD KEYWORDS. `head_subject_name` and `fact_head_subject_name` are two walks
    // over one question, and fixing the `rule` one alone would leave the `fact` one
    // under-counting a clause that now lands — APXSS's own defect, one keyword over.
    for (label, head, entry) in [
        (
            "rule-bare",
            "rule Rec.freshp719 :- true",
            "rule freshp719 :- true",
        ),
        (
            "rule-parens",
            "rule Rec.freshp719() :- true",
            "rule freshp719() :- true",
        ),
        ("fact-bare", "fact Rec.freshp719", "rule freshp719 :- true"),
        (
            "fact-parens",
            "fact Rec.freshp719()",
            "rule freshp719() :- true",
        ),
    ] {
        let src = format!(
            "namespace zz719.cen{label}\n  sort Rec\n    {head}\n  end\n  \
             namespace Rec\n    {entry}\n  end\nend\n"
        );
        let errs = crate::common::try_load_kb_with(&src)
            .err()
            .unwrap_or_else(|| {
                panic!(
                    "{label}: a clause of `Rec.freshp719` in the MAIN entry must refuse the \
                 secondary entry's rule; it loaded clean"
                )
            });
        assert!(
            errs.iter()
                .any(|e| e.contains("assembled from more than one entry")),
            "{label}: condition (2) must fire — got {errs:#?}"
        );
    }
}

/// THE FIFTH POSITION THAT DOES MOVE — a STRUCTURED PROOF STEP. A step is spelled `rule
/// <heads> :- <body> by <tactic>` and is encoded into a `ProofStepRecord` the prover
/// dispatches on, so its head is a claim and its body atoms are goals, exactly as the
/// `rule` it is spelled like. A chain left there would describe a step about
/// `field_access` and match nothing.
///
/// Asserted on the RECORD, because that is what the encoding produces and what the prover
/// reads — the head is not asserted as a clause anywhere, so there is no goal to drive it
/// with. Both spellings are rendered and required to name the predicate.
#[test]
fn a_proof_step_reads_the_dotted_citation_as_the_name_too() {
    for (label, mark) in [("bare", ""), ("parens", "()")] {
        let src = format!(
            "namespace zz719.pf{label}\n  fact b719(1)\n  \
             namespace inner\n    rule tgt{mark} :- b719(1)\n  end\n  \
             rule claim(?x) :- b719(?x)\n  \
             proof claim\n    rule zz719.pf{label}.inner.tgt{mark} :- \
             zz719.pf{label}.inner.tgt{mark} by derivation\n  end\n\
             end\n"
        );
        let mut kb = crate::common::load_kb_with(&src);
        // The step rides INSIDE the `ProofRecord`'s structured body, not as a fact of its
        // own — so the record is what is rendered and searched.
        let sort = kb
            .try_resolve_symbol("anthill.realization.ProofRecord")
            .expect("resolve ProofRecord");
        let heads: Vec<_> = kb
            .rules_by_functor(sort)
            .iter()
            .map(|&r| kb.rule_head(r))
            .collect();
        let printer = anthill_core::persistence::print::TermPrinter::new(&kb);
        let rendered: Vec<String> = heads.into_iter().map(|h| printer.print_term(h)).collect();
        let ours: Vec<&String> = rendered
            .iter()
            .filter(|r| r.contains(&format!("zz719.pf{label}")))
            .collect();
        assert!(
            !ours.is_empty(),
            "{label}: the proof's step record must be emitted; saw {rendered:#?}"
        );
        for r in &ours {
            // BOTH LEGS: the step's HEAD and its BODY goal are converted at two separate
            // sites, so the fixture writes the citation in both and this asserts over the
            // whole rendered record. An earlier cut wrote the citation only in the body,
            // and the HEAD-leg back-out then passed — half the change measured, which is
            // the `false &&` trap in another shape.
            assert!(
                !r.contains("field_access"),
                "{label}: a step's head AND its body goal must name the predicate, not \
                 the accessor: {r}"
            );
            assert_eq!(
                r.matches("tgt").count(),
                2,
                "{label}: `tgt` names the head and the goal — twice, once per leg: {r}"
            );
        }
    }
}
/// ONE HEAD, ONE FAULT, ONE REPORT — the fact head inside a SORT BODY, which two
/// loader walks read. `scan_sort_carrier_bindings` pre-scans a sort's `fact` items for
/// spec-application bindings (`fact Spec[… member = X …]`) BEFORE the body is loaded, and
/// it converted the head through the generic walk while `load_fact` converts it as a
/// SUBJECT — so one parse node had two readings, and a dotted paren-less head was
/// resolved twice: once as the CHAIN (whose root segment is a name of its own) and once
/// as the PATH.
///
/// MEASURED on an ambiguous root — the same defect class WI-745's quiet owner-resolve
/// exists to prevent, from a second producer:
///
///   pre-scan aligned (shipped): `ambiguous symbol 'M.tgt' … candidates [zzI.a.M, zzI.b.M]`
///   pre-scan on the generic walk: THAT, plus `ambiguous symbol 'M' …` — the root
///                                 segment reported as a name the author never wrote
///
/// THE APPLIED SPELLING IS THE CONTROL: its functor is already the joined name, so the
/// pre-scan resolves it once either way, and it gets one report under both readings.
#[test]
fn a_dotted_paren_less_fact_head_in_a_sort_body_is_reported_once() {
    const ROOTS: &str = "namespace zz719I.a\n  namespace M719\n    rule tgt :- true\n  end\nend\n\
                         namespace zz719I.b\n  namespace M719\n    rule tgt :- true\n  end\nend\n";
    for (label, mark) in [("bare", ""), ("parens", "()")] {
        let src = format!(
            "{ROOTS}namespace zz719I.use{label}\n  import zz719I.a.*\n  import zz719I.b.*\n  \
             sort S\n    fact M719.tgt{mark}\n  end\nend\n"
        );
        let errs = crate::common::try_load_kb_with(&src)
            .err()
            .unwrap_or_else(|| panic!("{label}: an ambiguous head must be refused"));
        let ambiguous: Vec<&String> = errs
            .iter()
            .filter(|e| e.contains("ambiguous symbol"))
            .collect();
        assert_eq!(
            ambiguous.len(),
            1,
            "{label}: one head, one fault, ONE report — got {ambiguous:#?}"
        );
        assert!(
            ambiguous[0].contains("'M719.tgt'"),
            "{label}: and it names the path the author wrote, not its root segment: {:?}",
            ambiguous[0]
        );
    }
}

/// THE EQUATION SIDE, WHICH MUST NOT MOVE. §5.3: a `[simp]` head is an APPLICATION, so a
/// paren-less subject matches no redex and fires nothing — dotted or not.
///
/// It is here because `head_subject_name`'s chain arm is NOT gated on the predicate path
/// the way P85Z7's bare-name arm is, and that gate is the one thing an equation subject
/// could have been moved by. The arm needs none: [`subject_introduces`] refuses every
/// name containing a dot, so a chain subject can never mint the `EquationFunctor` stamp
/// P85Z7's gate exists to prevent, and the clause census — the one other reader — filters
/// `RuleIntroduction::Predicate` itself.
///
/// GREEN BEFORE AND AFTER, and under every back-out: it is a PIN, not a separator. What
/// it pins is that the `[simp]` reach did not widen when the head walk learned to read a
/// chain.
#[test]
fn a_dotted_equation_subject_still_fires_nothing() {
    const EQN: &str = r#"
namespace zz719.eqn
  sort Bare
    import anthill.prelude.Int64
    operation tau() -> Int64 = 1
    -- the DOTTED bare subject: a law about a redex that does not exist
    rule Bare.tau <=> 7 [simp]
    operation drive() -> Int64 = tau()
  end

  sort Paren
    import anthill.prelude.Int64
    operation tau() -> Int64 = 1
    -- the APPLICATION, dotted: the spelling that defines
    rule Paren.tau() <=> 7 [simp]
    operation drive() -> Int64 = tau()
  end
end
"#;
    let mut interp = crate::common::interp_for(EQN);
    for (path, want, why) in [
        (
            "zz719.eqn.Bare.drive",
            1,
            "a dotted bare equation subject matches no redex, so the operation's own body \
             stands",
        ),
        (
            "zz719.eqn.Paren.drive",
            7,
            "the parenthesised law IS a redex, and `[simp]` inlines it before dispatch",
        ),
    ] {
        match interp.call(path, &[]) {
            Ok(Value::Int(n)) if n == want => {}
            other => panic!("{path} must answer {want}: {why}; got {other:?}"),
        }
    }
}
