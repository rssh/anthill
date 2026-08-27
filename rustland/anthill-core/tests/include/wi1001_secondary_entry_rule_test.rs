//! WI-1001 / proposal 059 R3 — THE **NARROW** RULE A SECONDARY ENTRY MAY DECLARE.
//!
//! WI-1000 shipped R3's default-deny list with a BLANKET ban on rules, which 059 calls
//! "the enforced rule, not the intended one". The intended one is a pair of conditions:
//!
//!   1. **ITS HEAD INTRODUCES** — the head resolves to nothing in the FINISHED program,
//!      so no existing goal can be about it; and
//!   2. **ONE ENTRY OWNS THE PREDICATE** — every clause of that head is written in that
//!      same entry, keyed as 059's Definitions individuate one: the main entry, or one
//!      file's text at that address.
//!
//! Both were uncomputable when WI-1000 shipped, and each gate is one of this ticket's
//! dependencies:
//!
//!   * **WI-980 / 845G7** — (1) had no stable answer while TEXT ORDER decided whether a
//!     head introduces. It is now the phase-2 ladder answer, read against the finished
//!     name table before any head is minted.
//!   * **WI-895** — (1) was UNSOUND while a rule body could name a predicate that
//!     resolves to nothing: the "fresh" head could then have a REFERENCE older than its
//!     definition. [`the_reference_before_the_definition_is_refused_without_the_entry`]
//!     drives that gate directly, and is why (1) can now mean what it says.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! TWO BACK-OUTS, both APPLIED AND RUN over this file plus `wi1000_secondary_entry_-
//! content_test` and `wi980_rule_head_order_test` (57 rows), and both PRESENT-BUT-WRONG
//! rather than deleted — deleting the collection would fell every row for the wrong
//! reason, since nothing would then reach the judge at all.
//!
//! **A — THE NARROW RULE ITSELF.** In `SecondaryEntryPass::defer_rule`, add a
//! `self.refuse(sort, "rule", …)` beside the push, restoring WI-1000's blanket ban with
//! the new machinery still running. **15 rows fail**: 13 here, plus
//! `wi1000::an_ordinary_namespace_keeps_its_content_rules` (its entry half goes from 5
//! refusals to 6) and `wi980::a_rule_in_a_secondary_entry_is_order_free` (the spelling
//! stops loading, which is what that row existed to pin before this ticket).
//!
//! The 13 split into two kinds, and the second is worth naming because the back-out is a
//! blunt instrument for it. **Ten fail because an ADMITTED program stops loading** —
//! every row that drives a value. **Three fail on a COUNT**, not on a sentence:
//! [`a_bodyless_rule_declaration_is_refused`], [`condition_2_a_clause_in_the_main_-
//! entry_refuses_the_entrys`] and [`a_predicate_assembled_from_two_entries_is_-
//! reported_once`] each assert `errs.len() == 1`, and the back-out's own refusal is a
//! second error.
//!
//! **FOUR PASS EITHER WAY under A, by design** — and all four are refusal rows, which is
//! the honest reading: with the judge still running, a refused program is refused with
//! the same sentence before and after. [`a_rule_in_a_provides_block_stays_refused`],
//! [`an_ordinary_namespace_is_still_not_reached`], [`a_desugared_or_qualified_head_-
//! introduces_nothing`] and [`condition_1_a_head_that_does_not_introduce_is_refused`]
//! assert the SENTENCE, so what they measure is that the verdict names its condition —
//! which the WI-1000 ban did not, since it had only one reason for every rule.
//!
//! **B — THE FACT CENSUS.** Gate off the `Item::Fact` arm of `RuleHeadCollectPass::-
//! at_item`, so no fact enters the clause census. (Measured when the census was a
//! separate `fact_heads` list gated in `judge_secondary_entry_rules` itself; the
//! population the gate removes is the same one.) **Exactly 2 rows fail**, both of them
//! the census's own: [`condition_2_counts_a_main_entry_fact_as_a_clause`] and
//! [`the_fact_census_is_scoped_and_attributed`]. Nothing else moves, which is what says
//! the census reaches the population it was added for and no other.
//!
//! WI-20260827-APXSS RE-KEYED THAT CENSUS, and the rows above are unmoved by it. It is
//! no longer `(scope, name)` read off the sites that INTRODUCE a name — a clause can
//! land on the predicate while introducing nothing at that key — but where each head's
//! subject RESOLVES from the scope it is written in, and which entry's TEXT it is
//! written in. `wi_apxss_clause_landing_test` owns that rule and its back-outs.
//!
//! ── PASS EITHER WAY, BY DESIGN — the controls ────────────────────────────────
//!
//!   * [`a_rule_in_a_provides_block_stays_refused`] — the one rule site the narrow rule
//!     does NOT reach. `load_provides_block` sets the domain to the block's SPEC, so a
//!     clause there is a clause of another type's predicate whatever its head looks
//!     like. Refused before and after; the row asserts the new sentence.
//!   * [`an_ordinary_namespace_is_still_not_reached`]'s first half — 059: "nothing in R3
//!     or R4 reaches" an address no sort occupies.
//!   * [`the_reference_before_the_definition_is_refused_without_the_entry`]'s WI-895
//!     half — the gate this whole ticket rests on, and it is not this change's doing.
//!   * [`condition_2_counts_a_main_entry_fact_as_a_clause`]'s control — the same program
//!     with no secondary entry loads and answers 1, which is the answer the admitted
//!     rule used to take away in silence.
//!
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// ONE SKELETON. `entry` is the secondary entry's body, `main` the sort body's — so a
/// row differs from its neighbour in exactly the text under test.
fn fixture(ns: &str, main: &str, entry: &str) -> String {
    format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, Bool}}\n  \
         sort Rec\n    entity rec(n: Int64)\n{main}  end\n  \
         namespace Rec\n{entry}  end\nend\n"
    )
}

fn errors_of(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default()
}

/// The R3 refusals only — so a row can say "R3 was silent" without claiming the whole
/// program had nothing else to report.
fn r3_errors(src: &str) -> Vec<String> {
    errors_of(src)
        .into_iter()
        .filter(|e| e.contains("is not allowed in a secondary entry"))
        .collect()
}

/// How many solutions `pattern` has, through the shipped query-pattern path.
fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// The clauses stored under `qn` — `None` when nothing is named `qn` at all, which is
/// the distinction a bare answer count cannot make.
fn clauses(kb: &KnowledgeBase, qn: &str) -> Option<usize> {
    let sym = kb.try_resolve_symbol(qn)?;
    Some(kb.rules_by_functor(sym).len())
}

// ── The capability ──────────────────────────────────────────────────────────

/// THE CAPABILITY WI-1000 COULD NOT SHIP. A fresh head, every clause of it in this one
/// entry — 059's two conditions, both met — loads, stores its clause at the SORT's
/// address, and ANSWERS. Driven rather than asserted-loaded: a rule whose head binds
/// nowhere loads clean too, so "no errors" passes through the regression as well as the
/// feature.
#[test]
fn a_fresh_head_owned_by_one_entry_answers() {
    let src = fixture(
        "wi1001.cap",
        "",
        "    rule freshp(1) :- true\n    rule reads(?y) :- freshp(?y)\n",
    );
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with(&src));
    assert_eq!(
        clauses(&kb, "wi1001.cap.Rec.freshp"),
        Some(1),
        "the clause is stored at the SORT's address — a secondary entry declares into \
         the sort's own scope (059 R2), not into a module beside it"
    );
    assert_eq!(answers(&mut kb, "wi1001.cap.Rec.freshp(1)"), 1);
    assert_eq!(
        answers(&mut kb, "wi1001.cap.Rec.freshp(2)"),
        0,
        "and it is the CLAUSE that answers, not a variable head matching anything"
    );
    // A READER in the same entry, so the predicate is reached by a goal rather than
    // only by the query pattern.
    assert_eq!(answers(&mut kb, "wi1001.cap.Rec.reads(1)"), 1);
    assert_eq!(answers(&mut kb, "wi1001.cap.Rec.reads(2)"), 0);
}

/// 059 DELIBERATELY ADMITS THIS: "Two blocks in ONE file are one entry, so they compose
/// `freshp` freely — that is one author writing two paragraphs, which is exactly the
/// case condition (2) has no reason to refuse." Both clauses answer.
#[test]
fn two_blocks_in_one_file_are_one_entry_and_compose() {
    const SRC: &str = "namespace wi1001.twoblocks\n  \
        sort Rec\n    entity rec(n: Int64)\n  end\n  \
        namespace Rec\n    rule freshp(1) :- true\n  end\n  \
        namespace Rec\n    rule freshp(2) :- true\n  end\nend\n";
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with(SRC));
    assert_eq!(
        clauses(&kb, "wi1001.twoblocks.Rec.freshp"),
        Some(2),
        "two blocks at one address in one file are ONE entry"
    );
    assert_eq!(answers(&mut kb, "wi1001.twoblocks.Rec.freshp(1)"), 1);
    assert_eq!(answers(&mut kb, "wi1001.twoblocks.Rec.freshp(2)"), 1);
}

/// THE `rule { … }` BLOCK SPELLING of the same admission — its entries are ordinary
/// clauses (grammar: `rule_entry` carries the same three forms as `rule_declaration`),
/// so the narrow rule reaches them one at a time, exactly as R4 clause 2 reaches an
/// `operation { … }` block's entries.
#[test]
fn a_rule_block_in_one_entry_composes() {
    let src = fixture(
        "wi1001.block",
        "",
        "    rule {\n      freshp(1) :- true\n      freshp(2) :- true\n    }\n",
    );
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with(&src));
    assert_eq!(clauses(&kb, "wi1001.block.Rec.freshp"), Some(2));
    assert_eq!(answers(&mut kb, "wi1001.block.Rec.freshp(1)"), 1);
    assert_eq!(answers(&mut kb, "wi1001.block.Rec.freshp(2)"), 1);
}

// ── Condition (1): its head introduces ──────────────────────────────────────

/// EVERY WAY A HEAD CAN FAIL TO INTRODUCE, one row each, every row reported — a matrix
/// rather than five tests so that a change fells all five rather than the first.
///
/// The message NAMES WHAT THE HEAD LANDED ON, which is the whole content of the
/// verdict: "does not introduce" is not actionable, "resolves to 'x.y'" is.
#[test]
fn condition_1_a_head_that_does_not_introduce_is_refused() {
    let rows: &[(&str, &str, &str, &str)] = &[
        // (label, sort body, entry body, the landing site the message must name)
        (
            "an OPERATION declared in the main entry",
            "    operation p(x: Int64) -> Int64 = x\n",
            "    rule p(1) :- true\n",
            "resolves to 'wi1001.c1r0.Rec.p'",
        ),
        (
            "a PREDICATE declared in the main entry (061)",
            "    rule p(?x)\n",
            "    rule p(1) :- true\n",
            "resolves to 'wi1001.c1r1.Rec.p'",
        ),
        (
            "a CONST declared in the main entry",
            "    const p: Int64 = 3\n",
            "    rule p(1) :- true\n",
            "resolves to 'wi1001.c1r2.Rec.p'",
        ),
        (
            "an operation the ENTRY ITSELF declares",
            "",
            "    operation p(x: Int64) -> Int64 = x\n    rule p(?x) <=> 2 [simp]\n",
            "resolves to 'wi1001.c1r3.Rec.p'",
        ),

    ];
    let mut bad = Vec::new();
    for (i, (label, main, entry, want)) in rows.iter().enumerate() {
        let src = fixture(&format!("wi1001.c1r{i}"), main, entry);
        let errs = r3_errors(&src);
        match errs.iter().find(|e| e.contains("does not INTRODUCE")) {
            Some(e) if e.contains(want) => {}
            Some(e) => bad.push(format!("{label}: refused, but does not name {want:?}: {e}")),
            None => bad.push(format!(
                "{label}: expected condition (1)'s refusal, got {errs:#?}"
            )),
        }
    }
    assert!(
        bad.is_empty(),
        "rows condition (1) did not refuse as required:\n  {}",
        bad.join("\n  ")
    );
}

/// CONDITION (1) READS THE LADDER, SO IT REACHES AN IMPORT — the channel the matrix
/// above cannot carry, since an import needs a second file to import FROM.
///
/// AND IT REACHES ONLY A DECLARED ONE, which is 061 working rather than a gap: a
/// selective import of a name a rule INTRODUCES cannot resolve in sub-pass 2 (the
/// head-functor symbol does not exist until sub-pass 3) and is retried in sub-pass 4,
/// AFTER the ladder answers this condition reads. So an imported AUTO-declared predicate
/// is invisible to a head at this point and the head mints its own — measured, and
/// identical in an ordinary namespace, so it is neither caused nor fixable here. The
/// declared spelling below is the one 061 tells an author to write, and it is the one
/// this condition sees.
#[test]
fn condition_1_reaches_an_imported_predicate() {
    let errs = crate::common::try_load_kb_with_named_files(&[
        (
            "lib.anthill",
            "namespace wi1001.implib\n  rule q(?x)\n  rule q(1) :- true\nend\n",
        ),
        (
            "user.anthill",
            "namespace wi1001.imp\n  sort Rec\n    entity rec(n: Int64)\n  end\n  \
             namespace Rec\n    import wi1001.implib.{q}\n    rule q(2) :- true\n  end\nend\n",
        ),
    ])
    .err()
    .unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("does not INTRODUCE")
            && e.contains("resolves to 'wi1001.implib.q'")),
        "an entry that imports a predicate and writes a head of that name EXTENDS it; \
         got {errs:#?}"
    );
    // THE CONTROL, one line apart: the same entry with the import removed. The head is
    // then fresh, owns its predicate, and is admitted — so the row above measures the
    // IMPORT and not the two-file shape.
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with_named_files(&[
        (
            "lib.anthill",
            "namespace wi1001.implib2\n  rule q(?x)\n  rule q(1) :- true\nend\n",
        ),
        (
            "user.anthill",
            "namespace wi1001.imp2\n  sort Rec\n    entity rec(n: Int64)\n  end\n  \
             namespace Rec\n    rule q(2) :- true\n  end\nend\n",
        ),
    ]));
    assert_eq!(answers(&mut kb, "wi1001.imp2.Rec.q(2)"), 1);
    assert_eq!(
        answers(&mut kb, "wi1001.implib2.q(2)"),
        0,
        "and the entry's own predicate is a DIFFERENT one from the library's"
    );
}

/// EXCLUDED BY CONDITION (1) RATHER THAN BY A CLAUSE OF THEIR OWN, which 059 calls "the
/// sign the condition is the right one": a DOT rule and an OPERATOR rule carry the
/// desugar's own functor (`dot_apply`, `add`), a QUALIFIED head references rather than
/// introduces, and none of the three is ever fresh — so the `[simp]`-fires-in-the-typer
/// hazard cannot arise through them.
#[test]
fn a_desugared_or_qualified_head_introduces_nothing() {
    let rows: &[(&str, &str, &str)] = &[
        ("a DOT rule", "", "    rule ?x.marker(?y) :- true\n"),
        ("an OPERATOR rule", "", "    rule ?a + ?b :- true\n"),
        (
            "a QUALIFIED head",
            "    rule outer(?x)\n",
            "    rule Rec.outer(2) :- true\n",
        ),
    ];
    let mut bad = Vec::new();
    for (i, (label, main, entry)) in rows.iter().enumerate() {
        let src = fixture(&format!("wi1001.nil{i}"), main, entry);
        let errs = r3_errors(&src);
        if !errs
            .iter()
            .any(|e| e.contains("this head introduces no name at all"))
        {
            bad.push(format!("{label}: expected the no-name refusal, got {errs:#?}"));
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n  "));
}

/// 061's DECLARATION FORM, refused here — both spellings. A body-less `rule p(?x)` is
/// what lets clauses in other files and other scopes land on one predicate, which is
/// precisely the spread condition (2) forbids an entry; inside one entry the clauses
/// declare the predicate themselves.
///
/// IT NEEDS ITS OWN ARM, and this row is why: pass 1 mints a declaration's name, so its
/// head DENOTES — to the symbol IT created. Without the arm the same rule would be
/// reported as "joins a predicate that already exists", which is the opposite of what a
/// declaration does. ONE message, not two: the clause beside it in the second row would
/// otherwise be refused a second time for denoting the declaration.
#[test]
fn a_bodyless_rule_declaration_is_refused() {
    for (label, entry, want_count) in [
        ("standalone", "    rule freshp(?x)\n", 1),
        (
            "with a clause beside it",
            "    rule freshp(?x)\n    rule freshp(1) :- true\n",
            1,
        ),
        ("inside a rule block", "    rule {\n      freshp(1)\n    }\n", 1),
    ] {
        let src = fixture("wi1001.decl", "", entry);
        let errs = r3_errors(&src);
        assert_eq!(
            errs.len(),
            want_count,
            "{label}: one message per predicate; got {errs:#?}"
        );
        assert!(
            errs[0].contains("a body-less `rule` DECLARES a predicate (061)"),
            "{label}: expected the declaration sentence, got {:?}",
            errs[0]
        );
    }
}

// ── Condition (2): one entry owns the predicate ─────────────────────────────

/// A CLAUSE IN THE MAIN ENTRY AND ONE IN THE SECONDARY ENTRY, in ONE file. 061's
/// multi-file report cannot see this — one file — and R4 cannot express it either,
/// because two clauses of one predicate are not a name collision. It is condition (2)'s
/// own population, and the message names where the other clause is.
#[test]
fn condition_2_a_clause_in_the_main_entry_refuses_the_entrys() {
    let src = fixture(
        "wi1001.c2main",
        "    rule freshp(1) :- true\n",
        "    rule freshp(2) :- true\n",
    );
    let errs = r3_errors(&src);
    assert_eq!(errs.len(), 1, "one predicate, one message; got {errs:#?}");
    assert!(
        errs[0].contains("assembled from more than one entry")
            && errs[0].contains(
                "a clause is written in the main entry — the declaration of 'wi1001.c2main.Rec' itself"
            ),
        "the message must name the main entry as the other party; got {:?}",
        errs[0]
    );
}

/// TWO SECONDARY ENTRIES IN TWO FILES — 059's own worked example, verbatim: "Two
/// secondary entries in different files that each introduce `freshp` do not collide —
/// both clauses join it … and the predicate ends up assembled by two parties that never
/// agreed on it."
///
/// AND EXACTLY ONE MESSAGE, which is the second half of this row. 061's
/// `PredicateHeadsSpanFiles` sees the same program and prescribes "declare it once, in
/// the scope that owns it" — a declaration R3 refuses in a secondary entry. Printing
/// both would prescribe a repair the other error forbids. MEASURED before the
/// suppression: this program reported THREE errors.
#[test]
fn a_predicate_assembled_from_two_entries_is_reported_once() {
    let errs = crate::common::try_load_kb_with_named_files(&[
        (
            "alpha.anthill",
            "namespace wi1001.c2files\n  sort Rec\n    entity rec(n: Int64)\n  end\n  \
             namespace Rec\n    rule freshp(1) :- true\n  end\nend\n",
        ),
        (
            "beta.anthill",
            "namespace wi1001.c2files\n  namespace Rec\n    rule freshp(2) :- true\n  end\nend\n",
        ),
    ])
    .err()
    .unwrap_or_default();
    assert_eq!(
        errs.len(),
        1,
        "R3's refusal, and NOT 061's multi-file report beside it; got {errs:#?}"
    );
    assert!(
        errs[0].contains("assembled from more than one entry")
            && errs[0].contains("another entry at this address is in beta.anthill"),
        "the message must name the other file; got {:?}",
        errs[0]
    );
    assert!(
        !errs[0].contains("proposal 061"),
        "061's prescription is the one R3 refuses; it must not be the message here"
    );
}

/// A `fact` IS A CLAUSE, SO CONDITION (2) COUNTS IT. Since 061 `fact H` *is*
/// `rule H :- true`, and 059 says "every CLAUSE of that head" — but a fact is not a
/// rule-head site (nothing in the scan collects one, deliberately: a fact must not MINT
/// and must not enter 061's multi-file report), so a first cut of this rule censused
/// rule heads only.
///
/// THIS ROW IS 059'S WORKED HARM, VERBATIM, and it LOADED CLEAN before the fact census
/// existed — found by `/code-review`, then driven: `Rec.freshp` held **two** clauses,
/// one from the main entry's `fact` and one from the entry's `rule`, and `q(0)` answered
/// **1 without the entry and 0 with it**. A statement that was true became false through
/// the one route R3 exists to close, while the `rule` spelling of the identical
/// main-entry clause was refused one keyword away.
///
/// THE CONTROL IS THE SAME PROGRAM WITHOUT THE ENTRY, and it must still LOAD and still
/// answer 1 — otherwise this row would be equally true of an implementation that had
/// simply broken the fact.
#[test]
fn condition_2_counts_a_main_entry_fact_as_a_clause() {
    const MAIN: &str = "    fact freshp(2)\n    rule q(0) :- not freshp(1)\n";
    let errs = r3_errors(&fixture("wi1001.fact", MAIN, "    rule freshp(1) :- true\n"));
    assert_eq!(errs.len(), 1, "one predicate, one message; got {errs:#?}");
    assert!(
        errs[0].contains("assembled from more than one entry")
            && errs[0].contains("a clause is written in the main entry"),
        "a fact in the main entry is a clause of `freshp`; got {:?}",
        errs[0]
    );
    // THE CONTROL: the same main entry with no secondary entry beside it.
    let without = format!(
        "namespace wi1001.fact2\n  import anthill.prelude.{{Int64, Bool}}\n  \
         sort Rec\n    entity rec(n: Int64)\n{MAIN}  end\nend\n"
    );
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with(&without));
    assert_eq!(
        answers(&mut kb, "wi1001.fact2.Rec.q(0)"),
        1,
        "CONTROL: without the entry the negated goal succeeds — which is the answer the \
         admitted rule used to take away in silence"
    );
    // AND A SECOND CONTROL, one name apart: a main-entry fact about a DIFFERENT
    // predicate is no clause of this one, and the entry's rule is admitted.
    let unrelated = fixture(
        "wi1001.fact3",
        "    fact otherp(2)\n",
        "    rule freshp(1) :- true\n",
    );
    assert!(
        errors_of(&unrelated).is_empty(),
        "the census is per (scope, name), not per file; got {:?}",
        errors_of(&unrelated)
    );
}

/// THE FACT CENSUS IS SCOPED, AND ITS TWO ATTRIBUTIONS ARE BOTH DRIVEN.
///
/// A fact head is UNSCOPED (§5.3): written in an ENCLOSING namespace it falls to the
/// bare intern rather than joining the entry's predicate, so it is NOT a site — driven
/// below by the clause count and by the answer, not merely by the absence of a refusal.
///
/// And a fact written in ANOTHER ENTRY is named as that entry, never as the main entry:
/// the fact ban already reports that fact, and a second message pointing at the wrong
/// text is worse than none.
#[test]
fn the_fact_census_is_scoped_and_attributed() {
    // NOT A SITE — the enclosing namespace's fact does not join.
    let enclosing = "namespace wi1001.factencl\n  fact freshp(2)\n  \
                     sort Rec\n    entity rec(n: Int64)\n  end\n  \
                     namespace Rec\n    rule freshp(1) :- true\n  end\nend\n";
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with(enclosing));
    assert_eq!(
        clauses(&kb, "wi1001.factencl.Rec.freshp"),
        Some(1),
        "the entry's predicate holds its own clause and not the enclosing fact's"
    );
    assert_eq!(answers(&mut kb, "wi1001.factencl.Rec.freshp(1)"), 1);
    assert_eq!(
        answers(&mut kb, "wi1001.factencl.Rec.freshp(2)"),
        0,
        "so the two really are separate predicates"
    );
    // ATTRIBUTED TO THE OTHER ENTRY, not to the main entry.
    let errs = crate::common::try_load_kb_with_named_files(&[
        (
            "a.anthill",
            "namespace wi1001.factentry\n  sort Rec\n    entity rec(n: Int64)\n  end\n  \
             namespace Rec\n    rule freshp(1) :- true\n  end\nend\n",
        ),
        (
            "b.anthill",
            "namespace wi1001.factentry\n  namespace Rec\n    fact freshp(2)\n  end\nend\n",
        ),
    ])
    .err()
    .unwrap_or_default();
    assert_eq!(
        errs.len(),
        2,
        "the fact ban on b.anthill's fact, and condition (2) on a.anthill's rule; got \
         {errs:#?}"
    );
    assert!(
        errs.iter().any(|e| e.contains("assembled from more than one entry")
            && e.contains("another entry at this address is in b.anthill")
            // The ATTRIBUTION phrase, not the words "main entry" — the sentence's
            // explanatory tail names both entry kinds and would match either way.
            && !e.contains("a clause is written in the main entry")),
        "condition (2) must name the OTHER ENTRY, not the main entry; got {errs:#?}"
    );
}

/// CONDITION (2) IS ABOUT WHERE THE CLAUSE IS **PLACED**, NOT ABOUT WHAT THE LADDER
/// SAID — and this row is the measurement that settled it, because the other reading is
/// the one that looks right.
///
/// A `!denotes` filter on the site set would say: a head that resolved ELSEWHERE is a
/// clause of what it resolved to, so it is not a clause of the predicate this entry is
/// minting. Driven on the three files below, that is FALSE. `main.anthill`'s head
/// resolves to `lib.p` at scan time (its own file imports it), and its clause is
/// nevertheless stored under `Rec.p` beside the entry's — `load_rule` remaps the head in
/// its SCOPE at load time, by which point the entry's head has minted `Rec.p` there and
/// a local symbol beats an import. That divergence is WI-20260820-JR7BB, filed by
/// WI-980 and not this rule's to fix; what it settles is that condition (2) must count
/// the head.
///
/// THE THIRD FILE IS LOAD-BEARING. Written in ONE file the entry sees the main entry's
/// import too (they share one scope), both heads denote, and condition (1) refuses
/// instead — measured. Imports are file-local (WI-995), so only a separate file gives
/// the two heads different ladder answers.
#[test]
fn condition_2_counts_a_head_by_where_its_clause_lands() {
    const LIB: (&str, &str) = (
        "lib.anthill",
        "namespace wi1001.c2imp.lib\n  rule p(?x)\n  rule p(1) :- true\nend\n",
    );
    const MAIN: (&str, &str) = (
        "main.anthill",
        "namespace wi1001.c2imp\n  sort Rec\n    import wi1001.c2imp.lib.{p}\n    \
         entity rec(n: Int64)\n    rule p(2) :- true\n  end\nend\n",
    );
    // THE CONTROL, run FIRST: without the entry, the main entry's head really does bind
    // through its own file's import. Without this the row below could not tell "the
    // ladder said `lib.p`" from "the ladder said nothing".
    let ctrl = crate::common::expect_loaded(crate::common::try_load_kb_with_named_files(&[
        LIB, MAIN,
    ]));
    assert_eq!(
        clauses(&ctrl, "wi1001.c2imp.lib.p"),
        Some(2),
        "CONTROL: the main entry's head binds through its own file's import"
    );
    assert_eq!(
        clauses(&ctrl, "wi1001.c2imp.Rec.p"),
        None,
        "CONTROL: and mints nothing at the sort"
    );
    // Now a secondary entry in a THIRD file writes a `p` of its own. Refused: whatever
    // the ladder answered, both clauses land in one predicate at one address, written by
    // two entries.
    let errs = crate::common::try_load_kb_with_named_files(&[
        LIB,
        MAIN,
        (
            "entry.anthill",
            "namespace wi1001.c2imp\n  namespace Rec\n    rule p(3) :- true\n  end\nend\n",
        ),
    ])
    .err()
    .unwrap_or_default();
    assert_eq!(errs.len(), 1, "one predicate, one message; got {errs:#?}");
    assert!(
        errs[0].contains("assembled from more than one entry")
            && errs[0].contains("a clause is written in the main entry"),
        "condition (2) must count the main entry's head; got {:?}",
        errs[0]
    );
}

/// THE CONTROL FOR THE ROW ABOVE, one token apart: the SAME two files, the same two
/// entries, DIFFERENT predicate names. Nothing is assembled from two parties, so both
/// load and both answer. Without it the refusal above would be equally true of an
/// implementation that refused every cross-file secondary entry.
#[test]
fn two_entries_in_two_files_with_distinct_predicates_both_answer() {
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with_named_files(&[
        (
            "alpha.anthill",
            "namespace wi1001.c2ok\n  sort Rec\n    entity rec(n: Int64)\n  end\n  \
             namespace Rec\n    rule alphap(1) :- true\n  end\nend\n",
        ),
        (
            "beta.anthill",
            "namespace wi1001.c2ok\n  namespace Rec\n    rule betap(2) :- true\n  end\nend\n",
        ),
    ]));
    assert_eq!(answers(&mut kb, "wi1001.c2ok.Rec.alphap(1)"), 1);
    assert_eq!(answers(&mut kb, "wi1001.c2ok.Rec.betap(2)"), 1);
}

// ── The gate condition (1) rests on ─────────────────────────────────────────

/// WI-895 IS WHY CONDITION (1) CAN MEAN WHAT IT SAYS. 059's worked failure of the naive
/// reading: a main entry carrying `rule q(0) :- not freshp(1)` answers `q(0)` once, and
/// adding `namespace Rec { rule freshp(1) }` takes it to zero — "the REFERENCE existed
/// before the DEFINITION did", though the head was as fresh as heads get.
///
/// THAT PAIR NO LONGER EXISTS, and this row is the measurement: the program WITHOUT the
/// entry does not load at all (WI-895 refuses a rule-body goal that names nothing), so
/// there is no earlier answer for the entry to change. The two halves must be run
/// together — the refusal alone would not show that the shape is reachable, and the
/// admitted half alone would not show what it replaced.
///
/// The WI-895 half PASSES EITHER WAY and is the gate; the admitted half fails when the
/// narrow rule is backed out.
#[test]
fn the_reference_before_the_definition_is_refused_without_the_entry() {
    const MAIN: &str = "    rule q(0) :- not freshp(1)\n";
    let with_entry = fixture("wi1001.gate", MAIN, "    rule freshp(1) :- true\n");
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with(&with_entry));
    assert_eq!(
        answers(&mut kb, "wi1001.gate.Rec.freshp(1)"),
        1,
        "the entry's clause is live"
    );
    assert_eq!(
        answers(&mut kb, "wi1001.gate.Rec.q(0)"),
        0,
        "so the negated goal fails — which is 059's harm, and the half below is why it \
         is no longer a CHANGE of anything"
    );
    // THE GATE. The same main entry with NO secondary entry beside it.
    let without = format!(
        "namespace wi1001.gate2\n  import anthill.prelude.{{Int64, Bool}}\n  \
         sort Rec\n    entity rec(n: Int64)\n{MAIN}  end\nend\n"
    );
    let errs = errors_of(&without);
    assert!(
        errs.iter()
            .any(|e| e.contains("rule-body goal `freshp` names nothing")),
        "WI-895 must refuse the reference-without-a-definition, or condition (1) is \
         unsound; got {errs:#?}"
    );
}

// ── Equations ───────────────────────────────────────────────────────────────

/// AN EQUATION'S SUBJECT TAKES THE SAME TWO CONDITIONS. 059 says the
/// `[simp]`-fires-in-the-typer hazard "cannot arise through" a desugared head *because
/// it is never fresh* — so freshness is what the hazard turns on, and a fresh subject is
/// admitted while a bound one is not.
///
/// The refused row is refused EITHER WAY (WI-1000 banned every rule); what this row
/// pins is that it is refused for the RIGHT reason, and that its neighbour one token
/// away is not refused at all.
#[test]
fn a_fresh_equation_subject_is_admitted() {
    let fresh = fixture("wi1001.eqok", "", "    rule freshf(?x) <=> ?x\n");
    assert!(
        errors_of(&fresh).is_empty(),
        "a fresh equation subject meets both conditions; got {:?}",
        errors_of(&fresh)
    );
    // BOUND — the subject names the main entry's operation, so the equation would
    // rewrite calls the entry does not own, in the TYPER, before dispatch.
    let bound = fixture(
        "wi1001.eqno",
        "    operation twice(x: Int64) -> Int64\n",
        "    rule twice(?x) <=> 2 [simp]\n",
    );
    let errs = r3_errors(&bound);
    assert!(
        errs.iter().any(|e| e.contains("does not INTRODUCE")
            && e.contains("resolves to 'wi1001.eqno.Rec.twice'")),
        "condition (1) must name the operation the subject landed on; got {errs:#?}"
    );
}

// ── The sites the narrow rule does not reach ────────────────────────────────

/// A `provides Spec language L … end` BLOCK'S INTERIOR — refused whatever the head, and
/// the reason is not the old blanket ban. `load_provides_block` sets the domain and
/// `current_scope` to the block's SPEC, so a rule written there is a clause of ANOTHER
/// type's predicate by construction: condition (2) can never hold for it, and neither
/// condition is even askable — no pass descends into a `provides` block, so such a rule
/// is never a `RuleHeadSite` and has no ladder answer to read.
#[test]
fn a_rule_in_a_provides_block_stays_refused() {
    let src = fixture(
        "wi1001.pb",
        "",
        "    provides Rec language rust\n      artifact \"nowhere.rs\"\n      \
         carrier { Rec: \"Rec\" }\n      rule freshp(1) :- true\n    end\n",
    );
    let errs = r3_errors(&src);
    assert!(
        errs.iter()
            .any(|e| e.contains("its clauses are loaded into the SPEC's scope")),
        "the block's own reason, not the retired blanket ban; got {errs:#?}"
    );
}

/// THE ADDRESS IS STILL THE CLASSIFIER, and after the narrowing the row that shows it
/// had to change. A FRESH head is now legal in both places, so the byte-identical pair
/// WI-1000 used no longer separates them; a head that JOINS does. An ordinary namespace
/// may extend a predicate declared above it — that has always been legal and 059 says
/// "nothing in R3 or R4 reaches it" — while the same text at a sort's address is
/// condition (1)'s refusal.
#[test]
fn an_ordinary_namespace_is_still_not_reached() {
    const BODY: &str = "    rule joins(2) :- true\n";
    // No sort at `Utils`' address: an ordinary namespace, joining the declared `joins`.
    let plain = format!(
        "namespace wi1001.plain\n  rule joins(?x)\n  namespace Utils\n{BODY}  end\nend\n"
    );
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with(&plain));
    assert_eq!(
        answers(&mut kb, "wi1001.plain.joins(2)"),
        1,
        "an ordinary namespace's clause joins the enclosing predicate, as it always has"
    );
    // The SAME text, at an address a sort occupies. Only the sort's presence differs.
    let entry = format!(
        "namespace wi1001.entry\n  rule joins(?x)\n  sort Utils\n    entity util(n: Int64)\n  \
         end\n  namespace Utils\n{BODY}  end\nend\n"
    );
    let errs = r3_errors(&entry);
    assert!(
        errs.iter().any(|e| e.contains("does not INTRODUCE")
            && e.contains("resolves to 'wi1001.entry.joins'")),
        "the identical text at a sort's address is a secondary entry, and its joining \
         head is refused; got {errs:#?}"
    );
}
