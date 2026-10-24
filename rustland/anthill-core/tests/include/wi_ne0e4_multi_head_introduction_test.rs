//! WI-20260908-NE0E4 — A MULTI-HEAD RULE'S HEADS ARE SCOPED WHERE THEY ARE WRITTEN.
//!
//! `rule law: H1, H2 :- B` is N clauses sharing one body (§5.3, "conjunctive sugar"), so
//! each head introduces exactly what the single-head rule `Hᵢ :- B` would: at the scope
//! it is written in, unless its name already denotes. Before this ticket the rule
//! introduced NOTHING — `subject_introduces` refused at `head_count != 1` — and each head
//! landed its clause under `remap_name_str`'s bare intern: ONE global name, so two sorts
//! writing `aa` shared one predicate and a reader in one sort answered from the other's
//! clause, on a program that loaded clean. WI-894's defect class, in the arm it did not
//! reach.
//!
//! A multi-head rule the load REFUSES mints nothing and is not judged by 059 R3: a
//! BODY-LESS one (it reads as a DECLARATION, which declares one predicate —
//! `NoIntroduction::SeveralHeads`) and an UNLABELED one (`several_heads_refusal`, the one
//! decider `load_rule` and the mint share).
//!
//! ── WHICH ROWS FAIL WHEN WHAT IS BACKED OUT ─────────────────────────────────
//!
//! Each back-out applied to `kb/load.rs` and this file, the census, APXSS, WI-1001 and
//! WI-894 suites run in a temporary binary (77 rows, all green at baseline); MEASURED
//! 2026-10-24, after the third `/code-review` round. The two ORDER rows fail under a
//! back-out of their tie-break 23 runs in 24 (see each row).
//!
//! **BACK-OUT 1 — THE HEAD COUNT GATE.** `RuleHeadCollectPass::collect` records nothing
//! for a head of a rule with `r.heads.len() != 1` (the pre-ticket population). FAILS 17:
//! [`two_sorts_writing_one_head_name_each_read_their_own_clause`],
//! [`the_label_cites_the_scoped_clauses`],
//! [`two_heads_of_one_name_in_one_rule_are_one_scoped_predicate`],
//! [`both_spellings_of_a_nullary_head_are_one_term`],
//! [`a_head_and_a_single_head_rule_in_visible_scopes_collide`],
//! [`heads_in_two_files_at_one_scope_must_be_declared`],
//! [`a_selective_import_reaches_a_multi_head_head`], the fresh-head `zz` half of
//! [`a_head_that_already_denotes_joins_rather_than_shadows`], every R3 row that judges a
//! head ([`a_multi_head_rule_of_fresh_heads_in_a_secondary_entry_is_admitted`], both
//! joining-head rows, [`a_qualified_head_refuses_the_rule_and_is_named`],
//! [`every_head_that_introduces_nothing_is_named`],
//! [`a_refused_rules_other_heads_are_judged_too`]), both order rows, and
//! `wi_rdgqc_head_introduction_census_test::a_multi_head_rules_heads_are_scoped_where_they_are_written`.
//!
//! **BACK-OUT 2 — ONE HEAD PER RULE AT THE R3 JOIN.** `judge_secondary_entry_rules`
//! groups only the LAST site of a rule (2b, what a one-site-per-span map keeps) or only
//! the FIRST (2a). FAILS: [`a_joining_head_first_refuses_the_rule`] (2b) or
//! [`a_joining_head_last_refuses_the_rule`] (2a) — the joining head goes unjudged — and
//! [`the_refusals_of_one_rule_print_in_head_order`] under both (one refusal, not four).
//!
//! **BACK-OUT 3 — ADMIT ON ANY SITE.** A deferred rule with one recorded site is admitted,
//! a [`HeadMiss`] beside it notwithstanding. FAILS 5: both named-head rows,
//! [`every_head_that_introduces_nothing_is_named`],
//! [`two_desugared_heads_are_told_apart_by_position`],
//! [`a_refused_rules_other_heads_are_judged_too`].
//!
//! **BACK-OUT 4 — MINT A BODY-LESS MULTI-HEAD RULE'S HEADS** (`collect`'s gate passing
//! `SeveralHeadsRefusal::Declaration`). FAILS:
//! [`a_body_less_multi_head_rule_is_refused_for_what_it_is`] — the minted head collides
//! with the sort's `aa`, and the author is told to declare a name in the scope whose line
//! was refused.
//!
//! **BACK-OUT 5 — MINT AN UNLABELED MULTI-HEAD RULE'S HEADS** (the gate stopping only
//! `Declaration`). FAILS: [`an_unlabeled_multi_head_rule_is_refused_and_mints_nothing`]
//! and [`unlabeled_heads_in_two_files_draw_no_declare_it`].
//!
//! **BACK-OUT 6 — DEFER A RULE THAT STORES NOTHING TO R3** (drop `defer_rule`'s gate).
//! FAILS: [`a_body_less_multi_head_rule_in_a_secondary_entry_is_refused_once`] and
//! [`an_unlabeled_multi_head_rule_in_a_secondary_entry_is_refused_once`]. **6b** — the
//! gate holding back only `Declaration` — fails the unlabeled row alone.
//!
//! **BACK-OUT 7 — JUDGE ONLY A RULE WITH NO MISS** (a refused rule's introducing heads
//! left out of the groups). FAILS: [`a_refused_rules_other_heads_are_judged_too`] — its
//! fresh head's spread is reported only after the qualified head is fixed.
//!
//! **BACK-OUT 8 / 9 — NO SITE-INDEX TIE-BREAK** in R3's report order / in the absorbed-
//! equation report order. FAILS: [`the_refusals_of_one_rule_print_in_head_order`] /
//! [`equation_refusals_of_one_rule_print_in_head_order`].
//!
//! **BACK-OUT 10 — A MULTI-HEAD REFUSAL GETS THE ONE-HEAD SENTENCE.** FAILS 5, as back-out
//! 3. **11** — naming only the FIRST head — and **14** — the heads not named by position
//! — each fail [`every_head_that_introduces_nothing_is_named`] and
//! [`two_desugared_heads_are_told_apart_by_position`].
//!
//! **BACK-OUT 12 — A QUERY SOURCE'S HEAD RECORDS NO MISS.** FAILS:
//! [`a_rule_in_a_query_sources_secondary_entry_is_refused_for_what_it_is`] — the judge's
//! inconsistency arm, a panic under debug assertions.
//!
//! **BACK-OUT 13 — THE ONE-HEAD REFUSAL GIVES THE GENERIC SENTENCE.** FAILS:
//! [`a_one_head_refusal_gives_its_heads_own_reason`] and the query-source row.
//!
//! Back-outs 5–14 cover what the three `/code-review` rounds found.
//!
//! **PASS EITHER WAY, BY DESIGN:** [`the_single_head_and_distinct_name_controls`] (what
//! makes the cross-sort row a measurement of the head COUNT), the "joins, does not
//! shadow" half of [`a_head_that_already_denotes_joins_rather_than_shadows`], and
//! [`an_unlabeled_empty_bodied_rule_with_a_connective_head_is_refused_for_the_connective`]
//! (rustland's order is unchanged; the row is scaland's twin, where it fails when the
//! order is backed out).
//!
//! A RULE WITH NO HEAD has no row either: the grammar writes at least one, and `load_rule`
//! refuses the IR shape.
//!
//! A `⊥` AMONG SEVERAL HEADS has no row: the grammar writes `⊥` only as a rule's sole
//! head, so no source reaches `SeveralHeadsRefusal::DenialAmongHeads`.
//!
//! A MULTI-HEAD RULE IN A HOST `provides … language … end` BLOCK has no row: a labeled
//! rule there does not load at all today ("unresolved name 'law'" — pass 1 never walks a
//! host block, so its rule labels are never defined), and a multi-head rule must be
//! labeled. Measured with one head and with two; it is WI-20261024-RMZQZ's, which owes
//! this file that row.
//!
//! STDLIB LOADS: every row loads through the `tests/common` recipe.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::resolve::ResolveConfig;

/// DEFINITE answers to the unary predicate `qn` — a floundered solution is not an
/// answer (WI-20260822-WZX6B).
fn answers(kb: &mut KnowledgeBase, qn: &str) -> usize {
    crate::common::definite_unary(kb, qn).len()
}

/// Solutions of a ground goal pattern.
fn holds(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// The clauses stored under `qn` — `None` when nothing is named `qn` at all, which is
/// the distinction a bare answer count cannot make.
fn clauses(kb: &KnowledgeBase, qn: &str) -> Option<usize> {
    let sym = kb.try_resolve_symbol(qn)?;
    Some(kb.rules_by_functor(sym).len())
}

/// The INVERTED PAIR (P85Z7's idiom): sort P's clause for `aa` is FALSE (its body reads
/// a fact that is not there), sort Q's is TRUE, and each sort reads `aa` through a rule
/// of its own. A merge is then a WRONG ANSWER in P rather than an extra one.
fn two_sorts(ns: &str, p_rule: &str, q_rule: &str, p_read: &str, q_read: &str) -> String {
    format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64}}\n\
         \x20 sort P\n    entity pe(v: Int64)\n    fact pbase(0)\n    {p_rule}\n    \
         rule see(?x) :- {p_read}(?x)\n  end\n\
         \x20 sort Q\n    entity qe(v: Int64)\n    {q_rule}\n    \
         rule see(?x) :- {q_read}(?x)\n  end\nend\n"
    )
}

#[test]
fn two_sorts_writing_one_head_name_each_read_their_own_clause() {
    // THE TICKET'S ROW. Before: P's reader answered 1, from Q's clause, and neither
    // `zzNE.cs.P.aa` nor `zzNE.cs.Q.aa` named anything.
    let src = two_sorts(
        "zzNE.cs",
        "rule lawP: aa(1), bb(1) :- pbase(1)",
        "rule lawQ: aa(1), cc(1) :- true",
        "aa",
        "aa",
    );
    let mut kb = crate::common::load_kb_with(&src);
    assert_eq!(
        answers(&mut kb, "zzNE.cs.P.see"),
        0,
        "P's own `aa` is false — a 1 here is Q's clause"
    );
    assert_eq!(answers(&mut kb, "zzNE.cs.Q.see"), 1, "and Q's is true");
    // THE NAMES, NOT ONLY THE ANSWERS: a count can be right for the wrong reason.
    let p_aa = kb.try_resolve_symbol("zzNE.cs.P.aa");
    let q_aa = kb.try_resolve_symbol("zzNE.cs.Q.aa");
    assert!(
        p_aa.is_some() && q_aa.is_some() && p_aa != q_aa,
        "each sort's head is its OWN citable symbol, got {p_aa:?} / {q_aa:?}"
    );
    for qn in ["zzNE.cs.P.bb", "zzNE.cs.Q.cc"] {
        assert_eq!(clauses(&kb, qn), Some(1), "every head is scoped, not only the first: {qn}");
    }
}

#[test]
fn the_single_head_and_distinct_name_controls() {
    // PASSES EITHER WAY. The single-head spelling of the same clause always scoped
    // (WI-894), and two DISTINCT names never shared a symbol — so the cross-sort row's
    // failure under back-out 1 is about the head COUNT, not about the fixture.
    for (ns, p_rule, q_rule, p_read, q_read) in [
        ("zzNE.cl", "rule aa(1) :- pbase(1)", "rule aa(1) :- true", "aa", "aa"),
        (
            "zzNE.cd",
            "rule lawP: pa(1), bb(1) :- pbase(1)",
            "rule lawQ: qa(1), cc(1) :- true",
            "pa",
            "qa",
        ),
    ] {
        let mut kb = crate::common::load_kb_with(&two_sorts(ns, p_rule, q_rule, p_read, q_read));
        assert_eq!(answers(&mut kb, &format!("{ns}.P.see")), 0, "{ns}");
    }
}

#[test]
fn the_label_cites_the_scoped_clauses() {
    // THE LABEL IS THE CITATION HANDLE, and that does not change: spelled unlike its
    // heads (as here), it holds no clause of its own (`rules_by_functor` under it is empty — it is not a predicate) and
    // `rules_by_label` fans it out to one stored clause per head. What changes is WHICH
    // clauses those are: the scoped ones.
    let src = "namespace zzNE.lb\n  import anthill.prelude.{Int64}\n  sort S\n    \
               entity se(v: Int64)\n    rule law: aa(1), bb(2) :- true\n  end\nend\n";
    let kb = crate::common::load_kb_with(src);
    let mut cited: Vec<usize> = kb
        .rule_ids_by_qn("zzNE.lb.S.law")
        .into_iter()
        .map(|r| r.index())
        .collect();
    cited.sort();
    let mut scoped: Vec<usize> = ["zzNE.lb.S.aa", "zzNE.lb.S.bb"]
        .iter()
        .flat_map(|qn| {
            let sym = kb
                .try_resolve_symbol(qn)
                .unwrap_or_else(|| panic!("`{qn}` names the head's own predicate"));
            kb.rules_by_functor(sym)
        })
        .map(|r| r.index())
        .collect();
    scoped.sort();
    assert_eq!(cited.len(), 2, "the label cites both heads' clauses");
    assert_eq!(cited, scoped, "and they are the clauses of the SCOPED predicates");
    let label = kb
        .try_resolve_symbol("zzNE.lb.S.law")
        .expect("the label is a scoped symbol");
    assert!(kb.rules_by_functor(label).is_empty(), "and the label itself holds no clause");
}

#[test]
fn two_heads_of_one_name_in_one_rule_are_one_scoped_predicate() {
    let src = "namespace zzNE.sn\n  import anthill.prelude.{Int64}\n  sort S\n    \
               entity se(v: Int64)\n    rule law: pp(1), pp(2) :- true\n  end\nend\n";
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(clauses(&kb, "zzNE.sn.S.pp"), Some(2), "two clauses, one predicate");
    assert_eq!(holds(&mut kb, "zzNE.sn.S.pp(2)"), 1, "and the second clause answers");
}

#[test]
fn both_spellings_of_a_nullary_head_are_one_term() {
    // WI-20260902-EQG4F item 4, the multi-head route. An undeclared head name stayed a
    // `Term::Ident` while `aa()` canonicalized to a `Term::Ref`, so `:- aa` answered and
    // `:- aa()` was a LOAD ERROR. A declared head is one term in both spellings.
    let src = "namespace zzNE.ns\n  rule law: aa, bb :- true\n  rule s1(1) :- aa\n  \
               rule s2(1) :- aa()\nend\n";
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with(src));
    assert_eq!(
        (answers(&mut kb, "zzNE.ns.s1"), answers(&mut kb, "zzNE.ns.s2")),
        (1, 1),
        "`aa` and `aa()` are one term"
    );
}

#[test]
fn a_head_and_a_single_head_rule_in_visible_scopes_collide() {
    // 845G7's refusal now sees a multi-head head as it sees any introducing head: the
    // namespace and the sort nested in it both introduce `aa`, and a bare `aa` in
    // either would reach only its own half. Before: the multi-head `aa` introduced
    // nothing, so the program loaded clean with the namespace's clause on a global.
    let src = "namespace zzNE.co\n  import anthill.prelude.{Int64}\n  \
               rule law: aa, bb :- true\n  sort S\n    entity se(v: Int64)\n    \
               rule aa :- true\n  end\nend\n";
    let errs = crate::common::load_errors_of(src);
    assert!(
        errs.iter().any(|e| e.contains("the rule head `aa` introduces that name at 2 scopes")),
        "{errs:#?}"
    );
}

#[test]
fn a_head_that_already_denotes_joins_rather_than_shadows() {
    // A DECLARED name in an enclosing scope DENOTES, so the head is a clause of it and
    // mints no local — as a single-head rule's head does. PASSES EITHER WAY for `aa`
    // (the ladder found the declaration before this ticket too); the sibling head `zz`,
    // which denotes nothing, is what fails under back-out 1.
    let src = "namespace zzNE.jn\n  import anthill.prelude.{Int64}\n  rule aa\n  sort S\n    \
               entity se(v: Int64)\n    rule law: aa, zz :- true\n  end\n  \
               rule see(1) :- aa\nend\n";
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(answers(&mut kb, "zzNE.jn.see"), 1, "the head is a clause of the declared `aa`");
    assert_eq!(clauses(&kb, "zzNE.jn.aa"), Some(1));
    assert!(
        kb.try_resolve_symbol("zzNE.jn.S.aa").is_none(),
        "and mints no `S.aa` shadowing it"
    );
    assert_eq!(clauses(&kb, "zzNE.jn.S.zz"), Some(1), "while the fresh head is S's own");
}

#[test]
fn heads_in_two_files_at_one_scope_must_be_declared() {
    // 061: a predicate whose heads are in two files is assembled by two parties and must
    // be declared. A multi-head head is now one of those heads.
    let errs = crate::common::load_errors_of_files(&[
        "namespace zzNE.tf\n  rule law1: aa(1), bb :- true\nend\n",
        "namespace zzNE.tf\n  rule law2: aa(2), cc :- true\nend\n",
    ]);
    assert!(
        errs.iter().any(|e| e.contains("the predicate `aa` has rule heads in 2 files")),
        "{errs:#?}"
    );
}

#[test]
fn a_selective_import_reaches_a_multi_head_head() {
    // `import X.Rec.{freshp}` is wired to the symbol a head of this scan will mint
    // (WI-20261022-JBHQC). A head that minted nothing left the import naming nothing.
    let src = "namespace zzNE.im\n  import anthill.prelude.{Int64}\n  sort Rec\n    \
               entity rec(v: Int64)\n    rule law: freshp(1), other(2) :- true\n  end\nend\n\
               namespace zzNE.side\n  import zzNE.im.Rec.{freshp}\n  \
               rule see(1) :- freshp(1)\nend\n";
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with(src));
    assert_eq!(answers(&mut kb, "zzNE.side.see"), 1);
}

// ── 059 R3: A MULTI-HEAD RULE IN A SECONDARY ENTRY IS JUDGED PER HEAD ───────────────
//
// R3 admits a rule in a secondary entry when its head INTRODUCES and one entry owns the
// predicate. A multi-head rule is N clauses, so it is admitted when every head would be
// — and refused when any one head would not. ONE ROW PER TEST, so each back-out's
// failure is that row's and not whichever row of a shared test panicked first.

/// A sort `Rec` whose main entry writes `main`, and a secondary entry (`namespace Rec`)
/// in the same file writing `rule`.
fn r3_program(ns: &str, main: &str, rule: &str) -> String {
    format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64}}\n  sort Rec\n    \
         entity rec(n: Int64)\n    {main}\n  end\n  namespace Rec\n    {rule}\n  end\nend\n"
    )
}

/// The 059 R3 refusals of a load, in the order the load reports them.
fn r3_refusals(errs: Vec<String>) -> Vec<String> {
    errs.into_iter()
        .filter(|e| e.contains("is not allowed in a secondary entry"))
        .collect()
}

#[test]
fn a_multi_head_rule_of_fresh_heads_in_a_secondary_entry_is_admitted() {
    // Refused before this ticket — "this head introduces no name at all", the rule
    // having had no site to judge.
    let src = r3_program("zzNE.r3a", "rule p(1) :- true", "rule law: f1(1), f2(2) :- true");
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with(&src));
    assert_eq!(holds(&mut kb, "zzNE.r3a.Rec.f2(2)"), 1, "the second head is Rec's own");
}

/// One head joins the main entry's `p`: the rule is refused for `p`.
fn assert_refused_for_joining_p(ns: &str, rule: &str) {
    let errs = r3_refusals(crate::common::load_errors_of(&r3_program(ns, "rule p(1) :- true", rule)));
    assert!(
        errs.iter().any(|e| e.contains("the predicate `p` is assembled from more than one entry")),
        "{errs:#?}"
    );
}

#[test]
fn a_joining_head_first_refuses_the_rule() {
    // A one-site-per-rule join keeps only the LAST head (back-out 2b).
    assert_refused_for_joining_p("zzNE.r3b", "rule law: p(2), f1(1) :- true");
}

#[test]
fn a_joining_head_last_refuses_the_rule() {
    // A join that keeps only the FIRST head (back-out 2a).
    assert_refused_for_joining_p("zzNE.r3c", "rule law: f1(1), p(2) :- true");
}

/// One head introduces nothing: the rule is refused NAMING that head, as its own
/// one-head rule would be.
fn assert_refused_for_the_head(ns: &str, rule: &str, why: &str) {
    let errs = r3_refusals(crate::common::load_errors_of(&r3_program(ns, "rule p(1) :- true", rule)));
    assert!(
        errs.iter().any(|e| e.contains("of this rule's 2 heads, one introduces no name at all")
            && e.contains(why)),
        "{errs:#?}"
    );
}

#[test]
fn a_qualified_head_refuses_the_rule_and_is_named() {
    // It records no site, so a judge that does not count heads admits the rule on its
    // fresh head alone (back-out 3).
    assert_refused_for_the_head(
        "zzNE.r3d",
        "rule law: f1(1), Rec.p(2) :- true",
        "`Rec.p` is a QUALIFIED name",
    );
}

#[test]
fn a_dot_rule_head_refuses_the_rule_and_is_named() {
    assert_refused_for_the_head(
        "zzNE.r3e",
        "rule law: f1(1), ?x.m(?y) :- true",
        "its head functor is the DESUGARING's",
    );
}

#[test]
fn every_head_that_introduces_nothing_is_named() {
    // Naming only the first would refuse the author again for the second once it is
    // fixed. Found by `/code-review`.
    let errs = r3_refusals(crate::common::load_errors_of(&r3_program(
        "zzNE.r3i",
        "rule p(1) :- true\n    rule q(1) :- true",
        "rule law: Rec.p(2), Rec.q(3), f1(1) :- true",
    )));
    assert!(
        errs.iter().any(|e| e.contains("of this rule's 3 heads, 2 introduce no name at all")
            && e.contains("head 1: `Rec.p` is a QUALIFIED name")
            && e.contains("head 2: `Rec.q` is a QUALIFIED name")),
        "{errs:#?}"
    );
}

#[test]
fn two_desugared_heads_are_told_apart_by_position() {
    // A dot head's and an operator head's reason is one sentence that quotes neither
    // head, so the POSITION is what names each. Found by `/code-review`.
    let errs = r3_refusals(crate::common::load_errors_of(&r3_program(
        "zzNE.r3k",
        "rule p(1) :- true",
        "rule law: f1(1), ?x.m(?y), ?a + ?b :- true",
    )));
    assert!(
        errs.iter().any(|e| e.contains("2 introduce no name at all")
            && e.contains("head 2: its head functor is the DESUGARING's")
            && e.contains("head 3: its head functor is the DESUGARING's")),
        "{errs:#?}"
    );
}

#[test]
fn a_one_head_refusal_gives_its_heads_own_reason() {
    // Not the sentence listing every shape that introduces nothing: the head's own.
    let errs = r3_refusals(crate::common::load_errors_of(&r3_program(
        "zzNE.r3l",
        "rule p(1) :- true",
        "rule Rec.p(2) :- true",
    )));
    assert!(
        errs.iter().any(|e| e.contains(
            "this head introduces no name at all: `Rec.p` is a QUALIFIED name"
        )),
        "{errs:#?}"
    );
}

#[test]
fn a_rule_in_a_query_sources_secondary_entry_is_refused_for_what_it_is() {
    // A query declares nothing (WI-20260821-RDGQC), so its head is a miss that says so.
    // It recorded neither a site nor a miss before, and the judge's inconsistency arm
    // fired — a panic in a build with debug assertions. Found by `/code-review`.
    let mut kb = crate::common::load_kb_with(
        "namespace zzNE.qs\n  import anthill.prelude.{Int64}\n  sort Rec\n    \
         entity rec(n: Int64)\n  end\nend\n",
    );
    let parsed = anthill_core::parse::parse(
        "namespace zzNE.qs\n  namespace Rec\n    rule p(1) :- true\n  end\nend\n",
    )
    .expect("parse the query source");
    let errors = anthill_core::kb::load::scan_query_definitions(&mut kb, &[&parsed]);
    let messages: Vec<String> = anthill_core::kb::load::LoadError::render_all(&errors).collect();
    assert!(
        messages.iter().any(|m| m.contains(
            "this head introduces no name at all: it is written in a QUERY source"
        )),
        "{messages:#?}"
    );
}

#[test]
fn a_refused_rules_other_heads_are_judged_too() {
    // The rule is refused for its qualified head, and its fresh head `f1` — which the
    // main entry in another file also writes — is judged as well: refused NOW for that
    // spread, not after the author has fixed the qualified head. And 061, whose repair
    // is a declaration R3 refuses a secondary entry, says nothing about it. Found by
    // `/code-review` (twice: first 061's second message, then the unjudged head).
    let errs = crate::common::load_errors_of_files(&[
        "namespace zzNE.r3f\n  import anthill.prelude.{Int64}\n  sort Rec\n    \
         entity rec(n: Int64)\n    rule p(1) :- true\n    rule f1(3) :- true\n  end\nend\n",
        "namespace zzNE.r3f\n  namespace Rec\n    rule law: f1(1), Rec.p(2) :- true\n  end\nend\n",
    ]);
    assert!(
        errs.iter().any(|e| e.contains("one introduces no name at all")),
        "the rule is refused for its qualified head: {errs:#?}"
    );
    assert!(
        errs.iter().any(|e| e.contains("the predicate `f1` is assembled from more than one entry")),
        "and for its fresh head's spread: {errs:#?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("has rule heads in 2 files")),
        "and 061 does not ask for a declaration R3 refuses: {errs:#?}"
    );
}

#[test]
fn a_body_less_multi_head_rule_in_a_secondary_entry_is_refused_once() {
    // It stores nothing, so it is not deferred to R3: the declaration refusal is the
    // whole report, not that plus "this head introduces no name at all".
    let errs = crate::common::load_errors_of(&r3_program(
        "zzNE.r3g",
        "rule p(1) :- true",
        "rule law: f1, f2",
    ));
    assert!(
        errs.iter().any(|e| e.contains("it writes 2 heads at once")),
        "{errs:#?}"
    );
    assert!(r3_refusals(errs.clone()).is_empty(), "{errs:#?}");
}

#[test]
fn an_unlabeled_multi_head_rule_in_a_secondary_entry_is_refused_once() {
    // The label refusal is the whole report: the rule stores nothing, so R3 has no head
    // to judge and must not add "introduces no name at all" for heads that do introduce.
    let errs = crate::common::load_errors_of(&r3_program(
        "zzNE.r3j",
        "rule p(1) :- true",
        "rule f1(1), f2(2) :- true",
    ));
    assert!(errs.iter().any(|e| e.contains("multi-head rule requires a label")), "{errs:#?}");
    assert!(r3_refusals(errs.clone()).is_empty(), "{errs:#?}");
}

#[test]
fn the_refusals_of_one_rule_print_in_head_order() {
    // Four heads, each joining a predicate of the main entry: four refusals at ONE span.
    // Their order must be the text's, not a hash map's — without the site index as the
    // tie-break (back-out 8) a run prints the 24 orders at random, and this row passes by
    // chance one run in 24.
    let errs = r3_refusals(crate::common::load_errors_of(&r3_program(
        "zzNE.r3h",
        "rule p(1) :- true\n    rule q(1) :- true\n    rule r(1) :- true\n    rule s(1) :- true",
        "rule law: p(2), q(2), r(2), s(2) :- true",
    )));
    let order: Vec<&str> = errs
        .iter()
        .map(|e| {
            ["p", "q", "r", "s"]
                .into_iter()
                .find(|n| e.contains(&format!("the predicate `{n}` is assembled")))
                .unwrap_or_else(|| panic!("a refusal names its head: {e}"))
        })
        .collect();
    assert_eq!(order, ["p", "q", "r", "s"], "{errs:#?}");
}

#[test]
fn a_body_less_multi_head_rule_is_refused_for_what_it_is() {
    // A body-less rule DECLARES, and a declaration declares one predicate — so it is
    // refused, and NOTHING ELSE is said about it: its heads are not minted, so they
    // cannot collide with the sort's `aa` and send the author to declare a name in a
    // scope whose line was the refused one (back-out 4).
    let src = "namespace zzNE.bl\n  import anthill.prelude.{Int64}\n  rule law: aa, bb\n  \
               sort S\n    entity se(v: Int64)\n    rule aa :- true\n  end\nend\n";
    let errs = crate::common::load_errors_of(src);
    assert!(
        errs.iter().any(|e| e.contains("it writes 2 heads at once, and a declaration declares ONE predicate")),
        "{errs:#?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("introduces that name at")),
        "a refused declaration mints nothing to collide with: {errs:#?}"
    );
}

/// A multi-head rule `load_rule` refuses, written in a namespace whose nested sort writes
/// `aa`: the refusal `why` is the whole report — a refused rule stores nothing, so its
/// heads mint nothing to collide with (back-out 5).
fn assert_refused_and_mints_nothing(ns: &str, rule: &str, why: &str) {
    let src = format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64}}\n  {rule}\n  sort S\n    \
         entity se(v: Int64)\n    rule aa :- true\n  end\nend\n"
    );
    let errs = crate::common::load_errors_of(&src);
    assert!(errs.iter().any(|e| e.contains(why)), "{errs:#?}");
    assert!(
        !errs.iter().any(|e| e.contains("introduces that name at")),
        "a refused rule mints nothing to collide with: {errs:#?}"
    );
}

#[test]
fn an_unlabeled_multi_head_rule_is_refused_and_mints_nothing() {
    assert_refused_and_mints_nothing(
        "zzNE.ul",
        "rule aa, bb :- true",
        "multi-head rule requires a label",
    );
}

#[test]
fn an_unlabeled_empty_bodied_rule_with_a_connective_head_is_refused_for_the_connective() {
    // PASSES EITHER WAY HERE — rustland's order is `load_rule`'s and unchanged: WI-1090's
    // `===` refusal before the label's. The row is the twin of scaland's, whose order was
    // moved to this one (found by `/code-review`), so the two say one thing.
    let errs = crate::common::load_errors_of("namespace zzNE.cy\n  rule f(1) === 2, g(1) :- true\nend\n");
    assert!(errs.iter().any(|e| e.contains("is the structural identity TEST")), "{errs:#?}");
    assert!(!errs.iter().any(|e| e.contains("requires a label")), "{errs:#?}");
}

#[test]
fn unlabeled_heads_in_two_files_draw_no_declare_it() {
    // 061's "declare it" is about heads that store clauses. These store none.
    let errs = crate::common::load_errors_of_files(&[
        "namespace zzNE.u2\n  rule aa(1), bb :- true\nend\n",
        "namespace zzNE.u2\n  rule aa(2) :- true\nend\n",
    ]);
    assert!(
        errs.iter().any(|e| e.contains("multi-head rule requires a label")),
        "{errs:#?}"
    );
    assert!(!errs.iter().any(|e| e.contains("has rule heads in 2 files")), "{errs:#?}");
}

#[test]
fn equation_refusals_of_one_rule_print_in_head_order() {
    // Four EQUATION heads of one rule whose subjects name predicates the enclosing
    // namespace DECLARES: four refusals at one span (WI-20260821-D0EXD), in the text's
    // order — without the site index as the tie-break (back-out 9) one run in 24 passes
    // by chance.
    let src = "namespace zzNE.eq\n  import anthill.prelude.{Int64}\n  \
               rule f(?a)\n  rule g(?a)\n  rule h(?a)\n  rule k(?a)\n  \
               sort S\n    entity se(v: Int64)\n    \
               rule law: f(?x) <=> 2, g(?x) <=> 3, h(?x) <=> 4, k(?x) <=> 5 :- true\n  \
               end\nend\n";
    let errs: Vec<String> = crate::common::load_errors_of(src)
        .into_iter()
        .filter(|e| e.contains("the equation subject `"))
        .collect();
    let order: Vec<&str> = errs
        .iter()
        .map(|e| {
            ["f", "g", "h", "k"]
                .into_iter()
                .find(|n| e.contains(&format!("the equation subject `{n}`")))
                .unwrap_or_else(|| panic!("a refusal names its subject: {e}"))
        })
        .collect();
    assert_eq!(order, ["f", "g", "h", "k"], "{errs:#?}");
}
