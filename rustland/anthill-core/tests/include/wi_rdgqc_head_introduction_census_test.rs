//! WI-20260821-RDGQC — WHICH HEAD SHAPES INTRODUCE A NAME, STATED ONCE AND DRIVEN ONCE.
//!
//! The ticket's complaint was that the answer lived nowhere: a head that introduced
//! nothing did so by falling out of a walk, so its name reached `remap_name_str`'s bare
//! `intern(name)` — ONE GLOBAL NAME two scopes then share, with the loser's clause
//! answering inside the winner's scope, on a program that loads clean. That is WI-894's
//! defect class, and four shapes were in it. This file is the census: every head-bearing
//! shape, its answer today, and — for the shapes still LEFT OUT — the leak itself,
//! pinned so that whoever closes one has to come here and say so.
//!
//! ── THE TWO HALVES OF THE ENUMERATION ───────────────────────────────────────
//!
//! A RULE HEAD's answer is [`load::NoIntroduction`], one type with one variant per
//! reason, replacing a bare `None` verdict paired with a SECOND walk
//! (`bodyless_declares_nothing_detail`) that re-derived the same questions to choose a
//! sentence. Part C below drives every variant.
//!
//! A FACT head and a host `provides … language … end` head never ask that type, because
//! they never ask: neither reaches [`RuleHeadSite`] at all. They are enumerated HERE,
//! driven, rather than given variants no producer builds (WI-816's class).
//!
//! ── THE LEDGER, MEASURED ON THIS TREE ───────────────────────────────────────
//!
//! Every row is the INVERTED PAIR idiom (P85Z7's): two sibling scopes write ONE head
//! name, one scope's clause is FALSE and the other's TRUE, and each scope reads through
//! a unary rule of its own. A merge is then a WRONG ANSWER rather than an extra one, and
//! asserting only the true side would pass against the defect. Siblings cannot see each
//! other, so 845G7's collision refusal does not fire — the subject here is the SPLIT.
//!
//! | shape                          | scoped? | this file's rows              |
//! |--------------------------------|---------|------------------------------|
//! | `rule p(1) :- …` applied       | YES     | A, 0 and 1                   |
//! | `rule p :- …` paren-less       | YES     | A, 0 and 1  (P85Z7)          |
//! | `rule f(?x) <=> …` equation    | YES     | A, two distinct symbols      |
//! | `fact p(1)` fact head          | YES     | A, 0 and 1  (see below)      |
//! | `rule l: p(1), q(9) :- …`      | **no**  | B, 2 and 2  (NE0E4)          |
//! | head in `provides … language`  | **no**  | B, 2 and 2  (TTHRK)          |
//! | `rule ns.p :- …` qualified     | n/a     | C — REFERENCES, by design    |
//! | `rule ?x.m(?y) :- …` desugared | n/a     | C — the desugar's functor    |
//!
//! ── WHICH ROWS FAIL WHEN WHAT IS BACKED OUT ─────────────────────────────────
//!
//! **BACK-OUT 1 — DROP `head_subject_name`'s `Term::Ident` ARM** (`_ => return
//! Err(NotAnApplication)` alone; P85Z7's axis A). **EXACTLY 3 ROWS FAIL**, and the third
//! is why it is worth stating rather than assuming:
//!   * [`a_paren_less_nullary_head_is_scoped_where_it_is_written`] — the shape itself;
//!   * [`both_spellings_of_a_qualified_head_get_one_reason`] and the
//!     `QualifiedSpelling` row of [`every_no_introduction_reason_is_reachable_and_distinct`]
//!     — because `rule ..nosuchxyz` then reaches `NotAnApplication` while
//!     `rule ..nosuchxyz()` still reaches `QualifiedSpelling`. That is the ORIGINAL drift
//!     (two spellings of one head, two explanations of one verdict) reappearing, which
//!     says these two rows really are guarding it and not merely describing it.
//! [`an_applied_head_is_scoped_where_it_is_written`] is UNMOVED, which is what makes the
//! axis the SPELLING and not the shape.
//!
//! **BACK-OUT 2 — MAKE TWO `NoIntroduction::detail` ARMS SHARE A SENTENCE** (give
//! `NotAnApplication` the `DenialHead` text). **EXACTLY 1 ROW FAILS:**
//! [`every_no_introduction_reason_is_reachable_and_distinct`], on its dedup assertion.
//! That is the drift-catcher the merge buys: before it, the same swap had two homes
//! (the verdict's and the second walk's) and only one of them was under test.
//!
//! **PART B PINS DEFECTS, SO IT HAS NO BACK-OUT — IT FAILS WHEN THEY ARE FIXED**, which
//! is the point. Each row asserts the leak (2 answers where 1 is right) BESIDE a control
//! in a shape that scopes (1 answer, its own). The control is what makes the 2 a
//! measurement of the shape rather than of the fixture: back the control out and you
//! learn nothing from the 2. Whoever closes NE0E4 or TTHRK edits the row and the table
//! above together.
//!
//! **AND PART C PASSES AGAINST THE PRE-MERGE CODE, BY DESIGN.** RDGQC's change is
//! behaviour-preserving — one walk where there were two — so no diagnostic moved:
//! measured, all five sentences byte-identical before and after. Part C is therefore the
//! LEDGER the merge had to preserve, not evidence that it happened; its teeth are
//! back-out 2, which is about the NEXT drift rather than this one.
//!
//! STDLIB LOADS: every row uses `load_kb_with` / `try_load_kb_with`, which bootstrap
//! only.

use anthill_core::kb::KnowledgeBase;

/// DEFINITE answers to the unary predicate `qn` — a floundered solution is not an
/// answer (WI-20260822-WZX6B), and this file counts answers.
fn answers(kb: &mut KnowledgeBase, qn: &str) -> usize {
    crate::common::definite_unary(kb, qn).len()
}

/// Two sibling scopes, one head name, the FIRST scope's clause false and the second's
/// true. `$shape` writes the head; `$read` reads it.
macro_rules! inverted_pair {
    ($ns:literal, $a_head:literal, $b_head:literal, $read:literal) => {
        format!(
            "namespace zzRDGQC.{ns}a\n  fact ba(1)\n  {a}\n  rule see(1) :- {r}\nend\n\
             namespace zzRDGQC.{ns}b\n  fact bb(1)\n  {b}\n  rule see(1) :- {r}\nend\n",
            ns = $ns,
            a = $a_head,
            b = $b_head,
            r = $read,
        )
    };
}

// ── PART A — THE ADMITTED SHAPES: two scopes, two predicates ────────────────

#[test]
fn an_applied_head_is_scoped_where_it_is_written() {
    let src = inverted_pair!(
        "ap",
        "rule pick(1) :- ba(999)",
        "rule pick(1) :- bb(1)",
        "pick(?)"
    );
    let mut kb = crate::common::load_kb_with(&src);
    assert!(
        kb.try_resolve_symbol("zzRDGQC.apa.pick").is_some()
            && kb.try_resolve_symbol("zzRDGQC.apb.pick").is_some(),
        "each scope's head is its own symbol — the mint this whole census is about"
    );
    assert_eq!(
        answers(&mut kb, "zzRDGQC.apa.see"),
        0,
        "the FALSE scope must stay false — a 1 here is the other scope's clause"
    );
    assert_eq!(answers(&mut kb, "zzRDGQC.apb.see"), 1, "and the true one answers");
}

#[test]
fn a_paren_less_nullary_head_is_scoped_where_it_is_written() {
    // BACK-OUT 1 (drop `head_subject_name`'s `Term::Ident` arm): this row fails —
    // `zzRDGQC.nua.see` answers 1, from the OTHER scope's clause — while
    // `an_applied_head_is_scoped_where_it_is_written` is unmoved. The pair is the
    // measurement: the axis is the SPELLING, not the shape. Two more rows fall with it;
    // the module header names them.
    let src = inverted_pair!("nu", "rule pick :- ba(999)", "rule pick :- bb(1)", "pick");
    let mut kb = crate::common::load_kb_with(&src);
    // THE NAMES, NOT ONLY THE ANSWERS. P85Z7 records the pre-fix state as "NEITHER
    // `shared_pl` NOR `nsx.shared_pl` resolved to a symbol" while ONE uncitable global
    // held both clauses — so a count can be right for the wrong reason and the
    // acceptance asks for the symbols by name.
    assert!(
        kb.try_resolve_symbol("zzRDGQC.nua.pick").is_some()
            && kb.try_resolve_symbol("zzRDGQC.nub.pick").is_some(),
        "each scope's paren-less head is CITABLE under its own qualified name"
    );
    assert_eq!(answers(&mut kb, "zzRDGQC.nua.see"), 0);
    assert_eq!(answers(&mut kb, "zzRDGQC.nub.see"), 1);
}

#[test]
fn an_equation_subject_is_scoped_where_it_is_written() {
    // THE SYMBOL, NOT THE CLAUSE COUNT, and that is WI-898 rather than a weaker
    // assertion: an equation's stored clause is headed by the `<=>` CONNECTIVE, so it
    // indexes NOTHING under the subject and a clause census would read 0 either way.
    // What the mint decides is whether the NAME exists in this scope.
    let src = "namespace zzRDGQC.eqa\n  rule pick(?x) <=> 1\nend\n\
               namespace zzRDGQC.eqb\n  rule pick(?x) <=> 2\nend\n";
    let kb = crate::common::load_kb_with(src);
    let a = kb.try_resolve_symbol("zzRDGQC.eqa.pick");
    let b = kb.try_resolve_symbol("zzRDGQC.eqb.pick");
    assert!(
        a.is_some() && b.is_some() && a != b,
        "two scopes' equation subjects are TWO symbols, got {a:?} / {b:?}"
    );
}

// ── PART B — THE SHAPES LEFT OUT: the leak, pinned beside a control ─────────

/// A FACT HEAD IS SCOPED WHERE IT IS WRITTEN, EXACTLY AS THE `rule … :- true` SPELLING
/// OF THE SAME CLAUSE IS — the two are ONE clause (§1234: "a `fact` counts, since
/// `fact H` is `rule H :- true`"), so a program that reads one way for `fact` and
/// another for `rule` is two programs written one way.
///
/// THIS ROW USED TO PIN THE OPPOSITE, and the pair is why it moved. It asserted (2, 2)
/// — each namespace reading the OTHER's fact, neither name resolving, one uncitable
/// global holding both clauses — beside a `rule … :- true` control at (1, 1). The
/// control was the refutation sitting next to the claim: same clause, same two scopes,
/// opposite programs. That is P85Z7's and CZJ2N's defect class, and §6.1's "a fact head
/// is unscoped" was its statement rather than its justification.
///
/// WRITTEN AS THE PAIR, not as an absolute, so a regression shows up as the two
/// spellings DISAGREEING again rather than as a count nobody can rank.
#[test]
fn a_fact_head_is_scoped_exactly_like_the_rule_spelling_of_the_same_clause() {
    for (label, head) in [("fact", "fact pick(1)"), ("rule", "rule pick(1) :- true")] {
        let src = format!(
            "namespace zzRDGQC.{label}a\n  fact ba(1)\n  {head}\n  \
             rule see(1) :- pick(?)\nend\n\
             namespace zzRDGQC.{label}b\n  fact bb(1)\n  {head2}\n  \
             rule see(1) :- pick(?)\nend\n",
            head2 = head.replace("pick(1)", "pick(2)"),
        );
        let mut kb = crate::common::load_kb_with(&src);
        assert!(
            kb.try_resolve_symbol(&format!("zzRDGQC.{label}a.pick")).is_some()
                && kb.try_resolve_symbol(&format!("zzRDGQC.{label}b.pick")).is_some(),
            "{label}: each scope's head is CITABLE under its own qualified name"
        );
        assert_eq!(
            (
                answers(&mut kb, &format!("zzRDGQC.{label}a.see")),
                answers(&mut kb, &format!("zzRDGQC.{label}b.see"))
            ),
            (1, 1),
            "{label}: each scope answers from its OWN clause and neither from the other's"
        );
    }
}

#[test]
fn a_multi_head_rules_functors_are_unscoped_and_two_scopes_share_one_predicate() {
    // `subject_introduces` refuses at `head_count != 1` — a rule with several heads
    // names no SINGLE predicate — while each head still LANDS its own clause. The heads
    // therefore take the bare intern. WI-20260908-NE0E4 owns the fix and carries the
    // sharper cross-sort row; this is the census entry.
    let src = "namespace zzRDGQC.ma\n  fact base(0)\n  rule law: pick(1), other(9) :- base(0)\n  \
               rule see(?x) :- pick(?x)\nend\n\
               namespace zzRDGQC.mb\n  fact base(0)\n  rule law: pick(2), other(8) :- base(0)\n  \
               rule see(?x) :- pick(?x)\nend\n";
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(
        (answers(&mut kb, "zzRDGQC.ma.see"), answers(&mut kb, "zzRDGQC.mb.see")),
        (2, 2),
        "LIVE (NE0E4): each scope reads the other's head. Closing it makes this (1, 1)"
    );
    assert!(
        kb.try_resolve_symbol("zzRDGQC.ma.pick").is_none()
            && kb.try_resolve_symbol("zzRDGQC.mb.pick").is_none(),
        "and neither name is citable — the clauses live under one uncitable global, \
         which is WHY the readers cross. Closing NE0E4 makes both `is_some()`"
    );
    // THE CONTROL that isolates the HEAD COUNT: the same clause as a SINGLE-head rule
    // mints and does not leak. Without it the (2, 2) could be about the label.
    let ctl = "namespace zzRDGQC.mca\n  fact base(0)\n  rule pick(1) :- base(0)\n  \
               rule see(?x) :- pick(?x)\nend\n\
               namespace zzRDGQC.mcb\n  fact base(0)\n  rule pick(2) :- base(0)\n  \
               rule see(?x) :- pick(?x)\nend\n";
    let mut kb = crate::common::load_kb_with(ctl);
    assert_eq!(
        (answers(&mut kb, "zzRDGQC.mca.see"), answers(&mut kb, "zzRDGQC.mcb.see")),
        (1, 1),
        "single-head control must scope — that is what makes the axis the head COUNT"
    );
}

#[test]
fn a_host_provides_block_head_is_unscoped_and_two_specs_share_one_predicate() {
    // No scan pass DESCENDS into a `provides … language … end` block, so a rule head
    // written there reaches no `RuleHeadSite`. Its CLAUSE still lands, in the SPEC's
    // scope (WI-20260827-APXSS); its NAME lands nowhere. WI-20260821-TTHRK owns it.
    let src = "namespace zzRDGQC.pv\n\
               \x20 sort RecP\n    entity P(v: Int64)\n    rule see(?x) :- pick(?x)\n  end\n\
               \x20 sort RecQ\n    entity Q(v: Int64)\n    rule see(?x) :- pick(?x)\n  end\n\
               \x20 provides RecP language rust\n    artifact \"x.rs\"\n    rule pick(1) :- true\n  end\n\
               \x20 provides RecQ language rust\n    artifact \"y.rs\"\n    rule pick(2) :- true\n  end\n\
               end\n";
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(
        (
            answers(&mut kb, "zzRDGQC.pv.RecP.see"),
            answers(&mut kb, "zzRDGQC.pv.RecQ.see")
        ),
        (2, 2),
        "LIVE (TTHRK): each spec reads the other's block head. Closing it makes this (1, 1)"
    );
    assert!(
        kb.try_resolve_symbol("zzRDGQC.pv.RecP.pick").is_none()
            && kb.try_resolve_symbol("zzRDGQC.pv.RecQ.pick").is_none(),
        "and neither name is citable in its spec's scope — the NAME lands nowhere even \
         though APXSS already lands the CLAUSE. Closing TTHRK makes both `is_some()`"
    );
    // THE CONTROL: the SAME two rules written IN the sorts rather than in a block.
    let ctl = "namespace zzRDGQC.pc\n\
               \x20 sort RecP\n    entity P(v: Int64)\n    rule pick(1) :- true\n    \
               rule see(?x) :- pick(?x)\n  end\n\
               \x20 sort RecQ\n    entity Q(v: Int64)\n    rule pick(2) :- true\n    \
               rule see(?x) :- pick(?x)\n  end\n\
               end\n";
    let mut kb = crate::common::load_kb_with(ctl);
    assert_eq!(
        (
            answers(&mut kb, "zzRDGQC.pc.RecP.see"),
            answers(&mut kb, "zzRDGQC.pc.RecQ.see")
        ),
        (1, 1),
        "in-sort control must scope — that is what makes the axis the BLOCK"
    );
}

// ── PART C — EVERY `NoIntroduction` VARIANT IS REACHABLE, AND SAYS ITS OWN THING ──

/// The five reasons, each driven from source and read back through the
/// `BodylessRuleDeclaresNothing` diagnostic — the only user-visible face
/// [`load::NoIntroduction`] has. A SIXTH variant added without a producer, or without a
/// distinct sentence, shows up here as an unreached row or a duplicate.
///
/// PASSES AGAINST THE PRE-MERGE CODE, BY DESIGN — see the module header. Its teeth are
/// back-out 2 (two arms made to share a sentence), which fells this row alone.
#[test]
fn every_no_introduction_reason_is_reachable_and_distinct() {
    let rows: [(&str, &str, &str); 5] = [
        (
            "SeveralHeads",
            "namespace zzRDGQC.c1\n  rule aa(1), bb(2)\nend\n",
            "it writes 2 heads at once, and a declaration declares ONE predicate",
        ),
        (
            "DenialHead",
            "namespace zzRDGQC.c2\n  rule p(1) :- true\n  rule \u{22A5}\nend\n",
            "a `\u{22A5}` denial names no predicate, so there is nothing for it to declare",
        ),
        (
            "DesugaredSubject",
            "namespace zzRDGQC.c3\n  rule ?x.m(?y)\nend\n",
            "its head functor is the DESUGARING's",
        ),
        (
            "NotAnApplication",
            "namespace zzRDGQC.c4\n  rule ?x\nend\n",
            "its head is not a functor application, so it names no predicate",
        ),
        (
            "QualifiedSpelling",
            "namespace zzRDGQC.c5\n  rule ..nosuchxyz\nend\n",
            "`..nosuchxyz` is a QUALIFIED name",
        ),
    ];
    let mut seen: Vec<String> = Vec::new();
    for (reason, src, sentence) in rows {
        let errs = crate::common::try_load_kb_with(src)
            .err()
            .unwrap_or_else(|| panic!("{reason}: expected a load refusal, the program loaded"));
        let hit = errs
            .iter()
            .find(|e| e.contains("declares nothing"))
            .unwrap_or_else(|| panic!("{reason}: no `declares nothing` refusal in {errs:?}"));
        assert!(
            hit.contains(sentence),
            "{reason}: expected the sentence `{sentence}`, got `{hit}`"
        );
        seen.push(sentence.to_owned());
    }
    seen.sort();
    seen.dedup();
    assert_eq!(
        seen.len(),
        5,
        "each reason must say its OWN thing — two arms sharing a sentence is the drift \
         this file exists to catch"
    );
}

/// THE PAREN-LESS AND PARENTHESISED SPELLINGS OF A QUALIFIED HEAD GET ONE SENTENCE.
/// They did not: `rule ..nosuchxyz` got "its head is not a functor application" while
/// `rule ..nosuchxyz()` got the QUALIFIED one — two spellings of one head, two
/// explanations of one verdict, found by `/code-review` on P85Z7's diff. That is the
/// drift the single walk now makes unrepresentable; this row is its regression test.
#[test]
fn both_spellings_of_a_qualified_head_get_one_reason() {
    let detail = |src: &str| -> String {
        crate::common::try_load_kb_with(src)
            .err()
            .expect("expected a load refusal")
            .into_iter()
            .find(|e| e.contains("declares nothing"))
            .expect("expected a `declares nothing` refusal")
    };
    let bare = detail("namespace zzRDGQC.q1\n  rule ..nosuchxyz\nend\n");
    let parens = detail("namespace zzRDGQC.q2\n  rule ..nosuchxyz()\nend\n");
    let reason = |s: &str| s[s.find("declares nothing").unwrap()..].to_owned();
    assert_eq!(
        reason(&bare),
        reason(&parens),
        "one head, one verdict, one sentence"
    );
}
