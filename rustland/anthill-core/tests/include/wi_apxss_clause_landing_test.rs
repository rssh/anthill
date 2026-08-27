//! WI-20260827-APXSS — 059 R3's CONDITION (2) IS A CENSUS OF WHERE A CLAUSE **LANDS**.
//!
//! WI-1001 keyed it on the sites that INTRODUCE a name — `(scope, name)` read off the
//! `RuleHeadSite` / fact-head collections. Introducing and landing are TWO QUESTIONS,
//! and SEVEN spellings answer them differently. Each one wrote a second party's clause
//! onto the entry's predicate while introducing nothing at its `(scope, name)`, so each
//! LOADED CLEAN with the predicate holding two clauses — 059's worked harm, through the
//! one route R3 exists to close, and the exact program the plain `rule` spelling of the
//! same clause was already refused for. Three were found by `/code-review` on the
//! WI-20260827-P1TPE diff and two more on this ticket's own; the other two by asking the
//! landing question of every form the loader files a clause from.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! SEVEN AXES, so SEVEN BACK-OUTS — each APPLIED AND RUN over this file plus
//! `wi1001_secondary_entry_rule_test`, `wi1000_secondary_entry_content_test` and
//! `wi980_rule_head_order_test` (74 rows), and each PRESENT-BUT-WRONG rather than
//! deleted: deleting a census fells WI-1001's own rows for the wrong reason.
//!
//! **A — THE LANDING KEY.** In `judge_secondary_entry_rules`' condition (2), filter the
//! landed sites back down to WI-1001's key — `site.resolves_in == scope && site.subject
//! == name`, which is that census expressed on the new, wider one — leaving every other
//! part of the change in place. **EXACTLY 4 ROWS FAIL:** the three refusals the ticket
//! names ([`a_qualified_fact_head_in_the_main_entry_is_refused`],
//! [`a_qualified_rule_head_in_the_main_entry_is_refused`],
//! [`a_fact_nested_in_the_main_entry_is_refused`]) and the fourth spelling the landing
//! key reaches on the way ([`a_clause_written_outside_the_type_is_named_as_such`]).
//!
//! **B — THE ENTRY'S TEXT RANGE.** In `entry_range_at`, additionally require the range
//! to be the one the clause's scope IS (`kb.symbols.scope_id(r.address) ==
//! site.written_in` at the call site) — the pre-APXSS reading, under which a clause in a
//! scope NESTED in a declaration is not that declaration's. **EXACTLY 2 ROWS FAIL**, one
//! per direction of nesting: [`a_nested_sort_inside_the_entry_still_composes`] (a nested
//! `sort` inside a SECONDARY entry stops composing) and
//! [`a_fact_nested_in_the_main_entry_is_refused`] (one inside the MAIN entry stops being
//! attributed to it). Making `entry_range_at` return `None` outright instead fells
//! **16** — the entry's own rule then reads as the main entry's and every admitted
//! program is refused, which measures loadability rather than this axis, and is why the
//! back-out is the narrowing and not the deletion.
//!
//! **C — THE `provides` BLOCK CENSUS.** Drop the `Item::ProvidesBlock` arm from
//! `RuleHeadCollectPass::at_item`. **EXACTLY 1 ROW FAILS:**
//! [`a_provides_block_clause_beside_the_type_is_refused`]. It survives back-out A — a
//! block's clause resolves in the spec's scope under its own short name, so WI-1001's
//! key would have caught it HAD the pass walked the block at all, which it did not. Two
//! independent holes, two axes.
//!
//! **D — THE PER-HEAD CENSUS.** Make `RuleHeadCollectPass::collect`'s head loop take
//! only the single-head case (`.take(if head_count == 1 { 1 } else { 0 })`), which is the
//! population it used to answer for. **EXACTLY 1 ROW FAILS:**
//! [`a_multi_head_rule_in_the_main_entry_is_refused`]. It too survives A, for the same
//! reason C does: the heads resolve where they are written, and it is the pass that
//! never recorded them.
//!
//! **E — THE JUDGE'S POSITION AFTER SUB-PASS 4.** Move the judge (and 061's report,
//! which travels with it) back above `// Sub-pass 4 (WI-295)`. **EXACTLY 1 ROW FAILS:**
//! [`a_clause_reaching_the_predicate_through_a_deferred_import_is_refused`] — and only
//! its deferred-import row; that row's two controls, which name the predicate without a
//! deferred import, stay green, which is what says the axis is the TABLE and not the
//! shape.
//!
//! **F — THE MAIN-ENTRY TEST AS A TEXT RANGE.** Add a `None if
//! scope_display_name(written_in).starts_with("<pred>.") => in_main_entry = true` arm —
//! the name-PREFIX reading. **EXACTLY 1 ROW FAILS:**
//! [`a_namespace_under_the_types_address_is_not_its_declaration`]. The refusal itself is
//! unaffected either way; what moves is which text the message sends the author to.
//!
//! **G — THE EQUATION FILTER.** Drop `if introduced_by == RuleIntroduction::Predicate`
//! in `RuleHeadCollectPass::collect`, so an equation head records a clause site as
//! WI-1001's census did. **EXACTLY 1 ROW FAILS:**
//! [`an_equation_in_the_main_entry_does_not_refuse_the_entrys_rule`] — the one program
//! this ticket ADMITS that the narrower census refused. Its companion
//! [`an_equation_head_lands_no_clause_under_its_subject`] passes either way and is what
//! says the admission is right rather than merely different.
//!
//! **THE REST PASS EITHER WAY, AND EACH SAYS WHY IT IS HERE:**
//!
//!   * The five `…_really_lands…` rows and
//!     [`an_equation_head_lands_no_clause_under_its_subject`] measure the LOADER, not
//!     R3: no secondary entry is involved, so they are green before and after. They are
//!     what makes the verdicts above mean something — without them "refused" is equally
//!     true of an implementation that had simply broken the spelling, and "admitted" of
//!     one that had stopped judging.
//!   * [`a_multi_head_rule_in_the_main_entry_is_refused`]'s two single-head controls
//!     were refused BEFORE this change too, which is what says its axis is the head
//!     COUNT and not the label.
//!   * [`an_enclosing_namespace_fact_is_still_a_separate_predicate`] is the ANTI-control
//!     and the other half of the spec sentence: nothing resolves INWARD, so a fact one
//!     level out is no clause of this predicate and the entry's rule stays ADMITTED. It
//!     is what says the census did not simply become "refuse everything nearby".
//!   * [`a_nested_sort_inside_the_entry_still_composes`] passes either way under A and
//!     is axis B's own row: both clauses are in ONE entry, so condition (2) holds and
//!     the rule is admitted. The first cut of this change REFUSED it — measured — which
//!     is why the attribution is a TEXT-RANGE question and not a scope-prefix one.
//!
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

fn errors_of(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default()
}

/// The R3 refusals only.
fn r3_errors(src: &str) -> Vec<String> {
    errors_of(src)
        .into_iter()
        .filter(|e| e.contains("is not allowed in a secondary entry"))
        .collect()
}

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

/// The two clauses of `Rec.freshp` really are ONE predicate, driven: the count, the
/// answer, and the absence of any second predicate the clause could have gone to.
fn assert_composed(src: &str, ns: &str, apart: Option<&str>) {
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with(src));
    assert_eq!(
        clauses(&kb, &format!("{ns}.Rec.freshp")),
        Some(2),
        "the two clauses land on ONE predicate"
    );
    assert_eq!(answers(&mut kb, &format!("{ns}.Rec.freshp(1)")), 1);
    assert_eq!(
        answers(&mut kb, &format!("{ns}.Rec.freshp(2)")),
        1,
        "and it is the SECOND clause answering, not a variable head matching anything"
    );
    if let Some(other) = apart {
        assert_eq!(
            clauses(&kb, &format!("{ns}.{other}")),
            None,
            "the clause did not go to a predicate of its own at {other}"
        );
    }
}

/// Every R3 refusal this ticket adds names the SAME fault the undotted spelling already
/// got, so the reader gets one sentence for one kind of mistake.
fn assert_spans_entries(errs: &[String], sort: &str, wheres: &str) {
    assert_eq!(errs.len(), 1, "one predicate, one message; got {errs:#?}");
    assert!(
        errs[0].contains("assembled from more than one entry")
            && errs[0].contains(&format!("of sort '{sort}'"))
            && errs[0].contains(wheres),
        "expected condition (2) naming {wheres}; got {:?}",
        errs[0]
    );
}

// ── (1) A QUALIFIED `fact` HEAD IN THE MAIN ENTRY ───────────────────────────

/// THE LANDING, DRIVEN — and no secondary entry in sight, so this row is about the
/// LOADER and is green before and after this change. `fact Rec.freshp(2)` written inside
/// `sort Rec` resolves `Rec.freshp` through the dotted ladder and files its clause on
/// the predicate the neighbouring rule minted. It introduces NOTHING (a qualified head
/// references), which is exactly why WI-1001's census could not see it.
#[test]
fn a_qualified_fact_head_really_lands_on_the_predicate() {
    assert_composed(
        "namespace apxss.qfl\n  import anthill.prelude.{Int64}\n  \
         sort Rec\n    entity rec(n: Int64)\n    rule freshp(1) :- true\n    \
         fact Rec.freshp(2)\n  end\nend\n",
        "apxss.qfl",
        None,
    );
}

/// SO IT IS A CLAUSE, AND THE ENTRY'S RULE IS REFUSED.
#[test]
fn a_qualified_fact_head_in_the_main_entry_is_refused() {
    const MAIN: &str = "    fact Rec.freshp(2)\n    rule q(0) :- not freshp(1)\n";
    let src = format!(
        "namespace apxss.qfact\n  import anthill.prelude.{{Int64, Bool}}\n  \
         sort Rec\n    entity rec(n: Int64)\n{MAIN}  end\n  \
         namespace Rec\n    rule freshp(1) :- true\n  end\nend\n"
    );
    assert_spans_entries(
        &r3_errors(&src),
        "apxss.qfact.Rec",
        "a clause is written in the main entry",
    );
    // THE CONTROL, ONE NAME APART: the same entry beside a main-entry clause of a
    // DIFFERENT predicate is ADMITTED and answers. So what the refusal is about is the
    // clause landing on THIS predicate, not the qualified spelling and not the entry.
    let unrelated = "namespace apxss.qfact2\n  import anthill.prelude.{Int64}\n  \
                     sort Rec\n    entity rec(n: Int64)\n    rule otherp(2) :- true\n    \
                     fact Rec.otherp(3)\n  end\n  \
                     namespace Rec\n    rule freshp(1) :- true\n  end\nend\n";
    assert!(
        errors_of(unrelated).is_empty(),
        "the census is per PREDICATE; got {:?}",
        errors_of(unrelated)
    );
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with(unrelated));
    assert_eq!(answers(&mut kb, "apxss.qfact2.Rec.freshp(1)"), 1);
    assert_eq!(
        clauses(&kb, "apxss.qfact2.Rec.otherp"),
        Some(2),
        "and the qualified head still landed — on the predicate it names"
    );
}

// ── (2) A QUALIFIED `rule` HEAD IN THE MAIN ENTRY ───────────────────────────

/// THE LANDING, DRIVEN — the rule side of the same spelling.
#[test]
fn a_qualified_rule_head_really_lands_on_the_predicate() {
    assert_composed(
        "namespace apxss.qrl\n  import anthill.prelude.{Int64}\n  \
         sort Rec\n    entity rec(n: Int64)\n    rule freshp(1) :- true\n    \
         rule Rec.freshp(2) :- true\n  end\nend\n",
        "apxss.qrl",
        None,
    );
}

/// AND THE ASYMMETRY THAT GAVE IT AWAY: the SAME qualified spelling written inside the
/// SECONDARY entry was already refused ("this head introduces no name at all"), so only
/// the main entry's side leaked. Both halves are asserted here — the refusal the entry
/// side gets is unchanged, and it is a DIFFERENT sentence from the one the main entry's
/// clause now earns.
#[test]
fn a_qualified_rule_head_in_the_main_entry_is_refused() {
    let src = "namespace apxss.qrule\n  import anthill.prelude.{Int64}\n  \
               sort Rec\n    entity rec(n: Int64)\n    rule Rec.freshp(2) :- true\n  end\n  \
               namespace Rec\n    rule freshp(1) :- true\n  end\nend\n";
    assert_spans_entries(
        &r3_errors(src),
        "apxss.qrule.Rec",
        "a clause is written in the main entry",
    );
    let inside_the_entry = "namespace apxss.qrule2\n  import anthill.prelude.{Int64}\n  \
                            sort Rec\n    entity rec(n: Int64)\n    rule outer(?x)\n  end\n  \
                            namespace Rec\n    rule Rec.outer(2) :- true\n  end\nend\n";
    let errs = r3_errors(inside_the_entry);
    assert!(
        errs.iter()
            .any(|e| e.contains("this head introduces no name at all")),
        "CONTROL, unmoved: the entry's OWN qualified head is refused per rule; got \
         {errs:#?}"
    );
}

// ── (3) A `fact` IN A SCOPE NESTED INSIDE THE MAIN ENTRY ────────────────────

/// THE LANDING, DRIVEN. A fact head is UNSCOPED (§5.3), so one written in a `sort`
/// nested inside `Rec` resolves UP the chain to `Rec.freshp` — and `Rec.Inner.freshp`
/// does not exist, which is the half a clause count on `Rec.freshp` alone cannot say.
/// WI-1001's census filtered `f.scope == scope` and argued that only ENCLOSING scopes
/// fall away; a DESCENDANT one resolves up and does not.
#[test]
fn a_fact_nested_in_the_main_entry_really_lands_on_the_predicate() {
    assert_composed(
        "namespace apxss.nfl\n  import anthill.prelude.{Int64}\n  \
         sort Rec\n    entity rec(n: Int64)\n    rule freshp(1) :- true\n    \
         sort Inner\n      entity inn(n: Int64)\n      fact freshp(2)\n    end\n  end\nend\n",
        "apxss.nfl",
        Some("Rec.Inner.freshp"),
    );
}

#[test]
fn a_fact_nested_in_the_main_entry_is_refused() {
    let src = "namespace apxss.nested\n  import anthill.prelude.{Int64}\n  \
               sort Rec\n    entity rec(n: Int64)\n    \
               sort Inner\n      entity inn(n: Int64)\n      fact freshp(2)\n    end\n  end\n  \
               namespace Rec\n    rule freshp(1) :- true\n  end\nend\n";
    assert_spans_entries(
        &r3_errors(src),
        "apxss.nested.Rec",
        "a clause is written in the main entry",
    );
}

// ── (4) A CLAUSE WRITTEN OUTSIDE THE TYPE ALTOGETHER ────────────────────────

/// THE FOURTH SPELLING, which the landing key reaches on the way and which no
/// scope-keyed census can: a clause written in an ORDINARY namespace beside the type,
/// naming the predicate by its qualified path. It is neither the main entry's nor
/// another entry's, so it is reported as what it is — the message names the SCOPE the
/// clause is written at, not "the main entry".
#[test]
fn a_clause_written_outside_the_type_is_named_as_such() {
    assert_composed(
        "namespace apxss.sidel\n  import anthill.prelude.{Int64}\n  \
         sort Rec\n    entity rec(n: Int64)\n    rule freshp(1) :- true\n  end\n  \
         namespace Side\n    fact Rec.freshp(2)\n  end\nend\n",
        "apxss.sidel",
        None,
    );
    let src = "namespace apxss.side\n  import anthill.prelude.{Int64}\n  \
               sort Rec\n    entity rec(n: Int64)\n  end\n  \
               namespace Side\n    fact Rec.freshp(2)\n  end\n  \
               namespace Rec\n    rule freshp(1) :- true\n  end\nend\n";
    let errs = r3_errors(src);
    assert_spans_entries(&errs, "apxss.side.Rec", "'apxss.side.Side'");
    assert!(
        !errs[0].contains("a clause is written in the main entry"),
        "a namespace beside the type is not its declaration; got {:?}",
        errs[0]
    );
}

// ── (5) A HOST `provides … language … end` BLOCK BESIDE THE TYPE ────────────

/// THE LANDING, DRIVEN — and the spelling no SCOPE-keyed census can reach at all.
/// `load_provides_block` switches `current_scope` to the spec's BASE SORT before taking
/// the block's rules through the ordinary `load_rule` path, so a clause written in an
/// ordinary namespace files itself on `Rec`'s predicate. R3 already refuses a rule in a
/// block written INSIDE a secondary entry, for the mirror-image reason; nothing saw one
/// written OUTSIDE.
///
/// The grammar keeps this out of the MAIN entry — `_sort_content` admits `provides_clause`
/// and not `provides_block`, so a host block is written at namespace level or not at all.
#[test]
fn a_provides_block_clause_really_lands_on_the_specs_predicate() {
    assert_composed(
        "namespace apxss.pbl
  import anthill.prelude.{Int64}
           sort Rec
    entity rec(n: Int64)
    rule freshp(1) :- true
  end
           namespace Side
    provides Rec language rust
      artifact \"nowhere.rs\"
               carrier { Rec: \"Rec\" }
      rule freshp(2) :- true
    end
  end
end
",
        "apxss.pbl",
        None,
    );
}

/// SO IT IS A CLAUSE — and it is attributed to the TEXT it is written in, not to the
/// scope it resolves in. Reading the resolution scope would report it as `Rec`'s own
/// declaration, which is the point of a site carrying both.
#[test]
fn a_provides_block_clause_beside_the_type_is_refused() {
    let src = "namespace apxss.pbr
  import anthill.prelude.{Int64}
                 sort Rec
    entity rec(n: Int64)
  end
                 namespace Side
    provides Rec language rust
      artifact \"nowhere.rs\"
                     carrier { Rec: \"Rec\" }
      rule freshp(2) :- true
    end
  end
                 namespace Rec
    rule freshp(1) :- true
  end
end
";
    let errs = r3_errors(src);
    assert_spans_entries(&errs, "apxss.pbr.Rec", "'apxss.pbr.Side'");
    assert!(
        !errs[0].contains("a clause is written in the main entry"),
        "the block's TEXT is in a namespace beside the type, not in its declaration; \
         got {:?}",
        errs[0]
    );
}

// ── (6) EVERY HEAD OF A LABELED MULTI-HEAD RULE ─────────────────────────────

/// THE LANDING, DRIVEN — and the second axis on which a clause census is wider than an
/// introduces census. A LABELED multi-head rule fans out into one asserted rule per head
/// (`load_rule`), so each head files its own clause, while the RULE introduces nothing:
/// it names no single predicate, which is why `rule_introduced_functor_name` returns
/// `None` for it and why nothing recorded those heads.
#[test]
fn every_head_of_a_multi_head_rule_really_lands_a_clause() {
    assert_composed(
        "namespace apxss.mhl\n  import anthill.prelude.{Int64}\n  \
         sort Rec\n    entity rec(n: Int64)\n    rule freshp(1) :- true\n    \
         rule law: freshp(2), other(1) :- true\n  end\nend\n",
        "apxss.mhl",
        None,
    );
    // AND THE **SECOND** HEAD LANDS TOO — otherwise this row would be equally true of an
    // implementation that dropped everything after the first head. Both names are minted
    // by the main entry's own single-head rules, since a multi-head rule introduces
    // neither of them.
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with(
        "namespace apxss.mhl2\n  import anthill.prelude.{Int64}\n  \
         sort Rec\n    entity rec(n: Int64)\n    rule freshp(1) :- true\n    \
         rule other(9) :- true\n    rule law: freshp(2), other(1) :- true\n  end\nend\n",
    ));
    assert_eq!(clauses(&kb, "apxss.mhl2.Rec.freshp"), Some(2));
    assert_eq!(clauses(&kb, "apxss.mhl2.Rec.other"), Some(2));
    assert_eq!(answers(&mut kb, "apxss.mhl2.Rec.other(1)"), 1);
    assert_eq!(answers(&mut kb, "apxss.mhl2.Rec.freshp(2)"), 1);
}

/// SO EVERY HEAD IS A CLAUSE, AND THE ENTRY'S RULE IS REFUSED.
///
/// THE CONTROLS SEPARATE THE AXIS FROM THE LABEL, and both were run: the same clause
/// written `rule law: freshp(2) :- true` and `rule freshp(2) :- true` in the main entry
/// was ALREADY refused before this change, so what the multi-head row adds is the head
/// COUNT and not the label. (An UNLABELED multi-head rule never reaches the question —
/// `load_rule` refuses it for having no citation handle.)
#[test]
fn a_multi_head_rule_in_the_main_entry_is_refused() {
    let src = "namespace apxss.mh\n  import anthill.prelude.{Int64}\n  \
               sort Rec\n    entity rec(n: Int64)\n    \
               rule law: freshp(2), other(1) :- true\n  end\n  \
               namespace Rec\n    rule freshp(1) :- true\n  end\nend\n";
    assert_spans_entries(
        &r3_errors(src),
        "apxss.mh.Rec",
        "a clause is written in the main entry",
    );
    for (label, main) in [
        ("labeled single head", "    rule law: freshp(2) :- true\n"),
        ("unlabeled single head", "    rule freshp(2) :- true\n"),
    ] {
        let control = format!(
            "namespace apxss.mhc\n  import anthill.prelude.{{Int64}}\n  \
             sort Rec\n    entity rec(n: Int64)\n{main}  end\n  \
             namespace Rec\n    rule freshp(1) :- true\n  end\nend\n"
        );
        assert!(
            r3_errors(&control)
                .iter()
                .any(|e| e.contains("assembled from more than one entry")),
            "CONTROL, refused before this change too: {label}"
        );
    }
}

// ── (7) A CLAUSE REACHING THE PREDICATE THROUGH A DEFERRED IMPORT ───────────

/// THE CENSUS MUST READ THE IMPORT TABLE THE **LOAD** WILL READ. A SELECTIVE PREDICATE
/// import is deferred to sub-pass 4 (WI-295: the predicate's symbol does not exist until
/// sub-pass 3 mints it), so a census asked before that runs sees a table one rung short
/// of the loader's — and a clause reaching the predicate through such an import is
/// invisible.
///
/// THE THREE ROWS ARE ONE PROGRAM SHAPE, differing only in HOW the clause names the
/// predicate, and the two controls were already refused before this: the WILDCARD import
/// is wired in sub-pass 2, and the QUALIFIED head needs no import at all. Only the
/// deferred one escaped. Found by `/code-review`.
#[test]
fn a_clause_reaching_the_predicate_through_a_deferred_import_is_refused() {
    for (label, imp, body) in [
        (
            "a SELECTIVE predicate import — deferred to sub-pass 4",
            "    import apxss.di.Rec.{freshp}\n",
            "    fact freshp(2)\n",
        ),
        (
            "CONTROL: a WILDCARD import — wired in sub-pass 2",
            "    import apxss.di.Rec.*\n",
            "    fact freshp(2)\n",
        ),
        (
            "CONTROL: no import at all — a qualified head",
            "",
            "    fact Rec.freshp(2)\n",
        ),
    ] {
        let src = format!(
            "namespace apxss.di\n  import anthill.prelude.{{Int64}}\n  \
             sort Rec\n    entity rec(n: Int64)\n  end\n  \
             namespace Side\n{imp}{body}  end\n  \
             namespace Rec\n    rule freshp(1) :- true\n  end\nend\n"
        );
        let errs = r3_errors(&src);
        assert!(
            errs.iter().any(|e| e.contains("assembled from more than one entry")
                && e.contains("'apxss.di.Side'")),
            "{label}: expected condition (2) naming the namespace the clause is written \
             in; got {errs:#?}"
        );
    }
}

/// AND A NAMESPACE **UNDER** THE TYPE'S ADDRESS IS NOT ITS DECLARATION. `namespace
/// Rec.Helper` is an ordinary namespace whose qualified name begins with the type's, so
/// a name-PREFIX reading of "is this the main entry" claims it — and sends the author to
/// a `sort` body that contains nothing of the kind. Whose declaration a clause sits in
/// is a TEXT-RANGE question at the predicate's own address, which is what
/// [`EntryTextRange`](../../../src/kb/load.rs) answers. Found by `/code-review`.
#[test]
fn a_namespace_under_the_types_address_is_not_its_declaration() {
    let src = "namespace apxss.under\n  import anthill.prelude.{Int64}\n  \
               sort Rec\n    entity rec(n: Int64)\n  end\n  \
               namespace Rec.Helper\n    fact freshp(2)\n  end\n  \
               namespace Rec\n    rule freshp(1) :- true\n  end\nend\n";
    let errs = r3_errors(src);
    assert_spans_entries(&errs, "apxss.under.Rec", "'apxss.under.Rec.Helper'");
    assert!(
        !errs[0].contains("a clause is written in the main entry"),
        "a namespace under the type's address is not the type's own declaration; got \
         {:?}",
        errs[0]
    );
}

// ── AN EQUATION IS NOT A CLAUSE OF ITS SUBJECT ──────────────────────────────

/// THE OTHER DIRECTION OF "WHERE DOES THE CLAUSE LAND", and the one a wider census gets
/// wrong. An equation's stored clause is headed by the `eq`/`unify` CONNECTIVE, so it
/// indexes NOTHING under the subject's name — the name is co-owned (WI-898's kind SET),
/// the PREDICATE is not. Condition (2) counts clauses, so it must not see one.
///
/// DRIVEN BOTH WAYS in one shape: the equation's subject holds ZERO clauses where a
/// predicate head of the same name holds one. Green before and after — it measures the
/// LOADER.
#[test]
fn an_equation_head_lands_no_clause_under_its_subject() {
    let program = |main: &str| {
        format!(
            "namespace apxss.eqn\n  import anthill.prelude.{{Int64}}\n  \
             sort Rec\n    entity rec(n: Int64)\n{main}  end\nend\n"
        )
    };
    let kb = crate::common::expect_loaded(crate::common::try_load_kb_with(&program(
        "    rule freshp(1) <=> 2\n",
    )));
    assert_eq!(
        clauses(&kb, "apxss.eqn.Rec.freshp"),
        Some(0),
        "the equation's clause is filed under the connective, not under its subject"
    );
    let kb = crate::common::expect_loaded(crate::common::try_load_kb_with(&program(
        "    rule freshp(1) :- true\n",
    )));
    assert_eq!(
        clauses(&kb, "apxss.eqn.Rec.freshp"),
        Some(1),
        "CONTROL: a PREDICATE head of the same name does file one"
    );
}

/// SO CONDITION (2) HOLDS, AND THE ENTRY'S RULE IS ADMITTED — with the equation written
/// in the main entry, where WI-1001's `(scope, name)` census counted it and refused.
/// This is the one place this ticket ADMITS a program the narrower census refused, and
/// it is what "a census of CLAUSES" means.
#[test]
fn an_equation_in_the_main_entry_does_not_refuse_the_entrys_rule() {
    for (label, main) in [
        ("an undotted subject", "    rule freshp(1) <=> 2\n"),
        ("a qualified subject", "    rule Rec.freshp(1) <=> 2\n"),
    ] {
        let src = format!(
            "namespace apxss.eqadm\n  import anthill.prelude.{{Int64}}\n  \
             sort Rec\n    entity rec(n: Int64)\n{main}  end\n  \
             namespace Rec\n    rule freshp(1) :- true\n  end\nend\n"
        );
        assert!(
            errors_of(&src).is_empty(),
            "{label}: an equation lands no clause on the predicate, so ONE entry still \
             owns it; got {:?}",
            errors_of(&src)
        );
        let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with(&src));
        assert_eq!(
            answers(&mut kb, "apxss.eqadm.Rec.freshp(1)"),
            1,
            "{label}: and the admitted rule ANSWERS"
        );
    }
}

// ── The two controls ────────────────────────────────────────────────────────

/// THE ANTI-CONTROL, and the other half of the spec sentence. A fact head is unscoped,
/// so one in an ENCLOSING namespace falls to the bare intern — nothing there resolves
/// INWARD — and is no clause of the entry's predicate. The entry's rule stays ADMITTED
/// and ANSWERS, which is what says the landing census did not become "refuse anything
/// spelled the same nearby".
#[test]
fn an_enclosing_namespace_fact_is_still_a_separate_predicate() {
    let src = "namespace apxss.encl\n  import anthill.prelude.{Int64}\n  \
               fact freshp(2)\n  \
               sort Rec\n    entity rec(n: Int64)\n  end\n  \
               namespace Rec\n    rule freshp(1) :- true\n  end\nend\n";
    assert!(
        errors_of(src).is_empty(),
        "the enclosing fact does not join; got {:?}",
        errors_of(src)
    );
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with(src));
    assert_eq!(clauses(&kb, "apxss.encl.Rec.freshp"), Some(1));
    assert_eq!(answers(&mut kb, "apxss.encl.Rec.freshp(1)"), 1);
    assert_eq!(
        answers(&mut kb, "apxss.encl.Rec.freshp(2)"),
        0,
        "so the two really are separate predicates"
    );
    // …UNLESS THE ENCLOSING SCOPE IMPORTS THE TYPE'S CONTENTS, which is what makes the
    // name resolve inward after all. "Enclosing" was never the property; RESOLVING is,
    // and this row is why the rule cannot be stated over lexical position. Found by
    // `/code-review` on the sentence this ticket added to the spec.
    let importing = "namespace apxss.enclimp\n  import anthill.prelude.{Int64}\n  \
                     import apxss.enclimp.Rec.*\n  fact freshp(2)\n  \
                     sort Rec\n    entity rec(n: Int64)\n  end\n  \
                     namespace Rec\n    rule freshp(1) :- true\n  end\nend\n";
    assert!(
        r3_errors(importing)
            .iter()
            .any(|e| e.contains("assembled from more than one entry")),
        "with the import the enclosing fact DOES land; got {:?}",
        r3_errors(importing)
    );
}

/// THE FALSE-REFUSAL CONTROL. A nested `sort` inside a SECONDARY entry is allowed (059
/// R3), and a fact written in it resolves up to the entry's own predicate — so BOTH
/// clauses are this one entry's text, condition (2) holds, and the rule is ADMITTED.
///
/// It is the row that decides HOW a clause is attributed. A landing census that reads
/// "the predicate's scope or any descendant of it ⇒ the main entry" refuses this
/// program, because `Rec.Inner` is a descendant either way; the entry a clause belongs
/// to is a question about the TEXT it is written in, which is how 059 individuates one.
#[test]
fn a_nested_sort_inside_the_entry_still_composes() {
    let src = "namespace apxss.entrynest\n  import anthill.prelude.{Int64}\n  \
               sort Rec\n    entity rec(n: Int64)\n  end\n  \
               namespace Rec\n    rule freshp(1) :- true\n    \
               sort Inner\n      entity inn(n: Int64)\n      fact freshp(2)\n    end\n  end\nend\n";
    assert!(
        errors_of(src).is_empty(),
        "both clauses are ONE entry's text; got {:?}",
        errors_of(src)
    );
    let mut kb = crate::common::expect_loaded(crate::common::try_load_kb_with(src));
    assert_eq!(clauses(&kb, "apxss.entrynest.Rec.freshp"), Some(2));
    assert_eq!(answers(&mut kb, "apxss.entrynest.Rec.freshp(2)"), 1);
}


