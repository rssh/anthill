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
//! ── WI-20260821-RDGQC REWROTE FIVE OF THESE ROWS ────────────────────────────
//!
//! `fact H` IS `rule H :- true` (§1234 / §6.1), and a fact head now DECLARES its
//! predicate at the scope it is written in, as the `rule` spelling always did. Five rows
//! here documented places where the two behaved differently — above all "a fact head is
//! UNSCOPED, so one written in a nested `sort` resolves UP the chain", which had no
//! counterpart in the `rule` spelling: that spelling was refused HERE, TODAY, measured on
//! the shipped tree with no change applied. So those rows recorded one spelling escaping
//! 845G7, not a design. They are now SPELLING PAIRS ([`both_spellings`]): each asserts
//! the two texts are refused by the same rule, or by none.
//!
//! **EVERY AXIS BELOW WAS RE-MEASURED AFTER THE REWRITE** — applied, run over this file
//! plus `wi1001_secondary_entry_rule_test`, `wi1000_secondary_entry_content_test` and
//! `wi980_rule_head_order_test` (**77 rows** now, 74 before), and restored. Three of the
//! seven moved, and two of those had stopped measuring anything at all:
//!
//!   * **A keeps its count of 4 but changed its SET.** `a_fact_nested_in_the_main_entry_is_refused`
//!     left it (that program is now refused by 845G7 before R3 runs) and
//!     [`a_clause_reaching_the_predicate_through_an_import_is_refused`] joined it — its
//!     selective arm depends on the landing key now that the deferred import reaches the
//!     mint guard.
//!   * **B and F fell to ZERO, and three rows were written to restore them.** Both axes
//!     are about R3's ATTRIBUTION, and a BARE head no longer reaches it: a `fact` head
//!     declares where it is written, so those fixtures collide one rule earlier and R3
//!     never runs. Backing either axis out fell nothing — the axes were untested, which a
//!     stale count would have hidden. [`a_nested_sort_inside_the_entry_still_composes`],
//!     [`a_clause_nested_in_the_main_entry_is_attributed_to_it`] and
//!     [`a_namespace_under_the_types_address_is_not_the_main_entry`] reach R3 through a
//!     QUALIFIED head, which references at every arity and so does not collide. With them
//!     B fells 2 (one per direction of nesting) and F fells 1, as before.
//!   * C, D, E and G are unchanged at 1 each, on the rows they always named.
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
//! [`a_clause_reaching_the_predicate_through_an_import_is_refused`]) and the fourth
//! spelling the landing key reaches on the way
//! ([`a_clause_written_outside_the_type_is_named_as_such`]). RE-MEASURED: the set moved,
//! the count did not — see the note above.
//!
//! **B — THE ENTRY'S TEXT RANGE.** In `entry_range_at`, additionally require the range
//! to be the one the clause's scope IS (`kb.symbols.scope_id(r.address) ==
//! site.written_in` at the call site) — the pre-APXSS reading, under which a clause in a
//! scope NESTED in a declaration is not that declaration's. **EXACTLY 2 ROWS FAIL**, one
//! per direction of nesting: [`a_nested_sort_inside_the_entry_still_composes`] (a nested
//! `sort` inside a SECONDARY entry stops composing) and
//! [`a_clause_nested_in_the_main_entry_is_attributed_to_it`] (one inside the MAIN entry
//! stops being attributed to it). Both reach R3 through a QUALIFIED head — see the
//! re-measurement note above for why a bare one no longer can. Making `entry_range_at` return `None` outright instead fells
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
//! [`a_clause_reaching_the_predicate_through_an_import_is_refused`] — and only
//! its deferred-import row; that row's two controls, which name the predicate without a
//! deferred import, stay green, which is what says the axis is the TABLE and not the
//! shape.
//!
//! **F — THE MAIN-ENTRY TEST AS A TEXT RANGE.** Add a `None if
//! scope_display_name(written_in).starts_with("<pred>.") => in_main_entry = true` arm —
//! the name-PREFIX reading. **EXACTLY 1 ROW FAILS:**
//! [`a_namespace_under_the_types_address_is_not_the_main_entry`]. The refusal itself is
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
//!   * [`an_enclosing_namespace_clause_reads_alike_in_both_spellings`] is the ANTI-control
//!     and the other half of the spec sentence: nothing resolves INWARD, so a fact one
//!     level out is no clause of this predicate and the entry's rule stays ADMITTED. It
//!     is what says the census did not simply become "refuse everything nearby".
//!   * [`a_nested_sort_inside_the_entry_reads_alike_in_both_spellings`] passes either way under A and
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

/// WI-20260821-RDGQC — THE SAME FIXTURE IN BOTH SPELLINGS OF ONE CLAUSE, asserted to
/// load ALIKE, returning the `fact` spelling's errors for the caller to inspect.
///
/// `fact H` IS `rule H :- true` (§1234 / §6.1). Several rows in this file used to
/// document the places where the two did not behave alike — a fact head declared
/// nothing, so it fell to one global intern where the `rule` spelling declared at the
/// scope it was written in, and the resulting programs differed. That is the divergence
/// RDGQC closed, and these rows now GUARD the convergence instead of recording its
/// absence.
///
/// COMPARED BY DIAGNOSTIC CLASS, not by text: the two sources differ in length, so every
/// span and column does too, and a `rule` head renders differently from a `fact` one. The
/// class is what the claim is about — "these two texts are refused by the same rule, or
/// by none".
fn diagnostic_kinds(errs: &[String]) -> Vec<&'static str> {
    const CLASSES: [&str; 5] = [
        "introduces that name at",
        "is not allowed in a secondary entry",
        "assembled from more than one entry",
        "captures a name that already resolves",
        "declares nothing",
    ];
    let mut kinds: Vec<&'static str> = errs
        .iter()
        .map(|e| {
            CLASSES
                .iter()
                .copied()
                .find(|c| e.contains(c))
                .unwrap_or("<unclassified>")
        })
        .collect();
    kinds.sort_unstable();
    kinds
}

fn both_spellings(src_with_fact: &str) -> Vec<String> {
    // The QUALIFIED spelling first: it is a superstring of the bare one, so replacing the
    // bare one first would leave `rule Rec.freshp(2) :- true` spelled `Rec.rule …`.
    let rule_src = if src_with_fact.contains("fact Rec.freshp(2)") {
        src_with_fact.replace("fact Rec.freshp(2)", "rule Rec.freshp(2) :- true")
    } else {
        src_with_fact.replace("fact freshp(2)", "rule freshp(2) :- true")
    };
    assert_ne!(
        rule_src, src_with_fact,
        "the fixture must carry a `fact …freshp(2)` head for the pair to be a pair"
    );
    let fact_errs = errors_of(src_with_fact);
    let rule_errs = errors_of(&rule_src);
    assert_eq!(
        diagnostic_kinds(&fact_errs),
        diagnostic_kinds(&rule_errs),
        "the two spellings of ONE clause must load alike.\n  fact: {fact_errs:#?}\n  \
         rule: {rule_errs:#?}"
    );
    fact_errs
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

/// A FACT NESTED IN A SORT DECLARES ITS OWN PREDICATE, EXACTLY AS THE `rule … :- true`
/// SPELLING OF THE SAME CLAUSE DOES — so the pair is REFUSED, both ways, by 845G7.
///
/// THIS ROW ASSERTED THE OPPOSITE AND WAS THE DIVERGENCE'S CLEAREST STATEMENT. It read:
/// "A fact head is UNSCOPED (§5.3), so one written in a `sort` nested inside `Rec`
/// resolves UP the chain to `Rec.freshp` — and `Rec.Inner.freshp` does not exist". The
/// resolve-up had no counterpart in the `rule` spelling, which was refused HERE, TODAY,
/// with no change of any kind — measured on the shipped tree before RDGQC touched
/// anything. So the "rule" it documented was one spelling escaping 845G7, not a design.
#[test]
fn a_fact_nested_in_a_sort_is_refused_exactly_like_the_rule_spelling() {
    let errs = both_spellings(
        "namespace apxss.nfl\n  import anthill.prelude.{Int64}\n  \
         sort Rec\n    entity rec(n: Int64)\n    rule freshp(1) :- true\n    \
         sort Inner\n      entity inn(n: Int64)\n      fact freshp(2)\n    end\n  end\nend\n",
    );
    assert!(
        errs.iter().any(|e| e.contains("introduces that name at 2 scopes")
            && e.contains("apxss.nfl.Rec")
            && e.contains("apxss.nfl.Rec.Inner")),
        "845G7 names both scopes; got {errs:#?}"
    );
}

/// THE SAME NESTING WITH THE DECLARATION IN A SECONDARY ENTRY — also refused, also
/// identically in both spellings. It used to be R3's condition (2) that caught this
/// (the fact's clause reached `Rec.freshp` because the fact head declared nothing);
/// 845G7 catches it now, one rule earlier and for both keywords.
#[test]
fn a_fact_nested_in_the_main_entry_is_refused() {
    let errs = both_spellings(
        "namespace apxss.nested\n  import anthill.prelude.{Int64}\n  \
         sort Rec\n    entity rec(n: Int64)\n    \
         sort Inner\n      entity inn(n: Int64)\n      fact freshp(2)\n    end\n  end\n  \
         namespace Rec\n    rule freshp(1) :- true\n  end\nend\n",
    );
    assert!(
        errs.iter().any(|e| e.contains("introduces that name at 2 scopes")),
        "the program is still refused, in both spellings; got {errs:#?}"
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

/// A CLAUSE REACHING THE PREDICATE THROUGH AN IMPORT — three import shapes, each in
/// BOTH spellings, each still refused.
///
/// THE SELECTIVE ARM FIXED A DEFECT OLDER THAN THIS FILE (WI-20260821-RDGQC). A
/// selective predicate import is deferred to sub-pass 4, because its target may not be
/// minted until sub-pass 3 has run — so at mint time `import X.Rec.{freshp}` had not
/// been wired, and a `freshp` head in `Side` read as introducing a name of its own.
/// MEASURED, with none of RDGQC's other changes applied: `rule freshp(2) :- true` there
/// MINTED `Side.freshp` and left the import DEAD, the author's clause silently becoming
/// its own predicate rather than a clause of the one they imported, on a program that
/// loaded clean. The `fact` spelling dodged it only because a fact head did not mint —
/// which is how R3 came to be the thing reporting this shape at all. The mint now asks
/// whether a deferred import brings the name in, so NEITHER spelling mints, both clauses
/// land on `Rec.freshp`, and R3 refuses the cross-entry assembly for both.
///
/// THE WILDCARD ARM IS REFUSED BY 845G7 RATHER THAN BY R3, and that is C666A's rule
/// showing through: a wildcard import is a whole-scope, non-enclosing edge, which does
/// NOT let a head join the predicate it exposes — so both spellings declare their own
/// and collide. Refused either way; the message names the more fundamental fault.
#[test]
fn a_clause_reaching_the_predicate_through_an_import_is_refused() {
    for (label, imp, body, expect) in [
        (
            "a SELECTIVE predicate import — deferred to sub-pass 4",
            "    import apxss.di.Rec.{freshp}\n",
            "    fact freshp(2)\n",
            "assembled from more than one entry",
        ),
        (
            "a WILDCARD import — a whole-scope edge, so the head declares its own",
            "    import apxss.di.Rec.*\n",
            "    fact freshp(2)\n",
            "introduces that name at 2 scopes",
        ),
        (
            "no import at all — a qualified head, which REFERENCES at every arity",
            "",
            "    fact Rec.freshp(2)\n",
            "assembled from more than one entry",
        ),
    ] {
        let src = format!(
            "namespace apxss.di\n  import anthill.prelude.{{Int64}}\n  \
             sort Rec\n    entity rec(n: Int64)\n  end\n  \
             namespace Side\n{imp}{body}  end\n  \
             namespace Rec\n    rule freshp(1) :- true\n  end\nend\n"
        );
        // BOTH SPELLINGS, and the qualified arm exercises the other substitution — a
        // qualified head never introduces, so it must stay R3's in both keywords.
        let rule_src = src
            .replace("fact freshp(2)", "rule freshp(2) :- true")
            .replace("fact Rec.freshp(2)", "rule Rec.freshp(2) :- true");
        for (spelling, text) in [("fact", &src), ("rule", &rule_src)] {
            let errs = errors_of(text);
            assert!(
                errs.iter().any(|e| e.contains(expect)),
                "{label} ({spelling}): expected `{expect}`; got {errs:#?}"
            );
        }
    }
}

/// A NAMESPACE UNDER THE TYPE'S ADDRESS is not the type's own declaration — still true,
/// and now said in both spellings. The refusal moved from R3's condition (2) to 845G7
/// for the same reason every other row here did.
#[test]
fn a_namespace_under_the_types_address_is_not_its_declaration() {
    let errs = both_spellings(
        "namespace apxss.under\n  import anthill.prelude.{Int64}\n  \
         sort Rec\n    entity rec(n: Int64)\n  end\n  \
         namespace Rec.Helper\n    fact freshp(2)\n  end\n  \
         namespace Rec\n    rule freshp(1) :- true\n  end\nend\n",
    );
    assert!(
        errs.iter().any(|e| e.contains("introduces that name at 2 scopes")
            && e.contains("apxss.under.Rec.Helper")),
        "the helper namespace is named as a contributor; got {errs:#?}"
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

/// AN ENCLOSING NAMESPACE'S CLAUSE, both spellings alike. It used to be admitted for the
/// `fact` spelling ("the enclosing fact does not join") because the fact fell to the bare
/// intern and so really was a separate predicate — accidentally the right answer, by the
/// mechanism that made two scopes share one name everywhere else. Both spellings are now
/// refused, by 845G7, and an author who wants two predicates declares them.
#[test]
fn an_enclosing_namespace_clause_reads_alike_in_both_spellings() {
    let errs = both_spellings(
        "namespace apxss.encl\n  import anthill.prelude.{Int64}\n  \
         fact freshp(2)\n  \
         sort Rec\n    entity rec(n: Int64)\n  end\n  \
         namespace Rec\n    rule freshp(1) :- true\n  end\nend\n",
    );
    assert!(
        errs.iter().any(|e| e.contains("introduces that name at 2 scopes")),
        "both spellings are refused; got {errs:#?}"
    );
}

/// A NESTED `sort` INSIDE A SECONDARY ENTRY: the two clauses are no longer one
/// predicate, and the pair says so in both spellings.
///
/// It was the FALSE-REFUSAL CONTROL — "a fact written in it resolves up to the entry's
/// own predicate, so BOTH clauses are this one entry's text, condition (2) holds, and
/// the rule is ADMITTED". The resolve-up is what carried it, and the `rule` spelling
/// never had it. What the row still decides is unchanged and still worth driving: the
/// two spellings must agree, whatever the answer is.
#[test]
fn a_nested_sort_inside_the_entry_reads_alike_in_both_spellings() {
    let errs = both_spellings(
        "namespace apxss.entrynest\n  import anthill.prelude.{Int64}\n  \
         sort Rec\n    entity rec(n: Int64)\n  end\n  \
         namespace Rec\n    rule freshp(1) :- true\n    \
         sort Inner\n      entity inn(n: Int64)\n      fact freshp(2)\n    end\n  end\nend\n",
    );
    assert!(
        errs.iter().any(|e| e.contains("introduces that name at 2 scopes")),
        "a nested sort declares its own predicate, in both spellings; got {errs:#?}"
    );
}



// ── THE R3 SUBJECTS, REACHED BY A QUALIFIED HEAD ────────────────────────────
//
// WI-20260821-RDGQC — three of this file's rows measure R3's ATTRIBUTION (which text a
// clause is credited to), and a bare head no longer reaches it: since a `fact` head
// declares where it is written, the bare fixtures collide at 845G7 one rule earlier and
// R3 never runs. MEASURED, and this is why the rows are here rather than simply
// re-pointed: with the bare fixtures alone, backing out AXIS B or AXIS F fells ZERO
// rows — the axes were left untested.
//
// A QUALIFIED head REFERENCES at every arity and introduces nothing (§"A
// rule-introduced functor is scoped where it is written"), so it does not collide, its
// clause lands on what it names, and R3's attribution runs exactly as before. Each row
// is still a spelling PAIR — `fact Rec.freshp(2)` and `rule Rec.freshp(2) :- true` both
// reference — so the convergence this ticket is about is asserted here too.

/// AXIS B, ONE DIRECTION: a nested `sort` inside a SECONDARY entry composes — both
/// clauses are that one entry's text, so the rule is ADMITTED.
#[test]
fn a_nested_sort_inside_the_entry_still_composes() {
    let errs = both_spellings(
        "namespace apxss.entrynest\n  import anthill.prelude.{Int64}\n  \
         sort Rec\n    entity rec(n: Int64)\n  end\n  \
         namespace Rec\n    rule freshp(1) :- true\n    \
         sort Inner\n      entity inn(n: Int64)\n      fact Rec.freshp(2)\n    end\n  end\nend\n",
    );
    assert!(
        errs.is_empty(),
        "both clauses are ONE entry's text; got {errs:#?}"
    );
}

/// AXIS B, THE OTHER DIRECTION: a clause nested inside the MAIN entry is attributed to
/// it, and the message says so.
#[test]
fn a_clause_nested_in_the_main_entry_is_attributed_to_it() {
    let errs = both_spellings(
        "namespace apxss.nested\n  import anthill.prelude.{Int64}\n  \
         sort Rec\n    entity rec(n: Int64)\n    \
         sort Inner\n      entity inn(n: Int64)\n      fact Rec.freshp(2)\n    end\n  end\n  \
         namespace Rec\n    rule freshp(1) :- true\n  end\nend\n",
    );
    assert_spans_entries(
        &errs,
        "apxss.nested.Rec",
        "a clause is written in the main entry",
    );
}

/// AXIS F: a `namespace` under the type's ADDRESS is not the type's own declaration —
/// the message must name that scope, not call it the main entry. The name-prefix reading
/// of "main entry" gets this wrong, and this row is what says so.
#[test]
fn a_namespace_under_the_types_address_is_not_the_main_entry() {
    let errs = both_spellings(
        "namespace apxss.under\n  import anthill.prelude.{Int64}\n  \
         sort Rec\n    entity rec(n: Int64)\n  end\n  \
         namespace Rec.Helper\n    fact Rec.freshp(2)\n  end\n  \
         namespace Rec\n    rule freshp(1) :- true\n  end\nend\n",
    );
    assert_spans_entries(&errs, "apxss.under.Rec", "'apxss.under.Rec.Helper'");
    assert!(
        !errs[0].contains("a clause is written in the main entry"),
        "a namespace under the type's address is not the type's own declaration; got \
         {:?}",
        errs[0]
    );
}
