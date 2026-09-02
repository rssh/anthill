//! WI-20260821-P85Z7 — A PAREN-LESS NULLARY RULE HEAD IS AN APPLICATION OF ARITY 0, AND
//! IS SCOPED WHERE IT IS WRITTEN.
//!
//! `rule holds :- base(1)` used to introduce NOTHING, ANYWHERE. The parser gives a bare
//! name a `Term::Ident` rather than a zero-argument `Term::Fn`, and `head_subject_name`
//! read only the `Fn` shape — so no `RuleHeadSite` was collected, `scan_rule_goal` never
//! minted, and the head fell to `remap_name_str`'s bare `intern(name)` fallback: ONE
//! GLOBAL NAME that two scopes' same-spelled heads then shared, with the loser's clause
//! answering inside the winner's scope, on a program that loaded clean. That is WI-894's
//! defect class — §"A rule-introduced functor is scoped where it is written" exists to
//! stop exactly it — and the nullary spelling never entered the fix.
//!
//! THE PARENTHESISED TWIN WAS ALREADY RIGHT, which is what made this a defect rather
//! than a design: `rule holds()` scoped, `rule holds` did not. Two spellings of one
//! nullary predicate, opposite programs. Every row below is written as that PAIR, so a
//! regression shows up as the two spellings disagreeing again rather than as an absolute
//! count nobody can rank.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! FOUR AXES, so FOUR BACK-OUTS. Each is PRESENT-BUT-WRONG rather than deleted, and
//! each was applied and run over the WHOLE `wi_tests` binary — 3 978 rows, not a
//! hand-picked neighbourhood — so each count below is EXHAUSTIVE over that population:
//! every row not named passed, anywhere in the suite. The counts are the failures, since
//! the complement is the binary's size and adds nothing.
//!
//! **AXIS C IS GONE, AND TWO ROWS HERE FLIPPED — WI-20260902-CZJ2N.** The two nullary
//! head spellings are ONE TERM now, so a bare `[simp]` head DEFINES and its subject
//! MINTS. The counts below are as measured when this ticket shipped; the rows they name
//! are unchanged except where said. See
//! [`a_bare_equation_subject_defines_exactly_like_its_parenthesised_twin`] and
//! [`a_bare_equation_subject_mints_exactly_like_its_parenthesised_twin`], each of which
//! carries its own back-out.
//!
//! **A — THE HEAD'S NULLARY SHAPE.** In `head_subject_name`, drop the `Term::Ident`
//! arm (`_ => return None` alone), which is the pre-fix reading. **EXACTLY 4 ROWS FAIL:**
//! [`two_scopes_writing_one_bare_nullary_head_get_two_predicates`],
//! [`two_scopes_that_see_each_other_are_refused_in_both_spellings`],
//! [`a_bare_nullary_clause_is_indexed_under_the_scoped_symbol`] here, and
//! `wi_fqc85_rule_declaration_test::a_body_less_bare_nullary_head_declares_its_predicate`.
//! [`a_bare_equation_subject_defines_exactly_like_its_parenthesised_twin`] passed either
//! way BY DESIGN under this ticket's reading; since CZJ2N its BARE arm depends on the
//! mint, so axis A fells it too. [`a_marked_absolute_nullary_head_that_names_nothing_is_refused`]
//! still passes either way here — its axis is B.
//!
//! **B — THE MARKED-ABSOLUTE REFUSAL.** In `Loader::load_rule`'s head loop, narrow the
//! pattern back to `Term::Fn { functor, .. }` so a paren-less marked head is not asked.
//! **EXACTLY 1 ROW FAILS:**
//! [`a_marked_absolute_nullary_head_that_names_nothing_is_refused`],
//! and only its BARE arm — its parenthesised arm and its RESOLVABLE arm pass either way,
//! which is what says the axis is the SPELLING and not the marker.
//!
//! **C — THE PREDICATE-PATH GATE. WITHDRAWN BY WI-20260902-CZJ2N.** The guard is
//! deleted, not narrowed: a bare EQUATION subject mints exactly as a parenthesised one
//! does. Its measurement was `a_bare_equation_subjects_citation_stays_loud`, which
//! asserted the REFUSAL the mint suppresses; that row is replaced by
//! [`a_bare_equation_subject_mints_exactly_like_its_parenthesised_twin`], whose
//! back-out is "restore the guard" and whose failing rows are the `bare` arm's two.
//! The reasoning for both directions is at that row.
//!
//! **D — THE DETAIL WALK'S NULLARY READING.** In `bodyless_declares_nothing_detail`,
//! narrow the head destructure back to `Term::Fn { functor, .. }`, so the sentence
//! explaining a refusal stops reading a bare name as an application. **EXACTLY 1 ROW
//! FAILS:** [`a_body_less_qualified_heads_refusal_reads_alike_in_both_spellings`], on its
//! BARE arm. The VERDICT is unmoved by this axis — only its explanation is — which is why
//! no other row sees it.
//!
//! ── WHAT THIS TICKET DELIBERATELY DID NOT FIX, AND WHERE IT WENT ────────────
//!
//! `a_dotted_paren_less_head_still_lands_no_clause` PINNED the one paren-less spelling
//! still silent — a QUALIFIED one (`rule nsx.tgt :- b(1)`), which the converter folds
//! into a minted `field_access` chain, so its clause landed under `field_access` and not
//! on `nsx.tgt`. WI-20260901-719FJ CLOSED IT, and the row moved there with its text
//! (`wi_719fj_dotted_paren_less_citation_test`): the chain is now read as the NAME it
//! spells in the rule head, the fact head, the rule-body goal and the query pattern
//! alike, while the operation body keeps proposal 052 §6.7's `Relation[T]` value. It
//! was never this ticket's shape — the same chain is what a dotted paren-less CITATION
//! lowers to in every position, so deciding it for the head meant deciding it for the
//! other three at once.
//!
//! A **fact** head stays unscoped at every arity (§6.1, and WI-20260821-RDGQC's
//! enumeration owns the question) — `fact holds` and `fact holds()` are alike, which is
//! what [`a_fact_head_is_unscoped_in_both_spellings`] asserts. The paren-less spelling
//! is therefore NOT a second hole on the fact side; it is the same one, whole.
//!
//! STDLIB LOADS: TWO —
//! [`a_bare_equation_subject_defines_exactly_like_its_parenthesised_twin`] and
//! [`a_bare_equation_subject_mints_exactly_like_its_parenthesised_twin`] need an
//! interpreter. Every other row uses `try_load_kb_with` / `load_kb_with`, which
//! bootstrap only.

use anthill_core::eval::Value;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// How many DEFINITE solutions `pattern` has, driven through the shipped query-pattern
/// path — the same instrument `wi_fqc85_rule_declaration_test` uses, so a head landing on
/// a different symbol is counted exactly as `anthill query` would count it.
///
/// DEFINITE, and that was a REAL MISS here rather than a precaution
/// (WI-20260901-719FJ found it): a plain `.len()` counts a FLOUNDERED solution as an
/// answer (WI-20260822-WZX6B, `common::definite_unary`'s doc), and this file has a
/// pattern that floundered — `zzP85Z7.idx.pl` is itself a DOTTED PAREN-LESS citation, so
/// before 719FJ it lowered to `field_access(zzP85Z7.idx, pl)` and came back
/// `conditional / residual: eq(field_access(…), true)`. MEASURED: with BOTH of that
/// fixture's clause bodies made false the count stayed 1, so
/// [`a_bare_nullary_clause_is_indexed_under_the_scoped_symbol`]'s "and the goal reaches
/// them" assertion was passing on a residual and proved nothing. It measures now.
fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

/// The clauses stored under the symbol `qn` names — `None` when NOTHING is named `qn`.
/// The distinction this file is about: pre-fix both scopes' `pl` answered `None` while
/// one uncitable global held both clauses.
fn clauses(kb: &KnowledgeBase, qn: &str) -> Option<usize> {
    let sym = kb.try_resolve_symbol(qn)?;
    Some(kb.rules_by_functor(sym).len())
}

/// THE TICKET'S OWN MEASUREMENT, INVERTED so a merge is visible rather than inferred:
/// `zzA`'s clause is FALSE and `zzB`'s is TRUE, and each namespace reads its own `pl`
/// through a unary rule of its own. Asserting only `zzB` would pass against the defect.
///
/// The two namespaces are SIBLINGS that cannot see each other, so 845G7's collision
/// refusal does not fire — this row is about the SPLIT, and the refusal is the next row.
const INVERTED_PAIR: &str = "\
namespace zzP85Z7.a
  fact ba(1)
  rule pl :- ba(999)
  rule seeA(1) :- pl
end

namespace zzP85Z7.b
  fact bb(1)
  rule pl :- bb(1)
  rule seeB(1) :- pl
end
";

/// The same program with every nullary head PARENTHESISED — the spelling that was
/// already right, so the pair says the two spellings now agree rather than merely that
/// one of them works.
const INVERTED_PAIR_PARENS: &str = "\
namespace zzP85Z7.pa
  fact ba(1)
  rule pl() :- ba(999)
  rule seeA(1) :- pl()
end

namespace zzP85Z7.pb
  fact bb(1)
  rule pl() :- bb(1)
  rule seeB(1) :- pl()
end
";

#[test]
fn two_scopes_writing_one_bare_nullary_head_get_two_predicates() {
    // BACKED OUT (A): every assertion in the BARE arm fails — `zzP85Z7.a.pl` and
    // `zzP85Z7.b.pl` are both `None` (one uncitable global `pl` holds both clauses) and
    // `seeA` answers 1, from the OTHER namespace's clause. The PARENS arm is unmoved,
    // which is what makes the pair a measurement of the spelling.
    for (label, src, a, b) in [
        ("bare", INVERTED_PAIR, "zzP85Z7.a", "zzP85Z7.b"),
        ("parens", INVERTED_PAIR_PARENS, "zzP85Z7.pa", "zzP85Z7.pb"),
    ] {
        let mut kb = crate::common::load_kb_with(src);
        assert_eq!(
            clauses(&kb, &format!("{a}.pl")),
            Some(1),
            "{label}: `{a}.pl` must be a predicate of its OWN scope, holding its own clause"
        );
        assert_eq!(
            clauses(&kb, &format!("{b}.pl")),
            Some(1),
            "{label}: `{b}.pl` likewise — two predicates, not one shared name"
        );
        assert_eq!(
            answers(&mut kb, &format!("{a}.seeA(?x)")),
            0,
            "{label}: `{a}`'s own clause is FALSE, so its reader answers nothing — \
             pre-fix it answered 1, from `{b}`'s clause"
        );
        assert_eq!(
            answers(&mut kb, &format!("{b}.seeB(?x)")),
            1,
            "{label}: `{b}`'s own clause is TRUE, so its reader answers — the control \
             that says the goal machinery works at all"
        );
    }
}

/// THE OTHER HALF OF §"A rule-introduced functor is scoped where it is written": two
/// scopes that CAN see each other may not both introduce one name (WI-20260822-845G7).
/// The bare spelling reached that refusal nowhere, because it introduced nothing to
/// collide.
#[test]
fn two_scopes_that_see_each_other_are_refused_in_both_spellings() {
    // BACKED OUT (A): the BARE arm loads clean — no head is collected, so no collision
    // exists to report — while the PARENS arm is refused exactly as it is here.
    for (label, head) in [("bare", "shared_pl"), ("parens", "shared_pl()")] {
        let src = format!(
            "namespace zzP85Z7.outer{label}\n  fact bo(1)\n  rule {head} :- bo(999)\n  \
             namespace nsx\n    fact bn(1)\n    rule {head} :- bn(1)\n    \
             rule inner(1) :- {head}\n  end\nend\n"
        );
        let errs = crate::common::try_load_kb_with(&src)
            .err()
            .unwrap_or_else(|| {
                panic!(
                    "{label}: two mutually-visible scopes introducing one nullary name must \
                     be refused; the fixture loaded clean"
                )
            });
        crate::common::assert_refused_naming(
            &errs,
            &["shared_pl", "introduces that name at 2 scopes"],
            "the 845G7 collision must name the head and the count",
        );
    }
}

/// THE `ALSO TO SETTLE` HALF OF THE TICKET — is the minted symbol reached AT LOAD, or
/// is the clause still on the bare intern? A minted-but-unreached symbol would answer
/// `Some(0)` here while the goal still answered from somewhere else, so the count and
/// the answer are asserted together.
///
/// ITS SECOND ASSERTION ONLY STARTED MEASURING AT WI-20260901-719FJ, and that is worth
/// saying because the row was green the whole time: the pattern `zzP85Z7.idx.pl` is
/// itself a DOTTED PAREN-LESS citation, so until 719FJ it lowered to a `field_access`
/// chain and came back as a RESIDUAL — which `answers` was counting (see its doc, and
/// the measurement that says the count stayed 1 with both clause bodies false). The
/// count assertion was always real; "and the goal reaches them" was not.
#[test]
fn a_bare_nullary_clause_is_indexed_under_the_scoped_symbol() {
    // BACKED OUT (A): `zzP85Z7.idx.pl` is `None` and the qualified goal panics in
    // `query_pattern_term`'s resolve — there is no such symbol to name.
    let mut kb = crate::common::load_kb_with(
        "namespace zzP85Z7.idx\n  fact bi(1)\n  rule pl :- bi(1)\n  rule pl :- bi(9)\nend\n",
    );
    assert_eq!(
        clauses(&kb, "zzP85Z7.idx.pl"),
        Some(2),
        "BOTH clauses of the one predicate index under the scoped symbol"
    );
    assert_eq!(
        answers(&mut kb, "zzP85Z7.idx.pl"),
        1,
        "and the goal reaches them: `bi(1)` holds, `bi(9)` does not"
    );
}

/// THE EQUATION SIDE, AND WI-20260902-CZJ2N MOVED IT. This row asserted the opposite
/// when P85Z7 shipped: §5.3 read a `[simp]` head as an APPLICATION that a bare name
/// could not be, so `rule tau <=> …` fired NOTHING and `Bare.drive` answered the
/// operation's own body, `1`. CZJ2N makes the two spellings ONE TERM
/// (`KnowledgeBase::nullary_canon`), so the bare law defines exactly as the
/// parenthesised one does and BOTH drivers answer 7. §5.3's trap "a nullary head must
/// carry its parentheses" is deleted with the old verdict.
///
/// STILL A PAIR, and that is what it is for: the claim is that the spellings AGREE.
/// BACKED OUT (restore the `is_constructor_symbol` gate in `nullary_canon`, or drop
/// `simp_rewrite::stored_eq_operand_functor`'s `Term::Ref` arm), `Bare.drive` returns
/// to 1 while `Paren.drive` stays 7 — which is what says the axis is the head SPELLING.
///
/// WI-881 measured the CALL-SITE twin of this on `Float.tau` (see
/// `wi884_sibling_backing_test`): a `[simp]` law matched `minValue()` and not the
/// `var_ref` a bare name lowers to. That half is NOT closed here — see
/// `wi881_float_arithmetic_test::the_constants_answer_in_both_nullary_call_forms` for
/// where the call-site reading lives.
#[test]
fn a_bare_equation_subject_defines_exactly_like_its_parenthesised_twin() {
    const EQN: &str = r#"
namespace zzP85Z7.eqn
  sort Bare
    import anthill.prelude.Int64
    operation tau() -> Int64 = 1
    -- the BARE subject: since WI-20260902-CZJ2N, the same redex the parens spell
    rule tau <=> 7 [simp]
    operation drive(n: Int64) -> Int64 = tau()
  end

  sort Paren
    import anthill.prelude.Int64
    operation tau() -> Int64 = 1
    -- the APPLICATION: the spelling that defines
    rule tau() <=> 7 [simp]
    operation drive(n: Int64) -> Int64 = tau()
  end
end
"#;
    let mut interp = crate::common::interp_for(EQN);
    for (path, want, why) in [
        (
            "zzP85Z7.eqn.Bare.drive",
            7,
            "a bare equation subject IS the application, so its law inlines before dispatch",
        ),
        (
            "zzP85Z7.eqn.Paren.drive",
            7,
            "the parenthesised law IS a redex, and `[simp]` inlines it before dispatch",
        ),
    ] {
        match interp.call(path, &[Value::Int(0)]) {
            Ok(Value::Int(n)) if n == want => {}
            other => panic!("{path} must answer {want}: {why}; got {other:?}"),
        }
    }
}

/// AXIS C, WITHDRAWN BY WI-20260902-CZJ2N — a bare equation subject MINTS, exactly as
/// the parenthesised one does, and this row now measures that they AGREE.
///
/// WHAT IT ASSERTED, and why it was right at the time: P85Z7 gated the mint on
/// `RuleIntroduction::Predicate`, so `rule tauFresh <=> 7 [simp]` left its subject
/// outside the symbol table and `rule reader(1) :- tauFresh` was REFUSED ("`tauFresh`
/// names nothing … can NEVER match", WI-1034's body-goal refusal). Minting it instead
/// made the citation resolve — to an `EquationFunctor` with no clauses — and the
/// program then loaded clean and answered nothing, in silence. Under the reading of the
/// day that was the right trade: the bare law fired nothing, so a name it introduced
/// could never be satisfied.
///
/// WHY THE TRADE IS GONE. CZJ2N makes the two head spellings ONE TERM, so the bare law
/// DEFINES. Keeping the guard would then be a new spelling-dependent rule — refusing at
/// arity 0 only, on the equation path only — and refusing at every arity would change
/// proposal 061: an equation-defined name is a spec'd feature (§5.3 l.2022 names
/// `operation` as "the declaration of an equation-defined name"), and
/// `LoadError::UnreducedEquationFunctor` (WI-898) is its own loud channel for a
/// citation the rewriter left standing.
///
/// SO THIS IS A PAIR OVER TWO POSITIONS, and the absolute values are what make it more
/// than "they agree": an OP-BODY citation answers **7** (the law inlines before
/// dispatch) and a RULE-BODY goal answers **0** (an equation's clauses index under the
/// CONNECTIVE, so its subject owns none — WI-898).
///
/// WHETHER THAT 0 SHOULD BE LOUD is the same question at every arity, and it is FILED
/// rather than answered here (WI-20260902, "a rule-body citation of an equation functor
/// answers nothing in silence"). It is filed rather than merely noted because deleting
/// the guard REMOVES a loud case: the bare spelling used to reach WI-1034's "names
/// nothing … can NEVER match", and now neither spelling does. One rule at every arity is
/// the right direction — the guard's premise, that a bare law fires nothing, is exactly
/// what this ticket deletes — but the gap it was accidentally covering is now
/// unmitigated. The parenthesised spelling was already silent, which is what says the
/// two are one question.
///
/// BACKED OUT (restore `if introduced_by == RuleIntroduction::Predicate` on
/// `head_subject_name`'s `Term::Ident` arm): the `bare` arm's LOAD is refused, so both
/// of its rows fail while the `parens` arm passes — which is what says the axis is the
/// spelling and not the equation path.
#[test]
fn a_bare_equation_subject_mints_exactly_like_its_parenthesised_twin() {
    for (label, head) in [("bare", "tauFresh"), ("parens", "tauFresh()")] {
        let src = format!(
            "namespace zzP85Z7.eqmint{label}\n  import anthill.prelude.Int64\n  \
             rule {head} <=> 7 [simp]\n  rule reader(1) :- tauFresh\n  \
             operation drive(n: Int64) -> Int64 = tauFresh()\nend\n"
        );
        let mut interp = crate::common::interp_for(&src);
        match interp.call(&format!("zzP85Z7.eqmint{label}.drive"), &[Value::Int(0)]) {
            Ok(Value::Int(7)) => {}
            other => panic!(
                "{label}: the op-body citation must inline the law and answer 7; got {other:?}"
            ),
        }
        let mut kb = crate::common::load_kb_with(&src);
        assert_eq!(
            answers(&mut kb, &format!("zzP85Z7.eqmint{label}.reader(?x)")),
            0,
            "{label}: an equation's clauses index under the connective, so its subject \
             answers no rule-body goal (WI-898)"
        );
    }

    // CONTROL — the SAME bare text on the PREDICATE path. It introduces AND answers,
    // which is what says the 0 above is about the equation reading and not about the
    // bare spelling failing to mint at all.
    let mut kb = crate::common::load_kb_with(
        "namespace zzP85Z7.predfresh\n  rule tauFresh :- true\n  \
         rule reader(1) :- tauFresh\nend\n",
    );
    assert_eq!(
        answers(&mut kb, "zzP85Z7.predfresh.reader(?x)"),
        1,
        "the predicate spelling of the same bare head introduces and answers"
    );
}

/// WI-1075's refusal, reached by BOTH nullary spellings (axis B). A marked absolute head
/// that names nothing must not fall to the bare intern and store a clause under a symbol
/// nothing can cite; the paren-less spelling escaped it for the same reason it escaped
/// scoping — it is a `Term::Ident`, not a zero-argument `Term::Fn`.
#[test]
fn a_marked_absolute_nullary_head_that_names_nothing_is_refused() {
    // BACKED OUT (B): the BARE arm loads clean — this is the row's whole subject. The
    // PARENS arm and the RESOLVABLE arm below both pass either way, which is what makes
    // them controls rather than a second measurement of the same thing.
    for (label, head) in [("bare", "..nosuchp85z7"), ("parens", "..nosuchp85z7()")] {
        let errs = crate::common::try_load_kb_with(&format!(
            "namespace zzP85Z7.abs{label}\n  fact b(1)\n  rule {head} :- b(1)\nend\n"
        ))
        .err()
        .unwrap_or_else(|| {
            panic!("{label}: a marked head naming nothing must be refused, not bare-interned")
        });
        crate::common::assert_refused_naming(
            &errs,
            &["..nosuchp85z7"],
            "the refusal must name the path the author wrote",
        );
    }

    // THE CONTROL — the SAME marked spelling, RESOLVABLE. It must keep landing its
    // clause on the top-level predicate in both spellings; the refusal is about naming
    // nothing, never about the marker.
    for (label, head) in [("bare", "..tgtp85z7"), ("parens", "..tgtp85z7()")] {
        let kb = crate::common::load_kb_with(&format!(
            "fact b(1)\nrule tgtp85z7() :- b(1)\nnamespace zzP85Z7.ok{label}\n  \
             rule {head} :- b(1)\nend\n"
        ));
        assert_eq!(
            clauses(&kb, "tgtp85z7"),
            Some(2),
            "{label}: a resolvable marked head joins the predicate it names"
        );
    }
}

/// AXIS D — THE VERDICT'S EXPLANATION MUST READ THE HEAD THE WAY THE VERDICT DID.
/// `bodyless_declares_nothing_detail` re-walks the head to say WHY a body-less rule
/// declares nothing, and it destructured only `Term::Fn` — so the nullary reading landed
/// in the verdict and not in its explanation, and the two spellings of ONE head got two
/// different sentences about one refusal. Found by `/code-review` on this ticket's own
/// diff, which is the point: the fix removed the split from the behaviour and left it in
/// the message.
///
/// `..nosuchxyz` IS THE ONE PAREN-LESS SPELLING WHOSE NAME CONTAINS A DOT — a
/// multi-segment `nsx.tgt` folds into a minted `field_access` chain and gets the
/// desugaring sentence instead (WI-20260901-719FJ) — so it is the only fixture that can
/// reach the qualified arm without parentheses. The rule is refused twice here (axis B's
/// unresolved-name refusal fires first); the assertion reads the 061 sentence out of the
/// set rather than requiring it to be alone.
///
/// BACKED OUT (narrow that walk back to `Term::Fn { functor, .. }`): THIS ROW FAILS on
/// its BARE arm. Its PARENS arm and its CONTROL both pass either way — the control is
/// what says the fallthrough sentence still has a shape that earns it.
#[test]
fn a_body_less_qualified_heads_refusal_reads_alike_in_both_spellings() {
    for (label, head) in [("bare", "..nosuchxyz"), ("parens", "..nosuchxyz()")] {
        let errs = crate::common::try_load_kb_with(&format!(
            "namespace zzP85Z7.qhd{label}\n  rule {head}\nend\n"
        ))
        .err()
        .unwrap_or_else(|| panic!("{label}: a body-less qualified head declares nothing"));
        assert!(
            errs.iter().any(|e| e.contains("is a QUALIFIED name")),
            "{label}: the refusal must EXPLAIN itself by the qualified spelling, the same \
             way for both spellings of one head; got {errs:#?}"
        );
    }

    // THE CONTROL — the shape that still earns "not a functor application": a bare
    // VARIABLE head, which names nothing at any arity. Without it the row above could be
    // passed by deleting the fallthrough sentence outright.
    let errs = crate::common::try_load_kb_with("namespace zzP85Z7.varhd\n  rule ?x\nend\n")
        .err()
        .expect("a bare variable head declares nothing");
    assert!(
        errs.iter().any(|e| e.contains("not a functor application")),
        "a variable head really is not an application, and must keep saying so: {errs:#?}"
    );
}

/// A FACT HEAD IS UNSCOPED AT EVERY ARITY (§6.1), so the two nullary spellings must
/// agree with EACH OTHER — which is the answer to the ticket's "does `fact holds` follow
/// the rule head". It does not: it follows the FACT rule, and that rule's own defect
/// (two scopes' fact heads sharing one uncitable name) is WI-20260821-RDGQC's, whole,
/// for every arity rather than newly for this one.
///
/// GREEN BEFORE AND AFTER. Its job is to say the fact side was not silently half-moved:
/// were `fact_head_subject_name` given the `Term::Ident` arm too, the two counts here
/// would part.
#[test]
fn a_fact_head_is_unscoped_in_both_spellings() {
    for (label, head) in [("bare", "holdsp85z7"), ("parens", "holdsp85z7()")] {
        let kb = crate::common::load_kb_with(&format!(
            "namespace zzP85Z7.fct{label}\n  fact {head}\nend\n"
        ));
        assert_eq!(
            clauses(&kb, &format!("zzP85Z7.fct{label}.holdsp85z7")),
            None,
            "{label}: a fact head mints no scoped symbol — §6.1, and RDGQC owns it"
        );
    }
}
