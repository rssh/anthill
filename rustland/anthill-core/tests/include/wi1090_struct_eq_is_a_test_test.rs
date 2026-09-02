//! WI-1090 — `===` IS THE STRUCTURAL IDENTITY TEST, ON BOTH SIDES OF THE LOADER.
//! `pratt::is_equation_functor` named three connectives (`eq` / `unify` / `struct_eq`)
//! where the KB-side owner (`KnowledgeBase::is_equality_connective_functor`) has always
//! cached two, so a `===` rule head was a defining equation to the parse layer and an
//! ordinary clause on a resolver builtin to everything downstream.
//!
//! THE DECISION, and it is the spec's, not a new one. §"Equality: test vs. bind,
//! structural vs. semantic" puts `===` in the TEST column beside `=`, with `<=>` alone
//! in the bind column; §"`===` — the structural identity *test*" makes it a resolver
//! builtin that is total, carrier-agnostic and never dispatches, and names `<=>` as
//! "the connective of equational rule heads". So the parse side moves: `EQUATION_FUNCTORS`
//! is `eq` + `unify`, and a bodyless `===` head — which now means nothing at all — is
//! REFUSED rather than loaded into silence.
//!
//! WHAT WAS SILENT, measured on the pre-fix loader and each pinned below:
//!
//!   1. `[simp]` could never fire. `simp_equation_rids` collects the `eq` and `unify`
//!      buckets; a `===` clause is in neither, so the rewriter never saw it.
//!   2. The subject was stamped `SymbolKind::EquationFunctor` with ZERO clauses under
//!      it, so the only diagnostic the author ever saw came from a CITATION and said
//!      "defined by equations … no defining equation for it can be found" — about an
//!      equation written three lines up.
//!   3. The clause was filed under `anthill.kernel.struct_eq`, behind a resolver
//!      builtin that answers first.
//!
//! AND ONE CLAIM THE TICKET MADE THAT IS FALSE, corrected here rather than left
//! standing: WI-1090's text said the un-unindexed law "drives automatic SLD rewriting"
//! and that `f(?a, ?b) === f(?b, ?a)` would loop. MEASURED, on a ground goal the law
//! makes true and the builtin makes false: 0 solutions WITH the law and 0 WITHOUT it.
//! The builtin decides before any clause is consulted (WI-899's stated behaviour), so
//! the clause was inert, not dangerous. Consequence 3 is a wasted clause, nothing more.
//!
//! THE CONTROLS, two of them, because this landed in two cuts and the second cut has to
//! be defended against the FIRST as well as against the original.
//!
//! * BACK OUT THE WHOLE TICKET — `STRUCT_EQ_FUNCTOR` back into
//!   `pratt::EQUATION_FUNCTORS`, and the two `NonDefiningConnectiveHead` pushes
//!   (named `StructEqDefiningHead` until WI-888 widened the variant to `=` as well)
//!   (`Loader::load_rule`, `Loader::load_fact`) disabled. FOUR fail, all of them rows
//!   about the refusal or the absent stamp:
//!   `a_bodyless_struct_eq_head_is_refused_and_names_the_substitute`,
//!   `a_struct_eq_subject_is_not_stamped_an_equation_functor`,
//!   `every_spelling_of_a_bodyless_struct_eq_head_is_refused`,
//!   `a_struct_eq_head_with_no_subject_is_refused_without_naming_one`.
//! * BACK OUT ONLY THE SPLIT — narrow list kept, `collect_rule_tvar_names` asking
//!   `parse_equation_lhs` again, which is the first cut review rejected. TWO fail:
//!   `a_bodied_struct_eq_head_keeps_its_type_var_introducer` (the regression) and
//!   `every_spelling_of_a_bodyless_struct_eq_head_is_refused` (its folded-guard row,
//!   whose bracket the un-split reader also drops, so the rule dies of the WI-839
//!   sweep before the refusal is reached).
//!
//! `a_bodied_struct_eq_head_keeps_its_type_var_introducer` passes against the ORIGINAL
//! loader and fails only against the first cut, which is exactly its job: it guards a
//! regression this ticket introduced and then repaired, not the ticket's own subject.
//!
//! Three pass in both runs, on purpose and marked at their sites: the goal state
//! (`the_same_definition_spelled_with_the_connective_works`), the limit
//! (`a_bodied_law_about_struct_eq_still_loads`), and the ticket's correction
//! (`a_clause_on_the_struct_eq_builtin_never_decides_a_goal`).
//!
//! The parse/KB agreement itself is pinned separately, by the unit tests in
//! `load::wi1090_connective_agreement_tests` (both halves are crate-private): the same
//! back-out fails two of those three.

use anthill_core::kb::KnowledgeBase;

fn load_errors(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default()
}

fn clauses_under(kb: &mut KnowledgeBase, qn: &str) -> usize {
    let sym = kb
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("`{qn}` must be a defined symbol"));
    kb.rules_by_functor(sym).len()
}

/// THE REFUSAL, and what it has to say. A `[simp]`-tagged `===` "definition" is the
/// exact source the three silences came from, so it is the source the message must
/// answer: it names the subject the author was defining, says `===` compares rather
/// than defines, and gives the substitute. Asserting the CONTENT because the whole
/// point is that the pre-fix diagnostic — which existed, at the citation — pointed the
/// author at the wrong thing.
#[test]
fn a_bodyless_struct_eq_head_is_refused_and_names_the_substitute() {
    const SRC: &str = r#"
namespace wi1090.refused
  sort S
    import anthill.prelude.{Int64}
    rule { g1090(?x) === ?x [simp] }
    operation drive(n: Int64) -> Int64 = g1090(n)
  end
end
"#;
    let errs = load_errors(SRC);
    let joined = errs.join("\n");
    assert!(
        joined.contains("`===` is the structural identity TEST"),
        "the rule itself must be refused, at the rule — every later site is silent or \
         mis-reports. Got: {joined}",
    );
    assert!(
        joined.contains("g1090") && joined.contains("Write `<=>`"),
        "the message must name the subject and the connective that defines it. \
         Got: {joined}",
    );
    assert!(
        !joined.contains("defined by equations"),
        "and it must displace the citation's old misdiagnosis, which blamed a missing \
         equation for a file that contains one. Got: {joined}",
    );
}

/// SILENCE 2, at the symbol. The subject of a `===` head is no longer an equation
/// functor — it is nothing at all, which is the truth: no clause is indexed under it.
/// Driven on a fixture WITHOUT a citation, so the claim is about the stamp and not
/// about a message.
///
/// The `<=>` row beside it is the positive: the same subject, one connective apart, IS
/// stamped and IS reachable. Without it this test would pass against a pass that
/// stopped stamping anything.
#[test]
fn a_struct_eq_subject_is_not_stamped_an_equation_functor() {
    const STRUCT_EQ: &str = r#"
namespace wi1090.stamp
  sort S
    import anthill.prelude.{Int64}
    rule { g1090(?x) === ?x }
  end
end
"#;
    const UNIFY: &str = r#"
namespace wi1090.stamp
  sort S
    import anthill.prelude.{Int64}
    rule { g1090(?x) <=> ?x }
  end
end
"#;
    let errs = load_errors(STRUCT_EQ);
    assert!(
        errs.iter()
            .any(|e| e.contains("`===` is the structural identity TEST")),
        "an UNTAGGED `===` head is refused too — the tag was never what made it \
         meaningless. Got: {errs:?}",
    );

    let kb = crate::common::load_kb_with(UNIFY);
    let sym = kb
        .try_resolve_symbol("wi1090.stamp.S.g1090")
        .expect("the `<=>` twin DOES introduce its subject — the positive this absence \
                 is measured against");
    assert_eq!(
        kb.kind_of(sym),
        Some(anthill_core::intern::SymbolKind::EquationFunctor),
        "`<=>` is the connective of equational rule heads, so its subject is an \
         equation functor — the stamp `===` was wrongly given",
    );
}

/// SILENCES 1 AND 3, driven end to end: the definition the author was reaching for
/// RUNS when spelled with the connective the spec names. `drive(7)` must compute, which
/// no `===` spelling of the same rule can do at any point in the pipeline.
///
/// EITHER WAY by design — this row is the goal state, not the fix. It is here so the
/// refusal above cannot be read as "this shape is unsupported": it is supported, one
/// character apart, and the message says so.
#[test]
fn the_same_definition_spelled_with_the_connective_works() {
    const SRC: &str = r#"
namespace wi1090.works
  sort S
    import anthill.prelude.{Int64}
    rule { g1090(?x) <=> ?x [simp] }
    operation drive(n: Int64) -> Int64 = g1090(n)
    rule out1090(?v) :- ?v <=> drive(7)
  end
end
"#;
    let mut kb = crate::common::load_kb_with(SRC);
    use anthill_core::kb::term::Literal;
    use anthill_core::kb::term_view::{TermView, ViewHead};
    let answers = crate::common::query_unary(&mut kb, "wi1090.works.S.out1090");
    let values: Vec<ViewHead> = answers.iter().map(|(v, _)| v.head(&kb)).collect();
    assert!(
        matches!(values.as_slice(), [ViewHead::Const(Literal::Int(7))]),
        "the `[simp]` equation rewrites `g1090(7)` to `7` before dispatch, so the \
         operation computes; got {values:?}",
    );
}

/// THE LIMIT OF THE REFUSAL, in both directions it could have overreached.
///
/// * A BODIED law about `===` stays legal — it is not an equation at all (§8.3) but an
///   ordinary clause on the connective, which is WI-899's subject. `totalfloat.anthill`
///   writes exactly this (`rule eq(?a, ?b) :- ?a === ?b`), so widening the refusal to
///   every `===` head would refuse the standard library.
/// * A `===` in a BODY GOAL is the operator's whole purpose and must not be touched.
///
/// EITHER WAY by design: neither shape is a bodyless minted `===` head, so
/// `parse_equation_lhs` and the refusal both decline it with or without the fix. The
/// row exists because a refusal is only as good as what it leaves alone, and this one
/// is keyed on two conditions that a careless widening would drop.
#[test]
fn a_bodied_law_about_struct_eq_still_loads() {
    const SRC: &str = r#"
namespace wi1090.bodied
  sort S
    import anthill.prelude.{Int64, Bool}
    entity f1090(a: Int64)
    rule same1090(?x) :- f1090(a: ?x) === f1090(a: 1)
    rule eq(?a, ?b) :- ?a === ?b
  end
end
"#;
    let errs = load_errors(SRC);
    assert!(
        errs.is_empty(),
        "a bodied rule is not an equation (§8.3), and a body-goal `===` is the \
         operator doing its job — `totalfloat.anthill` writes the second line. \
         Got: {errs:?}",
    );
}

/// THE OTHER SPELLINGS OF "BODYLESS", both found by review after the rule-with-no-`:-`
/// case shipped alone. A refusal that covers one spelling of its own condition is a
/// refusal with a hole, and each of these is one keyword or one guard away from the
/// row above.
///
/// * `fact lhs === rhs` — §6.1 defines a fact as a bodyless rule. MEASURED loading
///   clean through the built CLI while the `rule` spelling was refused, filing its
///   clause under the kernel connective exactly as before the fix.
/// * a rule whose ONLY body goal is a folded `Spec[T]` bound — the fold leaves no body
///   goals, which is why the check reads `body_nodes` (post-fold) and not the parse
///   IR's `body.is_some()`. The spec calls such a rule an equation for the same reason.
#[test]
fn every_spelling_of_a_bodyless_struct_eq_head_is_refused() {
    const AS_A_FACT: &str = r#"
namespace wi1090.asfact
  sort S
    import anthill.prelude.{Int64}
    entity boxed1090(v: Int64)
    fact boxed1090(v: 1) === boxed1090(v: 1)
  end
end
"#;
    const ONLY_A_FOLDED_GUARD: &str = r#"
namespace wi1090.folded
  import anthill.prelude.{Int64, Eq}
  rule g1090[t](?x) === ?x :- Eq[t]
end
"#;
    for (spelling, src) in [("fact", AS_A_FACT), ("folded guard only", ONLY_A_FOLDED_GUARD)] {
        let errs = load_errors(src);
        assert!(
            errs.iter()
                .any(|e| e.contains("`===` is the structural identity TEST")),
            "{spelling}: this is a bodyless `===` head under another name and must get \
             the same refusal. Got: {errs:?}",
        );
    }
}

/// THE `[T]` INTRODUCER STILL RIDES ON A `===` HEAD'S LHS — the regression this
/// ticket's first cut introduced, found by review. Narrowing the EQUATION set alone
/// also narrowed the reader that asks WHERE A HEAD'S BRACKET SITS, which is a question
/// about the head's SHAPE and has the same answer for every connective in the family.
///
/// MEASURED on that cut: `g[t](?x) === ?x :- Eq[t], p(?x)` drew WI-839's "call-site
/// type arguments `g[…](…)` are not supported here" — the bracket read off the
/// ARGUMENT, found nowhere, left unconsumed — while its one-character-apart `<=>` twin
/// loaded clean. That is WI-619's own defect for a spelling WI-619 predates, and the
/// repair is the split: `parse_connective_head` (the family, the shape) under
/// `parse_equation_lhs` (the defining subset, the meaning).
///
/// The body goal `p1090(?x)` is load-bearing: without it the folded guard leaves no
/// body goals and the rule is refused by the row above, which would hide this one.
#[test]
fn a_bodied_struct_eq_head_keeps_its_type_var_introducer() {
    let src = |connective: &str| {
        format!(
            r#"
namespace wi1090.tvar
  import anthill.prelude.{{Int64, Eq}}
  rule p1090(?x) :- ?x === 1
  rule g1090[t](?x) {connective} ?x :- Eq[t], p1090(?x)
end
"#
        )
    };
    for connective in ["===", "<=>"] {
        let errs = load_errors(&src(connective));
        assert!(
            errs.is_empty(),
            "`{connective}`: a connective head's `[t]` rides on its LHS operand, so the \
             `:- Eq[t]` guard folds and the bracket is consumed. Both spellings, because \
             the two must not differ on a SHAPE question. Got: {errs:?}",
        );
    }
}

/// A LEFT OPERAND THAT NAMES NOTHING still gets the refusal, and the message must not
/// invent a subject for it. Found by review: the first cut substituted the CONNECTIVE
/// into the subject slot and rendered "…and `===` is left naming no callable. Write
/// `<=>` to define `===` by equations" — a remedy instructing the author to define the
/// operator they had just used.
#[test]
fn a_struct_eq_head_with_no_subject_is_refused_without_naming_one() {
    const SRC: &str = r#"
namespace wi1090.nosubject
  sort S
    rule ?x === ?x
  end
end
"#;
    let joined = load_errors(SRC).join("\n");
    assert!(
        joined.contains("`===` is the structural identity TEST"),
        "a variable LHS names nothing to define, which makes the rule MORE hopeless, \
         not less. Got: {joined}",
    );
    assert!(
        !joined.contains("define `===` by equations"),
        "the remedy must not tell the author to define the operator. Got: {joined}",
    );
}

/// THE MEASUREMENT THAT CORRECTS THE TICKET. WI-1090's text claimed an un-unindexed
/// `===` law "drives automatic SLD rewriting" and would loop. It does not: the goal is
/// decided by the resolver builtin before any clause is consulted, so the clause was
/// inert. Driven on the shape that would show it — a GROUND goal the law makes true and
/// structural identity makes false.
///
/// Written against the WRITTEN-CALL spelling (`struct_eq(…)`, a predicate head), which
/// the WI-1090 refusal deliberately does not touch: that is WI-899's clause-on-a-
/// builtin-backed-name, and keeping it loadable is what lets this file measure the
/// claim at all. EITHER WAY, and that is the finding — the clause never mattered.
#[test]
fn a_clause_on_the_struct_eq_builtin_never_decides_a_goal() {
    const WITH_LAW: &str = r#"
namespace wi1090.inert
  sort S
    import anthill.prelude.{Int64, Bool}
    -- WI-909: `struct_eq` took an address and left the implicit tier, and a rule head is
    -- RESOLVED, not declared (WI-896) — so without this import the head below stops
    -- reaching the kernel primitive and introduces a local `wi1090.inert.S.struct_eq`
    -- instead. That would leave the fixture unable to construct this file's SUBJECT (a
    -- clause filed ON the builtin) while every assertion still passed.
    import anthill.kernel.{struct_eq}
    entity f1090(a: Int64, b: Int64)
    rule struct_eq(f1090(a: ?x, b: ?y), f1090(a: ?y, b: ?x)) :- true
    rule drive1090(?v) :- f1090(a: 1, b: 2) === f1090(a: 2, b: 1), ?v <=> 1
  end
end
"#;
    const WITHOUT_LAW: &str = r#"
namespace wi1090.inert
  sort S
    import anthill.prelude.{Int64, Bool}
    entity f1090(a: Int64, b: Int64)
    rule drive1090(?v) :- f1090(a: 1, b: 2) === f1090(a: 2, b: 1), ?v <=> 1
  end
end
"#;
    let mut with_law = crate::common::load_kb_with(WITH_LAW);
    assert_eq!(
        clauses_under(&mut with_law, "anthill.kernel.struct_eq"),
        1,
        "the clause IS filed under the kernel connective — that much of the ticket \
         holds, and is what made the claim plausible",
    );

    let with = crate::common::query_unary(&mut with_law, "wi1090.inert.S.drive1090").len();
    let mut without_law = crate::common::load_kb_with(WITHOUT_LAW);
    let without = crate::common::query_unary(&mut without_law, "wi1090.inert.S.drive1090").len();
    assert_eq!(
        (with, without),
        (0, 0),
        "the symmetry law would make this goal true if any clause of `===` were \
         consulted; the builtin answers first, so the clause decides nothing — the \
         ticket's 'drives automatic SLD rewriting / would loop' is FALSE",
    );
}
