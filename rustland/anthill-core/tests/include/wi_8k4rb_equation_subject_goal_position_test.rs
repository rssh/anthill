//! WI-20260902-8K4RB — AN EQUATION SUBJECT WRITTEN AS A RULE-BODY GOAL IS REFUSED.
//!
//! `rule reader(1) :- tauX` beside `rule tauX <=> 7 [simp]` used to LOAD CLEAN and
//! answer nothing, at every arity and in both nullary spellings. The name RESOLVES —
//! the mint stamps it `SymbolKind::EquationFunctor` — so WI-1034's "names nothing …
//! can NEVER match" declined it, and the goal-reading pass fell through its `op_record`
//! gate because an equation declares no operation. An equation's clauses are indexed
//! under the `eq`/`unify` CONNECTIVE (WI-898, spec §5.3), so the subject owns no clause
//! and the goal matched nothing: the empty relation, indistinguishable from facts that
//! do not hold.
//!
//! IT WAS NOT MERELY EMPTY. MEASURED on the parent commit, one file, three rules:
//! `:- tauX` answered 0, `:- tauX()` answered 0, and **`:- not(tauX)` answered ONE** —
//! negation-as-failure laundering an unsatisfiable goal into a confident `true`. That is
//! the same class CZJ2N removed for `:- flag`, and it is why this is refused rather than
//! tolerated: a term with NO GOAL READING has no "the sibling branch may answer" defence,
//! which is the distinction `check_goal_atom_reading`'s own doc draws against
//! WI-863/WI-1034's narrower descent.
//!
//! WHY CZJ2N IS WHERE THIS BECAME UNMITIGATED. Before it, `head_subject_name` gated the
//! mint on `RuleIntroduction::Predicate`, so a BARE undeclared equation subject stayed
//! outside the symbol table and its citation hit WI-1034's refusal — while the
//! PARENTHESISED spelling minted and was silent. CZJ2N deleted that guard (the two head
//! spellings are ONE TERM, so refusing at arity 0 only would be a new spelling-dependent
//! rule), which made the silence uniform and removed the one place a user was told.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! FOUR AXES, FOUR BACK-OUTS. Each is PRESENT-BUT-WRONG rather than deleted, and each
//! was applied and run over the WHOLE `wi_tests` binary — not a hand-picked
//! neighbourhood — so each list is EXHAUSTIVE over that population: every row not named
//! passed, anywhere in the suite.
//!
//! **A — THE ARM.** The `EquationSubjectInGoalPosition` arm inside
//! `check_goal_atom_reading`'s `op_record` `else` (typing.rs), neutralised by prefixing
//! its condition with `false &&`. The condition is ONE `&&` chain, so that disables the
//! whole arm and not merely its first leg. **EXACTLY 7 ROWS FAIL** of 4 036 run: the six
//! in this file that assert a refusal —
//! [`every_spelling_of_an_equation_subject_cited_as_a_goal_is_refused`] (all four arms
//! load clean and answer 0), [`a_negated_citation_is_refused`] (loads clean and answers
//! ONE — the wrong answer this ticket is really about),
//! [`a_citation_in_a_bare_or_branch_is_refused_too`],
//! [`neither_the_arity_nor_a_boolean_right_hand_side_makes_it_a_goal`] (both arms),
//! [`the_refusal_names_the_goal_position_not_a_failed_rewrite`], and
//! [`a_multi_head_rule_reports_one_goal_once`] (its EQUATION arm only — the constant arm
//! still passes, which is what says that row is not a second copy of the headline) —
//! plus, outside this file,
//! `wi_p85z7_paren_less_nullary_head_test::a_bare_equation_subject_mints_exactly_like_-
//! its_parenthesised_twin`, whose rule-body half this ticket flipped from "answers 0" to
//! "is refused".
//!
//! **B — THE GATE'S SECOND HALF.** Drop `&& !kb.cites_a_relation(f)`, leaving the kind
//! test alone — the OVER-WIDE gate, which is the mis-implementation worth ranking
//! against (a missing gate is axis A). **EXACTLY 1 ROW FAILS:**
//! [`a_predicate_clause_on_the_same_name_keeps_the_goal_legal`]. Every other row in this
//! file passes, so that row measures the gate and nothing else.
//!
//! **C — THE PER-GOAL DEDUP.** Delete the `errors.retain(…)` at the end of
//! `check_rule_body_goal_readings`. **EXACTLY 1 ROW FAILS:**
//! [`a_multi_head_rule_reports_one_goal_once`] — and BOTH its arms, the constant one
//! included, which is what says the duplication was the PASS's and not this ticket's.
//! Nothing else in the suite depended on the duplicate.
//!
//! **D — THE P85Z7 MINT GUARD, restored** (`Term::Ident(sym) if introduced_by ==
//! RuleIntroduction::Predicate => sym` in `head_subject_name`) — CZJ2N's withdrawn axis
//! C, re-run here because the flipped P85Z7 row's own back-out note claims it, and an
//! inherited claim is not a measurement. **EXACTLY 8 ROWS FAIL:** every row in this file
//! whose fixture writes a BARE equation head that must DEFINE — the six of axis A, plus
//! [`an_operation_body_citation_still_inlines_and_answers`], which axis A does NOT fell —
//! and the P85Z7 row. The two survivors are the two whose fixtures do not depend on a
//! bare head minting: [`a_predicate_clause_on_the_same_name_keeps_the_goal_legal`] (its
//! `Goal` kind comes from the predicate clause, not from the equation) and
//! [`a_declared_operation_carrying_equations_keeps_the_operation_diagnosis`] (its head is
//! parenthesised). That the op-body row is felled HERE and not by axis A is the two axes
//! working: D removes the DEFINITION, A removes only the goal-position refusal.
//!
//! **PASS EITHER WAY, BY DESIGN — the controls, and what each one ranks.**
//! [`an_operation_body_citation_still_inlines_and_answers`] is the pair the headline
//! needs: a fixture asserting only the refusal would pass with the VALUE-position
//! reading broken too, since both readings would then be "no answer". It has its own
//! namespace and its own subject, so it shares no fixture with the refused arms.
//! [`a_declared_operation_carrying_equations_keeps_the_operation_diagnosis`] ranks the
//! arm's POSITION: moved above the `op_record` gate it fails, because a declared
//! operation would then lose WI-583's more specific message. (It has no axis of its own
//! above because that move is not a back-out of anything shipped — it is the other place
//! the arm could have gone.)

use anthill_core::eval::Value;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// DEFINITE solutions only — `common::definite_unary`'s rule (WI-20260822-WZX6B): a
/// plain `.len()` counts a FLOUNDERED solution as an answer, and this file's subject is
/// a goal whose neighbours residualize (`?r = tauX()` comes back
/// `conditional / residual: eq(?_, 7)`), so a residual-counting helper would report
/// "it answers" for a rule that binds nothing.
fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

/// THE HEADLINE — the two HEAD spellings crossed with the two CITATION spellings, one
/// verdict. Four combinations because the ticket that made this uniform (CZJ2N) is
/// precisely about the two spellings being one term: a fix that refused only the
/// parenthesised citation, or only under a parenthesised head, would be the
/// spelling-dependent rule CZJ2N deleted, reintroduced one layer down.
///
/// Each arm is its OWN namespace, so the four are four programs and not one program with
/// four rules — otherwise a single refusal anywhere would satisfy all four assertions.
#[test]
fn every_spelling_of_an_equation_subject_cited_as_a_goal_is_refused() {
    for (hl, head) in [("bare", "tauX"), ("paren", "tauX()")] {
        for (cl, cite) in [("bare", "tauX"), ("paren", "tauX()")] {
            let src = format!(
                "namespace zz8K4RB.h{hl}c{cl}\n  import anthill.prelude.Int64\n  \
                 rule {head} <=> 7 [simp]\n  rule reader(1) :- {cite}\nend\n"
            );
            let errs = crate::common::try_load_kb_with(&src)
                .err()
                .unwrap_or_else(|| {
                    panic!(
                        "head={head} cite={cite}: an equation subject in a goal position must \
                     be refused, not loaded to answer the empty relation"
                    )
                });
            // THE GOAL, qualified — the spelling that locates the equations — and THE
            // DIAGNOSIS, the sentence that tells the author the POSITION is wrong rather
            // than the clause.
            let qualified = format!("zz8K4RB.h{hl}c{cl}.tauX");
            crate::common::assert_refused_naming(
                &errs,
                &[&qualified, "indexed under the `eq`/`unify` CONNECTIVE"],
                &format!("head={head} cite={cite}"),
            );
            // AND THE LOCATION, which is half the acceptance: the refusal must point at
            // the CITATION the author wrote, not at the equation that introduced the
            // name. Line 4 is `rule reader(1) :- …` in every arm and line 3 is the
            // equation, so the LINE is the discriminating part; the COLUMN moves with
            // the citation's spelling and is asserted only to be present, never pinned.
            // A `Located` renders `line:col:` through `Display` (the path is absent here
            // — these fixtures are unnamed sources), which is what `try_load_kb_with`
            // stringifies.
            assert!(
                errs.iter().any(|e| {
                    e.strip_prefix("4:")
                        .and_then(|rest| rest.split_once(':'))
                        .is_some_and(|(col, _)| col.parse::<u32>().is_ok())
                }),
                "head={head} cite={cite}: the refusal must name the CITATION's line:col \
                 (line 4), not the equation's (line 3); got:\n{}",
                errs.join("\n")
            );
        }
    }
}

/// THE GATE IS THE SUBJECT — not the arity, and not what the equation computes.
///
/// TWO AXES THE HEADLINE HOLDS FIXED, each of which a narrower fix would have got wrong.
/// **Arity**: the headline is nullary throughout, because that is the spelling CZJ2N
/// merged; an `n`-ary subject (`rule tauN(1) <=> 7 [simp]`) is the same defect and the
/// ticket says "at every arity", so it is driven rather than argued. **The right-hand
/// side's type**: `rule tauZ <=> true [simp]` is the shape an author most plausibly
/// writes on purpose — a boolean law meant as a condition — and it is exactly as
/// unmatchable, because the clause still indexes under the connective. A gate written on
/// the RETURN type (`Bool` reads as a goal, anything else does not — WI-583's rule for
/// OPERATIONS) would let that one through, and it is the one most likely to be written.
#[test]
fn neither_the_arity_nor_a_boolean_right_hand_side_makes_it_a_goal() {
    for (label, eqn, cite) in [
        ("arity1", "rule tauN(1) <=> 7 [simp]", "tauN(1)"),
        ("boolrhs", "rule tauZ <=> true [simp]", "tauZ"),
    ] {
        let errs = crate::common::try_load_kb_with(&format!(
            "namespace zz8K4RB.{label}\n  import anthill.prelude.{{Int64, Bool}}\n  \
             {eqn}\n  rule reader(1) :- {cite}\nend\n"
        ))
        .err()
        .unwrap_or_else(|| panic!("{label}: `{cite}` names an equation subject and cannot match"));
        crate::common::assert_refused_naming(
            &errs,
            &["indexed under the `eq`/`unify` CONNECTIVE"],
            label,
        );
    }
}

/// THE WRONG ANSWER — the row that makes this a defect rather than an ergonomic gap.
///
/// MEASURED on the parent commit, in one file: `:- tauX` answered 0 and `:- not(tauX)`
/// answered **1**. NAF resolves the inner goal to a complete-empty search and flips it to
/// a confident `true`, so the rule fired on a premise that cannot hold. `not` is the one
/// goal context WI-863 always descends into for exactly this reason.
#[test]
fn a_negated_citation_is_refused() {
    let errs = crate::common::try_load_kb_with(
        "namespace zz8K4RB.neg\n  import anthill.prelude.Int64\n  \
         rule tauX <=> 7 [simp]\n  rule reader(1) :- not(tauX)\nend\n",
    )
    .err()
    .expect("a negated equation-subject citation must be refused, not answered `true`");
    crate::common::assert_refused_naming(
        &errs,
        &[
            "zz8K4RB.neg.tauX",
            "indexed under the `eq`/`unify` CONNECTIVE",
        ],
        "the walk enters `not`, where the silence was a WRONG answer",
    );
}

/// THE DESCENT — refused inside a BARE `or` branch too, which is where this pass parts
/// company with WI-863/WI-1034's walk and the reason it had to be raised here.
///
/// That walk deliberately does NOT enter an un-negated `or` branch: a name it cannot find
/// might exist in another program or another load phase, and the sibling branch may answer
/// anyway, so refusing would reject a program that computes the right result
/// (`push_choice_test` names undefined branches on purpose). An equation subject has no
/// such defence — it is not ABSENT, it is present and unmatchable, in any program, in any
/// branch, under any binding — which is exactly the distinction
/// `check_goal_atom_reading`'s own doc draws for `:- base(1) | 42`.
///
/// The sibling branch is a fact that DOES answer, so the row is refused despite the rule
/// having a live way to succeed; that is what makes it a measurement of the descent and
/// not a second copy of the headline.
#[test]
fn a_citation_in_a_bare_or_branch_is_refused_too() {
    let errs = crate::common::try_load_kb_with(
        "namespace zz8K4RB.disj\n  import anthill.prelude.Int64\n  \
         fact base(1)\n  rule tauD <=> 7 [simp]\n  \
         rule reader(1) :- base(1) | tauD\nend\n",
    )
    .err()
    .expect(
        "an equation subject is unmatchable in EVERY branch, so the `or` tolerance \
         WI-863 grants an ABSENT name does not transfer to it",
    );
    crate::common::assert_refused_naming(
        &errs,
        &[
            "zz8K4RB.disj.tauD",
            "indexed under the `eq`/`unify` CONNECTIVE",
        ],
        "the goal-reading pass descends into every PROVED goal slot",
    );
}

/// THE NEIGHBOUR'S DOMAIN, unchanged — this arm must not STEAL a case that already had a
/// better diagnosis.
///
/// A name that is BOTH a declared `operation` and an equation subject has an op record, so
/// the arm is never reached and WI-583's `NonBoolOpInGoalPosition` answers instead: an
/// `Int64`-returning operation has no relational reading in goal position, which is a more
/// specific sentence than "its equations index under the connective" and names the return
/// sort. Passes either way against this change — it is a boundary assertion, and it fails
/// if the arm is moved ABOVE the `op_record` gate.
#[test]
fn a_declared_operation_carrying_equations_keeps_the_operation_diagnosis() {
    let errs = crate::common::try_load_kb_with(
        "namespace zz8K4RB.op\n  import anthill.prelude.Int64\n  \
         operation tauO() -> Int64\n  rule tauO() <=> 7 [simp]\n  \
         rule reader(1) :- tauO()\nend\n",
    )
    .err()
    .expect("a non-Bool operation in goal position is refused (WI-583)");
    let joined = errs.join(" | ");
    assert!(
        joined.contains("not `Bool`") || joined.contains("no relational reading"),
        "the OPERATION diagnosis must survive — it names the return sort, which this \
         ticket's message does not; got:\n{joined}"
    );
    assert!(
        !joined.contains("indexed under the `eq`/`unify` CONNECTIVE"),
        "this ticket's arm sits BELOW the `op_record` gate and must not preempt its \
         neighbour; got:\n{joined}"
    );
}

/// ONE GOAL IN THE TEXT REPORTS ONCE — WI-1034's rule for the sibling channel, which
/// this pass did not obey.
///
/// A `-:` multi-head rule desugars to one clause per conclusion SHARING THE BODY, so a
/// single bad goal reaches `check_rule_body_goal_readings` through N `RuleId`s. MEASURED
/// before the fix: the equation-subject refusal printed TWICE, and so did the constant
/// one — `rule banded: 42 -: gte(?d, 0), lte(?d, 9)` reported at `4:5` twice. That second
/// half is a PRE-EXISTING defect of this pass's older member, found by checking that the
/// new member obeyed the neighbouring channel's rule, and it is fixed with it: the dedup
/// is keyed at the caller, so all three variants this pass raises obey it.
///
/// BOTH ARMS, and the CONSTANT arm is the one that says the fix is the pass's and not
/// this ticket's: back out the dedup (axis C) and both fail, so neither arm is a
/// restatement of the other.
#[test]
fn a_multi_head_rule_reports_one_goal_once() {
    for (label, decl, goal, marker) in [
        (
            "equation",
            "rule tauH <=> 7 [simp]",
            "tauH",
            "is defined by EQUATIONS",
        ),
        (
            "constant",
            "fact anchorH(1)",
            "42",
            "in a rule-body GOAL position",
        ),
    ] {
        let errs = crate::common::try_load_kb_with(&format!(
            "namespace zz8K4RB.multi{label}\n  import anthill.prelude.Int64\n  \
             {decl}\n  rule banded:\n    {goal}\n    -: gte(?d, 0), lte(?d, 9)\nend\n"
        ))
        .err()
        .unwrap_or_else(|| panic!("{label}: the goal has no reading and must be refused"));
        assert_eq!(
            errs.join(" | ").matches(marker).count(),
            1,
            "{label}: one goal in the text, one refusal — the multi-head desugar must \
             not multiply it; got:\n{}",
            errs.join("\n")
        );
    }
}

/// THE PAIR — the VALUE-position reading must keep working, and must keep answering the
/// NUMBER, not merely loading.
///
/// This is what stops the headline from being satisfiable by breaking everything: if the
/// operation body stopped inlining, `drive` would answer nothing and the refusal above
/// would still hold, so the two rows together say the refusal is about the POSITION.
/// Both nullary head spellings, because CZJ2N is what made them one term.
#[test]
fn an_operation_body_citation_still_inlines_and_answers() {
    for (label, head) in [("bare", "tauV"), ("paren", "tauV()")] {
        let src = format!(
            "namespace zz8K4RB.val{label}\n  import anthill.prelude.Int64\n  \
             rule {head} <=> 7 [simp]\n  \
             operation drive(n: Int64) -> Int64 = tauV()\nend\n"
        );
        let mut interp = crate::common::interp_for(&src);
        match interp.call(&format!("zz8K4RB.val{label}.drive"), &[Value::Int(0)]) {
            Ok(Value::Int(7)) => {}
            other => panic!(
                "{label}: the op-body citation must inline the law and answer 7 — the \
                 goal-position refusal must not reach a rewrite site; got {other:?}"
            ),
        }
    }

    // THE REPAIR AS THE MESSAGE SPELLS IT, from ANOTHER namespace — qualified name,
    // parentheses written. The message names the goal qualified, so it must prescribe a
    // qualified repair: its first cut advised the SHORT name, which need not resolve at
    // the citing scope at all (found by `/code-review`). Driven here rather than argued,
    // because a refusal whose repair has not been run is how an author gets sent to a
    // second silent nothing.
    let mut interp = crate::common::interp_for(
        "namespace zz8K4RB.xinner\n  import anthill.prelude.Int64\n  \
         rule tauX <=> 7 [simp]\nend\n\
         namespace zz8K4RB.xouter\n  import anthill.prelude.Int64\n  \
         operation drive(n: Int64) -> Int64 = zz8K4RB.xinner.tauX()\nend\n",
    );
    match interp.call("zz8K4RB.xouter.drive", &[Value::Int(0)]) {
        Ok(Value::Int(7)) => {}
        other => panic!(
            "the repair the message prescribes — the QUALIFIED name with its parentheses, \
             in an operation body — must answer 7 from a foreign namespace; got {other:?}"
        ),
    }
}

/// THE CONTROL FOR THE GATE'S SECOND HALF, and the reason the gate asks
/// `cites_a_relation` rather than the kind alone.
///
/// One scope may write one name in BOTH head shapes, and then a predicate clause IS
/// indexed under it (`kb.symbols.define` merges kinds for a repeated name+scope, so the
/// symbol carries `Goal` AND `EquationFunctor`). The relational reading is then real and
/// the goal must keep answering.
///
/// BACKED OUT to `has_kind(EquationFunctor)` alone — the over-wide gate — THIS ROW FAILS
/// while every other row in the file still passes, which is what makes it a measurement
/// of the exact gate rather than a second copy of the headline. It passes either way
/// against the change as a whole, by design.
#[test]
fn a_predicate_clause_on_the_same_name_keeps_the_goal_legal() {
    let mut kb = crate::common::load_kb_with(
        "namespace zz8K4RB.both\n  import anthill.prelude.Int64\n  \
         rule tauB :- true\n  rule tauB <=> 7 [simp]\n  \
         rule reader(1) :- tauB\nend\n",
    );
    assert_eq!(
        answers(&mut kb, "zz8K4RB.both.reader(?x)"),
        1,
        "a name carrying a PREDICATE clause is a relation however many equations also \
         live on it (WI-898 `cites_a_relation`), so its goal must still answer"
    );
}

/// THE TICKET'S FIRST QUESTION, answered as an assertion: this is a SIBLING of
/// `UnreducedEquationFunctor`, not that error.
///
/// That one is the VALUE-position citation the rewriter left standing, and its census
/// branches send the author to tag the equation `[simp]` or to inspect the left-hand
/// patterns. The fixture here is `[simp]`-TAGGED with one defining clause, so that
/// census would reach its third branch — *"none of its 1 `[simp]` clause(s) fired here.
/// A clause fires only where its left-hand pattern matches STRUCTURALLY …"* — sending
/// the author to inspect a clause that is fine. The position admits no rewrite at all,
/// and the message has to say so.
#[test]
fn the_refusal_names_the_goal_position_not_a_failed_rewrite() {
    let errs = crate::common::try_load_kb_with(
        "namespace zz8K4RB.msg\n  import anthill.prelude.Int64\n  \
         rule tauM <=> 7 [simp]\n  rule reader(1) :- tauM\nend\n",
    )
    .err()
    .expect("must be refused");
    let joined = errs.join(" | ");
    assert!(
        joined.contains("a goal is MATCHED rather than rewritten"),
        "the message must say the POSITION admits no rewrite — and say it that way: \
         `[simp]` DOES fire in a rule body's VALUE slot, so \"a rule body is not a \
         rewrite site\" would be a false sentence about the line above; got:\n{joined}"
    );
    assert!(
        !joined.contains("clause(s) fired here"),
        "the `UnreducedEquationFunctor` wording would send the author to inspect a \
         `[simp]` clause that is fine; got:\n{joined}"
    );
}
