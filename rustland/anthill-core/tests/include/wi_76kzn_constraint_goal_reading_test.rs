//! WI-20261023-76KZN — A CONSTRAINT'S GOALS ARE READ AND TYPED AS A RULE BODY'S ARE. A
//! constraint is a headless rule (kernel-language §6.2): its goals are stored as a clause
//! with the head `⊥` beside the guard the engine evaluates, so the rule-body passes reach
//! them — the goal readings (a constant, a non-`Bool` const, an applied const, a const with
//! no load-time value), the clause typing (an effectful call, a function handed to a
//! relation, an argument of the wrong type) and the refusal of a goal that names nothing.
//! Each is the refusal the rule-body twin gets, at the goal's own text. Before, the `no`
//! rows loaded in silence and the `forall` rows reported the constraint violated by the
//! facts, where the defect was its text.
//!
//! The guard is evaluated as before, from the constraint's `LogicalQuery`, and the controls
//! hold under `forall` and fail under `no`; but a constraint whose text the load refuses is
//! not checked (kernel-language §8.4), so the refusal is its one report. An ordinary denial
//! stays inert; its invariant and its guard are goals and are held all the same.
//!
//! The typed binder `forall (?x: T) -: body` is removed from the grammar: its condition named
//! a relation nothing declares, so its guard matched nothing.
//!
//! Spelling: `constraint NAME :- G` has no label — the grammar reads `NAME` as the denial's
//! invariant, a goal, which is now refused when it names nothing. A labeled denial with no
//! invariant is `constraint NAME: false :- G`.
//!
//! ## Back-out
//!
//! Each piece made a no-op in place under a switch of its own, one build, this module and the
//! tests whose fixtures the change moved run under each (measured 2026-10-23):
//!
//! | backed out | fails |
//! |---|---|
//! | the clause (`assert_constraint_goal_clause` stores nothing) | `a_constraint_goal_with_no_goal_reading_is_refused`, `an_effectful_call_in_a_constraint_is_refused`, `a_function_handed_over_in_a_constraint_is_refused`, `a_constraint_goal_is_typed_and_name_checked`; `wi_719fj…::a_constraint_body_reads_a_citation_as_a_rule_body_does` |
//! | the clause filed as source, not derived | `wi_bvg8m_spec_laws_test::a_law_is_a_rule_or_a_constraint_written_in_the_spec`, `…::the_librarys_laws_are_not_its_default_bodies`: the constraint is two laws |
//! | the goals built outside goal position (`in_body_goal`) | `the_controls_hold_under_forall_and_fail_under_no` (`-: flag` is not folded to its value, and is refused), `wi_719fj…::a_constraint_body_reads_a_citation_as_a_rule_body_does` |
//! | the descriptions left to the clause's walk too (`descs_emitted_by_convert`) | `an_inline_description_in_a_constraint_goal_is_emitted_once`: two facts |
//! | the refused constraint's guard checked (`refused_constraint_guards` answers none) | `a_refused_constraint_is_not_checked_against_the_facts` |
//!
//! `the_typed_binder_is_not_parsed` fails with the grammar's line restored, by construction;
//! not run.
//!
//! NOT DRIVEN, and said rather than claimed: the clause's occurrences carry the constraint's
//! label as their owner, as a labeled rule's do. Backed out, no row fails — the owner is
//! read by reflect's `occurrence_owner` and copied onto the nodes the typer builds, and no
//! reader of a clause body's owner decides a verdict.
//!
//! CONTROLS, green under every back-out: `the_controls_hold_under_forall_and_fail_under_no`
//! under all but its own, `a_pure_function_handed_over_in_a_constraint_is_not_refused`.

use crate::common::{assert_refused_naming, load_errors_of, unrendered_load_errors_of};
use anthill_core::kb::load::{ConstGoalProblem, LoadError};

const PRELUDE: &str = r#"
namespace test.c76kzn
  import anthill.prelude.{Int64, String, Bool}
  import anthill.prelude.Time.{now, Clock}
  const nn: Int64 = 5
  const flag: Bool = true
  const big: Bool = Int64.gt(nn, 3)
  entity item(n: Int64)
  fact item(n: 1)
  operation is_big(x: Int64) -> Bool = Int64.gt(x, 0)
  operation dbl(x: Int64) -> Int64 = x
  operation plainStamp() -> String effects {Clock} = now()
  operation applyThunk[Rho](f: () -> String @ {Rho}) -> String effects {Rho} = f()
  rule applies(?f, ?r) :- applyThunk(?f, ?r)
"#;

fn program(constraint: &str) -> String {
    format!("{PRELUDE}  {constraint}\nend\n")
}

/// The ticket's rows, and the two positions of an ordinary denial: each refused by its
/// variant, naming what is written, at the goal's own text.
#[test]
fn a_constraint_goal_with_no_goal_reading_is_refused() {
    type Matches = fn(&LoadError) -> bool;
    let rows: &[(&str, &str, Matches)] = &[
        ("constraint c: forall ?x: item(n: ?x) -: 42", "42", |e| {
            matches!(e, LoadError::ConstantInGoalPosition { literal, .. } if literal == "42")
        }),
        ("constraint c: no ?x: item(n: ?x) -: 42", "42", |e| {
            matches!(e, LoadError::ConstantInGoalPosition { literal, .. } if literal == "42")
        }),
        ("constraint c: forall ?x: item(n: ?x) -: nn", "nn", |e| {
            matches!(e, LoadError::ConstInGoalPosition { name, problem: ConstGoalProblem::NotBool { .. }, .. }
                if name == "test.c76kzn.nn")
        }),
        ("constraint c: no ?x: item(n: ?x) -: nn", "nn", |e| {
            matches!(e, LoadError::ConstInGoalPosition { name, problem: ConstGoalProblem::NotBool { .. }, .. }
                if name == "test.c76kzn.nn")
        }),
        ("constraint c: no ?x: item(n: ?x) -: flag()", "flag()", |e| {
            matches!(e, LoadError::TypeMismatch { entity_name, field_name, .. }
                if entity_name == "flag" && field_name == "apply")
        }),
        ("constraint c: forall ?x: item(n: ?x) -: big", "big", |e| {
            matches!(e, LoadError::ConstInGoalPosition { name, problem: ConstGoalProblem::ValueUnavailable { .. }, .. }
                if name == "test.c76kzn.big")
        }),
        // An ordinary denial is inert (§6.2); its invariant and its guard are goals still.
        ("constraint c: 42 :- item(n: ?x)", "42", |e| {
            matches!(e, LoadError::ConstantInGoalPosition { literal, .. } if literal == "42")
        }),
        ("constraint c: false :- item(n: ?x), 42", "42", |e| {
            matches!(e, LoadError::ConstantInGoalPosition { literal, .. } if literal == "42")
        }),
    ];
    let mut bad = Vec::new();
    for (constraint, written, matches) in rows {
        let src = program(constraint);
        let errs = unrendered_load_errors_of(&src);
        let at_goal = errs.iter().find(|e| matches(e.peel())).and_then(|e| {
            let sp = e.user_span()?;
            src.get(sp.start as usize..sp.end as usize)
        });
        if at_goal != Some(*written) {
            bad.push(format!(
                "`{constraint}`: expected the refusal at `{written}`, got {at_goal:?} in {:#?}",
                errs.iter().map(|e| e.peel()).collect::<Vec<_>>()
            ));
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// The goals that have a reading: each holds under `forall` and fails under `no`, which is
/// the guard's verdict alone — nothing refuses the text.
#[test]
fn the_controls_hold_under_forall_and_fail_under_no() {
    for goal in ["true", "flag", "Int64.gt(nn, 3)", "is_big(?x)"] {
        let holds = load_errors_of(&program(&format!(
            "constraint c: forall ?x: item(n: ?x) -: {goal}"
        )));
        assert!(holds.is_empty(), "`forall … -: {goal}` holds; got {holds:#?}");
        let errs = unrendered_load_errors_of(&program(&format!(
            "constraint c: no ?x: item(n: ?x) -: {goal}"
        )));
        assert!(
            matches!(
                errs.iter().map(|e| e.peel()).collect::<Vec<_>>().as_slice(),
                [LoadError::ConstraintViolated { label: Some(l) }] if l == "c"
            ),
            "`no … -: {goal}` is violated by `item(n: 1)` and refused for nothing else; got \
             {errs:#?}"
        );
    }
}

/// A constraint performs no effect, as a rule body does not: the call is refused naming
/// itself and the effect, in the guard, the invariant and a quantified body.
#[test]
fn an_effectful_call_in_a_constraint_is_refused() {
    for constraint in [
        "constraint noStamp: false :- plainStamp() = \"2000\"",
        "constraint noStamp: plainStamp() = \"2000\"",
        "constraint noStamp: no ?x: item(n: ?x) -: plainStamp() = \"2000\"",
    ] {
        assert_refused_naming(
            &load_errors_of(&program(constraint)),
            &["the call `test.c76kzn.plainStamp`", "performs `Clock`"],
            constraint,
        );
    }
}

/// A function handed to a relation in a constraint's goal is held to its own row.
#[test]
fn a_function_handed_over_in_a_constraint_is_refused() {
    assert_refused_naming(
        &load_errors_of(&program(
            "constraint hands: no ?x: item(n: ?x) -: applies(lambda () -> now(), \"x\")",
        )),
        &["a function handed to `test.c76kzn.applies`", "performs `Clock`"],
        "an effectful function handed to a relation",
    );
}

/// The control: a pure function handed over is not refused for an effect. (The guard does
/// not decide it — a lambda in a guard keeps the parser's marker, WI-20261015-8JYER — and
/// that is not this module's.)
#[test]
fn a_pure_function_handed_over_in_a_constraint_is_not_refused() {
    let errs = load_errors_of(&program(
        "constraint hands: no ?x: item(n: ?x) -: applies(lambda () -> \"x\", \"x\")",
    ));
    assert!(
        errs.iter().all(|e| !e.contains("performs")),
        "a pure function performs nothing; got {errs:#?}"
    );
}

/// The rest of the rule-body checking reaches a constraint's goals: an argument of the wrong
/// type (WI-20260902-65QKB's row) and a goal that names nothing.
#[test]
fn a_constraint_goal_is_typed_and_name_checked() {
    assert_refused_naming(
        &load_errors_of(&program("constraint c: no ?x: item(n: ?x) -: dbl(true) = 1")),
        &["dbl.x (op-arg)", "expected Int64, got Bool"],
        "an argument of the wrong type",
    );
    assert_refused_naming(
        &load_errors_of(&program("constraint c: no ?x: item(n: ?x) -: bogus(?x)")),
        &["goal `bogus` names nothing"],
        "a goal that names nothing",
    );
    // The unlabeled spelling: `NAME` is the invariant, a goal.
    assert_refused_naming(
        &load_errors_of(&program("constraint no_ones :- item(n: 1)")),
        &["goal `no_ones` names nothing"],
        "an unlabeled denial's invariant",
    );
}

/// A constraint's goals are converted for its guard first, which emits a described
/// variable's description; the clause's atoms are built after, and do not emit it again.
#[test]
fn an_inline_description_in_a_constraint_goal_is_emitted_once() {
    use anthill_core::kb::term::{Literal, Term};
    let src = [
        PRELUDE,
        "  rule pos(?n) :- item(n: ?n)\n",
        "  constraint c: forall ?x: item(n: ?x) -: pos(?x {< the constraint value >}?)\n",
        "end\n",
    ]
    .concat();
    let kb = crate::common::load_kb_with(&src);
    let desc_sym = kb
        .try_resolve_symbol("anthill.reflect.DescriptionInfo")
        .expect("the reflect sort is registered by the prelude");
    let n = kb
        .rules_by_functor(desc_sym)
        .iter()
        .filter(|&&rid| match kb.get_term(kb.rule_head(rid)) {
            Term::Fn { named_args, .. } => named_args
                .iter()
                .find(|(f, _)| kb.local_name_of(*f) == "content")
                .is_some_and(|(_, v)| {
                    matches!(kb.get_term(*v), Term::Const(Literal::String(s)) if s == "the constraint value")
                }),
            _ => false,
        })
        .count();
    assert_eq!(n, 1, "one written description is one fact; got {n}");
}

/// A constraint whose text the load refuses is not checked against the facts (kernel-language
/// §8.4): the refusal is its one report, where the guard said "violated" or "not decided"
/// beside it. The control is the second constraint of the same file, which is checked and
/// violated: what is left out is the refused constraint's guard, not the check.
#[test]
fn a_refused_constraint_is_not_checked_against_the_facts() {
    for refused in [
        "constraint c: forall ?x: item(n: ?x) -: 42",
        "constraint c: forall ?x: item(n: ?x) -: nn",
        "constraint c: forall ?x: item(n: ?x) -: big",
        "constraint c: no ?x: item(n: ?x) -: applies(lambda () -> now(), \"x\")",
    ] {
        let src = program(&format!("{refused}\n  constraint d: no ?x: item(n: ?x) -: true"));
        let errs = unrendered_load_errors_of(&src);
        let guards: Vec<_> = errs
            .iter()
            .map(|e| e.peel())
            .filter(|e| {
                matches!(
                    e,
                    LoadError::ConstraintViolated { .. } | LoadError::ConstraintUndecidable { .. }
                )
            })
            .collect();
        assert!(
            matches!(guards.as_slice(), [LoadError::ConstraintViolated { label: Some(l) }] if l == "d"),
            "`{refused}`: only `d` is checked, and it is violated; got {errs:#?}"
        );
    }
}

/// The typed binder `forall (?x: T) -: body` is not in the grammar: its condition named a
/// relation nothing declares, so the guard matched nothing — `some (?x: item) -: true` was
/// violated beside `item(n: 1)` — and it is removed until it has a reading.
#[test]
fn the_typed_binder_is_not_parsed() {
    let errs = anthill_core::parse::parse(&program("constraint c: forall (?x: Int64) -: is_big(?x)"))
        .err()
        .expect("the typed binder form does not parse");
    assert!(
        errs.iter().any(|e| e.message == "syntax error near `?x: Int64`"),
        "the binder is where the parse stops; got {errs:#?}"
    );
}
