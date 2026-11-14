//! WI-20261106-3TFWV — a `Bool` goal of a body-less spec operation the typer did not pin is
//! the condition `eq(f(args), true)` (kernel-language §5.2's goal-position table), as the same
//! call in a value slot and its result-column twin are.
//!
//! Before, the resolver's Bool view (`dispatched_bool_relation`, kb/resolve.rs) read a goal
//! `f(args)` so only for an `f` with a body or a goal pinned to one. A goal a clause's guard
//! weaves (`ApplyWithin Pred.ok(?x, <dictionary>)`) and one left as the bare spec operation
//! were both looked up as the relation `Pred.ok`, which has no clause: the goal failed and its
//! `not` held. The result-column twin `Pred.ok(?x, ?r)` answered through WI-1057's view of a
//! body-less spec op. Now the Bool view admits the same operations
//! (`body_less_bool_relation`), and the weave's check that a goal has a reader counts it
//! (`woven_goal_has_reader`, kb/typing/rule_requirements.rs), so a goal at an open type is
//! refused at load as the twin is: a rule takes no dictionary it does not declare.
//!
//! BACKED OUT, MEASURED one part at a time in one build: the resolver's leg fails the rows
//! marked RESOLVER, the typer's leg fails the row marked TYPER; the controls pass either way.

use anthill_core::eval::Value;
use anthill_core::kb::load::QueryPattern;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

use crate::common::{assert_refused_naming, interp_for, load_errors_of, unrendered_load_errors_of};

const NS: &str = "t3tfwv";

/// The spec, a carrier whose own `ok` holds above 2, and a second provider of the same
/// instance whose `ok` is always false; `extra` is the program's own clauses.
fn program(extra: &str) -> String {
    format!(
        r#"
namespace {NS}
  import anthill.prelude.{{Bool, Int64, List}}

  sort Pred
    sort T = ?
    operation ok(x: T) -> Bool
  end

  sort Leaf
    entity leaf(v: Int64)
    provides Pred[T = Leaf]
    operation ok(x: Leaf) -> Bool = match x
      case leaf(v) -> v > 2
  end

  sort Other
    provides Pred[T = Leaf]
    operation ok(x: Leaf) -> Bool = false
  end

  fact src(leaf(v: 3))
  fact src1(leaf(v: 1))
{extra}
end
"#
    )
}

/// `(definite, total)` answers of the goal `pattern`, its head and `leaf` written unqualified
/// in the namespace: a suspension reads as neither a success nor a refutation.
fn count(kb: &mut KnowledgeBase, pattern: &str) -> (usize, usize) {
    let qualified = format!("{NS}.{}", pattern.replace("leaf(", &format!("{NS}.Leaf.leaf(")));
    let goal: QueryPattern = crate::common::query_pattern_term(kb, &qualified);
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    (sols.iter().filter(|s| s.is_definite()).count(), sols.len())
}

const GUARDED: &str = r#"
  rule chkG[A](?x: A) :- Pred[T = A], Pred.ok(?x)
  rule viaG(?y) :- src(?y), chkG(?y)
  rule notG(?y) :- src(?y), not(chkG(?y))
  rule viaG1(?y) :- src1(?y), chkG(?y)
  rule notG1(?y) :- src1(?y), not(chkG(?y))
  rule chkGR[A](?x: A, ?r) :- Pred[T = A], Pred.ok(?x, ?r)
  rule viaGR(?y, ?r) :- src(?y), chkGR(?y, ?r)
"#;

/// The ticket's guarded goal: it decides through the guard's dictionary, true for
/// `leaf(v: 3)` and false for `leaf(v: 1)`, and its `not` the other way. RESOLVER: `viaG`
/// answers nothing and `notG` holds. The false half and the result-column twin are
/// controls, passing either way (a relation with no clause fails, and the twin's view
/// already admitted the operation).
#[test]
fn a_guarded_bool_goal_decides_through_its_dictionary() {
    let mut interp = interp_for(&program(GUARDED));
    let kb = interp.kb_mut();
    assert_eq!(count(kb, "viaG(?y)"), (1, 1), "the guarded goal holds for leaf(v: 3)");
    assert_eq!(count(kb, "viaG(leaf(v: 3))"), (1, 1), "…and that is its one answer");
    assert_eq!(count(kb, "notG(?y)"), (0, 0), "…so its `not` fails");
    assert_eq!(count(kb, "viaG1(?y)"), (0, 0), "CONTROL: false for leaf(v: 1)");
    assert_eq!(count(kb, "notG1(?y)"), (1, 1), "CONTROL: …and its `not` holds");
    assert_eq!(
        count(kb, "viaGR(leaf(v: 3), true)"),
        (1, 1),
        "CONTROL: the result-column twin answers `true`"
    );
}

/// A citation passes the dictionary: `chkG[A = Leaf]` reads `Leaf`'s own `ok`, and
/// `chkG[A = Leaf, Pred = Other]` reads `Other`'s, from an operation body and from a rule
/// body, each `not` the other way. RESOLVER: `own` is false, `ownR` fails and `notOwnR`
/// holds. The `Other` rows are controls, passing either way.
#[test]
fn a_cited_guarded_goal_answers_the_passed_dictionary() {
    let extra = r#"
  rule chkG[A](?x: A) :- Pred[T = A], Pred.ok(?x)
  operation own() -> Bool effects {Error} = chkG[A = Leaf](leaf(v: 3)).nonEmpty
  operation other() -> Bool effects {Error} = chkG[A = Leaf, Pred = Other](leaf(v: 3)).nonEmpty
  rule ownR() :- chkG[A = Leaf](leaf(v: 3))
  rule notOwnR() :- not(chkG[A = Leaf](leaf(v: 3)))
  rule otherR() :- chkG[A = Leaf, Pred = Other](leaf(v: 3))
  rule notOtherR() :- not(chkG[A = Leaf, Pred = Other](leaf(v: 3)))
"#;
    let mut interp = interp_for(&program(extra));
    let call = |interp: &mut anthill_core::eval::Interpreter, op: &str| match interp.call(&format!("{NS}.{op}"), &[]) {
        Ok(Value::Bool(b)) => b,
        other => panic!("`{op}`: expected a Bool, got {other:?}"),
    };
    assert!(call(&mut interp, "own"), "`Leaf`'s own `ok` holds: one row");
    assert!(!call(&mut interp, "other"), "CONTROL: `Other`'s `ok` is false: no row");
    let kb = interp.kb_mut();
    assert_eq!(count(kb, "ownR()"), (1, 1), "the rule-body citation holds");
    assert_eq!(count(kb, "notOwnR()"), (0, 0), "…and its `not` fails");
    assert_eq!(count(kb, "otherR()"), (0, 0), "CONTROL: `Other`'s fails");
    assert_eq!(count(kb, "notOtherR()"), (1, 1), "CONTROL: …and its `not` holds");
}

/// A guarded goal whose argument nothing types is refused: a query leaving `A` open where it
/// is read, and a rule-body goal at a variable no head column reaches (`not(chkG(?z))`) at load
/// — no caller passes the requirement, and none is read from the value when the goal runs
/// (proposal 073 §6.2). It waited while the guard read the value: one conditional answer, and
/// its `not` undecided. Asked at a value, or at a variable a column of its own clause or a fact
/// types, it answers.
#[test]
fn a_guarded_goal_with_an_unbound_argument_is_refused() {
    let extra = r#"
  rule chkG[A](?x: A) :- Pred[T = A], Pred.ok(?x)
  rule lateG[A](?x: A) :- Pred[T = A], Pred.ok(?x), src(?x)
  rule lateF[A](?x: A) :- Pred[T = A], Pred.ok(?x), src1(?x)
  rule notLateF(?y) :- src1(?y), not(lateF(?y))
"#;
    crate::common::assert_refused_naming(
        &load_errors_of(&program(&format!("{extra}  rule nope() :- not(chkG(?z))\n"))),
        &["nope.body", "`Pred` at `chkG`'s `A`"],
        "a goal under `not` at a variable no head column reaches",
    );
    let mut interp = interp_for(&program(extra));
    let kb = interp.kb_mut();
    crate::common::assert_refused_naming(
        &crate::common::query_pattern_refusals(kb, &format!("{NS}.chkG(?y)")),
        &["`Pred` at `chkG`'s `A`"],
        "a query whose column nothing types",
    );
    assert_eq!(count(kb, "lateG(leaf(v: 3))"), (1, 1), "at a value, the goal answers true");
    assert_eq!(count(kb, "lateF(leaf(v: 1))"), (0, 0), "at `leaf(v: 1)` it is false");
    // A column its own clause types — `src(?x)` holds `Leaf`s — types the query's variable, as
    // a rule body's goal `lateG(?y)` is typed by it.
    assert_eq!(count(kb, "lateG(?y)"), (1, 1), "typed at `Leaf` by its column");
    assert_eq!(count(kb, "lateF(?y)"), (0, 0), "typed at `Leaf`, and false");
    assert_eq!(count(kb, "notLateF(?y)"), (1, 1), "…and its `not` holds, `?y` typed by `src1`");
}

/// At an open type the goal is refused as its result-column twin is, with the same refusal and
/// nothing else, and both repairs run: the guard and the typed head. TYPER: the goal form loads
/// clean. The twin's refusal and the typed head are controls, passing either way; the guard
/// repair is RESOLVER's too.
#[test]
fn an_open_type_goal_is_refused_as_its_twin_and_both_repairs_run() {
    let refusal = "a rule takes no dictionary it does not declare";
    for (form, rule) in [
        ("the goal", "  rule chk(?x) :- Pred.ok(?x)"),
        ("CONTROL: the twin", "  rule chk(?x, ?r) :- Pred.ok(?x, ?r)"),
    ] {
        let errs = load_errors_of(&program(rule));
        assert_eq!(errs.len(), 1, "{form}: one refusal, got {errs:#?}");
        assert_refused_naming(&errs, &[refusal, "Pred.ok", "chk.body"], form);
    }
    let repairs = r#"
  rule chk[A](?x: A) :- Pred[T = A], Pred.ok(?x)
  rule viaChk(?y) :- src(?y), chk(?y)
  rule viaChk1(?y) :- src1(?y), chk(?y)
  rule typed(?x: Leaf) :- Pred.ok(?x)
  rule viaTyped(?y) :- src(?y), typed(?y)
  rule viaTyped1(?y) :- src1(?y), typed(?y)
"#;
    let mut interp = interp_for(&program(repairs));
    let kb = interp.kb_mut();
    assert_eq!(count(kb, "viaChk(leaf(v: 3))"), (1, 1), "the guard repair answers");
    assert_eq!(count(kb, "viaChk1(?y)"), (0, 0), "CONTROL: …false at leaf(v: 1)");
    assert_eq!(count(kb, "viaTyped(leaf(v: 3))"), (1, 1), "CONTROL: the typed head is pinned");
    assert_eq!(count(kb, "viaTyped1(?y)"), (0, 0), "CONTROL: …false at leaf(v: 1)");
}

/// The goal in each other place a goal is proved — an `|` branch, a bounded quantifier's
/// body, a clause written in the spec itself, a top-level query — answers as its result-column
/// twin there does. RESOLVER: each goal row answers nothing; the twins are controls.
#[test]
fn the_goal_answers_as_its_twin_wherever_a_goal_is_proved() {
    let extra = r#"
  fact bag([leaf(v: 3), leaf(v: 4)])
  fact bag1([leaf(v: 3), leaf(v: 1)])
  rule orG[A](?x: A) :- Pred[T = A], (Pred.ok(?x) | false)
  rule viaOr(?y) :- src(?y), orG(?y)
  rule allG[A](?xs: List[T = A]) :- Pred[T = A], (forall ?x in ?xs: Pred.ok(?x))
  rule viaAll(?l) :- bag(?l), allG(?l)
  rule viaAll1(?l) :- bag1(?l), allG(?l)
  rule allGR[A](?xs: List[T = A]) :- Pred[T = A], (forall ?x in ?xs: Pred.ok(?x, true))
  rule viaAllR(?l) :- bag(?l), allGR(?l)
  rule viaGood(?y) :- src(?y), Pred.good(?y)
  rule viaGood1(?y) :- src1(?y), Pred.good(?y)
  rule viaGoodR(?y, ?r) :- src(?y), Pred.goodR(?y, ?r)
"#;
    let src = program(extra).replace(
        "    operation ok(x: T) -> Bool\n",
        "    operation ok(x: T) -> Bool\n    rule good(?x: T) :- ok(?x)\n    rule goodR(?x: T, ?r) :- ok(?x, ?r)\n",
    );
    assert!(src.contains("rule good(?x: T)"), "the spec's clauses are in the fixture");
    let mut interp = interp_for(&src);
    let kb = interp.kb_mut();
    assert_eq!(count(kb, "viaOr(leaf(v: 3))"), (1, 1), "an `|` branch");
    assert_eq!(count(kb, "viaAll(?l)"), (1, 1), "a quantifier's body");
    assert_eq!(count(kb, "viaAll1(?l)"), (0, 0), "CONTROL: …false where one element is");
    assert_eq!(count(kb, "viaAllR(?l)"), (1, 1), "CONTROL: …the twin there");
    assert_eq!(count(kb, "viaGood(leaf(v: 3))"), (1, 1), "a clause written in the spec");
    assert_eq!(count(kb, "viaGood1(?y)"), (0, 0), "CONTROL: …false at leaf(v: 1)");
    assert_eq!(count(kb, "viaGoodR(leaf(v: 3), true)"), (1, 1), "CONTROL: …the twin there");
    assert_eq!(count(kb, "Pred.ok(leaf(v: 3))"), (1, 1), "a top-level query");
    assert_eq!(count(kb, "Pred.ok(leaf(v: 1))"), (0, 0), "CONTROL: …false at leaf(v: 1)");
    assert_eq!(count(kb, "Pred.ok(leaf(v: 3), true)"), (1, 1), "CONTROL: …the twin there");
}

/// A constraint guard is read as a rule body is: `no … -: Pred.ok(?y)` is violated by a row
/// whose `ok` holds, as its twin `Pred.ok(?y, true)` is, and holds over one whose `ok` is
/// false. RESOLVER: the violated goal row loads clean. The rest are controls.
#[test]
fn a_constraint_guard_reads_the_goal_as_its_twin() {
    use anthill_core::kb::load::LoadError;
    for (form, guard) in [("the goal", "Pred.ok(?y)"), ("CONTROL: the twin", "Pred.ok(?y, true)")] {
        let errs = unrendered_load_errors_of(&program(&format!("  constraint allOk: no ?y: src(?y) -: {guard}")));
        assert!(
            matches!(
                errs.iter().map(|e| e.peel()).collect::<Vec<_>>().as_slice(),
                [LoadError::ConstraintViolated { label: Some(l) }] if l == "allOk"
            ),
            "{form}: violated by leaf(v: 3) and refused for nothing else; got {errs:#?}"
        );
    }
    for guard in ["Pred.ok(?y)", "Pred.ok(?y, true)"] {
        let errs = load_errors_of(&program(&format!("  constraint allOk: no ?y: src1(?y) -: {guard}")));
        assert!(errs.is_empty(), "CONTROL: `{guard}` holds over leaf(v: 1); got {errs:#?}");
    }
}

/// CONTROL: a bodied `Bool` operation's goal (WI-580's view) and the pinned body-less goal
/// (WI-1043) answer as before; both pass either way.
#[test]
fn the_bodied_and_pinned_bool_goals_are_unchanged() {
    let extra = r#"
  operation big(x: Leaf) -> Bool = match x
    case leaf(v) -> v > 2
  rule viaBig(?y) :- src(?y), big(?y)
  rule viaBig1(?y) :- src1(?y), big(?y)
  rule pinned() :- Pred.ok(leaf(v: 3))
  rule notPinned() :- not(Pred.ok(leaf(v: 3)))
"#;
    let mut interp = interp_for(&program(extra));
    let kb = interp.kb_mut();
    assert_eq!(count(kb, "viaBig(leaf(v: 3))"), (1, 1), "a bodied `Bool` goal holds");
    assert_eq!(count(kb, "viaBig1(?y)"), (0, 0), "…and is false at leaf(v: 1)");
    assert_eq!(count(kb, "pinned()"), (1, 1), "the pinned goal holds");
    assert_eq!(count(kb, "notPinned()"), (0, 0), "…and its `not` fails");
}
