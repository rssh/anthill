//! WI-20261121-G8E02 — THE PROOF OF A GOAL: `anthill.reflect.SLDProof.of(goal, ?p)` (proposal
//! 075; kernel-language §8.3, "The proof of a goal"). The search gives back the proof it makes,
//! as an `SLDProof` term: for a goal `g`, one answer per proof of `g`; for a negation `!g`, the
//! proof of `!g` the search finds — its refutation of `g` — and no other.
//!
//! Before: a goal with no answer said nothing about why (`no solutions`), and nothing in the
//! language could ask how a goal that holds was proved.
//!
//! Every row asks the relation FROM A RULE BODY, as a program does, and reads the answer of
//! that rule; the rows that fix a proof's whole shape compare it printed.
//!
//! BACK-OUTS: measured, listed at the end of this file.

use anthill_core::eval::Value;
use anthill_core::kb::resolve::{ResolveConfig, Solution};
use anthill_core::kb::term::{Term, TermId, Var};
use anthill_core::kb::term_view::{TermView, ViewHead};
use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::print::TermPrinter;

use crate::common::{load_kb_with, query_pattern_term};

const SRC: &str = r#"
namespace g8e02
  import anthill.prelude.{Int64}
  import anthill.reflect.{SLDProof, Step}
  import anthill.reflect.SLDProof.{refuted}

  rule pos(?x) :- ?x > 0
  rule big(?x) :- ?x > 5
  rule even(?x) :- ?x % 2 = 0
  rule good(?x) :- pos(?x), big(?x), even(?x)

  fact edge(1, 2)
  fact edge(1, 3)
  rule reach_big(?x) :- edge(?x, ?y), big(?y)

  rule all_big(?xs) :- (forall ?y in ?xs: ?y > 5)

  rule q(?x) :- ?x > 0
  rule notq(?x) :- !q(?x)

  rule loop(?x) :- loop(?x)
  rule guarded(?x) :- loop(?x), ?x > 5

  fact under10(p0)
  fact sale(p9)
  rule cheap(?p) :- under10(?p)
  rule cheap(?p) :- sale(?p), under10(?p)

  enum IntList
    entity i_nil
    entity i_cons(head: Int64, tail: IntList)
  end
  fact prop_holds(i_nil)
  rule prop_holds(i_cons(head: ?_h, tail: ?t)) :- prop_holds(?t)
  fact half(i_nil)

  -- The relation, asked from rule bodies.
  rule proof_good6(?p) :- SLDProof.of(good(6), ?p)
  rule proof_good1(?p) :- SLDProof.of(good(1), ?p)
  rule refute_good1(?p) :- SLDProof.of(!good(1), ?p)
  rule refute_good6(?p) :- SLDProof.of(!good(6), ?p)
  rule good1_fails_at(?f) :- SLDProof.of(!good(1), refuted(steps: [Step(failing: ?f)]))
  rule proof_edge(?y, ?p) :- SLDProof.of(edge(1, ?y), ?p)
  rule refute_all_big(?p) :- SLDProof.of(!all_big([7, 3, 9]), ?p)
  rule refute_reach_big(?p) :- SLDProof.of(!reach_big(1), ?p)
  rule refute_cheap(?p) :- SLDProof.of(!cheap(p1), ?p)
  rule refute_edge51(?p) :- SLDProof.of(!edge(5, 1), ?p)
  rule refute_notq(?p) :- SLDProof.of(!notq(1), ?p)
  rule refute_guarded(?p) :- SLDProof.of(!guarded(1), ?p)
  rule proof_big_open(?x, ?p) :- SLDProof.of(big(?x), ?p)
  rule proof_induction(?p) :- SLDProof.of(IntList.induction(prop_holds), ?p)
  rule refute_induction(?p) :- SLDProof.of(!(IntList.induction(half)), ?p)
  rule div_ok(?x) :- 10 / ?x > 1
  rule proof_div(?p) :- SLDProof.of(div_ok(0), ?p)
end
"#;

/// The answers of `pattern`, each its LAST argument printed, and whether it is definite.
fn last_args(kb: &mut KnowledgeBase, pattern: &str) -> Vec<(String, bool)> {
    let goal = query_pattern_term(kb, pattern);
    let written = anthill_core::kb::load::query_goal_as_written(kb, &goal);
    let last = match TermView::head(&written, kb) {
        ViewHead::Functor { pos_arity, .. } if pos_arity > 0 => TermView::pos_arg(&written, kb, pos_arity - 1)
            .expect("the last argument is readable")
            .to_value(),
        other => panic!("`{pattern}` is no application with an argument: {other:?}"),
    };
    let sols: Vec<Solution> = kb.resolve(&[goal], &ResolveConfig::default());
    sols.iter()
        .map(|sol| {
            let v = kb.reify_value(&last, &sol.subst);
            (print(kb, &v), sol.is_definite())
        })
        .collect()
}

fn print(kb: &mut KnowledgeBase, v: &Value) -> String {
    match v {
        Value::Term { id, .. } => TermPrinter::new(kb).print_term(*id),
        Value::Node(occ) => TermPrinter::new(kb).print_occurrence(occ),
        other => {
            let t = kb.alloc_from_value(other).expect("an answer lowers to a term");
            TermPrinter::new(kb).print_term(t)
        }
    }
}

/// The one definite answer of `pattern`, printed.
fn one_proof(kb: &mut KnowledgeBase, pattern: &str) -> String {
    let answers = last_args(kb, pattern);
    assert_eq!(answers.len(), 1, "`{pattern}` has one answer; got {answers:?}");
    assert!(answers[0].1, "`{pattern}`'s answer is definite; got {answers:?}");
    answers.into_iter().next().unwrap().0
}

fn has_rigid(kb: &KnowledgeBase, t: TermId) -> bool {
    match kb.get_term(t) {
        Term::Var(Var::Rigid(_)) => true,
        Term::Fn { pos_args, named_args, .. } => {
            pos_args.iter().any(|&a| has_rigid(kb, a)) || named_args.iter().any(|&(_, a)| has_rigid(kb, a))
        }
        _ => false,
    }
}

/// A goal that holds: by the clause that answered, by its label, with a proof of each body goal
/// in order, down to the builtins. Back-out: no instance recorded at a clause's opening — the
/// answer is a fault, "discharged by a step that recorded no proof".
#[test]
fn a_goal_that_holds_is_proved_by_its_clause_and_its_body() {
    let mut kb = load_kb_with(SRC);
    let p = one_proof(&mut kb, "g8e02.proof_good6(?p)");
    assert!(p.starts_with("by_clause(goal: good(6), clause: some(value: good-"), "{p}");
    for part in [
        "by_clause(goal: pos(6), clause: some(value: pos-",
        "by_builtin(goal: quoted(term: gt(6, 0)))",
        "by_clause(goal: big(6), clause: some(value: big-",
        "by_builtin(goal: quoted(term: gt(6, 5)))",
        "by_clause(goal: even(6), clause: some(value: even-",
    ] {
        assert!(p.contains(part), "the proof holds `{part}`: {p}");
    }
    // In order: pos before big before even.
    let (a, b, c) = (p.find("pos(6)").unwrap(), p.find("big(6)").unwrap(), p.find("even(6)").unwrap());
    assert!(a < b && b < c, "body proofs in written order: {p}");
}

/// The proof of `!g` names, for its one clause, the body goal the search failed at — `big(1)`
/// — and why: `1 > 5` is false. `even(1)`, after it, is never asked. Asked through a pattern, as
/// a program reads it. Back-out: no refutation built — no answer.
#[test]
fn the_proof_of_a_negation_names_the_goal_the_search_failed_at() {
    let mut kb = load_kb_with(SRC);
    let p = one_proof(&mut kb, "g8e02.refute_good1(?p)");
    assert!(p.starts_with("refuted(goal: good(1), steps: [Step(clause: some(value: good-"), "{p}");
    assert!(p.contains("failing: big(1)"), "{p}");
    assert!(p.contains("because: builtin_false(goal: quoted(term: gt(1, 5)))"), "{p}");
    assert!(!p.contains("even"), "a goal after the failure is not asked: {p}");
    assert_eq!(
        last_args(&mut kb, "g8e02.good1_fails_at(?f)"),
        vec![("big(1)".to_string(), true)],
        "a rule reads the failing goal out of the proof by a pattern"
    );
}

/// No proof of a goal that does not hold, and none of `!g` where `g` holds — the controls of
/// the two rows above.
#[test]
fn a_goal_that_fails_has_no_proof_and_its_negation_none_where_it_holds() {
    let mut kb = load_kb_with(SRC);
    assert!(last_args(&mut kb, "g8e02.proof_good1(?p)").is_empty());
    assert!(last_args(&mut kb, "g8e02.refute_good6(?p)").is_empty());
}

/// One answer per proof: each fact answers by its own label, and the goal's variables are bound
/// as the query's are.
#[test]
fn each_answer_has_its_own_proof() {
    let mut kb = load_kb_with(SRC);
    let goal = query_pattern_term(&mut kb, "g8e02.proof_edge(?y, ?p)");
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(sols.len(), 2, "two facts, two proofs");
    let printed: Vec<String> = last_args(&mut kb, "g8e02.proof_edge(?y, ?p)").into_iter().map(|(p, _)| p).collect();
    assert!(printed.iter().any(|p| p.starts_with("by_clause(goal: edge(1, 2), clause: some(value: edge-")), "{printed:?}");
    assert!(printed.iter().any(|p| p.starts_with("by_clause(goal: edge(1, 3), clause: some(value: edge-")), "{printed:?}");
    assert_ne!(printed[0].find("edge-").map(|i| &printed[0][i..i + 13]), printed[1].find("edge-").map(|i| &printed[1][i..i + 13]), "two facts, two labels");
}

/// A bounded `forall` is refuted at the element that breaks it, a step with no clause; the
/// elements that hold are no step.
#[test]
fn a_forall_is_refuted_at_its_failing_element() {
    let mut kb = load_kb_with(SRC);
    let p = one_proof(&mut kb, "g8e02.refute_all_big(?p)");
    assert!(p.contains("Step(clause: none, failing: quoted(term: gt(3, 5)), because: builtin_false(goal: quoted(term: gt(3, 5))))"), "{p}");
    assert!(!p.contains("failing: quoted(term: gt(7, 5))") && !p.contains("failing: quoted(term: gt(9, 5))"), "{p}");
}

/// Where the goals before a failing one have several answers, each branch has its step.
#[test]
fn each_branch_has_its_step() {
    let mut kb = load_kb_with(SRC);
    let p = one_proof(&mut kb, "g8e02.refute_reach_big(?p)");
    assert!(p.contains("failing: big(2)") && p.contains("failing: big(3)"), "{p}");
}

/// Every clause whose head matches has its step, each by its label.
#[test]
fn each_clause_has_its_step() {
    let mut kb = load_kb_with(SRC);
    let p = one_proof(&mut kb, "g8e02.refute_cheap(?p)");
    assert!(p.contains("failing: under10(p1)") && p.contains("failing: sale(p1)"), "{p}");
    assert_eq!(p.matches("clause: some(value: cheap-").count(), 2, "{p}");
}

/// No clause's head matching is a refutation with no step.
#[test]
fn no_clause_matching_is_a_refutation_with_no_step() {
    let mut kb = load_kb_with(SRC);
    assert_eq!(one_proof(&mut kb, "g8e02.refute_edge51(?p)"), "refuted(goal: edge(5, 1), steps: nil)");
}

/// A failing `!q(1)` is explained by `q(1)`'s proof.
#[test]
fn a_failing_negation_is_explained_by_the_proof_of_what_it_negates() {
    let mut kb = load_kb_with(SRC);
    let p = one_proof(&mut kb, "g8e02.refute_notq(?p)");
    assert!(p.contains("failing: quoted(term: not(q(1))), because: by_clause(goal: q(1), clause: some(value: q-"), "{p}");
}

/// Undecided as `!g` is: the depth limit cuts the search for `guarded(1)`, so the answer is
/// conditional and holds no proof. A conditional answer of `g` is a proof with a residual leaf,
/// conditional on the same goal.
#[test]
fn undecided_and_conditional_answers_stay_so() {
    let mut kb = load_kb_with(SRC);
    let guarded = last_args(&mut kb, "g8e02.refute_guarded(?p)");
    assert!(guarded.iter().all(|(_, definite)| !definite), "no definite proof of !guarded(1): {guarded:?}");
    let open = last_args(&mut kb, "g8e02.proof_big_open(?x, ?p)");
    assert_eq!(open.len(), 1, "{open:?}");
    assert!(!open[0].1, "conditional on `?x > 5`: {open:?}");
    assert!(open[0].0.contains("body: [residual(goal: quoted(term: gt("), "{open:?}");
}

/// A proof by induction: by the principle's clause, which the proof names by its label (the
/// principle's own name, kernel-language.md §4.1); the base case by the fact, the step case a
/// discharge — fresh constants, the hypothesis assumed and used as `by_assumption`. No fresh
/// constant escapes as a rigid variable. Back-out: no discharge instance — a fault, as for a
/// clause; the principle's clause stored with no label — `clause: none`.
#[test]
fn a_proof_by_induction_shows_its_discharge_and_its_hypothesis() {
    let mut kb = load_kb_with(SRC);
    let goal = query_pattern_term(&mut kb, "g8e02.proof_induction(?p)");
    let written = anthill_core::kb::load::query_goal_as_written(&kb, &goal);
    let arg = TermView::pos_arg(&written, &kb, 0).unwrap().to_value();
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(sols.len(), 1);
    let v = kb.reify_value(&arg, &sols[0].subst);
    let Value::Term { id, .. } = v else { panic!("a proof is a term: {v:?}") };
    assert!(!has_rigid(&kb, id), "a fresh constant is data in a proof, never a rigid variable");
    let p = TermPrinter::new(&kb).print_term(id);
    for part in [
        "by_clause(goal: induction(prop_holds), clause: some(value: induction), body: [",
        "by_clause(goal: prop_holds(i_nil), clause: some(value: prop_holds-",
        "by_discharge(",
        "fresh: [FreshConstant(",
        "assumed: [prop_holds(FreshConstant(",
        "by_assumption(goal: prop_holds(FreshConstant(",
    ] {
        assert!(p.contains(part), "the proof holds `{part}`: {p}");
    }
}

/// A failing induction is refuted at its step case: inside the discharge, with the hypothesis
/// assumed, the next case has no proof.
#[test]
fn a_failing_induction_is_refuted_inside_its_discharge() {
    let mut kb = load_kb_with(SRC);
    let p = one_proof(&mut kb, "g8e02.refute_induction(?p)");
    assert!(p.contains("because: by_discharge("), "{p}");
    assert!(p.contains("assumed: [half(FreshConstant("), "{p}");
    assert!(p.contains("proof: refuted(goal: half(i_cons("), "{p}");
}

/// A proof's goal that is still a variable waits for its binding, as a negand with an unbound
/// variable does: `SLDProof.of(?g, ?p), ?g = good(6)` is proved as `SLDProof.of(good(6), ?p)`
/// is. Reachable only where the goal arrives as a value — a host's goal list, built here by hand
/// — since a program cannot bind a goal variable to a call. Back-out: no wait — the search for
/// the variable runs at once and overflows the stack, aborting the test binary (MEASURED
/// 2026-11-22).
#[test]
fn a_goal_that_is_still_a_variable_waits_for_its_binding() {
    use anthill_core::kb::term::Literal;
    use smallvec::SmallVec;
    let mut kb = load_kb_with(SRC);
    let of = kb.resolve_symbol("anthill.reflect.SLDProof.of");
    let good = kb.resolve_symbol("g8e02.good");
    let unify = kb.unify_functor();
    let (g_name, p_name) = (kb.intern("g"), kb.intern("p"));
    let (g, p) = (kb.fresh_var(g_name), kb.fresh_var(p_name));
    let g_term = kb.alloc(Term::Var(Var::Global(g)));
    let p_term = kb.alloc(Term::Var(Var::Global(p)));
    let six = kb.alloc(Term::Const(Literal::Int(6)));
    let good6 = kb.alloc(Term::Fn { functor: good, pos_args: SmallVec::from_slice(&[six]), named_args: SmallVec::new() });
    let ask = kb.alloc(Term::Fn { functor: of, pos_args: SmallVec::from_slice(&[g_term, p_term]), named_args: SmallVec::new() });
    let bind = kb.alloc(Term::Fn { functor: unify, pos_args: SmallVec::from_slice(&[g_term, good6]), named_args: SmallVec::new() });
    let sols = kb.resolve(&[ask, bind], &ResolveConfig::default());
    assert_eq!(sols.len(), 1, "one proof");
    assert!(sols[0].is_definite(), "the goal was bound, and proved: no residual");
    let proof = kb.reify_value(&Value::term(p_term), &sols[0].subst);
    let printed = print(&mut kb, &proof);
    assert!(printed.starts_with("by_clause(goal: good(6), clause: some(value: good-"), "{printed}");
}

/// A goal whose search FAULTS (a zero divisor) has a proof form whose search faults too: its
/// end is the fault, as the goal's own is, not a truncation, and no proof. Back-out: the inner
/// search's faults folded only where its fuel ran out — the end is `Truncated`, the fault
/// gone (MEASURED 2026-11-22).
#[test]
fn a_goal_whose_search_faults_has_a_proof_form_that_faults() {
    use anthill_core::kb::resolve::SearchFailure;
    let mut kb = load_kb_with(SRC);
    for pattern in ["g8e02.div_ok(0)", "g8e02.proof_div(?p)"] {
        let goal = query_pattern_term(&mut kb, pattern);
        let stream = kb.resolve_lazy(&[goal], &ResolveConfig::default());
        match stream.split_first(&mut kb) {
            Err(SearchFailure::Faulted(_)) => {}
            Err(other) => panic!("`{pattern}` ends at its fault, got: {other}"),
            Ok(other) => panic!(
                "`{pattern}` has no answer and no complete end; got {}",
                if other.is_some() { "an answer" } else { "a complete end" }
            ),
        }
    }
}

// BACK-OUTS, measured on a selected run of this file (2026-11-22):
//
// * `SORT_SCOPED_BUILTIN_RELATIONS` emptied (the relation unbound): all 12 rows fail — the goal
//   argument is then no goal slot, so the fixture's `SLDProof.of(good(6), ?p)` is typed as a
//   value and the load is refused.
// * no `proof_took` where a clause is opened (`step_choice_point`, the bodied branch): 9 fail.
//   Pass by design: `a_goal_that_fails_has_no_proof_and_its_negation_none_where_it_holds` (it
//   asserts no answer), `each_answer_has_its_own_proof` (facts take the fact path, recorded
//   apart) and `no_clause_matching_is_a_refutation_with_no_step` (no clause is opened).
// * no Discharge instance in `step_forall_impl`: the two induction rows fail, the other 10 pass.
// * the induction principle's clause stored with `ClauseLabel::Runtime` (`emit_induction_rule`):
//   `a_proof_by_induction_shows_its_discharge_and_its_hypothesis` fails, its proof naming the
//   clause `none` (measured on that row, 2026-11-22; `wi_g8e02_derived_labels_test` has the
//   label rows' own back-outs).
//
// The control that proof mode changes no search — the same steps and answers with it as
// without it — is `kb::sld_proof::tests::proof_mode_takes_the_steps_and_gives_the_answers_of_the_search`.
