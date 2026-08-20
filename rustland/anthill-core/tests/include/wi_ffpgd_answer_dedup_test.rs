//! WI-20260820-FFPGD — answer dedup projects onto the QUERY's goals.
//!
//! An ANSWER is an answer to the query. Two proofs that agree on every query
//! variable are ONE answer, however differently they were derived; two that
//! disagree anywhere in the query are TWO, however much of the proof they share.
//! `SearchStream::is_duplicate_answer` keys on the whole query goal VECTOR under
//! the solution σ, and these tests drive both directions of that.
//!
//! Before this ticket the projection was onto the NEAREST ancestor
//! `ChoicePoint`'s goal, which sees only redundancy arising AT a choice point.
//! The first two tests are the two halves the frame walk got wrong and right:
//! [`an_existential_body_var_does_not_multiply_answers`] is what it MISSED, and
//! [`a_conjunctive_query_keeps_every_pairing`] is what a frame walk over ALL
//! ancestors — the tempting wrong fix — would have BROKEN.
//!
//! The other two pin decisions the move FORCED rather than the move itself.
//! [`an_anonymous_query_var_is_still_part_of_the_answer`] says a `?` in the QUERY
//! keeps distinguishing (the caller can read its binding), and
//! [`a_dropped_duplicate_still_counts_as_this_choice_points_proof`] pins the
//! ordering the stream-global seen-set made load-bearing — a dropped duplicate is
//! still a proof, and the choice point that made it must be told so or it
//! residualizes a floundered answer over a branch that succeeded.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId, Var};
use anthill_core::kb::KnowledgeBase;
use anthill_core::eval::{self, eval::value_functor};
use smallvec::SmallVec;

/// The ticket's repro, and the defect it names: `witness` is written `?` —
/// ANONYMOUS, i.e. existential — so the two `check` rows that agree on `t` differ
/// only in a field `tagged(?t)` never mentions, and must not be two answers.
///
/// This is acceptance clause (1), at the KB level. The same program through the
/// CLI (`anthill query --path dup.anthill 'dup.probe.tagged(?t)'`) reported
/// `?t = ok` twice and `3 solution(s)`.
///
/// CONTROL, MEASURED: restore the nearest-ancestor projection — replace
/// `is_duplicate_answer`'s body after the `bears_opaque` guard with a walk of
/// `self.stack.iter_mut().rev()` keying the first `FrameState::ChoicePoint`'s
/// `original_goal` into a per-frame `seen_goals` set. THREE tests go red and no
/// others: this one (3, not 2), `kb::resolve::tests::anonymous_vars_chain_through_rules`
/// (3, not 2), and `wi1046_boolean_goal_routing_test::an_imported_bool_no_longer_captures_disjunction`
/// (`[3,1,1,0]`, not `[2,1,1,0]` — its `pipe` row is a disjunction whose two arms
/// reach one shared answer, the same shape one level up). The two OTHER tests in
/// this file PASS under it, which is why they are separate tests: this is the one
/// that measures the FIX rather than guarding the losing direction.
///
/// A frame walk finds no duplicate here at ANY depth — not just at the nearest.
/// The innermost choice point is the one over `check`'s three rows and they are
/// GENUINELY distinct (different `witness`); the redundancy exists only in the
/// projection onto `tagged(?t)`. Accordingly this test PASSES under both wrong
/// fixes below (scan-all, outermost) — they are wrong in the other direction.
#[test]
fn an_existential_body_var_does_not_multiply_answers() {
    let mut kb = crate::common::load_kb_with(
        "namespace test.ffpgd_existential\n\
         \x20 sort Tag    entity ok    entity fail  end\n\
         \x20 sort Row    entity check(t: Tag, witness: Int64) end\n\
         \x20 fact check(t: ok(),   witness: 1)\n\
         \x20 fact check(t: ok(),   witness: 2)\n\
         \x20 fact check(t: fail(), witness: 3)\n\
         \x20 rule tagged(?t) :- check(t: ?t, witness: ?)\n\
         end\n",
    );
    let answers = crate::common::query_unary(&mut kb, "test.ffpgd_existential.tagged");
    assert_eq!(
        answers.len(),
        2,
        "`witness` is existential — one answer per distinct ?t, got {answers:?}",
    );
    // The SECOND, independent claim: dedup collapsed the RIGHT pair. A fix that
    // over-dedups would satisfy the count above with a single answer, and one that
    // keyed the wrong slot could satisfy it with `ok` twice.
    let mut names: Vec<String> = answers
        .iter()
        .map(|(v, definite)| {
            assert!(definite, "an existential body var must not flounder");
            let f = value_functor(&kb, v)
                .unwrap_or_else(|| panic!("?t must answer a constructor, got {v:?}"));
            kb.local_name_of(f).to_string()
        })
        .collect();
    names.sort();
    assert_eq!(names, vec!["fail", "ok"], "both tags, each exactly once");
}

/// ACCEPTANCE CLAUSE (2), and the one that matters: `a(?x), b(?y)` over two facts
/// each still returns FOUR. The pairs `(1,1)` and `(1,2)` agree on the FIRST goal
/// and differ on the second — the projection is onto the whole goal VECTOR, so
/// they are two answers.
///
/// A GENUINE TWO-GOAL QUERY, not a one-goal wrapper rule around a conjunction,
/// and that is the whole point: the wrong fixes are wrong about the QUERY's shape,
/// so a `pair(?x, ?y) :- a(?x), b(?y)` wrapper — one goal, one choice point over
/// one rule — cannot show it. `kb.resolve` takes a goal SLICE, which is how the
/// conjunction is spelled here.
///
/// CONTROL, MEASURED — this test is a guard on the LOSING direction (an answer
/// silently DROPPED), so it is red only for the wrong fixes, and green for both
/// the shipped one and the nearest-ancestor code it replaced:
///  - SCAN ALL ANCESTORS instead of returning at the nearest: `[(1,1), (2,1)]` —
///    two answers, not four. `(1,1)` and `(1,2)` both fingerprint `a(1)` at the
///    still-live `a(?x)` choice point, so the second is DISCARDED.
///  - TAKE THE OUTERMOST CHOICE POINT instead of the nearest: `[(1,1), (2,1)]`
///    again, for the same reason — for a query that IS a conjunction the outermost
///    choice point is `a(?x)`.
/// Both measured by editing `is_duplicate_answer` to each shape in turn (with the
/// per-frame `seen_goals` set restored). `an_existential_body_var_does_not_multiply_answers`
/// PASSES under both, and this one passes under the nearest-ancestor code — the
/// pair is only complete together.
///
/// SCAN-ALL also reddens four `wi739_guard_generator_delay_test` rows (9→3, 6→3,
/// `[2,3]`→`[2]`, and the six ordered pairs down to three), so that variant has
/// several witnesses. OUTERMOST reddens NOTHING ELSE in the workspace — this test
/// is its only witness, which is the reason it exists as a written test rather
/// than a note.
#[test]
fn a_conjunctive_query_keeps_every_pairing() {
    let mut kb = crate::common::load_kb_with(
        "namespace test.ffpgd_conj\n\
         \x20 sort Row  entity r(k: Int64, v: Int64)  end\n\
         \x20 fact r(k: 1, v: 1)\n\
         \x20 fact r(k: 1, v: 2)\n\
         \x20 fact r(k: 2, v: 1)\n\
         \x20 fact r(k: 2, v: 2)\n\
         \x20 rule a(?x) :- r(k: 1, v: ?x)\n\
         \x20 rule b(?y) :- r(k: 2, v: ?y)\n\
         end\n",
    );
    let (goal_a, x) = unary_goal(&mut kb, "test.ffpgd_conj.a", "x");
    let (goal_b, y) = unary_goal(&mut kb, "test.ffpgd_conj.b", "y");
    // PREMISE, asserted rather than assumed: the fixture really does offer two
    // answers per goal. Without it a `4` could come from a KB with four `a` rows
    // and a `b` that never matched, and the pairing claim would measure nothing.
    assert_eq!(
        (
            kb.resolve(&[goal_a], &ResolveConfig::default()).len(),
            kb.resolve(&[goal_b], &ResolveConfig::default()).len(),
        ),
        (2, 2),
        "premise: each goal alone has two answers",
    );
    let sols = kb.resolve(&[goal_a, goal_b], &ResolveConfig::default());
    let mut pairs: Vec<(i64, i64)> = sols
        .iter()
        .map(|s| (int_answer(&mut kb, x, s), int_answer(&mut kb, y, s)))
        .collect();
    pairs.sort();
    assert_eq!(
        pairs,
        vec![(1, 1), (1, 2), (2, 1), (2, 2)],
        "every pairing is a distinct answer to a two-goal query",
    );
}

/// An ANONYMOUS var in the QUERY still distinguishes answers, and that is
/// deliberate rather than an oversight of the projection.
///
/// `?` is existential wherever it is written, so the symmetry argument says
/// `seen(?t, ?)` should collapse just as `tagged(?t)` does. It does not, because
/// a query var IS observable however it was spelled: the CLI prints its binding
/// (`?t = ok, ?_ = 2`), and collapsing would drop a row the caller can see.
/// Distinguishing is also the FAIL-OPEN side — a duplicate answer, never a lost
/// one — which is the side both of this predicate's guards already take.
///
/// PASSES EITHER WAY BY DESIGN: the nearest-ancestor projection also reported 3
/// here. Pinned so the line is a decision with a reason at its site, not an
/// accident waiting to be "fixed" into an over-dedup.
#[test]
fn an_anonymous_query_var_is_still_part_of_the_answer() {
    let mut kb = crate::common::load_kb_with(
        "namespace test.ffpgd_anon_query\n\
         \x20 sort Tag    entity ok    entity fail  end\n\
         \x20 sort Row    entity check(t: Tag, witness: Int64) end\n\
         \x20 fact check(t: ok(),   witness: 1)\n\
         \x20 fact check(t: ok(),   witness: 2)\n\
         \x20 fact check(t: fail(), witness: 3)\n\
         \x20 rule seen(?t, ?w) :- check(t: ?t, witness: ?w)\n\
         end\n",
    );
    let seen = kb.resolve_symbol("test.ffpgd_anon_query.seen");
    let t = fresh_var_term(&mut kb, "t");
    // The resolver sees no difference between `?` and `?w`: both arrive as a
    // fresh `Var::Global`, which is exactly why the projection cannot single an
    // anonymous one out even if it wanted to.
    let anon = fresh_var_term(&mut kb, "_");
    let goal = kb.alloc(Term::Fn {
        functor: seen,
        pos_args: SmallVec::from_slice(&[t, anon]),
        named_args: SmallVec::new(),
    });
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(
        sols.len(),
        3,
        "a query var is part of the answer however it is spelled",
    );
}

/// A DROPPED DUPLICATE IS STILL A PROOF, and the choice point that produced it
/// must be told so. Found by `/code-review` on this ticket's own diff.
///
/// `child_solutions` has one reader — `step_choice_point`'s
/// `child_solutions == 0 && any_delayed` delay fallback — and it asks whether THIS
/// choice point produced a proof. Checking `is_duplicate_answer` before
/// `record_solution_in_nearest_choice_point` left it at zero for a branch that had
/// definitely succeeded, so the choice point rotated and residualized a FLOUNDERED
/// answer over a proof it already had.
///
/// The old order was safe BY CONSTRUCTION, and the construction is what this ticket
/// removed: dedup keyed the nearest ancestor ChoicePoint's OWN `seen_goals`, so a
/// duplicate implied an earlier solution had passed through that very frame and
/// already incremented it. `seen_answers` is stream-global, so a duplicate can now
/// arrive from a different subtree and leave the innermost live choice point at
/// zero — which is exactly what the fixture below builds.
///
/// THE FIXTURE, and every part of it is load-bearing. `g` has TWO rows so `inner`
/// is entered twice under two different `?y`; both entries answer `?x = 5`, so the
/// SECOND is the cross-subtree duplicate. `inner`'s rule clause leads with
/// `nonvar(?x)` on a caller var, which is one of the three NON-reorderable builtins
/// (`builtin_is_reorderable`: `NonVar`/`Ground`/`HoApply`) — so the open-time
/// pre-check delays that candidate and sets `any_delayed` on the `inner` choice
/// point (it is `anthill.reflect.nonvar`, and the import is REQUIRED — a bare
/// spelling is WI-1034's "rule-body goal names nothing" load error, not a silent
/// no-op). Its `ans(v: ?x)` conjunct has a fact, so WI-670 does not refute it away
/// first. `top` is what puts the `g` choice point ABOVE the `inner` one, so the
/// nearest ancestor at the yield is `inner`'s and it is a FRESH frame per `?y`.
///
/// `inner`'s ANSWERING clauses ARE FACTS, and that is not cosmetic — it is what
/// makes this fixture measure THIS ticket. `record_solution_in_nearest_choice_point`
/// credits the NEAREST choice point only, so if the answering clause had a body
/// (`rule inner(?y, ?x) :- ans(v: ?x)`) the goal `ans(v: ?x)` would open its own
/// choice point, take the credit, and leave `inner`'s counter at zero in BOTH
/// branches — spurious residuals with dedup on OR off. MEASURED on exactly that
/// fixture: 4 solutions `[0,1,0,1]` in proof mode, 3 `[0,1,1]` in answer mode. That
/// is a SEPARATE, pre-existing defect (the plural name over a `return`-at-the-first
/// walk, which this ticket's own description called "only a counter" and which in
/// fact manufactures a floundered answer); a bodyless clause pushes no intervening
/// choice point, so here the counter reaches `inner` and the only variable left is
/// the dedup ordering.
///
/// CONTROL, MEASURED by swapping the two statements back in `step_init`: 2
/// solutions, residual lengths `[0, 1]` — a definite `?x = 5` plus a FLOUNDERED
/// "conditional" answer to a question already definitely answered. The count and
/// `is_definite` are asserted separately because they fail for different reasons: a
/// fix that suppressed the residual without counting the proof would keep the count
/// at 1 by accident. Nothing else in the workspace reddens under that back-out,
/// which is why this test exists — the defect is latent, not caught by the suite.
#[test]
fn a_dropped_duplicate_still_counts_as_this_choice_points_proof() {
    let mut kb = crate::common::load_kb_with(
        "namespace test.ffpgd_child_count\n\
         \x20 import anthill.reflect.{nonvar}\n\
         \x20 sort N  entity g(v: Int64)    end\n\
         \x20 sort A  entity ans(v: Int64)  end\n\
         \x20 fact g(v: 1)\n\
         \x20 fact g(v: 2)\n\
         \x20 fact ans(v: 5)\n\
         \x20 fact inner(1, 5)\n\
         \x20 fact inner(2, 5)\n\
         \x20 rule inner(?y, ?x) :- nonvar(?x), ans(v: ?x)\n\
         \x20 rule top(?x) :- g(v: ?y), inner(?y, ?x)\n\
         end\n",
    );
    let (goal, x) = unary_goal(&mut kb, "test.ffpgd_child_count.top", "x");
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    let residuals: Vec<usize> = sols.iter().map(|s| s.residual.len()).collect();
    assert_eq!(
        sols.len(),
        1,
        "one answer, once — got {} with residual lengths {residuals:?}",
        sols.len(),
    );
    assert!(
        sols[0].is_definite(),
        "the answer is PROVED, not conditional — residual {:?}",
        sols[0].residual.len(),
    );
    assert_eq!(int_answer(&mut kb, x, &sols[0]), 5, "and it is 5");
}

// ── helpers ─────────────────────────────────────────────────────────────────

/// A fresh `Var::Global` term named `name`.
fn fresh_var_term(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    kb.alloc(Term::Var(Var::Global(vid)))
}

/// The goal `<qn>(?<var>)` and the var term it binds.
fn unary_goal(kb: &mut KnowledgeBase, qn: &str, var: &str) -> (TermId, TermId) {
    let functor = kb.resolve_symbol(qn);
    let arg = fresh_var_term(kb, var);
    let goal = kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::from_elem(arg, 1),
        named_args: SmallVec::new(),
    });
    (goal, arg)
}

/// The `i64` this solution binds `var` to, read CARRIER-NEUTRALLY — a fact loaded
/// from source answers on the hash-consed `Term` carrier, a value-built one on
/// `Value::Int`, and this test is about the count, not the carrier. PANICS on
/// anything else: a non-`Int` answer is a failure to report, not a row to drop.
fn int_answer(
    kb: &mut KnowledgeBase,
    var: TermId,
    sol: &anthill_core::kb::resolve::Solution,
) -> i64 {
    match kb.reify(var, &sol.subst) {
        eval::Value::Int(n) => n,
        eval::Value::Term { id, .. } => match kb.get_term(id) {
            Term::Const(Literal::Int(n)) => *n,
            other => panic!("expected an Int answer, got {other:?}"),
        },
        other => panic!("expected an Int answer, got {other:?}"),
    }
}
