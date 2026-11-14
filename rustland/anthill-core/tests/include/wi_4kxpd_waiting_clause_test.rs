//! WI-20260820-4KXPD — a clause that waits is asked again, and alone.
//!
//! A clause whose body asks the caller a question only the caller can answer —
//! `nonvar(?x)` over the caller's `?x` — does not open: it WAITS. Once the goal's
//! other candidates have answered, the goal goes behind the caller's remaining goals
//! and is asked again of that clause alone. If the caller binds the variable, the
//! clause runs; if nothing does, its answer is conditional on the clause's body.
//! Decided with the user 2026-11-14: the waiting clause is kept whatever its
//! siblings answered, and narrowed to itself.
//!
//! Before, the goal was rotated only when its choice point had been credited with
//! no solution, and the credit reached it only when no other choice point stood
//! between it and the solution — so a sibling clause WITH a body hid it, and the
//! same relation written with a bodyless sibling did not. The rotated goal was the
//! whole goal: it re-ran the clauses that had answered and floundered as the whole
//! goal. And a proof that finished after any delay left through the flounder exit,
//! past answer dedup and, under `definite_only`, dropped.
//!
//! CONTROLS, measured 2026-11-14 with this file run at the parent commit and with three
//! temporary switches in one build, each backing out one part: the empty-goals exit
//! (a proof with no goals left taken for a floundered branch), the clause restriction
//! (the whole goal asked again), and the residual narrowing (the goal as residual).
//! Each test says at its site which of the four redden it.

use anthill_core::eval::Value;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, TermId, Var};
use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::print::TermPrinter;
use smallvec::SmallVec;

/// The ticket's program: `inner`'s first clause answers `?x = 5` through a body, its
/// second waits on `?x`, and nothing after `inner` in `top` binds `?x`.
const FIXTURE: &str = "namespace test.kxpd_fixture\n\
     \x20 import anthill.reflect.{nonvar}\n\
     \x20 sort N  entity g(v: Int64)    end\n\
     \x20 sort A  entity ans(v: Int64)  end\n\
     \x20 fact g(v: 1)\n\
     \x20 fact g(v: 2)\n\
     \x20 fact ans(v: 5)\n\
     \x20 rule inner(?y, ?x) :- ans(v: ?x)\n\
     \x20 rule inner(?y, ?x) :- nonvar(?x), ans(v: ?x)\n\
     \x20 rule top(?x) :- g(v: ?y), inner(?y, ?x)\n\
     end\n";

/// The same relation with its answering clause written as facts — the shape that
/// used to credit `inner`'s choice point and drop the waiting clause in silence.
const TWIN: &str = "namespace test.kxpd_twin\n\
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
     end\n";

/// The caller binds what the waiting clause waits on: `pick` gives 5 and 7, the first
/// clause answers 5 and the waiting one answers 7 once `pick` has bound `?x`.
const CALLER_BINDS: &str = "namespace test.kxpd_binds\n\
     \x20 import anthill.reflect.{nonvar}\n\
     \x20 sort A  entity ans(v: Int64)   end\n\
     \x20 sort O  entity other(v: Int64) end\n\
     \x20 sort P  entity pick(v: Int64)  end\n\
     \x20 fact ans(v: 5)\n\
     \x20 fact other(v: 7)\n\
     \x20 fact pick(v: 5)\n\
     \x20 fact pick(v: 7)\n\
     \x20 rule inner(?y, ?x) :- ans(v: ?x)\n\
     \x20 rule inner(?y, ?x) :- nonvar(?x), other(v: ?x)\n\
     \x20 rule top(?x) :- inner(1, ?x), pick(v: ?x)\n\
     \x20 rule both(?x) :- top(?x), other(v: ?x)\n\
     \x20 rule first(?x) :- inner(1, ?x), !\n\
     end\n";

/// The example of kernel-language §8.3: the goal that waits is the query itself.
const SPEC_EXAMPLE: &str = "namespace test.kxpd_spec\n\
     \x20 import anthill.reflect.{nonvar}\n\
     \x20 sort A  entity ans(v: Int64)  end\n\
     \x20 fact ans(v: 5)\n\
     \x20 rule inner(?x) :- ans(v: ?x)\n\
     \x20 rule inner(?x) :- nonvar(?x), ans(v: ?x)\n\
     end\n";

/// Two waiting clauses and one answering one.
const TWO_WAITING: &str = "namespace test.kxpd_two\n\
     \x20 import anthill.reflect.{nonvar}\n\
     \x20 sort A  entity a(v: Int64)    end\n\
     \x20 sort B  entity b(v: Int64)    end\n\
     \x20 sort P  entity pick(v: Int64) end\n\
     \x20 fact a(v: 5)\n\
     \x20 fact b(v: 7)\n\
     \x20 fact pick(v: 5)\n\
     \x20 fact pick(v: 7)\n\
     \x20 fact pick(v: 9)\n\
     \x20 rule w(?x) :- nonvar(?x), a(v: ?x)\n\
     \x20 rule w(?x) :- nonvar(?x), b(v: ?x)\n\
     \x20 fact w(9)\n\
     \x20 rule picked(?x) :- w(?x), pick(v: ?x)\n\
     end\n";

/// One row of an answer set: the query variables' values, and the residual (empty for
/// a definite answer), each printed.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Row {
    answer: Vec<String>,
    residual: String,
}

impl Row {
    fn definite(&self) -> bool {
        self.residual.is_empty()
    }
}

/// Resolve `<qn>(?v1, …)` under `config` and print every solution.
fn rows(kb: &mut KnowledgeBase, qn: &str, arity: usize, config: &ResolveConfig) -> Vec<Row> {
    let functor = kb.resolve_symbol(qn);
    let vars: Vec<TermId> = (0..arity)
        .map(|i| {
            let sym = kb.intern(&format!("v{i}"));
            let vid = kb.fresh_var(sym);
            kb.alloc(Term::Var(Var::Global(vid)))
        })
        .collect();
    let goal = kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::from_slice(&vars),
        named_args: SmallVec::new(),
    });
    let sols = kb.resolve(&[goal], config);
    let mut out = Vec::new();
    for sol in &sols {
        let values: Vec<Value> = vars.iter().map(|v| kb.reify(*v, &sol.subst)).collect();
        let printer = TermPrinter::new(kb);
        out.push(Row {
            answer: values.iter().map(|v| printer.print_value(v)).collect(),
            residual: sol
                .residual
                .iter()
                .map(|g| printer.print_value(g))
                .collect::<Vec<_>>()
                .join(", "),
        });
    }
    out
}

fn answers() -> ResolveConfig {
    ResolveConfig::default()
}

fn proofs() -> ResolveConfig {
    // A PROOF COUNT: each proof is yielded, as the relation layer reads the stream.
    ResolveConfig {
        dedup_answers: false,
        ..ResolveConfig::default()
    }
}

fn definite_values(rows: &[Row]) -> Vec<String> {
    let mut v: Vec<String> = rows.iter().filter(|r| r.definite()).map(|r| r.answer.join(" ")).collect();
    v.sort();
    v
}

fn conditional(rows: &[Row]) -> Vec<&Row> {
    rows.iter().filter(|r| !r.definite()).collect()
}

/// The residual is the waiting clause's body — `nonvar(?_), ans(v: ?_)` — and not the
/// goal `inner(…)`, whose other clause has already answered `?x = 5`.
fn assert_clause_body(row: &Row, body_goal: &str) {
    assert!(
        row.residual.starts_with("nonvar(") && row.residual.contains(&format!("{body_goal}(")),
        "the residual is the waiting clause's body, got {row:?}",
    );
    assert!(!row.residual.contains("inner("), "not the whole goal, got {row:?}");
}

/// Acceptance (1), as decided: `?x = 5` once and definite, and the waiting clause's
/// answer kept, one per `?y`, narrowed to its body. In proof mode the definite answer
/// is proved once per `?y` and never a second time by the rotation.
///
/// FAILS at the parent commit, with the whole goal asked again and with the residual
/// narrowing backed out: the conditional answers' residual is `inner(1, ?_)`. Passes
/// with the empty-goals exit backed out: nothing finishes after a delay here.
#[test]
fn the_waiting_clause_is_kept_narrowed_to_its_body() {
    let mut kb = crate::common::load_kb_with(FIXTURE);
    for (mode, config, definite) in [("answer", answers(), vec!["5"]), ("proof", proofs(), vec!["5", "5"])] {
        let rows = rows(&mut kb, "test.kxpd_fixture.top", 1, &config);
        assert_eq!(definite_values(&rows), definite, "{mode} mode: {rows:?}");
        let cond = conditional(&rows);
        assert_eq!(cond.len(), 2, "{mode} mode: one conditional answer per `?y`: {rows:?}");
        for row in cond {
            assert_clause_body(row, "ans");
        }
    }
}

/// A relation reads the same whether its answering clause has a body or is a fact.
///
/// FAILS at the parent commit: the twin answered `?x = 5` alone, its waiting clause
/// dropped because the solution's credit reached `inner`'s choice point. Passes under
/// each of the three switches, by design: each reads the two spellings alike.
#[test]
fn a_bodyless_sibling_reads_as_a_bodied_one() {
    let mut fixture = crate::common::load_kb_with(FIXTURE);
    let mut twin = crate::common::load_kb_with(TWIN);
    for config in [answers(), proofs()] {
        let mut a = rows(&mut fixture, "test.kxpd_fixture.top", 1, &config);
        let mut b = rows(&mut twin, "test.kxpd_twin.top", 1, &config);
        a.sort();
        b.sort();
        assert_eq!(a, b, "one relation, two spellings");
    }
}

/// Acceptance (2): the caller binds the variable and the waiting clause answers — and
/// the clause that answered first is not asked again.
///
/// FAILS at the parent commit (answer mode `5, 5, 7`: the second `5` re-derived by the
/// rotated whole goal and let past dedup by the empty-goals exit) and with the whole
/// goal asked again (proof mode `5, 7, 5`). Passes with the empty-goals exit backed out
/// alone — the duplicate is the whole goal's; the exit only let it past dedup — and with
/// the residual narrowing backed out. Counting every solution below the choice point,
/// the other fix the ticket named, lost `?x = 7` (measured through the CLI).
#[test]
fn a_waiting_clause_answers_once_the_caller_binds_its_variable() {
    let mut kb = crate::common::load_kb_with(CALLER_BINDS);
    for (mode, config) in [("answer", answers()), ("proof", proofs())] {
        let rows = rows(&mut kb, "test.kxpd_binds.top", 1, &config);
        assert_eq!(rows.len(), 2, "{mode} mode: one proof of each answer: {rows:?}");
        assert_eq!(definite_values(&rows), vec!["5", "7"], "{mode} mode: {rows:?}");
    }
}

/// An answer found after a rotation is a definite answer: a definite-only search —
/// what a constraint, a guard and a proof read — keeps it.
///
/// FAILS at the parent commit and with the empty-goals exit backed out: the search
/// answered nothing, and the `no` constraint, which the query violates, loaded clean.
/// Passes under the other two switches.
#[test]
fn an_answer_found_after_a_rotation_is_definite() {
    let mut kb = crate::common::load_kb_with(CALLER_BINDS);
    let definite_only = ResolveConfig {
        definite_only: true,
        ..ResolveConfig::default()
    };
    let rows = rows(&mut kb, "test.kxpd_binds.both", 1, &definite_only);
    assert_eq!(definite_values(&rows), vec!["7"], "{rows:?}");

    let violated = CALLER_BINDS.replace(
        "end\n",
        "  constraint never_other: no ?x -: top(?x), other(v: ?x)\nend\n",
    );
    let errors = crate::common::load_errors_of(&violated);
    assert!(
        errors.iter().any(|e| e.contains("never_other")),
        "the constraint is violated by `?x = 7`: {errors:?}",
    );
}

/// The kernel-language §8.3 example: `?x = 5`, and conditionally the waiting clause's
/// body, in the query's own variable.
///
/// FAILS at the parent commit, with the whole goal asked again and with the residual
/// narrowing backed out: the residual is `inner(?v0)`.
#[test]
fn the_residual_is_the_clause_body_in_the_querys_variables() {
    let mut kb = crate::common::load_kb_with(SPEC_EXAMPLE);
    let rows = rows(&mut kb, "test.kxpd_spec.inner", 1, &answers());
    assert_eq!(definite_values(&rows), vec!["5"], "{rows:?}");
    let cond = conditional(&rows);
    assert_eq!(cond.len(), 1, "{rows:?}");
    assert_eq!(cond[0].answer, vec!["?v0"], "`?x` stays the query's, unbound: {rows:?}");
    assert_eq!(cond[0].residual, "nonvar(?v0), ans(v: ?v0)", "{rows:?}");
}

/// With nothing to bind `?x`, one conditional answer per waiting clause, each its own
/// body; the fact answers once.
///
/// FAILS at the parent commit (no conditional answer: the fact's solution credited the
/// choice point and both waiting clauses were dropped), and with the whole goal asked
/// again or the residual narrowing backed out (two conditional answers, each `w(?v0)`).
#[test]
fn each_waiting_clause_is_its_own_conditional_answer() {
    let mut kb = crate::common::load_kb_with(TWO_WAITING);
    let rows = rows(&mut kb, "test.kxpd_two.w", 1, &proofs());
    assert_eq!(definite_values(&rows), vec!["9"], "{rows:?}");
    let mut residuals: Vec<&str> = conditional(&rows).iter().map(|r| r.residual.as_str()).collect();
    residuals.sort();
    assert_eq!(residuals, vec!["nonvar(?v0), a(v: ?v0)", "nonvar(?v0), b(v: ?v0)"], "{rows:?}");
}

/// With a caller that binds `?x`, each waiting clause answers once, and the fact once.
///
/// FAILS at the parent commit (`9` proved twice: the rotated whole goal asked the fact
/// again) and with the whole goal asked again (`5, 5, 7, 7, 9, 9, 9`: each waiting clause's
/// branch asked all three). Passes under the other two switches.
#[test]
fn each_waiting_clause_answers_once_the_caller_binds() {
    let mut kb = crate::common::load_kb_with(TWO_WAITING);
    let rows = rows(&mut kb, "test.kxpd_two.picked", 1, &proofs());
    assert_eq!(definite_values(&rows), vec!["5", "7", "9"], "{rows:?}");
    assert!(conditional(&rows).is_empty(), "{rows:?}");
}

/// The narrowed residual carries the clause's head match: a goal variable the head
/// binds to a structure reads as that structure in the conditional answer.
///
/// FAILS at the parent commit, with the whole goal asked again and with the residual
/// narrowing backed out: `?v1` is unbound and the residual is `cl(?v0, ?v1)`.
#[test]
fn the_narrowed_residual_carries_the_head_match() {
    let mut kb = crate::common::load_kb_with(
        "namespace test.kxpd_link\n\
         \x20 import anthill.reflect.{nonvar}\n\
         \x20 sort A  entity a(v: Int64)  end\n\
         \x20 sort F  entity f(z: Int64)  end\n\
         \x20 fact a(v: 5)\n\
         \x20 rule cl(?z, f(z: ?z)) :- nonvar(?z), a(v: ?z)\n\
         end\n",
    );
    let rows = rows(&mut kb, "test.kxpd_link.cl", 2, &answers());
    assert_eq!(rows.len(), 1, "{rows:?}");
    assert_eq!(rows[0].answer, vec!["?v0", "f(z: ?v0)"], "the head's `f(z: ?z)` is the answer: {rows:?}");
    assert_eq!(rows[0].residual, "nonvar(?v0), a(v: ?v0)", "{rows:?}");
}

/// Under the `@[simp]` resolution phase a waiting clause reads as it does in the plain
/// search: the restricted ask and the narrowed residual select through the same
/// `rule_candidates` as the first ask. (The rewrite itself does not fire here — it fires
/// only for a goal with no clause candidate, and the waiting clause is one.)
///
/// FAILS with the whole goal asked again and with the residual narrowing backed out, as
/// its plain twin `the_residual_is_the_clause_body_in_the_querys_variables` does; passes
/// with the empty-goals exit backed out. Not run at the parent commit.
#[test]
fn the_waiting_clause_reads_the_same_under_simplify() {
    let mut kb = crate::common::load_kb_with(SPEC_EXAMPLE);
    let simplify = ResolveConfig {
        simplify: true,
        ..ResolveConfig::default()
    };
    let mut plain = rows(&mut kb, "test.kxpd_spec.inner", 1, &answers());
    let mut simp = rows(&mut kb, "test.kxpd_spec.inner", 1, &simplify);
    plain.sort();
    simp.sort();
    assert_eq!(simp, plain);
    assert_eq!(conditional(&simp).len(), 1, "{simp:?}");
    assert_eq!(conditional(&simp)[0].residual, "nonvar(?v0), ans(v: ?v0)", "{simp:?}");
}

/// A cut prunes a waiting clause as it prunes any other candidate of the goal: `first`
/// commits to `inner`'s first answer, so the waiting clause is not asked.
///
/// Passes at the parent commit and under the three switches, by design: it holds the
/// waiting clauses inside the choice point a cut prunes, where a branch pushed beside it
/// would escape the cut.
#[test]
fn a_cut_prunes_a_waiting_clause() {
    let mut kb = crate::common::load_kb_with(CALLER_BINDS);
    let rows = rows(&mut kb, "test.kxpd_binds.first", 1, &proofs());
    assert_eq!(rows.len(), 1, "{rows:?}");
    assert_eq!(definite_values(&rows), vec!["5"], "{rows:?}");
}

/// Acceptance (3): a variable nothing can bind still flounders.
///
/// Passes at the parent commit and under the three switches, by design.
#[test]
fn an_honest_flounder_still_flounders() {
    let mut kb = crate::common::load_kb_with(
        "namespace test.kxpd_honest\n\
         \x20 import anthill.prelude.PartialEq.{neq}\n\
         \x20 rule unbindable(?x) :- neq(?x, 1)\n\
         end\n",
    );
    let rows = rows(&mut kb, "test.kxpd_honest.unbindable", 1, &answers());
    assert_eq!(rows.len(), 1, "{rows:?}");
    assert!(!rows[0].definite(), "{rows:?}");
}
