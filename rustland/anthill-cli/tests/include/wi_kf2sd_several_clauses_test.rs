//! WI-20261012-KF2SD — A CALL IN A PROVED BODY IS READ BY THE ONE CLAUSE THAT CAN
//! ANSWER IT, AND REFUSED WHERE SEVERAL CAN.
//!
//! A rule call in the body of a `by z3` proof is a hypothesis, and a predicate of
//! several clauses holds when any of them does. The emitter read such a call as ONE
//! clause — the first fact its arguments agreed with, else the first clause with a
//! body — so
//!
//!   rule related(?a, ?b) :- gte(?a, ?b)
//!   rule related(?a, ?b) :- lte(?a, ?b)
//!   rule lemma: gte(?a, ?b) :- related(?a, ?b)        proof lemma by z3 end
//!
//! was `✓ proved`, which `related(1, 2)` refutes; and so was `gte(?d, 0.0) :- start(?d)`
//! over `fact start(5.0)`, `fact start(-1.0)`.
//!
//! Now (decided with the user, 2026-10-13, on the count in
//! `docs/measurements/test-infrastructure/several-clauses-2026-10-13.txt`):
//!
//!   * the clauses that CAN answer a call are those of its arity whose head no argument
//!     of the call rules out — a number against another number, a constructor against
//!     another constructor; a variable and a computed term rule nothing out;
//!   * exactly one: the call is read by it, as it was;
//!   * several: REFUSED, naming the predicate and how many. Their disjunction is what
//!     the call means, and is WI-20261013-1KF32;
//!   * none: refused too — the body never holds, and no proof is of that.
//!
//! The one predicate of several clauses that any proof of lf1 or of the suites read was
//! lf1's `real_pose_at/3` — two base facts and a step whose head is all variables — in
//! its four top-level safety proofs, each of which read it as a base fact. lf1 now has
//! the launch geometry as `initial_pose`, and those four read that.
//!
//! /code-review found the same reading in two more places, which are refused by the
//! same rule: THE RULE BEING PROVED, where its name is several clauses (a rule written
//! with several heads; a predicate written as several rules), and AN ENTITY PREMISE
//! over an entity of several facts. And it found what selecting a clause by the call's
//! arguments needs of the frame they are read in (the rows from
//! `a_proof_of_a_rule_of_several_clauses_is_refused` on).
//!
//! EVERY ROW BUT `the_verdicts_of_what_is_read_are_as_they_were` RUNS `--dry-run` and
//! reads the document or the refusal, so none passes for want of a solver.
//!
//! WHAT FAILS WHEN THE CHANGE IS BACKED OUT (measured; part by part in the measurement
//! file's §4). With the emitter as it was — the first fact that agrees, else the first
//! clause with a body — 15 of these 17 rows FAIL. Two PASS EITHER WAY, by design:
//!   * `a_call_one_clause_answers_is_read_as_it_was` — the control: the documents the
//!     change must not move;
//!   * `lf1s_proofs_read_the_launch_geometry_and_not_the_recursion` — which fails with
//!     lf1 AS IT WAS, whatever the emitter: it holds the model, not the reading.
//! `the_verdicts_of_what_is_read_are_as_they_were` fails when EITHER is backed out: a
//! refusal is in its count, and lf1's fourteen are.

use std::path::PathBuf;

use crate::common::{anthill, prove_dry_run, write_temp, z3_available, Output};

/// A dry run of `src`, in a file of this suite's own (the rows of one binary share a
/// directory of temporary files, named by the process and `name`).
fn dry_run(name: &str, src: &str) -> Output {
    prove_dry_run(&format!("kf2sd_{name}"), src)
}

fn errors(out: &Output) -> Vec<&str> {
    out.diagnostics("error:").collect()
}

/// The assertions of the proof `rule`'s document, in order.
fn assertions<'a>(out: &'a Output, rule: &str) -> Vec<&'a str> {
    let banner = format!("--- {rule} ---");
    let lines: Vec<&str> = out
        .stdout
        .lines()
        .skip_while(|l| *l != banner)
        .skip(1)
        .take_while(|l| !l.starts_with("------"))
        .collect();
    assert!(
        !lines.is_empty(),
        "`{rule}` has a document; stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    lines
        .into_iter()
        .filter(|l| l.starts_with("(assert "))
        .collect()
}

/// The one error of `out` that names `rule`, which has no document.
fn refusal<'a>(out: &'a Output, rule: &str) -> &'a str {
    let said: Vec<&str> = errors(out)
        .into_iter()
        .filter(|e| e.contains(&format!("error: {rule}: ")))
        .collect();
    assert_eq!(said.len(), 1, "one error names `{rule}`; stderr:\n{}", out.stderr);
    assert!(
        !out.stdout.contains(&format!("--- {rule} ---")),
        "`{rule}` has no document:\n{}",
        out.stdout
    );
    said[0]
}

/// The refusal of a call that `facts` facts and `bodied` clauses with a body can answer.
fn refused_as_several(out: &Output, rule: &str, relation: &str, facts: usize, bodied: usize) {
    let said = refusal(out, rule);
    let how_many = format!(
        "the call of `{relation}` can be answered by {} clauses of the predicate \
         ({facts} fact(s), {bodied} with a body)",
        facts + bodied
    );
    assert!(
        said.contains(&how_many) && said.contains("WI-20261013-1KF32"),
        "expected `{how_many}`, got:\n{said}"
    );
}

/// THE TICKET'S TWO CASES, as filed. Each proved; each is refused, and no document is
/// written for it.
#[test]
fn a_call_several_clauses_can_answer_is_refused() {
    let out = dry_run(
        "rules",
        r#"
namespace test.kf2sd.rules
  import anthill.prelude.PartialOrd.{gte, lte}

  rule related(?a, ?b) :- gte(?a, ?b)
  rule related(?a, ?b) :- lte(?a, ?b)

  rule lemma: gte(?a, ?b) :- related(?a, ?b)
  proof lemma by z3 end
end
"#,
    );
    refused_as_several(&out, "test.kf2sd.rules.lemma", "test.kf2sd.rules.related/2", 0, 2);

    let out = dry_run(
        "facts",
        r#"
namespace test.kf2sd.facts
  import anthill.prelude.PartialOrd.{gte, lte}

  fact start(5.0)
  fact start(-1.0)

  rule lemma: gte(?d, 0.0) :- start(?d)
  proof lemma by z3 end
end
"#,
    );
    refused_as_several(&out, "test.kf2sd.facts.lemma", "test.kf2sd.facts.start/1", 2, 0);
}

/// A FACT BESIDE A CLAUSE WITH A BODY IS TWO. The one-argument form read the body and
/// never looked at the fact; the other read the fact and never looked at the body.
/// `at/2` is lf1's `real_pose_at` in small: a base fact, and a step whose head is all
/// variables — which a ground argument does not rule out, so `at(0, ?x)` has two.
#[test]
fn a_fact_beside_a_clause_with_a_body_is_several() {
    let out = dry_run(
        "mixed",
        r#"
namespace test.kf2sd.mixed
  import anthill.prelude.PartialOrd.{gte, lte}

  fact cap(100.0)
  rule cap(?d) :- ?d = 2.0 + 3.0
  rule capped: lte(?d, 5.0) :- cap(?d)
  proof capped by z3 end

  fact at(0, 1.0)
  rule at(?k_next, ?x_next) :- at(?k, ?x), ?k_next = ?k + 1, ?x_next = ?x + 1.0
  rule base: lte(?x, 1.0) :- at(0, ?x)
  proof base by z3 end
end
"#,
    );
    refused_as_several(&out, "test.kf2sd.mixed.capped", "test.kf2sd.mixed.cap/1", 1, 1);
    refused_as_several(&out, "test.kf2sd.mixed.base", "test.kf2sd.mixed.at/2", 1, 1);
}

const TABLE: &str = r#"
namespace test.kf2sd.table
  import anthill.prelude.PartialOrd.{gte, lte}

  sort Drone
    entity Leader
    entity Follower
  end

  fact speed_of(Leader, 5.0)
  fact speed_of(Follower, 50.0)

  rule slow: lte(?v, 10.0) :- speed_of(Leader, ?v)
  proof slow by z3 end

  rule fast: gte(?v, 10.0) :- speed_of(Follower, ?v)
  proof fast by z3 end

  rule any: lte(?v, 10.0) :- speed_of(?who, ?v)
  proof any by z3 end
end
"#;

/// A GROUND ARGUMENT SELECTS AMONG FACTS, and a variable there does not. `slow` and
/// `fast` are each read by the fact of their drone — the second by the SECOND fact,
/// which no "first that matches" is — and `any`, which proved by the Leader's row, is
/// refused: it is a claim of both.
#[test]
fn a_ground_argument_selects_one_fact_and_a_variable_does_not() {
    let out = dry_run("table", TABLE);
    assert_eq!(
        assertions(&out, "test.kf2sd.table.slow"),
        ["(assert (not (<= 5.0 10.0)))"]
    );
    assert_eq!(
        assertions(&out, "test.kf2sd.table.fast"),
        ["(assert (not (>= 50.0 10.0)))"]
    );
    refused_as_several(&out, "test.kf2sd.table.any", "test.kf2sd.table.speed_of/2", 2, 0);
    assert_eq!(errors(&out).len(), 1, "stderr:\n{}", out.stderr);
}

/// A CONSTRUCTOR IN THE HEAD SELECTS AMONG CLAUSES WITH A BODY, as a ground argument
/// does among facts — by the call's own argument, and by what its variable is bound to.
/// The first bodied clause was read whatever the call, so `with_none` was "expects a
/// concrete `…some` construction": a loud mismatch where the second clause answers. A
/// variable nothing binds rules neither out.
#[test]
fn a_constructor_in_the_head_selects_one_clause_with_a_body() {
    let out = dry_run(
        "ctor",
        r#"
namespace test.kf2sd.ctor
  import anthill.prelude.PartialOrd.{gte, lte}
  import anthill.prelude.Option.{some, none}

  rule gain(some(?x), ?r) :- ?r = ?x + 1.0
  rule gain(none, ?r) :- ?r = 0.0

  rule with_some: gte(?r, 1.0) :- gain(some(0.0), ?r)
  proof with_some by z3 end

  rule with_none: lte(?r, 0.0) :- gain(none, ?r)
  proof with_none by z3 end

  rule bound_some: gte(?r, 3.0) :- ?o = some(2.0), gain(?o, ?r)
  proof bound_some by z3 end

  rule with_var: gte(?r, 0.0) :- gain(?o, ?r)
  proof with_var by z3 end
end
"#,
    );
    assert_eq!(
        assertions(&out, "test.kf2sd.ctor.with_some"),
        ["(assert (not (>= (+ 0.0 1.0) 1.0)))"]
    );
    assert_eq!(
        assertions(&out, "test.kf2sd.ctor.with_none"),
        ["(assert (not (<= 0.0 0.0)))"]
    );
    assert_eq!(
        assertions(&out, "test.kf2sd.ctor.bound_some"),
        ["(assert (not (>= (+ 2.0 1.0) 3.0)))"]
    );
    refused_as_several(&out, "test.kf2sd.ctor.with_var", "test.kf2sd.ctor.gain/2", 0, 2);
    assert_eq!(errors(&out).len(), 1, "stderr:\n{}", out.stderr);
}

/// A CLAUSE OF ANOTHER ARITY IS NO CANDIDATE: `span/2` beside `span/3` is two
/// predicates here. The first clause with a body was taken whichever the call was, so
/// `three` was "rule call arity mismatch for '…span': expected 2, got 3".
#[test]
fn a_clause_of_another_arity_answers_no_call() {
    let out = dry_run(
        "arity",
        r#"
namespace test.kf2sd.arity
  import anthill.prelude.PartialOrd.{gte, lte}

  rule span(?a, ?b) :- gte(?b, ?a)
  rule span(?a, ?b, ?c) :- gte(?b, ?a), gte(?c, ?b)

  rule two: gte(?b, ?a) :- span(?a, ?b)
  proof two by z3 end

  rule three: gte(?c, ?a) :- span(?a, ?b, ?c)
  proof three by z3 end
end
"#,
    );
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    assert_eq!(
        assertions(&out, "test.kf2sd.arity.two"),
        [
            "(assert (>= var_1 var_0))",
            "(assert (not (>= var_1 var_0)))"
        ]
    );
    assert_eq!(
        assertions(&out, "test.kf2sd.arity.three"),
        [
            "(assert (>= var_0 var_1))",
            "(assert (>= var_2 var_0))",
            "(assert (not (>= var_2 var_1)))"
        ]
    );
}

/// A CALL NO CLAUSE CAN ANSWER is a body that never holds, and is said so. It was
/// "unhandled body goal functor", which is what a name with no clause at all gets.
/// And a fact that CAN answer — nothing rules it out — but whose slot the call meets
/// with a term over variables is refused too: `?x + 1.0` against `5.0` is an equation,
/// and the fact so read would be the hypothesis without it. It was passed over as a
/// fact that did not match.
#[test]
fn a_call_that_is_answered_and_cannot_be_read_is_refused() {
    let out = dry_run(
        "unread",
        r#"
namespace test.kf2sd.unread
  import anthill.prelude.PartialOrd.{gte, lte}

  fact tab(1.0, 2.0)
  fact tab(3.0, 4.0)
  rule absent: gte(?v, 0.0) :- tab(7.0, ?v)
  proof absent by z3 end

  fact row(5.0, 1.0)
  rule computed: gte(?v, 0.0) :- row(?x + 1.0, ?v)
  proof computed by z3 end
end
"#,
    );
    let said = refusal(&out, "test.kf2sd.unread.absent");
    assert!(
        said.contains(
            "the call of `test.kf2sd.unread.tab/2` can be answered by no clause of the predicate"
        ) && said.contains("each of its 2"),
        "{said}"
    );
    let said = refusal(&out, "test.kf2sd.unread.computed");
    assert!(
        said.contains("the call of `test.kf2sd.unread.row` is answered by a fact")
            && said.contains("its argument 1 is a term the fact's slot is not compared with"),
        "{said}"
    );
}

/// THE REFUSAL NAMES THE RULE THE CALL STANDS IN, when that is not the proof's own:
/// `deep` calls `wrapper`, and it is `wrapper`'s body that calls `related`.
#[test]
fn a_refused_call_in_an_inlined_rule_names_that_rule() {
    let out = dry_run(
        "wrap",
        r#"
namespace test.kf2sd.wrap
  import anthill.prelude.PartialOrd.{gte, lte}

  rule related(?a, ?b) :- gte(?a, ?b)
  rule related(?a, ?b) :- lte(?a, ?b)
  rule wrapper(?a, ?b) :- related(?a, ?b), gte(?a, 0.0)

  rule deep: gte(?a, ?b) :- wrapper(?a, ?b)
  proof deep by z3 end
end
"#,
    );
    let said = refusal(&out, "test.kf2sd.wrap.deep");
    assert!(
        said.contains(
            "the call of `test.kf2sd.wrap.related/2`, in the body of \
             `test.kf2sd.wrap.wrapper` (read inlined), can be answered by 2 clauses"
        ),
        "{said}"
    );
}

/// THE CONTROL: a call exactly one clause answers is read as it was — by its body, by
/// its fact, and by the one-argument form. Passes with the change and without it, by
/// design: these are the documents the change must not move.
#[test]
fn a_call_one_clause_answers_is_read_as_it_was() {
    let out = dry_run(
        "one",
        r#"
namespace test.kf2sd.one
  import anthill.prelude.PartialOrd.{gte, lte}

  rule ordered(?a, ?b) :- gte(?a, ?b)
  rule by_body: gte(?a, ?b) :- ordered(?a, ?b)
  proof by_body by z3 end

  fact limit(5.0)
  rule by_fact: lte(?d, 5.0) :- limit(?d)
  proof by_fact by z3 end

  rule bound(?d) :- ?d = 2.0 + 3.0
  rule by_one: lte(?d, 5.0) :- bound(?d)
  proof by_one by z3 end
end
"#,
    );
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    assert_eq!(
        assertions(&out, "test.kf2sd.one.by_body"),
        [
            "(assert (>= var_1 var_0))",
            "(assert (not (>= var_1 var_0)))"
        ]
    );
    assert_eq!(
        assertions(&out, "test.kf2sd.one.by_fact"),
        ["(assert (not (<= 5.0 5.0)))"]
    );
    assert_eq!(
        assertions(&out, "test.kf2sd.one.by_one"),
        ["(assert (not (<= (+ 2.0 3.0) 5.0)))"]
    );
}

/// A CALL THAT IS NOT READ IS NOT REFUSED: the conclusion of a structured proof skips
/// its calls, whatever their clauses, and `related` here has two.
const SKIPPED: &str = r#"
namespace test.kf2sd.skipped
  import anthill.prelude.PartialOrd.{gte, lte}

  rule related(?a, ?b) :- gte(?a, ?b)
  rule related(?a, ?b) :- lte(?a, ?b)

  rule parent: gte(?a + 1.0, ?a) :- related(?a, ?b)
  proof parent
    rule kf_step: gte(?a + 1.0, ?a)
      by z3
    by z3
  end
end
"#;

fn lf1_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/webots-modelling/lf1")
}

/// NO PROOF OF lf1 IS REFUSED, and none reads `real_pose_at`. Its four top-level safety
/// proofs read the launch geometry — `initial_pose`, a predicate of facts alone, where
/// a ground drone selects one — and `real_pose_at`, which is that base clause and the
/// step, is called by no body a proof reads.
///
/// FAILS WITH lf1 AS IT WAS (`fact real_pose_at(0, Leader, …)` beside the step): the
/// four are refused, each naming `real_pose_at/3`. The emitter's change backed out, it
/// passes either way — which is the point: the model no longer leans on the reading.
#[test]
fn lf1s_proofs_read_the_launch_geometry_and_not_the_recursion() {
    let dir = lf1_dir();
    let out = anthill(&["prove", dir.to_str().unwrap(), "--dry-run", "--no-cache", "-v"]);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    for proof in [
        "gps.safety_min_distance",
        "gps.safety_max_distance",
        "transponder.safety_no_collision_transponder",
        "transponder.safety_bounded_excursion_transponder",
    ] {
        assert!(
            out.has_stdout_line(&format!("--- anthill.examples.lf1.safety.{proof} ---")),
            "`{proof}` has a document; stdout:\n{}",
            out.stdout
        );
    }
    let deps: Vec<&str> = out
        .stdout
        .lines()
        .filter(|l| l.trim_start().starts_with("deps: "))
        .collect();
    let reading = |name: &str| {
        deps.iter()
            .filter(|l| l.contains(&format!("anthill.examples.lf1.safety.common.{name}")))
            .count()
    };
    // A dependency is a rule a proof VISITED: read, or skipped and stated.
    assert_eq!(reading("real_pose_at"), 0, "{deps:#?}");
    assert_eq!(reading("initial_pose"), 4, "{deps:#?}");
}

/// THE VERDICTS, where there is a solver: what one clause answers proves as it did, a
/// structured proof whose conclusion skips a call of two clauses proves as it did, and
/// lf1 is fourteen proved.
#[test]
fn the_verdicts_of_what_is_read_are_as_they_were() {
    if !z3_available() {
        return;
    }
    let path = write_temp("kf2sd_v_table.anthill", TABLE);
    let out = anthill(&["prove", path.to_str().unwrap(), "--no-cache"]);
    for proved in ["test.kf2sd.table.slow", "test.kf2sd.table.fast"] {
        assert!(
            out.has_stdout_line(&format!("✓ {proved}: proved (z3: unsat)")),
            "stdout:\n{}\nstderr:\n{}",
            out.stdout,
            out.stderr
        );
    }
    assert!(
        out.has_stdout_line("summary: 2 proved, 1 failed, 0 skipped, 3 total"),
        "stdout:\n{}",
        out.stdout
    );

    let path = write_temp("kf2sd_v_skipped.anthill", SKIPPED);
    let out = anthill(&["prove", path.to_str().unwrap(), "--no-cache"]);
    assert!(
        out.has_stdout_line("✓ test.kf2sd.skipped.parent: proved (z3: unsat)"),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );

    let dir = lf1_dir();
    let out = anthill(&["prove", dir.to_str().unwrap(), "--no-cache"]);
    assert!(
        out.has_stdout_line("summary: 14 proved, 0 failed, 0 skipped, 14 total"),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}

// ── WHAT /code-review FOUND (the measurement file's §6) ──────────────────────────────
//
// The same reading in two more places — the rule being proved, and an entity premise —
// and what selecting a clause by the call's arguments needs of the frames it reads them
// in.

/// THE RULE BEING PROVED IS ONE CLAUSE, OR THE PROOF IS REFUSED. A rule written with
/// several heads is a clause for each under the one label, and a predicate written as
/// several rules is a clause for each: the first was read and the rest were not. `both`
/// proved by its first head — `gte(?x, 0.0)`, which the body gives — and its lift is of
/// every head, so `bad`, false at y = 1, proved by citing it; `viol` proved by its first
/// body, its second satisfiable.
#[test]
fn a_proof_of_a_rule_of_several_clauses_is_refused() {
    let out = dry_run(
        "heads",
        r#"
namespace test.kf2sd.heads
  import anthill.prelude.PartialOrd.{gte, lte}

  rule both: gte(?x, 0.0), gte(?x, 5.0) :- gte(?x, 1.0)
  proof both by z3 end

  rule bad: gte(?y, 5.0) :- gte(?y, 1.0)
  proof bad using both by z3 end

  rule viol(?w) :- gte(?w, 1.0), lte(?w, 0.0)
  rule viol(?w) :- gte(?w, 0.0)
  proof viol by z3 end

  rule one_head: gte(?x, 0.0) :- gte(?x, 1.0)
  proof one_head by z3 end
end
"#,
    );
    for rule in ["test.kf2sd.heads.both", "test.kf2sd.heads.viol"] {
        let said = refusal(&out, rule);
        assert!(
            said.contains(&format!("the rule '{rule}' is 2 clauses"))
                && said.contains("a proof is ONE document"),
            "{said}"
        );
    }
    // What is not proved is not cited.
    let said = refusal(&out, "test.kf2sd.heads.bad");
    assert!(said.contains("did not prove in this run"), "{said}");
    assert_eq!(
        assertions(&out, "test.kf2sd.heads.one_head"),
        [
            "(assert (>= var_0 1.0))",
            "(assert (not (>= var_0 0.0)))"
        ]
    );
}

/// AN ENTITY PREMISE READS AN ENTITY OF ONE FACT. Its fields are constants of the
/// document, defined off the entity's fact — the first, where there were several,
/// whichever fact the premise's own slots named: `Limit(cap: ?c)` over caps 5 and -1
/// proved `gte(?c, 0.0)`, and `Mode(kind: 2.0, cap2: ?c)` proved it with the cap of
/// kind 1. It is the call of several facts in an entity's spelling.
#[test]
fn an_entity_premise_over_several_facts_is_refused() {
    let out = dry_run(
        "ent",
        r#"
namespace test.kf2sd.ent
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte, lte}

  entity Limit(cap: Float)
  fact Limit(cap: 5.0)
  fact Limit(cap: -1.0)
  rule lemma: gte(?c, 0.0) :- Limit(cap: ?c)
  proof lemma by z3 end

  entity Mode(kind: Float, cap2: Float)
  fact Mode(kind: 1.0, cap2: 5.0)
  fact Mode(kind: 2.0, cap2: -1.0)
  rule of_two: gte(?c, 0.0) :- Mode(kind: 2.0, cap2: ?c)
  proof of_two by z3 end

  entity One(top: Float)
  fact One(top: 3.0)
  rule single: lte(?t, 3.0) :- One(top: ?t)
  proof single by z3 end
end
"#,
    );
    for (rule, entity) in [
        ("test.kf2sd.ent.lemma", "test.kf2sd.ent.Limit"),
        ("test.kf2sd.ent.of_two", "test.kf2sd.ent.Mode"),
    ] {
        let said = refusal(&out, rule);
        assert!(
            said.contains(&format!("the entity `{entity}` has several facts")),
            "{said}"
        );
    }
    assert_eq!(
        assertions(&out, "test.kf2sd.ent.single"),
        ["(assert (not (<= top 3.0)))"]
    );
}

const FRAMES: &str = r#"
namespace test.kf2sd.frames
  import anthill.prelude.PartialOrd.{gte, lte}
  import anthill.prelude.Option.{some, none}

  rule gain(none, ?r) :- ?r = 0.0
  rule gain(some(?x), ?r) :- ?r = ?x + 1.0
  rule bound(?d) :- gain(?o, ?d)

  rule claim0: gte(?v, 1.0) :- ?s = some(2.0), bound(?v)
  proof claim0 by z3 end

  rule pick(some(none), ?r) :- ?r = -100.0
  rule pick(some(some(?x)), ?r) :- ?r = ?x
  rule wrap(?o, ?r) :- ?z = some(1.0), pick(?o, ?r)

  rule claim_a: gte(?r, 0.0) :- wrap(some(?y), ?r)
  proof claim_a by z3 end

  rule chosen: gte(?r, 0.0) :- wrap(some(some(3.0)), ?r)
  proof chosen by z3 end
end
"#;

/// A CLAUSE IS SELECTED BY WHAT THE FRAME BEING READ KNOWS, AND BY NO OTHER FRAME'S.
/// Two leaks, each of which selected a clause by another rule's variable and proved a
/// false claim on the first cut of this change:
///
///   * `bound(?d) :- gain(?o, ?d)` is read by the one-argument form, which kept the
///     CALLER's entities installed: the caller's `?s = some(2.0)` has the index of
///     `bound`'s free `?o`, the `some` clause of `gain` was read for it, and `claim0`
///     proved — `bound(0.0)` holds by `gain(none, 0.0)`.
///   * `wrap(some(?y), ?r)` hands `wrap` a construction that still names the caller's
///     `?y`, and in `wrap`'s frame that index is `?z = some(1.0)`: the `some(none)`
///     clause of `pick` was ruled out by it, and `claim_a` — false at `?y = none`, where
///     the answer is -100 — proved.
///
/// Both are refused: two clauses can answer. `chosen` is the control that selection
/// through an inlined rule still works where the call WRITES what selects.
#[test]
fn a_clause_is_selected_by_the_frame_being_read_and_no_other() {
    let out = dry_run("frames", FRAMES);
    let said = refusal(&out, "test.kf2sd.frames.claim0");
    assert!(
        said.contains(
            "the call of `test.kf2sd.frames.gain/2`, in the body of \
             `test.kf2sd.frames.bound` (read inlined), can be answered by 2 clauses"
        ),
        "{said}"
    );
    let said = refusal(&out, "test.kf2sd.frames.claim_a");
    assert!(
        said.contains(
            "the call of `test.kf2sd.frames.pick/2`, in the body of \
             `test.kf2sd.frames.wrap` (read inlined), can be answered by 2 clauses"
        ),
        "{said}"
    );
    assert_eq!(
        assertions(&out, "test.kf2sd.frames.chosen"),
        ["(assert (not (>= 3.0 0.0)))"]
    );
    assert_eq!(errors(&out).len(), 2, "stderr:\n{}", out.stderr);
}

/// A NUMBER SELECTS AS A CONSTRUCTOR DOES — written in the call, or what the call's
/// variable was defined as — and a clause selected by the number in its head is READ:
/// `mode(0, ?r)` was "head arg must be a De Bruijn var or a constructor", the selection
/// made and the binding refused. Over facts, `?k = 1, at(?k, ?x)` read the FIRST fact
/// and rebound `?k` (`(assert (not (>= 1.0 2.0)))`, a COUNTEREXAMPLE of a true claim).
#[test]
fn a_number_selects_one_clause_written_or_bound() {
    let out = dry_run(
        "number",
        r#"
namespace test.kf2sd.number
  import anthill.prelude.PartialOrd.{gte, lte}

  rule mode(0, ?r) :- ?r = 1.0
  rule mode(1, ?r) :- ?r = 2.0

  rule mode0: lte(?r, 1.0) :- mode(0, ?r)
  proof mode0 by z3 end

  rule mode1: gte(?r, 2.0) :- ?k = 1, mode(?k, ?r)
  proof mode1 by z3 end

  rule mode_any: gte(?r, 1.0) :- mode(?k, ?r)
  proof mode_any by z3 end

  fact at(0, 1.0)
  fact at(1, 2.0)
  rule at1: gte(?x, 2.0) :- ?k = 1, at(?k, ?x)
  proof at1 by z3 end
end
"#,
    );
    assert_eq!(
        assertions(&out, "test.kf2sd.number.mode0"),
        ["(assert (not (<= 1.0 1.0)))"]
    );
    assert_eq!(
        assertions(&out, "test.kf2sd.number.mode1"),
        ["(assert (not (>= 2.0 2.0)))"]
    );
    assert_eq!(
        assertions(&out, "test.kf2sd.number.at1"),
        ["(assert (not (>= 2.0 2.0)))"]
    );
    refused_as_several(&out, "test.kf2sd.number.mode_any", "test.kf2sd.number.mode/2", 0, 2);
    assert_eq!(errors(&out).len(), 1, "stderr:\n{}", out.stderr);
}

/// A FACT'S SLOT IS READ, OR THE CALL IS REFUSED — none is passed over.
///
///   * a VARIABLE in the fact (`fact dflt(?who, 5.0)`) is every value there: the call's
///     `Leader` is one, and nothing is bound. It was "unhandled body goal functor" (the
///     fact "did not match"), and on the first cut a refusal that blamed the call's
///     argument.
///   * a NULLARY CONSTRUCTOR met by the call's variable binds it: `lead(?who)` makes
///     `?who` the `Follower`, and `speed_of(?who, ?v)` is then the Follower's fact. The
///     variable was left bound to nothing, the second call read the FIRST fact, and
///     `led` — false, the Follower's speed is 50 — proved.
///   * a STRING is a value a variable is not bound to: refused. It was "skip for v0".
#[test]
fn a_facts_slot_is_read_or_the_call_is_refused() {
    let out = dry_run(
        "slots",
        r#"
namespace test.kf2sd.slots
  import anthill.prelude.PartialOrd.{gte, lte}

  sort Drone
    entity Leader
    entity Follower
  end

  fact dflt(?who, 5.0)
  rule every: lte(?v, 5.0) :- dflt(Leader, ?v)
  proof every by z3 end

  fact lead(Follower)
  fact speed_of(Leader, 5.0)
  fact speed_of(Follower, 50.0)
  rule led: lte(?v, 10.0) :- lead(?who), speed_of(?who, ?v)
  proof led by z3 end

  fact named("a", 1.0)
  rule text: gte(?v, 0.0) :- named(?n, ?v)
  proof text by z3 end
end
"#,
    );
    assert_eq!(
        assertions(&out, "test.kf2sd.slots.every"),
        ["(assert (not (<= 5.0 5.0)))"]
    );
    assert_eq!(
        assertions(&out, "test.kf2sd.slots.led"),
        ["(assert (not (<= 50.0 10.0)))"]
    );
    let said = refusal(&out, "test.kf2sd.slots.text");
    assert!(
        said.contains("the call of `test.kf2sd.slots.named` is answered by a fact")
            && said.contains("the fact's slot 1 is a value the call's variable there is not bound to"),
        "{said}"
    );
}

/// A LEMMA STATED OF A PREDICATE IS ONE OF ITS CLAUSES: a rule with a label and the
/// predicate for its head is under the predicate as its definition is, the resolver
/// answers a goal by it, and what it adds — it is trusted here — is not read by reading
/// the definition beside it. `uses` read the definition and proved; it is refused, and
/// told what the second clause is.
#[test]
fn a_lemma_stated_of_a_predicate_is_one_of_its_clauses() {
    let out = dry_run(
        "lemma",
        r#"
namespace test.kf2sd.lemma
  import anthill.prelude.PartialOrd.{gte, lte}

  rule safe(?x, ?m) :- gte(?x, ?m)

  rule safe_weaken: safe(?x, ?n) :- safe(?x, ?m), gte(?m, ?n)
  proof safe_weaken by trust(reason: "a control") end

  rule uses: gte(?x, 0.0) :- safe(?x, 0.0)
  proof uses by z3 end
end
"#,
    );
    refused_as_several(&out, "test.kf2sd.lemma.uses", "test.kf2sd.lemma.safe/2", 0, 2);
    let said = refusal(&out, "test.kf2sd.lemma.uses");
    assert!(
        said.contains(
            "a rule stated with a label and this predicate for its head is one of its clauses"
        ),
        "{said}"
    );
}

/// THE RULE A PROOF IS OF IS THE CLAUSES ITS NAME STATES, and not a declaration that
/// shares the name. A rule named as the last segment of its namespace has the
/// namespace's symbol for the functor of its head, so the namespace's own clause is
/// under the name too, and first: the proof was of THAT — an empty document, `sat`, a
/// COUNTEREXAMPLE of a rule whose body cannot hold (5 is not above 99) — where the same
/// rule under another name proved. Found by the count this change makes of a rule's
/// clauses, which made this one "2 clauses".
#[test]
fn a_rule_named_as_its_namespace_is_proved_as_the_rule() {
    let out = dry_run(
        "samename",
        r#"
namespace test.kf2sd.legacy
  import anthill.prelude.{Int64}
  import anthill.prelude.PartialEq.{eq}
  import anthill.prelude.PartialOrd.{gt}

  entity Cfg(scale: Int64)
  fact Cfg(scale: 5)

  rule legacy(?marker) :- Cfg(scale: ?s), gt(?s, 99), eq(?marker, ?s)
  proof legacy by z3(logic: "LIA") end
end
"#,
    );
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    assert_eq!(
        assertions(&out, "test.kf2sd.legacy"),
        ["(assert (> scale 99.0))"]
    );
}
