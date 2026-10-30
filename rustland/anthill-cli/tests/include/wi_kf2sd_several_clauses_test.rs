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
//!     the call means, and is WI-20261013-1KF32 — which READS it so: the body is read in
//!     a world for each clause, and the document is their disjunction (decided with the
//!     user, 2026-10-14). The rows that were refusals of several say, each at its site,
//!     what they hold since: a world for each clause, or a refusal that stands for
//!     another reason (a recursive predicate; WI-687's construction in a head);
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
//! clause with a body — 15 of these 17 rows FAIL. (WI-20261013-1KF32 backed out — the
//! refusal of several put back — fails the nine rows it turned; its own measurement file,
//! `docs/measurements/test-infrastructure/disjunction-2026-10-14.txt`, has which.) Two PASS EITHER WAY, by design:
//!   * `a_call_one_clause_answers_is_read_as_it_was` — the control: the documents the
//!     change must not move;
//!   * `lf1s_proofs_read_the_launch_geometry_and_not_the_recursion` — which fails with
//!     lf1 AS IT WAS, whatever the emitter: it holds the model, not the reading.
//! `the_verdicts_of_what_is_read_are_as_they_were` fails when EITHER is backed out: a
//! failure is in its count (a refusal, now a COUNTEREXAMPLE), and lf1's fourteen are.

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

/// The lines of the proof `rule`'s document.
fn document<'a>(out: &'a Output, rule: &str) -> Vec<&'a str> {
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
}

/// The assertions of the proof `rule`'s document, in order.
fn assertions<'a>(out: &'a Output, rule: &str) -> Vec<&'a str> {
    document(out, rule)
        .into_iter()
        .filter(|l| l.starts_with("(assert "))
        .collect()
}

/// WI-20261013-1KF32 — the WORLDS of the proof `rule`'s document, a body read in
/// several: each world's conjunction, in order. (Its comment, which says the choices it
/// made, is `world_choices`.)
fn worlds<'a>(out: &'a Output, rule: &str) -> Vec<&'a str> {
    disjuncts(out, rule)
        .filter(|l| !l.starts_with(';'))
        .collect()
}

/// What each world of `rule`'s document chose, as its comment says it.
fn world_choices<'a>(out: &'a Output, rule: &str) -> Vec<&'a str> {
    disjuncts(out, rule)
        .filter_map(|l| l.strip_prefix("; "))
        .collect()
}

fn disjuncts<'a>(out: &'a Output, rule: &str) -> impl Iterator<Item = &'a str> {
    let lines = document(out, rule);
    assert!(
        lines.contains(&"(assert (or"),
        "`{rule}` is read in several worlds:\n{}",
        lines.join("\n")
    );
    lines
        .into_iter()
        .skip_while(|l| *l != "(assert (or")
        .skip(1)
        .take_while(|l| *l != "))")
        .map(str::trim)
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

/// The refusal of a call met while a clause of its own predicate is read
/// (WI-20261013-1KF32): `relation` in the body of `rule_read`.
fn refused_as_recursive(out: &Output, rule: &str, relation: &str, predicate: &str) {
    let said = refusal(out, rule);
    let recursive = format!(
        "the call of `{relation}`, in the body of `{predicate}` (read inlined), is answered \
         by a clause of `{predicate}` with a body while a clause of `{predicate}` is being \
         read: a recursive predicate is not unfolded"
    );
    assert!(said.contains(&recursive), "expected `{recursive}`, got:\n{said}");
}

/// THE TICKET'S TWO CASES, as filed. Each proved; KF2SD refused each; WI-20261013-1KF32
/// reads each in a world for each clause, and the second world is where the conclusion
/// fails (`related(1, 2)` by `lte`; `start(-1.0)`) — a COUNTEREXAMPLE, which
/// `wi_1kf32_disjunction_test` runs.
#[test]
fn a_call_several_clauses_can_answer_is_their_disjunction() {
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
    assert_eq!(
        worlds(&out, "test.kf2sd.rules.lemma"),
        [
            "(and (>= var_1 var_0) (not (>= var_1 var_0)))",
            "(and (<= var_1 var_0) (not (>= var_1 var_0)))"
        ]
    );

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
    assert_eq!(
        worlds(&out, "test.kf2sd.facts.lemma"),
        ["(not (>= 5.0 0.0))", "(not (>= (- 1.0) 0.0))"]
    );
}

/// A FACT BESIDE A CLAUSE WITH A BODY IS TWO. The one-argument form read the body and
/// never looked at the fact; the other read the fact and never looked at the body.
/// `at/2` is lf1's `real_pose_at` in small: a base fact, and a step whose head is all
/// variables — which a ground argument does not rule out, so `at(0, ?x)` has two.
/// KF2SD refused both. WI-20261013-1KF32: `capped` is a world for the fact and one for
/// the body; `base` is refused still, now as RECURSIVE — the step's world reads the
/// step's own call of `at`, and that is not unfolded.
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
    assert_eq!(
        worlds(&out, "test.kf2sd.mixed.capped"),
        ["(not (<= 100.0 5.0))", "(not (<= (+ 2.0 3.0) 5.0))"]
    );
    refused_as_recursive(
        &out,
        "test.kf2sd.mixed.base",
        "test.kf2sd.mixed.at/2",
        "test.kf2sd.mixed.at",
    );
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
/// a claim of both: KF2SD refused it, and WI-20261013-1KF32 reads it in a world for each
/// row, the Follower's 50 the one where it fails.
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
    assert_eq!(
        worlds(&out, "test.kf2sd.table.any"),
        ["(not (<= 5.0 10.0))", "(not (<= 50.0 10.0))"]
    );
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
}

/// A CONSTRUCTOR IN THE HEAD SELECTS AMONG CLAUSES WITH A BODY, as a ground argument
/// does among facts — by the call's own argument, and by what its variable is bound to.
/// The first bodied clause was read whatever the call, so `with_none` was "expects a
/// concrete `…some` construction": a loud mismatch where the second clause answers. A
/// variable nothing binds rules neither out — and KF2SD refused `with_var` for it.
/// WI-20261013-1KF32 reads it in a world for each clause, and it is refused STILL, in the
/// `some(?x)` clause's world: a free variable against a construction in a head is not
/// bound to it (a construction would carry the clause's own variables into the caller's
/// frame, WI-20261012-BR7P3), and that is WI-687's own refusal, naming the world.
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
    let said = refusal(&out, "test.kf2sd.ctor.with_var");
    assert!(
        said.contains(
            "WI-687: 'test.kf2sd.ctor.gain' expects a concrete `anthill.prelude.Option.some` \
             construction at a constructor-shaped head arg"
        ) && said.contains(
            "(in the world where `test.kf2sd.ctor.gain/2` (0 fact(s), 2 with a body) is \
             answered by its clause 1 of 2)"
        ),
        "{said}"
    );
    assert_eq!(errors(&out).len(), 1, "stderr:\n{}", out.stderr);
}

/// A CLAUSE OF ANOTHER ARITY WAS NO CANDIDATE: `span/2` beside `span/3` was two
/// predicates here, and the first clause with a body had been taken whichever the call
/// was ("rule call arity mismatch for '…span': expected 2, got 3"). Since
/// WI-20260821-6WVJB one name's clauses have one arity, so the program is refused at load
/// and no proof is read: the prover says so, naming both arities, and writes no document.
#[test]
fn a_clause_of_another_arity_is_refused_at_load() {
    let out = dry_run(
        "arity",
        r#"
namespace test.kf2sd.arity
  import anthill.prelude.PartialOrd.{gte, lte}

  rule span(?a, ?b) :- gte(?b, ?a)
  rule span(?a, ?b, ?c) :- gte(?b, ?a), gte(?c, ?b)

  rule two: gte(?b, ?a) :- span(?a, ?b)
  proof two by z3 end
end
"#,
    );
    let said = errors(&out);
    assert!(
        said.iter().any(|e| e.contains(
            "predicate 'test.kf2sd.arity.span' is written at more than one arity: 2 arguments"
        ) && e.contains("3 arguments")),
        "stderr:\n{}",
        out.stderr
    );
    assert!(!out.stdout.contains("--- test.kf2sd.arity.two ---"), "{}", out.stdout);
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

/// THE CALL IS NAMED WITH THE RULE IT STANDS IN, when that is not the proof's own:
/// `deep` calls `wrapper`, and it is `wrapper`'s body that calls `related`. KF2SD's
/// refusal named it; since WI-20261013-1KF32 each world's comment does, and the rest of
/// `wrapper`'s body — `gte(?a, 0.0)` — and the proof's conclusion are read in both.
#[test]
fn a_call_in_an_inlined_rule_is_named_with_that_rule() {
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
    assert_eq!(
        world_choices(&out, "test.kf2sd.wrap.deep"),
        [1, 2].map(|clause| format!(
            "{clause}: `test.kf2sd.wrap.related/2`, in the body of `test.kf2sd.wrap.wrapper` \
             (read inlined) (0 fact(s), 2 with a body) is answered by its clause {clause} of 2"
        ))
    );
    assert_eq!(
        worlds(&out, "test.kf2sd.wrap.deep"),
        [
            "(and (>= var_1 var_0) (>= var_1 0.0) (not (>= var_1 var_0)))",
            "(and (<= var_1 var_0) (>= var_1 0.0) (not (>= var_1 var_0)))"
        ]
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
/// lf1 is fourteen proved. The table's third proof, `any`, is the one failure: KF2SD's
/// refusal, and since WI-20261013-1KF32 a COUNTEREXAMPLE.
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

/// AN ENTITY PREMISE OF ONE FACT reads its fields as constants of the document, defined
/// off the fact (`single`). Where there were several it read the first, whichever fact
/// the premise's own slots named: `Limit(cap: ?c)` over caps 5 and -1 proved `gte(?c,
/// 0.0)`, and `Mode(kind: 2.0, cap2: ?c)` proved it with the cap of kind 1. It is the call
/// of several facts in an entity's spelling, and KF2SD refused it. WI-20261013-1KF32: a
/// world for each fact the premise's slots admit, the field's value bound in it — `lemma`
/// is two, and `of_two` is ONE, the fact of kind 2, whose cap is -1.
#[test]
fn an_entity_premise_over_several_facts_is_a_world_for_each() {
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
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    assert_eq!(
        world_choices(&out, "test.kf2sd.ent.lemma"),
        [1, 2].map(|fact| format!(
            "{fact}: the entity `test.kf2sd.ent.Limit` (2 facts) is answered by its fact \
             {fact} of 2"
        ))
    );
    assert_eq!(
        worlds(&out, "test.kf2sd.ent.lemma"),
        ["(not (>= 5.0 0.0))", "(not (>= (- 1.0) 0.0))"]
    );
    assert_eq!(
        assertions(&out, "test.kf2sd.ent.of_two"),
        ["(assert (not (>= (- 1.0) 0.0)))"]
    );
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
/// Both were refused by KF2SD: two clauses can answer. WI-20261013-1KF32 reads each in a
/// world for each clause, and both are refused STILL, in the world of the clause whose
/// head is `none`: the call's argument there is a variable the frame being read has bound
/// to nothing (`?o`, free in `bound`) or a construction over the caller's (`some(?y)`),
/// neither known to be `none`, which WI-687 refuses — and no world reads the leaked
/// binding. `chosen` was the control that selection through an inlined rule still works
/// where the call WRITES what selects.
///
/// `claim_a` AND `chosen` ARE REFUSED BEFORE ANY WORLD IS READ since WI-20261013-WF14Z
/// (user decision 2026-10-22: an inferred bound is as written): `pick(?o, ?r)` types `wrap`'s
/// column `?o` at `pick`'s, an `Option[T = Option[T = t]]`, a bound no SMT sort lowers — as
/// the written `wrap(?o: Option[T = Option[T = ?t]], ?r)` was refused before. `claim0`'s
/// `?o` is no column of `bound`, and is read as before.
#[test]
fn a_clause_is_selected_by_the_frame_being_read_and_no_other() {
    let out = dry_run("frames", FRAMES);
    for rule in ["claim_a", "chosen"] {
        let said = refusal(&out, &format!("test.kf2sd.frames.{rule}"));
        assert!(
            said.contains("has no SMT sort: a bound is lowered when it is"),
            "{said}"
        );
    }
    for (rule, callee, inlined) in [("claim0", "gain", "bound")] {
        let said = refusal(&out, &format!("test.kf2sd.frames.{rule}"));
        assert!(
            said.contains(&format!(
                "WI-687: nullary head constructor `anthill.prelude.Option.none` inlining \
                 'test.kf2sd.frames.{callee}' does not match the call argument"
            )) && said.contains(&format!(
                "(in the world where `test.kf2sd.frames.{callee}/2`, in the body of \
                 `test.kf2sd.frames.{inlined}` (read inlined) (0 fact(s), 2 with a body) is \
                 answered by its clause 1 of 2)"
            )),
            "{said}"
        );
    }
    assert_eq!(errors(&out).len(), 3, "stderr:\n{}", out.stderr);
}

/// `claim_a` and `chosen` over an option sort with no parameter, so `wrap`'s column is a
/// `OOF`, a type with no variable in it, and gets no bound: the frames are read as the
/// `Option` fixture's were before WI-20261013-WF14Z. `claim_a` is refused in the world of
/// `pick`'s clause whose head is the nullary `nf`, and `chosen` selects by what its call
/// writes.
const FRAMES_NOMINAL: &str = r#"
namespace test.kf2sd.framesn
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte, lte}

  sort OF
    entity nf
    entity sf(v: Float)
  end
  sort OOF
    entity nof
    entity sof(v: OF)
  end
  import test.kf2sd.framesn.OF.{nf, sf}
  import test.kf2sd.framesn.OOF.{nof, sof}

  rule pick(sof(nf), ?r) :- ?r = -100.0
  rule pick(sof(sf(?x)), ?r) :- ?r = ?x
  rule wrap(?o, ?r) :- ?z = sof(sf(1.0)), pick(?o, ?r)

  rule claim_a: gte(?r, 0.0) :- wrap(sof(?y), ?r)
  proof claim_a by z3 end

  rule chosen: gte(?r, 0.0) :- wrap(sof(sf(3.0)), ?r)
  proof chosen by z3 end
end
"#;

#[test]
fn a_clause_is_selected_by_the_frame_being_read_through_a_column() {
    let out = dry_run("framesn", FRAMES_NOMINAL);
    let said = refusal(&out, "test.kf2sd.framesn.claim_a");
    assert!(
        said.contains(
            "WI-687: nullary head constructor `test.kf2sd.framesn.OF.nf` inlining \
             'test.kf2sd.framesn.pick' does not match the call argument"
        ) && said.contains(
            "(in the world where `test.kf2sd.framesn.pick/2`, in the body of \
             `test.kf2sd.framesn.wrap` (read inlined) (0 fact(s), 2 with a body) is \
             answered by its clause 1 of 2)"
        ),
        "{said}"
    );
    assert_eq!(
        assertions(&out, "test.kf2sd.framesn.chosen"),
        ["(assert (not (>= 3.0 0.0)))"]
    );
    assert_eq!(errors(&out).len(), 1, "stderr:\n{}", out.stderr);
}

/// A NUMBER SELECTS AS A CONSTRUCTOR DOES — written in the call, or what the call's
/// variable was defined as — and a clause selected by the number in its head is READ:
/// `mode(0, ?r)` was "head arg must be a De Bruijn var or a constructor", the selection
/// made and the binding refused. Over facts, `?k = 1, at(?k, ?x)` read the FIRST fact
/// and rebound `?k` (`(assert (not (>= 1.0 2.0)))`, a COUNTEREXAMPLE of a true claim).
/// `mode_any`, whose free `?k` selects neither clause, KF2SD refused; WI-20261013-1KF32
/// reads it in a world for each, `?k` bound to the number of its clause's head, and the
/// claim — true of both — holds in both.
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
    assert_eq!(
        worlds(&out, "test.kf2sd.number.mode_any"),
        ["(not (>= 1.0 1.0))", "(not (>= 2.0 1.0))"]
    );
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
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
/// the definition beside it. `uses` read the definition and proved; KF2SD refused it as a
/// call of two clauses, and told it what the second is. Since WI-20261013-1KF32 the
/// lemma's world is read, and the lemma calls `safe` in its own body: refused as a
/// RECURSIVE predicate, which is not unfolded — so a predicate with a lemma stated of it
/// in this shape is still read by no proof (KF2SD §7 (iii), with the user).
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
    refused_as_recursive(
        &out,
        "test.kf2sd.lemma.uses",
        "test.kf2sd.lemma.safe/2",
        "test.kf2sd.lemma.safe",
    );
    let said = refusal(&out, "test.kf2sd.lemma.uses");
    assert!(
        said.contains(
            "a rule stated with a label and this predicate for its head is one of its clauses"
        ),
        "{said}"
    );
}

/// THE RULE A PROOF IS OF IS THE CLAUSES ITS NAME STATES, and not a declaration that
/// shares the name. A rule named as the last segment of its namespace had the
/// namespace's symbol for the functor of its head, so the namespace's own clause was
/// under the name too, and first: the proof was of THAT — an empty document, `sat`, a
/// COUNTEREXAMPLE of a rule whose body cannot hold (5 is not above 99) — where the same
/// rule under another name proved. Found by the count this change makes of a rule's
/// clauses, which made this one "2 clauses". Since WI-20261029-50361 the head introduces
/// a predicate of its own, `test.kf2sd.legacy.legacy`, and the proof is of it.
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
        assertions(&out, "test.kf2sd.legacy.legacy"),
        ["(assert (> scale 99.0))"]
    );
}

/// A PROOF NAMING A NAMESPACE is of no rule: what is under the name is the namespace's own
/// clause, and its document would be empty — `sat`, a counterexample. Refused as a rule
/// that is not there. Fails with `stated_clauses`' clause-kind filter backed out, which is
/// the one row that does since a rule head no longer lands on a namespace
/// (WI-20261029-50361).
#[test]
fn a_proof_naming_a_namespace_is_of_no_rule() {
    let out = dry_run(
        "nsproof",
        r#"
namespace test.kf2sd.nsproof.zed
  import anthill.prelude.{Int64}
  entity Cfg(scale: Int64)
end
namespace test.kf2sd.nsproof
  proof zed by z3(logic: "LIA") end
end
"#,
    );
    let said = refusal(&out, "test.kf2sd.nsproof.zed");
    assert!(said.contains("rule 'test.kf2sd.nsproof.zed' not found"), "{said}");
}
