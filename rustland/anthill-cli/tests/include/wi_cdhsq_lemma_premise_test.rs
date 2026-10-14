//! WI-20261012-CDHSQ — A CITED LEMMA'S PREMISE THAT IS A RULE'S PREDICATE IS ITS
//! ANTECEDENT.
//!
//! A cited rule is handed to the citing proof as `(=> premises conclusion)`, read
//! without chasing a rule call into its body. Until this a premise that WAS a rule call
//! was passed over with the body it was not chased into, so
//!
//!   rule related(?a, ?b) :- gte(?a, ?b)
//!   rule lemma: gte(?a, ?b) :- related(?a, ?b)
//!
//! lifted to `(=> true (>= var_1 var_0))` — every two reals compare — and a proof that
//! cited it proved `gte(?c, 5.0) :- gte(0.0, ?c)`. So did a premise that is a fact's
//! predicate, a one-argument rule's, a connective over goals, and the premise of a
//! structured proof's step.
//!
//! Now (decided with the user, 2026-10-12, on the count in
//! `docs/measurements/test-infrastructure/lemma-premise-2026-10-12.txt`; proposal 030
//! γ.1):
//!
//!   * the predicate is an UNINTERPRETED RELATION of its own name and arity
//!     (`ns.related/2`), declared once in the consumer's document, and the lift's
//!     premise is written with it;
//!   * a proof states ITS OWN call of a relation a lemma it cites declared — the call it
//!     skips (a structured proof's conclusion) and the call it reads the body of alike —
//!     which is what discharges the premise;
//!   * a proof that cites no such lemma states no call: its document is the one it was;
//!   * what cannot be written whole is REFUSED, in the lift and in the proof, and not
//!     left out: named arguments, an argument with no SMT form or no sort, a second
//!     signature — and in the lift, a connective over goals and an entity's slot that is
//!     no variable. A call inside an inlined rule that names that rule's own variable was
//!     refused too, until WI-20261012-BR7P3 gave such a variable a name of its own: it is
//!     stated of it.
//!
//! A LAW's premise that is a rule's predicate is as WI-20261012-ZZ7PH left it: the law
//! is not lowered, and said (`wi_zz7ph_law_lowering_test`'s
//! `a_law_whose_premise_is_a_rules_predicate_is_left_out_whole`).
//!
//! THE ROWS THAT CARRY THE SUBJECT RUN `--dry-run` and read the document, so none passes
//! for want of a solver; the lemmas are `by trust`, which a dry run discharges. The
//! verdict rows are one test, guarded, at the foot.
//!
//! WHAT FAILS WHEN A PART IS BACKED OUT is measured, row by row, in the measurement
//! file's §4.

use crate::common::{anthill, prove_dry_run, write_temp, z3_available, Output};

/// A dry run of `src`, in a file of this suite's own: the rows of one binary run side
/// by side and share a directory of temporary files, named by the process and `name`.
fn dry_run(name: &str, src: &str) -> Output {
    prove_dry_run(&format!("cdhsq_{name}"), src)
}

fn errors(out: &Output) -> Vec<&str> {
    out.diagnostics("error:").collect()
}

/// The document of the proof `rule`: the lines between its banner and the next rule.
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

fn assert_has(doc: &[&str], line: &str) {
    assert!(
        doc.contains(&line),
        "the document has the line\n  {line}\ndocument:\n{}",
        doc.join("\n")
    );
}

/// `related` is more than nothing and less than the lemma: a proof that reads its body
/// and not the lemma cannot have the lemma's conclusion.
const BASE: &str = r#"
namespace test.cdhsq.base
  import anthill.prelude.PartialOrd.{gte, lte}

  rule related(?a, ?b) :- gte(?a, ?b)

  rule lemma: gte(?a, ?b + 1.0) :- related(?a, ?b)
  proof lemma by trust(reason: "a control") end

  rule bogus: gte(?c, 5.0) :- gte(0.0, ?c)
  proof bogus using lemma by z3 end

  rule holds: gte(?x, ?y + 1.0) :- related(?x, ?y)
  proof holds using lemma by z3 end
end
"#;

/// THE TICKET'S CASE. The lift keeps its premise, as the relation of the predicate's
/// name over the sorts of its arguments, which the consumer's document declares — and
/// which makes the document's logic one with uninterpreted functions.
#[test]
fn a_lemmas_premise_that_is_a_rules_predicate_is_its_antecedent() {
    let out = dry_run("base", BASE);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let doc = document(&out, "test.cdhsq.base.bogus");
    assert_has(&doc, "(set-logic UFLRA)");
    assert_has(
        &doc,
        "(declare-fun test.cdhsq.base.related/2 (Real Real) Bool)",
    );
    assert_has(
        &doc,
        "(assert (forall ((var_0 Real) (var_1 Real)) \
         (=> (test.cdhsq.base.related/2 var_1 var_0) (>= var_1 (+ var_0 1.0)))))",
    );
    assert!(
        !doc.iter().any(|l| l.contains("(=> true")),
        "no premise is passed over:\n{}",
        doc.join("\n")
    );
    // `bogus` calls no `related`, and so holds none: its body is what it was.
    assert_eq!(
        doc.iter()
            .filter(|l| l.starts_with("(assert (test.cdhsq.base.related/2 "))
            .count(),
        0,
        "{}",
        doc.join("\n")
    );
}

/// A PROOF STATES ITS OWN CALL, beside the body it reads of it: the lemma has the
/// relation and not the body, and `(>= var_1 var_0)` alone does not discharge its
/// premise (z3 on that document: `sat`).
#[test]
fn a_proof_states_its_own_call_beside_the_body_it_reads() {
    let out = dry_run("base_holds", BASE);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let doc = document(&out, "test.cdhsq.base.holds");
    assert_has(&doc, "(assert (>= var_1 var_0))");
    assert_has(&doc, "(assert (test.cdhsq.base.related/2 var_1 var_0))");
    assert_has(&doc, "(assert (not (>= var_1 (+ var_0 1.0))))");
    assert_eq!(
        doc.iter()
            .filter(|l| l.starts_with("(declare-fun test.cdhsq.base.related/2 "))
            .count(),
        1,
        "declared once, for the lemma and the body:\n{}",
        doc.join("\n")
    );
}

const SHAPES: &str = r#"
namespace test.cdhsq.shapes
  import anthill.prelude.PartialOrd.{gte, lte}

  fact start(5.0)
  rule bound(?r) :- ?r = 2.0 + 3.0

  rule of_start: gte(?d, 100.0) :- start(?d)
  proof of_start by trust(reason: "a control") end
  rule of_bound: gte(?d, 100.0) :- bound(?d)
  proof of_bound by trust(reason: "a control") end

  rule bogus_start: gte(?c, 5.0) :- gte(0.0, ?c)
  proof bogus_start using of_start by z3 end
  rule bogus_bound: gte(?c, 5.0) :- gte(0.0, ?c)
  proof bogus_bound using of_bound by z3 end

  rule holds_start: gte(?z, 100.0) :- start(?z)
  proof holds_start using of_start by z3 end
  rule holds_bound: gte(?z, 100.0) :- bound(?z)
  proof holds_bound using of_bound by z3 end
end
"#;

/// A FACT'S PREDICATE AND A ONE-ARGUMENT RULE ARE PREMISES TOO. Each was passed over
/// by the same branch — `(=> true (>= var_0 100.0))`, measured — and a proof reads each
/// by its own path: a fact is matched, a one-argument rule's value is bound. The call is
/// stated AFTER that reading, so its argument is the value the reading gave it; stated
/// before, it named a variable the document then never declared.
#[test]
fn a_facts_predicate_and_a_one_argument_rule_are_premises_too() {
    let out = dry_run("shapes", SHAPES);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    for (predicate, value) in [("start", "5.0"), ("bound", "(+ 2.0 3.0)")] {
        let relation = format!("test.cdhsq.shapes.{predicate}/1");
        let lift =
            format!("(assert (forall ((var_0 Real)) (=> ({relation} var_0) (>= var_0 100.0))))");
        let bogus = document(&out, &format!("test.cdhsq.shapes.bogus_{predicate}"));
        assert_has(&bogus, &format!("(declare-fun {relation} (Real) Bool)"));
        assert_has(&bogus, &lift);
        let holds = document(&out, &format!("test.cdhsq.shapes.holds_{predicate}"));
        assert_has(&holds, &lift);
        assert_has(&holds, &format!("(assert ({relation} {value}))"));
        assert_has(&holds, &format!("(assert (not (>= {value} 100.0)))"));
    }
}

/// `small`'s step is named apart from `big`'s: two structured proofs of one file with a
/// step of one name is its own defect (the second's step is "not found"), measured
/// beside this change and not of it.
const STRUCTURED: &str = r#"
namespace test.cdhsq.steps
  import anthill.prelude.PartialOrd.{gte, lte}

  rule related(?a, ?b) :- gte(?a, ?b)

  rule big: gte(?x, ?y + 1.0) :- related(?x, ?y)
  proof big
    rule h1: gte(?x, ?y + 1.0) :- related(?x, ?y)
      by trust(reason: "a control")
    using h1
    by z3
  end

  rule small: gte(?x, ?y + 1.0) :- lte(?x, 100.0), lte(?y, 100.0)
  proof small
    rule h2: gte(?x, ?y + 1.0) :- related(?x, ?y)
      by trust(reason: "a control")
    using h2
    by z3
  end
end
"#;

/// A STEP OF A STRUCTURED PROOF KEEPS ITS PREMISE, AND ITS PARENT STATES THE CALL IT
/// SKIPS. A step is cited by its parent's conclusion, in the parent's frame: its lift
/// was the bare `(>= var_1 (+ var_0 1.0))`, handed to a parent whether or not the
/// parent held `related(?x, ?y)`. The parent's body is emitted abstractly — the call is
/// not chased — and is where the premise is discharged from: `big` holds it, `small`
/// does not.
#[test]
fn a_steps_premise_is_kept_and_the_parent_states_the_call_it_skips() {
    let out = dry_run("steps", STRUCTURED);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let relation = "test.cdhsq.steps.related/2";
    let step = format!("(assert (=> ({relation} var_1 var_0) (>= var_1 (+ var_0 1.0))))");

    let big = document(&out, "test.cdhsq.steps.big");
    assert_has(&big, &format!("(declare-fun {relation} (Real Real) Bool)"));
    assert_has(&big, &step);
    assert_has(&big, &format!("(assert ({relation} var_1 var_0))"));
    assert!(
        !big.contains(&"(assert (>= var_1 var_0))"),
        "the parent's call is not chased into its body:\n{}",
        big.join("\n")
    );

    let small = document(&out, "test.cdhsq.steps.small");
    assert_has(&small, &step);
    assert!(
        !small
            .iter()
            .any(|l| l.starts_with(&format!("(assert ({relation} "))),
        "`small` calls no `related`, and holds none:\n{}",
        small.join("\n")
    );
}

/// THE CONTROL: A PROOF THAT CITES NO SUCH LEMMA STATES NO CALL. `user` reads
/// `related`'s body, as it always did, and cites a lemma whose premise is a comparison:
/// the document declares nothing, names no relation, and keeps the logic it had. This
/// is what leaves every document that existed to the byte — and `skipper`, a structured
/// proof's conclusion that skips its call, is the same.
#[test]
fn a_proof_that_cites_no_such_lemma_states_no_call() {
    let src = r#"
namespace test.cdhsq.nocite
  import anthill.prelude.PartialOrd.{gte, lte}

  rule related(?a, ?b) :- gte(?a, ?b)

  rule plain: gte(?a, 3.0) :- gte(?a, 5.0)
  proof plain by trust(reason: "a control") end

  rule user: gte(?x, ?y) :- related(?x, ?y), gte(?x, 5.0)
  proof user using plain by z3 end

  rule skipper: gte(?x, 3.0) :- related(?x, ?y), gte(?x, 5.0)
  proof skipper
    rule h1: gte(?x, 3.0) :- gte(?x, 5.0)
      by trust(reason: "a control")
    using h1
    by z3
  end
end
"#;
    let out = dry_run("nocite", src);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    for rule in ["test.cdhsq.nocite.user", "test.cdhsq.nocite.skipper"] {
        let doc = document(&out, rule);
        assert_has(&doc, "(set-logic LRA)");
        assert!(
            !doc.iter()
                .any(|l| l.contains("declare-fun") || l.contains("test.cdhsq.nocite.related")),
            "`{rule}` declares and states nothing:\n{}",
            doc.join("\n")
        );
    }
    // And `user` reads the body of its call, where `skipper` reads nothing of it.
    assert_has(
        &document(&out, "test.cdhsq.nocite.user"),
        "(assert (>= var_1 var_0))",
    );
    assert!(!document(&out, "test.cdhsq.nocite.skipper").contains(&"(assert (>= var_1 var_0))"));
}

const INLINED: &str = r#"
namespace test.cdhsq.inl
  import anthill.prelude.PartialOrd.{gte, lte}

  rule related(?a, ?b) :- gte(?a, ?b)
  rule wrapper(?p, ?q) :- related(?p, ?q), gte(?p, 0.0)

  rule lemma: gte(?a, ?b + 1.0) :- related(?a, ?b)
  proof lemma by trust(reason: "a control") end

  rule deep: gte(?x, ?y + 1.0) :- wrapper(?x, ?y)
  proof deep using lemma by z3 end
end
"#;

/// A CALL INSIDE A BODY THE PROOF INLINES IS STATED, of what the proof passed: `deep`
/// holds `related(?x, ?y)` through `wrapper`, whose head variables are the call's
/// arguments, and the lemma is about `related`.
#[test]
fn a_call_inside_an_inlined_body_is_stated_of_what_the_proof_passed() {
    let out = dry_run("inl", INLINED);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let doc = document(&out, "test.cdhsq.inl.deep");
    assert_has(&doc, "(assert (>= var_1 var_0))");
    assert_has(&doc, "(assert (test.cdhsq.inl.related/2 var_1 var_0))");
    assert_has(&doc, "(assert (>= var_1 0.0))");
    assert!(
        !doc.iter().any(|l| l.contains("test.cdhsq.inl.wrapper")),
        "`wrapper` is no lemma's premise, and is not stated:\n{}",
        doc.join("\n")
    );
}

/// `PartialOrd` has no law that gives `gte` from `lte` turned round, so `p` needs the
/// lemma, and `q`, which holds `lte` and not `related`, does not have it.
const CARRIER: &str = r#"
namespace test.cdhsq.carrier
  import anthill.prelude.PartialOrd.{gte, lte}

  sort Scope
    sort T = ?
    requires anthill.prelude.PartialOrd[T = T]

    rule related(?a: T, ?b: T) :- lte(?b, ?a)

    rule lemma: gte(?a: T, ?b) :- related(?a, ?b)
    proof lemma by trust(reason: "a control") end

    rule p: gte(?x: T, ?y) :- related(?x, ?y)
    proof p using lemma by z3 end

    rule q: gte(?x: T, ?y) :- lte(?y, ?x)
    proof q using lemma by z3 end
  end
end
"#;

/// A PREMISE ABOUT THE CARRIER IS A RELATION OVER THE CARRIER'S SORT. The sorts of the
/// relation are the sorts of the call's arguments — a bound's, or a signature's — and
/// the lemma's premise and the proof's call agree on them.
#[test]
fn a_premise_about_the_carrier_is_a_relation_over_its_sort() {
    let out = dry_run("carrier", CARRIER);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let t = "test.cdhsq.carrier.Scope.T";
    let relation = "test.cdhsq.carrier.Scope.related/2";
    let gte = format!("anthill.prelude.PartialOrd.gte@{t}");
    let doc = document(&out, "test.cdhsq.carrier.Scope.p");
    assert_has(&doc, &format!("(declare-fun {relation} ({t} {t}) Bool)"));
    assert_has(
        &doc,
        &format!(
            "(assert (forall ((var_1 {t}) (var_2 {t})) \
             (=> ({relation} var_2 var_1) ({gte} var_2 var_1))))"
        ),
    );
    assert_has(&doc, &format!("(assert ({relation} var_2 var_1))"));
}

const NULLARY: &str = r#"
namespace test.cdhsq.nullary
  import anthill.prelude.PartialOrd.{gte, lte}

  rule ready :- gte(1.0, 0.0)

  rule lemma: gte(?a, 1.0) :- ready, gte(?a, 0.0)
  proof lemma by trust(reason: "a control") end

  rule bogus: gte(?c, 1.0) :- gte(?c, 0.0)
  proof bogus using lemma by z3 end

  rule big: gte(?c, 1.0) :- ready, gte(?c, 0.0)
  proof big
    rule h1: gte(?c, 1.0) :- ready, gte(?c, 0.0)
      by trust(reason: "a control")
    using h1
    by z3
  end
end
"#;

/// A PREDICATE OF NO ARGUMENTS IS A PREMISE TOO, named bare as a step stores it: the
/// relation of no arguments, `ns.ready/0`. Named bare the goal was "non-Fn body goal"
/// where `ready()` in a rule's body was read — one term, two treatments (/code-review).
#[test]
fn a_predicate_of_no_arguments_named_bare_is_a_premise() {
    let out = dry_run("nullary", NULLARY);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let relation = "test.cdhsq.nullary.ready/0";
    let bogus = document(&out, "test.cdhsq.nullary.bogus");
    assert_has(&bogus, &format!("(declare-fun {relation} () Bool)"));
    assert_has(
        &bogus,
        &format!(
            "(assert (forall ((var_0 Real)) \
             (=> (and {relation} (>= var_0 0.0)) (>= var_0 1.0))))"
        ),
    );
    assert!(!bogus.contains(&format!("(assert {relation})").as_str()));
    let big = document(&out, "test.cdhsq.nullary.big");
    assert_has(
        &big,
        &format!("(assert (=> (and {relation} (>= var_0 0.0)) (>= var_0 1.0)))"),
    );
    assert_has(&big, &format!("(assert {relation})"));
}

const BODIED_OPERATION: &str = r#"
namespace test.cdhsq.defrule
  import anthill.prelude.PartialOrd.{gte, lte}
  import anthill.prelude.{Float}

  operation double(x: Float) -> Float = x + x

  rule lemma: gte(?r, 100.0) :- double(?x, ?r), gte(?x, 50.0)
  proof lemma by trust(reason: "r = 2x") end

  rule holds: gte(?s, 100.0) :- double(?y, ?s), gte(?y, 50.0)
  proof holds using lemma by z3 end
end
"#;

/// A PREMISE THAT CALLS A BODIED OPERATION RELATIONALLY IS A RULE'S PREDICATE, WHICHEVER
/// PROOF RAN FIRST. `double(?x, ?r)` is one once the operation's defining rule is
/// synthesized, and that was done for a rule being discharged, after its cites were
/// lifted, and for a trusted lemma never: this file's one cite was "unhandled body goal
/// functor 'test.cdhsq.defrule.double'" (/code-review, measured), where after another
/// proof that called `double` the same cite lifted. The proof's own call is read by the
/// defining rule — `?s` is `(+ var_0 var_0)` — and stated of that value.
#[test]
fn a_premise_that_calls_a_bodied_operation_is_a_rules_predicate_whoever_ran_first() {
    let out = dry_run("defrule", BODIED_OPERATION);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let relation = "test.cdhsq.defrule.double/2";
    let doc = document(&out, "test.cdhsq.defrule.holds");
    assert_has(&doc, &format!("(declare-fun {relation} (Real Real) Bool)"));
    assert_has(
        &doc,
        &format!(
            "(assert (forall ((var_0 Real) (var_1 Real)) \
             (=> (and ({relation} var_0 var_1) (>= var_0 50.0)) (>= var_1 100.0))))"
        ),
    );
    assert_has(
        &doc,
        &format!("(assert ({relation} var_0 (+ var_0 var_0)))"),
    );
}

/// The one error of a run of `src`, which names `rule`.
fn refusal(name: &str, src: &str, rule: &str) -> String {
    let out = dry_run(name, src);
    let said = errors(&out);
    assert_eq!(said.len(), 1, "stderr:\n{}", out.stderr);
    assert!(said[0].contains(rule), "{}", said[0]);
    assert!(
        !out.stdout.contains(&format!("--- {rule} ---")),
        "`{rule}` has no document:\n{}",
        out.stdout
    );
    said[0].to_owned()
}

/// A CALL THAT CANNOT BE WRITTEN IS REFUSED, NOT LEFT OUT — a premise left out of a
/// lift is the defect, and a call left out of a proof is a cite that reads as honoured
/// and gives nothing. Three shapes, the first in the PROOF and the others in the LIFT:
/// a constructor as an argument, which the expression reader writes as a bare token
/// (a symbol nothing declares); a string, which it writes as the text it spells; and
/// named arguments, which the relation has no order for.
#[test]
fn a_call_that_cannot_be_written_is_refused() {
    let said = refusal(
        "ctor",
        r#"
namespace test.cdhsq.ctor
  import anthill.prelude.PartialOrd.{gte, lte}

  sort Drone
    entity Leader
    entity Follower
  end

  rule speed_of(?who, ?v) :- gte(?v, 0.0)

  rule lemma: lte(?v, 9.0) :- speed_of(?who, ?v)
  proof lemma by trust(reason: "a control") end

  rule slow: lte(?v, 10.0) :- speed_of(Leader, ?v)
  proof slow using lemma by z3 end
end
"#,
        "test.cdhsq.ctor.slow",
    );
    assert!(
        said.contains("a call of the rule's predicate `test.cdhsq.ctor.speed_of`")
            && said.contains("argument 1 is the bare name `Leader`, which is not written"),
        "{said}"
    );

    let said = refusal(
        "str",
        r#"
namespace test.cdhsq.str
  import anthill.prelude.PartialOrd.{gte, lte}

  rule tagged(?tag, ?v) :- gte(?v, 0.0)

  rule lemma: lte(?v, 9.0) :- tagged("1.0", ?v)
  proof lemma by trust(reason: "a control") end

  rule slow: lte(?v, 10.0) :- gte(?v, 0.0)
  proof slow using lemma by z3 end
end
"#,
        "test.cdhsq.str.slow",
    );
    assert!(
        said.contains("cite `test.cdhsq.str.lemma`")
            && said.contains(r#"argument 1 is the string "1.0", which is not written"#),
        "{said}"
    );

    let said = refusal(
        "named",
        r#"
namespace test.cdhsq.named
  import anthill.prelude.PartialOrd.{gte, lte}

  rule ranked(low: ?a, high: ?b) :- gte(?b, ?a)

  rule lemma: gte(?b, ?a + 1.0) :- ranked(low: ?a, high: ?b)
  proof lemma by trust(reason: "a control") end

  rule p: gte(?c, 5.0) :- gte(0.0, ?c)
  proof p using lemma by z3 end
end
"#,
        "test.cdhsq.named.p",
    );
    assert!(
        said.contains("cite `test.cdhsq.named.lemma`")
            && said.contains("written with named arguments"),
        "{said}"
    );
}

/// AN ARGUMENT THAT NOTHING GIVES A SORT IS REFUSED UNDER AN ABSTRACT PARAMETER, as a
/// variable so placed is. `top` is a constant of the carrier, and a rule's predicate has
/// no signature to say so: guessed a `Real`, the argument was "unhandled arithmetic op
/// 'anthill.prelude.BoundedLattice.top'" (/code-review, measured), which reads as if the
/// operation were at fault.
#[test]
fn an_argument_nothing_gives_a_sort_is_refused_under_an_abstract_parameter() {
    let said = refusal(
        "top",
        r#"
namespace test.cdhsq.top
  import anthill.prelude.PartialOrd.{gte, lte}
  import anthill.prelude.BoundedLattice.{lub, top}

  sort Scope
    sort T = ?
    requires anthill.prelude.BoundedLattice[T = T]

    rule related(?a: T, ?b: T) :- lte(?a, ?b)

    rule lemma: gte(lub(?a: T, top), top) :- related(?a, top)
    proof lemma by trust(reason: "a control") end

    rule p: gte(lub(?x: T, top), top) :- lte(?x, ?x)
    proof p using lemma by z3 end
  end
end
"#,
        "test.cdhsq.top.Scope.p",
    );
    assert!(
        said.contains("cite `test.cdhsq.top.Scope.lemma`")
            && said.contains("nothing gives argument 2 a sort"),
        "{said}"
    );
}

/// A CALL INSIDE AN INLINED RULE THAT NAMES THAT RULE'S OWN VARIABLE IS STATED OF IT.
/// `wrap2`'s `?r` is neither passed by its head nor defined by its body. An inlined
/// rule's own variable went by the name the proof's variable of the same index has
/// (WI-20261012-BR7P3): the call was stated `(related var_1 var_0)`, `var_0` the PROOF's
/// `?y`, the lemma's premise held of two variables the proof never related, and `deep` —
/// false at x = 0, y = 50 — proved (/code-review, measured); so it was refused here. Now
/// `?r` is named past `deep`'s two variables, `var_2`, and the relation is stated of it;
/// `deep` is a COUNTEREXAMPLE (`wi_fheek_inlined_names_test`'s verdict row). FAILS with
/// BR7P3's naming backed out, as it did before it: refused.
#[test]
fn a_call_in_an_inlined_rule_that_names_its_own_variable_is_stated_of_it() {
    let out = dry_run(
        "own",
        r#"
namespace test.cdhsq.own
  import anthill.prelude.PartialOrd.{gte, lte}

  rule related(?a, ?b) :- gte(?a, ?b)
  rule wrap2(?p, ?q) :- related(?p, ?r), gte(?q, 0.0)

  rule lemma: gte(?a, ?b + 1.0) :- related(?a, ?b)
  proof lemma by trust(reason: "a control") end

  rule deep: gte(?x, ?y + 1.0) :- wrap2(?x, ?x), lte(?y, 100.0)
  proof deep using lemma by z3 end
end
"#,
    );
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let deep = document(&out, "test.cdhsq.own.deep");
    for line in [
        "(declare-const var_2 Real)",
        "(assert (>= var_1 var_2))",
        "(assert (test.cdhsq.own.related/2 var_1 var_2))",
        "(assert (<= var_0 100.0))",
    ] {
        assert!(deep.contains(&line), "`{line}`:\n{}", deep.join("\n"));
    }
}

/// A PREMISE THAT IS A CONNECTIVE OVER GOALS IS REFUSED. `a | b` is `anthill.kernel.or(a,
/// b)` and `or` is a RULE of the kernel (`or(?a, ?b) :- push_choice(?a, ?b)`), as `and`
/// is: the branch that passed a rule call over passed these over too — measured, the
/// lift was `(=> true (>= var_0 0.0))` and `bogus` proved. Stated as the relation of its
/// name it would be `(anthill.kernel.or/2 (>= var_0 1.0) (>= var_0 2.0))`, uninterpreted:
/// sound, discharged by no consumer, and nothing said.
#[test]
fn a_premise_that_is_a_connective_over_goals_is_refused() {
    for (name, connective, word) in [("disj", "|", "or"), ("conj", "&", "and")] {
        let src = format!(
            r#"
namespace test.cdhsq.{name}
  import anthill.prelude.PartialOrd.{{gte, lte}}

  rule lemma: gte(?a, 0.0) :- gte(?a, 1.0) {connective} gte(?a, 2.0)
  proof lemma by trust(reason: "a control") end

  rule bogus: gte(?c, 0.0) :- lte(?c, 100.0)
  proof bogus using lemma by z3 end
end
"#
        );
        let said = refusal(name, &src, &format!("test.cdhsq.{name}.bogus"));
        assert!(
            said.contains(&format!("cite `test.cdhsq.{name}.lemma`"))
                && said.contains(&format!(
                    "a premise that is a connective over goals (`{word}`, `anthill.kernel.{word}`) \
                     is not read into a lift"
                )),
            "{said}"
        );
    }
}

const ENTITY_SLOTS: &str = r#"
namespace test.cdhsq.slot
  import anthill.prelude.PartialOrd.{gte, lte}
  import anthill.prelude.{Float}

  entity Mode(kind: Float, cap: Float)
  fact Mode(kind: 1.0, cap: 9.0)

  rule open_lemma: gte(?x, ?c) :- Mode(kind: ?k, cap: ?c), gte(?x, ?c + 1.0)
  proof open_lemma by trust(reason: "a control: every slot a variable") end

  rule uses: gte(?y, ?c) :- Mode(kind: ?k, cap: ?c), gte(?y, ?c + 1.0)
  proof uses using open_lemma by z3 end
end
"#;

/// AN ENTITY PREMISE'S SLOT THAT IS NO VARIABLE IS REFUSED IN A LIFT. `Mode(kind: 2.0,
/// cap: ?c)` says which `Mode` the lemma is of, and the entity reader binds the variable
/// slots and passes the others over: the lift was `(=> (>= var_1 cap) (>= var_1
/// 100.0))`, the `kind` premise gone, and a proof about the `Mode` of kind 1 proved by
/// citing a lemma about kind 2 (/code-review, measured — the lemma is vacuous, the proof
/// false at y = 9). THE CONTROL: an entity premise whose slots are variables lifts as it
/// did, its fields the constants the consumer's document defines.
#[test]
fn an_entity_premises_slot_that_is_no_variable_is_refused_in_a_lift() {
    let said = refusal(
        "slot",
        r#"
namespace test.cdhsq.slot
  import anthill.prelude.PartialOrd.{gte, lte}
  import anthill.prelude.{Float}

  entity Mode(kind: Float, cap: Float)
  fact Mode(kind: 1.0, cap: 9.0)

  rule lemma: gte(?x, 100.0) :- Mode(kind: 2.0, cap: ?c), gte(?x, ?c)
  proof lemma by trust(reason: "vacuous: no Mode of kind 2") end

  rule bogus: gte(?y, 100.0) :- Mode(kind: 1.0, cap: ?c), gte(?y, ?c)
  proof bogus using lemma by z3 end
end
"#,
        "test.cdhsq.slot.bogus",
    );
    assert!(
        said.contains("cite `test.cdhsq.slot.lemma`")
            && said.contains(
                "the premise `test.cdhsq.slot.Mode` is an entity and its field `kind` is given \
                 a value that is no variable"
            ),
        "{said}"
    );

    let out = dry_run("slot_open", ENTITY_SLOTS);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let doc = document(&out, "test.cdhsq.slot.uses");
    assert_has(&doc, "(define-fun cap () Real 9.0)");
    assert_has(
        &doc,
        "(assert (forall ((var_2 Real)) (=> (>= var_2 (+ cap 1.0)) (>= var_2 cap))))",
    );
}

/// PREDICATES OF ONE NAME AND TWO ARITIES ARE TWO RELATIONS. `span` has a clause of two
/// arguments and one of three; the step's premise is the first and the parent's call
/// the second, which no lemma is about: it is not stated, and the step's premise is not
/// discharged by it. (Named by the predicate alone the two were one relation at two
/// signatures, and the proof was refused where only the name collided.)
#[test]
fn predicates_of_one_name_and_two_arities_are_two_relations() {
    let out = dry_run("arity", ARITIES);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let doc = document(&out, "test.cdhsq.arity.three");
    assert_has(
        &doc,
        "(declare-fun test.cdhsq.arity.span/2 (Real Real) Bool)",
    );
    assert_has(
        &doc,
        "(assert (=> (test.cdhsq.arity.span/2 var_2 var_1) (>= var_2 (+ var_1 1.0))))",
    );
    assert!(
        !doc.iter().any(|l| l.contains("span/3")),
        "the call of three arguments is no lemma's premise:\n{}",
        doc.join("\n")
    );
}

const ARITIES: &str = r#"
namespace test.cdhsq.arity
  import anthill.prelude.PartialOrd.{gte, lte}

  rule span(?a, ?b) :- gte(?a, ?b)
  rule span(?a, ?b, ?c) :- gte(?a, ?b), gte(?b, ?c)

  rule three: gte(?x, ?y + 1.0) :- span(?x, ?y, ?z)
  proof three
    rule h1: gte(?x, ?y + 1.0) :- span(?x, ?y)
      by trust(reason: "a control")
    using h1
    by z3
  end
end
"#;

/// A PREMISE AND A CALL AT TWO SIGNATURES ARE NOT ONE RELATION. The lemma's premise
/// gives `flag` a `Bool` for its first argument; the proof's call gives it a variable
/// nothing sorts, which is a `Real` as every such variable is. Declared twice the
/// solver would have two functions of one name; declared once at either, the other
/// application is ill-sorted.
#[test]
fn a_premise_and_a_call_at_two_signatures_are_refused() {
    let said = refusal(
        "sig",
        r#"
namespace test.cdhsq.sig
  import anthill.prelude.PartialOrd.{gte, lte}

  rule flag(?b, ?v) :- gte(?v, 0.0)

  rule lemma: lte(?v, 9.0) :- flag(true, ?v)
  proof lemma by trust(reason: "a control") end

  rule p: lte(?v, 10.0) :- flag(?b, ?v)
  proof p using lemma by z3 end
end
"#,
        "test.cdhsq.sig.p",
    );
    assert!(
        said.contains(
            "`test.cdhsq.sig.flag/2` is declared at two signatures in one document: \
             (Real Real) Bool and (Bool Real) Bool"
        ),
        "{said}"
    );
}

const INLINED_DEFINITION: &str = r#"
namespace test.cdhsq.dbl
  import anthill.prelude.PartialOrd.{gte, lte, lt}

  rule dbl(?a, ?r) :- ?r = ?a + ?a

  rule viol(?r) :- dbl(?x, ?r), lt(?x, 0.0)
  proof viol by z3 end
end
"#;

/// A DEFINITION IN AN INLINED RULE IS NOT A CONDITION ON THE CALLER'S VARIABLE. `?x =
/// <a term that names ?x>` is a condition and no definition (WI-20261012-ZZ7PH), and
/// that was asked of the term's TEXT, which inside an inlined rule is in the caller's
/// names: `dbl`'s `?r = ?a + ?a` has the right side `(+ var_0 var_0)`, the caller's
/// `?x`, and `dbl`'s own `?r` is `var_0` by its index. So the definition was read as
/// `(= var_0 (+ var_0 var_0))` — x = 0 — and `viol`, whose body holds at x = -1, proved
/// (/code-review, measured). It is asked of the term.
#[test]
fn a_definition_in_an_inlined_rule_is_not_a_condition_on_the_callers_variable() {
    let out = dry_run("dbl", INLINED_DEFINITION);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let doc = document(&out, "test.cdhsq.dbl.viol");
    assert_has(&doc, "(assert (< var_0 0.0))");
    assert_eq!(
        doc.iter().filter(|l| l.starts_with("(assert ")).count(),
        1,
        "the definition asserts nothing:\n{}",
        doc.join("\n")
    );
}

/// THE VERDICTS, where there is a solver:
///
///   * the ticket's `bogus` is a COUNTEREXAMPLE — it proved — with the lemma trusted and
///     with the lemma PROVED, whose own discharge reads `related`'s body;
///   * a proof that holds the premise proves, and needs the lemma to: a call it reads
///     the body of (`holds`), a fact, a one-argument rule, a call inside a body it
///     inlines, a predicate of no arguments, a call over the carrier — where one that
///     holds the body of `related` and not `related` is a COUNTEREXAMPLE;
///   * a structured proof proves when its parent holds its step's premise, and is a
///     COUNTEREXAMPLE when it does not — it proved — or holds one of another arity;
///   * a rule whose body an inlined definition made unsatisfiable is a COUNTEREXAMPLE.
#[test]
fn the_verdicts_follow_the_premise() {
    if !z3_available() {
        return;
    }
    let prove = |name: &str, src: &str| {
        let path = write_temp(&format!("cdhsq_{name}.anthill"), src);
        anthill(&["prove", path.to_str().unwrap(), "--no-cache"])
    };
    let verdict = |out: &Output, rule: &str, proved: bool| {
        let line = if proved {
            format!("✓ {rule}: proved (z3: unsat)")
        } else {
            format!("✗ {rule}: COUNTEREXAMPLE (z3: sat)")
        };
        assert!(
            out.has_stdout_line(&line),
            "`{line}`; stdout:\n{}\nstderr:\n{}",
            out.stdout,
            out.stderr
        );
    };

    let out = prove("v_base", BASE);
    verdict(&out, "test.cdhsq.base.bogus", false);
    verdict(&out, "test.cdhsq.base.holds", true);

    // The ticket's fixture as it was measured: the lemma proved by the solver.
    let out = prove(
        "v_proved",
        r#"
namespace test.cdhsq.proved
  import anthill.prelude.PartialOrd.{gte, lte}

  rule related(?a, ?b) :- gte(?a, ?b)

  rule lemma: gte(?a, ?b) :- related(?a, ?b)
  proof lemma by z3 end

  rule bogus: gte(?c, 5.0) :- gte(0.0, ?c)
  proof bogus using lemma by z3 end
end
"#,
    );
    verdict(&out, "test.cdhsq.proved.lemma", true);
    verdict(&out, "test.cdhsq.proved.bogus", false);

    let out = prove("v_shapes", SHAPES);
    for predicate in ["start", "bound"] {
        verdict(&out, &format!("test.cdhsq.shapes.bogus_{predicate}"), false);
        verdict(&out, &format!("test.cdhsq.shapes.holds_{predicate}"), true);
    }

    let out = prove("v_inl", INLINED);
    verdict(&out, "test.cdhsq.inl.deep", true);

    let out = prove("v_nullary", NULLARY);
    verdict(&out, "test.cdhsq.nullary.bogus", false);
    verdict(&out, "test.cdhsq.nullary.big", true);

    let out = prove("v_defrule", BODIED_OPERATION);
    verdict(&out, "test.cdhsq.defrule.holds", true);

    let out = prove("v_slot", ENTITY_SLOTS);
    verdict(&out, "test.cdhsq.slot.uses", true);

    let out = prove("v_carrier", CARRIER);
    verdict(&out, "test.cdhsq.carrier.Scope.p", true);
    verdict(&out, "test.cdhsq.carrier.Scope.q", false);

    let out = prove("v_steps", STRUCTURED);
    verdict(&out, "test.cdhsq.steps.big", true);
    verdict(&out, "test.cdhsq.steps.small", false);

    let out = prove("v_arity", ARITIES);
    verdict(&out, "test.cdhsq.arity.three", false);

    let out = prove("v_dbl", INLINED_DEFINITION);
    verdict(&out, "test.cdhsq.dbl.viol", false);
}
