//! WI-20261014-VVRHJ — AN ENTITY'S FIELD IS THE ENTITY'S. A field read as a constant of a
//! document is named by the entity's qualified name with the field (`test.vvrhj.two.A.cap`),
//! where it was the field's short name, one constant for every entity with a field so
//! named; and a cited lemma's lift reads the fact's value in place of the premise's
//! variable, where it named that constant for a consumer that does not define it
//! (`docs/smtlib-forward-mapping.md` §7.6). An entity of no fact gives a field no value, and
//! is refused: the constant was 0.0.
//!
//! WHAT FAILS WHEN A PART IS BACKED OUT (measured, each part alone, by a temporary switch
//! in the emitter): the field named by its short name — `two_entities_…` (`small` proves),
//! `a_field_named_like_a_variable_…` (the solver's "already defined") and
//! `a_lift_reads_the_facts_value` (the consumer's own constant is `cap`); the lift naming
//! the field's constant — `a_lift_reads_the_facts_value` (the solver's "unknown constant")
//! and `a_lemma_about_one_entity_…` (the same); the field of no fact read as 0.0 —
//! `an_entity_of_no_fact_is_refused`. `a_lemma_about_one_entity_…` PROVES its false claim
//! only with the first two backed out together. With the binary of the tree before
//! (0e696fe2) every row fails. None passes either way.

use crate::common::{anthill, prove_dry_run, write_temp, z3_available, Output};

fn prove(name: &str, src: &str) -> Output {
    let path = write_temp(&format!("vvrhj_{name}.anthill"), src);
    anthill(&["prove", path.to_str().unwrap(), "--no-cache"])
}

fn dry_run(name: &str, src: &str) -> Output {
    prove_dry_run(&format!("vvrhj_{name}"), src)
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

fn assert_line(out: &Output, line: &str) {
    assert!(
        out.has_stdout_line(line),
        "`{line}`; stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}

const TWO: &str = r#"
namespace test.vvrhj.two
  import anthill.prelude.PartialOrd.{gte, lte}
  import anthill.prelude.{Float}

  entity A(cap: Float)
  entity B(cap: Float)
  fact A(cap: 5.0)
  fact B(cap: 1.0)

  rule small: lte(?a, 2.0) :- A(cap: ?a), B(cap: ?b)
  proof small by z3 end
  rule twin: gte(?a, 3.0) :- A(cap: ?a), B(cap: ?b)
  proof twin by z3 end
end
"#;

/// TWO ENTITIES WITH A FIELD OF ONE NAME ARE TWO CONSTANTS. `small` is false — `?a` is 5 —
/// and PROVED while both were `cap`, defined once, by the fact read last (B's 1.0); its twin,
/// true, was a COUNTEREXAMPLE.
#[test]
fn two_entities_with_a_field_of_one_name_are_two_constants() {
    let out = dry_run("two", TWO);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let doc = document(&out, "test.vvrhj.two.small");
    for line in [
        "(define-fun test.vvrhj.two.A.cap () Real 5.0)",
        "(define-fun test.vvrhj.two.B.cap () Real 1.0)",
        "(assert (not (<= test.vvrhj.two.A.cap 2.0)))",
    ] {
        assert!(doc.contains(&line), "{line}:\n{}", doc.join("\n"));
    }
    if !z3_available() {
        return;
    }
    let out = prove("two", TWO);
    assert_line(&out, "✗ test.vvrhj.two.small: COUNTEREXAMPLE (z3: sat)");
    assert_line(&out, "✓ test.vvrhj.two.twin: proved (z3: unsat)");
}

const VAR: &str = r#"
namespace test.vvrhj.var
  import anthill.prelude.PartialOrd.{gte, lte}
  import anthill.prelude.{Float}

  entity E(var_0: Float)
  fact E(var_0: 5.0)

  rule f: gte(?x, 3.0) :- E(var_0: ?v), lte(?x, 1.0), lte(?v, 9.0)
  proof f by z3 end
  rule g: gte(?v, 4.0) :- E(var_0: ?v), lte(?x, 1.0)
  proof g by z3 end
end
"#;

/// A FIELD NAMED LIKE A VARIABLE IS ITS ENTITY'S: the constant `var_0` was also the name of
/// `?v`, and the document both defined and declared it — the solver's "named expression
/// already defined with this name var_0".
#[test]
fn a_field_named_like_a_variable_is_its_entitys() {
    let out = dry_run("var", VAR);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let doc = document(&out, "test.vvrhj.var.g");
    assert!(
        doc.contains(&"(define-fun test.vvrhj.var.E.var_0 () Real 5.0)")
            && doc.contains(&"(assert (not (>= test.vvrhj.var.E.var_0 4.0)))"),
        "{}",
        doc.join("\n")
    );
    if !z3_available() {
        return;
    }
    let out = prove("var", VAR);
    assert_line(&out, "✗ test.vvrhj.var.f: COUNTEREXAMPLE (z3: sat)");
    assert_line(&out, "✓ test.vvrhj.var.g: proved (z3: unsat)");
}

const LIFT: &str = r#"
namespace test.vvrhj.lift
  import anthill.prelude.PartialOrd.{gte, lte}
  import anthill.prelude.{Float}

  entity Lim(cap: Float)
  fact Lim(cap: 5.0)

  rule lemma: gte(?a, 0.0) :- Lim(cap: ?c), gte(?c, 1.0), ?c = ?a + 1.0
  proof lemma by trust(reason: "a control") end

  rule plain: gte(?x, 0.0) :- lte(?x, 100.0), gte(?w, 1.0)
  proof plain using lemma by z3 end
  rule reads: gte(?x, 0.0) :- Lim(cap: ?d), lte(?x, 100.0)
  proof reads using lemma by z3 end
end
"#;

/// A LIFT READS THE FACT'S VALUE IN PLACE OF THE PREMISE'S VARIABLE. It named the
/// constant `cap`, which `plain` — reading no `Lim` — does not define: the solver's
/// "unknown constant cap", and no verdict. A consumer that reads `Lim` itself defines its
/// own constant, and the lift is the same text in its document.
#[test]
fn a_lift_reads_the_facts_value() {
    let out = dry_run("lift", LIFT);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let lift = "(assert (forall ((var_1 Real)) (=> (and (>= 5.0 1.0) (= 5.0 (+ var_1 1.0))) \
                (>= var_1 0.0))))";
    let plain = document(&out, "test.vvrhj.lift.plain");
    assert!(
        plain.contains(&lift) && !plain.iter().any(|l| l.contains("define-fun")),
        "{}",
        plain.join("\n")
    );
    let reads = document(&out, "test.vvrhj.lift.reads");
    assert!(
        reads.contains(&lift)
            && reads.contains(&"(define-fun test.vvrhj.lift.Lim.cap () Real 5.0)"),
        "{}",
        reads.join("\n")
    );
    if !z3_available() {
        return;
    }
    // Both are false at x = -1, which the lemma says nothing of.
    let out = prove("lift", LIFT);
    assert_line(&out, "✗ test.vvrhj.lift.plain: COUNTEREXAMPLE (z3: sat)");
    assert_line(&out, "✗ test.vvrhj.lift.reads: COUNTEREXAMPLE (z3: sat)");
}

/// A LEMMA ABOUT ONE ENTITY IS NOT GIVEN ANOTHER ENTITY'S FIELD. `lemma` is true and the
/// solver proves it; `user` is false at x = 7. Before, the lift named `cap` and `user`'s
/// document defined `cap` as B's 0.0, so the lemma said `x >= 5 => x >= 10` and `user` PROVED.
#[test]
fn a_lemma_about_one_entity_is_not_given_another_entitys_field() {
    if !z3_available() {
        return;
    }
    let out = prove(
        "other",
        r#"
namespace test.vvrhj.other
  import anthill.prelude.PartialOrd.{gte, lte}
  import anthill.prelude.{Float}

  entity Lim(cap: Float)
  entity B(cap: Float)
  fact Lim(cap: 5.0)
  fact B(cap: 0.0)

  rule lemma: gte(?a, 10.0) :- Lim(cap: ?c), gte(?a, ?c + 5.0)
  proof lemma by z3 end
  rule user: gte(?x, 10.0) :- B(cap: ?b), gte(?x, 5.0)
  proof user using lemma by z3 end
end
"#,
    );
    assert_line(&out, "✓ test.vvrhj.other.lemma: proved (z3: unsat)");
    assert_line(&out, "✗ test.vvrhj.other.user: COUNTEREXAMPLE (z3: sat)");
}

/// The ranking proof of `prove_ranking_test`, its boundedness violated — `upc` = -4 is in
/// the post-armed bound and below -3 — over a `State` of no fact, or of every value.
fn ranking(namespace: &str, state: &str) -> String {
    format!(
        r#"
namespace {namespace}
  import anthill.prelude.Additive.{{add}}
  import anthill.prelude.PartialEq.{{eq}}
  import anthill.prelude.PartialOrd.{{gte, lt}}
  entity State(upc: Int64, upc_next: Int64)
  {state}

  rule bound_violation(?marker)
    :- State(upc: ?u, upc_next: ?_), gte(?u, -6), lt(?u, 0), lt(?u, -3), eq(?marker, ?u)
  rule decrease_violation(?marker)
    :- State(upc: ?u, upc_next: ?n), gte(?u, -6), lt(?u, 0), eq(?n, add(?u, 1)),
       gte(?n, ?u), lt(?n, ?u), eq(?marker, ?u)
  rule rank_proof(?marker) :- eq(?marker, true)
  proof rank_proof
    by z3(tactic: ranking(boundedness: bound_violation, decrease: decrease_violation),
          logic: "LIA")
  end
end
"#
    )
}

/// AN ENTITY OF NO FACT GIVES A FIELD NO VALUE, and is refused — in a proof's body, in a
/// ranking's sub-query and in a lift. Its field was the constant 0.0, a value no fact gives:
/// `bad`, true of no `Lim` at all, was a COUNTEREXAMPLE at `cap` = 0; and the ranking proof
/// below proved because `lt(?u, 0)` is false at 0, whatever its sub-queries said of a state.
/// THE CONTROL: a fact whose field is a variable is every value — `bad` is false of
/// `Lim(cap: 0.0)`, and the ranking's boundedness of `upc` = -4.
#[test]
fn an_entity_of_no_fact_is_refused() {
    let none = |facts: &str, lemma: &str| {
        format!(
            r#"
namespace test.vvrhj.none
  import anthill.prelude.PartialOrd.{{gte, lte}}
  import anthill.prelude.{{Float}}

  entity Lim(cap: Float)
  {facts}
  rule bad: lte(?c, -1.0) :- Lim(cap: ?c)
  proof bad by z3 end
  {lemma}
end
"#
        )
    };
    let cited = r#"
  rule lemma: gte(?a, 0.0) :- Lim(cap: ?c), ?c = ?a + 1.0
  proof lemma by trust(reason: "a control") end
  rule user: gte(?x, 0.0) :- lte(?x, 100.0)
  proof user using lemma by z3 end"#;
    let said = |out: &Output, rule: &str| -> bool {
        out.stderr.lines().any(|l| {
            l.starts_with(&format!("error: {rule}: "))
                && l.contains(
                    "has no fact, and a premise here reads its fields off one: a field no fact \
                     gives has no value",
                )
        })
    };
    let out = dry_run("none", &none("", cited));
    for rule in ["test.vvrhj.none.bad", "test.vvrhj.none.user"] {
        assert!(said(&out, rule), "{rule}; stderr:\n{}", out.stderr);
    }
    assert!(
        out.stderr.contains("cite `test.vvrhj.none.lemma`"),
        "the lift is refused:\n{}",
        out.stderr
    );
    let out = dry_run("ranking_none", &ranking("test.vvrhj.rank.none", ""));
    assert!(said(&out, "test.vvrhj.rank.none.rank_proof"), "stderr:\n{}", out.stderr);
    if !z3_available() {
        return;
    }
    let out = prove("every", &none("fact Lim(cap: ?any)", ""));
    assert_line(&out, "✗ test.vvrhj.none.bad: COUNTEREXAMPLE (z3: sat)");
    let out = prove(
        "ranking_every",
        &ranking("test.vvrhj.rank.every", "fact State(upc: ?u, upc_next: ?n)"),
    );
    assert_line(&out, "✗ test.vvrhj.rank.every.rank_proof: COUNTEREXAMPLE (z3: sat)");
}
