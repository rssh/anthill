//! WI-20261013-1KF32 — A CALL SEVERAL CLAUSES CAN ANSWER IS THEIR DISJUNCTION: the body of
//! a `by z3` proof is read in a WORLD for each choice of the clauses that answer its
//! calls, and the document asserts the disjunction of the worlds.
//!
//! WI-20261012-KF2SD refused such a call (a predicate of several clauses holds when ANY
//! of them does, and each reading took one), so a definition by cases and a table of
//! facts could not be called from a proved body at all. Decided with the user,
//! 2026-10-14: the document SPLIT BY THE CHOICE OF CLAUSE, kept ONE document — each world
//! reads the whole body and the conclusion, a variable bound by substitution in it as
//! before, an entity an occurrence there, a later call selected by what the world bound —
//! so the record, the cache key and the witness stay of one document, and a body that
//! meets no choice point is the document it was; a RECURSIVE clause is refused, the
//! one-clause case too; at most 64 worlds; and a number in a bodied head met by a free
//! variable binds it, as a fact's slot does.
//!
//! EVERY ROW BUT `the_verdicts_are_the_disjunctions` RUNS `--dry-run` and reads the
//! document or the refusal, so none passes for want of a solver.
//!
//! WHAT FAILS WHEN THE CHANGE IS BACKED OUT (measured; part by part in
//! `docs/measurements/test-infrastructure/disjunction-2026-10-14.txt` §4). With the
//! emitter as it was (79a6703f), every row FAILS but one, which PASSES EITHER WAY by
//! design and says so: `a_body_that_meets_no_choice_is_the_document_it_was` — the control,
//! the documents the change must not move. Each part of the change backed out alone fails
//! at least one row: the choice point (every row), the recursion guard
//! (`a_recursive_predicate_is_refused_and_not_unfolded`), the arity it compares and the
//! free variable an inlined rule passes (`what_is_read_inlined_is_read_as_it_is_in_the_
//! proof`), the number a head binds (`a_number_in_a_head_binds_a_free_variable`), every
//! row of an entity and a row's variable field (`a_row_whose_field_is_a_variable_…`), the
//! equation of a variable named or defined before its value
//! (`a_variable_named_before_its_value_is_equated_with_it`), one value for a variable
//! written twice (`a_variable_written_twice_meets_one_value`), the slot that is neither
//! a variable nor a number (`an_entity_premise_is_a_world_for_each_fact_it_admits`), the
//! cap (`more_worlds_than_the_cap_are_refused`), and the order of the worlds
//! (`independent_choices_are_their_product`).

use crate::common::{anthill, prove_dry_run, write_temp, z3_available, Output};

fn dry_run(name: &str, src: &str) -> Output {
    prove_dry_run(&format!("kf32_{name}"), src)
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

/// The worlds of `rule`'s document: each world's conjunction, in order.
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

/// The ticket's definition by cases: a piecewise relation, written as Horn clauses.
const CASES: &str = r#"
namespace test.kf32.cases
  import anthill.prelude.PartialOrd.{gte, lte, lt}

  rule commanded_speed(?range, ?v) :- lt(?range, 5.0), ?v = 0.0
  rule commanded_speed(?range, ?v) :- gte(?range, 5.0), ?v = 2.0

  rule speed_is_bounded: lte(?v, 2.0) :- commanded_speed(?range, ?v)
  proof speed_is_bounded by z3 end

  rule never_moves: lte(?v, 0.0) :- commanded_speed(?range, ?v)
  proof never_moves by z3(model: true) end
end
"#;

/// The ticket's table: a claim of every row of it.
const TABLE: &str = r#"
namespace test.kf32.table
  import anthill.prelude.PartialOrd.{gte, lte}

  sort Drone
    entity Leader
    entity Follower
  end

  fact speed_max(Leader, 8.0)
  fact speed_max(Follower, 10.0)

  rule every_drone_is_bounded: lte(?v, 10.0) :- speed_max(?who, ?v)
  proof every_drone_is_bounded by z3 end

  rule every_drone_is_slow: lte(?v, 8.0) :- speed_max(?who, ?v)
  proof every_drone_is_slow by z3 end

  fact margin(Leader, 2.0)
  fact margin(Follower, 0.0)
  rule within: lte(?v + ?m, 10.0) :- speed_max(?who, ?v), margin(?who, ?m)
  proof within by z3 end
end
"#;

/// A DEFINITION BY CASES IS A WORLD FOR EACH CASE. Each case's guard and its value are
/// read in its world, and the conclusion with them: `?v` is `0.0` in the first and `2.0`
/// in the second, and `?range` — which neither binds — is one constant of the document.
/// KF2SD refused both proofs; before it, both PROVED, read as the first case.
#[test]
fn a_definition_by_cases_is_a_world_for_each_case() {
    let out = dry_run("cases", CASES);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let choices = [1, 2].map(|clause| {
        format!(
            "{clause}: `test.kf32.cases.commanded_speed/2` (0 fact(s), 2 with a body) is \
             answered by its clause {clause} of 2"
        )
    });
    assert_eq!(world_choices(&out, "test.kf32.cases.speed_is_bounded"), choices);
    assert_eq!(
        worlds(&out, "test.kf32.cases.speed_is_bounded"),
        [
            "(and (< var_0 5.0) (not (<= 0.0 2.0)))",
            "(and (>= var_0 5.0) (not (<= 2.0 2.0)))"
        ]
    );
    assert_eq!(world_choices(&out, "test.kf32.cases.never_moves"), choices);
    assert_eq!(
        worlds(&out, "test.kf32.cases.never_moves"),
        [
            "(and (< var_0 5.0) (not (<= 0.0 0.0)))",
            "(and (>= var_0 5.0) (not (<= 2.0 0.0)))"
        ]
    );
    assert!(
        document(&out, "test.kf32.cases.never_moves").contains(&"(declare-const var_0 Real)"),
        "the range is one constant of the document"
    );
}

/// A TABLE IS A WORLD FOR EACH ROW, and a LATER CALL IS SELECTED BY WHAT ITS WORLD
/// BOUND: in `within`, the row of `speed_max` binds `?who` to its drone, and `margin`
/// is then that drone's fact — two worlds, not the four of every pairing, one of which
/// (the Follower's 10 with the Leader's 2) would refute a true claim.
#[test]
fn a_table_is_a_world_for_each_row() {
    let out = dry_run("table", TABLE);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    assert_eq!(
        worlds(&out, "test.kf32.table.every_drone_is_bounded"),
        ["(not (<= 8.0 10.0))", "(not (<= 10.0 10.0))"]
    );
    assert_eq!(
        worlds(&out, "test.kf32.table.every_drone_is_slow"),
        ["(not (<= 8.0 8.0))", "(not (<= 10.0 8.0))"]
    );
    assert_eq!(
        worlds(&out, "test.kf32.table.within"),
        ["(not (<= (+ 8.0 2.0) 10.0))", "(not (<= (+ 10.0 0.0) 10.0))"]
    );
    assert_eq!(world_choices(&out, "test.kf32.table.within").len(), 2);
}

/// CHOICES THAT DO NOT SELECT EACH OTHER ARE THEIR PRODUCT, in the order of the choices:
/// the first clause's world first, the last call's choice varying fastest. Each world's
/// comment says every choice it made.
#[test]
fn independent_choices_are_their_product() {
    let out = dry_run(
        "product",
        r#"
namespace test.kf32.product
  import anthill.prelude.PartialOrd.{lte}

  fact gain(1.0)
  fact gain(2.0)
  fact lag(0.5)
  fact lag(1.5)
  rule sum: lte(?g + ?l, 3.5) :- gain(?g), lag(?l)
  proof sum by z3 end
end
"#,
    );
    assert_eq!(
        worlds(&out, "test.kf32.product.sum"),
        [
            "(not (<= (+ 1.0 0.5) 3.5))",
            "(not (<= (+ 1.0 1.5) 3.5))",
            "(not (<= (+ 2.0 0.5) 3.5))",
            "(not (<= (+ 2.0 1.5) 3.5))"
        ]
    );
    let gain = |n: u8| {
        format!("`test.kf32.product.gain/1` (2 fact(s), 0 with a body) is answered by its clause {n} of 2")
    };
    let lag = |n: u8| {
        format!("`test.kf32.product.lag/1` (2 fact(s), 0 with a body) is answered by its clause {n} of 2")
    };
    assert_eq!(
        world_choices(&out, "test.kf32.product.sum"),
        [
            format!("1: {}; {}", gain(1), lag(1)),
            format!("2: {}; {}", gain(1), lag(2)),
            format!("3: {}; {}", gain(2), lag(1)),
            format!("4: {}; {}", gain(2), lag(2)),
        ]
    );
}

/// A RECURSIVE PREDICATE IS REFUSED, AND NOT UNFOLDED (decided with the user). A clause
/// read in a world that calls its own predicate again would be a world for each depth,
/// and a predicate of one such clause has no base case to stop at: `loop` OVERFLOWED THE
/// STACK and aborted the binary (exit 134) on the tree before this change, where it was
/// one clause and read without a choice. Mutual recursion is the same, named where the
/// call stands.
#[test]
fn a_recursive_predicate_is_refused_and_not_unfolded() {
    let out = dry_run(
        "recursive",
        r#"
namespace test.kf32.rec
  import anthill.prelude.PartialOrd.{gte}

  rule loop(?x) :- loop(?x), gte(?x, 0.0)
  rule claim: gte(?x, 0.0) :- loop(?x)
  proof claim by z3 end

  rule ping(?x) :- pong(?x), gte(?x, 0.0)
  rule pong(?x) :- ping(?x)
  rule mutual: gte(?x, 0.0) :- ping(?x)
  proof mutual by z3 end
end
"#,
    );
    assert_ne!(out.code, 134, "no abort; stderr:\n{}", out.stderr);
    let said = refusal(&out, "test.kf32.rec.claim");
    assert!(
        said.contains(
            "the call of `test.kf32.rec.loop/1`, in the body of `test.kf32.rec.loop` (read \
             inlined), is answered by a clause of `test.kf32.rec.loop` with a body while a \
             clause of `test.kf32.rec.loop` is being read: a recursive predicate is not \
             unfolded into a proof's document"
        ) && said.contains("Prove the claim by induction"),
        "{said}"
    );
    let said = refusal(&out, "test.kf32.rec.mutual");
    assert!(
        said.contains(
            "the call of `test.kf32.rec.ping/1`, in the body of `test.kf32.rec.pong` (read \
             inlined), is answered by a clause of `test.kf32.rec.ping` with a body while a \
             clause of `test.kf32.rec.ping` is being read"
        ),
        "{said}"
    );
}

/// AT MOST 64 WORLDS. Two calls of a table of eight are 64, and read; one of eight and
/// one of nine are 72, and refused, naming each choice and how many it had.
#[test]
fn more_worlds_than_the_cap_are_refused() {
    let facts = |name: &str, rows: u8| {
        (1..=rows)
            .map(|n| format!("  fact {name}({n}.0)\n"))
            .collect::<String>()
    };
    let src = format!(
        r#"
namespace test.kf32.cap
  import anthill.prelude.PartialOrd.{{gte}}
{}{}
  rule at_cap: gte(?a + ?b, 0.0) :- t8(?a), t8(?b)
  proof at_cap by z3 end

  rule past_cap: gte(?a + ?b, 0.0) :- t8(?a), t9(?b)
  proof past_cap by z3 end
end
"#,
        facts("t8", 8),
        facts("t9", 9)
    );
    let out = dry_run("cap", &src);
    assert_eq!(worlds(&out, "test.kf32.cap.at_cap").len(), 64);
    let said = refusal(&out, "test.kf32.cap.past_cap");
    assert!(
        said.contains("the body is read in more than 64 worlds")
            && said.contains(
                "`test.kf32.cap.t8/1` (8 fact(s), 0 with a body) — 8 clauses; \
                 `test.kf32.cap.t9/1` (9 fact(s), 0 with a body) — 9 clauses"
            ),
        "{said}"
    );
}

/// A NUMBER IN A BODIED HEAD MET BY A FREE VARIABLE BINDS IT, as a fact's slot does
/// (decided with the user). `mode(?k, ?r)` is a world for each clause, `?k` the number in
/// its head — so `lt(?k, 0.5)`, written after the call, rules the second world out and
/// `low` holds. `one`, of ONE such clause, was refused ("has the number 0.0 … not known
/// to be it"). A variable the frame defined as a computed term, and a computed term, are
/// still refused: that is an equation that is not written.
#[test]
fn a_number_in_a_head_binds_a_free_variable() {
    let out = dry_run(
        "number",
        r#"
namespace test.kf32.number
  import anthill.prelude.PartialOrd.{lte, lt}

  rule mode(0, ?r) :- ?r = 1.0
  rule mode(1, ?r) :- ?r = 2.0
  rule low: lte(?r, 1.0) :- mode(?k, ?r), lt(?k, 0.5)
  proof low by z3 end

  rule only(0, ?r) :- ?r = 1.0
  rule one: lte(?r, 1.0) :- only(?k, ?r)
  proof one by z3 end

  rule shifted: lte(?r, 1.0) :- ?k = ?j + 1.0, only(?k, ?r)
  proof shifted by z3 end
end
"#,
    );
    assert_eq!(
        worlds(&out, "test.kf32.number.low"),
        [
            "(and (< 0.0 0.5) (not (<= 1.0 1.0)))",
            "(and (< 1.0 0.5) (not (<= 2.0 1.0)))"
        ]
    );
    assert_eq!(
        document(&out, "test.kf32.number.one")
            .into_iter()
            .filter(|l| l.starts_with("(assert "))
            .collect::<Vec<_>>(),
        ["(assert (not (<= 1.0 1.0)))"]
    );
    let said = refusal(&out, "test.kf32.number.shifted");
    assert!(
        said.contains(
            "'test.kf32.number.only' has the number 0.0 for an argument of its head, and \
             the call's argument there is not known to be it"
        ),
        "{said}"
    );
    assert_eq!(errors(&out).len(), 1, "stderr:\n{}", out.stderr);
}

/// AN ENTITY PREMISE OVER SEVERAL FACTS is a world for each fact its slots ADMIT, and a
/// slot's variable the frame defined admits by its value as a written number does
/// (`by_var` is the fact of kind 2 alone). A premise no fact admits is refused, one
/// that binds two fields binds both in each world, and a slot that is neither a variable
/// nor a number is refused.
#[test]
fn an_entity_premise_is_a_world_for_each_fact_it_admits() {
    let out = dry_run(
        "entity",
        r#"
namespace test.kf32.entity
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte, lte}

  entity Mode(kind: Float, cap2: Float)
  fact Mode(kind: 1.0, cap2: 5.0)
  fact Mode(kind: 2.0, cap2: -1.0)

  rule by_var: gte(?c, 0.0) :- ?k = 2.0, Mode(kind: ?k, cap2: ?c)
  proof by_var by z3 end

  rule no_row: gte(?c, 0.0) :- Mode(kind: 3.0, cap2: ?c)
  proof no_row by z3 end

  rule both_fields: lte(?k, 2.0) :- Mode(kind: ?k, cap2: ?c), lte(?c, 0.0)
  proof both_fields by z3 end

  rule computed: gte(?c, 0.0) :- Mode(kind: ?j + 1.0, cap2: ?c)
  proof computed by z3 end
end
"#,
    );
    assert_eq!(
        document(&out, "test.kf32.entity.by_var")
            .into_iter()
            .filter(|l| l.starts_with("(assert "))
            .collect::<Vec<_>>(),
        ["(assert (not (>= (- 1.0) 0.0)))"]
    );
    // A slot that is neither a variable nor a number was passed over, and every fact
    // admitted (/code-review): an equation that is not written, refused.
    let said = refusal(&out, "test.kf32.entity.computed");
    assert!(
        said.contains(
            "the premise `test.kf32.entity.Mode` gives its field `kind` a value that is \
             neither a variable nor a number"
        ),
        "{said}"
    );
    let said = refusal(&out, "test.kf32.entity.no_row");
    assert!(
        said.contains("the premise `test.kf32.entity.Mode` is answered by none of the entity's 2 facts"),
        "{said}"
    );
    assert_eq!(
        world_choices(&out, "test.kf32.entity.both_fields"),
        [1, 2].map(|fact| format!(
            "{fact}: the entity `test.kf32.entity.Mode` (2 facts) is answered by its fact \
             {fact} of 2"
        ))
    );
    assert_eq!(
        worlds(&out, "test.kf32.entity.both_fields"),
        [
            "(and (<= 5.0 0.0) (not (<= 1.0 2.0)))",
            "(and (<= (- 1.0) 0.0) (not (<= 2.0 2.0)))"
        ]
    );
}

// ── WHAT /code-review FOUND (the measurement file's §6) ──────────────────────────────

const ROWS: &str = r#"
namespace test.kf32.rows
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte}

  entity Lim(cap: Float)
  fact Lim(cap: 5.0)
  fact Lim(cap: 6.0)
  fact Lim(cap: ?any)
  rule pos: gte(?c, 0.0) :- Lim(cap: ?c)
  proof pos by z3 end

  entity Lone(cap: Float)
  fact Lone(cap: ?any)
  rule lone: gte(?c, 0.0) :- Lone(cap: ?c)
  proof lone by z3 end
end
"#;

/// A ROW WHOSE FIELD IS A VARIABLE IS A WORLD, and the slot is free in it. Only a row with
/// a field that is a number was a row: on 79a6703f `fact Lim(cap: ?any)` beside numbers
/// was no row, and alone it was `cap` = 0.0 — `pos` and `lone` PROVED a claim `Lim(cap:
/// -1.0)` refutes. The first cut of this change read `pos` in the two numeric worlds and
/// proved it too.
#[test]
fn a_row_whose_field_is_a_variable_is_a_world_where_the_slot_is_free() {
    let out = dry_run("rows", ROWS);
    assert_eq!(
        worlds(&out, "test.kf32.rows.pos"),
        ["(not (>= 5.0 0.0))", "(not (>= 6.0 0.0))", "(not (>= var_0 0.0))"]
    );
    let lone = document(&out, "test.kf32.rows.lone");
    assert!(
        lone.contains(&"(declare-const var_0 Real)")
            && lone.contains(&"(assert (not (>= var_0 0.0)))")
            && !lone.iter().any(|l| l.contains("define-fun cap")),
        "{}",
        lone.join("\n")
    );
}

const NAMED: &str = r#"
namespace test.kf32.named
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte, lte}

  fact one_start(5.0)
  rule early_one: gte(?d, -1.0) :- lte(?d, 10.0), one_start(?d)
  proof early_one by z3 end

  fact start(5.0)
  fact start(-1.0)
  rule early_fact: gte(?d, -1.0) :- lte(?d, 10.0), start(?d)
  proof early_fact by z3 end

  entity Lim(cap: Float)
  fact Lim(cap: 5.0)
  fact Lim(cap: -1.0)
  rule ent_early: gte(?c, -1.0) :- lte(?c, 10.0), Lim(cap: ?c)
  proof ent_early by z3 end

  rule mode(0, ?r) :- ?r = 1.0
  rule mode(1, ?r) :- ?r = 2.0
  rule early: lte(?r, 2.0) :- gte(?k, -5.0), mode(?k, ?r)
  proof early by z3 end

  rule pick(0, ?r) :- ?r = 1.0
  rule pick(?n, ?r) :- gte(?n, 5.0), ?r = 1.0
  rule lost: gte(?m, 0.0) :- gte(?m, ?k), pick(?k, ?r)
  proof lost by z3 end

  fact start2(0.0)
  fact start2(1.0)
  rule shift: lte(?j, 0.0) :- ?k = ?j + 1.0, start2(?k)
  proof shift by z3 end
end
"#;

/// A VARIABLE NAMED BEFORE A WORLD GIVES IT A VALUE IS EQUATED WITH THE VALUE, and stays a
/// constant of the document. A fact's slot, an entity's field and a head's number each
/// SUBSTITUTED, and a goal read before kept the variable: one fact, `early_one`, was z3's
/// "unknown constant var_0" on 79a6703f; of several, the variable was declared by a world
/// that did not bind it and unconstrained in the one that did (`lost`, a true claim, was
/// a COUNTEREXAMPLE on the first cut) or still undeclared (`early`). And a variable the
/// body DEFINED as a term (`shift`) had its definition overwritten.
#[test]
fn a_variable_named_before_its_value_is_equated_with_it() {
    let out = dry_run("named", NAMED);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let early_one = document(&out, "test.kf32.named.early_one");
    assert!(
        early_one.contains(&"(declare-const var_0 Real)")
            && early_one.contains(&"(assert (<= var_0 10.0))")
            && early_one.contains(&"(assert (= var_0 5.0))"),
        "{}",
        early_one.join("\n")
    );
    for rule in ["early_fact", "ent_early"] {
        assert_eq!(
            worlds(&out, &format!("test.kf32.named.{rule}")),
            [
                "(and (<= var_0 10.0) (= var_0 5.0) (not (>= var_0 (- 1.0))))",
                "(and (<= var_0 10.0) (= var_0 (- 1.0)) (not (>= var_0 (- 1.0))))"
            ]
        );
    }
    assert_eq!(
        worlds(&out, "test.kf32.named.early"),
        [
            "(and (>= var_0 (- 5.0)) (= var_0 0.0) (not (<= 1.0 2.0)))",
            "(and (>= var_0 (- 5.0)) (= var_0 1.0) (not (<= 2.0 2.0)))"
        ]
    );
    assert_eq!(
        worlds(&out, "test.kf32.named.lost"),
        [
            "(and (>= var_2 var_1) (= var_1 0.0) (not (>= var_2 0.0)))",
            "(and (>= var_2 var_1) (>= var_1 5.0) (not (>= var_2 0.0)))"
        ]
    );
    assert_eq!(
        worlds(&out, "test.kf32.named.shift"),
        [
            "(and (= (+ var_1 1.0) 0.0) (not (<= var_1 0.0)))",
            "(and (= (+ var_1 1.0) 1.0) (not (<= var_1 0.0)))"
        ]
    );
}

/// A VARIABLE WRITTEN TWICE MEETS ONE VALUE. Each position of a call was admitted on its
/// own, so `twice(?k, ?k, ?r)` admitted `twice(0, 1, ?r)`, whose world was then refused
/// whole; `pair(?x, ?x)` read `fact pair(1.0, 2.0)` with `?x` = 2.0 (a COUNTEREXAMPLE on
/// 79a6703f of a body that never holds — now refused as one: no clause can answer); and
/// the entity premise `M(kind: ?x, cap: ?x)` had a world for the row of kind 1 and cap 5.
#[test]
fn a_variable_written_twice_meets_one_value() {
    let out = dry_run(
        "twice",
        r#"
namespace test.kf32.twice
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte}

  rule twice(0, 1, ?r) :- ?r = 1.0
  rule twice(0, 0, ?r) :- ?r = 2.0
  rule tw: gte(?r, 2.0) :- twice(?k, ?k, ?r)
  proof tw by z3 end

  fact pair(1.0, 2.0)
  rule diag_fact: gte(?x, 5.0) :- pair(?x, ?x)
  proof diag_fact by z3 end

  entity M(kind: Float, cap: Float)
  fact M(kind: 1.0, cap: 5.0)
  fact M(kind: 2.0, cap: 2.0)
  rule diag: gte(?x, 2.0) :- M(kind: ?x, cap: ?x)
  proof diag by z3 end
end
"#,
    );
    for rule in ["tw", "diag"] {
        assert_eq!(
            document(&out, &format!("test.kf32.twice.{rule}"))
                .into_iter()
                .filter(|l| l.starts_with("(assert "))
                .collect::<Vec<_>>(),
            ["(assert (not (>= 2.0 2.0)))"],
            "{rule}"
        );
    }
    let said = refusal(&out, "test.kf32.twice.diag_fact");
    assert!(
        said.contains("the call of `test.kf32.twice.pair/2` can be answered by no clause"),
        "{said}"
    );
}

/// A CALL OF ANOTHER PREDICATE IS NO RECURSION, and A VARIABLE PASSED THROUGH AN INLINED
/// RULE IS STILL FREE where a head's number meets it. On the first cut `wide` was refused
/// as recursive — then `span3` was a second clause of `span`, `span/2` beside `span/3`,
/// and the stack held names, not arities — and `wrapped` as "not known to be" the number,
/// where the same call written in the proof read. One name at two arities is refused at
/// load since WI-20260821-6WVJB, so the three-argument relation has a name of its own.
#[test]
fn what_is_read_inlined_is_read_as_it_is_in_the_proof() {
    let out = dry_run(
        "inlined",
        r#"
namespace test.kf32.inlined
  import anthill.prelude.PartialOrd.{gte, lte}

  rule span3(?a, ?b, ?c) :- gte(?a, ?b + ?c)
  rule span(?a, ?b) :- span3(?a, ?b, 0.0)
  rule wide: gte(?x, ?y) :- span(?x, ?y)
  proof wide by z3 end

  rule mode(0, ?r) :- ?r = 1.0
  rule mode(1, ?r) :- ?r = 2.0
  rule wrap(?k, ?r) :- mode(?k, ?r)
  rule wrapped: lte(?r, 2.0) :- wrap(?k, ?r)
  proof wrapped by z3 end
end
"#,
    );
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    assert!(
        document(&out, "test.kf32.inlined.wide").contains(&"(assert (>= var_1 (+ var_0 0.0)))")
    );
    assert_eq!(
        worlds(&out, "test.kf32.inlined.wrapped"),
        ["(not (<= 1.0 2.0))", "(not (<= 2.0 2.0))"]
    );
}

/// THE CONTROL: A BODY THAT MEETS NO CHOICE POINT IS THE DOCUMENT IT WAS, TO THE BYTE —
/// a call one clause answers, by its body and by a fact, and an entity premise of one
/// fact, whose field is still a constant of the document. PASSES WITH THE CHANGE AND
/// WITHOUT IT, by design: these are documents it must not move (the measurement file's
/// §5 has every document of the suites and of lf1 before and after).
#[test]
fn a_body_that_meets_no_choice_is_the_document_it_was() {
    let out = dry_run(
        "none",
        r#"
namespace test.kf32.none
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte, lte}

  rule ordered(?a, ?b) :- gte(?a, ?b)
  fact limit(5.0)
  entity One(top: Float)
  fact One(top: 3.0)

  rule plain: lte(?d, ?t) :- ordered(?a, ?b), limit(?d), One(top: ?t), lte(?d, ?a)
  proof plain by z3 end
end
"#,
    );
    assert_eq!(
        document(&out, "test.kf32.none.plain").join("\n"),
        "; Generated by anthill-smt-gen — satisfiability check for rule test.kf32.none.plain.\n\
         ; `unsat` ⇒ rule body has no solution ⇒ encoded property holds.\n\
         (set-logic LRA)\n\
         \n\
         (define-fun top () Real 3.0)\n\
         \n\
         (declare-const var_0 Real)\n\
         (declare-const var_1 Real)\n\
         \n\
         (assert (>= var_1 var_0))\n\
         (assert (<= 5.0 var_1))\n\
         ; Negated conclusion (from `-:` clause).\n\
         (assert (not (<= 5.0 top)))\n\
         \n\
         (check-sat)"
    );
}

/// THE VERDICTS, by the solver — the ticket's control. The definition by cases: bounded
/// by 2 in both cases, PROVED; never moving is false where the range is 5 or more, a
/// COUNTEREXAMPLE whose model has the range there. The table: bounded by 10, PROVED; slow
/// is false of the Follower's row; `within` PROVED, which the product of the two tables
/// would refute. KF2SD's two — `related` by `gte` and by `lte`, `start` of 5 and -1 — are
/// COUNTEREXAMPLES. And a lemma CITED of a predicate of two clauses discharges each world,
/// the call stated beside it in each: it proved before KF2SD by the lemma and the first
/// clause, and KF2SD refused it.
#[test]
fn the_verdicts_are_the_disjunctions() {
    if !z3_available() {
        return;
    }
    let path = write_temp("kf32_v_cases.anthill", CASES);
    let out = anthill(&["prove", path.to_str().unwrap(), "--no-cache", "-v"]);
    assert!(
        out.has_stdout_line("✓ test.kf32.cases.speed_is_bounded: proved (z3: unsat)")
            && out.has_stdout_line("✗ test.kf32.cases.never_moves: COUNTEREXAMPLE (z3: sat)"),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    let model: Vec<&str> = out
        .stdout
        .lines()
        .map(str::trim)
        .skip_while(|l| *l != "(define-fun var_0 () Real")
        .skip(1)
        .take(1)
        .collect();
    let range: f64 = model
        .first()
        .and_then(|value| value.trim_end_matches(')').parse().ok())
        .unwrap_or_else(|| panic!("the model has the range; stdout:\n{}", out.stdout));
    assert!(range >= 5.0, "the counterexample is where the range is 5 or more: {range}");

    let path = write_temp("kf32_v_table.anthill", TABLE);
    let out = anthill(&["prove", path.to_str().unwrap(), "--no-cache"]);
    for line in [
        "✓ test.kf32.table.every_drone_is_bounded: proved (z3: unsat)",
        "✗ test.kf32.table.every_drone_is_slow: COUNTEREXAMPLE (z3: sat)",
        "✓ test.kf32.table.within: proved (z3: unsat)",
    ] {
        assert!(out.has_stdout_line(line), "{line}\nstdout:\n{}", out.stdout);
    }

    // /code-review's: a row whose field is a variable refutes the claim; a variable named
    // before its value, or defined as a term, is equated and the true claims prove.
    let path = write_temp("kf32_v_rows.anthill", ROWS);
    let out = anthill(&["prove", path.to_str().unwrap(), "--no-cache"]);
    for line in [
        "✗ test.kf32.rows.pos: COUNTEREXAMPLE (z3: sat)",
        "✗ test.kf32.rows.lone: COUNTEREXAMPLE (z3: sat)",
    ] {
        assert!(out.has_stdout_line(line), "{line}\nstdout:\n{}", out.stdout);
    }
    let path = write_temp("kf32_v_named.anthill", NAMED);
    let out = anthill(&["prove", path.to_str().unwrap(), "--no-cache"]);
    assert!(
        out.has_stdout_line("summary: 6 proved, 0 failed, 0 skipped, 6 total"),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );

    let path = write_temp(
        "kf32_v_kf2sd.anthill",
        r#"
namespace test.kf32.kf2sd
  import anthill.prelude.PartialOrd.{gte, lte}

  rule related(?a, ?b) :- gte(?a, ?b)
  rule related(?a, ?b) :- lte(?a, ?b)
  rule lemma: gte(?a, ?b) :- related(?a, ?b)
  proof lemma by z3 end

  fact start(5.0)
  fact start(-1.0)
  rule from_start: gte(?d, 0.0) :- start(?d)
  proof from_start by z3 end

  rule wider: gte(?a, ?b + 1.0) :- related(?a, ?b)
  proof wider by trust(reason: "a control: false, and trusted") end
  rule cited: gte(?x, ?y + 1.0) :- related(?x, ?y)
  proof cited using wider by z3 end
end
"#,
    );
    let out = anthill(&["prove", path.to_str().unwrap(), "--no-cache"]);
    for line in [
        "✗ test.kf32.kf2sd.lemma: COUNTEREXAMPLE (z3: sat)",
        "✗ test.kf32.kf2sd.from_start: COUNTEREXAMPLE (z3: sat)",
        "✓ test.kf32.kf2sd.cited: proved (z3: unsat)",
    ] {
        assert!(
            out.has_stdout_line(line),
            "{line}\nstdout:\n{}\nstderr:\n{}",
            out.stdout,
            out.stderr
        );
    }
}
