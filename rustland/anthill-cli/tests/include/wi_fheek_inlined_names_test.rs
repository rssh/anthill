//! WI-20261014-FHEEK, WI-20261012-BR7P3 — A VARIABLE IS GIVEN A VALUE WHERE THE DOCUMENT
//! HAS WRITTEN IT, AND A RULE READ INLINED HAS VARIABLES OF ITS OWN.
//!
//! FHEEK: `?e = ?d + 1.0, p(?d)`, `p` answering `?d` by a fact, was z3's "unknown constant
//! var_0" where a verdict was owed. The caller's `?e` is the text `(+ var_0 1.0)`, and the
//! value `p` gave `?d` came back by substitution, which left that text naming a variable
//! the document no longer declared. The same at every place a variable is given a value
//! by substitution: an equation, a one-argument rule's result, an entity's field read by
//! its constant, and what an inlined rule hands back. Each now goes through one helper
//! (`Emitter::bind_variable`): a variable the document has written is equated with its
//! value, asked in the frame whose text that is.
//!
//! BR7P3: that helper asks the TEXT, and in a rule read inlined a variable of its own went
//! by the name of the clause's variable of the same index. Measured on d7a8ffcb, three
//! FALSE claims proved — `q2(?x, ?w) :- start(?y), …` beside `lte(?c, 3.0)` equated `q2`'s
//! `?y` with the claim's `?c` — and BR7P3's two reproductions proved satisfiable bodies
//! unsatisfiable. Decided with the user, 2026-10-14: such a variable is named apart, with
//! a name past the clause's own (`var_<n>`, continued). A construction the caller passes
//! is closed over the caller's frame before it crosses, for the same reason the other way:
//! its variables are the caller's.
//!
//! And an ALIAS (`?x = ?y`) given a value gives it to the variable it stands for: the value
//! put in its place left `?y` free, and a true claim of `?y` was a COUNTEREXAMPLE.
//!
//! EVERY ROW BUT `the_verdicts` RUNS `--dry-run` and reads the document, so none passes for
//! want of a solver.
//!
//! WHAT FAILS WHEN A PART IS BACKED OUT (measured, each alone, on this file's rows and
//! CDHSQ's, 1KF32's and KF2SD's; `docs/measurements/test-infrastructure/
//! inlined-names-2026-10-14.txt` §4). `the_verdicts` fails with each but the last two.
//!   * the hand-back substituting: `the_value_an_inlined_rule_gives…`,
//!     `an_inlined_rules_own_variable…` (`by_number`), `a_construction_crosses…`;
//!   * the equation substituting: `every_place_a_variable…`, `an_alias…`;
//!   * the entity's constant substituting: `every_place_a_variable…`;
//!   * the one-argument result substituting: `every_place_a_variable…`,
//!     `the_value_an_inlined_rule_gives…` (`ticket`, the ticket's own program, read by the
//!     one-argument form), `an_alias…` (`by_rule`);
//!   * the naming: `an_inlined_rules_own_variable…`, `an_own_variable_of_a_declared_sort…`,
//!     `every_place_a_variable…`, `a_construction_crosses…`, and CDHSQ's
//!     `a_call_in_an_inlined_rule_that_names_its_own_variable_is_stated_of_it`;
//!   * a construction not closed, the clause's own variable not closed to its name (and
//!     KF2SD's `a_clause_is_selected_by_the_frame_being_read_and_no_other`, whose call
//!     passes one), a closed field met by a head passed over, constructions not read by the
//!     check of what is written, the hand-back compared with the caller's name and not
//!     with what it passed: `a_construction_crosses…`;
//!   * the alias: `an_alias…`;
//!   * the sorts kept: `an_own_variable_of_a_declared_sort…`;
//!   * a variable bound to its own name binding nothing: `an_inlined_rules_own_variable…`;
//!   * the worlds each numbered from the clause's frame: `own_names_run_on…`;
//!   * a construction written as a term: `a_construction_written_as_a_term…`.
//! PASSES EITHER WAY, by design: `a_caller_that_writes_nothing_it_hands_on_has_the_
//! document_it_had`, the documents the change must not move.

use crate::common::{anthill, prove_dry_run, write_temp, z3_available, Output};

fn dry_run(name: &str, src: &str) -> Output {
    prove_dry_run(&format!("fheek_{name}"), src)
}

fn errors(out: &Output) -> Vec<&str> {
    out.diagnostics("error:").collect()
}

/// What the proof `rule`'s document declares and asserts, in order: its lines but the
/// comments, the blank ones and the solver's commands.
fn stated<'a>(out: &'a Output, rule: &str) -> Vec<&'a str> {
    let banner = format!("--- {rule} ---");
    let lines: Vec<&str> = out
        .stdout
        .lines()
        .skip_while(|l| *l != banner)
        .skip(1)
        .take_while(|l| !l.starts_with("------"))
        .map(str::trim)
        .filter(|l| {
            !l.is_empty()
                && !l.starts_with(';')
                && !l.starts_with("(set-")
                && !l.starts_with("(check-sat")
                && !l.starts_with("(get-")
        })
        .collect();
    assert!(
        !lines.is_empty(),
        "`{rule}` has a document; stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    lines
}

/// Each `(rule, document)` of `out` is that document, line for line.
fn documents(out: &Output, namespace: &str, expected: &[(&str, &[&str])]) {
    assert_eq!(errors(out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    documents_ignoring_errors(out, namespace, expected);
}

/// [`documents`] where the caller has read `out`'s errors itself.
fn documents_ignoring_errors(out: &Output, namespace: &str, expected: &[(&str, &[&str])]) {
    for (rule, lines) in expected {
        assert_eq!(
            stated(out, &format!("{namespace}.{rule}")),
            *lines,
            "the document of `{rule}`"
        );
    }
}

/// FHEEK's own program, and what an inlined rule hands back.
const BACK: &str = r#"
namespace test.fheek.back
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte, lte}

  fact start(5.0)
  rule p(?x) :- start(?x)
  rule p2(?x, ?y) :- start(?x), ?y = 0.0
  rule mid(?y, ?z) :- p2(?y, ?z)
  rule dbl(?a, ?r) :- ?r = ?a + ?a

  rule ticket: gte(?e, 0.0) :- ?e = ?d + 1.0, p(?d)
  proof ticket by z3 end
  rule two_args: gte(?e, 0.0) :- ?e = ?d + 1.0, p2(?d, ?z)
  proof two_args by z3 end
  rule nested: gte(?e, 0.0) :- ?e = ?d + 1.0, mid(?d, ?z)
  proof nested by z3 end
  rule by_equation: lte(?r, 10.0) :- lte(?r, 100.0), ?d = 3.0, dbl(?d, ?r)
  proof by_equation by z3 end
  rule defined_by_it: lte(?s, 10.0) :- ?s = ?r + 1.0, ?d = 3.0, dbl(?d, ?r)
  proof defined_by_it by z3 end
end
"#;

/// THE VALUE AN INLINED RULE GIVES A VARIABLE ITS CALLER WROTE IS EQUATED WITH IT, in the
/// caller's frame: the caller's definition of `?e` (`(+ var_1 1.0)`) or its goal
/// (`(<= var_1 100.0)`) names the variable, and the value that came back by substitution
/// left it undeclared — z3's "unknown constant" for each of the five on d7a8ffcb. Through
/// a fact (`ticket`, by the one-argument form; `two_args`, handed back), two rules down
/// (`nested`), and through the inlined rule's own equation (`by_equation`,
/// `defined_by_it`).
#[test]
fn the_value_an_inlined_rule_gives_a_variable_its_caller_wrote_is_equated_with_it() {
    let out = dry_run("back", BACK);
    let at_five: &[&str] = &[
        "(declare-const var_1 Real)",
        "(assert (= var_1 5.0))",
        "(assert (not (>= (+ var_1 1.0) 0.0)))",
    ];
    documents(
        &out,
        "test.fheek.back",
        &[
            (
                "ticket",
                &[
                    "(declare-const var_0 Real)",
                    "(assert (= var_0 5.0))",
                    "(assert (not (>= (+ var_0 1.0) 0.0)))",
                ],
            ),
            ("two_args", at_five),
            ("nested", at_five),
            (
                "by_equation",
                &[
                    "(declare-const var_1 Real)",
                    "(assert (<= var_1 100.0))",
                    "(assert (= var_1 (+ 3.0 3.0)))",
                    "(assert (not (<= var_1 10.0)))",
                ],
            ),
            (
                "defined_by_it",
                &[
                    "(declare-const var_1 Real)",
                    "(assert (= var_1 (+ 3.0 3.0)))",
                    "(assert (not (<= (+ var_1 1.0) 10.0)))",
                ],
            ),
        ],
    );
}

const SITES: &str = r#"
namespace test.fheek.sites
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte, lte}

  rule bound(?r) :- ?r = 3.0
  entity Lim(cap: Float)
  fact Lim(cap: 5.0)
  rule inc(?a, ?b) :- ?b = ?a + 1.0
  rule set4(?a, ?z) :- ?a = 4.0, ?z = 0.0

  rule eq_named: gte(?d, 0.0) :- lte(?d, 10.0), ?d = 3.0
  proof eq_named by z3 end
  rule eq_defined_by: gte(?e, 0.0) :- ?e = ?d + 1.0, ?d = 3.0
  proof eq_defined_by by z3 end
  rule eq_twice: gte(?d, 5.0) :- ?d = 3.0, ?d = 4.0
  proof eq_twice by z3 end
  rule one_named: gte(?r, 0.0) :- lte(?r, 10.0), bound(?r)
  proof one_named by z3 end
  rule one_defined_by: gte(?e, 0.0) :- ?e = ?r + 1.0, bound(?r)
  proof one_defined_by by z3 end
  rule ent_named: gte(?c, 0.0) :- lte(?c, 10.0), Lim(cap: ?c)
  proof ent_named by z3 end
  rule ent_defined_by: gte(?e, 0.0) :- ?e = ?c + 1.0, Lim(cap: ?c)
  proof ent_defined_by by z3 end
  rule itself: gte(?d, 100.0) :- inc(?d, ?d)
  proof itself by z3 end
  rule redefined: gte(?d, 5.0) :- ?d = 3.0, set4(?d, ?z)
  proof redefined by z3 end
end
"#;

/// EVERY PLACE A VARIABLE IS GIVEN A VALUE ASKS WHAT WAS WRITTEN — an equation, a
/// one-argument rule's result, an entity's field read by its constant: each substituted,
/// and a goal or a definition read before named the variable undeclared (z3's "unknown
/// constant" for the six `_named` / `_defined_by` on d7a8ffcb). A variable DEFINED twice is
/// the equation of the two (`eq_twice`, and `redefined`, the second definition an inlined
/// rule's): the second overwrote the first, and a body that cannot hold was a
/// COUNTEREXAMPLE. And `itself`: `inc`'s `?b = ?a + 1.0` with both `?d` — the value names
/// the variable, which `?a`'s binding writes, and is a condition on it; the substitution
/// bound the variable to a term of itself and left it undeclared.
#[test]
fn every_place_a_variable_is_given_a_value_asks_what_was_written() {
    let out = dry_run("sites", SITES);
    let named = |value: &'static str| -> Vec<String> {
        vec![
            "(declare-const var_0 Real)".to_owned(),
            "(assert (<= var_0 10.0))".to_owned(),
            format!("(assert (= var_0 {value}))"),
            "(assert (not (>= var_0 0.0)))".to_owned(),
        ]
    };
    let defined_by = |value: &'static str| -> Vec<String> {
        vec![
            "(declare-const var_0 Real)".to_owned(),
            format!("(assert (= var_0 {value}))"),
            "(assert (not (>= (+ var_0 1.0) 0.0)))".to_owned(),
        ]
    };
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let cap = "(define-fun cap () Real 5.0)".to_owned();
    for (rule, expected) in [
        ("eq_named", named("3.0")),
        ("eq_defined_by", defined_by("3.0")),
        ("one_named", named("3.0")),
        ("one_defined_by", defined_by("3.0")),
        ("ent_named", [vec![cap.clone()], named("cap")].concat()),
        ("ent_defined_by", [vec![cap.clone()], defined_by("cap")].concat()),
    ] {
        assert_eq!(
            stated(&out, &format!("test.fheek.sites.{rule}")),
            expected,
            "the document of `{rule}`"
        );
    }
    documents(
        &out,
        "test.fheek.sites",
        &[
            ("eq_twice", &["(assert (= 3.0 4.0))", "(assert (not (>= 3.0 5.0)))"]),
            ("redefined", &["(assert (= 3.0 4.0))", "(assert (not (>= 3.0 5.0)))"]),
            (
                "itself",
                &[
                    "(declare-const var_0 Real)",
                    "(assert (= var_0 (+ var_0 1.0)))",
                    "(assert (not (>= var_0 100.0)))",
                ],
            ),
        ],
    );
}

const OWN: &str = r#"
namespace test.fheek.own
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte, lte, lt}

  rule helper(?x, ?w) :- lt(?x, ?y), lt(?y, ?w)
  rule apart :- helper(?a, ?b), gte(?a, 5.0)
  proof apart by z3 end
  rule shifted(?r) :- ?r = ?y + 1.0, gte(?y, 0.0)
  rule one_arg :- shifted(?v), lt(?z, 0.0), gte(?v, 0.0)
  proof one_arg by z3 end

  fact start(5.0)
  rule q2(?x, ?w) :- start(?y), ?x = ?w
  rule by_fact: gte(?a, 100.0) :- lte(?c, 3.0), q2(?a, ?a)
  proof by_fact by z3 end
  rule mode(0, ?r) :- ?r = 1.0
  rule via_mode(?x, ?w) :- mode(?y, ?w), ?x = ?w
  rule by_number: gte(?a, 100.0) :- lte(?c, -3.0), via_mode(?a, ?a)
  proof by_number by z3 end
  entity Lim(cap: Float)
  fact Lim(cap: 5.0)
  fact Lim(cap: 6.0)
  rule via_lim(?x, ?w) :- Lim(cap: ?y), ?x = ?w
  rule by_row: gte(?a, 100.0) :- lte(?c, 3.0), via_lim(?a, ?a)
  proof by_row by z3 end
end
"#;

/// AN INLINED RULE'S OWN VARIABLE IS NAMED APART FROM THE CLAUSE'S: past them, `var_2` for
/// a clause of two. By its index it was the clause's variable of that index. BR7P3's two
/// reproductions (`apart`: `helper`'s `?y` was `apart`'s `?b`, `(< var_0 var_0)`;
/// `one_arg`: `shifted`'s `?y` was `one_arg`'s `?z`) proved satisfiable bodies
/// unsatisfiable. And 1KF32's helper, asking the text, EQUATED the two where a fact
/// (`by_fact`), a head's number (`by_number`) or an entity's row (`by_row`) gave the rule's
/// own `?y` a value — `(= var_0 5.0)` beside the claim's `(<= var_0 3.0)` — and the three
/// false claims proved. Now `?y` is substituted where nothing wrote it, as before 1KF32.
#[test]
fn an_inlined_rules_own_variable_is_named_apart_from_the_clauses() {
    let out = dry_run("own", OWN);
    let row = "(and (<= var_0 3.0) (not (>= var_1 100.0)))";
    documents(
        &out,
        "test.fheek.own",
        &[
            (
                "apart",
                &[
                    "(declare-const var_0 Real)",
                    "(declare-const var_1 Real)",
                    "(declare-const var_2 Real)",
                    "(assert (< var_1 var_2))",
                    "(assert (< var_2 var_0))",
                    "(assert (>= var_1 5.0))",
                ],
            ),
            (
                "one_arg",
                &[
                    "(declare-const var_0 Real)",
                    "(declare-const var_3 Real)",
                    "(assert (>= var_3 0.0))",
                    "(assert (< var_0 0.0))",
                    "(assert (>= (+ var_3 1.0) 0.0))",
                ],
            ),
            (
                "by_fact",
                &[
                    "(declare-const var_0 Real)",
                    "(declare-const var_1 Real)",
                    "(assert (<= var_0 3.0))",
                    "(assert (not (>= var_1 100.0)))",
                ],
            ),
            (
                "by_number",
                &[
                    "(declare-const var_0 Real)",
                    "(declare-const var_1 Real)",
                    "(assert (<= var_0 (- 3.0)))",
                    "(assert (= var_1 1.0))",
                    "(assert (not (>= var_1 100.0)))",
                ],
            ),
            (
                "by_row",
                &[
                    "(declare-const var_0 Real)",
                    "(declare-const var_1 Real)",
                    "(assert (or",
                    row,
                    row,
                    "))",
                ],
            ),
        ],
    );
}

/// AN OWN VARIABLE OF A DECLARED SORT IS DECLARED AT IT (BR7P3's control). `between`'s
/// `?b` is of `T` by what it is compared with, and is named past `p`'s frame — `var_5`, the
/// frame holding the parameter's slots too. By its index it was `p`'s `?y`: the document
/// said `(lt@T var_1 var_1)`.
#[test]
fn an_own_variable_of_a_declared_sort_is_declared_at_it() {
    let out = dry_run(
        "sorted",
        r#"
namespace test.fheek.sorted
  import anthill.prelude.PartialOrd.{lt}

  sort Scope
    sort T = ?
    requires anthill.prelude.PartialOrd[T = T]

    rule between(?a: T, ?c: T) :- lt(?a, ?b), lt(?b, ?c)
    rule p(?x: T, ?y: T) :- between(?x, ?y), lt(?y, ?x)
    proof p by z3 end
  end
end
"#,
    );
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let t = "test.fheek.sorted.Scope.T";
    let lt = format!("anthill.prelude.PartialOrd.lt@{t}");
    let document = stated(&out, "test.fheek.sorted.Scope.p");
    for line in [
        format!("(declare-const var_5 {t})"),
        format!("(assert ({lt} var_2 var_5))"),
        format!("(assert ({lt} var_5 var_1))"),
        format!("(assert ({lt} var_1 var_2))"),
    ] {
        assert!(document.contains(&line.as_str()), "`{line}`:\n{}", document.join("\n"));
    }
}

const CTOR: &str = r#"
namespace test.fheek.ctor
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte, lte}
  import anthill.prelude.Option.{some, none}

  entity P(x: Float, y: Float)
  rule fx(?p, ?r) :- lte(?w, 0.0), ?r = ?p.x
  rule passed: lte(?r, 0.0) :- gte(?a, 1.0), fx(P(x: ?a, y: 0.0), ?r)
  proof passed by z3 end
  rule held: gte(?r, 1.0) :- gte(?a, 1.0), ?q = P(x: ?a, y: 0.0), fx(?q, ?r)
  proof held by z3 end

  fact start(5.0)
  rule mk(?d, ?p) :- ?p = P(x: ?d, y: 0.0)
  rule built: gte(?e, 0.0) :- mk(?d, ?p), start(?d), ?e = ?p.x
  proof built by z3 end

  rule get(some(?x), ?r) :- ?r = ?x
  rule get(none, ?r) :- ?r = 0.0
  rule fwd(some(?x), ?r) :- get(some(?x), ?r)
  rule leaf: gte(?r, 1.0) :- lte(1.0, ?a), fwd(some(?a), ?r)
  proof leaf by z3 end
  rule fwdVar(?o, ?r) :- get(?o, ?r)
  rule leafVar: gte(?r, 1.0) :- lte(1.0, ?a), fwdVar(some(?a), ?r)
  proof leafVar by z3 end

  sort OF
    entity nf
    entity sf(v: Float)
  end
  import test.fheek.ctor.OF.{nf, sf}
  rule getN(sf(?x), ?r) :- ?r = ?x
  rule getN(nf, ?r) :- ?r = 0.0
  rule fwdN(?o, ?r) :- getN(?o, ?r)
  rule leafN: gte(?r, 1.0) :- lte(1.0, ?a), fwdN(sf(?a), ?r)
  proof leafN by z3 end
end
"#;

/// A CONSTRUCTION CROSSES INTO AN INLINED RULE CLOSED OVER ITS CALLER'S FRAME: its
/// variables are the caller's, and read in the rule's frame by their indices they were the
/// rule's. `passed`: `fx`'s `?p.x` is the claim's `?a`, which by its index was `fx`'s own
/// `?w`, so `r = w` with `w <= 0`, and the false claim proved on d7a8ffcb; with the naming
/// alone it is `fx`'s `var_3`, and it proves still. `held`: the clause's own `?a`, which
/// nothing binds, closes to its own name — refused on d7a8ffcb ("cannot be closed across
/// the inline boundary"). `built`: a construction holding the caller's `?d` names it, and
/// the value `start` gives `?d` is equated with it — z3's "unknown constant" on d7a8ffcb.
/// `leaf`: a field of a closed construction met by a head's variable (`get(some(?x), …)`)
/// is what the caller passed there — it was passed over, and the true claim was a
/// COUNTEREXAMPLE.
///
/// `leaf` passes the construction through `fwd`'s head `some(?x)`; through a column of
/// `fwd`'s, `leafVar` as `leaf` was written, it is refused since WI-20261013-WF14Z (user
/// decision 2026-10-22: an inferred bound is as written): `get(?o, ?r)` types the column `?o`
/// at `get`'s, an `Option[T = t]`, a bound no SMT sort lowers — as the written `fwd(?o:
/// Option[T = ?t], ?r)` was refused before. Its document was `leaf`'s, and it is `leafN`'s,
/// the same claim through a column over an option sort with no parameter (`OF`), which gets
/// no bound.
#[test]
fn a_construction_crosses_into_an_inlined_rule_closed_over_its_callers_frame() {
    let out = dry_run("ctor", CTOR);
    let refused: Vec<&str> = errors(&out);
    assert!(
        refused.len() == 1
            && refused[0].contains("test.fheek.ctor.leafVar: the bound of")
            && refused[0].contains("has no SMT sort"),
        "stderr:\n{}",
        out.stderr
    );
    documents_ignoring_errors(
        &out,
        "test.fheek.ctor",
        &[
            (
                "passed",
                &[
                    "(declare-const var_0 Real)",
                    "(declare-const var_3 Real)",
                    "(assert (>= var_0 1.0))",
                    "(assert (<= var_3 0.0))",
                    "(assert (not (<= var_0 0.0)))",
                ],
            ),
            (
                "held",
                &[
                    "(declare-const var_1 Real)",
                    "(declare-const var_3 Real)",
                    "(assert (>= var_1 1.0))",
                    "(assert (<= var_3 0.0))",
                    "(assert (not (>= var_1 1.0)))",
                ],
            ),
            (
                "built",
                &[
                    "(declare-const var_1 Real)",
                    "(assert (= var_1 5.0))",
                    "(assert (not (>= var_1 0.0)))",
                ],
            ),
            (
                "leaf",
                &[
                    "(declare-const var_0 Real)",
                    "(assert (<= 1.0 var_0))",
                    "(assert (not (>= var_0 1.0)))",
                ],
            ),
            (
                "leafN",
                &[
                    "(declare-const var_0 Real)",
                    "(assert (<= 1.0 var_0))",
                    "(assert (not (>= var_0 1.0)))",
                ],
            ),
        ],
    );
}

/// AN INLINED RULE'S OWN NAMES RUN ON ACROSS THE WORLDS OF ONE DOCUMENT: the worlds are
/// disjuncts of one document, and a name of it is one constant. Numbered in each world from
/// the clause's frame, `two`'s clause 1 named its `?b` (of `T`) and clause 2 its `?c` (a
/// real) alike, and the proof was refused — "of sort T in one world … and of Real in
/// another" (/code-review, measured); on d7a8ffcb it was z3's "unknown constant".
#[test]
fn own_names_run_on_across_the_worlds_of_a_document() {
    let out = dry_run(
        "worlds",
        r#"
namespace test.fheek.many
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte, lte, lt}

  sort Scope
    sort T = ?
    requires anthill.prelude.PartialOrd[T = T]

    rule two(?a: T, ?k) :- lt(?a, ?b), ?k = 0.0
    rule two(?a: T, ?k) :- lte(?c, 1.0), ?k = 1.0
    rule worlds(?x: T) :- two(?x, ?k), gte(?k, 5.0)
    proof worlds by z3 end
  end
end
"#,
    );
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let t = "test.fheek.many.Scope.T";
    let document = stated(&out, "test.fheek.many.Scope.worlds");
    for line in [
        format!("(declare-const var_2 {t})"),
        format!("(declare-const var_4 {t})"),
        "(declare-const var_6 Real)".to_owned(),
        format!("(and (anthill.prelude.PartialOrd.lt@{t} var_2 var_4) (>= 0.0 5.0))"),
        "(and (<= var_6 1.0) (>= 1.0 5.0))".to_owned(),
    ] {
        assert!(document.contains(&line.as_str()), "`{line}`:\n{}", document.join("\n"));
    }
}

/// A CONSTRUCTION WRITTEN AS A TERM IS REFUSED, in the clause's own frame and in an
/// inlined rule's. `related(?a, ?b) :- gte(?a, ?b)` read of a variable bound to `P(x:
/// 1.0)` wrote it as a variable nothing ties to the construction — `(>= var_0 var_1)` in
/// `top`, a COUNTEREXAMPLE on d7a8ffcb. Inside `wrap` it was CDHSQ's refusal of `?p` as the
/// rule's own variable, which BR7P3's naming retired; it is this refusal now (/code-review).
/// The claims compare `?y` with itself: `related` ties its two columns to one type, so `?y`
/// is a `P`, and a `Float` beside it is refused at load (068-implementation §6.2, decision 3).
#[test]
fn a_construction_written_as_a_term_is_refused() {
    let out = dry_run(
        "built_term",
        r#"
namespace test.fheek.built_term
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte, lte}

  entity P(x: Float)
  rule related(?a, ?b) :- gte(?a, ?b)
  rule lemma: gte(?a, ?b + 1.0) :- related(?a, ?b)
  proof lemma by trust(reason: "a control") end

  rule wrap(?p, ?q) :- related(?p, ?q)
  rule inl: gte(?y, ?y) :- wrap(P(x: 1.0), ?y)
  proof inl using lemma by z3 end

  rule top: gte(?y, ?y) :- ?p = P(x: 1.0), related(?p, ?y)
  proof top using lemma by z3 end
end
"#,
    );
    let said = errors(&out);
    assert_eq!(said.len(), 2, "stderr:\n{}", out.stderr);
    for rule in ["inl", "top"] {
        assert!(
            said.iter().any(|e| e.starts_with(&format!("error: test.fheek.built_term.{rule}: "))
                && e.contains("is a construction, which has no SMT term")),
            "`{rule}` refused:\n{}",
            out.stderr
        );
    }
}

const ALIAS: &str = r#"
namespace test.fheek.alias
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte}

  fact start(5.0)
  rule p(?a) :- start(?a)
  rule by_fact: gte(?y, 0.0) :- ?x = ?y, start(?x)
  proof by_fact by z3 end
  rule by_equation: gte(?y, 0.0) :- ?x = ?y, ?x = 5.0
  proof by_equation by z3 end
  rule by_rule: gte(?y, 0.0) :- ?x = ?y, p(?x)
  proof by_rule by z3 end
end
"#;

/// AN ALIAS GIVEN A VALUE GIVES IT TO THE VARIABLE IT STANDS FOR. `?x = ?y` binds `?x` to
/// `?y`'s name; the value a fact, an equation or a rule then gave `?x` was put in its
/// place, `?y` was left free, and each true claim of `?y` was a COUNTEREXAMPLE on d7a8ffcb
/// (and on 79a6703f, before 1KF32's helper).
#[test]
fn an_alias_given_a_value_gives_it_to_the_variable_it_stands_for() {
    let out = dry_run("alias", ALIAS);
    let to_y: &[&str] = &[
        "(declare-const var_1 Real)",
        "(assert (= var_1 5.0))",
        "(assert (not (>= var_1 0.0)))",
    ];
    documents(
        &out,
        "test.fheek.alias",
        &[("by_fact", to_y), ("by_equation", to_y), ("by_rule", to_y)],
    );
}

/// A CALLER THAT WRITES NOTHING IT HANDS ON HAS THE DOCUMENT IT HAD — the value
/// substituted, byte for byte what d7a8ffcb emits: through a rule of two arguments, of
/// one, a fact read directly, and a variable nothing gives a value. PASSES EITHER WAY, by
/// design: these are the documents the change must not move (lf1's sixteen and the
/// suites' are the same, `inlined-names-2026-10-14.txt` §5).
#[test]
fn a_caller_that_writes_nothing_it_hands_on_has_the_document_it_had() {
    let out = dry_run(
        "control",
        r#"
namespace test.fheek.control
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte, lte}

  fact start(5.0)
  rule p(?x) :- start(?x)
  rule p2(?x, ?y) :- start(?x), ?y = 0.0
  rule passes: gte(?e, 0.0) :- p2(?d, ?z), ?e = ?d + 1.0
  proof passes by z3 end
  rule one: gte(?e, 0.0) :- p(?d), ?e = ?d + 1.0
  proof one by z3 end
  rule direct: gte(?e, 0.0) :- start(?d), ?e = ?d + 1.0
  proof direct by z3 end
  rule free: gte(?e, 0.0) :- lte(?d, 1.0), ?e = ?d + 1.0
  proof free by z3 end
end
"#,
    );
    let substituted: &[&str] = &["(assert (not (>= (+ 5.0 1.0) 0.0)))"];
    documents(
        &out,
        "test.fheek.control",
        &[
            ("passes", substituted),
            ("one", substituted),
            ("direct", substituted),
            (
                "free",
                &[
                    "(declare-const var_0 Real)",
                    "(assert (<= var_0 1.0))",
                    "(assert (not (>= (+ var_0 1.0) 0.0)))",
                ],
            ),
        ],
    );
}

/// The verdicts, by the solver: every claim above that holds is proved, and every one that
/// does not is a COUNTEREXAMPLE.
#[test]
fn the_verdicts() {
    if !z3_available() {
        return;
    }
    let prove = |name: &str, src: &str| {
        let path = write_temp(&format!("fheek_v_{name}.anthill"), src);
        anthill(&["prove", path.to_str().unwrap(), "--no-cache"])
    };
    let verdicts = |out: &Output, namespace: &str, proved: &[&str], refuted: &[&str]| {
        for (rules, line) in [
            (proved, "proved (z3: unsat)"),
            (refuted, "COUNTEREXAMPLE (z3: sat)"),
        ] {
            for rule in rules {
                let mark = if line.starts_with("proved") { '✓' } else { '✗' };
                let expected = format!("{mark} {namespace}.{rule}: {line}");
                assert!(
                    out.has_stdout_line(&expected),
                    "`{expected}`; stdout:\n{}\nstderr:\n{}",
                    out.stdout,
                    out.stderr
                );
            }
        }
    };
    verdicts(
        &prove("back", BACK),
        "test.fheek.back",
        &["ticket", "two_args", "nested", "by_equation", "defined_by_it"],
        &[],
    );
    verdicts(
        &prove("sites", SITES),
        "test.fheek.sites",
        &[
            "eq_named",
            "eq_defined_by",
            "eq_twice",
            "one_named",
            "one_defined_by",
            "ent_named",
            "ent_defined_by",
            "itself",
            "redefined",
        ],
        &[],
    );
    verdicts(
        &prove("own", OWN),
        "test.fheek.own",
        &[],
        &["apart", "one_arg", "by_fact", "by_number", "by_row"],
    );
    verdicts(
        &prove("ctor", CTOR),
        "test.fheek.ctor",
        &["held", "built", "leaf", "leafN"],
        &["passed"],
    );
    verdicts(
        &prove("alias", ALIAS),
        "test.fheek.alias",
        &["by_fact", "by_equation", "by_rule"],
        &[],
    );
    // CDHSQ's `a_call_in_an_inlined_rule_that_names_its_own_variable_is_stated_of_it`:
    // the relation stated of `wrap2`'s own `?r`, and `deep` false at x = 0, y = 50.
    verdicts(
        &prove(
            "stated",
            r#"
namespace test.fheek.stated
  import anthill.prelude.PartialOrd.{gte, lte}

  rule related(?a, ?b) :- gte(?a, ?b)
  rule wrap2(?p, ?q) :- related(?p, ?r), gte(?q, 0.0)

  rule lemma: gte(?a, ?b + 1.0) :- related(?a, ?b)
  proof lemma by trust(reason: "a control") end

  rule deep: gte(?x, ?y + 1.0) :- wrap2(?x, ?x), lte(?y, 100.0)
  proof deep using lemma by z3 end
end
"#,
        ),
        "test.fheek.stated",
        &[],
        &["deep"],
    );
}
