//! WI-20261012-1P005 — A VARIABLE A PREMISE NAMES BEFORE THE GOAL THAT GIVES IT A VALUE IS
//! A VARIABLE OF THE LIFT: in its quantifier, and equated with the value.
//!
//! A goal read before the binder wrote the variable by its name, and the binder then
//! substituted, so the name was bound and not free: left out of a lift's quantifier it was
//! the consumer's variable of the same index, and `user` — false at x = -5, w = 1 — proved
//! by citing a true, trusted lemma; in the lemma's own document it was not declared, and
//! the solver said "unknown constant". So for each binder after a use: an equation, an
//! entity's field, a fact, a one-argument rule's value, and an equation after a relation
//! written for a premise. Closed by WI-20261014-FHEEK (6f5262ce): every place a variable is
//! given a value equates one the document has written (`Emitter::bind_variable`) — 1P005's
//! option (b), as an equation rather than a substitution into what was written.
//!
//! EVERY ROW BUT `the_verdicts` RUNS `--dry-run` and reads the document.
//!
//! WHAT FAILS WHEN A PART IS BACKED OUT (measured, each alone; `docs/measurements/
//! test-infrastructure/inlined-names-2026-10-14.txt` §9). `the_verdicts` fails with each.
//!   * the equation substituting: `a_variable_named_before_its_binder_is_quantified_in_the_
//!     lift` and `the_lemma_proved_by_the_solver_declares_it` — every lemma's last goal is
//!     that equation;
//!   * the entity's constant substituting: both (`ent`);
//!   * the fact's slot substituting: `the_lemma_proved…` (`fact`);
//!   * the one-argument result substituting: `the_lemma_proved…` (`one`).

use crate::common::{anthill, prove_dry_run, write_temp, z3_available, Output};

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

/// Three trusted lemmas, each naming a variable before the goal that gives it a value, and
/// a false claim citing each.
const LIFTED: &str = r#"
namespace test.p1005.lifted
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte, lte}

  rule eq_lemma: gte(?a, 0.0) :- gte(?kn, 1.0), ?kn = ?a + 1.0
  proof eq_lemma by trust(reason: "a control") end
  rule eq_user: gte(?x, 0.0) :- lte(?x, 100.0), gte(?w, 1.0)
  proof eq_user using eq_lemma by z3 end

  entity Lim(cap: Float)
  fact Lim(cap: 5.0)
  rule ent_lemma: gte(?a, 0.0) :- gte(?c, 1.0), Lim(cap: ?c), ?c = ?a + 1.0
  proof ent_lemma by trust(reason: "a control") end
  rule ent_user: gte(?x, 0.0) :- lte(?x, 100.0), gte(?w, 1.0)
  proof ent_user using ent_lemma by z3 end

  rule related(?a, ?b) :- gte(?a, ?b)
  rule rel_lemma: gte(?a, 0.0) :- related(?k, 1.0), ?k = ?a + 1.0
  proof rel_lemma by trust(reason: "a control") end
  rule rel_user: gte(?x, 0.0) :- lte(?x, 100.0), related(?w, 1.0)
  proof rel_user using rel_lemma by z3 end
end
"#;

/// A VARIABLE NAMED BEFORE ITS BINDER IS QUANTIFIED IN THE LIFT, and equated with what the
/// binder gives it. On d7a8ffcb the lift of `eq_lemma` was `(forall ((var_1 Real)) (=> (>=
/// var_0 1.0) (>= var_1 0.0)))`: `var_0` free, the consumer's `?w`, and `eq_user` proved;
/// so did `ent_user` and `rel_user`. `ent_lemma`'s lift names the field constant `cap`,
/// which its consumer does not declare — so does a lemma whose entity premise comes FIRST,
/// on d7a8ffcb as now (`Lim(cap: ?c), gte(?c, 1.0), …`): the solver refuses the consumer's
/// document, which is loud, and is not of this ticket.
#[test]
fn a_variable_named_before_its_binder_is_quantified_in_the_lift() {
    let out = prove_dry_run("p1005_lifted", LIFTED);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    for (user, premise) in [
        ("eq_user", "(>= var_0 1.0)"),
        ("ent_user", "(>= var_0 1.0) (= var_0 cap)"),
        ("rel_user", "(test.p1005.lifted.related/2 var_0 1.0)"),
    ] {
        let lift = format!(
            "(assert (forall ((var_0 Real) (var_1 Real)) (=> (and {premise} (= var_0 (+ var_1 \
             1.0))) (>= var_1 0.0))))"
        );
        let document = stated(&out, &format!("test.p1005.lifted.{user}"));
        assert!(
            document.contains(&lift.as_str()),
            "`{user}` cites `{lift}`:\n{}",
            document.join("\n")
        );
    }
}

const PROVED: &str = r#"
namespace test.p1005.proved
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte, lte}

  fact start(5.0)
  rule bound(?r) :- ?r = 3.0
  entity Lim(cap: Float)
  fact Lim(cap: 5.0)
  rule related(?a, ?b) :- gte(?a, ?b)

  rule eq_lemma: gte(?a, 0.0) :- gte(?kn, 1.0), ?kn = ?a + 1.0
  proof eq_lemma by z3 end
  rule ent_lemma: gte(?a, 0.0) :- gte(?c, 1.0), Lim(cap: ?c), ?c = ?a + 1.0
  proof ent_lemma by z3 end
  rule fact_lemma: gte(?a, 0.0) :- gte(?k, 1.0), start(?k), ?k = ?a + 1.0
  proof fact_lemma by z3 end
  rule one_lemma: gte(?a, 0.0) :- gte(?k, 1.0), bound(?k), ?k = ?a + 1.0
  proof one_lemma by z3 end
  rule rel_lemma: gte(?a, 0.0) :- related(?k, 1.0), ?k = ?a + 1.0
  proof rel_lemma by z3 end
end
"#;

/// THE LEMMA PROVED BY THE SOLVER DECLARES IT: each of the five binders after a use was
/// "unknown constant var_0" on d7a8ffcb.
#[test]
fn the_lemma_proved_by_the_solver_declares_it() {
    let out = prove_dry_run("p1005_proved", PROVED);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    let lemma = |given: &[&'static str]| -> Vec<&'static str> {
        [
            &[
                "(declare-const var_0 Real)",
                "(declare-const var_1 Real)",
                "(assert (>= var_0 1.0))",
            ][..],
            given,
            &[
                "(assert (= var_0 (+ var_1 1.0)))",
                "(assert (not (>= var_1 0.0)))",
            ],
        ]
        .concat()
    };
    for (rule, expected) in [
        ("eq_lemma", lemma(&[])),
        (
            "ent_lemma",
            [
                vec!["(define-fun cap () Real 5.0)"],
                lemma(&["(assert (= var_0 cap))"]),
            ]
            .concat(),
        ),
        ("fact_lemma", lemma(&["(assert (= var_0 5.0))"])),
        ("one_lemma", lemma(&["(assert (= var_0 3.0))"])),
        ("rel_lemma", lemma(&[])),
    ] {
        assert_eq!(
            stated(&out, &format!("test.p1005.proved.{rule}")),
            expected,
            "the document of `{rule}`"
        );
    }
}

/// The verdicts: the five lemmas prove, and no false claim citing one does — two are
/// COUNTEREXAMPLES, and `ent_user` the solver's refusal of the undeclared `cap` (see
/// `a_variable_named_before_its_binder_is_quantified_in_the_lift`).
#[test]
fn the_verdicts() {
    if !z3_available() {
        return;
    }
    let prove = |name: &str, src: &str| {
        let path = write_temp(&format!("p1005_v_{name}.anthill"), src);
        anthill(&["prove", path.to_str().unwrap(), "--no-cache"])
    };
    let has = |out: &Output, line: &str| {
        assert!(
            out.has_stdout_line(line),
            "`{line}`; stdout:\n{}\nstderr:\n{}",
            out.stdout,
            out.stderr
        );
    };
    let out = prove("proved", PROVED);
    for rule in ["eq_lemma", "ent_lemma", "fact_lemma", "one_lemma", "rel_lemma"] {
        has(&out, &format!("✓ test.p1005.proved.{rule}: proved (z3: unsat)"));
    }
    let out = prove("lifted", LIFTED);
    for user in ["eq_user", "rel_user"] {
        has(
            &out,
            &format!("✗ test.p1005.lifted.{user}: COUNTEREXAMPLE (z3: sat)"),
        );
    }
    assert!(
        !out.stdout.contains("test.p1005.lifted.ent_user: proved"),
        "`ent_user` is false:\n{}",
        out.stdout
    );
}
