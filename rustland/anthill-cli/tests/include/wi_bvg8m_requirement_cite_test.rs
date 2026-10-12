//! WI-20261011-BVG8M — A PROOF IN A SCOPE THAT HAS A `requires` IS RUN, AND WHICH LAWS
//! IT IS NOT GIVEN IS SAID.
//!
//! Proposal 030 γ.4 hands a proof the requirements of its enclosing scopes without its
//! naming them. Each was lowered as a cited rule is — by lifting the rule of the cited
//! name — and a requirement's record is no rule, so every `by z3` proof in a scope that
//! has a `requires` was an error before the solver was asked anything:
//!
//! ```text
//! error: test.imp.Scope.r: cite `test.imp.Scope.requires.anthill.prelude.Eq[T = …]`
//!   (in proof `test.imp.Scope.r`) could not be lowered under its translation policy:
//!   rule '…' not found
//! ```
//!
//! A requirement lowers to the LAWS of the spec it requires now. None is lowered to SMT
//! yet (proposal 030, γ.4: decided and not built), so a law is left out and SAID — a
//! `warning:` names the laws of each requirement, once a run — and a requirement of a
//! spec with no law says nothing. A missing hypothesis can only lose an `unsat`.
//! Decided with the user, 2026-10-12.
//!
//! NO z3 GUARD on the rows that carry the subject. They run `--dry-run`, which prints
//! the SMT document and returns before the solver is invoked — past where the cites are
//! lowered, which is where the refusal was. The last row asks z3 for the verdicts where
//! there is one, and is the only row that can pass having asked nothing.
//!
//! WHAT FAILS WHEN A PART IS BACKED OUT is measured, row by row, in
//! `docs/measurements/test-infrastructure/requirement-cites-2026-10-12.txt` §5.

use crate::common::{anthill, prove_dry_run, write_temp, z3_available, Output};

/// One violation-shape proof whose goal needs no law — `scale` is 5 and the body asks
/// for more than 99 — in the sort `Scope`, whose body is `scope_body` above the proof.
fn fixture(namespace: &str, scope_body: &str) -> String {
    format!(
        r#"
namespace {namespace}
  import anthill.prelude.PartialEq.{{eq}}
  import anthill.prelude.PartialOrd.{{gt}}
  import anthill.prelude.{{Int64}}

  sort Lawless
    sort T = ?
  end

  sort Scope
    {scope_body}

    entity Cfg(scale: Int64)
    fact Cfg(scale: 5)
    rule r(?marker) :- Cfg(scale: ?s), gt(?s, 99), eq(?marker, ?s)
    proof r by z3(logic: "LIA") end
  end
end
"#
    )
}

const REQUIRES_EQ: &str = "sort T = ?\n    requires anthill.prelude.Eq[T = T]";

/// The proof's one assertion, as the document states it: emitted, so not refused.
const THE_BODY: &str = "(assert (> scale 99.0))";

fn assert_emitted(out: &Output) {
    assert_eq!(
        out.diagnostics("error:").collect::<Vec<_>>(),
        Vec::<&str>::new(),
        "a proof under a requirement is not refused; stderr:\n{}",
        out.stderr
    );
    assert!(
        out.stdout.contains(THE_BODY),
        "the proof's document is emitted; stdout:\n{}",
        out.stdout
    );
}

/// The warnings of laws left out, whichever requirement each is of.
fn laws_left_out(out: &Output) -> Vec<&str> {
    out.diagnostics("warning:")
        .filter(|line| line.contains("a spec's law is not lowered to SMT yet"))
        .collect()
}

/// The ONE such warning of `out`, which is of the requirement `scope requires spec`.
fn the_law_warning<'a>(out: &'a Output, scope: &str, spec: &str) -> &'a str {
    let warnings = laws_left_out(out);
    assert_eq!(warnings.len(), 1, "one requirement has a law; stderr:\n{}", out.stderr);
    assert!(
        warnings[0].starts_with(&format!("warning: `{scope}` requires `{spec}`, and")),
        "it is `{scope}`'s requirement of `{spec}`: {}",
        warnings[0]
    );
    warnings[0]
}

/// THE REPRODUCTION, as far as its document. The proof is under `requires Eq[T = T]`;
/// it is emitted, and one warning names the law of `Eq` it runs without.
#[test]
fn a_proof_under_a_requirement_is_emitted_and_the_law_it_is_not_given_is_said() {
    let out = prove_dry_run("under_eq", &fixture("test.bvg8m.eq", REQUIRES_EQ));
    assert_emitted(&out);
    let warning = the_law_warning(
        &out,
        "test.bvg8m.eq.Scope",
        "anthill.prelude.Eq[T = test.bvg8m.eq.Scope.T]",
    );
    assert!(
        warning.ends_with("runs without its law: anthill.prelude.Eq.eq_refl"),
        "{warning}"
    );
}

/// THE DOCUMENT IS THE ONE THE PROOF HAS WITHOUT THE REQUIREMENT, to the byte: a law
/// left out is left out of the document, and nothing else of it moves. This is the row
/// that changes when a law is lowered — the law is then an `(assert (forall …))` here.
#[test]
fn a_law_left_out_changes_nothing_in_the_document() {
    let with = prove_dry_run("doc_with", &fixture("test.bvg8m.doc", REQUIRES_EQ));
    let without = prove_dry_run("doc_without", &fixture("test.bvg8m.doc", "sort T = ?"));
    assert_emitted(&with);
    assert_emitted(&without);
    assert_eq!(with.stdout, without.stdout);
    // THE CONTROL: the proof with no requirement in scope is told nothing.
    assert_eq!(laws_left_out(&without), Vec::<&str>::new());
    assert_eq!(laws_left_out(&with).len(), 1);
}

/// `Lawless` has no law, so a requirement of it lowers to nothing — and there is
/// nothing to say.
#[test]
fn a_requirement_of_a_spec_with_no_law_says_nothing() {
    let out = prove_dry_run(
        "lawless",
        &fixture("test.bvg8m.lawless", "sort T = ?\n    requires Lawless[T = T]"),
    );
    assert_emitted(&out);
    assert_eq!(laws_left_out(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
}

/// TWO REQUIREMENTS OF ONE SCOPE, each its own clause: `Lawless` says nothing and `Eq`
/// names its law, once.
#[test]
fn two_requirements_of_one_scope_are_each_their_own() {
    let out = prove_dry_run(
        "two",
        &fixture(
            "test.bvg8m.two",
            "sort T = ?\n    requires Lawless[T = T]\n    requires anthill.prelude.Eq[T = T]",
        ),
    );
    assert_emitted(&out);
    let warning = the_law_warning(
        &out,
        "test.bvg8m.two.Scope",
        "anthill.prelude.Eq[T = test.bvg8m.two.Scope.T]",
    );
    assert!(warning.ends_with("runs without its law: anthill.prelude.Eq.eq_refl"), "{warning}");
}

/// `WeakOrd` has nine laws — eight equations and a constraint — beside the default
/// bodies of `max` and `min`, which are not laws. Two of the nine are cited by a
/// label; the rest are counted by what they are.
#[test]
fn the_warning_counts_the_laws_and_names_them() {
    let out = prove_dry_run(
        "weak_ord",
        &fixture(
            "test.bvg8m.wo",
            "sort T = ?\n    requires anthill.prelude.WeakOrd[T = T]",
        ),
    );
    assert_emitted(&out);
    let warning = the_law_warning(
        &out,
        "test.bvg8m.wo.Scope",
        "anthill.prelude.WeakOrd[T = test.bvg8m.wo.Scope.T]",
    );
    assert!(
        warning.ends_with(
            "runs without its 9 laws: anthill.prelude.WeakOrd.compare_antisym, \
             anthill.prelude.WeakOrd.compare_refl, 6 unlabelled equations, 1 constraint"
        ),
        "nine laws, two named: {warning}"
    );
}

/// THE CHAIN IS NOT FOLLOWED (user, 2026-10-12): a requirement says the laws of the
/// spec it NAMES. `Ord` has one law of its own and provides `WeakOrd`, which has nine,
/// and reaches `Eq`; `Strict` has none of its own and provides `Ord`. This is the row
/// that changes when the chain is followed — until then what is said under a
/// requirement is not all a holder of it is owed, and for `Strict` it is nothing.
#[test]
fn the_laws_of_what_a_spec_provides_in_turn_are_not_read() {
    let out = prove_dry_run(
        "chain_ord",
        &fixture(
            "test.bvg8m.ord",
            "sort T = ?\n    requires anthill.prelude.Ord[T = T]",
        ),
    );
    assert_emitted(&out);
    let warning = the_law_warning(
        &out,
        "test.bvg8m.ord.Scope",
        "anthill.prelude.Ord[T = test.bvg8m.ord.Scope.T]",
    );
    assert!(
        warning.ends_with("runs without its law: anthill.prelude.Ord.compare_eq"),
        "`Ord`'s own law, and not `WeakOrd`'s nine: {warning}"
    );

    let src = r#"
namespace test.bvg8m.strict
  import anthill.prelude.PartialOrd.{gte}

  sort Strict
    sort T = ?
    provides anthill.prelude.Ord[T = T]
  end

  sort Scope
    sort T = ?
    requires Strict[T = T]

    rule r: gte(?x, 0.0)
      :- gte(?x, 5.0)
    proof r by z3(logic: "LRA") end
  end
end
"#;
    let out = prove_dry_run("chain_strict", src);
    assert_eq!(out.diagnostics("error:").count(), 0, "stderr:\n{}", out.stderr);
    assert!(
        out.stdout.contains("--- test.bvg8m.strict.Scope.r ---"),
        "stdout:\n{}",
        out.stdout
    );
    assert_eq!(laws_left_out(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
}

/// A proof in a sort NESTED under the one that has the requirement is handed it too —
/// the walk is of every enclosing scope — and was refused the same way.
#[test]
fn a_proof_nested_under_a_requirement_is_emitted() {
    let src = r#"
namespace test.bvg8m.nest
  import anthill.prelude.PartialEq.{eq}
  import anthill.prelude.PartialOrd.{gt}
  import anthill.prelude.{Int64}

  sort Outer
    sort T = ?
    requires anthill.prelude.Eq[T = T]

    sort Inner
      entity Cfg(scale: Int64)
      fact Cfg(scale: 5)
      rule r(?marker) :- Cfg(scale: ?s), gt(?s, 99), eq(?marker, ?s)
      proof r by z3(logic: "LIA") end
    end
  end
end
"#;
    let out = prove_dry_run("nested", src);
    assert_emitted(&out);
    // The requirement is the OUTER scope's.
    the_law_warning(
        &out,
        "test.bvg8m.nest.Outer",
        "anthill.prelude.Eq[T = test.bvg8m.nest.Outer.T]",
    );
}

/// A structured proof — one step, and a conclusion that cites it — under a requirement.
const STRUCTURED: &str = r#"
namespace test.bvg8m.step
  import anthill.prelude.PartialOrd.{gte}

  sort Scope
    sort T = ?
    requires anthill.prelude.Eq[T = T]

    rule big_lemma: gte(?x, 0.0)
      :- gte(?x, 5.0)

    proof big_lemma
      rule h1: gte(?x, 3.0)
        :- gte(?x, 5.0)
        by z3(logic: "LRA")

      using h1
      by z3(logic: "LRA")
    end
  end
end
"#;

/// The STEP of a structured proof is a query of its own, dispatched under the step's
/// name — which is under the proof's rule, which is under the scope. It was refused
/// there, before the parent was reached.
#[test]
fn a_step_of_a_structured_proof_under_a_requirement_is_emitted() {
    let out = prove_dry_run("step", STRUCTURED);
    assert_eq!(
        out.diagnostics("error:").collect::<Vec<_>>(),
        Vec::<&str>::new(),
        "stderr:\n{}",
        out.stderr
    );
    assert!(
        out.stdout.contains("--- test.bvg8m.step.Scope.big_lemma.h1 ---"),
        "the step's document is emitted; stdout:\n{}",
        out.stdout
    );
    the_law_warning(
        &out,
        "test.bvg8m.step.Scope",
        "anthill.prelude.Eq[T = test.bvg8m.step.Scope.T]",
    );
}

/// ONCE A RUN, however many queries are under the requirement: two proofs of one scope
/// are two queries, and one warning.
#[test]
fn a_requirement_is_said_once_a_run() {
    let src = r#"
namespace test.bvg8m.once
  import anthill.prelude.PartialOrd.{gte}

  sort Scope
    sort T = ?
    requires anthill.prelude.Eq[T = T]

    rule first: gte(?x, 0.0)
      :- gte(?x, 5.0)
    proof first by z3(logic: "LRA") end

    rule second: gte(?x, 1.0)
      :- gte(?x, 5.0)
    proof second by z3(logic: "LRA") end
  end
end
"#;
    let out = prove_dry_run("once", src);
    assert_eq!(out.diagnostics("error:").count(), 0, "stderr:\n{}", out.stderr);
    for query in ["first", "second"] {
        assert!(
            out.stdout.contains(&format!("--- test.bvg8m.once.Scope.{query} ---")),
            "both proofs are queries of the run; stdout:\n{}",
            out.stdout
        );
    }
    the_law_warning(
        &out,
        "test.bvg8m.once.Scope",
        "anthill.prelude.Eq[T = test.bvg8m.once.Scope.T]",
    );
}

/// A claim about the scope's abstract carrier, under a requirement of it:
/// `gte(?a, ?a)` wherever `gte(?a, ?b)`.
const ABOUT_THE_CARRIER: &str = r#"
namespace test.bvg8m.reals
  import anthill.prelude.PartialOrd.{gte}

  sort Scope
    sort T = ?
    requires anthill.prelude.PartialOrd[T = T]

    rule refl_like: gte(?a, ?a)
      :- gte(?a, ?b)
    proof refl_like by z3(logic: "LRA") end
  end
end
"#;

/// WHAT RUNNING THESE PROOFS DOES NOT MAKE TRUE: a verdict under a requirement is about
/// the REALS, as every verdict of this emitter is. The document declares `?a` and `?b`
/// `Real` and writes `gte` as `>=`, whatever they range over, so reflexivity of `gte`
/// is the theory's — `PartialOrd` has no law, and none was needed. The refusal BVG8M
/// removes kept this proof from running, by accident; the same rule in a scope that
/// requires nothing always ran (/code-review, reproduced). This is the row the
/// carrier's own SMT sort turns (proposal 030, "What a requirement's record lowers to").
#[test]
fn a_verdict_under_a_requirement_is_about_the_reals() {
    let out = prove_dry_run("reals", ABOUT_THE_CARRIER);
    assert_eq!(out.diagnostics("error:").count(), 0, "stderr:\n{}", out.stderr);
    for stated in [
        "(declare-const var_0 Real)",
        "(declare-const var_1 Real)",
        "(assert (>= var_1 var_0))",
        "(assert (not (>= var_1 var_1)))",
    ] {
        assert!(out.stdout.contains(stated), "the document has `{stated}`:\n{}", out.stdout);
    }
    // `PartialOrd` has no law: nothing is left out, and nothing is said.
    assert_eq!(laws_left_out(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
}

/// THE VERDICTS, where there is a solver: the reproduction proves; the proof under a
/// requirement of a spec with no law proves; the structured proof proves — its step and
/// its conclusion each a query under the requirement, and the requirement said once;
/// and the claim about the abstract carrier proves, of the reals.
#[test]
fn the_proofs_under_a_requirement_prove() {
    if !z3_available() {
        return;
    }
    let prove = |name: &str, src: &str| {
        let path = write_temp(&format!("{name}.anthill"), src);
        anthill(&["prove", path.to_str().unwrap(), "--no-cache"])
    };
    let assert_proved = |out: &Output, rule: &str| {
        assert!(
            out.has_stdout_line(&format!("✓ {rule}: proved (z3: unsat)")),
            "`{rule}` proves; stdout:\n{}\nstderr:\n{}",
            out.stdout,
            out.stderr
        );
    };

    let out = prove("verdict_eq", &fixture("test.bvg8m.v", REQUIRES_EQ));
    assert_proved(&out, "test.bvg8m.v.Scope.r");

    let out = prove(
        "verdict_lawless",
        &fixture("test.bvg8m.vl", "sort T = ?\n    requires Lawless[T = T]"),
    );
    assert_proved(&out, "test.bvg8m.vl.Scope.r");

    let out = prove("verdict_step", STRUCTURED);
    assert_proved(&out, "test.bvg8m.step.Scope.big_lemma");
    assert_eq!(
        laws_left_out(&out).len(),
        1,
        "the step and the conclusion are two queries, and the requirement is said once; \
         stderr:\n{}",
        out.stderr
    );

    let out = prove("verdict_reals", ABOUT_THE_CARRIER);
    assert_proved(&out, "test.bvg8m.reals.Scope.refl_like");
}
