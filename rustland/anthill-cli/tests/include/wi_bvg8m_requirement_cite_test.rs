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
//!
//! WI-20261012-ZZ7PH TURNED THE ROWS THIS FILE SAID IT WOULD. A law IS lowered now, over
//! the sort the scope's abstract parameter is, and the chain is followed: the document
//! under a requirement holds its laws (`a_requirement_adds_its_laws_…`), the warning is
//! of a law that does NOT lower and no longer of every law
//! (`the_warning_counts_the_laws_left_out_and_names_them`), `requires Ord[T]` gives the
//! twelve laws of its chain (`the_laws_of_what_a_spec_provides_in_turn_are_read`), and
//! the claim about the carrier that proved of the reals is refused for want of a bound
//! (`a_claim_about_the_carrier_with_no_bound_is_refused`). What a lowered law IS, row by
//! row, is `wi_zz7ph_law_lowering_test`; the rows here still hold what BVG8M built — a
//! proof under a `requires` is run, in a nested sort and for a step too, and what it is
//! not given is said once a run.

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
        .filter(|line| line.contains("not lowered to SMT"))
        .collect()
}

/// The laws a document holds: the lines of its "Laws of the specs …" section.
fn laws_of<'a>(out: &'a Output, query: &str) -> Vec<&'a str> {
    out.stdout
        .lines()
        .skip_while(|l| *l != format!("--- {query} ---"))
        .take_while(|l| *l != "------")
        .skip_while(|l| !l.starts_with("; Laws of the specs the enclosing scopes require."))
        .skip(1)
        .take_while(|l| !l.is_empty())
        .collect()
}

/// `eq_refl` at the abstract parameter `t`: `eq` at it is the carrier's own.
fn eq_refl_at(t: &str) -> String {
    format!(
        "(assert (forall ((var_0 {t})) (= (anthill.prelude.PartialEq.eq@{t} var_0 var_0) true)))"
    )
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
/// it is emitted, and — WI-20261012-ZZ7PH — with the laws it is owed: `Eq`'s `eq_refl`
/// and the `neq` law of the `PartialEq` that `Eq` provides. Nothing is left out, so
/// nothing is said.
#[test]
fn a_proof_under_a_requirement_is_emitted_with_the_laws_it_is_owed() {
    let out = prove_dry_run("under_eq", &fixture("test.bvg8m.eq", REQUIRES_EQ));
    assert_emitted(&out);
    let laws = laws_of(&out, "test.bvg8m.eq.Scope.r");
    assert_eq!(laws.len(), 2, "stdout:\n{}", out.stdout);
    assert_eq!(laws[0], eq_refl_at("test.bvg8m.eq.Scope.T"));
    assert_eq!(laws_left_out(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
}

/// A REQUIREMENT ADDS ITS LAWS AND WHAT THEY DECLARE, AND NOTHING ELSE OF THE DOCUMENT
/// MOVES: take the declarations and the laws out of the document the proof has under
/// `requires Eq[T = T]`, and the `UF` its logic gained for them, and it is the document
/// the proof has without the requirement, to the byte. (This row was
/// `a_law_left_out_changes_nothing_in_the_document`, and said it was the one that would
/// change when a law was lowered.)
#[test]
fn a_requirement_adds_its_laws_and_what_they_declare_and_nothing_else() {
    let with = prove_dry_run("doc_with", &fixture("test.bvg8m.doc", REQUIRES_EQ));
    let without = prove_dry_run("doc_without", &fixture("test.bvg8m.doc", "sort T = ?"));
    assert_emitted(&with);
    assert_emitted(&without);
    // THE CONTROL: the proof with no requirement in scope is given nothing.
    assert_eq!(laws_of(&without, "test.bvg8m.doc.Scope.r"), Vec::<&str>::new());
    assert_eq!(laws_of(&with, "test.bvg8m.doc.Scope.r").len(), 2);
    assert_ne!(with.stdout, without.stdout);

    let mut stripped = String::new();
    let mut in_added_block = false;
    for line in with.stdout.lines() {
        if line.starts_with("; Declared:") || line.starts_with("; Laws of the specs") {
            in_added_block = true;
        }
        if in_added_block {
            in_added_block = !line.is_empty();
            continue;
        }
        stripped.push_str(&line.replace("(set-logic UFLIA)", "(set-logic LIA)"));
        stripped.push('\n');
    }
    assert_eq!(stripped, without.stdout);
    assert_eq!(laws_left_out(&without), Vec::<&str>::new());
    assert_eq!(laws_left_out(&with), Vec::<&str>::new());
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
    // And its document is the one the proof has with no requirement at all, to the byte.
    let without = prove_dry_run("lawless_without", &fixture("test.bvg8m.lawless", "sort T = ?"));
    assert_eq!(out.stdout, without.stdout);
}

/// TWO REQUIREMENTS OF ONE SCOPE, each its own clause: `Lawless` gives nothing and `Eq`
/// its two laws.
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
    let laws = laws_of(&out, "test.bvg8m.two.Scope.r");
    assert_eq!(laws.len(), 2, "stdout:\n{}", out.stdout);
    assert_eq!(laws[0], eq_refl_at("test.bvg8m.two.Scope.T"));
    assert_eq!(laws_left_out(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
}

/// THE WARNING IS OF THE LAWS THAT ARE NOT LOWERED, counted against what the requirement
/// gives and named: `WeakOrd` at `Int64` gives eleven — its nine, `Eq`'s, `PartialEq`'s —
/// and at a concrete carrier none is lowered (a law is asserted of a carrier's own
/// sort). Three of the eleven are cited by a label; the rest are counted by what they
/// are. At the scope's own parameter all eleven lower, and nothing is said.
#[test]
fn the_warning_counts_the_laws_left_out_and_names_them() {
    let out = prove_dry_run(
        "weak_ord_int",
        &fixture("test.bvg8m.woi", "requires anthill.prelude.WeakOrd[T = Int64]"),
    );
    assert_emitted(&out);
    let warning = the_law_warning(
        &out,
        "test.bvg8m.woi.Scope",
        "anthill.prelude.WeakOrd[T = anthill.prelude.Int64]",
    );
    assert!(
        warning.contains(
            ", and 11 of the 11 laws it gives a proof are not lowered to SMT — a `by z3` proof \
             under it runs without: anthill.prelude.WeakOrd.compare_antisym, \
             anthill.prelude.WeakOrd.compare_refl, anthill.prelude.Eq.eq_refl, 7 unlabelled \
             equations, 1 constraint ("
        ),
        "eleven laws, all left out, three named: {warning}"
    );
    assert_eq!(laws_of(&out, "test.bvg8m.woi.Scope.r"), Vec::<&str>::new(), "{}", out.stdout);

    let out = prove_dry_run(
        "weak_ord",
        &fixture(
            "test.bvg8m.wo",
            "sort T = ?\n    requires anthill.prelude.WeakOrd[T = T]",
        ),
    );
    assert_emitted(&out);
    assert_eq!(laws_of(&out, "test.bvg8m.wo.Scope.r").len(), 11, "stdout:\n{}", out.stdout);
    assert_eq!(laws_left_out(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
}

/// THE CHAIN IS FOLLOWED (user, 2026-10-12; WI-20261012-ZZ7PH). `Ord` has one law of
/// its own and provides `WeakOrd`, which has nine and reaches `Eq` and `PartialEq`:
/// twelve. `Strict` has none of its own and provides `Ord`: the same twelve. BVG8M read
/// a spec's OWN laws, and held this row the other way — one law under `Ord`, and
/// nothing at all under `Strict`.
#[test]
fn the_laws_of_what_a_spec_provides_in_turn_are_read() {
    let out = prove_dry_run(
        "chain_ord",
        &fixture(
            "test.bvg8m.ord",
            "sort T = ?\n    requires anthill.prelude.Ord[T = T]",
        ),
    );
    assert_emitted(&out);
    assert_eq!(laws_of(&out, "test.bvg8m.ord.Scope.r").len(), 12, "stdout:\n{}", out.stdout);
    assert_eq!(laws_left_out(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);

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
    assert_eq!(
        laws_of(&out, "test.bvg8m.strict.Scope.r").len(),
        12,
        "`Strict` provides `Ord`; stdout:\n{}",
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
    // The requirement is the OUTER scope's: its law is over the outer scope's parameter.
    let laws = laws_of(&out, "test.bvg8m.nest.Outer.Inner.r");
    assert_eq!(laws.len(), 2, "stdout:\n{}", out.stdout);
    assert_eq!(laws[0], eq_refl_at("test.bvg8m.nest.Outer.T"));
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
    // The step is under the scope's requirement: its document holds the laws. (A dry
    // run stops at the step; the conclusion's query is the verdict row's.)
    let laws = laws_of(&out, "test.bvg8m.step.Scope.big_lemma.h1");
    assert_eq!(laws.len(), 2, "stdout:\n{}", out.stdout);
    assert_eq!(laws[0], eq_refl_at("test.bvg8m.step.Scope.T"));
}

/// ONCE A RUN, however many queries are under the requirement: two proofs of one scope
/// are two queries, and one warning. (The requirement is at `Int64`, where no law is
/// lowered: at the scope's own parameter both are, and there is nothing to say once or
/// twice.)
#[test]
fn a_requirement_is_said_once_a_run() {
    let src = r#"
namespace test.bvg8m.once
  import anthill.prelude.PartialOrd.{gte}
  import anthill.prelude.{Int64}

  sort Scope
    requires anthill.prelude.Eq[T = Int64]

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
        "anthill.prelude.Eq[T = anthill.prelude.Int64]",
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

/// A CLAIM ABOUT THE CARRIER WITH NO BOUND IS REFUSED (WI-20261012-ZZ7PH; user,
/// 2026-10-12). This row was `a_verdict_under_a_requirement_is_about_the_reals`: the
/// document declared `?a` and `?b` `Real` and wrote `gte` as `>=`, whatever they ranged
/// over, so reflexivity of `gte` was the theory's and the rule proved — under a
/// requirement of a spec with no law, and with nothing said. Nothing gives `?a` or `?b`
/// a sort, and under a scope that has an abstract parameter that is now an error that
/// says to write the bound. With `?a: T` the claim is answered of the carrier, and does
/// not prove (`wi_zz7ph_law_lowering_test`).
#[test]
fn a_claim_about_the_carrier_with_no_bound_is_refused() {
    let out = prove_dry_run("reals", ABOUT_THE_CARRIER);
    let errors: Vec<&str> = out.diagnostics("error:").collect();
    assert_eq!(errors.len(), 1, "stderr:\n{}", out.stderr);
    assert!(
        errors[0].starts_with(
            "error: test.bvg8m.reals.Scope.refl_like: `test.bvg8m.reals.Scope.refl_like`: \
             nothing gives `?var_"
        ),
        "{}",
        errors[0]
    );
    assert!(
        !out.stdout.contains("(declare-const"),
        "no document of two `Real` constants:\n{}",
        out.stdout
    );
}

/// THE VERDICTS, where there is a solver: the reproduction proves, its document now
/// holding the laws and a declared sort, under the `LIA` it wrote with `UF` added; the
/// proof under a requirement of a spec with no law proves; the structured proof proves
/// — its step and its conclusion each a query under the requirement; and the claim
/// about the abstract carrier, written with no bound, does NOT prove any more.
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
    assert_eq!(laws_left_out(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);

    let out = prove("verdict_reals", ABOUT_THE_CARRIER);
    assert!(
        !out.stdout.contains("refl_like: proved"),
        "a claim about the carrier is not proved of the reals; stdout:\n{}",
        out.stdout
    );
    assert_eq!(out.diagnostics("error:").count(), 1, "stderr:\n{}", out.stderr);
}
