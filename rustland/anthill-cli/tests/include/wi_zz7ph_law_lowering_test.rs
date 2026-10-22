//! WI-20261012-ZZ7PH — A SPEC'S LAW IS LOWERED TO SMT, OVER THE SORT THE SCOPE'S ABSTRACT
//! PARAMETER IS.
//!
//! WI-20261011-BVG8M ran a proof under a `requires` and gave it no hypothesis: a law was
//! left out and said. And what it ran was answered of the REALS — every operand a `Real`,
//! `PartialEq.eq` as `=`, `PartialOrd.gte` as `>=` — so `gte(?a, ?a) :- gte(?a, ?b)`
//! proved under `requires PartialOrd[T = T]`, of a carrier nothing was known about.
//!
//! Now (proposal 030, "What a requirement's record lowers to"; decided with the user,
//! 2026-10-12, on the count in
//! `docs/measurements/test-infrastructure/law-lowering-2026-10-12.txt`):
//!
//!   * the scope's abstract parameter is ITS OWN SMT SORT, and a spec's operation at it
//!     an UNINTERPRETED FUNCTION, `eq` included, declared once for the law and the body;
//!   * a variable has its sort by its BOUND (`?a: T`), or by the signature of an
//!     operation it is an operand of; one that neither gives a sort is REFUSED under a
//!     scope that has an abstract parameter;
//!   * a requirement gives the laws of its spec AND of what that requires or provides in
//!     turn, each an `(assert (forall …))`;
//!   * a law is asserted of a carrier's OWN sort and of nothing else: at a concrete
//!     carrier (`requires Eq[T = Int64]`) no law is lowered, and that is said — the
//!     emitter models `Int64` and `Float` by the theory's reals, where a law is a theorem
//!     already or is not known to hold (found by /code-review: the first cut asserted a
//!     law there, and one true of the integers and false of the reals proved anything);
//!   * the logic is the one written, with what the document needs beyond it.
//!
//! THE ROWS THAT CARRY THE SUBJECT RUN `--dry-run` and read the document, so none passes
//! for want of a solver. The verdict rows are one test, guarded, at the foot.
//!
//! WHAT FAILS WHEN A PART IS BACKED OUT is measured, row by row, in the measurement
//! file's §5.

use crate::common::{anthill, prove_dry_run, write_temp, z3_available, Output};

/// One proof `p`, in the sort `Scope` of `test.zz7ph.<name>`, which has the abstract
/// parameter `T` and `scope_body` above the rule.
fn in_scope(name: &str, scope_body: &str, rule: &str, tactic: &str) -> String {
    format!(
        r#"
namespace test.zz7ph.{name}
  import anthill.prelude.PartialEq.{{eq, neq}}
  import anthill.prelude.PartialOrd.{{gte, gt}}
  import anthill.prelude.{{Int64, Float}}

  sort Scope
    sort T = ?
    {scope_body}

    {rule}
    proof p by {tactic} end
  end
end
"#
    )
}

/// The sort `Scope.T` of `test.zz7ph.<name>` is, in a document.
fn carrier(name: &str) -> String {
    format!("test.zz7ph.{name}.Scope.T")
}

fn errors(out: &Output) -> Vec<&str> {
    out.diagnostics("error:").collect()
}

/// The warnings of laws that were not lowered.
fn laws_not_lowered(out: &Output) -> Vec<&str> {
    out.diagnostics("warning:")
        .filter(|line| line.contains("not lowered to SMT"))
        .collect()
}

fn assert_stated(out: &Output, lines: &[String]) {
    assert_eq!(errors(out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    for line in lines {
        assert!(
            out.stdout.lines().any(|l| l == line),
            "the document has the line\n  {line}\nstdout:\n{}",
            out.stdout
        );
    }
}

/// The laws a document holds: the lines of its "Laws of the specs …" section.
fn laws_of(out: &Output) -> Vec<&str> {
    out.stdout
        .lines()
        .skip_while(|l| !l.starts_with("; Laws of the specs the enclosing scopes require."))
        .skip(1)
        .take_while(|l| !l.is_empty())
        .collect()
}

const IRREFLEXIVE: &str = "rule p(?a: T) :- neq(?a, ?a)";

/// THE CONTROL, as far as its document: `neq(?a, ?a)` for a `?a: T` under `requires
/// Eq[T = T]`. The parameter is a declared sort; `eq` and `neq` at it are declared
/// functions; `?a` is a constant of the sort; and `Eq`'s `eq_refl` and the `neq` law of
/// the `PartialEq` that `Eq` provides are each an `(assert (forall …))` over it.
///
/// This is the document BVG8M's `a_law_left_out_changes_nothing_in_the_document` said
/// would change.
#[test]
fn a_law_is_an_assertion_over_the_parameters_own_sort() {
    let out = prove_dry_run(
        "irr",
        &in_scope(
            "irr",
            "requires anthill.prelude.Eq[T = T]",
            IRREFLEXIVE,
            "z3",
        ),
    );
    let t = carrier("irr");
    let eq = format!("anthill.prelude.PartialEq.eq@{t}");
    let neq = format!("anthill.prelude.PartialEq.neq@{t}");
    assert_stated(
        &out,
        &[
            format!("(declare-sort {t} 0)"),
            format!("(declare-fun {eq} ({t} {t}) Bool)"),
            format!("(declare-fun {neq} ({t} {t}) Bool)"),
            format!("(declare-const var_1 {t})"),
            format!("(assert (forall ((var_0 {t})) (= ({eq} var_0 var_0) true)))"),
            format!(
                "(assert (forall ((var_0 {t}) (var_1 {t})) \
                 (= ({neq} var_1 var_0) (not ({eq} var_1 var_0)))))"
            ),
            format!("(assert ({neq} var_1 var_1))"),
        ],
    );
    assert_eq!(
        laws_of(&out).len(),
        2,
        "`Eq`'s law and `PartialEq`'s:\n{}",
        out.stdout
    );
    // Every law lowered: nothing is left out, and nothing is said.
    assert_eq!(
        laws_not_lowered(&out),
        Vec::<&str>::new(),
        "stderr:\n{}",
        out.stderr
    );
}

/// THE CHAIN IS FOLLOWED (user, 2026-10-12): under `requires PartialEq[T = T]` alone
/// the proof is handed the `neq` law and NOT `eq_refl` — reflexivity is `Eq`'s law, and
/// `eq` as `=` gave it for nothing. Under `requires Ord[T = T]` it is handed twelve:
/// `Ord`'s one, the nine of the `WeakOrd` it provides, `Eq`'s and `PartialEq`'s — each
/// once, though `PartialEq` is reached through `Eq` and through `PartialOrd`.
///
/// This is the row BVG8M's `the_laws_of_what_a_spec_provides_in_turn_are_not_read`
/// said would change.
#[test]
fn a_requirement_gives_the_laws_of_what_its_spec_requires_or_provides_in_turn() {
    let alone = prove_dry_run(
        "peq",
        &in_scope(
            "peq",
            "requires anthill.prelude.PartialEq[T = T]",
            IRREFLEXIVE,
            "z3",
        ),
    );
    assert_eq!(
        errors(&alone),
        Vec::<&str>::new(),
        "stderr:\n{}",
        alone.stderr
    );
    let laws = laws_of(&alone);
    assert_eq!(laws.len(), 1, "`PartialEq` has one law:\n{}", alone.stdout);
    assert!(
        laws[0].contains("anthill.prelude.PartialEq.neq@"),
        "{}",
        laws[0]
    );

    let ord = prove_dry_run(
        "ord",
        &in_scope(
            "ord",
            "requires anthill.prelude.Ord[T = T]",
            IRREFLEXIVE,
            "z3",
        ),
    );
    assert_eq!(errors(&ord), Vec::<&str>::new(), "stderr:\n{}", ord.stderr);
    let laws = laws_of(&ord);
    assert_eq!(laws.len(), 12, "1 + 9 + 1 + 1:\n{}", ord.stdout);
    let t = carrier("ord");
    // `Ord`'s own, the first: `eq(?a, ?b) <=> eq(WeakOrd.compare(?a, ?b), 0)` — `eq` at
    // the carrier is the carrier's, and `eq` of two `Int64` is the theory's `=`.
    assert_eq!(
        laws[0],
        format!(
            "(assert (forall ((var_0 {t}) (var_1 {t})) \
             (= (anthill.prelude.PartialEq.eq@{t} var_1 var_0) \
             (= (anthill.prelude.WeakOrd.compare@{t} var_1 var_0) 0.0))))"
        )
    );
    // `WeakOrd`'s `constraint compare_congruent`, a guard and a conclusion.
    assert!(
        laws.contains(
            &format!(
                "(assert (forall ((var_0 {t}) (var_1 {t})) \
                 (=> (anthill.prelude.PartialEq.eq@{t} var_0 var_1) \
                 (= (anthill.prelude.WeakOrd.compare@{t} var_0 var_1) 0.0))))"
            )
            .as_str()
        ),
        "the constraint is an implication:\n{}",
        ord.stdout
    );
    assert_eq!(
        ord.stdout
            .lines()
            .filter(|l| l.starts_with(&format!(
                "(declare-fun anthill.prelude.WeakOrd.compare@{t} "
            )))
            .collect::<Vec<_>>(),
        vec![format!("(declare-fun anthill.prelude.WeakOrd.compare@{t} ({t} {t}) Real)").as_str()],
        "`compare` is into `Int64`, which is a `Real` here"
    );
    assert_eq!(
        laws_not_lowered(&ord),
        Vec::<&str>::new(),
        "stderr:\n{}",
        ord.stderr
    );
}

/// A VERDICT UNDER A REQUIREMENT IS OF THE CARRIER. `gte(?a, ?a) :- gte(?a, ?b)` under
/// `requires PartialOrd[T = T]`: written with no bound, nothing gives `?a` or `?b` a
/// sort, and under a scope that has an abstract parameter that is REFUSED (user,
/// 2026-10-12) — it was two `Real` constants and `>=`. With `?a: T` both are of the
/// carrier (`?b` by `gte`'s signature: a bound cannot be written in a body), `gte` is
/// the carrier's own relation, and `PartialOrd` has no law to say it is reflexive.
///
/// This is the row BVG8M's `a_verdict_under_a_requirement_is_about_the_reals` held the
/// other way.
#[test]
fn a_variable_that_nothing_gives_a_sort_is_refused_under_an_abstract_parameter() {
    let requires = "requires anthill.prelude.PartialOrd[T = T]";
    let unbounded = prove_dry_run(
        "unb",
        &in_scope(
            "unb",
            requires,
            "rule p: gte(?a, ?a) :- gte(?a, ?b)",
            r#"z3(logic: "LRA")"#,
        ),
    );
    let refused = errors(&unbounded);
    assert_eq!(refused.len(), 1, "stderr:\n{}", unbounded.stderr);
    assert!(
        refused[0].contains("nothing gives `?var_") && refused[0].contains("a sort"),
        "{}",
        refused[0]
    );
    assert!(
        !unbounded.stdout.contains("(declare-const"),
        "no document:\n{}",
        unbounded.stdout
    );

    let bounded = prove_dry_run(
        "bnd",
        &in_scope(
            "bnd",
            requires,
            "rule p: gte(?a: T, ?a) :- gte(?a, ?b)",
            r#"z3(logic: "LRA")"#,
        ),
    );
    let t = carrier("bnd");
    let gte = format!("anthill.prelude.PartialOrd.gte@{t}");
    assert_stated(
        &bounded,
        &[
            // The logic written, and `UF` for the declared function.
            "(set-logic UFLRA)".to_owned(),
            format!("(declare-fun {gte} ({t} {t}) Bool)"),
            format!("(declare-const var_1 {t})"),
            format!("(declare-const var_2 {t})"),
            format!("(assert ({gte} var_2 var_1))"),
            format!("(assert (not ({gte} var_2 var_2)))"),
        ],
    );
    assert!(
        !bounded.stdout.contains(">="),
        "no order of the reals:\n{}",
        bounded.stdout
    );
    // THE CONTROL of the refusal: the same unbounded rule in a sort with no abstract
    // parameter is the document it always was — two `Real` constants.
    let no_parameter = prove_dry_run(
        "nop",
        r#"
namespace test.zz7ph.nop
  import anthill.prelude.PartialOrd.{gte}
  sort Scope
    rule p: gte(?a, ?a) :- gte(?a, ?b)
    proof p by z3(logic: "LRA") end
  end
end
"#,
    );
    assert_stated(
        &no_parameter,
        &[
            "(set-logic LRA)".to_owned(),
            "(declare-const var_0 Real)".to_owned(),
            "(declare-const var_1 Real)".to_owned(),
            "(assert (>= var_1 var_0))".to_owned(),
            "(assert (not (>= var_1 var_1)))".to_owned(),
        ],
    );
}

/// A VARIABLE AN OPERATION'S SIGNATURE GIVES A SORT IS NOT REFUSED, under an abstract
/// parameter or not: `?x` compared with a `Float` literal is a `Real`. And a bound that
/// is a scalar is read too — `?x: Float` was refused before any bound was read
/// ("unhandled body goal functor 'anthill.kernel.__domain_guard'"). The scope has the
/// parameter and requires nothing, so nothing is declared.
#[test]
fn a_scalar_is_a_real_by_its_literal_or_its_bound() {
    for (name, rule) in [
        ("lit", "rule p: gte(?x, 0.0) :- gte(?x, 5.0)"),
        ("flt", "rule p(?x: Float) :- gte(?x, 5.0), gte(0.0, ?x)"),
    ] {
        let out = prove_dry_run(name, &in_scope(name, "", rule, r#"z3(logic: "LRA")"#));
        assert_stated(
            &out,
            &[
                // Nothing declared: the logic is the one written.
                "(set-logic LRA)".to_owned(),
                "(declare-const var_0 Real)".to_owned(),
                "(assert (>= var_0 5.0))".to_owned(),
            ],
        );
        assert!(
            !out.stdout.contains("declare-sort"),
            "{name}:\n{}",
            out.stdout
        );
    }
}

/// The law `lt(?a, ?b) <=> lte(?a + 1, ?b)`: true of the integers, false of the reals.
const DISCRETE_AT_INT64: &str = r#"
namespace test.zz7ph.disc
  import anthill.prelude.PartialOrd.{lt, lte, gte}
  import anthill.prelude.Additive.{add}
  import anthill.prelude.{Int64}

  sort Discrete
    sort T = ?
    rule discrete: lt(?a, ?b) <=> lte(add(?a, 1), ?b)
  end

  sort Scope
    requires Discrete[T = Int64]

    rule p: gte(?x, 100) :- gte(?x, 5)
    proof p by z3 end
  end
end
"#;

/// A LAW IS ASSERTED OF A CARRIER'S OWN SORT, AND NOT AT A CONCRETE CARRIER. `Int64` is
/// modelled by the theory's reals, and a law is an assumption, not a lemma proved in
/// that model: `discrete` holds of the integers and is false of the reals, so asserted
/// over `Real` it is inconsistent and everything under it proves — the first cut did
/// that, and `gte(?x, 100) :- gte(?x, 5)` proved (/code-review, reproduced). So at a
/// concrete carrier no law is in the document, nothing is declared, the logic is the
/// one written, and the laws left out are said. `eq_refl` is left out with the rest: it
/// is a theorem of `=` there, and adds nothing.
#[test]
fn a_law_is_asserted_of_a_carriers_own_sort_and_not_at_a_concrete_carrier() {
    let out = prove_dry_run(
        "int",
        &in_scope(
            "int",
            "requires anthill.prelude.Eq[T = Int64]",
            "rule p: gte(?x, 0) :- gte(?x, 5)",
            r#"z3(logic: "QF_LRA")"#,
        ),
    );
    assert_stated(&out, &["(set-logic QF_LRA)".to_owned()]);
    assert!(laws_of(&out).is_empty(), "{}", out.stdout);
    assert!(
        !out.stdout.contains("forall") && !out.stdout.contains("declare-sort"),
        "{}",
        out.stdout
    );
    let said = laws_not_lowered(&out);
    assert_eq!(said.len(), 1, "stderr:\n{}", out.stderr);
    assert!(
        said[0].starts_with(
            "warning: `test.zz7ph.int.Scope` requires `anthill.prelude.Eq[T = \
             anthill.prelude.Int64]`, and 2 of the 2 laws it gives a proof are not lowered to \
             SMT — a `by z3` proof under it runs without: anthill.prelude.Eq.eq_refl, 1 \
             unlabelled equation ("
        ) && said[0].contains("a law is asserted of a carrier's own sort"),
        "{}",
        said[0]
    );

    let out = prove_dry_run("disc", DISCRETE_AT_INT64);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    assert!(laws_of(&out).is_empty(), "{}", out.stdout);
    assert!(
        !out.stdout.contains("forall"),
        "no law over the reals:\n{}",
        out.stdout
    );
    assert_eq!(laws_not_lowered(&out).len(), 1, "stderr:\n{}", out.stderr);
}

/// A LAW'S PREMISE THAT IS A RULE'S PREDICATE IS NOT DROPPED. A cited lemma's is passed
/// over; a law is assumed, and `eq(weight(?a), weight(?b)) :- related(?a, ?b)` without
/// its premise is "every two weights are equal" — the first cut asserted that, and
/// `gt(weight(?a), weight(?b))` was refuted of every carrier (/code-review,
/// reproduced). The law is left out, and said with why.
#[test]
fn a_law_whose_premise_is_a_rules_predicate_is_left_out_whole() {
    let out = prove_dry_run("prem", RULE_PREMISE);
    assert_eq!(errors(&out), Vec::<&str>::new(), "stderr:\n{}", out.stderr);
    assert!(
        laws_of(&out).is_empty(),
        "no law without its premise:\n{}",
        out.stdout
    );
    let said = laws_not_lowered(&out);
    assert_eq!(said.len(), 1, "stderr:\n{}", out.stderr);
    assert!(
        said[0].contains("test.zz7ph.prem.Spec.same_weight")
            && said[0]
                .contains("the law's premise `test.zz7ph.prem.Spec.related` is a rule's predicate"),
        "{}",
        said[0]
    );
}

const RULE_PREMISE: &str = r#"
namespace test.zz7ph.prem
  import anthill.prelude.PartialEq.{eq}
  import anthill.prelude.PartialOrd.{gt}
  import anthill.prelude.{Int64}

  sort Spec
    sort T = ?
    operation weight(a: T) -> Int64
    rule related(?a, ?b) :- eq(weight(?a), 7), eq(weight(?b), 7)
    rule same_weight: eq(weight(?a), weight(?b)) :- related(?a, ?b)
  end

  sort Scope
    sort T = ?
    requires Spec[T = T]

    rule p(?a: T, ?b: T) :- gt(Spec.weight(?a), Spec.weight(?b))
    proof p by z3 end
  end
end
"#;

/// A LAW THAT BOUNDS ITS OWN VARIABLE IS OF THE REQUIREMENT'S CARRIER. `?a: T` written in
/// `Spec` names `Spec.T`, and the law is lowered at a requirement that binds it: the
/// variable is of what it is bound to. The first cut took `Spec.T` for a sort of its
/// own — the law was about a carrier no proof names, constrained nothing, and counted as
/// lowered (/code-review, reproduced: the proof below was a counterexample).
#[test]
fn a_law_that_bounds_its_own_variable_is_of_the_requirements_carrier() {
    let out = prove_dry_run("lawb", LAW_WITH_A_BOUND);
    let t = "test.zz7ph.lawb.Scope.T";
    assert_stated(
        &out,
        &[format!(
            "(assert (forall ((var_1 {t})) (>= (test.zz7ph.lawb.Spec.w@{t} var_1) 0.0)))"
        )],
    );
    assert!(
        !out.stdout.contains("test.zz7ph.lawb.Spec.T"),
        "the spec's own parameter is no sort of the document:\n{}",
        out.stdout
    );
    assert_eq!(
        laws_not_lowered(&out),
        Vec::<&str>::new(),
        "stderr:\n{}",
        out.stderr
    );
}

const LAW_WITH_A_BOUND: &str = r#"
namespace test.zz7ph.lawb
  import anthill.prelude.PartialOrd.{gte, lt}
  import anthill.prelude.{Int64}

  sort Spec
    sort T = ?
    operation w(a: T) -> Int64
    rule w_nonneg: gte(w(?a: T), 0) :- true
  end

  sort Scope
    sort T = ?
    requires Spec[T = T]

    rule p(?a: T) :- lt(Spec.w(?a), 0)
    proof p by z3 end
  end
end
"#;

/// THE REFUSAL IS OF EVERY RULE READ FOR THE DOCUMENT, not of the one proved: `both` is
/// in a parametric scope and is refused there, and `outer`, outside it, inlines the same
/// body. Decided by the proved rule's name alone, `outer` read it over the reals and
/// proved `gt(?x, ?w), gt(?w, ?x)` unsatisfiable of a carrier `PartialOrd` says nothing
/// of (/code-review, reproduced).
#[test]
fn a_rule_of_a_parametric_scope_inlined_from_outside_it_is_refused_too() {
    let out = prove_dry_run(
        "inl",
        r#"
namespace test.zz7ph.inl
  import anthill.prelude.PartialOrd.{gt}

  sort PScope
    sort T = ?
    requires anthill.prelude.PartialOrd[T = T]
    rule both(?x, ?w) :- gt(?x, ?w), gt(?w, ?x)
  end

  rule outer :- PScope.both(?a, ?b)
  proof outer by z3 end
end
"#,
    );
    let refused = errors(&out);
    assert_eq!(refused.len(), 1, "stderr:\n{}", out.stderr);
    assert!(
        refused[0].starts_with(
            "error: test.zz7ph.inl.outer: `test.zz7ph.inl.PScope.both`: nothing gives `?var_"
        ),
        "{}",
        refused[0]
    );
}

/// A SORT GOES DOWN THROUGH A NESTED CALL, AND COMES FROM AN ENTITY'S FIELD: under a
/// parametric scope `?d + ?step` compared with a literal is a `Real`, and so are its
/// operands; and `?d` compared with a variable an entity's `Float` field binds is one
/// too. Neither is refused — the first cut gave a sort to a bare variable operand only,
/// and refused both (/code-review, reproduced).
#[test]
fn a_sort_goes_down_through_a_nested_call_and_comes_from_an_entitys_field() {
    let out = prove_dry_run(
        "down",
        r#"
namespace test.zz7ph.down
  import anthill.prelude.PartialOrd.{gt, lt}
  import anthill.prelude.{Float}

  entity Limits(max: Float, min: Float)
  fact Limits(max: 1.0, min: 2.0)

  sort Scope
    sort T = ?

    rule nested :- lt(?d + ?step, 3.0), gt(?d + ?step, 5.0)
    proof nested by z3 end

    rule field :- Limits(max: ?m, min: ?n), gt(?d, ?m), lt(?d, ?n)
    proof field by z3 end
  end
end
"#,
    );
    assert_stated(
        &out,
        &[
            "(assert (< (+ var_1 var_0) 3.0))".to_owned(),
            "(assert (> var_0 max))".to_owned(),
        ],
    );
    assert_eq!(
        out.stdout
            .lines()
            .filter(|l| l.starts_with("(declare-const") && l.ends_with(" Real)"))
            .count(),
        3,
        "`?d` and `?step`, and `?d`:\n{}",
        out.stdout
    );
}

/// A STEP'S OWN VARIABLE: a step writes no bound, and the refusal says so — "write its
/// bound on the rule's head" cannot be followed there (/code-review).
#[test]
fn a_steps_own_variable_is_refused_with_what_a_step_can_do() {
    let out = prove_dry_run(
        "stepvar",
        r#"
namespace test.zz7ph.stepvar
  import anthill.prelude.PartialEq.{eq}
  import anthill.prelude.PartialOrd.{gte}

  sort Scope
    sort T = ?
    requires anthill.prelude.WeakOrd[T = T]

    rule big: gte(?a: T, ?a) :- eq(?a, ?a)

    proof big
      rule h1: gte(?z, ?w)
        :- gte(?z, ?w)
        by z3

      using h1
      by z3
    end
  end
end
"#,
    );
    let refused = errors(&out);
    assert_eq!(refused.len(), 1, "stderr:\n{}", out.stderr);
    assert!(
        refused[0].contains("`test.zz7ph.stepvar.Scope.big.h1`: nothing gives `?var_")
            && refused[0].contains("A step of a structured proof writes no bound"),
        "{}",
        refused[0]
    );
}

/// ONLY A SPEC'S OPERATION IS UNINTERPRETED AT THE CARRIER. `same` is `Scope`'s own —
/// a member of a sort that has a parameter — and its body is a DEFAULT a carrier may
/// replace, so it is the carrier's function and the body is no hypothesis (as an
/// operation's default body is no law). `pick` is a free operation: its body is its
/// definition, and it is not made uninterpreted — it is refused as it was, where
/// uninterpreted it would have dropped the definition in silence.
#[test]
fn only_a_specs_operation_is_uninterpreted_at_the_carrier() {
    let scope = |rule: &str| {
        format!(
            r#"
namespace test.zz7ph.ops
  import anthill.prelude.PartialEq.{{eq, neq}}

  operation pick[A](a: A, b: A) -> A = a

  sort Scope
    sort T = ?
    requires anthill.prelude.Eq[T = T]
    operation same(a: T, b: T) -> T = a

    {rule}
    proof p by z3 end
  end
end
"#
        )
    };
    let t = "test.zz7ph.ops.Scope.T";
    let out = prove_dry_run(
        "ops_same",
        &scope("rule p(?a: T, ?b: T) :- neq(same(?a, ?b), ?a)"),
    );
    assert_stated(
        &out,
        &[format!(
            "(declare-fun test.zz7ph.ops.Scope.same@{t} ({t} {t}) {t})"
        )],
    );
    let out = prove_dry_run(
        "ops_pick",
        &scope("rule p(?a: T, ?b: T) :- neq(pick(?a, ?b), ?a)"),
    );
    assert_eq!(
        errors(&out),
        vec!["error: test.zz7ph.ops.Scope.p: v0: unhandled arithmetic op 'test.zz7ph.ops.pick'"],
        "stdout:\n{}",
        out.stdout
    );
}

/// WHAT A PROOF WAS HANDED IS OF WHAT IT DEPENDS ON. A law is no rule the proof visits,
/// so the proof's record did not hold it: with the law weakened the lemma `l` no longer
/// proves, and a proof citing `l` went on reading its record as current (/code-review,
/// reproduced). The scope's `requires` and the spec's laws are in the dependency set
/// now, and the cite is refused as stale.
#[test]
fn a_proofs_record_goes_stale_when_a_law_it_was_handed_changes() {
    if !z3_available() {
        return;
    }
    let source = |bound: &str| {
        format!(
            r#"
namespace test.zz7ph.stale
  import anthill.prelude.PartialOrd.{{gte}}
  import anthill.prelude.{{Int64}}

  sort Spec
    sort T = ?
    operation w(a: T) -> Int64
    rule w_nonneg: gte(w(?a), {bound}) <=> true
  end

  sort Scope
    sort T = ?
    requires Spec[T = T]

    rule l: gte(Spec.w(?a: T), 0) :- true
    proof l by z3 end

    rule m: gte(Spec.w(?b: T), 0 - 1) :- true
    proof m using l by z3 end
  end
end
"#
        )
    };
    let path = write_temp("stale.anthill", &source("0"));
    let cache = path.with_file_name("cache");
    let prove = |rule: &str| {
        anthill(&[
            "prove",
            path.to_str().unwrap(),
            "--cache-dir",
            cache.to_str().unwrap(),
            "--rule",
            rule,
            "-v",
        ])
    };
    let out = prove("test.zz7ph.stale.Scope.l");
    assert!(
        out.has_stdout_line("✓ test.zz7ph.stale.Scope.l: proved (z3: unsat)"),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    assert!(
        out.has_stdout_line(
            "deps: laws of test.zz7ph.stale.Spec, requires of test.zz7ph.stale.Scope, \
             test.zz7ph.stale.Scope.l"
        ),
        "stdout:\n{}",
        out.stdout
    );
    // THE CONTROL: with the law as it was, the cite is good.
    let out = prove("test.zz7ph.stale.Scope.m");
    assert!(
        out.has_stdout_line("✓ test.zz7ph.stale.Scope.m: proved (z3: unsat)"),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );

    std::fs::write(&path, source("0 - 5")).unwrap();
    let out = prove("test.zz7ph.stale.Scope.m");
    let refused = errors(&out);
    assert_eq!(
        refused.len(),
        1,
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    assert!(
        refused[0].contains("cite `test.zz7ph.stale.Scope.l`") && refused[0].contains("is stale"),
        "{}",
        refused[0]
    );
}

/// TWO REQUIREMENTS OF ONE SPEC AT TWO PARAMETERS: `eq` at `T` and `eq` at `U` are two
/// functions, each with its own law, and a variable's is the one of its sort. An
/// application across the two carriers is of no instance, and is refused — at load, where
/// `neq(?a, ?b)` makes the sort's parameter `U` the `T` of `?a` (068-implementation §6.2,
/// decision 3). The translation refused it before, "of two sorts".
#[test]
fn one_operation_at_two_carriers_is_two_functions() {
    let scope = |rule: &str| {
        format!(
            r#"
namespace test.zz7ph.two
  import anthill.prelude.PartialEq.{{eq, neq}}

  sort Scope
    sort T = ?
    sort U = ?
    requires anthill.prelude.Eq[T = T]
    requires anthill.prelude.Eq[T = U]

    {rule}
    proof p by z3 end
  end
end
"#
        )
    };
    let out = prove_dry_run(
        "two",
        &scope("rule p(?a: T, ?b: U) :- neq(?a, ?a), neq(?b, ?b)"),
    );
    let (t, u) = ("test.zz7ph.two.Scope.T", "test.zz7ph.two.Scope.U");
    assert_stated(
        &out,
        &[
            format!("(declare-sort {t} 0)"),
            format!("(declare-sort {u} 0)"),
            format!("(declare-fun anthill.prelude.PartialEq.eq@{t} ({t} {t}) Bool)"),
            format!("(declare-fun anthill.prelude.PartialEq.eq@{u} ({u} {u}) Bool)"),
            format!("(assert (forall ((var_0 {t})) (= (anthill.prelude.PartialEq.eq@{t} var_0 var_0) true)))"),
            format!("(assert (forall ((var_0 {u})) (= (anthill.prelude.PartialEq.eq@{u} var_0 var_0) true)))"),
            format!("(assert (anthill.prelude.PartialEq.neq@{t} var_3 var_3))"),
            format!("(assert (anthill.prelude.PartialEq.neq@{u} var_2 var_2))"),
        ],
    );
    assert_eq!(
        laws_of(&out).len(),
        4,
        "two laws at each carrier:\n{}",
        out.stdout
    );

    let across = prove_dry_run("two_across", &scope("rule p(?a: T, ?b: U) :- neq(?a, ?b)"));
    let refused = errors(&across);
    assert_eq!(refused.len(), 1, "stderr:\n{}", across.stderr);
    assert!(
        refused[0].contains("type mismatch in Scope.U (sort-parameter): expected U, got T"),
        "{}",
        refused[0]
    );
}

/// A LAW THAT IS NOT LOWERED IS LEFT OUT AND SAID, and the others of its spec are
/// lowered: `tag` is into `String`, which has no SMT sort. The warning names the law,
/// counts it against what the requirement gives, and says why.
#[test]
fn a_law_that_is_not_lowered_is_left_out_and_said() {
    let src = r#"
namespace test.zz7ph.odd
  import anthill.prelude.PartialEq.{eq}
  import anthill.prelude.PartialOrd.{gte}
  import anthill.prelude.{Int64, String}

  sort Odd
    sort T = ?
    operation weight(a: T) -> Int64
    operation tag(a: T) -> String

    rule weight_nonneg: gte(weight(?a), 0) <=> true
    rule tagged: eq(tag(?a), "x") <=> true
  end

  sort Scope
    sort T = ?
    requires Odd[T = T]

    rule p(?a: T) :- gte(-1, Odd.weight(?a))
    proof p by z3 end
  end
end
"#;
    let out = prove_dry_run("odd", src);
    let t = "test.zz7ph.odd.Scope.T";
    assert_stated(
        &out,
        &[
            format!("(declare-fun test.zz7ph.odd.Odd.weight@{t} ({t}) Real)"),
            format!("(assert (forall ((var_0 {t})) (= (>= (test.zz7ph.odd.Odd.weight@{t} var_0) 0.0) true)))"),
            format!("(assert (>= (- 1.0) (test.zz7ph.odd.Odd.weight@{t} var_1)))"),
        ],
    );
    assert_eq!(laws_of(&out).len(), 1, "{}", out.stdout);
    let said = laws_not_lowered(&out);
    assert_eq!(said.len(), 1, "stderr:\n{}", out.stderr);
    assert!(
        said[0].starts_with(&format!(
            "warning: `test.zz7ph.odd.Scope` requires `test.zz7ph.odd.Odd[T = {t}]`, and 1 of \
             the 2 laws it gives a proof is not lowered to SMT — a `by z3` proof under it runs \
             without: test.zz7ph.odd.Odd.tagged ("
        )) && said[0].contains("no SMT sort"),
        "{}",
        said[0]
    );
}

/// A CITED LEMMA ABOUT THE CARRIER quantifies over the carrier's sort — the bound on
/// its head is the quantifier's sort, not a premise dropped — and what it declares is
/// declared in the consumer's document, once, with what the consumer's own body uses.
/// The scope requires nothing, and the consumer's body names `lte` and `gte`: `eq` at
/// the carrier is in the document for the lemma alone.
#[test]
fn a_cited_lemma_about_the_carrier_quantifies_over_its_sort() {
    let src = r#"
namespace test.zz7ph.cite
  import anthill.prelude.PartialEq.{eq}
  import anthill.prelude.PartialOrd.{gte, lte}

  sort Scope
    sort T = ?

    rule gte_of_lte: gte(?a: T, ?a) :- lte(?a, ?a), eq(?a, ?a)
    proof gte_of_lte by trust(reason: "assumed of the carrier") end

    rule p: gte(?b: T, ?b) :- lte(?b, ?b)
    proof p using gte_of_lte by z3 end
  end
end
"#;
    let out = prove_dry_run("cite", src);
    let t = "test.zz7ph.cite.Scope.T";
    let eq = format!("anthill.prelude.PartialEq.eq@{t}");
    let gte = format!("anthill.prelude.PartialOrd.gte@{t}");
    let lte = format!("anthill.prelude.PartialOrd.lte@{t}");
    assert_stated(
        &out,
        &[
            format!("(declare-fun {eq} ({t} {t}) Bool)"),
            format!("(declare-fun {gte} ({t} {t}) Bool)"),
            format!(
                "(assert (forall ((var_1 {t})) \
                 (=> (and ({lte} var_1 var_1) ({eq} var_1 var_1)) ({gte} var_1 var_1))))"
            ),
            format!("(assert ({lte} var_1 var_1))"),
            format!("(assert (not ({gte} var_1 var_1)))"),
        ],
    );
    assert_eq!(
        out.stdout
            .lines()
            .filter(|l| l.starts_with(&format!("(declare-fun {gte} ")))
            .count(),
        1,
        "declared once:\n{}",
        out.stdout
    );
    assert!(
        laws_of(&out).is_empty(),
        "the scope requires nothing:\n{}",
        out.stdout
    );
}

/// A NULLARY OPERATION NAMED BARE IS A CONSTANT OF THE SORT, in a law (`lub(?a, top)
/// <=> top`) and in a body, which stores `top` as an application of no arguments. And a
/// law headed by a RELATION of its spec — `less(bottom, ?a) :- true` is neither an
/// equation nor a comparison — is not read: the two are left out and named, of the
/// seventeen `BoundedLattice` gives (its six, `Lattice`'s nine, `Eq`'s, `PartialEq`'s).
#[test]
fn a_nullary_operation_is_a_constant_and_a_relation_headed_law_is_left_out() {
    let out = prove_dry_run(
        "bl",
        r#"
namespace test.zz7ph.bl
  import anthill.prelude.PartialEq.{eq, neq}
  import anthill.prelude.PartialOrd.{gte}
  import anthill.prelude.Lattice.{lub}
  import anthill.prelude.BoundedLattice.{top}

  sort Scope
    sort T = ?
    requires anthill.prelude.BoundedLattice[T = T]

    rule p(?a: T) :- neq(lub(?a, top), top)
    proof p by z3 end

    rule q: gte(lub(?a: T, top), top) :- eq(?a, ?a)
    proof q by z3 end
  end
end
"#,
    );
    let t = "test.zz7ph.bl.Scope.T";
    let top = format!("anthill.prelude.BoundedLattice.top@{t}");
    let lub = format!("anthill.prelude.Lattice.lub@{t}");
    assert_stated(
        &out,
        &[
            format!("(declare-fun {top} () {t})"),
            format!("(assert (forall ((var_0 {t})) (= ({lub} var_0 {top}) {top})))"),
            // In a BODY, where `top` is stored as an application of no arguments …
            format!("(assert (anthill.prelude.PartialEq.neq@{t} ({lub} var_1 {top}) {top}))"),
            // … and in a HEAD, where it is a `Ref`: the position it stands in is of the
            // carrier, and so is it.
            format!(
                "(assert (not (anthill.prelude.PartialOrd.gte@{t} ({lub} var_1 {top}) {top})))"
            ),
        ],
    );
    assert_eq!(
        laws_of(&out).len(),
        15,
        "seventeen, less two:\n{}",
        out.stdout
    );
    let said = laws_not_lowered(&out);
    assert_eq!(said.len(), 1, "stderr:\n{}", out.stderr);
    assert!(
        said[0].contains(
            ", and 2 of the 17 laws it gives a proof are not lowered to SMT — a `by z3` proof \
             under it runs without: anthill.prelude.BoundedLattice.less_bottom, \
             anthill.prelude.BoundedLattice.less_top ("
        ) && said[0].contains("rule head shape not supported"),
        "{}",
        said[0]
    );
}

/// A STEP OF A STRUCTURED PROOF HAS ITS PARENT'S BOUNDS. The bound is written on the
/// parent's head; the step borrows the parent's frame and is its own query, so its
/// variable is of the carrier there too — it was a variable nothing gave a sort.
#[test]
fn a_step_of_a_structured_proof_has_the_sorts_of_its_parents_bounds() {
    let out = prove_dry_run("step", STEP_OVER_THE_CARRIER);
    let t = "test.zz7ph.step.Scope.T";
    assert!(
        out.stdout.contains("--- test.zz7ph.step.Scope.big.h1 ---"),
        "the step's document:\n{}",
        out.stdout
    );
    assert_stated(
        &out,
        &[
            format!("(declare-const var_1 {t})"),
            format!("(assert (anthill.prelude.PartialEq.eq@{t} var_1 var_1))"),
            format!("(assert (not (anthill.prelude.PartialOrd.lte@{t} var_1 var_1)))"),
        ],
    );
}

const STEP_OVER_THE_CARRIER: &str = r#"
namespace test.zz7ph.step
  import anthill.prelude.PartialEq.{eq}
  import anthill.prelude.PartialOrd.{gte, lte}

  sort Scope
    sort T = ?
    requires anthill.prelude.WeakOrd[T = T]

    rule big: gte(?a: T, ?a) :- eq(?a, ?a)

    proof big
      rule h1: lte(?a, ?a)
        :- eq(?a, ?a)
        by z3

      using h1
      by z3
    end
  end
end
"#;

/// THE VERDICTS, where there is a solver.
///
///   * the control proves under `requires Eq[T = T]` — the body is unsat by `eq_refl`
///     and `PartialEq`'s `neq` law — and under `requires PartialEq[T = T]` alone it does
///     NOT: reflexivity is `Eq`'s law;
///   * `gte(?a: T, ?a) :- gte(?a, ?b)` does not prove under `requires PartialOrd[T = T]`;
///   * antisymmetry of `gt` proves from `WeakOrd`'s laws, for two head variables;
///   * a proof whose document declares a function runs under the logic it wrote with
///     `UF` added — z3 refuses a declared function under `LRA`.
///   * a structured proof about the carrier proves, its step under its parent's bound;
///   * a law false of the reals, and a law whose premise was a rule's predicate, are not
///     assumed — the proofs that "needed" them are counterexamples — and a law that
///     bounds its own variable is.
#[test]
fn the_verdicts_are_of_the_carrier() {
    if !z3_available() {
        return;
    }
    let prove = |name: &str, src: &str| {
        let path = write_temp(&format!("{name}.anthill"), src);
        anthill(&["prove", path.to_str().unwrap(), "--no-cache"])
    };
    let verdict = |out: &Output, name: &str, line: &str| {
        assert!(
            out.has_stdout_line(&format!(
                "{line} test.zz7ph.{name}.Scope.p: {}",
                if line == "✓" {
                    "proved (z3: unsat)"
                } else {
                    "COUNTEREXAMPLE (z3: sat)"
                }
            )),
            "`{name}`; stdout:\n{}\nstderr:\n{}",
            out.stdout,
            out.stderr
        );
    };

    let out = prove(
        "v_eq",
        &in_scope(
            "v_eq",
            "requires anthill.prelude.Eq[T = T]",
            IRREFLEXIVE,
            "z3",
        ),
    );
    verdict(&out, "v_eq", "✓");
    let out = prove(
        "v_eq_lra",
        &in_scope(
            "v_eq_lra",
            "requires anthill.prelude.Eq[T = T]",
            IRREFLEXIVE,
            r#"z3(logic: "QF_LRA")"#,
        ),
    );
    verdict(&out, "v_eq_lra", "✓");
    let out = prove(
        "v_peq",
        &in_scope(
            "v_peq",
            "requires anthill.prelude.PartialEq[T = T]",
            IRREFLEXIVE,
            "z3",
        ),
    );
    verdict(&out, "v_peq", "✗");
    let out = prove(
        "v_refl",
        &in_scope(
            "v_refl",
            "requires anthill.prelude.PartialOrd[T = T]",
            "rule p: gte(?a: T, ?a) :- gte(?a, ?b)",
            r#"z3(logic: "LRA")"#,
        ),
    );
    verdict(&out, "v_refl", "✗");
    let out = prove(
        "v_anti",
        &in_scope(
            "v_anti",
            "requires anthill.prelude.WeakOrd[T = T]",
            "rule p(?a: T, ?b: T) :- gt(?a, ?b), gt(?b, ?a)",
            "z3",
        ),
    );
    verdict(&out, "v_anti", "✓");

    // A law true of the integers and false of the reals is not assumed of the reals,
    // and a law is not assumed without its premise: neither proof goes through.
    for (name, src, rule) in [
        ("v_disc", DISCRETE_AT_INT64, "test.zz7ph.disc.Scope.p"),
        ("v_prem", RULE_PREMISE, "test.zz7ph.prem.Scope.p"),
    ] {
        let out = prove(name, src);
        assert!(
            out.has_stdout_line(&format!("✗ {rule}: COUNTEREXAMPLE (z3: sat)")),
            "`{rule}`; stdout:\n{}\nstderr:\n{}",
            out.stdout,
            out.stderr
        );
    }
    // And a law that bounds its own variable is of the requirement's carrier: it is used.
    let out = prove("v_lawb", LAW_WITH_A_BOUND);
    assert!(
        out.has_stdout_line("✓ test.zz7ph.lawb.Scope.p: proved (z3: unsat)"),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );

    // The structured proof over the carrier: its step and its conclusion each a query.
    let out = prove("v_step", STEP_OVER_THE_CARRIER);
    assert!(
        out.has_stdout_line("✓ test.zz7ph.step.Scope.big: proved (z3: unsat)"),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}
