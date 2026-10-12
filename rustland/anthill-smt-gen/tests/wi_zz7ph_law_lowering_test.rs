//! WI-20261012-ZZ7PH — the emitter's side of lowering a spec's law: `lower_spec_law`,
//! the sorts of a clause's variables, the logic a document is checked under.
//!
//! The documents a PROOF gets are driven through the binary
//! (`anthill-cli/tests/include/wi_zz7ph_law_lowering_test.rs`); these rows hold what
//! that cannot count or cannot reach: every law of the library's lawful requirements,
//! the two entry points' different reading of a one-variable head, and each arm of the
//! logic.
//!
//! What fails when a part is backed out:
//! `docs/measurements/test-infrastructure/law-lowering-2026-10-12.txt` §5.

use super::common::load_kb_with;
use anthill_core::kb::load::{requirement_chain, requires_clauses_of, RequirementInstance};
use anthill_core::kb::KnowledgeBase;
use anthill_smt_gen::{
    emit_obligation, emit_satisfiability_check, emit_satisfiability_check_with,
    lift_rule_to_implication_clause, lower_spec_law, Obligation, ProofConfig,
};

/// A sort `Scope` with the abstract parameter `T` and one `requires` of `spec` at it.
fn scope_requiring(spec: &str) -> String {
    format!(
        r#"
namespace test.zz7ph.laws
  sort Scope
    sort T = ?
    requires {spec}[T = T]
  end
end
"#
    )
}

/// The chain of `Scope`'s one clause, flattened: the spec it names, then what that
/// requires or provides in turn, each instance once.
fn instances_of(kb: &mut KnowledgeBase) -> Vec<RequirementInstance> {
    let clauses = requires_clauses_of(kb, &["test.zz7ph.laws.Scope"]).expect("the clauses");
    assert_eq!(clauses.len(), 1);
    let chain = requirement_chain(kb, &clauses[0]).expect("the chain");
    let mut flat: Vec<RequirementInstance> = Vec::new();
    let mut pending = vec![chain];
    while let Some(instance) = pending.pop() {
        pending.extend(instance.in_turn.iter().rev().cloned());
        if !flat.iter().any(|seen| seen.spec_text == instance.spec_text) {
            flat.push(instance);
        }
    }
    flat
}

/// THE COUNT THE TICKET WAS FILED ON, turned: 11 of the standard library's 42
/// requirement records name a spec with a law — `Eq`, `PartialEq`, `Ring`, `WeakOrd`,
/// `Lattice` — and no law of theirs lifted ("rule head shape not supported
/// (functor=anthill.kernel.unify, pos_args=2)"; 18 of the 21 equations and the
/// constraint named an operation with no SMT form). At an abstract parameter EVERY law
/// such a requirement gives lowers, those of what the spec requires or provides in turn
/// with it; `Ord` is here for its chain, which is the longest.
#[test]
fn every_law_a_lawful_library_requirement_gives_lowers_at_an_abstract_parameter() {
    for (spec, given) in [
        ("anthill.prelude.PartialEq", 1),
        ("anthill.prelude.Eq", 2),           // its own, and `PartialEq`'s
        ("anthill.prelude.algebra.Ring", 9), // 2, `Additive`'s 5, `Multiplicative`'s 2
        ("anthill.prelude.WeakOrd", 11),     // 9, `Eq`'s, `PartialEq`'s
        ("anthill.prelude.Lattice", 11),     // 9, `Eq`'s, `PartialEq`'s
        ("anthill.prelude.Ord", 12),         // 1, and `WeakOrd`'s 11
    ] {
        let mut kb = load_kb_with(&scope_requiring(spec));
        let mut lowered = 0;
        for instance in instances_of(&mut kb) {
            for law in kb.spec_laws(instance.spec) {
                let law = lower_spec_law(&kb, &law, &instance).unwrap_or_else(|e| {
                    panic!(
                        "a law of `{}` is not lowered: {}",
                        instance.spec_text, e.message
                    )
                });
                assert!(
                    law.assertion
                        .starts_with("(assert (forall ((var_0 test.zz7ph.laws.Scope.T)"),
                    "over the parameter's own sort: {}",
                    law.assertion
                );
                assert!(!law.declarations.is_empty(), "{}", law.assertion);
                lowered += 1;
            }
        }
        assert_eq!(lowered, given, "`requires {spec}[T = T]`");
    }
}

/// NO LAW IS LOWERED AT A CONCRETE CARRIER: a law is asserted of a carrier's own sort.
/// `Int64` is modelled by the theory's reals, where each of the eleven `WeakOrd[T =
/// Int64]` gives is a theorem already (`eq_refl`, of `=`) or is not known to hold — and
/// a law true of the integers alone would be inconsistent there. Each is refused and
/// says so; none is an uninterpreted function at a theory sort.
#[test]
fn no_law_is_lowered_at_a_concrete_carrier() {
    let mut kb = load_kb_with(
        r#"
namespace test.zz7ph.laws
  import anthill.prelude.{Int64}
  sort Scope
    requires anthill.prelude.WeakOrd[T = Int64]
  end
end
"#,
    );
    let mut refused = Vec::new();
    for instance in instances_of(&mut kb) {
        for law in kb.spec_laws(instance.spec) {
            match lower_spec_law(&kb, &law, &instance) {
                Ok(law) => panic!("lowered at `{}`: {}", instance.spec_text, law.assertion),
                Err(e) => refused.push(e.message),
            }
        }
    }
    assert_eq!(refused.len(), 11);
    // The eight whose every operation has a theory row are refused for the carrier;
    // the three that name `compare`, `max` or `min` are refused before that, as an
    // operation with no row at a theory sort always was.
    assert!(
        refused
            .iter()
            .any(|why| why.contains("a law is asserted of a carrier's own sort")),
        "{refused:?}"
    );
    assert!(
        refused.iter().all(|why| {
            why.contains("a law is asserted of a carrier's own sort") || why.contains("unhandled")
        }),
        "{refused:?}"
    );
}

/// A NAME SEGMENT SPELLED LIKE A VARIABLE IS NOT ONE. A document names a declared
/// function by its qualified name, and the free variables of a fragment are its whole
/// tokens: read by splitting at every `.`, the `var_7` of this namespace was a variable
/// nothing gave a sort.
#[test]
fn a_name_segment_spelled_like_a_variable_is_not_a_variable() {
    let kb = load_kb_with(
        r#"
namespace test.zz7ph.var_7
  import anthill.prelude.PartialEq.{neq}
  sort Scope
    sort T = ?
    rule p(?a: T) :- neq(?a, ?a)
  end
end
"#,
    );
    let document = emit_satisfiability_check(&kb, "test.zz7ph.var_7.Scope.p").expect("emitted");
    let declared: Vec<&str> = document
        .lines()
        .filter(|l| l.starts_with("(declare-const"))
        .collect();
    assert_eq!(
        declared,
        ["(declare-const var_1 test.zz7ph.var_7.Scope.T)"],
        "{document}"
    );
}

/// THE LAWS A PROOF WAS HANDED ARE OF THE STATE ITS RECORD IS HASHED OVER: an entry for
/// the spec's laws and one for the scope's `requires`, each hashed as what it names. A
/// law weakened moves the first, a clause changed the second; and an ordinary rule's
/// entry is hashed as it was.
#[test]
fn the_state_a_proof_is_hashed_over_holds_the_laws_and_the_clause() {
    use anthill_smt_gen::cache::{state_hash, visited_laws_of, visited_requires_of};
    let source = |law: &str, requires: &str| {
        format!(
            r#"
namespace test.zz7ph.hash
  import anthill.prelude.PartialOrd.{{gte}}
  import anthill.prelude.{{Int64}}
  sort Spec
    sort T = ?
    operation w(a: T) -> Int64
    rule w_nonneg: gte(w(?a), {law}) <=> true
  end
  sort Other
    sort T = ?
  end
  sort Scope
    sort T = ?
    requires {requires}[T = T]
    rule p(?a: T) :- gte(Spec.w(?a), 3)
  end
end
"#
        )
    };
    let hashes = |law: &str, requires: &str| {
        let kb = load_kb_with(&source(law, requires));
        let of = |entry: String| state_hash(&kb, &std::iter::once(entry).collect());
        (
            of(visited_laws_of("test.zz7ph.hash.Spec")),
            of(visited_requires_of("test.zz7ph.hash.Scope")),
            of("test.zz7ph.hash.Scope.p".to_owned()),
        )
    };
    let (laws, clause, rule) = hashes("0", "Spec");
    assert_eq!(
        hashes("0", "Spec"),
        (laws.clone(), clause.clone(), rule.clone()),
        "stable"
    );
    let (weaker_laws, same_clause, same_rule) = hashes("0 - 5", "Spec");
    assert_ne!(weaker_laws, laws, "the law changed");
    assert_eq!((same_clause, same_rule), (clause.clone(), rule.clone()));
    let (same_laws, other_clause, same_rule) = hashes("0", "Other");
    assert_ne!(other_clause, clause, "the clause changed");
    assert_eq!((same_laws, same_rule), (laws, rule));
}

const ONE_VARIABLE_HEAD: &str = r#"
namespace test.zz7ph.head
  import anthill.prelude.PartialOrd.{gte}
  rule p(?x) :- gte(?x, 5.0), gte(0.0, ?x)
end
"#;

/// A ONE-VARIABLE HEAD IS READ TWO WAYS, by who asks. An OBLIGATION bounds the head's
/// result, so the body must bind it. A SATISFIABILITY check does not: there a head
/// variable the body leaves unbound is the rule's parameter, free like any other — it
/// was "rule body never bound the result variable" in both, which left no way to write
/// the one-variable violation rule a bound goes on.
#[test]
fn a_violation_rules_head_variable_is_its_parameter() {
    let kb = load_kb_with(ONE_VARIABLE_HEAD);
    let document = emit_satisfiability_check(&kb, "test.zz7ph.head.p").expect("emitted");
    for line in [
        "(declare-const var_0 Real)",
        "(assert (>= var_0 5.0))",
        "(assert (>= 0.0 var_0))",
    ] {
        assert!(
            document.lines().any(|l| l == line),
            "`{line}` in:\n{document}"
        );
    }
    assert!(!document.contains("define-fun"), "{document}");

    let refused = emit_obligation(
        &kb,
        &Obligation {
            rule_qn: "test.zz7ph.head.p".to_owned(),
            upper_bound: 1.0,
        },
    )
    .expect_err("an obligation has a result to bound");
    assert!(
        refused.message.contains("never bound the result variable"),
        "{}",
        refused.message
    );
}

/// AN EQUATION IS A CONCLUSION, for a cited lemma as for a law: `lhs <=> rhs` lifts to
/// `(= lhs rhs)`. It was "rule head shape not supported (functor=anthill.kernel.unify,
/// pos_args=2)".
#[test]
fn an_equational_lemma_lifts() {
    let kb = load_kb_with(
        r#"
namespace test.zz7ph.eqn
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte}
  rule halves: ?x + ?x <=> 2.0 * ?x
  rule guarded: gte(?x + 1.0, 0.0) <=> true :- gte(?x, 0.0)
end
"#,
    );
    assert_eq!(
        lift_rule_to_implication_clause(&kb, "test.zz7ph.eqn.halves").expect("lifted"),
        vec!["(assert (forall ((var_0 Real)) (=> true (= (+ var_0 var_0) (* 2.0 var_0)))))"]
    );
    // A side that is `Bool`-valued is a formula, and a guard is the premise.
    assert_eq!(
        lift_rule_to_implication_clause(&kb, "test.zz7ph.eqn.guarded").expect("lifted"),
        vec![
            "(assert (forall ((var_0 Real)) (=> (>= var_0 0.0) (= (>= (+ var_0 1.0) 0.0) true))))"
        ]
    );
}

/// `?x = <a term that names ?x>` IS A CONDITION, NOT A DEFINITION. Read as a definition,
/// `eq(?x, ?x)` bound `?x` to itself; a bound variable is not declared, so the document
/// named a constant it never declared and the solver answered "unknown constant var_0"
/// where a verdict was expected. A goal that defines — `eq(?y, ?x + 1.0)` — still does.
#[test]
fn a_goal_equating_a_variable_with_a_term_that_names_it_is_a_condition() {
    let kb = load_kb_with(
        r#"
namespace test.zz7ph.selfeq
  import anthill.prelude.{Float}
  import anthill.prelude.PartialEq.{eq}
  import anthill.prelude.PartialOrd.{gte}
  rule p(?x) :- eq(?x, ?x), eq(?y, ?x + 1.0), gte(?y, 5.0)
end
"#,
    );
    let document = emit_satisfiability_check(&kb, "test.zz7ph.selfeq.p").expect("emitted");
    let var = |line: &str| document.lines().any(|l| l == line);
    // `?x` is free and declared; `?y` is defined, and stands for its definition.
    assert!(
        document.contains("(declare-const var_") && document.matches("(declare-const").count() == 1,
        "{document}"
    );
    let x = document
        .lines()
        .find_map(|l| l.strip_prefix("(declare-const ")?.strip_suffix(" Real)"))
        .expect("the free variable")
        .to_owned();
    assert!(var(&format!("(assert (= {x} {x}))")), "{document}");
    assert!(var(&format!("(assert (>= (+ {x} 1.0) 5.0))")), "{document}");
}

const OVER_THE_CARRIER: &str = r#"
namespace test.zz7ph.logic
  import anthill.prelude.PartialOrd.{gte}
  sort Scope
    sort T = ?
    rule p(?a: T) :- gte(?a, ?a)
  end
  rule scalar(?x) :- gte(?x, 5.0)
end
"#;

/// THE LOGIC IS THE ONE WRITTEN, AND WHAT THE DOCUMENT NEEDS BEYOND IT (user,
/// 2026-10-12): `UF` for a declared function — z3 refuses one under `LRA`, "logic does
/// not support uninterpreted functions", and then answers `sat` — and not `QF_` once a
/// hypothesis is quantified. A document that declares nothing keeps its logic.
#[test]
fn the_logic_is_the_one_written_and_what_the_document_needs() {
    let kb = load_kb_with(OVER_THE_CARRIER);
    let logic_of = |rule: &str, config: &ProofConfig| {
        let document = emit_satisfiability_check_with(&kb, rule, config).expect("emitted");
        document
            .lines()
            .find_map(|l| {
                l.strip_prefix("(set-logic ")?
                    .strip_suffix(')')
                    .map(str::to_owned)
            })
            .expect("a logic")
    };
    let written = |logic: Option<&str>| ProofConfig {
        logic: logic.map(str::to_owned),
        ..ProofConfig::default()
    };
    let carrier = "test.zz7ph.logic.Scope.p";
    for (logic, document) in [
        (None, "UFLRA"),
        (Some("LRA"), "UFLRA"),
        (Some("LIA"), "UFLIA"),
        (Some("QF_LRA"), "QF_UFLRA"),
        (Some("UFLRA"), "UFLRA"),
        (Some("AUFLIA"), "AUFLIA"),
        (Some("ALIA"), "AUFLIA"),
        (Some("ALL"), "ALL"),
    ] {
        assert_eq!(
            logic_of(carrier, &written(logic)),
            document,
            "written {logic:?}"
        );
    }
    // A quantified hypothesis: the document is not quantifier-free.
    let with_a_law = ProofConfig {
        logic: Some("QF_LRA".to_owned()),
        laws: vec!["(assert (forall ((v Real)) (= v v)))".to_owned()],
        ..ProofConfig::default()
    };
    assert_eq!(logic_of(carrier, &with_a_law), "UFLRA");
    // THE CONTROL: a document that declares nothing is checked under what was written.
    let scalar = "test.zz7ph.logic.scalar";
    assert_eq!(logic_of(scalar, &written(None)), "LRA");
    assert_eq!(logic_of(scalar, &written(Some("QF_LRA"))), "QF_LRA");
}

/// AT A THEORY SORT AN OPERATION WITH NO ROW IS STILL REFUSED: it is an uninterpreted
/// function only at a declared sort, where its laws say what it is. `neq` of two
/// `Float`s made uninterpreted would be a discharge made weaker in silence.
#[test]
fn an_operation_with_no_row_is_not_uninterpreted_at_a_theory_sort() {
    let kb = load_kb_with(
        r#"
namespace test.zz7ph.row
  import anthill.prelude.{Float}
  import anthill.prelude.PartialEq.{neq}
  rule p(?x: Float) :- neq(?x, ?x)
end
"#,
    );
    let refused = emit_satisfiability_check(&kb, "test.zz7ph.row.p").expect_err("no row for `neq`");
    assert_eq!(
        refused.message,
        "v0: unhandled body goal functor 'anthill.prelude.PartialEq.neq'"
    );
}
