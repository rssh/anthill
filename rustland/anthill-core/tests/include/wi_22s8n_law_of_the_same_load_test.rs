//! A LAW IS A PREMISE FOR THE PROOFS OF ITS OWN LOAD (WI-20261117-22S8N, kernel-language §5.3).
//! A guard is refuted, and a precondition proved, while an operation body is typed, and a
//! proof takes a guarded `=` law as a premise, instantiating its type variable and passing the
//! instances its body reads (WI-20261117-V0RPW). The typer typed every rule after the bodies,
//! so a law of the same load had no reads yet and the lemma went unused where the same law of
//! an earlier load was used — MEASURED, with the law below in its own file loaded first,
//! `risky(x, 2)` loaded clean, and in the program's file it owed `Boom`. A load now elaborates
//! its laws before its bodies — since WI-20261117-8J8NG with every other rule, in one sweep
//! ahead of the bodies (`typing::elaborate_rules`), where this ticket had listed the untagged
//! guarded laws alone (`laws_elaborated_ahead`, gone). The back-outs below were measured against
//! that list; `wi_8j8ng_rules_before_bodies_test`'s header has the sweep's.
//!
//! The rows here are a program's OWN law, which is in the program's load in every recipe; the
//! library's laws used in the library's own load are `wi_v0rpw`'s rows under
//! `ANTHILL_TEST_FRESH_LOAD=1`, unpinned by this ticket.
//!
//! ## What fails with the change backed out
//!
//! Measured one at a time over this file and `wi_v0rpw_law_over_type_variable_test`, on the
//! shared base and one-shot (2026-11-17):
//!
//! * The laws typed and woven in the sweep after the bodies, as before: [`guard_rows`] and
//!   [`precondition_rows`] on both; one-shot also `wi_v0rpw`'s
//!   `euclid_div_is_used_at_a_euclidean_domain_and_not_at_a_zero_divisor` and
//!   `the_field_laws_are_used_at_a_field`.
//! * Only the reads of a law's requirements installed after the bodies: the same four.
//! * The laws woven ahead but typed in the sweep after the bodies — which then passes over a
//!   woven body, so the law is never typed:
//!   [`a_law_typed_ahead_reports_its_contradiction`] alone, on both.
//!
//! NO ROW FAILS, and said rather than hidden, with a `@[simp]` guarded `=` equation listed ahead
//! too. It is a rewrite the bodies fire, and the requirement weave rewrites its right-hand side,
//! so it keeps its place after them (`typing::laws_elaborated_ahead`). One that declares a
//! requirement carries a typed pattern over its type variable, and none of three fixtures tried
//! fired in a body (`f[A](?x: A) = Desc.d(?x) :- Desc[T = A], gt(1, 0) @[simp]` left `f`
//! bodiless); the first cut listed them, and the workspace was green over it.
//!
//! PASSES EITHER WAY, BY DESIGN: the goal of a law's bound installed after the bodies fails no
//! row. Using the law takes the bound's type from the value its bounded column matched
//! (`law_type_instantiation`), so the goal holds wherever the law is instantiated, and where it
//! is not, the reads of its requirements wait on the same open type. It is installed ahead so a
//! law's body is the one a later load's proof would run. The `false` rows of each table, and
//! the contradiction row under the first two back-outs (the sweep types a law before weaving
//! it), pass either way too.

use crate::common::load_errors_of;

/// A program over `ty` with `risky`'s contract `contract` and `c` calling it as `call`; with
/// `law`, the program's own law over a type variable, `(a * b) / b = a` at a Euclidean domain
/// and a divisor that is not its zero — a law the library does not state.
fn program(ns: &str, law: bool, ty: &str, contract: &str, call: &str) -> String {
    let law = if law {
        "rule mul_div: div[A](mul(?a, ?b: A), ?b) = ?a :- EuclideanDomain[T = A], Additive[T = A], neq(?b, zero)"
    } else {
        ""
    };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, BigInt, Bool, PartialEq, Effect, EuclideanDomain, Additive}}
  import anthill.prelude.PartialEq.{{eq, neq}}
  import anthill.prelude.Additive.{{zero}}
  import anthill.prelude.Multiplicative.{{mul}}
  import anthill.prelude.Divisible.{{div}}
  sort Boom
    entity Bang
    provides Effect[T = Boom]
  end
  {law}
  operation risky(a: {ty}, b: {ty}) -> {ty} {contract} = a
  operation c(x: {ty}) -> {ty} = {call}
end
"#
    )
}

const GUARD: &str = "effects { Boom :- neq((a * b) / b, a) }";
const PRECONDITION: &str = "requires eq((a * b) / b, a)";

fn boom_owed(errors: &[String]) -> bool {
    errors
        .iter()
        .any(|e| e.contains("c.effects") && e.contains("undeclared effect: Boom"))
}

/// The law refutes `neq((a * b) / b, a)` at a non-zero divisor of an `Int64` or a `BigInt`, each
/// a Euclidean domain, and not at a zero one (`zero` is the divisor's type's); with no law the
/// effect is owed.
#[test]
fn guard_rows() {
    for (i, (law, ty, call, owes)) in [
        (true, "Int64", "risky(x, 2)", false),
        (true, "BigInt", "risky(x, 2n)", false),
        (true, "Int64", "risky(x, 0)", true),
        (true, "BigInt", "risky(x, 0n)", true),
        (false, "Int64", "risky(x, 2)", true),
    ]
    .iter()
    .enumerate()
    {
        let errs = load_errors_of(&program(&format!("test.s8n.guard{i}"), *law, ty, GUARD, call));
        assert_eq!(boom_owed(&errs), *owes, "law {law} {ty} {call}: {errs:?}");
    }
}

/// The same law proves the precondition `eq((a * b) / b, a)` at the same calls, and nothing
/// proves it at a zero divisor or with no law: the call is refused there.
#[test]
fn precondition_rows() {
    for (i, (law, ty, call, proved)) in [
        (true, "Int64", "risky(x, 2)", true),
        (true, "BigInt", "risky(x, 2n)", true),
        (true, "Int64", "risky(x, 0)", false),
        (false, "Int64", "risky(x, 2)", false),
    ]
    .iter()
    .enumerate()
    {
        let errs = load_errors_of(&program(&format!("test.s8n.pre{i}"), *law, ty, PRECONDITION, call));
        let unproved = errs
            .iter()
            .any(|e| e.contains("risky.requires") && e.contains("unsatisfied precondition"));
        assert_eq!(!unproved, *proved, "law {law} {ty} {call}: {errs:?}");
        if *proved {
            assert!(errs.is_empty(), "law {law} {ty} {call}: {errs:?}");
        }
    }
}

/// A law of the load is TYPED before its calls are woven through its reads, as the sweep
/// types a rule before the weave: a law whose variable is at a `String` and an `Int64` field is
/// refused.
#[test]
fn a_law_typed_ahead_reports_its_contradiction() {
    let src = r#"
namespace test.s8n.contradiction
  import anthill.prelude.{Int64, String, Bool, PartialEq, EuclideanDomain, Additive}
  import anthill.prelude.PartialEq.{eq, neq}
  import anthill.prelude.Additive.{zero}
  import anthill.prelude.Multiplicative.{mul}
  import anthill.prelude.Divisible.{div}
  entity pr(s: String, n: Int64)
  rule bad: div[A](mul(?a, ?b: A), ?b) = ?a :- EuclideanDomain[T = A], Additive[T = A], neq(?b, zero), pr(s: ?c, n: ?c)
end
"#;
    let errs = load_errors_of(src);
    assert!(errs.iter().any(|e| e.contains("contradictory variable types")), "{errs:?}");
}
