//! WI-20261105-CBRD2 — a contract proof decides each comparison at the member the typer gave it.
//! A contract over an operation's parameters is proved over skolems, and a comparison there at
//! the operation's own type parameter is deferred to the requirement it holds: its member is
//! that requirement's, and `Eq`'s law decides identical operands (proposal 051's JEE0E rule).
//! A `neq` deferred so is read as the `eq` at the same requirement, and a comparison written
//! with its result column (`neq(x, 1, true)`) as its two operands' comparison, at its member.
//! A comparison an `ensures` makes at a type nothing the operation requires covers does not
//! type, and is refused at load, as the same comparison in the body is; a `requires` or an effect
//! guard is decided at each call instead, typed at the call's arguments.
//!
//! Before, each of these was compared with no member, counted by
//! `untyped_equalities_by_this_thread`, the verdicts the same; and the one at an uncovered type
//! loaded and was undecided.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, then removed. The control is each switch unset: every
//! row passes.
//!
//! * A comparison deferred to a requirement counted as untyped, as before (`builtin_sem_eq`):
//!   [`a_comparison_at_the_requirement_is_decided_by_its_law`] fails on the count.
//! * A `neq` deferred to a requirement read through an untyped `eq` (`neq_as_not_eq` reading
//!   no class off it): the same row fails on the count, at its `neq` contracts.
//! * The result column's pair built as a bare term (`comparison_of_result_column`):
//!   [`a_result_column_comparison_keeps_its_member`] fails on the count.
//! * An unresolved comparison in a contract kept, as before (`type_conjunct_comparisons`):
//!   [`a_comparison_no_requirement_covers_is_refused`] fails, the contract loading.
//! * The refusal applied to every part of a contract, not to an `ensures` alone
//!   (`proved_only` taken as true): [`a_precondition_no_requirement_covers_is_decided_at_the_call`]
//!   fails, the `requires` refused at load, and so does
//!   `wi_5vm2g_bigint_zero_divisor_test::a_body_less_operations_contract_comparisons_are_typed`
//!   (a spec's guard over its `T`).

use anthill_core::kb::proof_verify::{verify_proofs, ProofVerdict};
use anthill_core::kb::resolve::untyped_equalities_by_this_thread;

fn program(ns: &str, sig: &str, ensures: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.{{Int64, Bool, Eq, Ord, PartialEq}}
  import anthill.prelude.PartialEq.{{eq, neq}}
  sort Box
    operation {sig}
      ensures {ensures}
      = x
    proof wrap.ensures by derivation end
  end
end
"#
    )
}

/// The verdict of `wrap.ensures` and the equalities its proof compared with no member.
fn verdict(src: &str) -> (ProofVerdict, usize) {
    let mut kb = crate::common::load_kb_with(src);
    let before = untyped_equalities_by_this_thread();
    let v = verify_proofs(&mut kb)
        .into_iter()
        .find(|r| r.rule_qn.ends_with("wrap.ensures"))
        .expect("the proof is reported")
        .verdict;
    (v, untyped_equalities_by_this_thread() - before)
}

fn discharged(v: &ProofVerdict) -> bool {
    matches!(v, ProofVerdict::Discharged)
}

fn refuted(v: &ProofVerdict) -> bool {
    matches!(v, ProofVerdict::Failed { reason } if reason.contains("is not derivable"))
}

fn undecided(v: &ProofVerdict) -> bool {
    matches!(v, ProofVerdict::Failed { reason } if reason.contains("could not be DECIDED"))
}

/// `wrap[T](x: T) -> T = x` under `requires Eq[T = T]`: `eq(result, x)` and `not(neq(result,
/// x))` are discharged and `neq(result, x)` refuted, by `Eq`'s law at the requirement; under
/// `requires PartialEq[T = T]` alone `eq(result, x)` is undecided. Nothing is compared with no
/// member.
#[test]
fn a_comparison_at_the_requirement_is_decided_by_its_law() {
    let eq = "wrap[T](x: T) -> T requires Eq[T = T]";
    let partial = "wrap[T](x: T) -> T requires PartialEq[T = T]";
    let rows: [(&str, &str, fn(&ProofVerdict) -> bool); 4] = [
        (eq, "eq(result, x)", discharged),
        (eq, "not(neq(result, x))", discharged),
        (eq, "neq(result, x)", refuted),
        (partial, "eq(result, x)", undecided),
    ];
    for (n, (sig, ensures, expect)) in rows.into_iter().enumerate() {
        let (v, untyped) = verdict(&program(&format!("cbrd2.cp.law{n}"), sig, ensures));
        assert!(expect(&v), "`{sig}` ensures `{ensures}`: {v:?}");
        assert_eq!(untyped, 0, "`{ensures}`: an equality compared with no member");
    }
}

/// `neq(x, 1, true)` over `x: Int64` rests on `x`: undecided, its operands compared at
/// `Int64`'s member.
#[test]
fn a_result_column_comparison_keeps_its_member() {
    let (v, untyped) = verdict(&program("cbrd2.cp.col", "wrap(x: Int64) -> Int64", "neq(x, 1, true)"));
    assert!(undecided(&v), "{v:?}");
    assert_eq!(untyped, 0, "an equality compared with no member");
}

/// `eq(result, x)` over `x: B` under `requires Eq[T = A]` does not type: refused at load, in the
/// body's words, the advice to write `===` given once.
#[test]
fn a_comparison_no_requirement_covers_is_refused() {
    let errs = crate::common::load_errors_of(&program(
        "cbrd2.cp.uncovered",
        "wrap[A, B](a: A, x: B) -> B requires Eq[T = A]",
        "eq(result, x)",
    ));
    let refusal = errs
        .iter()
        .find(|e| e.contains("wrap.ensures") && e.contains("requires PartialEq[T = …]"))
        .unwrap_or_else(|| panic!("refused at load: {errs:?}"));
    assert_eq!(refusal.matches("`===` compares any two values structurally").count(), 1, "{refusal}");
}

/// The same comparison written as a `requires` is decided at each call, typed at the call's
/// arguments: `neq(x, y)` over `x, y: B` is `Int64`'s at `pick(1, 2, 2)`, refuted there, and
/// holds at `pick(1, 2, 3)`. Only an `ensures`, which no call types, is refused.
#[test]
fn a_precondition_no_requirement_covers_is_decided_at_the_call() {
    for (ns, call, refused) in [("cbrd2.cp.reqbad", "pick(1, 2, 2)", true), ("cbrd2.cp.reqgood", "pick(1, 2, 3)", false)] {
        let src = format!(
            r#"namespace {ns}
  import anthill.prelude.{{Int64, Bool, Eq, PartialEq}}
  import anthill.prelude.PartialEq.{{eq, neq}}
  sort Box
    operation pick[A, B](a: A, x: B, y: B) -> B requires Eq[T = A], neq(x, y) = x
    operation caller() -> Int64 = {call}
  end
end
"#
        );
        let before = untyped_equalities_by_this_thread();
        let errs = crate::common::load_errors_of(&src);
        assert!(!errs.iter().any(|e| e.contains("requires PartialEq[T = …]")), "{ns}: {errs:?}");
        assert_eq!(errs.iter().any(|e| e.contains("unsatisfied precondition")), refused, "{ns}: {errs:?}");
        assert_eq!(untyped_equalities_by_this_thread() - before, 0, "{ns}: an equality compared with no member");
    }
}
