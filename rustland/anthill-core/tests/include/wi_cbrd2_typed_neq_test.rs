//! A TYPED `neq` GOAL IS `not(eq(…))` AT THE `eq` ITS BODY CALLS (WI-20261105-CBRD2). `neq`'s
//! body is `Bool.not(eq(a, b))` in `PartialEq`; a call typed at an instance enters it with that
//! instance's dictionary, so its `eq` is the dictionary's member. A goal reads it so: the
//! resolver writes a typed `neq(a, b)` as `not(eq(a, b))` with the `eq` at that member
//! (`neq_as_not_eq`, `CallClass::sibling_through_dictionary`), and a contract's `neq` and an
//! in-body proof's keep the member they were typed at, as their `eq`s do. Before, only a `neq`
//! no type reached was read so, and the contracts and in-body proofs kept no member for one:
//! its `eq` was untyped, and the resolver read the equality index for the member an operand's
//! constructor names.
//!
//! The index names the member the typer does for each of these programs, so their verdicts
//! are the same either way: what the rows measured was that the index is not read
//! (`resolve::eq_index_reads_by_this_thread`), beside the verdicts, until the index's run-time
//! readers went (see the end of this note).
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, then removed. The control is each switch unset: every
//! row passes.
//!
//! * The members not kept or carried for a `neq` (the contract twin and the in-body carry
//!   taking `eq`'s alone): [`a_precondition_neq_reads_its_carriers_eq`],
//!   [`a_postcondition_neq_reads_its_carriers_eq`], [`an_in_body_neq_reads_its_carriers_eq`]
//!   and [`a_neq_reads_an_eq_bound_by_the_provision`] fail on the index reads, their verdicts
//!   unchanged.
//! * The `eq` of the rewrite untyped (a member read as the spec's own): those four, and
//!   [`a_rule_body_neq_reads_its_carriers_eq`] and
//!   [`a_rule_body_neq_over_a_bound_variable_reads_its_carriers_eq`], the same way.
//! * The rewrite for an untyped `neq` only, the carried member then running `neq`'s body:
//!   every row here passes, the body route through the eval bridge reading no index either.
//!   `wi_jee0e_neq_body_test`'s `a_contract_reads_neq_through_eq_at_the_parameters_type` and
//!   `a_contract_reads_the_law_at_the_parameters_requirements` fail, `neq(x, 1)` over a
//!   parameter 'could not be EVALUATED': run as a function, the body meets the eigenvariable
//!   where a value is expected.
//! * A `neq` carried whatever its class: [`a_generic_neq_is_read_through_an_untyped_eq`] fails,
//!   `needy(1, 2)` refused under `requires neq(a, b)` at `T` — the class deferred to `needy`'s
//!   requirement ran the body where no frame holds it.
//!
//! THE INDEX READS ARE NO LONGER COUNTED (WI-20261105-CBRD2, part 5r): every run-time reader of
//! the equality index is gone, and its counter with them, so no comparison can be decided by
//! reading a value's constructor there. A back-out above that fails "on the index reads" is of
//! code that no longer exists; the rows keep their verdicts.

use anthill_core::kb::node_occurrence::Expr;
use anthill_core::kb::proof_verify::{verify_proofs, ProofVerdict};
use anthill_core::kb::typing::{in_body_proof_goal, prove_from_gamma, FlowEnv};

use crate::common::{load_errors_of, load_kb_with, load_stdlib_kb, query_pattern_term};

/// `Color`'s own `eq` holds of any two colours.
const CUSTOM_EQ: &str = r#"
  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color]
    provides Eq[T = Color]
    operation eq(a: Color, b: Color) -> Bool = true
  end
"#;

/// The control: structural equality is `Color`'s.
const STRUCTURAL_EQ: &str = r#"
  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color]
    provides Eq[T = Color]
  end
"#;

fn src(ns: &str, color: &str, ops: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Eq, PartialEq, Option, List}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.PartialEq.{{eq, neq}}
{color}
{ops}
end
"#
    )
}

/// `f`'s result and the equality index reads it made, the shared base loaded first so its own
/// load is not counted.
fn counting<R>(f: impl FnOnce() -> R) -> R {
    drop(load_stdlib_kb());
    f()
}

/// The load errors of `src`, asserting the load read no equality index.
fn errors_reading_no_index(src: &str) -> Vec<String> {
    let errs = counting(|| load_errors_of(src));
    errs
}

/// The precondition of `needy(<arg>)`: refused over the custom `Color`, whose `eq` makes the
/// two operands equal, proved over the structural one, and over `not` the other way round.
#[test]
fn a_precondition_neq_reads_its_carriers_eq() {
    for (n, (param, clause, arg, custom_holds)) in [
        ("c: Color", "neq(c, Red)", "Green", false),
        ("o: Option[T = Color]", "neq(o, some(Red))", "some(Green)", false),
        ("l: List[T = Color]", "neq(l, [Red])", "[Green]", false),
        ("c: Color", "not(neq(c, Red))", "Green", true),
        ("c: Color", "neq(c, Red, false)", "Green", true),
    ]
    .into_iter()
    .enumerate()
    {
        let ops = format!(
            "  operation needy({param}) -> Int64 requires {clause} = 1\n  \
             operation caller() -> Int64 = needy({arg})"
        );
        for (tag, color, holds) in [("c", CUSTOM_EQ, custom_holds), ("s", STRUCTURAL_EQ, !custom_holds)] {
            let errs = errors_reading_no_index(&src(&format!("test.cbrd2.tneq.pre{n}{tag}"), color, &ops));
            let refused = errs.iter().any(|e| e.contains("unsatisfied precondition"));
            assert_eq!(
                !refused,
                holds,
                "`{clause}` at `needy({arg})`, {}: {errs:?}",
                if tag == "c" { "custom" } else { "structural" }
            );
        }
    }
}

/// `ensures neq(result, …)` over a body that returns the other colour: not derivable over the
/// custom `Color`, discharged over the structural one.
#[test]
fn a_postcondition_neq_reads_its_carriers_eq() {
    for (n, (ret, goal, body)) in [
        ("Color", "neq(result, Red)", "Green"),
        ("Option[T = Color]", "neq(result, some(Red))", "some(Green)"),
    ]
    .into_iter()
    .enumerate()
    {
        let ops = format!(
            "  operation pick() -> {ret}\n    ensures {goal}\n    = {body}\n\n  \
             proof pick.ensures by derivation end"
        );
        for (tag, color, discharged) in [("c", CUSTOM_EQ, false), ("s", STRUCTURAL_EQ, true)] {
            let mut kb = load_kb_with(&src(&format!("test.cbrd2.tneq.post{n}{tag}"), color, &ops));
            let verdict = counting(|| {
                verify_proofs(&mut kb)
                    .into_iter()
                    .find(|r| r.rule_qn.ends_with("pick.ensures"))
                    .expect("the proof is reported")
                    .verdict
            });
            assert_eq!(
                matches!(verdict, ProofVerdict::Discharged),
                discharged,
                "`{goal}` over `= {body}`, {tag}: {verdict:?}"
            );
        }
    }
}

/// `conclude neq(some(Green), some(Red))`: the load proves it without reading the index, and
/// the goal it proves is not discharged over the custom `Color` and is over the structural one.
#[test]
fn an_in_body_neq_reads_its_carriers_eq() {
    let ops = "  operation caller() -> Int64 =\n    \
               proof h by derivation conclude neq(some(Green), some(Red)) end\n    0";
    for (ns, color, discharged) in [
        ("test.cbrd2.tneq.inc", CUSTOM_EQ, false),
        ("test.cbrd2.tneq.ins", STRUCTURAL_EQ, true),
    ] {
        let program = src(ns, color, ops);
        let mut kb = counting(|| load_kb_with(&program));
        let caller = kb.try_resolve_symbol(&format!("{ns}.caller")).expect("caller");
        let body = kb.op_body_node(caller).expect("caller's body");
        let Some(Expr::Proof {
            target, conclude, ..
        }) = body.as_expr()
        else {
            panic!("caller's body is not the proof: {:?}", body.as_expr());
        };
        let (target, conclude) = (*target, conclude.clone());
        let proved = counting(|| {
            let goal = in_body_proof_goal(&mut kb, target, conclude.as_ref());
            prove_from_gamma(&mut kb, &FlowEnv::empty(), &goal)
        });
        assert_eq!(proved, discharged, "{ns}");
    }
}

/// A rule body's typed `neq` reads its carrier's `eq`, at `Color` and at `Option[T = Color]`.
#[test]
fn a_rule_body_neq_reads_its_carriers_eq() {
    let rules = "  rule rc() :- neq(Green, Red)\n  \
                 rule ro() :- neq(some(Green), some(Red))\n  \
                 rule rn() :- not(neq(Green, Red))";
    for (ns, color, custom) in [
        ("test.cbrd2.tneq.rbc", CUSTOM_EQ, true),
        ("test.cbrd2.tneq.rbs", STRUCTURAL_EQ, false),
    ] {
        let mut kb = load_kb_with(&src(ns, color, rules));
        for (rule, holds) in [("rc()", !custom), ("ro()", !custom), ("rn()", custom)] {
            let goal = query_pattern_term(&mut kb, &format!("{ns}.{rule}"));
            let got = counting(|| kb.resolve(&[goal], &Default::default()));
            assert_eq!(got.iter().any(|s| s.is_definite()), holds, "{ns}: `{rule}`");
        }
    }
}

/// A rule body's `neq` over a variable an earlier goal binds reads the carrier's `eq` at the
/// value it was bound to.
#[test]
fn a_rule_body_neq_over_a_bound_variable_reads_its_carriers_eq() {
    let rules = "  entity Pick(c: Color)\n  fact Pick(c: Green)\n  \
                 rule rv(?c) :- Pick(c: ?c), neq(?c, Red)";
    for (ns, color, rows) in [
        ("test.cbrd2.tneq.bvc", CUSTOM_EQ, 0),
        ("test.cbrd2.tneq.bvs", STRUCTURAL_EQ, 1),
    ] {
        let mut kb = load_kb_with(&src(ns, color, rules));
        let goal = query_pattern_term(&mut kb, &format!("{ns}.rv(?c)"));
        let got = counting(|| kb.resolve(&[goal], &Default::default()));
        assert_eq!(got.iter().filter(|s| s.is_definite()).count(), rows, "{ns}: `rv(?c)`");
    }
}

/// A provider whose `eq` is a provision's binding: the `neq`'s `eq` is the bound operation, at
/// a precondition and in a rule body.
#[test]
fn a_neq_reads_an_eq_bound_by_the_provision() {
    let color = r#"
  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color, eq = sameColor]
    provides Eq[T = Color]
  end
  operation sameColor(a: Color, b: Color) -> Bool = true
"#;
    let ns = "test.cbrd2.tneq.bind";
    let ops = "  operation needy(c: Color) -> Int64 requires neq(c, Red) = 1
  \
               operation caller() -> Int64 = needy(Green)
  \
               rule rc() :- neq(Green, Red)";
    let errs = errors_reading_no_index(&src(ns, color, ops));
    assert!(
        errs.iter().any(|e| e.contains("unsatisfied precondition")),
        "`sameColor` holds of `(Green, Red)`: {errs:?}"
    );
    let rule_only = "  rule rc() :- neq(Green, Red)";
    let mut kb = load_kb_with(&src("test.cbrd2.tneq.bindr", color, rule_only));
    let goal = query_pattern_term(&mut kb, "test.cbrd2.tneq.bindr.rc()");
    let got = counting(|| kb.resolve(&[goal], &Default::default()));
    assert!(!got.iter().any(|s| s.is_definite()), "`sameColor` holds of `(Green, Red)`");
}

/// A `neq` typed at an operation's type parameter is deferred to its requirement, which a goal
/// at the call has no frame for: it is typed at the call's arguments, at `Int64`'s member
/// (`wi_cbrd2_call_site_comparison_test`).
#[test]
fn a_generic_neq_is_read_through_an_untyped_eq() {
    for (ns, needy, arg, holds) in [
        ("test.cbrd2.tneq.g12", "needy[T](a: T, b: T)", "1, 2", true),
        ("test.cbrd2.tneq.g11", "needy[T](a: T, b: T)", "1, 1", false),
    ] {
        let ops = format!(
            "  operation {needy} -> Int64 requires PartialEq[T = T], neq(a, b) = 1\n  \
             operation caller() -> Int64 = needy({arg})"
        );
        let errs = load_errors_of(&src(ns, STRUCTURAL_EQ, &ops));
        assert_eq!(errs.is_empty(), holds, "`needy({arg})`: {errs:?}");
        if !holds {
            assert!(errs.iter().any(|e| e.contains("unsatisfied precondition")), "{errs:?}");
        }
    }
}
