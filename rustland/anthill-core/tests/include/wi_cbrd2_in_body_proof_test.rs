//! AN IN-BODY PROOF'S `eq` IS DECIDED AT THE MEMBER IT WAS TYPED AT (WI-20261105-CBRD2). The
//! typer proves a `proof … by derivation conclude P` once `P` is typed, and the goal it proves
//! keeps, for each `eq` in `P`, the carrier's member the typer chose: an `eq` over
//! `Option[T = Color]` or `List[T = Color]` runs that composite's member with `Color`'s
//! dictionary rather than reading an operand's constructor at run time.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, then removed. The control is each switch unset: every
//! row passes.
//!
//! * The list literal written as its list (`list_literals_as_lists` returning its term):
//!   [`an_eq_over_a_composite_is_decided_by_its_member`] fails at `eq([Green], [Red])`,
//!   which `List`'s `eq` refutes, reading `ListLiteral(Green)` as no list. The rows of
//!   `wi_cbrd2_list_literal_goal_test` measure that change at its other sites.
//! * The members not carried onto the goal (`in_body_proof_goal` lowering the conclusion
//!   only): every row passes, by design. The equality index then finds `some` and `cons`
//!   (their derived members are dispatched) and reaches the same members, its bridge
//!   building `Color`'s dictionary from the operands, under `not` as well. The rows read it
//!   12 times with the switch and not at all without (traced, trace removed): the census is
//!   the measurement, as for an `=` at a composite in a rule body.
//!
//! [`a_composite_eq_over_a_structural_element_is_decided_alike`] and
//! [`a_generic_operations_proof_is_typed_and_left_undecided`] are controls: the member
//! decides what structure decided before, and a member entered through a parameter's
//! dictionary, which a load-time proof has no value for, leaves the proof undecided rather
//! than failing the load.
//!
//! That the typer's own discharge reads the typed conclusion is not observable by a row: a
//! discharged conclusion is assumed into a Γ that already derives it. It too was measured by
//! the index's readers, with a switch proving the conclusion before it is typed: the load
//! then read the index once in the in-body `eq` row of `wi756_proof_path_eq_override_test`,
//! and as it stands it reads it not at all.

use anthill_core::kb::node_occurrence::Expr;
use anthill_core::kb::typing::{in_body_proof_goal, prove_from_gamma, FlowEnv};

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

fn src(ns: &str, color: &str, caller: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Eq, PartialEq, Option, List}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.PartialEq.{{eq, neq}}
{color}
  {caller}
end
"#
    )
}

/// Load `src`, take the `Expr::Proof` heading `<ns>.caller`'s body as the load left it, and
/// prove its goal as the typer does, under the empty Γ a proof at the body's entry sees.
fn discharges(src: &str, ns: &str) -> bool {
    let mut kb = crate::common::load_kb_with(src);
    let caller = kb
        .try_resolve_symbol(&format!("{ns}.caller"))
        .expect("caller symbol");
    let body = kb.op_body_node(caller).expect("caller body node");
    let Some(Expr::Proof {
        target, conclude, ..
    }) = body.as_expr()
    else {
        panic!("caller body is not Expr::Proof: {:?}", body.as_expr());
    };
    let (target, conclude) = (*target, conclude.clone());
    let goal = in_body_proof_goal(&mut kb, target, conclude.as_ref());
    prove_from_gamma(&mut kb, &FlowEnv::empty(), &goal)
}

fn conclude(goal: &str) -> String {
    format!("operation caller() -> Int64 =\n    proof h by derivation conclude {goal} end\n    0")
}

/// `eq(some(Green), some(Red))` and `eq([Green], [Red])` hold by `Color`'s `eq`, entered
/// through `Option`'s and `List`'s members.
#[test]
fn an_eq_over_a_composite_is_decided_by_its_member() {
    for (ns, goal) in [
        ("test.cbrd2.ibp.opt", "eq(some(Green), some(Red))"),
        ("test.cbrd2.ibp.list", "eq([Green], [Red])"),
    ] {
        assert!(
            discharges(&src(ns, CUSTOM_EQ, &conclude(goal)), ns),
            "`Color.eq` holds of `(Green, Red)`, so `{goal}` is proved"
        );
    }
    // Under `not`, which the goal spells `kernel.not`, the `eq` keeps its member as well.
    let ns = "test.cbrd2.ibp.notopt";
    assert!(!discharges(
        &src(ns, CUSTOM_EQ, &conclude("not(eq(some(Green), some(Red)))")),
        ns
    ));
}

/// Over the structural carrier the same conclusions are false, and an identical pair true.
#[test]
fn a_composite_eq_over_a_structural_element_is_decided_alike() {
    for (ns, goal, holds) in [
        ("test.cbrd2.ibp.sopt", "eq(some(Green), some(Red))", false),
        ("test.cbrd2.ibp.slist", "eq([Green], [Red])", false),
        ("test.cbrd2.ibp.srefl", "eq(some(Red), some(Red))", true),
        ("test.cbrd2.ibp.snot", "not(eq(some(Green), some(Red)))", true),
    ] {
        assert_eq!(
            discharges(&src(ns, STRUCTURAL_EQ, &conclude(goal)), ns),
            holds,
            "`{goal}` over structural `Color`"
        );
    }
}

/// A generic operation's `eq(a, b)` is typed at `T`'s dictionary: the proof loads and is not
/// proved, its operands being parameters.
#[test]
fn a_generic_operations_proof_is_typed_and_left_undecided() {
    let ns = "test.cbrd2.ibp.gen";
    let caller = "operation caller[T](a: T, b: T) -> Int64 requires PartialEq[T = T] =\n    \
                  proof h by derivation conclude eq(a, b) end\n    0";
    assert!(!discharges(&src(ns, CUSTOM_EQ, caller), ns));
}
