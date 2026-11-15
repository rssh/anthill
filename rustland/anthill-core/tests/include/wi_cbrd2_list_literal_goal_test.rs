//! A LIST LITERAL IN A GOAL BUILT FROM OPERATION-BODY CODE IS THE LIST IT BUILDS
//! (WI-20261105-CBRD2). A call's argument substituted into its callee's `requires` or effect
//! guard, a fact Γ learns from a `let` or an `if`, an in-body proof's conclusion and `result`
//! in a contract proof are built from the code's term (`typing::code_goal_term`), where
//! `[e…]` is the reflect `ListLiteral(e…)`; it is written as the `cons`/`nil` spine, as a rule
//! body's list literal is, so the members that read a list and the clause's own literal
//! (lowered at load) see one value.
//!
//! Found by the in-body proof rows: with `eq` decided at its member, `List`'s `eq` read
//! `eq([Green], [Red])` as two constructors of no list and answered `false` over a `Color`
//! whose `eq` holds of every pair, so `requires not(eq(l, [Red]))` held at `needy([Green])`.
//! It loaded before as well, the structural verdict reading `ListLiteral(Green)` and
//! `ListLiteral(Red)` as unequal terms.
//!
//! ## What fails with the change backed out
//!
//! Measured with a temporary switch (`code_goal_term` returning the code's term unlowered),
//! then removed. The control is the switch unset: every row passes.
//!
//! * [`a_list_literal_argument_is_compared_as_a_list`]: the custom `Color` call is refused,
//!   `eq([Green], [Red])` refuted;
//! * [`a_list_literal_does_not_refute_its_own_equality`]: the `not(eq(…))` call loads;
//! * [`an_operation_reads_a_list_literal_argument`]: `needy([1, 2])` under `eq(length(l), 2)`
//!   is refused, `length` reading no list;
//! * [`a_fact_learned_from_a_list_literal_is_the_list`]: each of the five calls is refused;
//! * [`a_body_returning_a_list_literal_is_the_list_its_contract_reads`]: both contracts fail,
//!   'an `ensures` conjunct is not derivable from the body';
//! * [`an_effect_guard_reads_a_list_literal_argument`]: `head([1, 2])` owes
//!   `Error[EmptyStream]`, `isEmpty` reading no list.
//!
//! [`a_list_holding_a_parameter_stays_unproved`] passes either way by design: it is the
//! control that the spine keeps a parameter a parameter.

use crate::common::{load_errors_of, load_kb_with};

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
  import anthill.prelude.List.{{length}}
  import anthill.prelude.PartialEq.{{eq, neq}}
{color}
{ops}
end
"#
    )
}

fn loads(src: &str) {
    load_kb_with(src);
}

fn refused_as_unsatisfied(src: &str) {
    let errs = load_errors_of(src);
    assert!(
        errs.iter().any(|e| e.contains("unsatisfied precondition")),
        "the call's precondition is not proved; got {errs:?}"
    );
}

/// `needy([Green])` under `requires eq(l, [Red])`: proved by `List`'s `eq` at `Color`'s,
/// which holds; refused over the structural `Color`.
#[test]
fn a_list_literal_argument_is_compared_as_a_list() {
    let ops = "  operation needy(l: List[T = Color]) -> Int64 requires eq(l, [Red]) = 1\n  \
               operation caller() -> Int64 = needy([Green])";
    loads(&src("test.cbrd2.llg.c", CUSTOM_EQ, ops));
    refused_as_unsatisfied(&src("test.cbrd2.llg.s", STRUCTURAL_EQ, ops));
}

/// `needy([Green])` under `requires not(eq(l, [Red]))` over the custom `Color`: the two
/// lists are equal, so the precondition does not hold.
#[test]
fn a_list_literal_does_not_refute_its_own_equality() {
    let ops = "  operation needy(l: List[T = Color]) -> Int64 requires not(eq(l, [Red])) = 1\n  \
               operation caller() -> Int64 = needy([Green])";
    refused_as_unsatisfied(&src("test.cbrd2.llg.n", CUSTOM_EQ, ops));
}

/// `length([1, 2])` is `2` and not `0`.
#[test]
fn an_operation_reads_a_list_literal_argument() {
    let call = "  operation caller() -> Int64 = needy([1, 2])";
    loads(&src(
        "test.cbrd2.llg.l2",
        STRUCTURAL_EQ,
        &format!("  operation needy(l: List[T = Int64]) -> Int64 requires eq(length(l), 2) = 1\n{call}"),
    ));
    refused_as_unsatisfied(&src(
        "test.cbrd2.llg.l0",
        STRUCTURAL_EQ,
        &format!("  operation needy(l: List[T = Int64]) -> Int64 requires eq(length(l), 0) = 1\n{call}"),
    ));
}

/// A `let`, an `if` and an argument that hold a list literal — empty, nested, inside an
/// `Option` — prove a precondition the clause's own literal states.
#[test]
fn a_fact_learned_from_a_list_literal_is_the_list() {
    for (ns, ops) in [
        (
            "test.cbrd2.llg.let",
            "  operation needy(l: List[T = Int64]) -> Int64 requires eq(l, [1, 2]) = 1\n  \
             operation caller() -> Int64 =\n    let xs = [1, 2]\n    needy(xs)",
        ),
        (
            "test.cbrd2.llg.if",
            "  operation needy(l: List[T = Int64]) -> Int64 requires eq(l, [1, 2]) = 1\n  \
             operation caller(xs: List[T = Int64]) -> Int64 =\n    \
             if eq(xs, [1, 2]) then needy(xs) else 0",
        ),
        (
            "test.cbrd2.llg.empty",
            "  operation needy(l: List[T = Int64]) -> Int64 requires eq(length(l), 0) = 1\n  \
             operation caller() -> Int64 = needy([])",
        ),
        (
            "test.cbrd2.llg.nested",
            "  operation needy(l: List[T = List[T = Int64]]) -> Int64 requires eq(l, [[1], [2, 3]]) = 1\n  \
             operation caller() -> Int64 = needy([[1], [2, 3]])",
        ),
        (
            "test.cbrd2.llg.opt",
            "  operation needy(o: Option[T = List[T = Int64]]) -> Int64 requires eq(o, some([1])) = 1\n  \
             operation caller() -> Int64 = needy(some([1]))",
        ),
    ] {
        loads(&src(ns, STRUCTURAL_EQ, ops));
    }
}

/// `needy([c])` over a parameter `c`: `[c]` is a list of an unknown colour, and
/// `eq([c], [Red])` is not proved.
#[test]
fn a_list_holding_a_parameter_stays_unproved() {
    let ops = "  operation needy(l: List[T = Color]) -> Int64 requires eq(l, [Red]) = 1\n  \
               operation caller(c: Color) -> Int64 = needy([c])";
    refused_as_unsatisfied(&src("test.cbrd2.llg.p", STRUCTURAL_EQ, ops));
}

/// The verdict `verify_proofs` gives `<ns>.pick.ensures`.
fn ensures_verdict(src: &str) -> anthill_core::kb::proof_verify::ProofVerdict {
    let mut kb = load_kb_with(src);
    let report = anthill_core::kb::proof_verify::verify_proofs(&mut kb);
    let hits: Vec<_> = report
        .iter()
        .filter(|r| r.rule_qn.ends_with("pick.ensures"))
        .collect();
    assert_eq!(hits.len(), 1, "one `pick.ensures` record");
    hits[0].verdict.clone()
}

/// A contract proof reads `result` as the body's term: `= [Green]` is the list, so
/// `ensures eq(result, [Red])` is proved through `Color`'s `eq` and `ensures
/// eq(length(result), 1)` through `length`.
#[test]
fn a_body_returning_a_list_literal_is_the_list_its_contract_reads() {
    use anthill_core::kb::proof_verify::ProofVerdict;
    for (ns, color, goal) in [
        ("test.cbrd2.llg.pe", CUSTOM_EQ, "eq(result, [Red])"),
        ("test.cbrd2.llg.pl", STRUCTURAL_EQ, "eq(length(result), 1)"),
    ] {
        let ops = format!(
            "  operation pick() -> List[T = Color]\n    ensures {goal}\n    = [Green]\n\n  \
             proof pick.ensures by derivation end"
        );
        assert_eq!(
            ensures_verdict(&src(ns, color, &ops)),
            ProofVerdict::Discharged,
            "`{goal}` over `[Green]`"
        );
    }
}

/// `head`'s `Error[EmptyStream] :- isEmpty(xs)` is refuted at `head([1, 2])`, which then owes
/// no error; `head([])` still does.
#[test]
fn an_effect_guard_reads_a_list_literal_argument() {
    let program = |ns: &str, arg: &str| {
        format!(
            "namespace {ns}\n  import anthill.prelude.{{Int64, List}}\n  \
             import anthill.prelude.List.{{head}}\n  operation f() -> Int64 = head({arg})\nend\n"
        )
    };
    loads(&program("test.cbrd2.llg.h2", "[1, 2]"));
    let errs = load_errors_of(&program("test.cbrd2.llg.h0", "[]"));
    assert!(
        errs.iter().any(|e| e.contains("undeclared effect: Error[T = EmptyStream]")),
        "`head([])` owes `Error[EmptyStream]`; got {errs:?}"
    );
}
