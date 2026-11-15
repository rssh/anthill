//! AN EFFECT GUARD'S COMPARISONS ARE TYPED IN THE OPERATION'S SIGNATURE (WI-20261105-CBRD2),
//! as a contract's are: each `=`, `eq` and `neq` of a guard in the effects row is the call of
//! its carrier's member at the parameters' types, and one that does not type is refused at
//! load, naming `===` for a structural comparison (decided with the user, 2026-11-15). A
//! refutation of a guard at a call, and of a `requires` at a rule-body call, proves the
//! negation as typed there — the swapped comparison is typed beside the conjunct
//! (`negated_comparison_term`) — so each is decided at the member, not by the equality index
//! reading an operand's constructor.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, then removed. The control is each switch unset: every
//! row passes.
//!
//! * Guards not typed (only `requires` and `ensures`):
//!   [`an_ill_typed_guard_comparison_is_refused_naming_structural_equality`] fails, each guard
//!   loading clean, and
//!   [`a_guard_comparison_is_refuted_at_its_carriers_eq`] fails on the index reads, its
//!   verdicts unchanged.
//! * The refutation reading the substituted term (no typed twin, the negation built by
//!   `negate_goal`): [`a_guard_comparison_is_refuted_at_its_carriers_eq`] and
//!   [`a_rule_body_precondition_is_refuted_at_its_carriers_eq`] fail on the index reads.
//! * The refusal without its advice (`cause` alone): the two refusal rows fail on the text.
//!
//! [`a_well_typed_guard_loads`] and [`a_dispatched_implementations_guard_is_refuted_at_its_carriers_eq`]
//! pass either way by design: the control, and the verdicts of a call whose spec operation's
//! guard is at a type parameter.

use anthill_core::kb::resolve::eq_index_reads_by_this_thread;

use crate::common::{load_errors_of, load_stdlib_kb};

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
  import anthill.prelude.{{Int64, Bool, Eq, PartialEq, Option, Effect}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.PartialEq.{{eq, neq}}
  sort Boom
    entity Bang
    provides Effect[T = Boom]
  end
{color}
{ops}
end
"#
    )
}

/// The load errors of `src` and the equality index reads the load made, the shared base
/// loaded first so its own load is not counted.
fn errors_and_index_reads(src: &str) -> (Vec<String>, usize) {
    drop(load_stdlib_kb());
    let before = eq_index_reads_by_this_thread();
    let errs = load_errors_of(src);
    (errs, eq_index_reads_by_this_thread() - before)
}

const ADVICE: &str = "`===` compares any two values structurally";

/// `eq(c, 1)`, `c = 1` and `neq(c, "a")` over `c: Color` compare values of two types.
#[test]
fn an_ill_typed_guard_comparison_is_refused_naming_structural_equality() {
    for (n, guard) in ["eq(c, 1)", "c = 1", "neq(c, \"a\")"].into_iter().enumerate() {
        let ops = format!("  operation risky(c: Color) -> Int64\n    effects {{ Boom :- {guard} }} = 0");
        let errs = load_errors_of(&src(&format!("test.cbrd2.egc.bad{n}"), CUSTOM_EQ, &ops));
        assert!(
            errs.iter().any(|e| e.contains("risky.effects") && e.contains(ADVICE)),
            "`{guard}` over `c: Color`: {errs:?}"
        );
    }
}

/// A contract's comparison is refused in the same words.
#[test]
fn an_ill_typed_contract_comparison_names_structural_equality_too() {
    let ops = "  operation needy(c: Color) -> Int64 requires eq(c, 1) = 0";
    let errs = load_errors_of(&src("test.cbrd2.egc.req", CUSTOM_EQ, ops));
    assert!(
        errs.iter().any(|e| e.contains("needy.requires") && e.contains(ADVICE)),
        "`requires eq(c, 1)`: {errs:?}"
    );
}

/// The control: a guard comparing two colours loads, its effect dropped where it is refuted.
#[test]
fn a_well_typed_guard_loads() {
    let ops = "  operation risky(c: Color) -> Int64\n    effects { Boom :- eq(c, Red) } = 0\n  \
               operation caller() -> Int64 = risky(Green)";
    let errs = load_errors_of(&src("test.cbrd2.egc.ok", STRUCTURAL_EQ, ops));
    assert!(errs.is_empty(), "{errs:?}");
}

/// `risky(<arg>)` under `effects { Boom :- <guard> }`: over the custom `Color`, whose `eq`
/// makes the operands equal, the call owes `Boom` where the guard is an `eq` and owes nothing
/// where it is a `neq`; over the structural one the other way round. Decided at the members,
/// the index not read.
#[test]
fn a_guard_comparison_is_refuted_at_its_carriers_eq() {
    for (n, (param, guard, arg, custom_owes)) in [
        ("c: Color", "eq(c, Red)", "Green", true),
        ("c: Color", "neq(c, Red)", "Green", false),
        ("o: Option[T = Color]", "eq(o, some(Red))", "some(Green)", true),
        ("o: Option[T = Color]", "neq(o, some(Red))", "some(Green)", false),
    ]
    .into_iter()
    .enumerate()
    {
        let ops = format!(
            "  operation risky({param}) -> Int64\n    effects {{ Boom :- {guard} }} = 0\n  \
             operation caller() -> Int64 = risky({arg})"
        );
        for (tag, color, owes) in [("c", CUSTOM_EQ, custom_owes), ("s", STRUCTURAL_EQ, !custom_owes)] {
            let (errs, reads) = errors_and_index_reads(&src(&format!("test.cbrd2.egc.g{n}{tag}"), color, &ops));
            assert_eq!(reads, 0, "`{guard}` at `risky({arg})`, {tag}: the load read the equality index");
            assert_eq!(
                errs.iter().any(|e| e.contains("undeclared effect: Boom")),
                owes,
                "`{guard}` at `risky({arg})`, {tag}: {errs:?}"
            );
        }
    }
}

/// A rule body's call of `needy(Green)` under `requires neq(c, Red)`: refuted over the custom
/// `Color` and refused at load, left standing over the structural one.
#[test]
fn a_rule_body_precondition_is_refuted_at_its_carriers_eq() {
    let ops = "  operation needy(c: Color) -> Int64 requires neq(c, Red) = 0\n  \
               entity Holder(c: Color)\n  \
               rule uses(?r) :- Holder(c: ?), eq(?r, needy(Green))";
    for (ns, color, refused) in [
        ("test.cbrd2.egc.rbc", CUSTOM_EQ, true),
        ("test.cbrd2.egc.rbs", STRUCTURAL_EQ, false),
    ] {
        let (errs, reads) = errors_and_index_reads(&src(ns, color, ops));
        assert_eq!(reads, 0, "{ns}: the load read the equality index");
        assert_eq!(
            errs.iter().any(|e| e.contains("needy.requires")),
            refused,
            "{ns}: {errs:?}"
        );
    }
}

/// A spec call dispatched to its implementation is charged the implementation's guarded
/// effect: `Chk.risky(Green, Red)` over the custom `Color` owes `Boom`, over the structural one
/// nothing. The verdicts only: the spec operation's own guard, `eq(c, d)` at `T`, is refuted
/// at the call untyped, the equality index naming `Color.eq` (one read over the custom
/// `Color`) — a comparison at a callee's type parameter has its member at the call's type,
/// which no load types yet.
#[test]
fn a_dispatched_implementations_guard_is_refuted_at_its_carriers_eq() {
    let chk = "  sort Chk\n    sort T = ?\n    \
               operation risky(c: T, d: T) -> Int64 effects { Boom :- eq(c, d) }\n  end\n";
    let member = "    provides Chk[T = Color]\n    \
                  operation risky(c: Color, d: Color) -> Int64\n      effects { Boom :- eq(c, d) } = 0\n";
    let caller = "  operation caller() -> Int64 = Chk.risky(Green, Red)";
    for (ns, color, owes) in [
        ("test.cbrd2.egc.dc", CUSTOM_EQ, true),
        ("test.cbrd2.egc.ds", STRUCTURAL_EQ, false),
    ] {
        let color = color.replace("  end\n", &format!("{member}  end\n"));
        let errs = load_errors_of(&src(ns, &format!("{chk}{color}"), caller));
        assert_eq!(
            errs.iter().any(|e| e.contains("undeclared effect: Boom")),
            owes,
            "{ns}: {errs:?}"
        );
    }
}
