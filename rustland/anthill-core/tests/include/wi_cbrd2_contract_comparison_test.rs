//! A CONTRACT'S COMPARISONS ARE TYPED IN THE OPERATION'S SIGNATURE (WI-20261105-CBRD2,
//! decided with the user 2026-11-15, "refuse ill-typed contracts"). Each `=`, `eq` and `neq` in
//! a `requires` or `ensures` clause is typed at the operation's parameters' declared types and
//! `result` at its return type, as the call of its carrier's member it is, and one that does not
//! type is refused at load. An `eq` keeps the member it was typed at, beside the clause as loaded,
//! and a proof over the clause reads it there rather than reading the operand's constructor at
//! run time.
//!
//! ## What fails with the change backed out
//!
//! Measured with a temporary switch (`type_contract_comparisons` not run), then removed. The
//! control is the switch unset: every row passes.
//!
//! * [`an_ill_typed_contract_comparison_is_refused`]: each program loads;
//! * [`a_comparison_written_with_its_result_column_is_typed_on_its_operands`]: the ill-typed
//!   one loads.
//!
//! [`a_well_typed_contract_comparison_loads`] passes either way by design: it is the control
//! that the typing refuses nothing it should accept, a field projection and a result column
//! included.

use crate::common::{load_errors_of, load_kb_with};

fn program(ns: &str, op: &str) -> String {
    format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, Bool, String, Float, PartialEq}}\n  \
         import anthill.prelude.PartialEq.{{eq, neq}}\n  sort Box\n    entity box(value: Int64)\n    \
         {op}\n  end\nend\n"
    )
}

fn refused(ns: &str, op: &str, says: &str) {
    let errs = load_errors_of(&program(ns, op));
    assert!(
        errs.iter().any(|e| e.contains(says)),
        "`{op}` is refused saying `{says}`; got {errs:?}"
    );
}

/// `eq(result, "a")` over an `Int64` result, `eq(b, "x")` over an `Int64` parameter and
/// `neq(x, 1.5)` over an `Int64` are refused where the operation is declared.
#[test]
fn an_ill_typed_contract_comparison_is_refused() {
    refused(
        "test.cbrd2.cc.r1",
        "operation f(x: Int64) -> Int64\n      ensures eq(result, \"a\")\n      = x",
        "expected Int64, got String",
    );
    refused(
        "test.cbrd2.cc.r2",
        "operation f(b: Int64) -> Int64\n      requires eq(b, \"x\")\n      = b",
        "expected Int64, got String",
    );
    refused(
        "test.cbrd2.cc.r3",
        "operation f(x: Int64) -> Int64\n      ensures neq(x, 1.5)\n      = x",
        "expected Int64, got Float",
    );
}

/// A comparison written with its result column, the relational form a goal may take, is typed
/// as the call of its two operands.
#[test]
fn a_comparison_written_with_its_result_column_is_typed_on_its_operands() {
    refused(
        "test.cbrd2.cc.c1",
        "operation f(x: Int64) -> Int64\n      ensures neq(x, \"a\", true)\n      = x",
        "expected Int64, got String",
    );
}

/// A comparison over a field projection of `result`, over a parameter and with its result
/// column loads.
#[test]
fn a_well_typed_contract_comparison_loads() {
    for (ns, op) in [
        (
            "test.cbrd2.cc.w1",
            "operation wrap(x: Int64) -> Box\n      ensures eq(result.value, x)\n      = box(value: x)",
        ),
        (
            "test.cbrd2.cc.w2",
            "operation f(b: Int64) -> Int64\n      requires neq(b, 0)\n      = b",
        ),
        (
            "test.cbrd2.cc.w3",
            "operation f(x: Int64) -> Int64\n      ensures neq(x, 1, true)\n      = x",
        ),
    ] {
        load_kb_with(&program(ns, op));
    }
}
