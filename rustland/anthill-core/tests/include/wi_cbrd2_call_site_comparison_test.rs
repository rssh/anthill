//! WI-20261105-CBRD2 — a comparison in a callee's `requires` or effect guard, proved or refuted
//! at a call, is decided at its member there. The clause is typed in the callee's signature
//! (proposal 073 §5), and a comparison its signature leaves with no member — one at the callee's
//! type parameter, `neq(a, b)` over `a: T` — is typed at the call's arguments, as the same
//! comparison written in an operation body is: `needy(Green, Red)` under `requires neq(a, b)`
//! reads `Color`'s `eq`. A guard is read as a clause of the operation whose row it is, the
//! override a spec call is charged with included. And a law a proof uses there reads its own
//! guards' dictionaries: `neq(?b, zero)` in `mul_div`'s guard, under `EuclideanDomain[T = A]`,
//! is `A`'s `PartialEq` from that dictionary's chain (proposal 060.1 §1).
//!
//! Before, each of these was compared with no member, counted by
//! `untyped_equalities_by_this_thread`; the verdicts were the same, read off the operands'
//! constructors by the equality index.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, then removed. The control is each switch unset: every
//! row passes.
//!
//! * The call-site typing off (`comparisons_typed_at_the_call` keeping the goal as built):
//!   [`a_comparison_at_the_callees_parameter_is_typed_at_the_call`],
//!   [`a_spec_operations_guard_is_typed_at_the_call`] and
//!   [`a_contract_call_typed_before_its_callees_contract`] fail on the count.
//! * A guarded equation skipped by the weave, as before
//!   ([`a_laws_guard_reads_the_dictionary_its_guard_read`]), and the bare parameter's chain
//!   route off (`composed_from_guards` declining an instance that is the parameter itself):
//!   the law row fails on the count either way, one equality compared with no member.
//! * The override's guard looked up under the spec operation (`fn_sym` for `return_owner` at
//!   the discharge): every row passes, the call-site typing typing the override's guard
//!   instead, its operands being the call's literals. With both backed out
//!   [`an_overrides_guard_is_refuted_as_its_own_clause`] fails on the count too.

use anthill_core::kb::resolve::untyped_equalities_by_this_thread;

use crate::common::{load_errors_of, load_stdlib_kb};

/// The load errors of `src` and the equalities the load compared with no member, the shared
/// base loaded first so its own load is not counted.
fn errors_and_untyped(src: &str) -> (Vec<String>, usize) {
    drop(load_stdlib_kb());
    let before = untyped_equalities_by_this_thread();
    let errs = load_errors_of(src);
    (errs, untyped_equalities_by_this_thread() - before)
}

/// `Color`, whose own `eq` holds of any two colours.
const CUSTOM_EQ: &str = r#"
  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color]
    provides Eq[T = Color]
    operation eq(a: Color, b: Color) -> Bool = true
  end
"#;

fn src(ns: &str, decls: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Eq, PartialEq, Effect, Error, DivisionByZero}}
  import anthill.prelude.PartialEq.{{eq, neq}}
  sort Boom
    entity Bang
    provides Effect[T = Boom]
  end
{CUSTOM_EQ}
{decls}
end
"#
    )
}

fn refused_naming(errs: &[String], text: &str) -> bool {
    errs.iter().any(|e| e.contains(text))
}

/// `needy[T](a: T, b: T) requires PartialEq[T = T], neq(a, b)`: at `Int64` the precondition is
/// proved for `1, 2` and not for `1, 1`; at `Color` it is not proved for `Green, Red`, whose
/// `eq` holds. Each decided at the call's member.
#[test]
fn a_comparison_at_the_callees_parameter_is_typed_at_the_call() {
    for (n, (args, holds)) in [("1, 2", true), ("1, 1", false), ("Green, Red", false)].into_iter().enumerate() {
        let decls = format!(
            "  operation needy[T](a: T, b: T) -> Int64 requires PartialEq[T = T], neq(a, b) = 1\n  \
             operation caller() -> Int64 = needy({args})"
        );
        let (errs, untyped) = errors_and_untyped(&src(&format!("cbrd2.cs.par{n}"), &decls));
        assert_eq!(!refused_naming(&errs, "unsatisfied precondition"), holds, "needy({args}): {errs:?}");
        assert_eq!(untyped, 0, "needy({args}): an equality compared with no member");
    }
}

/// A spec operation's guard at its type parameter, `Chk.risky(c: T, d: T) effects { Boom :-
/// eq(c, d) }`, at a call at `Color` that `Color`'s own `risky` answers: `Color`'s `eq` holds,
/// so the call owes `Boom`.
#[test]
fn a_spec_operations_guard_is_typed_at_the_call() {
    let decls = "  sort Chk\n    sort T = ?\n    \
                 operation risky(c: T, d: T) -> Int64 effects { Boom :- eq(c, d) }\n  end\n  \
                 operation caller() -> Int64 = Chk.risky(Green, Red)\n";
    let program = src("cbrd2.cs.spec", decls).replace(
        "    operation eq(a: Color, b: Color) -> Bool = true\n",
        "    operation eq(a: Color, b: Color) -> Bool = true\n    provides Chk[T = Color]\n    \
         operation risky(c: Color, d: Color) -> Int64\n      effects { Boom :- eq(c, d) } = 0\n",
    );
    let (errs, untyped) = errors_and_untyped(&program);
    assert!(refused_naming(&errs, "undeclared effect: Boom"), "{errs:?}");
    assert_eq!(untyped, 0, "an equality compared with no member");
}

/// A spec call the fallback charges with its override's row refutes the override's guard as
/// that operation's clause: `Sp.op(x, 2)` drops `Error[DivisionByZero] :- eq(d, 0)`, and
/// `Sp.op(x, 0)` owes it.
#[test]
fn an_overrides_guard_is_refuted_as_its_own_clause() {
    let program = |ns: &str, d: &str| {
        src(
            ns,
            &format!(
                "  sort Sp\n    sort T = ?\n    effects E = ?\n    \
                 operation op(s: Self, d: Int64) -> Int64 effects {{s.E, Error[DivisionByZero] :- eq(d, 0)}}\n  end\n  \
                 sort Car\n    sort V = ?\n    effects EC = ?\n    entity car(v: V)\n    \
                 provides Sp[T = V, E = {{EC}}]\n    \
                 operation op(c: Self, d: Int64) -> Int64 effects {{EC, Error[DivisionByZero] :- eq(d, 0)}} = 1\n  end\n  \
                 operation viaSpec[R](x: Car[V = Int64, EC = R]) -> Int64 effects {{R}} = Sp.op(x, {d})\n"
            ),
        )
    };
    for (n, (d, owes)) in [("2", false), ("0", true)].into_iter().enumerate() {
        let (errs, untyped) = errors_and_untyped(&program(&format!("cbrd2.cs.over{n}"), d));
        assert_eq!(refused_naming(&errs, "DivisionByZero"), owes, "d = {d}: {errs:?}");
        assert_eq!(untyped, 0, "d = {d}: an equality compared with no member");
    }
}

/// A call in a contract typed before its callee's contract is: `Sp.spec`'s `requires eq(needy(0),
/// 1)` calls `needy(0)` under `requires neq(x, 0)` while the contracts are typed ahead of the
/// bodies, and the precondition is still decided at `Int64`'s member, and refused.
#[test]
fn a_contract_call_typed_before_its_callees_contract() {
    let decls = "  operation needy(x: Int64) -> Int64 requires neq(x, 0) = x\n  \
                 sort Sp\n    sort T = ?\n    \
                 operation spec(b: T) -> Int64 requires eq(needy(0), 1)\n  end\n";
    let (errs, untyped) = errors_and_untyped(&src("cbrd2.cs.ahead", decls));
    assert!(
        errs.iter().any(|e| e.contains("needy.requires") && e.contains("unsatisfied precondition")),
        "{errs:?}"
    );
    assert_eq!(untyped, 0, "an equality compared with no member");
}

/// A law the proof uses to refute a guard compares in its own guard through the dictionaries
/// its guards read: `mul_div`'s `neq(?b, zero)`, at the `Int64` or `BigInt` the matched divisor
/// is, is that type's `PartialEq` held by its `EuclideanDomain`. `risky(x, 2)` drops `Boom` by
/// the law, `risky(x, 0)` owes it.
#[test]
fn a_laws_guard_reads_the_dictionary_its_guard_read() {
    let program = |ns: &str, ty: &str, call: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, BigInt, Effect, EuclideanDomain, Additive}}
  import anthill.prelude.PartialEq.{{neq}}
  import anthill.prelude.Additive.{{zero}}
  import anthill.prelude.Multiplicative.{{mul}}
  import anthill.prelude.Divisible.{{div}}
  sort Boom
    entity Bang
    provides Effect[T = Boom]
  end
  rule mul_div: div[A](mul(?a, ?b: A), ?b) = ?a :- EuclideanDomain[T = A], Additive[T = A], neq(?b, zero)
  operation risky(a: {ty}, b: {ty}) -> {ty} effects {{ Boom :- neq((a * b) / b, a) }} = a
  operation c(x: {ty}) -> {ty} = {call}
end
"#
        )
    };
    for (n, (ty, call, owes)) in [
        ("Int64", "risky(x, 2)", false),
        ("Int64", "risky(x, 0)", true),
        ("BigInt", "risky(x, 2n)", false),
    ]
    .into_iter()
    .enumerate()
    {
        let (errs, untyped) = errors_and_untyped(&program(&format!("cbrd2.cs.law{n}"), ty, call));
        assert_eq!(refused_naming(&errs, "undeclared effect: Boom"), owes, "{call}: {errs:?}");
        assert_eq!(untyped, 0, "{call}: an equality compared with no member");
    }
}
