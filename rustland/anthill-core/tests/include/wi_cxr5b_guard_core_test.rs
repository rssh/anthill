//! WI-20261122-CXR5B — THE GUARD CORE, BY DECISION 1 (`docs/design/spec-carrier-set.md`).
//!
//! `simp_guard_decision` — the `@[simp]` guards', the rule-body check's and an operation body's
//! question "can this call have an instance" — asked two questions by where the call's carriers
//! stand: every carrier at the spec's single carrier parameter asked each carrier to provide the
//! spec; a carrier anywhere else asked whether a provision binds them all. So which question a
//! call of a two-type-var spec got turned on which type-var is declared first, and with it the
//! refusal: `Sp.get(foo)` with no provision at `A = Foo` was refused "`Foo` provides no `Sp`"
//! with `A` declared first and "no provision of `Sp` binds `A = Foo`" with `B` first; `Sp.op(foo,
//! 1)` the same two ways. Now a spec with a dictionary and two or more type-vars
//! (`spec_asks_provisions`) is asked for a provision at what the call fixes, wherever it stands,
//! and refused "no provision of `S` binds …" naming it — WI-20260925-PRVA2's sentence, since
//! "`String` provides no `Conv`" is false of a provision's second binding. An operation body
//! asks this before the carrier at the single parameter, a defaulted operation's call as a
//! body-less one's. A self-representing spec keeps the per-carrier question (its carrier is the
//! provider; e7's row, `wi_cxr5b_self_rep_no_provision_test`, passes either way).
//!
//! The refusal "no provision binds …" told an operation that declares a requirement of the spec
//! not covering the call that it "declares no `Sp` requirement of its own"; it says the one it
//! declares does not cover it now.
//!
//! WHAT FAILS IF THIS IS BACKED OUT, and what passes either way, is said at each row. MEASURED
//! 2026-11-23: see each row.

use crate::common::{interp_for, load_errors_of};

/// `Sp[A, B]` (in the order `b_first` gives), `Foo`, two providers at `A = Self` and a driver
/// `go` whose body is `body`, with `extra` beside it.
fn program(ns: &str, b_first: bool, extra: &str, body: &str) -> String {
    let (x, y) = if b_first { ("B", "A") } else { ("A", "B") };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Sp
    sort {x} = ?
    sort {y} = ?
    operation op(c: A, x: B) -> Int64
    operation get(c: A) -> B
  end
  sort Foo
    entity foo
  end
  sort P
    entity p
    provides Sp[A = Self, B = Int64]
    operation op(c: P, x: Int64) -> Int64 = 1
    operation get(c: P) -> Int64 = 5
  end
  sort Q
    entity q
    provides Sp[A = Self, B = Int64]
    operation op(c: Q, x: Int64) -> Int64 = 2
    operation get(c: Q) -> Int64 = 6
  end
{extra}
  sort Driver
    operation go() -> Int64 = {body}
  end
end
"#
    )
}

/// The refusal of `body` in the order `b_first` gives, its namespace written `NS`.
fn refusal(order: &str, b_first: bool, extra: &str, body: &str) -> String {
    let ns = format!("wicxr5bgc.{order}");
    load_errors_of(&program(&ns, b_first, extra, body)).join("\n").replace(&ns, "NS")
}

/// A call fixing one carrier no provision is at is refused "no provision of `Sp` binds `A =
/// Foo`" in either order. FAILS backed out: with `A` declared first it was "`Foo` provides no
/// `Sp`".
#[test]
fn one_carrier_no_provision_is_at_is_refused_alike_in_either_order() {
    let a = refusal("get.afirst", false, "", "Sp.get(foo) + 0");
    let b = refusal("get.bfirst", true, "", "Sp.get(foo) + 0");
    assert!(a.contains("no provision of `NS.Sp` binds `A = NS.Foo`"), "A first:\n{a}");
    assert_eq!(a, b, "the two orders");
}

/// A call fixing two carriers no provision binds together is refused "no provision of `Sp` binds
/// `A = Foo, B = …`" in either order. FAILS backed out: with `A` declared first it was "`Foo`
/// provides no `Sp`".
#[test]
fn carriers_no_provision_binds_are_refused_alike_in_either_order() {
    let a = refusal("op.afirst", false, "", "Sp.op(foo, 1)");
    let b = refusal("op.bfirst", true, "", "Sp.op(foo, 1)");
    assert!(a.contains("no provision of `NS.Sp` binds `A = NS.Foo, B = anthill.prelude.Int64`"), "A first:\n{a}");
    assert_eq!(a, b, "the two orders");
}

/// An operation declaring a requirement of the spec that does not cover the call is told so, not
/// that it declares none — in either order. FAILS backed out: with `B` first the refusal said
/// "this operation declares no `Sp` requirement of its own", and with `A` first it was "`Foo`
/// provides no `Sp`".
#[test]
fn a_requirement_that_does_not_cover_the_call_is_named() {
    let extra = "  operation viaP[X](x: X) -> Int64 requires Sp[A = X, B = Int64] = Sp.op(foo, \"s\")\n";
    for (order, b_first) in [("cover.afirst", false), ("cover.bfirst", true)] {
        let text = refusal(order, b_first, extra, "viaP(p)");
        assert!(text.contains("the `Sp` requirement this operation declares does not cover it"), "{order}:\n{text}");
        assert!(!text.contains("declares no `Sp` requirement"), "{order}:\n{text}");
    }
}

/// CONTROL: a call at a provision answers in either order. Passes either way, by design.
#[test]
fn a_call_at_a_provision_answers_in_either_order() {
    for (order, b_first) in [("run.afirst", false), ("run.bfirst", true)] {
        let ns = format!("wicxr5bgc.{order}");
        let got = interp_for(&program(&ns, b_first, "", "Sp.op(p, 1) + Sp.get(q)"))
            .call(&format!("{ns}.Driver.go"), &anthill_core::eval::HostValue::all(&[]))
            .map(|h| h.value);
        assert!(matches!(got, Ok(anthill_core::eval::Value::Int(7))), "{order}: {got:?}");
    }
}
