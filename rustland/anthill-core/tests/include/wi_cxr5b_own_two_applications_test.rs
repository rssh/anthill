//! WI-20261122-CXR5B, the P readers — A PROVIDER'S OWN PROVISIONS AT TWO APPLICATIONS (decision 1
//! of `docs/design/spec-carrier-set.md`, its d15).
//!
//! `Foo provides Coll[C = Self, Elem = Int64, first = f1]` beside `Coll[C = Self, Elem = String,
//! first = f2]` are two carriers by the model, as a witness's two provisions are (d5), and a call
//! tells them apart by what it fixes. Step 3 kept them refused at load, "conflicting provisions",
//! because the readers of a value's sort's ONE view of a spec (`provider_spec_view_bindings`)
//! merged them and kept the first binding written: admitted, `c.Elem` off a `Foo` meant whichever
//! provision came first. Now the refusal is lifted, the view keeps what the provisions agree on
//! and leaves out what they bind apart (`own_bindings_apart`), and a projection of such a member
//! is refused naming both types, since it fixes the receiver and nothing else.
//!
//! WHAT FAILS IF THIS IS BACKED OUT, and what passes either way, is said at each row. MEASURED
//! 2026-11-23: backed out whole, every row but the controls was refused "conflicting
//! provisions"; with the refusal lifted and the view left as it was, the projection rows answered
//! by the order written.

use anthill_core::eval::{HostValue, Value};

use crate::common::{interp_for, load_errors_of};

fn coll(ns: &str, first: &str, second: &str, extra: &str, go: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Bool}}
  sort Coll
    sort C = ?
    sort Elem = ?
    operation first(c: C) -> Elem
  end
  sort Foo
    entity foo
    {first}
    {second}
    operation f1(c: Foo) -> Int64 = 1
    operation f2(c: Foo) -> String = "two"
  end
{extra}
  operation go() -> Int64 = {go}
end
"#
    )
}

const INT: &str = "provides Coll[C = Self, Elem = Int64, first = Foo.f1]";
const STR: &str = "provides Coll[C = Self, Elem = String, first = Foo.f2]";

/// Both orders the two provisions can be written in.
fn orders() -> [(&'static str, &'static str, &'static str); 2] {
    [("is", INT, STR), ("si", STR, INT)]
}

fn go(src: &str, ns: &str) -> i64 {
    match interp_for(src).call(&format!("{ns}.go"), &HostValue::all(&[])).map(|h| h.value) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{ns}.go` answered no Int64: {other:?}"),
    }
}

/// The type the call expects, a bracket, a generic call's `requires` and an operation's own
/// `requires` each fix `Elem`, and the provision there answers — in either order. FAILS backed
/// out: refused at load, "conflicting provisions".
#[test]
fn a_call_reads_the_provision_at_what_it_fixes_in_either_order() {
    let via = "  operation viaS[X](x: X) -> String requires Coll[C = X, Elem = String] = Coll.first(x)\n  \
               operation takes(i: Foo) -> Int64 requires Coll[C = Foo, Elem = Int64] = Coll.first(i)\n";
    for (order, a, b) in orders() {
        for (shape, body, want) in [
            ("int", "Coll.first(foo)", 1),
            ("str", "String.length(Coll.first(foo))", 3),
            ("bracket", "String.length(Coll[Elem = String].first(foo))", 3),
            ("generic", "String.length(viaS(foo))", 3),
            ("requires", "takes(foo)", 1),
        ] {
            let ns = format!("wicxr5bot.call.{shape}.{order}");
            assert_eq!(go(&coll(&ns, a, b, via, body), &ns), want, "{ns}");
        }
    }
}

/// A call that fixes nothing else leaves `Elem` open between the two, and is refused as b8's call
/// between two witnesses is — the call's refusal, not the load's. FAILS backed out: the call's
/// refusal is raised beside "conflicting provisions", which this row refuses.
#[test]
fn a_call_fixing_nothing_else_leaves_elem_open() {
    let extra = "  operation open() -> Int64 =\n    let x = Coll.first(foo)\n    7\n";
    for (order, a, b) in orders() {
        let ns = format!("wicxr5bot.open.{order}");
        let text = load_errors_of(&coll(&ns, a, b, extra, "open()")).join("\n");
        assert!(text.contains("it leaves `Elem` open"), "`{ns}`:\n{text}");
        assert!(!text.contains("conflicting provisions"), "`{ns}`:\n{text}");
    }
}

/// `c.Elem` off a `Foo` fixes the receiver and nothing else, so it names neither provision's
/// `Elem` and is refused, naming both — in either order, and where the body would have handed an
/// `Int64` to a `String` reader (`-> c.Elem = 5`). FAILS backed out: refused "conflicting
/// provisions"; with the refusal lifted and the view as it was, `getE` was typed by the provision
/// written first (1 in one order, refused in the other), and `-> c.Elem = 5` LOADED and died at
/// run.
#[test]
fn a_projection_off_the_provider_names_neither_application() {
    for (order, a, b) in orders() {
        for (shape, extra, body) in [
            ("call", "  operation getE(c: Foo) -> c.Elem = Coll.first(c)\n", "getE(foo)"),
            ("unsound", "  operation getE(c: Foo) -> c.Elem = 5\n", "String.length(getE(foo))"),
        ] {
            let ns = format!("wicxr5bot.proj.{shape}.{order}");
            let text = load_errors_of(&coll(&ns, a, b, extra, body)).join("\n");
            for want in ["binding its member 'Elem' apart", "Int64", "String"] {
                assert!(text.contains(want), "`{ns}`: `{want}` missing:\n{text}");
            }
        }
    }
}

/// The view leaving `Elem` out is no provision at every `Elem`: a `requires` at `Elem = Bool`,
/// which neither provision is at, is refused in either order, naming it, and the load raises no
/// conflict. FAILS backed out (the conflict is raised beside it); with the lift alone, the view
/// as it was, it passes — the guard is that the view's left-out `Elem` reads as no provision.
#[test]
fn an_application_neither_provision_is_at_is_refused() {
    let extra = "  operation takesB(i: Foo) -> Int64 requires Coll[C = Foo, Elem = Bool] = 4\n";
    for (order, a, b) in orders() {
        let ns = format!("wicxr5bot.bool.{order}");
        let text = load_errors_of(&coll(&ns, a, b, extra, "takesB(foo)")).join("\n");
        assert!(text.contains("Elem = anthill.prelude.Bool"), "`{ns}`:\n{text}");
        assert!(!text.contains("conflicting provisions"), "`{ns}`:\n{text}");
    }
}
