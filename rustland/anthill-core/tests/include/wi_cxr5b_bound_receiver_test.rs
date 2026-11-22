//! WI-20261122-CXR5B, fifth step — THE RECEIVER OF AN OPERATION BOUND BY NAME (the "bound
//! `joinTwo`" row of `docs/design/spec-carrier-set.md` §7, with ONE provision).
//!
//! For a self-representing spec, a provision's carrier is its provider (decisions 5 and 8):
//! `Bag provides Holder[C = Box, …]` is at `Bag`. A spec operation's first parameter typed
//! `Self` is the receiver, and a call reaches the provision through a value of the provider, so
//! the provider's member may narrow it to the provider — `check_member_signature` passes that
//! receiver. The check of an operation bound by name (`joinTwo = Bag.join`,
//! `check_instance_fact_op_signatures`) compared it against the spec at the provision's
//! bindings instead, and refused `Bag.join(a: Bag, b: Holder)` as incompatible with
//! `Holder[C = Box, Element = Int64]`, while the same receiver written as `Bag`'s member passed
//! (e4). Now the bound check passes the same receiver; a second parameter narrowed to the
//! provider is still refused, as it is for a member.
//!
//! WHAT FAILS IF THIS IS BACKED OUT, and what passes either way, is said at each row. MEASURED
//! 2026-11-22, these rows kept: with `src/` at `9ce71a1d9`, the first two fail and the third, a
//! guard against matching the receiver by its head alone, passes.

use crate::common::{interp_for, load_errors_of};

/// e4's `Holder`, `Box` and `Bag`, with `Bag`'s `peek` and `joinTwo` bound by name and `join`
/// declared `join_sig`, and a driver answering `joinTwo(bag, bag) * 10 + peek(box)`.
fn program(ns: &str, join_sig: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Holder
    sort C = ?
    sort Element = ?
    operation peek(c: C) -> Int64
    operation joinTwo(a: Self, b: Self) -> Int64
  end
  sort Box
    entity box(n: Int64)
  end
  sort Bag
    entity bag(n: Int64)
    provides Holder[C = Box, Element = Int64, peek = Bag.peekBox, joinTwo = Bag.join]
    operation peekBox(c: Box) -> Int64 = 2
    operation join({join_sig}) -> Int64 = 3
  end
  sort Driver
    operation go() -> Int64 = Holder.joinTwo(bag(n: 1), bag(n: 2)) * 10 + Holder.peek(box(n: 5))
  end
end
"#
    )
}

/// The bound `joinTwo` whose receiver is the provider answers, as the member form does (32).
/// FAILS backed out: refused at load, "parameter 1 of the bound operation has type `Bag`,
/// incompatible with the spec parameter type `Holder[C = Box, Element = Int64]`".
#[test]
fn a_bound_operation_may_narrow_its_receiver_to_the_provider() {
    let ns = "wicxr5bbr.receiver";
    let v = interp_for(&program(ns, "a: Bag, b: Holder"))
        .call(&format!("{ns}.Driver.go"), &anthill_core::eval::HostValue::all(&[]))
        .map(|h| h.value)
        .unwrap_or_else(|e| panic!("`{ns}.Driver.go`: {e:?}"));
    assert!(matches!(v, anthill_core::eval::Value::Int(32)), "{v:?}");
}

/// A SECOND parameter narrowed to the provider admits no other provider and stays refused,
/// naming that parameter alone. Refused either way, by design; that it names parameter 2 and not
/// parameter 1 FAILS backed out, where both were named.
#[test]
fn a_second_parameter_narrowed_to_the_provider_is_refused() {
    let text = load_errors_of(&program("wicxr5bbr.second", "a: Bag, b: Bag")).join("\n");
    assert!(text.contains("parameter 2 of the bound operation has type `Bag`"), "{text}");
    assert!(!text.contains("parameter 1 of the bound operation"), "{text}");
}

/// A parameterized provider's receiver is its CARRIER, the provider at its own type-vars: written
/// so (`join(a: Bag[T = T], …)`) the bound operation answers (5); narrowed to one instance
/// (`a: Bag[T = Int64]`), a call on another `Bag` would reach it, and it is refused naming the
/// receiver, as the member form is. FOUND BY /code-review: a first cut recognised the receiver by
/// its head alone, and `joinTwo(bag(v: "s"), …)` ran `join` on a `String` — this row FAILS under
/// that cut. It passes with the step backed out, by design: the own-type-vars form passed before
/// (the comparison is open where a type parameter stands), and every narrowed receiver was
/// refused.
#[test]
fn a_parameterized_providers_receiver_is_its_carrier() {
    let program = |ns: &str, join: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Holder
    sort C = ?
    operation peek(c: C) -> Int64
    operation joinTwo(a: Self, b: Self) -> Int64
  end
  sort Box
    entity box(n: Int64)
  end
  sort Bag
    sort T = ?
    entity bag(v: T)
    provides Holder[C = Box, peek = Bag.peekBox, joinTwo = Bag.join]
    operation peekBox(c: Box) -> Int64 = 2
    {join}
  end
  sort Driver
    operation go() -> Int64 = Holder.joinTwo(bag(v: "s"), bag(v: 1))
  end
end
"#
        )
    };
    let ns = "wicxr5bbr.own";
    let v = interp_for(&program(ns, "operation join(a: Bag[T = T], b: Holder) -> Int64 = 5"))
        .call(&format!("{ns}.Driver.go"), &anthill_core::eval::HostValue::all(&[]))
        .map(|h| h.value)
        .unwrap_or_else(|e| panic!("`{ns}.Driver.go`: {e:?}"));
    assert!(matches!(v, anthill_core::eval::Value::Int(5)), "{v:?}");
    let text = load_errors_of(&program(
        "wicxr5bbr.narrowed",
        "operation join(a: Bag[T = Int64], b: Holder) -> Int64 =\n      match a\n        case bag(v) -> v + 1",
    ))
    .join("\n");
    assert!(text.contains("parameter 1 of the bound operation has type `Bag[T = Int64]`"), "{text}");
}
