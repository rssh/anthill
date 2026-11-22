//! WI-20261122-CXR5B, ninth step — WHO OWES A SPEC'S OPERATIONS: A WITNESS, READ BY DECISION 6
//! (`docs/design/spec-carrier-set.md`).
//!
//! `provider_owes_operations` asks a constructor-less provider to back a spec's operations only
//! where its provision is a WITNESS (`is_witness_provision`): its own provision may leave them to
//! its providers, as a sub-interface does. It read the witness at the spec's single carrier
//! parameter, the first declared that an operation takes, so over `Bag2 { put(c: C, x: T) }` a
//! constructor-less `MyBag provides Bag2[T = Int64, C = Self]` with no `put` was a witness at
//! `Int64` and refused "backs no operation" with `T` declared first, and its own provision,
//! loading, with `C` first. A provision is its provider's own where the provider heads its
//! carrier or one of its bindings (decision 6): `MyBag` heads `C`'s, in either order. A witness
//! is a provision that is not and binds another type; a forwarding of the provider's own
//! parameters stays a sub-interface.
//!
//! WHAT FAILS IF THIS IS BACKED OUT, and what passes either way, is said at each row. MEASURED
//! 2026-11-22, these rows kept: with `src/` at `7cb515b08`, the first fails and the two controls
//! pass.

use crate::common::{interp_for, load_errors_of};

/// `Bag2 { put(c: C, x: T) }` with `first` declared first, a provider `MyBag` (constructors
/// where `entity`) providing `Bag2[T = Int64, C = Self]` with no `put`, and `OtherBag`, which
/// writes one; `go` calls `put` on an `OtherBag`.
fn program(ns: &str, t_first: bool, entity: bool) -> String {
    let (a, b) = if t_first { ("T", "C") } else { ("C", "T") };
    let my_entity = if entity { "    entity bag\n" } else { "" };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Bag2
    sort {a} = ?
    sort {b} = ?
    operation put(c: C, x: T) -> Int64
  end
  sort MyBag
{my_entity}    provides Bag2[T = Int64, C = Self]
  end
  sort OtherBag
    entity obag
    provides Bag2[T = Int64, C = Self]
    operation put(c: OtherBag, x: Int64) -> Int64 = x + 100
  end
  sort Driver
    operation go() -> Int64 = Bag2.put(obag, 5)
  end
end
"#
    )
}

/// A constructor-less provider's OWN provision leaves `put` to its providers in either order,
/// and the program runs (105). FAILS backed out: with `T` declared first it was refused "backs no
/// operation".
#[test]
fn a_constructor_less_providers_own_provision_owes_nothing_in_either_order() {
    for (t_first, ns) in [(true, "wicxr5bwb.tfirst"), (false, "wicxr5bwb.cfirst")] {
        let src = program(ns, t_first, false);
        let v = interp_for(&src)
            .call(&format!("{ns}.Driver.go"), &anthill_core::eval::HostValue::all(&[]))
            .map(|h| h.value)
            .unwrap_or_else(|e| panic!("`{ns}.Driver.go`: {e:?}"));
        assert!(matches!(v, anthill_core::eval::Value::Int(105)), "{ns}: {v:?}");
    }
}

/// CONTROL: a provider WITH constructors owes the operation in either order, and is refused.
/// Passes either way, by design.
#[test]
fn a_provider_with_constructors_owes_it_in_either_order() {
    for (t_first, ns) in [(true, "wicxr5bwb.ctfirst"), (false, "wicxr5bwb.ccfirst")] {
        let text = load_errors_of(&program(ns, t_first, true)).join("\n");
        assert!(text.contains("backs no operation"), "{ns}:\n{text}");
    }
}

/// CONTROL: a constructor-less WITNESS — its provider heads no binding — still owes it: `Hi
/// provides MySpec[T = Int64]` over `ping() -> Int64` (`is_witness_provision`'s measured case).
/// Passes either way, by design.
#[test]
fn a_constructor_less_witness_still_owes_it() {
    let src = r#"
namespace wicxr5bwb.witness
  import anthill.prelude.{Int64}
  sort MySpec
    sort T = ?
    operation ping() -> Int64
  end
  sort Hi
    provides MySpec[T = Int64]
  end
end
"#;
    let text = load_errors_of(src).join("\n");
    assert!(text.contains("backs no operation"), "{text}");
}
