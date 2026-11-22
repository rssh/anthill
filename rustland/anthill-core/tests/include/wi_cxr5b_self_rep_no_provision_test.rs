//! WI-20261122-CXR5B, sixth step — A SELF-REPRESENTING SPEC'S CALL AT A TYPE-VAR NOTHING PROVIDES
//! (e7 of `docs/design/spec-carrier-set.md`).
//!
//! `Holder` takes a `Self` value (`joinTwo(a: Self, …)`), so its provisions are at their
//! providers (decision 8), and `peek(c: C)` is `peek(c: Self.C)`. A call with no `Self` value
//! names no provider: `Holder.peek(crate(n: 5))` fixes `C = Crate` by its argument, and with
//! nothing providing `Holder` at `C = Crate` it reached the dispatch with no candidate and no
//! carrier — the receiver's classification found no provision there, and the checks after it ask
//! a carrier at the spec's single parameter. It loaded clean and died at run, "operation has no
//! body: `Holder.peek`", where a spec with a dictionary refuses the same call at load. By
//! decision 1 the call reads what it leaves free off the provisions at what it fixes; with none
//! there, it is refused at load (`NoProvisionAtCarriers`, `typing::a_provision_meets_fixed`).
//!
//! Only for a spec something provides: a sort nothing provides answers through no provision,
//! and its own body-less operations are symbolic algebra left as data. A first cut without that
//! gate refused `Set.empty[T = Int64]()` in six suites (`wi880_reflect_mapping_test`,
//! `wi939_contains_rename_test` ×2, `wi_4xxsd_fold_host_arg_value_test`,
//! `wi_cbrd2_unrunnable_call_test`, `wi_vpewk_host_op_operand_test`), which are its guard.
//!
//! WHAT FAILS IF THIS IS BACKED OUT, and what passes either way, is said at each row. MEASURED
//! 2026-11-22, these rows kept: with `src/` at `dc607734e`, the first fails and the control
//! passes.

use crate::common::{interp_for, load_errors_of};

/// e4's `Holder`, `Box`, `Crate` and `Bag` (at `C = Box`), and a driver whose `go` is `body`.
fn program(ns: &str, body: &str) -> String {
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
  sort Crate
    entity crate(n: Int64)
  end
  sort Bag
    entity bag(n: Int64)
    provides Holder[C = Box, Element = Int64]
    operation peek(c: Box) -> Int64 = 2
    operation joinTwo(a: Bag, b: Holder) -> Int64 = 3
  end
  sort Driver
    operation go() -> Int64 = {body}
  end
end
"#
    )
}

/// e7: refused at load, naming the binding nothing provides and the provision that would. FAILS
/// backed out: the program loads, and `go` dies at run, "operation has no body".
#[test]
fn a_call_at_a_type_var_nothing_provides_is_refused_at_load() {
    let text = load_errors_of(&program("wicxr5bnp.atcrate", "Holder.peek(crate(n: 5))")).join("\n");
    for want in ["Holder.peek", "no provision of", "binds `C = ", "Crate"] {
        assert!(text.contains(want), "`{want}` missing:\n{text}");
    }
}

/// CONTROL, e4: the calls at `C = Box`, where `Bag` provides, answer 32. Passes either way, by
/// design.
#[test]
fn a_call_at_a_type_var_a_provision_binds_still_answers() {
    let ns = "wicxr5bnp.atbox";
    let src = program(ns, "Holder.joinTwo(bag(n: 1), bag(n: 2)) * 10 + Holder.peek(box(n: 5))");
    let v = interp_for(&src)
        .call(&format!("{ns}.Driver.go"), &anthill_core::eval::HostValue::all(&[]))
        .map(|h| h.value)
        .unwrap_or_else(|e| panic!("`{ns}.Driver.go`: {e:?}"));
    assert!(matches!(v, anthill_core::eval::Value::Int(32)), "{v:?}");
}
