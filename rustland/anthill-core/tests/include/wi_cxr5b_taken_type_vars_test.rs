//! WI-20261122-CXR5B, seventh step — A PROVISION BINDS EACH TYPE-VAR AN OPERATION OF ITS SPEC
//! TAKES A VALUE OF (decision 3 of `docs/design/spec-carrier-set.md`; the `?` spelling decided with
//! the user 2026-11-22).
//!
//! `check_provision_names_carrier` asked a written provision to bind ONE type-var, the parameter
//! dispatch reads (`spec_carrier_param`: the first declared that some operation takes). Over `Bag2
//! { put(c: C, x: T) }`, `MyBag provides Bag2[C = Self]` was refused "binds nothing at the carrier
//! parameter `T`" with `T` declared first, and with `C` first passed that check — refused only by
//! the member check where `put` took a narrower `x`, and LOADED where the member was generic over
//! it. Now every type-var some operation takes a value of (a parameter typed at it or at an
//! application it heads, `typing::spec_taken_type_vars`) must be bound, in either order. A `?`
//! written there binds nothing, as leaving it out does — a left-out parameter IS the `?` written
//! there (WI-20261003-GR5EN), and the two spellings have one verdict. A type-var only a result
//! mentions may still be left out.
//!
//! WHAT FAILS IF THIS IS BACKED OUT, and what passes either way, is said at each row. MEASURED
//! 2026-11-22, these rows kept: see each row.

use crate::common::{interp_for, load_errors_of};

/// `Bag2 { put(c: C, x: T) }` with `first` declared first, `MyBag` providing `Bag2[{binds}]`
/// with the member `put`.
fn bag2(ns: &str, t_first: bool, binds: &str, put: &str) -> String {
    let (a, b) = if t_first { ("T", "C") } else { ("C", "T") };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Bag2
    sort {a} = ?
    sort {b} = ?
    operation put(c: C, x: T) -> C
  end
  sort MyBag
    entity bag
    provides Bag2[{binds}]
    operation {put}
  end
end
"#
    )
}

/// The refusal, naming `T` and `put`, in either declaration order and either spelling, the member
/// generic over `T` included. FAILS backed out, at every case: the refusal named no operation;
/// with `C` declared first the clause passed this check, refused only by the member check for a
/// narrower `x` (the `Int64` member) and LOADED for a generic one; and `T = ?` written passed it
/// in both orders.
#[test]
fn every_type_var_an_operation_takes_is_bound_in_either_order() {
    for (t_first, order) in [(true, "tfirst"), (false, "cfirst")] {
        for (binds, spelling) in [("C = Self", "left"), ("C = Self, T = ?", "question")] {
            for (put, member) in [
                ("put(c: MyBag, x: Int64) -> MyBag = c", "int"),
                ("put[W](c: MyBag, x: W) -> MyBag = c", "generic"),
            ] {
                let ns = format!("wicxr5btv.{order}.{spelling}.{member}");
                let text = load_errors_of(&bag2(&ns, t_first, binds, put)).join("\n");
                for want in ["binds nothing at", "carrier parameter `T`", "Bag2.put` takes a value of"] {
                    assert!(text.contains(want), "`{ns}`: `{want}` missing:\n{text}");
                }
            }
        }
    }
}

/// CONTROL: the binding written, the provision loads and its member answers, in either order.
/// Passes either way, by design.
#[test]
fn the_type_var_written_is_the_repair() {
    for (t_first, order) in [(true, "tfirst"), (false, "cfirst")] {
        let ns = format!("wicxr5btv.written.{order}");
        let src = bag2(&ns, t_first, "C = Self, T = Int64", "put(c: MyBag, x: Int64) -> MyBag = c")
            .replace("end\nend\n", "end\n  sort Driver\n    operation go() -> Int64 =\n      let _ = Bag2.put(bag, 1)\n      7\n  end\nend\n");
        let v = interp_for(&src)
            .call(&format!("{ns}.Driver.go"), &anthill_core::eval::HostValue::all(&[]))
            .map(|h| h.value)
            .unwrap_or_else(|e| panic!("`{ns}.Driver.go`: {e:?}"));
        assert!(matches!(v, anthill_core::eval::Value::Int(7)), "{ns}: {v:?}");
    }
}

/// CONTROL: a type-var only a RESULT mentions may be left out — "takes a value of" is the
/// parameters, on purpose. Passes either way, by design.
#[test]
fn a_type_var_only_a_result_mentions_may_be_left_out() {
    let src = r#"
namespace wicxr5btv.result
  import anthill.prelude.{Int64}
  sort Mk
    sort C = ?
    sort T = ?
    operation mk(c: C) -> T
  end
  sort Foo
    entity foo
    provides Mk[C = Self]
    operation mk[W](c: Foo) -> W = mk(c)
  end
end
"#;
    let errs = load_errors_of(src);
    assert!(errs.is_empty(), "{errs:#?}");
}
