//! WI-20261122-CXR5B, tenth step — A CALL OF AN OPERATION THAT TAKES NO VALUE AT THE DISPATCH
//! PARAMETER (decision 1 of `docs/design/spec-carrier-set.md`), found by an order-swap sweep.
//!
//! The sweep ran every program of a grid — `Sp[A, B]` with its type-vars in both declaration
//! orders, operations taking both, one or neither of them, swapped; provisions own at either
//! type-var or a witness at another sort; members written or bound; calls qualified, through a
//! `requires`, at an expected type or a bracket — and compared each pair's verdict. One shape
//! differed: `Sp { op(c: A, x: B); get(c: A) -> B }`. `op` takes both, so the spec's single
//! carrier parameter is the one declared FIRST; with `B` first, `get(c: A)` takes no value there,
//! and its argument, which fixes `A`, was read as fixing no carrier: the witness lookup and the
//! provisions a call chooses among (`provision_binds_param_to_carrier`, `provisions_at_carrier`)
//! accepted a witness only by its binding at that parameter. So `Sp.get(foo)` beside `W provides
//! Sp[A = Foo, B = Int64]` answered 6 with `A` first and was refused "missing `requires Sp`" with
//! `B` first. Now an operation that takes no value at the dispatch parameter has a witness read at
//! the type-var it does take (`WitnessRead::AtAskedParam`); a call taking a value there reads as
//! before.
//!
//! WHAT FAILS IF THIS IS BACKED OUT, and what passes either way, is said at each row. MEASURED
//! 2026-11-22, these rows kept: see each row.

use crate::common::{interp_for, load_errors_of};

/// `Sp[A, B]` (in `order`), `Foo`, the providers `provs` and a driver whose `go` is `body`.
fn program(ns: &str, b_first: bool, provs: &str, body: &str) -> String {
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
{provs}
  sort Driver
    operation go() -> Int64 = {body}
  end
end
"#
    )
}

const OWN_AND_WITNESS: &str = r#"  sort P
    entity p
    provides Sp[A = Self, B = Int64]
    operation op(c: P, x: Int64) -> Int64 = 1
    operation get(c: P) -> Int64 = 5
  end
  sort W
    provides Sp[A = Foo, B = Int64]
    operation op(c: Foo, x: Int64) -> Int64 = 2
    operation get(c: Foo) -> Int64 = 6
  end"#;

const TWO_WITNESSES_B_APART: &str = r#"  sort W1
    provides Sp[A = Foo, B = Int64]
    operation op(c: Foo, x: Int64) -> Int64 = 1
    operation get(c: Foo) -> Int64 = 5
  end
  sort W2
    provides Sp[A = Foo, B = String]
    operation op(c: Foo, x: String) -> Int64 = 2
    operation get(c: Foo) -> String = "s"
  end"#;

fn go(src: &str, ns: &str) -> i64 {
    match interp_for(src)
        .call(&format!("{ns}.Driver.go"), &anthill_core::eval::HostValue::all(&[]))
        .map(|h| h.value)
        .unwrap_or_else(|e| panic!("`{ns}.Driver.go`: {e:?}"))
    {
        anthill_core::eval::Value::Int(n) => n,
        other => panic!("`{ns}.Driver.go` answered no Int64: {other:?}"),
    }
}

/// The witness at `A = Foo` answers `get(foo)` in either order. FAILS backed out: with `B`
/// declared first, refused "missing `requires Sp`".
#[test]
fn a_witness_answers_an_operation_taking_no_value_at_the_dispatch_parameter() {
    for (b_first, ns) in [(false, "wicxr5bos.own.afirst"), (true, "wicxr5bos.own.bfirst")] {
        assert_eq!(go(&program(ns, b_first, OWN_AND_WITNESS, "Sp.get(foo) + 0"), ns), 6, "{ns}");
    }
}

/// Two witnesses at `A = Foo` that bind `B` apart: the type expected at the call and a bracket
/// each select one, and a call fixing neither is refused for leaving `B` open — in either order.
/// FAILS backed out: with `B` first every call was refused "missing `requires Sp`"; with only
/// the selection's half backed out (`provisions_at_carrier`), `Sp.get(foo)` answered `W1`'s 5.
#[test]
fn two_witnesses_at_the_type_var_the_call_fixes_are_told_apart_in_either_order() {
    for (b_first, order) in [(false, "afirst"), (true, "bfirst")] {
        let ns = format!("wicxr5bos.two.{order}.str");
        assert_eq!(go(&program(&ns, b_first, TWO_WITNESSES_B_APART, "String.length(Sp.get(foo))"), &ns), 1);
        let ns = format!("wicxr5bos.two.{order}.bracket");
        assert_eq!(go(&program(&ns, b_first, TWO_WITNESSES_B_APART, "String.length(Sp.get[Sp = W2](foo))"), &ns), 1);
        let ns = format!("wicxr5bos.two.{order}.open");
        let text = load_errors_of(&program(&ns, b_first, TWO_WITNESSES_B_APART, "Sp.get(foo) + 0")).join("\n");
        assert!(text.contains("leaves `B` open"), "`{ns}`:\n{text}");
    }
}

/// CONTROL: a call taking a value at the dispatch parameter classifies as it did — `op(foo, 1)`
/// on the witness, in either order. Passes either way, by design.
#[test]
fn a_call_taking_a_value_at_the_dispatch_parameter_reads_as_before() {
    for (b_first, ns) in [(false, "wicxr5bos.op.afirst"), (true, "wicxr5bos.op.bfirst")] {
        assert_eq!(go(&program(ns, b_first, OWN_AND_WITNESS, "Sp.op(foo, 1)"), ns), 2, "{ns}");
    }
}
