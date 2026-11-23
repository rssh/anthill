//! WI-20261122-CXR5B, second step — WHAT A CALL FIXES SELECTS ITS PROVISION (decision 1 of
//! `docs/design/spec-carrier-set.md`, with §5.4's two approved amendments), on the typed call
//! path.
//!
//! A call of a body-less spec operation over a carrier parameter read the type-vars it left
//! free off the FIRST provision at the receiver's carrier, in declaration order
//! (`carrier_param_receiver` → the late ground bind), before the type expected at the call was
//! read; a bracket naming a provider was read only at the spec's single carrier parameter; and
//! a spec with no type-var answered a pinned call with the spec itself. Now:
//!
//! - where several provisions stand at the receiver's carrier, the call chooses among them by
//!   the provider its bracket names, by what its arguments and a receiver bracket fixed, and by
//!   the type expected at the call (`typing::select_provision_at_carrier`); where those leave a
//!   type-var the standing provisions give different types, the call is refused
//!   (`ParameterNamedApart`) and the instance is written at the call;
//! - a bracket naming a provider fixes every type-var that provider's provisions write one
//!   ground type for (`bind_carrier_the_witness_says`), and the pinned goal of a spec with no
//!   type-var is read at the pin (`resolve_inner`);
//! - for a self-representing spec, the type expected at a result typed `Self` fixes the
//!   provider, and types the result.
//!
//! WHAT FAILS IF THIS IS BACKED OUT, and what passes either way, is said at each row.
//! MEASURED 2026-11-22 with `src/` at the step-1 tree (`7425f192a`) and these rows kept: 7 of
//! the 8 fail, and the d8 control passes, by design.
//!
//! NOT HERE: one provider writing two provisions (d5, refused at load by three checks), a
//! bracket naming a provider with constructors (c3, g4: §5.4's concrete-provider rule), and the
//! untyped eval path (`carrier_param_receiver_for_values`). Later steps of the ticket.

use crate::common::{interp_for, load_errors_of};

/// What a driver answers, comparably.
#[derive(Debug, PartialEq)]
enum Value {
    Int(i64),
    Str(String),
}

/// What `{ns}.Driver.{op}()` answers.
fn call(src: &str, ns: &str, op: &str) -> Value {
    let v = interp_for(src)
        .call(&format!("{ns}.Driver.{op}"), &anthill_core::eval::HostValue::all(&[]))
        .map(|h| h.value)
        .unwrap_or_else(|e| panic!("`{ns}.Driver.{op}`: {e:?}"));
    match v {
        anthill_core::eval::Value::Int(n) => Value::Int(n),
        anthill_core::eval::Value::Str(s) => Value::Str(s),
        other => panic!("`{ns}.Driver.{op}` answered neither an Int64 nor a String: {other:?}"),
    }
}

/// `Coll { first(c: C) -> Elem }`, `W1` at `Coll[C = Foo, Elem = Int64]` answering 1 and `W2`
/// at `Coll[C = Foo, Elem = String]` answering "two", declared in the order given, and `driver`.
fn coll(ns: &str, w2_first: bool, driver: &str) -> String {
    let w1 = "  sort W1\n    provides Coll[C = Foo, Elem = Int64]\n    \
              operation first(c: Foo) -> Int64 = 1\n  end\n";
    let w2 = "  sort W2\n    provides Coll[C = Foo, Elem = String]\n    \
              operation first(c: Foo) -> String = \"two\"\n  end\n";
    let (a, b) = if w2_first { (w2, w1) } else { (w1, w2) };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Coll
    sort C = ?
    sort Elem = ?
    operation first(c: C) -> Elem
  end
  sort Foo
    entity foo
  end
{a}{b}  sort Driver
{driver}
  end
end
"#
    )
}

/// b5–b7. The type expected at the call selects the witness whose `Elem` it is, in either
/// declaration order. Before: the first-declared witness answered — 1 with `W1` first, and with
/// `W2` first the `Int64` call refused "expected Int64, got String"; the `String` call refused
/// "expected String, got Int64" with `W1` first. FAILS backed out (three of the four).
#[test]
fn the_type_expected_at_the_call_selects_the_witness() {
    let driver = "    operation int() -> Int64 = Coll.first(foo)\n    \
                  operation str() -> String = Coll.first(foo)";
    for (ns, w2_first) in [("wicxr5bc.w1first", false), ("wicxr5bc.w2first", true)] {
        let src = coll(ns, w2_first, driver);
        assert_eq!(call(&src, ns, "int"), Value::Int(1), "{ns}");
        assert_eq!(call(&src, ns, "str"), Value::Str("two".into()), "{ns}");
    }
}

/// b8. Nothing fixes `Elem`, and the witnesses at `C = Foo` give it two types: refused, naming
/// both and the bracket to write. Both spellings of the repair answer. Before: it ran with the
/// first-declared witness's `Elem`. FAILS backed out (the refusal; the repairs pass either way).
#[test]
fn a_call_leaving_a_disagreed_type_var_free_is_refused_until_it_writes_it() {
    let ns = "wicxr5bc.open";
    let errs = load_errors_of(&coll(ns, false, "    operation any() -> Int64 =\n      let x = Coll.first(foo)\n      0"));
    assert!(
        errs.iter().any(|e| e.contains("it leaves `Elem` open")
            && e.contains("W1")
            && e.contains("W2")
            && e.contains("Coll[Elem = …].first(…)")),
        "{errs:#?}"
    );
    let src = coll(
        ns,
        false,
        "    operation int() -> Int64 =\n      let x = Coll[Elem = Int64].first(foo)\n      x\n    \
         operation str() -> String =\n      let x = Coll.first[Elem = String](foo)\n      x",
    );
    assert_eq!(call(&src, ns, "int"), Value::Int(1));
    assert_eq!(call(&src, ns, "str"), Value::Str("two".into()));
}

/// d7. A bracket naming the witness selects it, with the other declared first. Before: refused,
/// "W1 provides Coll, but not at the bindings this call needs" — the bindings read off `W2`.
/// FAILS backed out.
///
/// And where the type expected at the call contradicts the named witness — `W2`, at `Elem =
/// String`, in a call expected at `Int64` — the expected type still fixes `Elem`, and the
/// selection is refused AT THE CALL, naming it. Read off `W2` instead, it was refused at the
/// caller's return (MEASURED while this was written). FAILS backed out with `W2` declared
/// first, where the first witness read was `W2`.
#[test]
fn a_bracket_naming_the_witness_selects_it() {
    let ns = "wicxr5bc.named";
    let src = coll(ns, true, "    operation int() -> Int64 =\n      let x = Coll.first[Coll = W1](foo)\n      x");
    assert_eq!(call(&src, ns, "int"), Value::Int(1));
    let errs = load_errors_of(&coll("wicxr5bc.namedwrong", true, "    operation int() -> Int64 = Coll.first[Coll = W2](foo)"));
    assert!(
        errs.iter().any(|e| e.contains("Coll.first.selection") && e.contains("not at the bindings this call")),
        "{errs:#?}"
    );
}

/// d8, the control: ONE provision at `C = Foo`, nothing fixing `Elem` — read off it, as
/// `Iterable.find(xs)` reads `Element` off `List`'s. Passes either way, by design.
#[test]
fn one_provision_at_the_carrier_still_gives_what_the_call_leaves_free() {
    let ns = "wicxr5bc.one";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Coll
    sort C = ?
    sort Elem = ?
    operation first(c: C) -> Elem
  end
  sort Foo
    entity foo
  end
  sort W1
    provides Coll[C = Foo, Elem = Int64]
    operation first(c: Foo) -> Int64 = 1
  end
  sort Driver
    operation int() -> Int64 =
      let x = Coll.first(foo)
      x
  end
end
"#
    );
    assert_eq!(call(&src, ns, "int"), Value::Int(1));
}

/// d11. A bracket naming the provider fixes its provision: `Dflt.dflt[Dflt = W1]()` over
/// `dflt() -> T`, nothing expected, is at `W1`'s `Dflt[T = Int64]`. Before: refused, "no impl
/// matches" — `T` was read only at the spec's single carrier parameter, which `Dflt` has none
/// of. FAILS backed out.
#[test]
fn a_bracket_naming_the_provider_fixes_what_its_provision_writes() {
    let ns = "wicxr5bc.dflt";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Dflt
    sort T = ?
    operation dflt() -> T
  end
  sort W1
    provides Dflt[T = Int64]
    operation dflt() -> Int64 = 1
  end
  sort Driver
    operation int() -> Int64 =
      let x = Dflt.dflt[Dflt = W1]()
      x
  end
end
"#
    );
    assert_eq!(call(&src, ns, "int"), Value::Int(1));
}

/// d12/d13. A spec with no type-var is fixed by a bracket naming its provider: 7. Before: the
/// program loaded and failed at run, "operation has no body: Greeter.greet" — the pinned goal
/// was answered by the spec itself. Without the bracket (d13) it is refused at load, either way.
/// The first assertion FAILS backed out; the second passes either way, by design.
#[test]
fn a_spec_with_no_type_var_is_fixed_by_naming_its_provider() {
    let program = |ns: &str, call: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Greeter
    operation greet() -> Int64
  end
  sort W1
    provides Greeter
    operation greet() -> Int64 = 7
  end
  sort Driver
    operation int() -> Int64 = {call}
  end
end
"#
        )
    };
    let ns = "wicxr5bc.greet";
    assert_eq!(call(&program(ns, "Greeter.greet[Greeter = W1]()"), ns, "int"), Value::Int(7));
    let errs = load_errors_of(&program("wicxr5bc.greetbare", "Greeter.greet()"));
    assert!(errs.iter().any(|e| e.contains("nothing can run")), "{errs:#?}");
}

/// g6. A self-representing spec's call with no `Self` value: the type expected at its `Self`
/// result fixes the provider, and is the result's type — `let o: Ones = Src.make[T = Int64]()`
/// is `Ones`'s, and `Twos`'s at `Twos`. An expected type that provides nothing fixes nothing,
/// and the call stays the tie it was. Before: both refused as a tie of `Ones` and `Twos`. The
/// first two FAIL backed out; the third passes either way, by design.
#[test]
fn the_type_expected_at_a_self_result_fixes_the_provider() {
    let program = |ns: &str, annotated: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Src
    sort T = ?
    operation next(s: Self) -> Int64
    operation make() -> Self
  end
  sort Ones
    sort T = ?
    entity ones
    provides Src[T = T]
    operation next(s: Ones) -> Int64 = 1
    operation make() -> Self = ones
  end
  sort Twos
    sort T = ?
    entity twos
    provides Src[T = T]
    operation next(s: Twos) -> Int64 = 2
    operation make() -> Self = twos
  end
  sort Driver
    operation int() -> Int64 =
      let o: {annotated} = Src.make[T = Int64]()
      Src.next(o)
  end
end
"#
        )
    };
    assert_eq!(call(&program("wicxr5bc.ones", "Ones"), "wicxr5bc.ones", "int"), Value::Int(1));
    assert_eq!(call(&program("wicxr5bc.twos", "Twos"), "wicxr5bc.twos", "int"), Value::Int(2));
    let errs = load_errors_of(&program("wicxr5bc.neither", "Int64"));
    assert!(errs.iter().any(|e| e.contains("ambiguous dispatch") && e.contains("Src.make")), "{errs:#?}");
    // What the call fixed holds at the provider (`Src.T` is `Ones.T`): an expected type that
    // agrees is taken, and one that contradicts the bracket is refused at the call's return
    // rather than adopted as the result's type (found by review: adopted, it loaded clean).
    assert_eq!(call(&program("wicxr5bc.agrees", "Ones[T = Int64]"), "wicxr5bc.agrees", "int"), Value::Int(1));
    let errs = load_errors_of(&program("wicxr5bc.contradicts", "Ones[T = String]"));
    assert!(
        errs.iter().any(|e| e.contains("make.return") && e.contains("expected Ones[T = String], got Src[T = Int64]")),
        "{errs:#?}"
    );
}
