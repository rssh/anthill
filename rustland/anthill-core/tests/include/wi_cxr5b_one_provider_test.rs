//! WI-20261122-CXR5B, third step — ONE PROVIDER AND SEVERAL ARE HELD ALIKE (decision 1 of
//! `docs/design/spec-carrier-set.md`, its d5; decision 7 for a self-representing spec).
//!
//! A provider's provisions of a spec were grouped by their binding of the spec's single
//! carrier parameter, at three places: the suppliers of an operation a dictionary of the
//! provider answers (`spec_op_suppliers_of_provider`, with the application a resolved instance
//! is for, `tree_application`), the coherence grouping's instance facts, and the agreement of
//! the bindings (`check_provision_binding_agreement`). So a witness writing `Coll[C = Foo, Elem
//! = Int64, first = f1]` beside `Coll[C = Foo, Elem = String, first = f2]` — two carriers, which
//! a call tells apart by what it fixes, as it tells two witnesses apart (b5–b8) — was refused at
//! load three times: a supplier tie at `Foo`, two ambiguous instance facts, and `Elem` and
//! `first` "bound two ways". Now each reads the provision's binding of EVERY type-var
//! (`typing::SpecApplication`), and a self-representing spec is one application per provider.
//!
//! WHAT FAILS IF THIS IS BACKED OUT, and what passes either way, is said at each row.
//! MEASURED 2026-11-22, these rows kept: with `src/` at `757d23229`, 5 of the 6 fail (the
//! last at its binding form) and the own-provision control passes. Backed out one part at a time: the supplier grouping
//! (`provision.rs`, `call_class.rs`) fails the first two rows; the instance-fact verdict alone
//! fails those two and d14; the agreement's buckets alone fail those two and decision 7's; the
//! named-provider half alone (`named_stands`) fails the second row only.
//!
//! NOT HERE: a provider's OWN provisions of a spec with a dictionary that agree where the
//! provider heads a binding and bind another type-var apart stay refused at load, since the readers of a value's sort's one view of a spec take the
//! first (`provider_spec_view_bindings`; the P readers, a later step), and the control row below
//! pins that.

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

/// d5: `Coll { first(c: C) -> Elem }` and ONE witness `WB` writing both of b5's provisions, the
/// `String` one first where `string_first`, and `driver`.
fn one_witness_two_provisions(ns: &str, string_first: bool, driver: &str) -> String {
    let int = "    provides Coll[C = Foo, Elem = Int64, first = WB.f1]\n";
    let string = "    provides Coll[C = Foo, Elem = String, first = WB.f2]\n";
    let (a, b) = if string_first { (string, int) } else { (int, string) };
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
  sort WB
{a}{b}    operation f1(c: Foo) -> Int64 = 1
    operation f2(c: Foo) -> String = "two"
  end
  sort Driver
{driver}
  end
end
"#
    )
}

/// d5 → b5–b8's answers. What the call fixes selects the provision: the type expected at the
/// call, or a receiver bracket, in either order the provisions are written. FAILS backed out:
/// the program is refused at load, "ambiguous dispatch of `Coll.first` on carrier `Foo`: 2
/// implementations", "2 distinct instance facts provide `Coll` for carrier `WB`" and
/// "conflicting provisions … binding `Elem`" (and `first`). Each of the three moved is
/// load-bearing: with any one of them alone backed out the load still refuses.
#[test]
fn one_witness_writing_two_provisions_answers_what_the_call_fixes() {
    let driver = "    operation int() -> Int64 = Coll.first(foo)\n    \
                  operation str() -> String = Coll.first(foo)\n    \
                  operation bracketed() -> String = Coll[Elem = String].first(foo)";
    for (ns, string_first) in [("wicxr5bo.intfirst", false), ("wicxr5bo.strfirst", true)] {
        let src = one_witness_two_provisions(ns, string_first, driver);
        assert_eq!(call(&src, ns, "int"), Value::Int(1), "{ns}");
        assert_eq!(call(&src, ns, "str"), Value::Str("two".into()), "{ns}");
        assert_eq!(call(&src, ns, "bracketed"), Value::Str("two".into()), "{ns}");
    }
}

/// d5 with nothing fixing `Elem` (b8's call), and with the bracket naming `WB`, whose own two
/// provisions give `Elem` different types: refused AT THE CALL, naming `Elem` and `WB`, with the
/// repair, which runs. FAILS backed out: the refusals are the load's three, and none names the
/// call's `Elem`; with only the named-provider half backed out (`select_provision_at_carrier`'s
/// `named_stands`), the bracketed call runs the provision written first.
#[test]
fn a_call_leaving_the_disagreed_type_var_free_is_refused_at_the_call() {
    for (ns, body) in [
        ("wicxr5bo.free", "    operation go() -> Int64 =\n      let x = Coll.first(foo)\n      0"),
        ("wicxr5bo.named", "    operation go() -> Int64 =\n      let x = Coll.first[Coll = WB](foo)\n      0"),
    ] {
        let text = load_errors_of(&one_witness_two_provisions(ns, false, body)).join("\n");
        for want in ["leaves `Elem` open", "WB` provides", "more than once", "[Elem = …]"] {
            assert!(text.contains(want), "`{ns}`: `{want}` missing:\n{text}");
        }
    }
    let repaired = one_witness_two_provisions(
        "wicxr5bo.repaired",
        false,
        "    operation go() -> Int64 = Coll.first[Elem = Int64](foo)",
    );
    assert_eq!(call(&repaired, "wicxr5bo.repaired", "go"), Value::Int(1));
}

/// d14: one witness binding a spec's operation at two sorts of a one-type-var spec — two
/// carriers, two dictionaries. FAILS backed out: refused at load, "2 distinct instance facts
/// provide `Tag` for carrier `WT`".
#[test]
fn one_witness_binding_an_operation_at_two_sorts_answers_at_each() {
    let src = r#"
namespace wicxr5bo.twosorts
  import anthill.prelude.{Int64}
  sort Tag
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort Foo
    entity foo
  end
  sort Bar
    entity bar
  end
  sort WT
    provides Tag[T = Foo, tag = WT.tagFoo]
    provides Tag[T = Bar, tag = WT.tagBar]
    operation tagFoo(x: Foo) -> Int64 = 1
    operation tagBar(x: Bar) -> Int64 = 20
  end
  sort Driver
    operation go() -> Int64 = Tag.tag(foo) + Tag.tag(bar)
  end
end
"#;
    assert_eq!(call(src, "wicxr5bo.twosorts", "go"), Value::Int(21));
}

/// Decision 7 (e3/e5): one provider of a SELF-REPRESENTING spec writing two provisions that bind
/// a type-var apart is one carrier with two readings of `Self.C`, refused at load, and the
/// refusal names `C`. Refused either way, by design; the conflict naming `C` FAILS backed out,
/// where the provisions were bucketed by their binding at `C` and only the instance facts'
/// ambiguity was reported.
#[test]
fn one_provider_of_a_self_representing_spec_binding_a_type_var_apart_is_refused() {
    let src = r#"
namespace wicxr5bo.selfrep
  import anthill.prelude.{Int64}
  sort Holder
    sort C = ?
    operation peek(c: C) -> Int64
    operation joinTwo(a: Self, b: Self) -> Int64
  end
  sort Box
    entity box(n: Int64)
  end
  sort Crate
    entity crate(n: Int64)
  end
  sort TwoHolder
    provides Holder[C = Box, peek = TwoHolder.peekBox, joinTwo = TwoHolder.join]
    provides Holder[C = Crate, peek = TwoHolder.peekCrate, joinTwo = TwoHolder.join]
    operation peekBox(c: Box) -> Int64 = 2
    operation peekCrate(c: Crate) -> Int64 = 7
    operation join(a: Holder, b: Holder) -> Int64 = 3
  end
end
"#;
    let text = load_errors_of(src).join("\n");
    for want in ["conflicting provisions", "binding 'C' to 2", "Box", "Crate"] {
        assert!(text.contains(want), "`{want}` missing:\n{text}");
    }
}

/// CONTROL: a provider's OWN provisions of a spec with a dictionary (`Foo` heads `C = Self`)
/// that bind `Elem` apart stay refused at load, by name, in either order — the readers of `Foo`'s
/// one view of `Coll` would take the first. Passes either way, by design.
#[test]
fn own_provisions_binding_a_type_var_apart_stay_refused() {
    for (ns, a, b) in [("wicxr5bo.own.int", "Int64", "String"), ("wicxr5bo.own.str", "String", "Int64")] {
        let src = format!(
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
    provides Coll[C = Self, Elem = {a}]
    provides Coll[C = Self, Elem = {b}]
  end
end
"#
        );
        let text = load_errors_of(&src).join("\n");
        for want in ["conflicting provisions", "binding 'Elem' to 2"] {
            assert!(text.contains(want), "`{ns}`: `{want}` missing:\n{text}");
        }
    }
}

/// A provider's own provisions it heads APART are two carriers, kept apart: `Box` provides
/// `Show` for itself at `Box[E = Int64]` and at `Box[E = String]`, by its own member (2 = 1 +
/// 1) and by two operation bindings (21). FOUND BY /code-review: a first cut put every own
/// provision of a provider in one bucket and refused the member form, which the bucket at the
/// first type-var admitted; the binding form was refused before this step as two ambiguous
/// instance facts. The member form passes either way, by design (a guard); the binding form
/// FAILS backed out.
#[test]
fn own_provisions_the_provider_heads_apart_are_two_carriers() {
    for (ns, bindings, members, answer) in [
        (
            "wicxr5bo.headed.member",
            ["", ""],
            "    operation show(x: Box) -> Int64 = 1\n",
            2,
        ),
        (
            "wicxr5bo.headed.bound",
            [", show = Box.si", ", show = Box.ss"],
            "    operation si(x: Box[E = Int64]) -> Int64 = 1\n    \
             operation ss(x: Box[E = String]) -> Int64 = 20\n",
            21,
        ),
    ] {
        let src = format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Show
    sort T = ?
    operation show(x: T) -> Int64
  end
  sort Box
    sort E = ?
    entity box(e: E)
    provides Show[T = Box[E = Int64]{b0}]
    provides Show[T = Box[E = String]{b1}]
{members}  end
  sort Driver
    operation go() -> Int64 = Show.show(box(e: 5)) + Show.show(box(e: "a"))
  end
end
"#,
            b0 = bindings[0],
            b1 = bindings[1],
        );
        assert_eq!(call(&src, ns, "go"), Value::Int(answer), "{ns}");
    }
}
