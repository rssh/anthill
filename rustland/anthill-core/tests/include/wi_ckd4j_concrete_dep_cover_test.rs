//! WI-20260918-CKD4J (prerequisite, fixed inline) — an unrelated `requires` in scope
//! must not turn a CONCRETE dependency's failed construction into a WI-821 refusal.
//!
//! `gt(i, i)` over an `Opaque` operand needs `PartialOrd[Opaque]`, and through
//! `PartialOrd`'s own chain `PartialEq[Opaque]`. `Opaque` provides neither, so that
//! dependency cannot be constructed. (The fixture used `Int64` and relied on a stdlib
//! loaded WITHOUT the stl host bindings, where `Int64` provides neither; WI-20260922-BRT4Y
//! made that load a refusal. Under the full closure `Int64` provides both, so the
//! dependency constructs and there is no refusal for the guard below to decide — a sort
//! that provides nothing in ANY closure keeps the rows measuring. Re-measured on the
//! `Opaque` fixture: the back-out below fails the row as stated.) With nothing in scope the
//! call loads (the verdict belongs to the arms after the σ-refusal one). With a
//! `requires PartialEq[T]` in scope — sort-level, or a conditional provision's
//! `:- PartialEq[T]` — `explain_dep_refusal` counted that entry as a "σ-refused cover"
//! and refused the call, blaming it: "the enclosing scope's `requires PartialEq[T =
//! …Bag.T]` covers only as a wildcard and is not forwarded — its element is a different
//! type parameter under this call". The element is `Int64`, not a type parameter, and a
//! wildcard is never forwarded to a concrete dep, so the entry is not why the dep failed.
//!
//! MEASURED as the blocker for CKD4J's conditional rows: hand-writing
//! `provides PartialEq[List] :- PartialEq[T]` made `List.nth`'s `gt(i, 0)` this refusal
//! and failed 55 stl-less unit tests.
//!
//! ── WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT ──────────────────────────────
//!
//! Removing the `dep_is_concrete` guard in `explain_dep_refusal` fails
//! `a_concrete_dep_is_not_blamed_on_an_unrelated_requires` on BOTH fixtures with the
//! refusal quoted above. `with_nothing_in_scope_the_same_call_is_refused` passes either way
//! by design: it is the control showing what the verdict should agree with. Since
//! WI-20260909-SM910 that verdict is a refusal — `gt` at `Opaque` is the carrier's member,
//! refused for want of an order whatever is in scope — and that row fails with
//! `PartialOrd.gt` registered as a builtin again (the call loads).

const SORT_LEVEL: &str = r#"
namespace wickd4j.cover.sortlevel
  import anthill.prelude.{Bool, Int64, PartialEq}
  import anthill.prelude.PartialOrd.{gt}
  sort Opaque
  end
  sort Bag
    sort T = ?
    requires PartialEq[T]
    entity bag(v: T)
    operation pos(b: Self, i: Opaque) -> Bool = gt(i, i)
  end
end
"#;

const CONDITIONAL: &str = r#"
namespace wickd4j.cover.conditional
  import anthill.prelude.{Bool, Int64, PartialEq}
  import anthill.prelude.PartialOrd.{gt}
  sort Opaque
  end
  sort Bag
    sort T = ?
    entity bag(v: T)
    provides PartialEq[Self] :- PartialEq[T]
    operation pos(b: Self, i: Opaque) -> Bool = gt(i, i)
  end
end
"#;

const NOTHING_IN_SCOPE: &str = r#"
namespace wickd4j.cover.none
  import anthill.prelude.{Bool, Int64}
  import anthill.prelude.PartialOrd.{gt}
  sort Opaque
  end
  sort Bag
    sort T = ?
    entity bag(v: T)
    operation pos(b: Self, i: Opaque) -> Bool = gt(i, i)
  end
end
"#;

fn refusals(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default()
}

/// `src`'s refusals with each fixture's namespace and the location dropped, so the three
/// fixtures' verdicts compare.
fn verdict(src: &str, ns: &str) -> Vec<String> {
    refusals(src)
        .iter()
        .map(|e| {
            let text = e.split_once(": ").map_or(e.as_str(), |(_, t)| t);
            text.replace(ns, "NS")
        })
        .collect()
}

/// Since WI-20260909-SM910 the call is refused with nothing in scope: `gt` at `Opaque` is the
/// carrier's member, and `Opaque` provides no order (`PartialOrd`'s `PartialEq[Opaque]`,
/// and the `WeakOrd[Opaque]` its body requires). Until then it loaded, as a builtin
/// answered structurally.
#[test]
fn with_nothing_in_scope_the_same_call_is_refused() {
    let got = verdict(NOTHING_IN_SCOPE, "wickd4j.cover.none");
    assert!(
        got.iter().any(|e| e.contains("`anthill.prelude.PartialEq[T = NS.Opaque]` of `anthill.prelude.PartialOrd` cannot be supplied")),
        "{got:#?}"
    );
}

#[test]
fn a_concrete_dep_is_not_blamed_on_an_unrelated_requires() {
    let none = verdict(NOTHING_IN_SCOPE, "wickd4j.cover.none");
    for (spelling, src, ns) in [
        ("sort-level", SORT_LEVEL, "wickd4j.cover.sortlevel"),
        ("conditional", CONDITIONAL, "wickd4j.cover.conditional"),
    ] {
        assert_eq!(
            verdict(src, ns),
            none,
            "{spelling} `PartialEq[T]` in scope must not change the verdict on the \
             concrete `PartialEq[Opaque]` dependency of `gt(i, i)`"
        );
    }
}
