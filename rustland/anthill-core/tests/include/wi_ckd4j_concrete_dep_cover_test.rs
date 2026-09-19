//! WI-20260918-CKD4J (prerequisite, fixed inline) — an unrelated `requires` in scope
//! must not turn a CONCRETE dependency's failed construction into a WI-821 refusal.
//!
//! `gt(i, 0)` needs `PartialOrd[Int64]`, and through `PartialOrd`'s own chain
//! `PartialEq[Int64]`. On a stdlib loaded WITHOUT the stl host bindings `Int64`
//! provides neither, so that dependency cannot be constructed. With nothing in scope the
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
//! refusal quoted above. `with_nothing_in_scope_the_same_call_loads` passes either way
//! by design: it is the control showing what the verdict should agree with.

const SORT_LEVEL: &str = r#"
namespace wickd4j.cover.sortlevel
  import anthill.prelude.{Bool, Int64, PartialEq}
  import anthill.prelude.PartialOrd.{gt}
  sort Bag
    sort T = ?
    requires PartialEq[T]
    entity bag(v: T)
    operation pos(b: Bag, i: Int64) -> Bool = gt(i, 0)
  end
end
"#;

const CONDITIONAL: &str = r#"
namespace wickd4j.cover.conditional
  import anthill.prelude.{Bool, Int64, PartialEq}
  import anthill.prelude.PartialOrd.{gt}
  sort Bag
    sort T = ?
    entity bag(v: T)
    provides PartialEq[Bag] :- PartialEq[T]
    operation pos(b: Bag, i: Int64) -> Bool = gt(i, 0)
  end
end
"#;

const NOTHING_IN_SCOPE: &str = r#"
namespace wickd4j.cover.none
  import anthill.prelude.{Bool, Int64}
  import anthill.prelude.PartialOrd.{gt}
  sort Bag
    sort T = ?
    entity bag(v: T)
    operation pos(b: Bag, i: Int64) -> Bool = gt(i, 0)
  end
end
"#;

fn refusals(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with_stdlib_only(src)
        .err()
        .unwrap_or_default()
}

#[test]
fn with_nothing_in_scope_the_same_call_loads() {
    assert_eq!(refusals(NOTHING_IN_SCOPE), Vec::<String>::new());
}

#[test]
fn a_concrete_dep_is_not_blamed_on_an_unrelated_requires() {
    for (spelling, src) in [("sort-level", SORT_LEVEL), ("conditional", CONDITIONAL)] {
        assert_eq!(
            refusals(src),
            Vec::<String>::new(),
            "{spelling} `PartialEq[T]` in scope must not change the verdict on the \
             concrete `PartialEq[Int64]` dependency of `gt(i, 0)`"
        );
    }
}
