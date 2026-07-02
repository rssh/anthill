//! WI-614 — dot-dispatch resolves an Iterable-ONLY member (`find` / `isEmpty` /
//! `iterator`) on a receiver whose static type is `FiniteCollection[…]` (the thin
//! WI-599 `.map`/`.filter` result) by traversing the receiver spec's `requires`
//! graph. `FiniteCollection requires Iterable[C=C, Element=Element, E=E]`, so a
//! `FiniteCollection` IS walkable and those members are sound on it.
//!
//! Before WI-614 dot-dispatch searched only the receiver spec's OWN members and its
//! PROVIDED specs — never the specs it REQUIRES — so `xs.map(f).find(p)` failed with
//! `FiniteCollection.find: no such member (dot dispatch)`, forcing a `collect`-to-
//! `List`-first workaround (the pre-WI-614 shape of the wi492 tests). The fix adds a
//! `requires`-graph member-resolution fallback (`find_spec_op_for_required_sort`),
//! gated on an abstract-spec receiver (`carrier_is_abstract_spec`); grounding of the
//! synthesized `Iterable.find(receiver, …)` then rides the WI-608 carrier-param
//! requires-view. These are EVAL tests — the direct form must both type-check and
//! evaluate, exercising the requires resolution AND the eval-side value-dispatch on
//! the concrete combinator carrier.

use anthill_core::eval::Value;

fn expect_int(v: Value) -> i64 {
    v.as_int().unwrap_or_else(|| panic!("expected Int64, got {v:?}"))
}

const SRC: &str = r#"
namespace wi614.requires_dispatch
  import anthill.prelude.{List, Int64, Bool, Stream}
  import anthill.prelude.List.{length}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Stream.{takeN}

  operation inc(n: Int64) -> Int64 = n + 1
  operation is_big(n: Int64) -> Bool = n > 2
  operation is_huge(n: Int64) -> Bool = n > 9

  -- `.find` on the FiniteCollection map-result — `Iterable.find` via `requires
  -- Iterable`, no `collect`-to-`List` first. [1,2,3,4] -map(+1)-> [2,3,4,5], first > 2 is 3.
  operation map_then_find(xs: List[T = Int64]) -> Int64 =
    match xs.map(inc).find(is_big)
      case some(v) -> v
      case none() -> 0 - 1

  -- `.isEmpty` on the FiniteCollection filter-result — `Iterable.isEmpty` via requires.
  -- [1,2,3,4] -filter(>9)-> [] empty.
  operation filter_then_is_empty(xs: List[T = Int64]) -> Bool =
    xs.filter(is_huge).isEmpty()

  -- `.iterator` on the FiniteCollection map-result — `Iterable.iterator` via requires.
  -- Produces a Stream; counted soundly by a bounded `takeN` + `length`.
  -- [1,2,3,4] -map(+1)-> [2,3,4,5], walked -> 4.
  operation map_then_iterator_count(xs: List[T = Int64]) -> Int64 =
    length(takeN(xs.map(inc).iterator(), 1000))

  -- CONTROL: `.isEmpty()` on a CONCRETE `List` resolves via the PROVIDES chain
  -- (List -> Stream -> Iterable), NOT the requires fallback — the requires arm is
  -- gated on an abstract-spec receiver and a `List` has constructors. [] is empty.
  operation list_is_empty(xs: List[T = Int64]) -> Bool =
    xs.isEmpty()

  operation mk_list() -> List[T = Int64] = [1, 2, 3, 4]
  operation mk_empty() -> List[T = Int64] = []
end
"#;

/// `find` (Iterable-only) resolves on the `FiniteCollection` map-result via requires.
#[test]
fn find_on_finite_collection_map_result() {
    let mut interp = crate::common::interp_for(SRC);
    let xs = interp
        .call("wi614.requires_dispatch.mk_list", &[])
        .expect("build list");
    let got = interp
        .call("wi614.requires_dispatch.map_then_find", &[xs])
        .unwrap_or_else(|e| panic!("call map_then_find: {e:?}"));
    assert_eq!(expect_int(got), 3);
}

/// `isEmpty` (Iterable-only) resolves on the `FiniteCollection` filter-result.
#[test]
fn is_empty_on_finite_collection_filter_result() {
    let mut interp = crate::common::interp_for(SRC);
    let xs = interp
        .call("wi614.requires_dispatch.mk_list", &[])
        .expect("build list");
    let got = interp
        .call("wi614.requires_dispatch.filter_then_is_empty", &[xs])
        .unwrap_or_else(|e| panic!("call filter_then_is_empty: {e:?}"));
    assert_eq!(
        got.as_bool(),
        Some(true),
        "filtered-out result is empty; got {got:?}"
    );
}

/// `iterator` (Iterable-only, the requires-lent walk primitive) resolves on the
/// `FiniteCollection` map-result and produces a walkable Stream.
#[test]
fn iterator_on_finite_collection_map_result() {
    let mut interp = crate::common::interp_for(SRC);
    let xs = interp
        .call("wi614.requires_dispatch.mk_list", &[])
        .expect("build list");
    let got = interp
        .call("wi614.requires_dispatch.map_then_iterator_count", &[xs])
        .unwrap_or_else(|e| panic!("call map_then_iterator_count: {e:?}"));
    assert_eq!(
        expect_int(got),
        4,
        "a mapped 4-element finite collection walks to 4"
    );
}

/// CONTROL: `.isEmpty()` on a concrete `List` still resolves through the PROVIDES
/// chain (List -> Stream -> Iterable), independent of the requires fallback — locks
/// the coverage the wi492 collect-first-drop would otherwise have removed.
#[test]
fn is_empty_on_concrete_list_via_provides() {
    let mut interp = crate::common::interp_for(SRC);
    let empty = interp
        .call("wi614.requires_dispatch.mk_empty", &[])
        .expect("build empty list");
    let got = interp
        .call("wi614.requires_dispatch.list_is_empty", &[empty])
        .unwrap_or_else(|e| panic!("call list_is_empty(empty): {e:?}"));
    assert_eq!(got.as_bool(), Some(true), "[] is empty; got {got:?}");
    let full = interp
        .call("wi614.requires_dispatch.mk_list", &[])
        .expect("build list");
    let got2 = interp
        .call("wi614.requires_dispatch.list_is_empty", &[full])
        .unwrap_or_else(|e| panic!("call list_is_empty(full): {e:?}"));
    assert_eq!(got2.as_bool(), Some(false), "[1,2,3,4] is non-empty; got {got2:?}");
}

/// GATE: the requires fallback must not OVER-accept. A member on NO spec the
/// receiver owns / provides / requires still fails dot-dispatch loudly — `sizzle`
/// exists nowhere, so `.sizzle()` on a `FiniteCollection` map-result is an error.
#[test]
fn unknown_member_on_finite_collection_still_errors() {
    let src = r#"
namespace wi614.gate
  import anthill.prelude.{List, Int64}
  operation inc(n: Int64) -> Int64 = n + 1
  operation bad(xs: List[T = Int64]) -> Int64 = xs.map(inc).sizzle()
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.iter()
            .any(|e| e.contains("sizzle") || e.contains("dot dispatch")),
        "an unknown member on a FiniteCollection map-result must still fail \
         dot-dispatch; got: {errs:?}"
    );
}

/// CARRIER-PRESERVATION (soundness): a CONSTRAINT-STYLE `requires` over an ELEMENT
/// must NOT lend its members to the whole collection. `Widget` is self-representing
/// (`combine(a: Widget, …)`) and `requires Eq[T]` over its element; `HashWidget
/// provides Widget` opens the abstract-spec gate. Without the carrier-preservation
/// guard, `w.eq(x)` would mis-resolve to `Eq.eq(widget, x)` — passing a Widget where
/// an element is expected. The guard rejects the edge ⟹ a clean dot-dispatch error.
#[test]
fn constraint_style_requires_member_not_borrowable() {
    let src = r#"
namespace wi614.carrier_guard
  import anthill.prelude.{Int64, Bool, Eq}

  sort Widget
    sort T = ?
    requires Eq[T]
    operation combine(a: Widget, b: Widget) -> Widget
  end

  sort HashWidget
    entity hw(x: Int64)
    provides Widget[T = Int64]
    operation combine(a: HashWidget, b: HashWidget) -> HashWidget = a
  end

  operation try_eq(w: Widget[T = Int64], x: Widget[T = Int64]) -> Bool = w.eq(x)
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.iter()
            .any(|e| e.contains("eq") && e.contains("dot dispatch")),
        "a constraint-style `requires Eq[T]` over the element must NOT lend `.eq` to \
         the collection value (carrier-preservation); expected a dot-dispatch error \
         on `eq`, got: {errs:?}"
    );
}
