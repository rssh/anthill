//! WI-492 — transitive spec provision for the stream combinators.
//!
//! Originally written for the LAZY carriers (`MappedStream`/`FilteredStream`),
//! which `provides Stream` and derive Iterable-ness TRANSITIVELY (`Stream
//! provides Iterable`). POST-WI-588 (finiteness Phase B) the chains below now
//! resolve `.map`/`.filter` on a `List` to `FiniteCollection.map`/`filter` (List
//! provides FiniteCollection at provision-graph depth 1, beating Iterable at
//! depth 2), producing the FINITE carriers `FiniteMappedStream` /
//! `FiniteFilteredStream`. So these tests now exercise the SAME transitive-
//! provision machinery on the finite path: an op resolved on a finite combinator
//! value through its `FiniteStream → FiniteCollection` / `Stream → Iterable`
//! provision chain.
//!
//!   * `.filter(p).map(f)` — `.map` on a `FiniteFilteredStream` value resolves
//!     `FiniteCollection.map` (the carrier provides FiniteCollection directly).
//!   * `.map(f).size()`    — `.size` on a `FiniteMappedStream` value resolves
//!     `FiniteCollection.size` (the carrier's FiniteCollection provision).
//!
//! WI-599 (thin design): the combinators now provide `FiniteCollection` + `Iterable`
//! directly (not `FiniteStream`), and `.map`/`.filter` return `FiniteCollection`.
//! Iterable-ONLY members (`find`/`isEmpty`) resolve on that result via WI-614:
//! dot-dispatch traverses `FiniteCollection requires Iterable`, so `xs.map(f).find(p)`
//! / `xs.filter(p).isEmpty()` type-check and evaluate directly (no `collect`-to-`List`
//! materialization first — that was the pre-WI-614 workaround). The lazy
//! `mapped`/`filtered` carriers are still reached on a genuinely-infinite bare
//! `Stream`, where `FiniteCollection` does not apply.

use anthill_core::eval::Value;

fn expect_int(v: Value) -> i64 {
    v.as_int().unwrap_or_else(|| panic!("expected Int64, got {v:?}"))
}

const SRC: &str = r#"
namespace wi492.transitive
  import anthill.prelude.{List, Int64, Stream, Bool, Iterable}
  import anthill.prelude.List.{nil, cons, length}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.FiniteCollection.{collect, foldLeft}
  import anthill.prelude.Stream.{takeN}

  operation inc(n: Int64) -> Int64 = n + 1
  operation is_big(n: Int64) -> Bool = n > 2
  operation is_huge(n: Int64) -> Bool = n > 9
  operation addp(a: Int64, b: Int64) -> Int64 = a + b

  -- LAZY-carrier coverage (post-WI-588 the dot-dispatch chains above go FINITE,
  -- so the lazy MappedStream's transitive provision would otherwise be untested):
  -- a QUALIFIED `Iterable.map` forces the lazy `mapped` carrier (it returns a bare
  -- Stream), then a QUALIFIED `Iterable.iterator` resolves on that MappedStream
  -- value TRANSITIVELY (MappedStream → Stream → Iterable, the original WI-492 path —
  -- `iterator` is the very op WI-492 was written for). The produced bare Stream is
  -- maybe-infinite, so it is counted SOUNDLY by a BOUNDED `takeN` then `length` —
  -- the unsound eager `Iterable.size` consumer the test used here was removed in
  -- Phase C / WI-589. [1,2,3,4] -Iterable.map(+1)-> [2,3,4,5], counted -> 4.
  operation lazy_map_iterator_count(xs: List[T = Int64]) -> Int64 =
    length(takeN(Iterable.iterator(Iterable.map(xs, inc)), 1000))

  -- filter THEN map: `.filter` → FiniteCollection.filter (FiniteFilteredStream),
  -- then `.map` over that finite value resolves FiniteCollection.map transitively
  -- (FiniteFilteredStream → FiniteStream → FiniteCollection).
  -- [1,2,3,4] -filter(>2)-> [3,4] -map(+1)-> [4,5] -foldLeft sum-> 9.
  operation filter_then_map_sum(xs: List[T = Int64]) -> Int64 =
    foldLeft(xs.filter(is_big).map(inc), 0, addp)

  -- map THEN size: `.map` → FiniteCollection.map (FiniteMappedStream), then
  -- `.size` resolves FiniteCollection.size transitively (FiniteMappedStream →
  -- FiniteStream → FiniteCollection — List → FiniteStream → size).
  -- [1,2,3,4] -map(+1)-> [2,3,4,5], size = 4.
  operation map_then_size(xs: List[T = Int64]) -> Int64 =
    xs.map(inc).size()

  -- map THEN find (WI-614): the WI-599 thin `.map` returns a `FiniteCollection`
  -- (consume view). `find` is Iterable-ONLY, and `FiniteCollection requires
  -- Iterable`, so dot-dispatch resolves `.find` DIRECTLY on the FiniteCollection
  -- map-result by traversing the requires graph (no `collect`-to-`List` first —
  -- that workaround was WI-614's motivation). [1,2,3,4] -map(+1)-> [2,3,4,5], first > 2 is 3.
  operation map_then_find(xs: List[T = Int64]) -> Int64 =
    match xs.map(inc).find(is_big)
      case some(v) -> v
      case none() -> 0 - 1

  -- filter THEN isEmpty (WI-614): same requires-traversal — the thin `.filter`
  -- returns a `FiniteCollection`, and `isEmpty` is Iterable-only, reached via
  -- `FiniteCollection requires Iterable` without a `collect`-first materialization.
  -- [1,2,3,4] -filter(>9)-> [] empty.
  operation filter_then_is_empty(xs: List[T = Int64]) -> Bool =
    xs.filter(is_huge).isEmpty()

  operation mk_list() -> List[T = Int64] = [1, 2, 3, 4]
end
"#;

#[test]
fn filtered_stream_iterator_resolves_transitively() {
    let mut interp = crate::common::interp_for(SRC);
    let xs = interp.call("wi492.transitive.mk_list", &[]).expect("build list");
    let got = interp
        .call("wi492.transitive.filter_then_map_sum", &[xs])
        .unwrap_or_else(|e| panic!("call filter_then_map_sum: {e:?}"));
    assert_eq!(expect_int(got), 9);
}

#[test]
fn mapped_stream_iterator_resolves_transitively() {
    let mut interp = crate::common::interp_for(SRC);
    let xs = interp.call("wi492.transitive.mk_list", &[]).expect("build list");
    let got = interp
        .call("wi492.transitive.map_then_size", &[xs])
        .unwrap_or_else(|e| panic!("call map_then_size: {e:?}"));
    assert_eq!(expect_int(got), 4);
}

#[test]
fn iterable_find_on_mapped_stream_resolves_transitively() {
    let mut interp = crate::common::interp_for(SRC);
    let xs = interp.call("wi492.transitive.mk_list", &[]).expect("build list");
    let got = interp
        .call("wi492.transitive.map_then_find", &[xs])
        .unwrap_or_else(|e| panic!("call map_then_find: {e:?}"));
    assert_eq!(expect_int(got), 3);
}

#[test]
fn iterable_is_empty_on_filtered_stream_resolves_transitively() {
    let mut interp = crate::common::interp_for(SRC);
    let xs = interp.call("wi492.transitive.mk_list", &[]).expect("build list");
    let got = interp
        .call("wi492.transitive.filter_then_is_empty", &[xs])
        .unwrap_or_else(|e| panic!("call filter_then_is_empty: {e:?}"));
    assert_eq!(got.as_bool(), Some(true), "filtered-out stream is empty; got {got:?}");
}

/// The LAZY carrier's transitive provision (the original WI-492 path), preserved
/// after WI-588 routed the dot chains to the finite carriers: a qualified
/// `Iterable.map` yields a lazy `MappedStream`, and a qualified `Iterable.iterator`
/// on it resolves through MappedStream → Stream → Iterable — the canonical WI-492
/// op. The produced bare Stream is counted soundly by a bounded `takeN` + `length`
/// (the original eager `Iterable.size` consumer was removed in Phase C / WI-589 as
/// unsound on a maybe-infinite stream).
#[test]
fn iterable_iterator_on_lazy_mapped_stream_resolves_transitively() {
    let mut interp = crate::common::interp_for(SRC);
    let xs = interp.call("wi492.transitive.mk_list", &[]).expect("build list");
    let got = interp
        .call("wi492.transitive.lazy_map_iterator_count", &[xs])
        .unwrap_or_else(|e| panic!("call lazy_map_iterator_count: {e:?}"));
    assert_eq!(expect_int(got), 4, "a mapped 4-element list counts to 4");
}
