//! WI-492 — transitive spec provision for the lazy stream combinators.
//!
//! `MappedStream` / `FilteredStream` no longer declare an explicit `provides
//! Iterable` + identity `iterator`. They `provides Stream`, and `Stream
//! provides Iterable` (stream.anthill), so the engine derives their
//! Iterable-ness TRANSITIVELY: a value-directed `iterator(c)` on a `mapped(…)`
//! / `filtered(…)` value resolves through the intermediate `Stream` carrier
//! (whose `iterator(s) = s` is the genuine impl) instead of dying
//! `UnknownOperation{iterator}`.
//!
//! The WI-278 chain `xs.map(f).filter(p)` never calls `iterator` on a lazy
//! carrier (its `.filter` runs `Iterable.filter`'s default body, and the final
//! `collect` consumes via `splitFirst`). These tests force the path the old
//! explicit declarations existed for: an Iterable op AFTER a lazy combinator,
//! whose default body calls `iterator(c)` on the lazy value.
//!
//!   * `.filter(p).map(f)` — `Iterable.map`'s `mapped(iterator(c), f)` calls
//!     `iterator` on a `FilteredStream` value.
//!   * `.map(f).size()`    — `Iterable.size`'s `Stream.count(iterator(c))`
//!     calls `iterator` on a `MappedStream` value.

use anthill_core::eval::Value;

fn expect_int(v: Value) -> i64 {
    v.as_int().unwrap_or_else(|| panic!("expected Int64, got {v:?}"))
}

const SRC: &str = r#"
namespace wi492.transitive
  import anthill.prelude.{List, Int64, Stream, Bool}
  import anthill.prelude.List.{nil, cons}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Stream.{collect, foldLeft}

  operation inc(n: Int64) -> Int64 = n + 1
  operation is_big(n: Int64) -> Bool = n > 2
  operation is_huge(n: Int64) -> Bool = n > 9
  operation addp(a: Int64, b: Int64) -> Int64 = a + b

  -- filter THEN map: `.map` over a FilteredStream value runs Iterable.map's
  -- default body `mapped(iterator(c), inc)`, calling `iterator` on the
  -- FilteredStream — resolved via transitive provision (FilteredStream → Stream).
  -- [1,2,3,4] -filter(>2)-> [3,4] -map(+1)-> [4,5] -foldLeft sum-> 9.
  operation filter_then_map_sum(xs: List[T = Int64]) -> Int64 =
    foldLeft(xs.filter(is_big).map(inc), 0, addp)

  -- map THEN size: `.size` over a MappedStream value runs Iterable.size's
  -- default body `Stream.count(iterator(c))`, calling `iterator` on the
  -- MappedStream — resolved via transitive provision (MappedStream → Stream).
  -- [1,2,3,4] -map(+1)-> [2,3,4,5], size = 4.
  operation map_then_size(xs: List[T = Int64]) -> Int64 =
    xs.map(inc).size()

  -- map THEN find: `.find` over a MappedStream value runs Iterable.find's
  -- default body `Stream.find(iterator(c), pred)`. [1,2,3,4] -map(+1)-> [2,3,4,5],
  -- first > 2 is 3.
  operation map_then_find(xs: List[T = Int64]) -> Int64 =
    match xs.map(inc).find(is_big)
      case some(v) -> v
      case none() -> 0 - 1

  -- filter THEN isEmpty: `.isEmpty` over a FilteredStream value runs
  -- Iterable.isEmpty's `Stream.isEmpty(iterator(c))`. [1,2,3,4] -filter(>9)-> []
  -- is empty.
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
