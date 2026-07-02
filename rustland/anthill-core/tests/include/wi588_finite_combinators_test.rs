//! WI-588 (finiteness Phase B, proposal library/003): finite-preserving
//! `map` / `filter` on `FiniteCollection`, returning a `FiniteStream`.
//!
//! UNLIKE `Iterable.map`/`filter` (→ lazy maybe-infinite `Stream`), the finite
//! versions return a `FiniteStream`, so a pipeline over a finite source stays
//! consumable: `xs.map(f).size()` keeps type-checking once the eager consumers
//! move off `Stream` (Phase C). They live on `FiniteCollection` so a finite-but-
//! NON-stream carrier — a `Map` — gets them too. The thin body wraps the finite
//! cursor (`finiteIterator`, the finite dual of `iterator`) in the finite carrier
//! (`fmapped`/`ffiltered`); the recursive carrier re-wrap is the WI-594 case.

use anthill_core::eval::{Interpreter, Value};

fn run_int(interp: &mut Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// Finite `map` / `filter` on a `List` EVAL via the finite carriers, and a
/// `map`-then-`filter` chain stays finite-and-consumable end to end.
#[test]
fn finite_map_filter_on_list_eval() {
    let src = r#"
namespace test.wi588.list
  import anthill.prelude.{List, Int64, Bool}
  import anthill.prelude.FiniteCollection.{map, filter, size, foldLeft}

  operation inc(n: Int64) -> Int64 = n + 1
  operation is_big(n: Int64) -> Bool = n > 2
  operation addp(a: Int64, b: Int64) -> Int64 = a + b

  -- map then size: [1,2,3,4] -map(+1)-> [2,3,4,5], size = 4 (size = length(collect(.)),
  -- so this also exercises `collect` on the finite mapped carrier).
  operation map_size() -> Int64 = size(map([1, 2, 3, 4], inc))
  -- filter then size: [1,2,3,4] -filter(>2)-> [3,4], size = 2
  operation filter_size() -> Int64 = size(filter([1, 2, 3, 4], is_big))
  -- map then foldLeft sum: [2,3,4,5] summed = 14 (eager consume of the finite carrier)
  operation map_sum() -> Int64 = foldLeft(map([1, 2, 3, 4], inc), 0, addp)
  -- filter THEN map THEN size: [1,2,3,4] -filter(>2)-> [3,4] -map(+1)-> [4,5], size = 2
  operation filter_map_size() -> Int64 = size(map(filter([1, 2, 3, 4], is_big), inc))
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi588.list.map_size"), 4);
    assert_eq!(run_int(&mut interp, "test.wi588.list.filter_size"), 2);
    assert_eq!(run_int(&mut interp, "test.wi588.list.map_sum"), 14);
    assert_eq!(run_int(&mut interp, "test.wi588.list.filter_map_size"), 2);
}

/// DISPATCH COHERENCE: `map` on a `List` resolves to `FiniteCollection.map`
/// (→ `FiniteStream`), NOT `Iterable.map` (→ lazy `Stream`). Pinned structurally:
/// `FiniteCollection.size` is imported and applied to `xs.map(inc)` — that only
/// type-checks if the map result PROVIDES `FiniteCollection` (i.e. is a
/// `FiniteStream`). A lazy `Stream` (Iterable.map's result) does not, so this
/// would fail to load if dispatch picked the lazy `map`. (List provides
/// FiniteCollection at provision-graph depth 1; Iterable is depth 2 via Stream.)
#[test]
fn finite_map_wins_dispatch_over_iterable_map() {
    let src = r#"
namespace test.wi588.coherence
  import anthill.prelude.{List, Int64}
  -- `size` is FiniteCollection's; `.map` is the dot-dispatched combinator.
  import anthill.prelude.FiniteCollection.{size}

  operation inc(n: Int64) -> Int64 = n + 1
  -- xs.map(inc) must be a FiniteStream for FiniteCollection.size to apply.
  operation map_then_size(xs: List[T = Int64]) -> Int64 = size(xs.map(inc))
  operation run() -> Int64 = map_then_size([10, 20, 30])
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi588.coherence.run"), 3);
}

/// `Map.map`/`.filter` exist AND are finite via the NATURAL dot form (the driving
/// requirement). A `Map` is finite but NOT a stream, so it provides `Iterable`
/// AND `FiniteCollection` at EQUAL provision-graph distance (both direct) — unlike
/// a `List`, where `Iterable` is farther (via `Stream`). The resolver's
/// requires-refinement tie-break (`FiniteCollection requires Iterable`, so it is
/// the more specific spec) picks the finite ops over the lazy `Iterable` ones.
/// Pinned STRUCTURALLY (WI-599 thin design): the dot result is consumed by
/// `.size()`, a FiniteCollection consumer — that only type-checks if `.filter`/
/// `.map` resolved to the finite ops (their `FiniteCollection` result provides it);
/// a lazy `Iterable` result (a bare `Stream`) does NOT provide FiniteCollection.
#[test]
fn map_dot_dispatch_map_filter_are_finite() {
    let src = r#"
namespace test.wi588.mapdot
  import anthill.prelude.{Map, Int64, Bool, Pair}

  operation keep(e: Pair[A = Int64, B = Int64]) -> Bool = true
  operation to_zero(e: Pair[A = Int64, B = Int64]) -> Int64 = 0

  -- dot-dispatch: the results must be finite (FiniteCollection), consumable by
  -- `.size()`; a lazy Iterable Stream result would not type-check under `.size()`.
  operation dot_filter(m: Map[K = Int64, V = Int64]) -> Int64 = m.filter(keep).size()
  operation dot_map(m: Map[K = Int64, V = Int64]) -> Int64 = m.map(to_zero).size()
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(errs.is_empty(),
        "Map.map/.filter via dot-dispatch must resolve to the finite FiniteCollection \
         ops (consumable by .size()) via the requires-refinement tie-break, not the \
         lazy Iterable ops (-> Stream):\n{}", errs.join("\n"));
}

/// `Map.filter`/`.map` via dot-dispatch EVALUATE finitely and the result is itself
/// consumable (`.size()`). Constant predicates/callbacks (Pair's `fst`/`snd` are
/// law-backed, not runnable in a lazy callback, so a content predicate can't eval
/// — cardinality/finiteness is what's tested here): filter keep-all -> 3,
/// drop-all -> 0; map (collapsing each entry to 0) -> 3.
#[test]
fn finite_map_filter_on_map_eval() {
    let src = r#"
namespace test.wi588.map
  import anthill.prelude.{Map, Int64, Bool, Pair}
  import anthill.prelude.Map.{empty, put}

  operation keep_all(e: Pair[A = Int64, B = Int64]) -> Bool = true
  operation drop_all(e: Pair[A = Int64, B = Int64]) -> Bool = false
  operation to_zero(e: Pair[A = Int64, B = Int64]) -> Int64 = 0

  operation m3() -> Map[K = Int64, V = Int64] =
    put(put(put(empty(), 1, 10), 2, 20), 3, 30)

  -- all dot-dispatch -> finite carriers; `.size()` consumes them.
  operation kept_size() -> Int64 = m3().filter(keep_all).size()
  operation dropped_size() -> Int64 = m3().filter(drop_all).size()
  operation mapped_size() -> Int64 = m3().map(to_zero).size()
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi588.map.kept_size"), 3);
    assert_eq!(run_int(&mut interp, "test.wi588.map.dropped_size"), 0);
    assert_eq!(run_int(&mut interp, "test.wi588.map.mapped_size"), 3);
}
