//! WI-495 — a GENUINE non-Stream Iterable.
//!
//! Every Iterable in the prelude used to also be a Stream (List, the lazy
//! combinators), so the Iterable≠Stream split was never exercised by a carrier
//! that is Iterable WITHOUT being a Stream. This pins that case for real:
//!
//!   * `Bag` (a concrete test carrier) wraps a `List` but is NOT a Stream — it
//!     has no `splitFirst`. It `provides Iterable` EXPLICITLY with a NON-identity
//!     `iterator` that materializes its elements as a `List` (which provides
//!     Stream, so it is admissible as the produced Stream). The inherited
//!     `Iterable.size/isEmpty/find` then EVALUATE on a `Bag` value, end to end.
//!   * stdlib `Map` is the real-world instance of the same shape (it produces a
//!     Stream of entries via `iterator(m) = entries(m)`); since `Map` is abstract
//!     we pin it at the TYPE level — `Iterable.size` on a `Map` type-checks.
//!
//! Contrast with WI-492/WI-495's Stream carriers: those derive Iterable
//! TRANSITIVELY through Stream with an identity iterator. `Bag`/`Map` show the
//! split carries its weight — a non-Stream carrier provides Iterable directly.

use anthill_core::eval::Value;

fn expect_int(v: Value) -> i64 {
    v.as_int().unwrap_or_else(|| panic!("expected Int64, got {v:?}"))
}

const EVAL_SRC: &str = r#"
namespace wi495.nonstream
  import anthill.prelude.{List, Int64, Bool, Pair, Stream, Iterable, Option}
  import anthill.prelude.List.{nil, cons}
  import anthill.prelude.Iterable.{size, isEmpty, find}

  -- A concrete non-Stream Iterable: a bag of Int64s backed by a List, but NOT
  -- itself a Stream (no `splitFirst`). Provides Iterable directly, with a
  -- NON-identity iterator that hands back the backing List (which IS a Stream).
  -- Concrete element type (Int64), so the iterator return needs no element
  -- threading — the point here is the Iterable≠Stream split, not parametric
  -- field projection.
  sort IntBag
    import anthill.prelude.{List, Int64, Stream, Iterable}
    entity ibag(items: List[T = Int64])
    provides Iterable[C = IntBag, Element = Int64, E = {}]
    operation iterator(b: IntBag) -> Stream[T = Int64, E = {}] = b.items
  end

  operation big(n: Int64) -> Bool = n > 1

  operation mk() -> IntBag =
    ibag(items: cons(head: 1, tail: cons(head: 2, tail: cons(head: 3, tail: nil))))

  operation mk_empty() -> IntBag = ibag(items: nil)

  -- Iterable.size on a non-Stream carrier (walks the produced stream).
  operation bag_size(b: IntBag) -> Int64 = size(b)

  -- Iterable.isEmpty on a non-Stream carrier.
  operation bag_is_empty(b: IntBag) -> Bool = isEmpty(b)

  -- Iterable.find on a non-Stream carrier; unwrap the Option.
  operation bag_find_big(b: IntBag) -> Int64 =
    match find(b, big)
      case some(v) -> v
      case none() -> 0 - 1
end
"#;

#[test]
fn non_stream_iterable_size_evaluates() {
    let mut interp = crate::common::interp_for(EVAL_SRC);
    let b = interp.call("wi495.nonstream.mk", &[]).expect("build bag");
    let got = interp
        .call("wi495.nonstream.bag_size", &[b])
        .unwrap_or_else(|e| panic!("call bag_size: {e:?}"));
    assert_eq!(expect_int(got), 3);
}

#[test]
fn non_stream_iterable_is_empty_evaluates() {
    let mut interp = crate::common::interp_for(EVAL_SRC);
    let full = interp.call("wi495.nonstream.mk", &[]).expect("build bag");
    let empty = interp.call("wi495.nonstream.mk_empty", &[]).expect("build empty bag");
    let got_full = interp
        .call("wi495.nonstream.bag_is_empty", &[full])
        .unwrap_or_else(|e| panic!("call bag_is_empty(full): {e:?}"));
    let got_empty = interp
        .call("wi495.nonstream.bag_is_empty", &[empty])
        .unwrap_or_else(|e| panic!("call bag_is_empty(empty): {e:?}"));
    assert_eq!(got_full.as_bool(), Some(false), "non-empty bag");
    assert_eq!(got_empty.as_bool(), Some(true), "empty bag");
}

#[test]
fn non_stream_iterable_find_evaluates() {
    let mut interp = crate::common::interp_for(EVAL_SRC);
    let b = interp.call("wi495.nonstream.mk", &[]).expect("build bag");
    let got = interp
        .call("wi495.nonstream.bag_find_big", &[b])
        .unwrap_or_else(|e| panic!("call bag_find_big: {e:?}"));
    assert_eq!(expect_int(got), 2, "first element > 1 is 2");
}

// ── Map: the stdlib non-Stream Iterable, pinned at the type level ────────

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver, LoadError};
use anthill_core::parse;

fn load_errs(extra: &str) -> Vec<LoadError> {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).err().unwrap_or_default()
}

#[test]
fn map_iterable_members_typecheck() {
    // `Map` provides Iterable but NOT Stream (it has no splitFirst). An
    // `Iterable.size` over a `Map` must type-check — dispatched on the Map's
    // direct Iterable provision, grounding the access effect to pure `{}`.
    let src = r#"
namespace wi495.map_iter
  import anthill.prelude.{Map, Int64}
  import anthill.prelude.Iterable.{size}

  operation entry_count(m: Map[K = Int64, V = Int64]) -> Int64 = size(m)
end
"#;
    let errs = load_errs(src);
    assert!(
        errs.is_empty(),
        "Iterable.size on a Map (non-Stream Iterable) must type-check; got: {}",
        errs.iter().map(|e| e.to_string()).collect::<Vec<_>>().join("\n"),
    );
}
