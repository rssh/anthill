//! WI-585 (finiteness Phase A, proposal library/003): `FiniteCollection` — the
//! eager consumers (`collect` / `size` / `foldLeft` / `foldRight`) on the
//! guaranteed-finite sort, where walking to the end is sound.
//!
//! ADDITIVE phase: `Stream` / `Iterable` still carry their consumers (removal is
//! Phase C / WI-589), so this only checks the NEW path. `List` and `Map` provide
//! `FiniteCollection`; `collect` is the finiteness primitive (List: identity;
//! Map: `entries`), and `size` / folds derive from it via `List`'s concrete ops.

use anthill_core::eval::{Interpreter, Value};

fn run_int(interp: &mut Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// `FiniteCollection.size` / `foldLeft` / `foldRight` / `collect` on a `List`
/// type-check pure and EVAL. Non-commutative subtraction separates the two fold
/// directions (and would catch a swapped tuple order): foldLeft ((0-1)-2)-3 = -6;
/// foldRight 1-(2-(3-0)) = 2.
#[test]
fn finite_collection_on_list_eval() {
    let src = r#"
namespace test.wi585.list
  import anthill.prelude.{List, Int64}
  import anthill.prelude.FiniteCollection.{size, foldLeft, foldRight, collect}

  operation addp(a: Int64, b: Int64) -> Int64 = a + b
  operation subt(a: Int64, b: Int64) -> Int64 = a - b

  operation size3() -> Int64 = size([1, 2, 3])
  operation size0() -> Int64 = size([])
  operation sum() -> Int64 = foldLeft([1, 2, 3, 4], 0, addp)
  operation foldl_sub() -> Int64 = foldLeft([1, 2, 3], 0, subt)
  operation foldr_sub() -> Int64 = foldRight([1, 2, 3], 0, subt)
  -- collect on a List is the identity; its length is the element count
  operation collect_len() -> Int64 = List.length(collect([1, 2, 3, 4, 5]))
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi585.list.size3"), 3);
    assert_eq!(run_int(&mut interp, "test.wi585.list.size0"), 0);
    assert_eq!(run_int(&mut interp, "test.wi585.list.sum"), 10);
    assert_eq!(run_int(&mut interp, "test.wi585.list.foldl_sub"), -6);
    assert_eq!(run_int(&mut interp, "test.wi585.list.foldr_sub"), 2);
    assert_eq!(run_int(&mut interp, "test.wi585.list.collect_len"), 5);
}

/// `FiniteCollection.size` on a `Map` (a finite, non-Stream carrier) EVALS via
/// the `Map provides FiniteCollection` (`collect = entries`) provision. `size`
/// works because its compound `Element` (`Pair[K, V]`) is consumed internally
/// (`length(collect(m))` → `Int64`). `collect` / `foldLeft` on a `Map`, where
/// the compound `Element` ESCAPES into the result / callback, await
/// compound-`Element` threading on a non-Stream provision (the WI-357 mechanism
/// covers Stream / simple elements only) — tracked as WI-593; until then the
/// typer demands a `requires FiniteCollection[Element = …]` it cannot ground.
#[test]
fn finite_collection_size_on_map_eval() {
    let src = r#"
namespace test.wi585.map
  import anthill.prelude.{Map, Int64}
  import anthill.prelude.Map.{empty, put}
  import anthill.prelude.FiniteCollection.{size}

  operation m3() -> Map[K = Int64, V = Int64] =
    put(put(put(empty(), 1, 10), 2, 20), 3, 30)

  operation msize() -> Int64 = size(m3())
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi585.map.msize"), 3);
}

/// `FiniteCollection`'s full consume-path (`collect` / `size` / `foldLeft` /
/// `foldRight`) on a NON-List, NON-Stream carrier with a CONCRETE element type.
/// `FiniteBag` wraps a `List[Int64]`, provides `Iterable` (required) with a
/// non-identity `iterator`, and provides `FiniteCollection` with `collect`
/// handing back the backing list. Concrete `Element = Int64`, so no element
/// threading is needed — this isolates the FiniteCollection machinery from the
/// compound-`Element` gap above. Non-commutative subtraction separates the folds.
#[test]
fn finite_collection_on_custom_carrier_eval() {
    let src = r#"
namespace test.wi585.bag
  import anthill.prelude.{List, Int64}
  import anthill.prelude.List.{nil, cons}
  import anthill.prelude.FiniteCollection.{size, foldLeft, foldRight, collect}

  sort FiniteBag
    import anthill.prelude.{List, Int64, Stream, Iterable, FiniteCollection}
    entity fbag(items: List[T = Int64])
    provides Iterable[C = FiniteBag, Element = Int64, E = {}]
    operation iterator(b: FiniteBag) -> Stream[T = Int64, E = {}] = b.items
    provides FiniteCollection[C = FiniteBag, Element = Int64, E = {}]
    operation collect(b: FiniteBag) -> List[T = Int64] = b.items
  end

  operation addp(a: Int64, b: Int64) -> Int64 = a + b
  operation subt(a: Int64, b: Int64) -> Int64 = a - b

  operation mk() -> FiniteBag = fbag(items: cons(head: 1, tail: cons(head: 2, tail: cons(head: 3, tail: nil))))

  operation bsize() -> Int64 = size(mk())
  operation bcollect_len() -> Int64 = List.length(collect(mk()))
  operation bsum() -> Int64 = foldLeft(mk(), 0, addp)
  operation bfoldl_sub() -> Int64 = foldLeft(mk(), 0, subt)
  operation bfoldr_sub() -> Int64 = foldRight(mk(), 0, subt)
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi585.bag.bsize"), 3);
    assert_eq!(run_int(&mut interp, "test.wi585.bag.bcollect_len"), 3);
    assert_eq!(run_int(&mut interp, "test.wi585.bag.bsum"), 6);
    assert_eq!(run_int(&mut interp, "test.wi585.bag.bfoldl_sub"), -6);
    assert_eq!(run_int(&mut interp, "test.wi585.bag.bfoldr_sub"), 2);
}
