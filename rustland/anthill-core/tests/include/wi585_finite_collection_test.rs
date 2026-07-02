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

/// `FiniteCollection`'s full consume path on a `Map` — a finite, NON-Stream
/// carrier whose `Element` is COMPOUND (`Pair[K, V]`). `size` consumes the element
/// internally (`length(collect(m))` → `Int64`); `collect` ESCAPES it into the
/// result (`List[Pair[K, V]]`) and `foldLeft` / `foldRight` into the callback param
/// (`e: Pair[K, V]`). WI-593 grounds that compound `Element` from the concrete
/// `Map[K = Int64, V = Int64]` receiver — threading `K`/`V` through the provision's
/// `Element = Pair[A = K, B = V]` (rebuilt from its `reflect.SortView` wrapper into
/// the plain `Pair[A = Int64, B = Int64]` the callback/result are written against) —
/// so all of these type-check and EVAL with NO explicit type args. Before WI-593
/// only `size` worked; `collect` / `foldLeft` raised `MissingRequiresForSpecOp`
/// (the compound `Element` could not be grounded, so the test would not even load).
/// The count callbacks keep EVAL off the law-backed `Pair.fst`/`snd` (orthogonal
/// to the grounding); `foldRight`'s callback takes `(x: Element, acc: Acc)`.
#[test]
fn finite_collection_on_map_eval() {
    let src = r#"
namespace test.wi585.map
  import anthill.prelude.{Map, List, Int64, Pair}
  import anthill.prelude.Map.{empty, put}
  import anthill.prelude.FiniteCollection.{size, collect, foldLeft, foldRight}

  operation m3() -> Map[K = Int64, V = Int64] =
    put(put(put(empty(), 1, 10), 2, 20), 3, 30)

  operation count_l(acc: Int64, e: Pair[A = Int64, B = Int64]) -> Int64 = acc + 1
  operation count_r(e: Pair[A = Int64, B = Int64], acc: Int64) -> Int64 = acc + 1

  operation msize() -> Int64 = size(m3())
  operation mcollect_len() -> Int64 = List.length(collect(m3()))
  operation mfoldl_count() -> Int64 = foldLeft(m3(), 0, count_l)
  operation mfoldr_count() -> Int64 = foldRight(m3(), 0, count_r)
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi585.map.msize"), 3);
    assert_eq!(run_int(&mut interp, "test.wi585.map.mcollect_len"), 3);
    assert_eq!(run_int(&mut interp, "test.wi585.map.mfoldl_count"), 3);
    assert_eq!(run_int(&mut interp, "test.wi585.map.mfoldr_count"), 3);
}

/// SOUNDNESS anchor for WI-593: the compound `Element` grounds to the CONCRETE
/// `Pair[Int64, Int64]` (threading the Map's `K` / `V`), NOT an erased `?_`. A
/// `foldLeft` callback whose element param is `Pair[A = String, B = Bool]` (wrong
/// `K` / `V`) must be REJECTED — were `Element` erased to a free var it would unify
/// with any callback element type and load clean. This is meaningful only because
/// grounding now SUCCEEDS *before* the callback is checked (pre-WI-593 the call
/// failed to load on the Element-grounding error itself, a different reason). The
/// positive test above confirms the well-typed callback grounds; this confirms a
/// MISMATCHED one is still caught, pinning the grounding to the right `Pair[K, V]`.
#[test]
fn finite_collection_map_wrong_element_callback_rejected() {
    let src = r#"
namespace test.wi585.map_unsound
  import anthill.prelude.{Map, Int64, String, Bool, Pair}
  import anthill.prelude.Map.{empty, put}
  import anthill.prelude.FiniteCollection.{foldLeft}

  operation m1() -> Map[K = Int64, V = Int64] = put(empty(), 1, 10)
  -- WRONG: the Map's element is `Pair[Int64, Int64]`, not `Pair[String, Bool]`.
  operation bad_cb(acc: Int64, e: Pair[A = String, B = Bool]) -> Int64 = acc + 1
  operation oops() -> Int64 = foldLeft(m1(), 0, bad_cb)
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        !errs.is_empty(),
        "a foldLeft callback with element Pair[String, Bool] (≠ the Map's \
         Pair[Int64, Int64]) must be rejected — proving WI-593 grounds Element to \
         the concrete compound, not an erased ?_; loaded clean instead",
    );
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
    import anthill.prelude.{List, Int64, Stream, FiniteStream, Iterable, FiniteCollection}
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
