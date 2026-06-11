//! WI-424: `find` / `map` lifted onto `Iterable` (the shared read interface),
//! deriving via `iterator(c)` — every Iterable carrier (List, Stream, a future
//! non-Stream carrier) gets them, instead of reaching them only through
//! List-provides-Stream.
//!
//! The abstract member bodies (`Stream.find(iterator(c), pred)` /
//! `mapped(iterator(c), f)`) exercise the abstract-carrier iterator-walk: the
//! sibling `iterator(c)` must thread Iterable's own `Element` / `E` into the
//! produced Stream. The concrete call sites ground `Element`/`E` through the
//! written provisions (`provides Iterable[C = List[T], Element = T, E = {}]`,
//! `provides Iterable[C = Stream, Element = T, E = E]`).

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Call a nullary op and expect an Int result.
fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

pub(crate) fn load_errors(extras: &[&str]) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    for ex in extras {
        parsed.push(parse::parse(ex).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// The stdlib itself (with the Iterable members + written provisions) loads
/// clean — the abstract bodies typecheck.
#[test]
fn stdlib_with_iterable_members_loads_clean() {
    let errs = load_errors(&[]);
    assert!(
        errs.is_empty(),
        "stdlib with Iterable.find/map must load clean; got: {errs:?}",
    );
}

/// `Iterable.find` on a List (via List-provides-Iterable) typechecks PURE and
/// threads the element: the result is `Option[T = Int64]`.
#[test]
fn iterable_find_on_list_typechecks_pure() {
    let src = r#"
namespace test.wi424.find_list
  import anthill.prelude.{List, Int64, Option, Bool}
  import anthill.prelude.Iterable.{find}
  operation is_big(n: Int64) -> Bool = n > 2
  operation first_big(xs: List[T = Int64]) -> Option[T = Int64] = find(xs, is_big)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "Iterable.find on a List must typecheck pure with Option[Int64]; got: {errs:?}",
    );
}

/// The element really threads: claiming the find result is `Option[String]`
/// is REJECTED.
#[test]
fn iterable_find_on_list_wrong_element_rejected() {
    let src = r#"
namespace test.wi424.find_wrong
  import anthill.prelude.{List, Int64, String, Option, Bool}
  import anthill.prelude.Iterable.{find}
  operation is_big(n: Int64) -> Bool = n > 2
  operation first_big(xs: List[T = Int64]) -> Option[T = String] = find(xs, is_big)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "find on List[Int64] is Option[Int64]; returning Option[String] must be rejected",
    );
}

/// `Iterable.map` on a List typechecks: the produced stream collects back to
/// `List[Int64]` in a pure op.
#[test]
fn iterable_map_on_list_typechecks_pure() {
    let src = r#"
namespace test.wi424.map_list
  import anthill.prelude.{List, Int64}
  import anthill.prelude.Iterable.{map}
  import anthill.prelude.Stream.{collect}
  operation inc(n: Int64) -> Int64 = n + 1
  operation bump(xs: List[T = Int64]) -> List[T = Int64] = collect(map[Dst = Int64](xs, inc))
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "collect(Iterable.map(xs, inc)) must typecheck pure as List[Int64]; got: {errs:?}",
    );
}

/// `Iterable.isEmpty` on a List typechecks PURE (List's access row is `{}`)
/// and evaluates: one `splitFirst` step of the produced iterator.
#[test]
fn iterable_is_empty_on_list() {
    let src = r#"
namespace test.wi424.isempty_list
  import anthill.prelude.{List, Int64, Bool}
  import anthill.prelude.Iterable.{isEmpty}

  operation check(xs: List[T = Int64]) -> Bool = isEmpty(xs)
  operation on_empty() -> Int64 = if check([]) then 1 else 0
  operation on_full() -> Int64 = if check([1, 2]) then 1 else 0
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi424.isempty_list.on_empty"), 1);
    assert_eq!(run_int(&mut interp, "test.wi424.isempty_list.on_full"), 0);
}

/// A NON-Stream Iterable carrier: `BoxColl` provides Iterable (with its own
/// `iterator` unwrapping to a List) but does NOT provide Stream — so
/// `find`/`map` reach it ONLY through the Iterable members, never through
/// List-provides-Stream. Typecheck + eval.
#[test]
fn iterable_members_on_non_stream_carrier() {
    let src = r#"
namespace test.wi424.boxcoll
  import anthill.prelude.{List, Int64, Option, Bool, Stream, Iterable}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Iterable.{find, isEmpty}

  sort BoxColl
    import anthill.prelude.{List, Int64, Stream, Iterable}
    entity boxed(items: List[T = Int64])
    provides Iterable[C = BoxColl, Element = Int64, E = {}]
    operation iterator(b: BoxColl) -> Stream[Int64, {}] =
      match b
        case boxed(items) -> items
  end

  operation is_big(n: Int64) -> Bool = n > 2

  operation unwrap(o: Option[T = Int64]) -> Int64 =
    match o
      case some(x) -> x
      case none() -> 0 - 1

  operation found() -> Int64 = unwrap(find(boxed([1, 2, 3, 4]), is_big))
  operation found_none() -> Int64 = unwrap(find(boxed([1, 2]), is_big))
  operation empty_box() -> Int64 = if isEmpty(boxed([])) then 1 else 0
  operation full_box() -> Int64 = if isEmpty(boxed([1])) then 1 else 0
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi424.boxcoll.found"), 3);
    assert_eq!(run_int(&mut interp, "test.wi424.boxcoll.found_none"), -1);
    assert_eq!(run_int(&mut interp, "test.wi424.boxcoll.empty_box"), 1);
    assert_eq!(run_int(&mut interp, "test.wi424.boxcoll.full_box"), 0);
}

/// EVAL: Iterable.find / Iterable.map run end-to-end on a List.
#[test]
fn iterable_members_eval_on_list() {
    let src = r#"
namespace test.wi424.eval
  import anthill.prelude.{List, Int64, Option, Bool}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.List.{cons}
  import anthill.prelude.Iterable.{find, map}
  import anthill.prelude.Stream.{collect}

  operation is_big(n: Int64) -> Bool = n > 2
  operation inc(n: Int64) -> Int64 = n + 1

  operation unwrap(o: Option[T = Int64]) -> Int64 =
    match o
      case some(x) -> x
      case none() -> 0 - 1

  operation encode3(xs: List[T = Int64]) -> Int64 =
    match xs
      case cons(a, cons(b, cons(c, _))) -> a * 100 + b * 10 + c
      case _ -> 0

  operation found() -> Int64 = unwrap(find([1, 2, 3, 4], is_big))
  operation found_none() -> Int64 = unwrap(find([1, 2], is_big))
  operation mapped_inc() -> Int64 = encode3(collect(map[Dst = Int64]([1, 2, 3], inc)))
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi424.eval.found"), 3);
    assert_eq!(run_int(&mut interp, "test.wi424.eval.found_none"), -1);
    assert_eq!(run_int(&mut interp, "test.wi424.eval.mapped_inc"), 234);
}
