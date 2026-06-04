//! WI-368 / WI-380 acceptance anchor: consuming `List.iterator(xs)` via
//! `collect` / `length` typechecks PURE and threads the element to `List[Int]`.
//!
//! Both cases were PROVEN to pass in isolation during the WI-386 design
//! (`docs/design/effect-rows-on-cross-sort-carriers.md`) with FIX 2 + a
//! `provides Stream[T=T, E={}]` clause + a written-`E` `List.iterator`. They are
//! `#[ignore]`'d pending the WI-386 *implementation* (WI-387) — specifically
//! FIX 3 (the abstract/requires-coverage check must treat a provided concrete
//! `E` as covering `Stream.E`), without which writing `E={}` on List's Stream
//! provision regresses delivered wi357/wi210. Un-ignore when WI-387 lands.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn load_errors(extras: &[&str]) -> Vec<String> {
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

/// `length(collect(List.iterator(xs)))` in a PURE op (no effects clause) must
/// load clean — no floating `?_` observation effect.
#[test]
fn collect_iterator_list_is_pure() {
    let src = r#"
namespace test.wi368.pure
  import anthill.prelude.{List, Int}
  import anthill.prelude.List.{iterator, length}
  import anthill.prelude.Stream.{collect}
  operation walk(xs: List[T = Int]) -> Int = length(collect(iterator(xs)))
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "length(collect(List.iterator(xs))) must typecheck pure (no undeclared ?_); got: {errs:?}",
    );
}

/// The element threads: `collect(List.iterator(xs))` is `List[Int]`, so
/// returning it where `List[T = Int]` is declared conforms, and returning it
/// where `List[T = String]` is declared is REJECTED (the element is really Int).
#[test]
fn collect_iterator_threads_element_int() {
    let ok = r#"
namespace test.wi368.elem_ok
  import anthill.prelude.{List, Int}
  import anthill.prelude.List.{iterator}
  import anthill.prelude.Stream.{collect}
  operation gather(xs: List[T = Int]) -> List[T = Int] = collect(iterator(xs))
end
"#;
    let errs = load_errors(&[ok]);
    assert!(
        errs.is_empty(),
        "collect(List.iterator(xs)) is List[Int]; returning it as List[Int] conforms; got: {errs:?}",
    );

    let wrong = r#"
namespace test.wi368.elem_wrong
  import anthill.prelude.{List, Int, String}
  import anthill.prelude.List.{iterator}
  import anthill.prelude.Stream.{collect}
  operation gather(xs: List[T = Int]) -> List[T = String] = collect(iterator(xs))
end
"#;
    let errs = load_errors(&[wrong]);
    assert!(
        !errs.is_empty(),
        "collect(List.iterator(xs)) is List[Int], not List[String] — must be rejected",
    );
}
