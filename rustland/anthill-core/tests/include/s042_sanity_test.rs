//! Sanity-check (temporary): operation type parameters (042) inference —
//! same-sort baseline vs the cross-sort case (a `List[Int]` used where a
//! `Stream[T = Elem]` is expected, via List-provides-Stream admissibility).

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn try_load(extra: &str) -> Vec<load::LoadError> {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p).unwrap();
            parse::parse(&src).unwrap()
        })
        .collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).err().unwrap_or_default()
}

fn errors_text(errs: &[load::LoadError]) -> String {
    errs.iter().map(|e| format!("{e}")).collect::<Vec<_>>().join("\n")
}

// ── Baseline: SAME-sort 042 inference (List arg, List param) ────────────────

#[test]
fn same_sort_infers() {
    let src = r#"
namespace test.s042.same
  import anthill.prelude.{List, Int}
  operation id_list[Elem](xs: List[T = Elem]) -> List[T = Elem] = xs
  operation use_it(ys: List[T = Int]) -> List[T = Int] = id_list(ys)
end
"#;
    let errs = try_load(src);
    eprintln!("=== same_sort_infers ===\n{}", errors_text(&errs));
    assert!(errs.is_empty(), "same-sort [Elem] inference: {}", errors_text(&errs));
}

#[test]
fn same_sort_wrong_return_rejected() {
    let src = r#"
namespace test.s042.samewrong
  import anthill.prelude.{List, Int, String}
  operation id_list[Elem](xs: List[T = Elem]) -> List[T = Elem] = xs
  operation use_it(ys: List[T = Int]) -> List[T = String] = id_list(ys)
end
"#;
    let errs = try_load(src);
    eprintln!("=== same_sort_wrong ===\n{}", errors_text(&errs));
    assert!(!errs.is_empty(), "id_list(List[Int]) is List[Int], not List[String]");
}

// ── THE question: CROSS-sort 042 inference (List used as Stream) ────────────

#[test]
fn cross_sort_infers() {
    let src = r#"
namespace test.s042.cross
  import anthill.prelude.{List, Int, Stream}
  import anthill.prelude.Option.{some, none}
  operation probe[Elem](s: Stream[T = Elem]) -> Option[T = Elem] = none
  operation use_it(ys: List[T = Int]) -> Option[T = Int] = probe(ys)
end
"#;
    let errs = try_load(src);
    eprintln!("=== cross_sort_infers ===\n{}", errors_text(&errs));
    assert!(
        errs.is_empty(),
        "cross-sort [Elem]: List[Int] used as Stream[T=Elem] should pin Elem := Int: {}",
        errors_text(&errs)
    );
}

#[test]
fn cross_sort_wrong_return_rejected() {
    let src = r#"
namespace test.s042.crosswrong
  import anthill.prelude.{List, Int, String, Stream}
  import anthill.prelude.Option.{some, none}
  operation probe[Elem](s: Stream[T = Elem]) -> Option[T = Elem] = none
  operation use_it(ys: List[T = Int]) -> Option[T = String] = probe(ys)
end
"#;
    let errs = try_load(src);
    eprintln!("=== cross_sort_wrong ===\n{}", errors_text(&errs));
    assert!(!errs.is_empty(), "probe(List[Int] as Stream) is Option[Int], not Option[String]");
}
