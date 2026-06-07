//! WI-379: bidirectional operation-type-parameter (042) inference —
//! arguments are synthesized BEFORE the expected return type is consulted, in
//! BOTH the operation-apply path (`check_apply_iter`) and the constructor path
//! (`check_constructor_iter`). A wrong declared return is then rejected by the
//! use-site conformance check (`check_operation_bodies` for an op return,
//! `LetAfterValue` for an annotated `let`) because `resolved_ret` carries the
//! argument-derived type.

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
  import anthill.prelude.{List, Int64}
  operation id_list[Elem](xs: List[T = Elem]) -> List[T = Elem] = xs
  operation use_it(ys: List[T = Int64]) -> List[T = Int64] = id_list(ys)
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
  import anthill.prelude.{List, Int64, String}
  operation id_list[Elem](xs: List[T = Elem]) -> List[T = Elem] = xs
  operation use_it(ys: List[T = Int64]) -> List[T = String] = id_list(ys)
end
"#;
    let errs = try_load(src);
    eprintln!("=== same_sort_wrong ===\n{}", errors_text(&errs));
    assert!(!errs.is_empty(), "id_list(List[Int64]) is List[Int64], not List[String]");
}

// ── CROSS-sort 042 inference (List used as Stream, via List-provides-Stream) ─

#[test]
fn cross_sort_infers() {
    let src = r#"
namespace test.s042.cross
  import anthill.prelude.{List, Int64, Stream, Option}
  import anthill.prelude.Option.{some, none}
  operation probe[Elem](s: Stream[T = Elem]) -> Option[T = Elem] = none
  operation use_it(ys: List[T = Int64]) -> Option[T = Int64] = probe(ys)
end
"#;
    let errs = try_load(src);
    eprintln!("=== cross_sort_infers ===\n{}", errors_text(&errs));
    assert!(
        errs.is_empty(),
        "cross-sort [Elem]: List[Int64] used as Stream[T=Elem] should pin Elem := Int64: {}",
        errors_text(&errs)
    );
}

#[test]
fn cross_sort_wrong_return_rejected() {
    let src = r#"
namespace test.s042.crosswrong
  import anthill.prelude.{List, Int64, String, Stream, Option}
  import anthill.prelude.Option.{some, none}
  operation probe[Elem](s: Stream[T = Elem]) -> Option[T = Elem] = none
  operation use_it(ys: List[T = Int64]) -> Option[T = String] = probe(ys)
end
"#;
    let errs = try_load(src);
    eprintln!("=== cross_sort_wrong ===\n{}", errors_text(&errs));
    assert!(!errs.is_empty(), "probe(List[Int64] as Stream) is Option[Int64], not Option[String]");
}

// ── Constructor path: same args-before-expected order (check_constructor_iter) ─

#[test]
fn constructor_infers_ok() {
    let src = r#"
namespace test.s042.ctorok
  import anthill.prelude.{Int64, Option}
  import anthill.prelude.Option.{some}
  operation make() -> Option[T = Int64] = some(42)
end
"#;
    let errs = try_load(src);
    eprintln!("=== constructor_infers_ok ===\n{}", errors_text(&errs));
    assert!(errs.is_empty(), "some(42) is Option[Int64]: {}", errors_text(&errs));
}

// WI-384 (the constructor analogue of the apply-path fix): `some(42)` typed against a
// declared `Option[String]` is now REJECTED. `check_constructor_iter` unifies the
// fields FIRST (pinning `T = Int64`), then seeds `expected` (the contradicting
// `String` does not overwrite the pinned `T`), builds `Option[T = Int64]`, and the
// use-site return-conformance check rejects it. The reorder is sound because the
// build-from-subst now includes an unbound param as a fresh `?_` rather than dropping
// it (which had broken stdlib `pair(h, t)` → `Pair[B=List]`).
#[test]
fn constructor_wrong_return_rejected() {
    let src = r#"
namespace test.s042.ctorwrong
  import anthill.prelude.{Int64, String, Option}
  import anthill.prelude.Option.{some}
  operation make() -> Option[T = String] = some(42)
end
"#;
    let errs = try_load(src);
    eprintln!("=== constructor_wrong_return ===\n{}", errors_text(&errs));
    assert!(!errs.is_empty(), "some(42) is Option[Int64], not Option[String]");
}

// ── Annotated-let conformance (the LetAfterValue use-site check) ─────────────

#[test]
fn let_annotation_conformance_ok() {
    let src = r#"
namespace test.s042.letok
  import anthill.prelude.{List, Int64}
  operation id_list[Elem](xs: List[T = Elem]) -> List[T = Elem] = xs
  operation use_it(ys: List[T = Int64]) -> List[T = Int64] =
    let v : List[T = Int64] = id_list(ys)
    v
end
"#;
    let errs = try_load(src);
    eprintln!("=== let_annotation_conformance_ok ===\n{}", errors_text(&errs));
    assert!(errs.is_empty(), "let v: List[Int64] = id_list(List[Int64]) conforms: {}", errors_text(&errs));
}

#[test]
fn let_annotation_conformance_rejected() {
    let src = r#"
namespace test.s042.letwrong
  import anthill.prelude.{List, Int64, String}
  operation id_list[Elem](xs: List[T = Elem]) -> List[T = Elem] = xs
  operation use_it(ys: List[T = Int64]) -> List[T = String] =
    let v : List[T = String] = id_list(ys)
    v
end
"#;
    let errs = try_load(src);
    eprintln!("=== let_annotation_conformance_rejected ===\n{}", errors_text(&errs));
    assert!(
        !errs.is_empty(),
        "id_list(List[Int64]) is List[Int64]; the let annotation List[String] must be rejected"
    );
}
