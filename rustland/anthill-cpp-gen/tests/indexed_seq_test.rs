//! `anthill.prelude.IndexedSeq.{nth, length}` lowers to container-
//! agnostic C++ that works against any type with `size()` and
//! `operator[]` — `std::vector`, `std::array`, user-defined.
//!
//! - `length(xs)` → `static_cast<int64_t>(xs.size())`
//! - `nth(xs, i)` → bounds-checked `std::optional<T>`

use super::common;

use anthill_cpp_gen::emit_traits_struct;
use common::load_kb_with_lenient;

#[test]
fn length_lowers_to_size_cast() {
    let source = r#"
        namespace test.is_len
          import anthill.prelude.{Int, List}
          import anthill.prelude.IndexedSeq.{length}
          export Calc
          sort Calc
            operation count(xs: List[T = Int]) -> Int = length(xs)
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.is_len.Calc")
        .expect("emit Calc");
    assert!(
        cpp.contains("return static_cast<int64_t>(xs.size());"),
        "length should lower to xs.size():\n{cpp}"
    );
}

#[test]
fn nth_lowers_to_bounds_checked_optional() {
    let source = r#"
        namespace test.is_nth
          import anthill.prelude.{Int, List, Option}
          import anthill.prelude.IndexedSeq.{nth}
          export Calc
          sort Calc
            operation pick(xs: List[T = Int], i: Int) -> Option[T = Int] = nth(xs, i)
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&kb, "test.is_nth.Calc")
        .expect("emit Calc");
    // The bounds check covers both lower and upper bounds in one
    // expression so the result type stays `std::optional<T>`.
    assert!(
        cpp.contains("(i >= 0 && static_cast<size_t>(i) < xs.size())"),
        "nth should bounds-check:\n{cpp}"
    );
    assert!(
        cpp.contains("std::make_optional(xs[i])"),
        "nth should wrap in std::make_optional:\n{cpp}"
    );
    assert!(
        cpp.contains("std::nullopt"),
        "nth should fall through to std::nullopt:\n{cpp}"
    );
}
