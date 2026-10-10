//! A const's initializer is of the const's declared type.
//!
//! THE RULE. `: Type` is the name's contract (`docs/kernel-language.md` §5.9), so the
//! value a const is given has that type, as the value of an annotated `let` has its
//! annotation's. A slot the declared type leaves out is the declaration's to pick.
//!
//! BEFORE. The declared type was handed to the initializer as a hint and the
//! initializer's own type was never compared with it. A form that reads the hint was
//! held to it — a branch, a list element — and a value that reads none was not: `const
//! LIMIT: Int64 = "s"`, `const B: String = A` over `const A: Int64`, `const C: String =
//! A + 1` all LOADED, and failed where they were used.
//!
//! CONTROLS — measured:
//!
//!   the comparison backed out (`check_constant_bodies` typing the initializer and
//!   stopping there) — FAIL:
//!     a_const_given_a_value_of_another_type_is_refused
//!     and, in `alias_written_name_test`,
//!     a_const_typed_by_an_alias_keeps_the_alias_it_was_written_by
//!   the two compared without unifying first — FAIL:
//!     a_slot_the_declared_type_leaves_out_is_the_initializers, at its written `?`
//!
//!   PASS EITHER WAY, by design:
//!     a_const_of_its_declared_type_is_its_value — the fence: what must keep loading,
//!       and evaluate.

use anthill_core::eval::Value;

use crate::common::{interp_for, load_errors_of};

fn source(ns: &str, body: &str) -> String {
    format!(
        "namespace test.{ns}\n  import anthill.prelude.{{Int64, Float, String, Bool, List}}\n  \
         import anthill.prelude.List.{{cons, nil}}\n{body}\nend\n"
    )
}

/// A value of another type is refused at the const, whatever form it has: a literal, a
/// reference to another const, a computed expression.
#[test]
fn a_const_given_a_value_of_another_type_is_refused() {
    for (ns, decls, expected) in [
        ("citlit", "  const LIMIT: Int64 = \"s\"", "LIMIT.value (const): expected Int64, got String"),
        (
            "citref",
            "  const A: Int64 = 1\n  const B: String = A",
            "B.value (const): expected String, got Int64",
        ),
        (
            "citcomputed",
            "  const A: Int64 = 1\n  const C: String = A + 1",
            "C.value (const): expected String, got Int64",
        ),
        ("citbool", "  const D: Bool = 2.5", "D.value (const): expected Bool, got Float"),
    ] {
        let errs = load_errors_of(&source(ns, decls));
        assert_eq!(errs.len(), 1, "{ns}: one refusal: {errs:#?}");
        assert!(errs[0].contains(expected), "{ns}: {}", errs[0]);
    }
}

/// A const given a value of its declared type loads, and is that value.
#[test]
fn a_const_of_its_declared_type_is_its_value() {
    let mut interp = interp_for(&source(
        "citfence",
        "  const A: Int64 = 1\n  const B: Int64 = A + 1\n  const NAMES: List[T = String] = [\"a\", \"b\"]\n  \
         operation go() -> Int64 = B + List.length(NAMES)",
    ));
    assert!(matches!(interp.call("test.citfence.go", &[]), Ok(Value::Int(4))));
}

/// A slot the declared type leaves out is the initializer's to fill: `const things: List`
/// is some list, and its value says which. The same with the slot written `?`.
#[test]
fn a_slot_the_declared_type_leaves_out_is_the_initializers() {
    let errs = load_errors_of(&source(
        "citopen",
        "  sort Car\n    sort V = ?\n    entity car(v: V)\n  end\n  \
         const things: List = cons(head: 1, tail: nil)\n  \
         const bare: Car = car(v: \"s\")\n  \
         const written: Car[V = ?] = car(v: 3)\n  \
         operation go() -> Int64 = List.length(things)",
    ));
    assert!(errs.is_empty(), "{errs:#?}");
}
