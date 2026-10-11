//! A const is read by its dotted name in an operation body and in a const's value
//! (kernel-language.md §5.9) — found while delivering WI-20261011-2QZ3F.
//!
//! THE RULE. `S.c`, `ns.S.c` and `Float.infinity` name the const, as the one-segment
//! name does where it is in scope. A dotted name with no `(…)` parses as a
//! `field_access` chain (§6.7); when the chain's segments spell a name that resolves to
//! a const, the loader lowers it to the reference the one-segment spelling lowers to
//! (`Loader::try_qualified_const_ref`).
//!
//! BEFORE. The chain was left standing and the typer walked it: `operation rd() ->
//! Int64 = S.c` was refused, `c.name: expected resolved name, got unresolved`, about a
//! const the sort declares. The same dotted name in a clause's data slot was already the
//! value, and so was the imported one-segment name.
//!
//! EVERY ROW HAS ITS OWN SOURCE.
//!
//! CONTROLS — measured by taking the rung out of `visit_load`'s ladder and running this
//! file. FAIL, each refused "expected resolved name, got unresolved":
//!     a_sorts_const_is_read_by_its_dotted_name
//!     a_library_const_is_read_by_its_dotted_name
//!     a_const_is_read_by_its_absolute_name
//!     a_const_is_read_through_an_alias_of_its_sort
//!     a_dotted_const_stands_wherever_a_value_does
//!     a_consts_value_may_name_a_const_by_its_dotted_name
//!   PASS either way, by design:
//!     the_one_segment_name_reads_the_same
//!     a_local_named_like_the_sort_is_the_receiver
//!     a_hidden_const_is_not_reached_by_its_dotted_name
//!
//!   NOT COVERED, each measured the same before and after. A const as the RECEIVER of a
//!   dot does not project or dispatch, in any spelling: `origin.x`, `Q.origin.x` and
//!   `origin.getX()` are refused where `P.getX(Q.origin)` runs. A nullary operation and
//!   a constructor written dotted with no `(…)` (`Box.zero`, `Kind.k1`) are refused in
//!   an operation body (WI-20260902-40KSW's family).

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

fn ns(name: &str, decls: &str) -> String {
    format!(
        "namespace test.{name}\n  import anthill.prelude.{{Int64, Float}}\n{decls}\nend\n"
    )
}

/// A sort with one const.
const S: &str = "  sort S\n    const c: Int64 = 5\n  end\n";

fn assert_reads(name: &str, decls: &str, expected: i64) {
    let source = ns(name, decls);
    assert_eq!(
        run_int64(&source, &format!("test.{name}.rd")),
        Ok(expected),
        "{source}"
    );
}

#[test]
fn a_sorts_const_is_read_by_its_dotted_name() {
    assert_reads("dn1", &format!("{S}  operation rd() -> Int64 = S.c"), 5);
}

/// A host-supplied const of the standard library, which has no one-segment name here.
#[test]
fn a_library_const_is_read_by_its_dotted_name() {
    assert_reads(
        "dn2",
        "  operation below(x: Float) -> Int64 = if x < Float.infinity then 1 else 0\n  operation rd() -> Int64 = below(2.0)",
        1,
    );
}

#[test]
fn a_const_is_read_by_its_absolute_name() {
    assert_reads("dn3", &format!("{S}  operation rd() -> Int64 = test.dn3.S.c"), 5);
}

#[test]
fn a_const_is_read_through_an_alias_of_its_sort() {
    assert_reads(
        "dn4",
        &format!("{S}  sort A = S\n  operation rd() -> Int64 = A.c"),
        5,
    );
}

/// A condition and an argument.
#[test]
fn a_dotted_const_stands_wherever_a_value_does() {
    assert_reads(
        "dn5",
        &format!(
            "{S}  operation inc(n: Int64) -> Int64 = n + 1\n  operation rd() -> Int64 = if S.c > 4 then inc(S.c) else 0"
        ),
        6,
    );
}

/// A const's value is typed as an operation body is, and reads the name the same way.
#[test]
fn a_consts_value_may_name_a_const_by_its_dotted_name() {
    assert_reads(
        "dn6",
        &format!("{S}  const D: Int64 = S.c + 1\n  operation rd() -> Int64 = D"),
        6,
    );
    assert_reads(
        "dn6b",
        "  const B: Float = Float.infinity\n  operation rd() -> Int64 = if 2.0 < B then 1 else 0",
        1,
    );
}

// ── What does not move ───────────────────────────────────────────────

#[test]
fn the_one_segment_name_reads_the_same() {
    assert_reads(
        "dn7",
        "  sort S\n    const c: Int64 = 5\n    operation inside() -> Int64 = c\n  end\n  operation rd() -> Int64 = S.inside()",
        5,
    );
}

/// A parameter named `S` is a value, and `S.v` its field: the local pass runs first.
#[test]
fn a_local_named_like_the_sort_is_the_receiver() {
    assert_reads(
        "dn8",
        "  sort S\n    const v: Int64 = 99\n  end\n  sort Box\n    entity mk(v: Int64)\n  end\n  operation read(S: Box) -> Int64 = S.v\n  operation rd() -> Int64 = read(Box.mk(7))",
        7,
    );
}

/// `internal` hides the const from outside its sort, by any spelling.
#[test]
fn a_hidden_const_is_not_reached_by_its_dotted_name() {
    let errs = load_errors_of(&ns(
        "dn9",
        "  sort S\n    internal const c: Int64 = 5\n  end\n  operation rd() -> Int64 = S.c",
    ));
    assert_refused_naming(
        &errs,
        &["c.name", "expected resolved name"],
        "the const is internal to `S`, and nothing else is named `S.c`",
    );
}
