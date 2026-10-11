//! A `const` name is declared at most once per scope (kernel-language.md §5.9) — found
//! while delivering WI-20261011-2QZ3F, on the question of which consts a seal holds.
//!
//! THE RULE. A scope maps a name to one symbol, and a const keeps one declared type and
//! one value under it. A second `const` of the same name in the same scope is a load
//! error that names every declaration, as a second `operation` is; a seal carries the
//! rule to a later load, the sealed load's site named first.
//!
//! BEFORE. The declarations merged and nothing was said: `const K: Int64 = 1` then
//! `const K: Int64 = 2` loaded clean and `K` read 2. A program that
//! declared the standard library's `anthill.cli.help.NAME_COLUMN` again loaded clean
//! over the seal, and the name read the program's 99 in every library body.
//!
//! EVERY ROW HAS ITS OWN SOURCE.
//!
//! CONTROLS — each measured by backing the named piece out and running this file.
//!
//!   THE CHECK OUT (`check_duplicate_const_declarations` answering nothing). FAIL, each
//!   loading clean:
//!     a_second_const_of_one_name_is_refused_in_either_order
//!     a_second_const_in_a_sort_is_refused_and_every_one_is_named
//!     a_const_written_through_a_secondary_entry_is_a_second_one
//!     a_second_const_in_another_file_is_refused
//!     a_bodyless_const_and_a_bodied_one_are_two_declarations
//!     a_program_may_not_declare_a_library_const_again
//!
//!   THE SEAL KEEPING NO CONST (`seal_declarations_where` filling none). FAIL on the
//!   shared base and under `ANTHILL_TEST_TWO_STEP_LOAD=1`, where the library is an
//!   earlier, sealed load:
//!     a_program_may_not_declare_a_library_const_again
//!   It passes under `ANTHILL_TEST_FRESH_LOAD=1` either way: one call over the library
//!   and the program is two declarations in one scan.
//!
//!   PASS with all of it backed out, by design:
//!     consts_of_one_name_on_two_sorts_are_two_consts
//!     the_advised_repair_loads_and_each_const_reads_its_own
//!
//!   THE REFUSAL DOES NOT UNDO THE MERGE, as the operation's does not: `const K: Int64
//!   = 2` then `const K: String` is refused for the name and, by the typer, for the
//!   second's type against the first's value. `the_refusal` counts ONE error on purpose,
//!   so a row whose pair merges into something another pass refuses says so.
//!
//!   NOT REFUSED, measured loading clean before and after: a const beside an
//!   `operation`, an `entity` or a `sort` of the same name in one scope. A bodyless
//!   const with the `const_map` entry that supplies it is one declaration and its
//!   binding: the standard library's `Float.infinity` is in every load here.

use crate::common::{assert_refused_naming, load_errors_of, load_errors_of_files, run_int64};

fn ns(name: &str, decls: &str) -> String {
    format!("namespace test.{name}\n  import anthill.prelude.{{Int64, String}}\n{decls}\nend\n")
}

/// The refusal of `source`: one error, of a const declared more than once.
fn the_refusal(errs: &[String], name: &str, declarations: usize) {
    assert_eq!(errs.len(), 1, "one refusal, of the const; got: {errs:?}");
    assert_refused_naming(
        errs,
        &[
            &format!("const '{name}' is declared more than once in its scope"),
            &format!("({declarations} declarations)"),
        ],
        name,
    );
}

/// The two declarations differ in type and value, so each order loses something else;
/// the refusal is the same.
#[test]
fn a_second_const_of_one_name_is_refused_in_either_order() {
    let (a, b) = ("  const K: Int64 = 1", "  const K: String = \"s\"");
    for (name, first, second) in [("dc1a", a, b), ("dc1b", b, a)] {
        let errs = load_errors_of(&ns(name, &format!("{first}\n{second}")));
        the_refusal(&errs, &format!("test.{name}.K"), 2);
        assert_refused_naming(&errs, &["3:3", "4:3"], "both lines");
    }
}

#[test]
fn a_second_const_in_a_sort_is_refused_and_every_one_is_named() {
    let errs = load_errors_of(&ns(
        "dc2",
        "  sort S\n    const K: Int64 = 1\n    const K: Int64 = 2\n    const K: Int64 = 3\n  end",
    ));
    the_refusal(&errs, "test.dc2.S.K", 3);
    assert_refused_naming(&errs, &["4:5", "5:5", "6:5"], "all three lines");
}

/// `namespace E` beside `sort E` is a second entry to `E`'s scope (§5.1): a const
/// written in it is `E`'s.
#[test]
fn a_const_written_through_a_secondary_entry_is_a_second_one() {
    let errs = load_errors_of(&ns(
        "dc3",
        "  sort E\n    entity e0\n    const K: Int64 = 1\n  end\n  namespace E\n    const K: Int64 = 2\n  end",
    ));
    the_refusal(&errs, "test.dc3.E.K", 2);
}

#[test]
fn a_second_const_in_another_file_is_refused() {
    let errs = load_errors_of_files(&[
        &ns("dc4", "  const K: Int64 = 1"),
        &ns("dc4", "  const K: Int64 = 2"),
    ]);
    the_refusal(&errs, "test.dc4.K", 2);
}

/// A bodyless const is a declaration whose value the host supplies; a second `const`
/// with a value does not give it one.
#[test]
fn a_bodyless_const_and_a_bodied_one_are_two_declarations() {
    let errs = load_errors_of(&ns("dc5", "  const K: Int64\n  const K: Int64 = 2"));
    the_refusal(&errs, "test.dc5.K", 2);
}

/// The standard library is an earlier load, and sealed (§8.3): its const is declared
/// already.
#[test]
fn a_program_may_not_declare_a_library_const_again() {
    let errs = load_errors_of(
        "namespace anthill.cli.help\n  import anthill.prelude.{Int64}\n  const NAME_COLUMN: Int64 = 99\nend\n",
    );
    the_refusal(&errs, "anthill.cli.help.NAME_COLUMN", 2);
}

// ── What does not move ───────────────────────────────────────────────

/// One name on two sorts is two symbols.
#[test]
fn consts_of_one_name_on_two_sorts_are_two_consts() {
    let source = ns(
        "dc6",
        "  sort S\n    const K: Int64 = 2\n    operation rd() -> Int64 = K\n  end\n  sort T\n    const K: Int64 = 3\n    operation rd() -> Int64 = K\n  end",
    );
    assert_eq!(run_int64(&source, "test.dc6.S.rd"), Ok(2));
    assert_eq!(run_int64(&source, "test.dc6.T.rd"), Ok(3));
}

/// "Rename one."
#[test]
fn the_advised_repair_loads_and_each_const_reads_its_own() {
    let source = ns(
        "dc7",
        "  const K: Int64 = 1\n  const K2: Int64 = 2\n  operation rd() -> Int64 = K\n  operation rd2() -> Int64 = K2",
    );
    assert_eq!(run_int64(&source, "test.dc7.rd"), Ok(1));
    assert_eq!(run_int64(&source, "test.dc7.rd2"), Ok(2));
}
