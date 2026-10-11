//! The load errors of operations written at namespace level come in the order the
//! operations are written, each run.
//!
//! The typer's sweep over the operations no sort owns read them off the operation table,
//! a hash map, in the table's order, which is another each run: one load printed the same
//! two errors in two orders in two runs. The sweep takes them in the order their bodies
//! were written, as the sweep over the constants' values does, and by the symbol's index
//! between two bodies a pass built at one place.
//!
//! CONTROL — measured with the ordering backed out of `type_check_sorts`' sweep:
//! the_errors_of_namespace_level_operations_come_in_the_order_written FAILS, in every
//! run of ten (the table's order is the written one in one run of 12!). The operations
//! of a sort were typed in the order `SortInfo` lists them and pass either way.
//!
//! Found while delivering WI-20261011-3HN0N.

use crate::common::load_errors_of;

const COUNT: usize = 12;

/// The operation each error names, read off `… in f<i>.return …`.
fn named_operations(errs: &[String]) -> Vec<usize> {
    errs.iter()
        .map(|e| {
            let at = e.find(" in f").unwrap_or_else(|| panic!("an error naming no operation: {e}"));
            let digits: String = e[at + 5..].chars().take_while(char::is_ascii_digit).collect();
            digits.parse().unwrap_or_else(|_| panic!("an error naming no operation: {e}"))
        })
        .collect()
}

fn operations(indent: &str) -> String {
    (0..COUNT)
        .map(|i| format!("{indent}operation f{i}() -> Int64 = \"s{i}\"\n"))
        .collect()
}

#[test]
fn the_errors_of_namespace_level_operations_come_in_the_order_written() {
    let errs = load_errors_of(&format!(
        "namespace test.hn0nerrorder\n  import anthill.prelude.{{Int64, String}}\n{}end\n",
        operations("  ")
    ));
    assert_eq!(named_operations(&errs), (0..COUNT).collect::<Vec<_>>(), "{errs:#?}");
}

#[test]
fn the_errors_of_a_sorts_operations_come_in_the_order_written() {
    let errs = load_errors_of(&format!(
        "namespace test.hn0nerrsort\n  import anthill.prelude.{{Int64, String}}\n  sort Calc\n{}  end\nend\n",
        operations("    ")
    ));
    assert_eq!(named_operations(&errs), (0..COUNT).collect::<Vec<_>>(), "{errs:#?}");
}
