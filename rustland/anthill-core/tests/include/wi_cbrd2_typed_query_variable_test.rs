//! A TYPED VARIABLE IN A QUERY READS AS A TYPED RULE HEAD'S (WI-20261105-CBRD2, proposal 010.1
//! §3.1, stage 2). A query is a clause with no head, and `?x: T` written in it adds the goals a
//! typed head's bound adds (060 §2.3): the conformance guard in front of the pattern and `T`'s
//! `fill` after it, by name where it reads no dictionary and through the type where it does.
//! A type that leaves a parameter unwritten is refused, its domain being a requirement at an
//! open type that a query has no caller to pass; a variable given two types is refused, as a
//! rule head's is; a typed variable under a connective is refused, its goals standing around the
//! goal it is written in; and a pattern no typer reads (`--match`, a goal built at run time) refuses
//! a typed variable, having nothing to read it with. Before this, `?bal: Int64` in a query
//! panicked the loader (`unreachable!` in `convert_query_term_expecting`).
//!
//! ## What fails with each part backed out
//!
//! Measured with temporary switches in one build, then removed. The control is every switch
//! unset: every row passes.
//!
//! * the goals not added (the pattern converted with each typed variable read as its bare
//!   variable): [`a_typed_query_variable_checks_its_column`] (`?bal: String` answers 2),
//!   [`a_typed_query_variable_lists_its_types_values`] (one answer, `?c` free),
//!   [`a_parameterised_type_is_checked_through_its_domain`] (`Option[T = String]` answers 1),
//!   [`a_type_left_open_is_refused`] and [`a_variable_given_two_types_is_refused`] (each
//!   converts);
//! * the connective check not made: [`a_typed_variable_under_a_connective_is_refused`] (both
//!   patterns convert, the disjunction then answering `Color`'s three values and no account);
//! * the query walk not descending through a conjunction (`collect_undefined_goal_functors`):
//!   [`a_typed_pattern_naming_nothing_is_reported`] (the typed pattern reports nothing);
//! * the untyped conversion not refusing a typed variable:
//!   [`a_pattern_no_typer_reads_refuses_a_typed_variable`] (it converts, the type dropped).
//!
//! [`a_variable_given_two_types_is_refused`]'s alias line passes with the types compared
//! undealiased, on both carriers (measured): an alias written as a typed variable's type lowers
//! to its target's term.

use crate::common::{load_kb_with, pattern_answer_counts, query_pattern_refusals, query_pattern_term};
use anthill_core::kb::load;
use anthill_core::parse;

const SRC: &str = r#"
namespace test.cbrd2.tqv
  import anthill.prelude.{Int64, String, Bool, Option, List}
  import anthill.prelude.Option.{some, none}

  sort Account
    entity account(id: Int64, owner: String, balance: Int64)
  end
  fact account(id: 1, owner: "ann", balance: 500)
  fact account(id: 2, owner: "bob", balance: 2000)

  sort Color
    entity red
    entity green
    entity blue
  end

  sort Count = Int64

  rule anyOf(?c) :- true
  rule held(?o) :- ?o <=> some(3)
end
"#;

/// The definite answers of the query `pattern`, every answer definite.
fn definite(pattern: &str) -> usize {
    let mut kb = load_kb_with(SRC);
    let (definite, total) = pattern_answer_counts(&mut kb, pattern);
    assert_eq!(definite, total, "every answer of `{pattern}` is definite");
    definite
}

/// What converting the query `pattern` refuses, rendered.
fn refusals(pattern: &str) -> Vec<String> {
    let mut kb = load_kb_with(SRC);
    query_pattern_refusals(&mut kb, pattern)
}

/// `?bal: Int64` holds of each account's balance; `?bal: String` of none.
#[test]
fn a_typed_query_variable_checks_its_column() {
    assert_eq!(definite("test.cbrd2.tqv.Account.account(?id, ?owner, ?bal: Int64)"), 2);
    assert_eq!(definite("test.cbrd2.tqv.Account.account(?id, ?owner, ?bal: String)"), 0);
}

/// `anyOf` binds nothing, so `?c: Color` is filled from `Color`'s domain: its three values.
#[test]
fn a_typed_query_variable_lists_its_types_values() {
    assert_eq!(definite("test.cbrd2.tqv.anyOf(?c: test.cbrd2.tqv.Color)"), 3);
}

/// `Option`'s domain is conditional on its parameter, so its fill runs through the type:
/// `some(3)` is an `Option[T = Int64]` and no `Option[T = String]`.
#[test]
fn a_parameterised_type_is_checked_through_its_domain() {
    assert_eq!(
        definite("test.cbrd2.tqv.held(?o: anthill.prelude.Option[T = Int64])"),
        1
    );
    assert_eq!(
        definite("test.cbrd2.tqv.held(?o: anthill.prelude.Option[T = String])"),
        0
    );
}

/// `?o: Option` leaves `T` unwritten: the domain of `Option[T = ?]` is a requirement at an open
/// type, and a query has no caller to pass it.
#[test]
fn a_type_left_open_is_refused() {
    let errs = refusals("test.cbrd2.tqv.held(?o: anthill.prelude.Option)");
    assert!(
        errs.iter().any(|e| e.contains("leaves a type parameter unwritten")),
        "the open `T` is refused; got {errs:?}"
    );
}

/// A variable's type is declared once: `?id: Int64` and `?id: String` are refused, and the same
/// type written twice is one declaration.
#[test]
fn a_variable_given_two_types_is_refused() {
    let errs = refusals("test.cbrd2.tqv.Account.account(?id: Int64, ?owner, ?id: String)");
    assert!(
        errs.iter().any(|e| e.contains("is given two types")),
        "the second type is refused; got {errs:?}"
    );
    assert!(refusals("test.cbrd2.tqv.Account.account(?id: Int64, ?owner, ?bal: Int64)").is_empty());
    assert!(
        refusals("test.cbrd2.tqv.Account.account(?id: test.cbrd2.tqv.Count, ?owner, ?id: Int64)")
            .is_empty(),
        "an alias and the type it stands for are one type"
    );
}

/// A typed pattern is the pattern joined with its type's goals, and is still committed to the
/// pattern's own head: a name that denotes nothing is reported, as in the untyped pattern.
#[test]
fn a_typed_pattern_naming_nothing_is_reported() {
    let mut kb = load_kb_with(SRC);
    for pattern in [
        "test.cbrd2.tqv.account(?id, ?owner, ?bal)",
        "test.cbrd2.tqv.account(?id, ?owner, ?bal: Int64)",
    ] {
        let qt = query_pattern_term(&mut kb, pattern);
        let unknown = kb.undefined_query_goal_functors(&qt);
        assert_eq!(unknown.len(), 1, "`{pattern}` names no relation; got {unknown:?}");
    }
}

/// Under a connective the goals would stand around the whole pattern and check the type outside
/// the negand or branch the variable is written in: `account(?id, ?o, ?b) | anyOf(?b: Color)`
/// would keep only `Color`s from the `account` branch too. A typed variable is refused there.
#[test]
fn a_typed_variable_under_a_connective_is_refused() {
    for pattern in [
        "not(test.cbrd2.tqv.Account.account(?id, ?o, ?b: String))",
        "test.cbrd2.tqv.Account.account(?id, ?o, ?b) | test.cbrd2.tqv.anyOf(?b: test.cbrd2.tqv.Color)",
    ] {
        let errs = refusals(pattern);
        assert!(
            errs.iter().any(|e| e.contains("is written under a connective")),
            "`{pattern}` is refused; got {errs:?}"
        );
    }
}

/// The untyped conversion — a structural browse's, a goal built at run time's — has no typer to
/// read a typed variable with, and refuses it rather than dropping its type.
#[test]
fn a_pattern_no_typer_reads_refuses_a_typed_variable() {
    let mut kb = load_kb_with(SRC);
    let pattern = "test.cbrd2.tqv.Account.account(?id, ?owner, ?bal: String)";
    let parsed = parse::parse(&format!("fact {pattern}")).expect("parse query pattern");
    let errs = load::scan_query_definitions(&mut kb, &[&parsed]);
    assert!(errs.is_empty(), "the pattern scans clean: {errs:?}");
    let anthill_core::parse::ir::Item::Fact(fact) = &parsed.items[0] else {
        panic!("the pattern is a fact item");
    };
    let scope = kb.global_scope();
    let mut var_map = std::collections::HashMap::new();
    match load::convert_patterns_untyped(&mut kb, &parsed, &[fact.term], scope, &mut var_map) {
        Ok(_) => panic!("an untyped pattern must refuse `?bal: String`, not drop its type"),
        Err(errs) => assert!(
            errs.iter()
                .any(|e| e.to_string().contains("is read only by a typed query")),
            "got {:?}",
            errs.iter().map(|e| e.to_string()).collect::<Vec<_>>()
        ),
    }
}
