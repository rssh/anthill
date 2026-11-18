//! WI-20261113-S4D63 — the SLD bridge is passed the dictionaries a rule-body call needs, read
//! off the types its arguments are at, as an operation body's call is (decided with the user
//! 2026-11-18: "read ?s's type"). A rule variable is at the type its positions write: a
//! parameter that leaves a named slot unwritten (`has(s: MySet[T = String])`) is open there
//! (kernel-language §5.2), and a position that writes it says which — the call that makes the
//! variable (`?s <=> byLength()`), a head's bound, a relation's column. So `has(?s, "aa")`
//! reads `s.O = ByLength` off `?s`, its dictionary is built at load, and the bridge derives
//! nothing from the value.
//!
//! Before WI-20261113-S4D63 these clauses loaded and the bridge derived `O` from the value,
//! which carries none: §8.7's order chose `String`'s own ordering, and every row below
//! answered `false` where the set is ordered by length (`aa` and `zz` are one class). Since its
//! open-slot refusal and before this, they were refused at load.

use crate::common::{load_errors_of, load_kb_with, one_definite, show_value};

const CARRIER: &str = r#"
namespace s4d63.rv
  import anthill.prelude.{WeakOrd, String, Int64, Bool}
  sort ByLength
    import anthill.prelude.String.{length}
    import anthill.prelude.Numeric.{sub}
    provides WeakOrd[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))
  end
  enum MySet
    import anthill.prelude.PartialOrd.{lt, gt}
    sort T = ?
    requires O: WeakOrd[T]
    entity nothing
    entity node(elem: T, rest: MySet[T = T, O = O])
    operation contains(s: MySet[T = T, O = O], x: T) -> Bool =
      match s
        case nothing() -> false
        case node(y, r) ->
          let c = WeakOrd.compare(x, y)
          if lt(c, 0) then false
          else if gt(c, 0) then contains(r, x)
          else true
    operation empty() -> MySet[T = T, O = O] = nothing()
    operation insert(s: MySet[T = T, O = O], x: T) -> MySet[T = T, O = O] = node(x, s)
  end
  sort Bulk
    operation has(s: MySet[T = String], x: String) -> Bool = MySet.contains(s, x)
  end
  operation byLength() -> MySet[T = String, O = ByLength] =
    MySet.insert(MySet.empty[T = String, O = ByLength](), "zz")
  operation byString() -> MySet[T = String, O = String] =
    MySet.insert(MySet.empty[T = String, O = String](), "zz")
"#;

/// The carrier with `rules` added to its namespace.
fn program(rules: &str) -> String {
    format!("{CARRIER}{rules}end\n")
}

fn answer(kb: &mut anthill_core::kb::KnowledgeBase, rel: &str) -> String {
    let v = one_definite(kb, &format!("s4d63.rv.{rel}"));
    show_value(kb, &v)
}

/// The variable a call makes is at that call's result: `?s <=> byLength()` holds a set
/// ordered by length, and `has(?s, "aa")` reads `O = ByLength` off it, as `let s =
/// byLength()` does in a body. The `String`-ordered twin answers `false`, by its own `O`.
/// FAILS with the called value's bindings not read (`LatePosition::CalledValue`): refused at
/// load, `?s` at `MySet[T = String]`.
#[test]
fn a_variable_is_at_the_result_of_the_call_that_makes_it() {
    let mut kb = load_kb_with(&program(
        r#"  rule viaLength(?b) :- ?s <=> byLength(), ?b <=> Bulk.has(?s, "aa")
  rule viaString(?b) :- ?s <=> byString(), ?b <=> Bulk.has(?s, "aa")
  operation inBody() -> Bool =
    let s = byLength()
    Bulk.has(s, "aa")
  rule bodyTwin(?b) :- ?b <=> inBody()
"#,
    ));
    assert_eq!(answer(&mut kb, "viaLength"), "true", "ordered by length, `aa` is `zz`'s class");
    assert_eq!(answer(&mut kb, "viaString"), "false", "ordered as strings, it is not");
    assert_eq!(answer(&mut kb, "bodyTwin"), "true", "the operation body's twin");
}

/// A head's bound writes the slot, and a relation's column carries it to a caller: `useCol`
/// hands the set to `atColumn`, whose `?s` is at its bound, and `back` reads its own column
/// back from `mk`.
/// FAILS with a bound's bindings not read where the variable's type leaves them unwritten
/// (`constrain_var_at`): refused at load; so does
/// [`a_set_at_another_ordering_is_refused_at_its_column`], whose bound then writes nothing.
#[test]
fn a_head_bound_and_a_column_carry_the_slot() {
    let mut kb = load_kb_with(&program(
        r#"  rule atColumn(?s: MySet[T = String, O = ByLength], ?b) :- ?b <=> Bulk.has(?s, "aa")
  rule useCol(?b) :- ?s <=> byLength(), atColumn(?s, ?b)
  rule mk(?s) :- ?s <=> byLength()
  rule back(?b) :- mk(?s), ?b <=> Bulk.has(?s, "aa")
"#,
    ));
    assert_eq!(answer(&mut kb, "useCol"), "true", "through the bound");
    assert_eq!(answer(&mut kb, "back"), "true", "through the column");
}

/// An operation's parameter that writes the slot is one of the variable's positions too:
/// `viaParam`'s `?s` stands at `has`'s `MySet[T = String]` and at `hasLen`'s `MySet[T = String,
/// O = ByLength]`, and so is a set ordered by length, which `useParam` hands it.
/// FAILS with a walked position's bindings not read where the variable's type leaves them
/// unwritten (`constrain_vid`): refused at load. Before S4D63 it answered `false`.
#[test]
fn a_parameter_that_writes_the_slot_types_the_variable() {
    let mut kb = load_kb_with(&program(
        r#"  operation hasLen(s: MySet[T = String, O = ByLength], x: String) -> Bool = Bulk.has(s, x)
  rule viaParam(?s, ?b) :- ?b <=> Bulk.has(?s, "aa"), ?a <=> hasLen(?s, "zz")
  rule mk(?s) :- ?s <=> byLength()
  rule useParam(?b) :- mk(?s), viaParam(?s, ?b)
"#,
    ));
    assert_eq!(answer(&mut kb, "useParam"), "true");
}

/// A set ordered as strings handed to a column that writes `O = ByLength` is refused at the
/// column: the two positions write the slot apart. Before S4D63 it loaded and answered
/// `false`.
#[test]
fn a_set_at_another_ordering_is_refused_at_its_column() {
    let errors = load_errors_of(&program(
        r#"  rule atColumn(?s: MySet[T = String, O = ByLength], ?b) :- ?b <=> Bulk.has(?s, "aa")
  rule mixed(?b) :- ?s <=> byString(), atColumn(?s, ?b)
"#,
    ));
    assert!(
        errors.iter().any(|e| e.contains("atColumn") && e.contains("O = ByLength") && e.contains("O = String")),
        "refused at `atColumn`'s column, naming both: {errors:#?}"
    );
}

/// Two clauses of one relation that make sets at two orderings give its column no `O`, and a
/// call that reads `s.O` off it is refused, naming `O`: the value does not say which.
/// Passes either way by design (refused before this change too, for the column alone).
#[test]
fn clauses_that_disagree_on_the_slot_leave_it_open() {
    let errors = load_errors_of(&program(
        r#"  rule pick(?s) :- ?s <=> byLength()
  rule pick(?s) :- ?s <=> byString()
  rule usePick(?b) :- pick(?s), ?b <=> Bulk.has(?s, "aa")
"#,
    ));
    assert!(
        errors.iter().any(|e| e.contains("Bulk.has") && e.contains("`O`")),
        "refused at the call, naming `O`: {errors:#?}"
    );
}
