//! WI-936: the entity FIELD-TYPE registry — and every conversion decision keyed on
//! it — is LOAD-ORDER INDEPENDENT.
//!
//! `kb.entity_field_types` is the expected-type hint the term conversion reads, and
//! three decisions hang off it: the WI-007 `ListLiteral → cons/nil` desugaring, the
//! WI-408 bare-value-in-an-`Option`-field `some(…)` wrap, and the WI-716
//! absent-optional `none()` fill. It used to be written by `load_entity`, during the
//! source-order load pass, so a fact whose entity was declared in a later-loaded file
//! converted against `expected = None` — which is ALSO what a genuinely untyped
//! position gives, so it took the "leave it alone" branch WI-007 installed
//! deliberately for `Set`/`Vec` contexts. An illegal state indistinguishable from a
//! legal one: nothing could report it, and nothing did.
//!
//! MEASURED before the fix, the two files below, only the order swapped:
//!
//! | probe                          | decl, use | use, decl |
//! |--------------------------------|-----------|-----------|
//! | `first_column_type` (cons)     |     1     |     0     |
//! | `wrapped_note` (`some(?)`)     |     1     |     0     |
//! | `terse_note_is_present`        |     0     |     1     |
//!
//! Both orders loaded with ZERO errors either way. The third row is the one that
//! makes this more than a missing answer: an omitted optional field was var-filled
//! instead of `none()`-filled, so `note: some(?)` matched a fact that never mentions
//! `note` — WI-716's stated unsoundness, reachable by nothing but load order.
//!
//! CONTROL. `an_untyped_list_literal_stays_flat_in_either_order` passes BOTH before
//! and after the fix, by design: it pins the case WI-007 protects (a literal in a
//! position with no declared type is left alone), so it is what stops the fix from
//! being "desugar everywhere".
//!
//! BACKED OUT, MEASURED rather than asserted — the declaration pass made a no-op and
//! the load-time lowering restored in `load_entity` / `load_sort_with_body`. Exactly
//! SIX tests fail across the whole workspace: the four subjects here (each on its
//! `use, decl` half; `a_forward_declared_entity_in_one_file_desugars` outright), plus
//! `sql_store_example_test`'s `both_load_orders_of_the_example_answer_the_same` and
//! `the_demo_column_list_destructures_through_its_declared_type`. The control here
//! and the other 4023 pass either way.
//!
//! The sibling driver on REAL files is that `sql_store_example_test`, whose example is
//! loaded by a sorted directory walk — `demo.anthill` before `sql.anthill`, i.e. the
//! losing order — and answers the same as the dependency order.

use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;

/// The DECLARING file: an entity with one `List`-shaped field and one `Option`-shaped
/// field — the two type shapes the conversion keys on.
const DECL: &str = r#"
namespace test.wi936.decl
  import anthill.prelude.{List, Option}

  entity ColumnDef(name: String, sql_type: String)

  entity QueryBinding(
    table   : String,
    columns : List[T = ColumnDef],
    note    : Option[T = String]
  )
end
"#;

/// The USING file: facts written against `DECL`'s schema, and the rules that read
/// them back. Nothing here names a load order.
const USE: &str = r#"
namespace test.wi936.use
  import test.wi936.decl.{ColumnDef, QueryBinding}
  import anthill.prelude.List.{cons}
  import anthill.prelude.Option.{some}

  fact binding(QueryBinding(
    table: "audit",
    columns: [ColumnDef(name: "account", sql_type: "text"),
              ColumnDef(name: "amount",  sql_type: "numeric")],
    note: "written bare"))

  -- `note` is OMITTED: an `Option` field left unsaid is `none()`, never "anything".
  fact terse(QueryBinding(table: "terse", columns: []))

  rule first_column_type(?ty)
    :- binding(QueryBinding(table: ?,
                            columns: cons(head: ColumnDef(name: "account", sql_type: ?ty),
                                          tail: ?),
                            note: ?))

  -- CONTROL for the rule above, inside the language: `amount` is the SECOND column,
  -- so matching it at the spine's HEAD must answer nothing. Without it a positive
  -- `first_column_type` would not say the head was matched.
  rule second_column_at_head(?ty)
    :- binding(QueryBinding(table: ?,
                            columns: cons(head: ColumnDef(name: "amount", sql_type: ?ty),
                                          tail: ?),
                            note: ?))

  rule wrapped_note(?n)
    :- binding(QueryBinding(table: ?, columns: ?, note: some(?n)))

  rule terse_note_is_present(?t)
    :- terse(QueryBinding(table: ?t, columns: ?, note: some(?)))

  -- The fact IS there whichever way `note` was filled — so a zero from the rule
  -- above is about the FILL, not about a missing fact.
  rule terse_table(?t)
    :- terse(QueryBinding(table: ?t, columns: ?, note: ?))
end
"#;

/// A list literal in a position with NO declared type — the case WI-007 leaves alone
/// on purpose. Same file, so no order is involved; it is here to be run in both
/// worlds.
const UNTYPED: &str = r#"
namespace test.wi936.untyped
  import anthill.prelude.List.{cons}

  fact loose([1, 2, 3])

  rule loose_head(?h) :- loose(cons(head: ?h, tail: ?))
  rule loose_whole(?l) :- loose(?l)
end
"#;

fn kb_in_order(sources: &[&str]) -> KnowledgeBase {
    crate::common::try_load_kb_with_files(sources).unwrap_or_else(|errs| {
        for e in &errs {
            eprintln!("load error: {e}");
        }
        panic!("every order must load; got {} error(s)", errs.len());
    })
}

/// The answers of a unary rule, as values.
fn answers(kb: &mut KnowledgeBase, qn: &str) -> Vec<Value> {
    crate::common::query_unary(kb, qn)
        .into_iter()
        .map(|(v, _)| v)
        .collect()
}

fn text_of(kb: &KnowledgeBase, v: &Value) -> String {
    use anthill_core::kb::term::{Literal, Term};
    match v {
        Value::Term { id } => match kb.get_term(*id) {
            Term::Const(Literal::String(s)) => s.clone(),
            other => panic!("expected a string literal, got {other:?}"),
        },
        other => panic!("expected a term, got {other:?}"),
    }
}

/// Run `probe` against BOTH file orders and return the two results, so every subject
/// below states its claim once and the orders cannot silently diverge.
fn both_orders<T: std::fmt::Debug + PartialEq>(probe: impl Fn(&mut KnowledgeBase) -> T) -> T {
    let mut decl_first = kb_in_order(&[DECL, USE]);
    let mut use_first = kb_in_order(&[USE, DECL]);
    let a = probe(&mut decl_first);
    let b = probe(&mut use_first);
    assert_eq!(
        a, b,
        "the two load orders disagree — `decl, use` gave {a:?} and `use, decl` gave {b:?}",
    );
    a
}

/// SUBJECT — the list literal desugars to a `cons` spine either way.
#[test]
fn a_list_literal_desugars_in_either_file_order() {
    let (head, second) = both_orders(|kb| {
        let head: Vec<String> = answers(kb, "test.wi936.use.first_column_type")
            .iter()
            .map(|v| text_of(kb, v))
            .collect();
        let second = answers(kb, "test.wi936.use.second_column_at_head").len();
        (head, second)
    });
    assert_eq!(
        head,
        ["text"],
        "the spine's HEAD is the `account` column, and it carries its own field"
    );
    assert_eq!(
        second, 0,
        "the SECOND column must not match at the head — else the pattern is matching anywhere"
    );
}

/// SUBJECT — a bare value written into an `Option`-typed field is wrapped in `some(…)`
/// either way (WI-408). This is the same registry, a different decision off it: a fix
/// that only special-cased list literals would leave this one order-dependent.
#[test]
fn a_bare_option_value_is_wrapped_in_either_file_order() {
    let notes = both_orders(|kb| {
        answers(kb, "test.wi936.use.wrapped_note")
            .iter()
            .map(|v| text_of(kb, v))
            .collect::<Vec<_>>()
    });
    assert_eq!(
        notes,
        ["written bare"],
        "the bare `note` value is wrapped, so `some(?n)` reaches it"
    );
}

/// SUBJECT — an OMITTED optional field is `none()`-filled either way (WI-716), so a
/// `some(?)` pattern does NOT match it.
///
/// The strongest of the four: pre-fix the losing order answered ONE here. A var-filled
/// optional makes the produced entity `forall v. E(note: v)`, which unifies `some(?)` —
/// an answer that is not missing but wrong, invented by nothing but load order.
#[test]
fn an_omitted_optional_is_none_filled_in_either_file_order() {
    let (present, table) = both_orders(|kb| {
        let present = answers(kb, "test.wi936.use.terse_note_is_present").len();
        let table: Vec<String> = answers(kb, "test.wi936.use.terse_table")
            .iter()
            .map(|v| text_of(kb, v))
            .collect();
        (present, table)
    });
    assert_eq!(
        present, 0,
        "an omitted `Option` field is `none()`, so `some(?)` must not match it"
    );
    assert_eq!(
        table,
        ["terse"],
        "…and the fact is there — the zero above is about the FILL, not a missing fact"
    );
}

/// SUBJECT — the intra-file twin: the entity declared TEXTUALLY AFTER the fact that
/// uses it. This is WI-499's shape (which moved field NAMES into the scan for exactly
/// this reason) carried over to field TYPES; one file, so it needs no order at all.
#[test]
fn a_forward_declared_entity_in_one_file_desugars() {
    let src = r#"
namespace test.wi936.forward
  import anthill.prelude.{List, Option}
  import anthill.prelude.List.{cons}
  import anthill.prelude.Option.{some}

  fact holding(Holder(items: [Tag(label: "first"), Tag(label: "second")], mark: "bare"))

  rule first_label(?l)
    :- holding(Holder(items: cons(head: Tag(label: ?l), tail: ?), mark: ?))

  rule wrapped_mark(?m)
    :- holding(Holder(items: ?, mark: some(?m)))

  entity Tag(label: String)
  entity Holder(items: List[T = Tag], mark: Option[T = String])
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let labels: Vec<String> = answers(&mut kb, "test.wi936.forward.first_label")
        .iter()
        .map(|v| text_of(&kb, v))
        .collect();
    assert_eq!(
        labels,
        ["first"],
        "a forward-declared entity's List field still desugars"
    );
    let marks: Vec<String> = answers(&mut kb, "test.wi936.forward.wrapped_mark")
        .iter()
        .map(|v| text_of(&kb, v))
        .collect();
    assert_eq!(marks, ["bare"], "…and its Option field is still wrapped");
}

/// CONTROL — a list literal in a position with NO declared type is LEFT ALONE, in
/// either order (WI-007's `Set`/`Vec` case, and the reason a diagnostic cannot key on
/// `expected == None` alone).
///
/// This test passes both before and after the change, by design. It is what says the
/// fix moved WHEN the field type is known, not WHICH positions desugar: were the
/// declaration pass to desugar unconditionally, `loose_head` would start answering.
#[test]
fn an_untyped_list_literal_stays_flat_in_either_order() {
    for order in [[UNTYPED, DECL, USE], [USE, DECL, UNTYPED]] {
        let mut kb = kb_in_order(&order);
        assert_eq!(
            answers(&mut kb, "test.wi936.untyped.loose_head").len(),
            0,
            "an untyped `[1, 2, 3]` must stay a flat n-ary node — a `cons` pattern matches nothing",
        );
        assert_eq!(
            answers(&mut kb, "test.wi936.untyped.loose_whole").len(),
            1,
            "…and the fact is there: read as a whole it answers once",
        );
    }
}
