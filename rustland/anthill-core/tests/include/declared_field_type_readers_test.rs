//! An entity's field type is read on whichever carrier it rides.
//!
//! THE RULE. A field's declared type directs how a value written for the field is read: a
//! bare value under `Option` is wrapped, a `[…]` literal under a collection that is no
//! `List` is left as written, a field declared `anthill.reflect.Term` holds a quoted
//! pattern, a persisted name under a sort is that sort's variant, an absent `Option` field
//! of a persisted row is `none`. It directs it the same whether the type is a term, holds
//! a value (`Foo[T = Int64, N = 3]`), or was written through an alias. A mismatch at a
//! field written through an alias leads with the name as written: `expected Money
//! (Int64), got String`.
//!
//! BEFORE. Each reader below took the declared type as a term, or as nothing:
//!
//!   * the loader's and the query converter's expected-type hint. A field typed
//!     `Option[T = Foo[T = Int64, N = 3]]` was given its bare value unwrapped, and one
//!     typed `Set[T = Foo[T = Int64, N = 3]]` had its `[…]` literal lowered to a `cons`
//!     spine, as if no type had been declared;
//!   * the persistence reader. A row with that `Option` field absent was refused,
//!     `MissingField`, where its twin at a plain type reads back `none`;
//!   * the quoted-field test of the body walk, and the derived domain of a sort, which a
//!     field typed through an alias reaches.
//!
//! CONTROLS — measured, each piece backed out on its own:
//!
//!   a field's type lowered without the alias node (`register_declared_field_types`
//!   calling `type_expr_to_value`) — FAIL:
//!     a_field_mismatch_names_the_alias_as_written
//!   a fact's field mismatch printing the declared type as the type it is alone (the
//!   fact-side checks not calling `declared_type_display`) — FAIL: the same row.
//!   the loader's hint narrowed to a term (`convert_term_inner` and
//!   `wrap_bare_option_value` dropping an expected type that is no term) — FAIL:
//!     a_bare_value_is_wrapped_under_an_option_of_a_type_holding_a_value
//!     a_literal_stays_flat_under_a_set_of_a_type_holding_a_value
//!     a_field_typed_by_an_alias_of_an_option_of_a_list_wraps_and_lowers
//!     a_query_pattern_matches_what_was_stored_under_a_type_holding_a_value — the two
//!       converters then disagree about the stored shape
//!   the query converter's hint narrowed to a term (`convert_query_term_expecting`
//!   dropping one that is no term) — FAIL:
//!     a_query_pattern_matches_what_was_stored_under_a_type_holding_a_value
//!   the persistence reader keeping only the fields typed by a term
//!   (`entity_field_type_map`) — FAIL:
//!     an_absent_option_field_of_a_type_holding_a_value_reads_back_none
//!     a_persisted_name_under_an_alias_of_a_sort_is_that_sorts_variant
//!   the body walk's quoted-field test on a term alone (`entity_field_is_quoted`) — FAIL:
//!     a_field_typed_by_an_alias_of_term_holds_a_quoted_pattern
//!   the derived domain naming a field's type only when it is a term
//!   (`domain_field_type_term`) — FAIL, in `wi_shed7_fillable_test`:
//!     an_aliased_field_is_filled_as_its_target
//!
//!   PASS EITHER WAY, by design:
//!     a_field_typed_by_an_alias_takes_a_value_of_the_type — the fence: what the node
//!       must not change.

use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::term_ser;

use crate::common::{interp_for, load_errors_of, load_kb_with, query_unary};

fn source(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace test.{ns}
  import anthill.prelude.{{Int64, Float, String, Bool, List, Option, Set}}
  import anthill.prelude.List.{{cons, nil}}
  import anthill.prelude.Option.{{some, none}}
  sort Foo
    sort T = ?
    sort N = ?
    entity foo(v: T)
  end
  sort Money = Int64
  fact mark(1)
{body}
end
"#
    )
}

/// The definite answers of a unary rule.
fn answers(kb: &mut KnowledgeBase, qn: &str) -> Vec<Value> {
    query_unary(kb, qn)
        .into_iter()
        .filter(|(_, definite)| *definite)
        .map(|(v, _)| v)
        .collect()
}

/// The integers a unary rule answers.
fn ints(kb: &mut KnowledgeBase, qn: &str) -> Vec<i64> {
    answers(kb, qn)
        .into_iter()
        .map(|v| match v {
            Value::Int(n) => n,
            other => panic!("{qn}: expected an Int64, got {other:?}"),
        })
        .collect()
}

/// The strings a unary rule answers.
fn strings(kb: &mut KnowledgeBase, qn: &str) -> Vec<String> {
    answers(kb, qn)
        .into_iter()
        .map(|v| match v {
            Value::Str(s) => s,
            other => panic!("{qn}: expected a String, got {other:?}"),
        })
        .collect()
}

/// The one refusal of a source that must not load.
fn refusal(ns: &str, body: &str) -> String {
    let errs = load_errors_of(&source(ns, body));
    assert_eq!(errs.len(), 1, "{ns}: one refusal: {errs:#?}");
    errs.into_iter().next().unwrap()
}

// ── a field type that holds a value ─────────────────────────────────────────

/// A bare value written for an `Option` field is wrapped, also when the option's type
/// holds a value: `some(…)` reaches it.
#[test]
fn a_bare_value_is_wrapped_under_an_option_of_a_type_holding_a_value() {
    let mut kb = load_kb_with(&source(
        "dfwrap",
        "  sort Slot\n    entity slot(note: Option[T = Foo[T = Int64, N = 3]])\n  end\n  \
         fact slot(note: foo(v: 7))\n  \
         rule noted(?n) :- slot(note: some(foo(v: ?n)))",
    ));
    assert_eq!(ints(&mut kb, "test.dfwrap.noted"), [7]);
}

/// A `[…]` literal written for a field declared a `Set` stays as written, also when the
/// set's element type holds a value: a `cons` pattern matches nothing, and the fact is
/// there.
#[test]
fn a_literal_stays_flat_under_a_set_of_a_type_holding_a_value() {
    let mut kb = load_kb_with(&source(
        "dfset",
        "  entity Tagged(tags: Set[T = Foo[T = Int64, N = 3]])\n  \
         fact tagged(Tagged(tags: [foo(v: 1), foo(v: 2)]))\n  \
         rule set_head(?m) :- mark(?m), tagged(Tagged(tags: cons(head: ?, tail: ?)))\n  \
         rule set_whole(?m) :- mark(?m), tagged(Tagged(tags: ?))",
    ));
    assert_eq!(query_unary(&mut kb, "test.dfset.set_head").len(), 0);
    assert_eq!(ints(&mut kb, "test.dfset.set_whole"), [1]);
}

/// A query pattern takes the shape the loader stored under the same declared type: the
/// literal a `Set` field was written with finds the fact, and another literal does not.
#[test]
fn a_query_pattern_matches_what_was_stored_under_a_type_holding_a_value() {
    let mut kb = load_kb_with(&source(
        "dfquery",
        "  entity Tagged(tags: Set[T = Foo[T = Int64, N = 3]])\n  \
         fact tagged(Tagged(tags: [foo(v: 1), foo(v: 2)]))",
    ));
    crate::common::supply_invocation_imports(&mut kb, &["test.dfquery.*", "test.dfquery.Foo.*"]);
    fn hits(kb: &mut KnowledgeBase, pattern: &str) -> usize {
        use anthill_core::kb::resolve::ResolveConfig;
        let goal = crate::common::query_pattern_term(kb, pattern);
        kb.resolve(&[goal], &ResolveConfig::default()).len()
    }
    assert_eq!(hits(&mut kb, "tagged(Tagged(tags: [foo(v: 1), foo(v: 2)]))"), 1);
    assert_eq!(hits(&mut kb, "tagged(Tagged(tags: [foo(v: 1), foo(v: 9)]))"), 0);
}

/// A persisted row that leaves out an `Option` field reads back with `none` there, also
/// when the option's type holds a value.
#[test]
fn an_absent_option_field_of_a_type_holding_a_value_reads_back_none() {
    let mut kb = load_kb_with(&source(
        "dfabsent",
        "  sort Job\n    entity Job(id: String, note: Option[T = Foo[T = Int64, N = 3]])\n  end\n  \
         rule unnoted(?i) :- Job(id: ?i, note: none)",
    ));
    let domain = kb.intern("dfabsent_domain");
    term_ser::load_toml(
        &mut kb,
        "[meta]\nentity = \"test.dfabsent.Job\"\n\n[data]\nid = \"j1\"\n",
        domain,
    )
    .expect("a row without its optional field loads");
    assert_eq!(strings(&mut kb, "test.dfabsent.unnoted"), ["j1"]);
}

// ── a field type written through an alias ───────────────────────────────────

/// A field typed by an alias takes a value of the type, and gives it back as that type.
#[test]
fn a_field_typed_by_an_alias_takes_a_value_of_the_type() {
    let mut interp = interp_for(&source(
        "dffence",
        "  sort Purse\n    entity purse(m: Money)\n  end\n  \
         operation go() -> Int64 = purse(m: 4).m + 1",
    ));
    assert!(matches!(interp.call("test.dffence.go", &[]), Ok(Value::Int(5))));
}

/// A mismatch at a field written through an alias leads with the alias, in a fact and at
/// a construction.
#[test]
fn a_field_mismatch_names_the_alias_as_written() {
    let refused = refusal(
        "dfname",
        "  sort Purse\n    entity purse(m: Money)\n  end\n  fact purse(m: \"s\")",
    );
    assert!(refused.contains("expected Money (Int64), got String"), "{refused}");
    let refused = refusal(
        "dfnamector",
        "  sort Purse\n    entity purse(m: Money)\n  end\n  \
         operation go() -> Int64 = purse(m: \"s\").m",
    );
    assert!(refused.contains("expected Money (Int64), got String"), "{refused}");
}

/// A field typed by an alias of `Option[T = List[…]]` reads its value as that type does:
/// the literal is a list, and the bare list is wrapped.
#[test]
fn a_field_typed_by_an_alias_of_an_option_of_a_list_wraps_and_lowers() {
    let mut kb = load_kb_with(&source(
        "dfdeps",
        "  sort Deps = Option[T = List[T = String]]\n  \
         sort Item\n    entity item(deps: Deps)\n  end\n  \
         fact item(deps: [\"a\", \"b\"])\n  \
         rule first(?h) :- item(deps: some(cons(?h, ?)))",
    ));
    assert_eq!(strings(&mut kb, "test.dfdeps.first"), ["a"]);
}

/// A field typed by an alias of `anthill.reflect.Term` holds a quoted pattern: a const
/// in it is the name its author wrote, not its value.
#[test]
fn a_field_typed_by_an_alias_of_term_holds_a_quoted_pattern() {
    let mut kb = load_kb_with(&source(
        "dfquoted",
        "  import anthill.reflect.{Term}\n  const D_MIN: Float = 1.5\n  \
         sort Pattern = Term\n  \
         sort Rec\n    entity f(v: Float)\n    entity holds(pattern: Pattern)\n  end\n  \
         fact holds(pattern: f(v: D_MIN))\n  \
         rule by_name(1) :- holds(pattern: f(v: D_MIN))\n  \
         rule by_value(1) :- holds(pattern: f(v: 1.5))",
    ));
    assert_eq!(ints(&mut kb, "test.dfquoted.by_name"), [1]);
    assert_eq!(query_unary(&mut kb, "test.dfquoted.by_value").len(), 0);
}

/// A persisted name under a field typed by an alias of a sort is that sort's variant.
#[test]
fn a_persisted_name_under_an_alias_of_a_sort_is_that_sorts_variant() {
    let mut kb = load_kb_with(&source(
        "dfvariant",
        "  sort Status\n    entity Open\n    entity Closed\n  end\n  sort St = Status\n  \
         sort Job\n    entity Job(id: String, status: St)\n  end\n  \
         rule closed(?i) :- Job(id: ?i, status: Closed)",
    ));
    let domain = kb.intern("dfvariant_domain");
    term_ser::load_toml(
        &mut kb,
        "[meta]\nentity = \"test.dfvariant.Job\"\n\n[data]\nid = \"j1\"\nstatus = \"Closed\"\n",
        domain,
    )
    .expect("a variant of the declared sort loads");
    assert_eq!(strings(&mut kb, "test.dfvariant.closed"), ["j1"]);
}
