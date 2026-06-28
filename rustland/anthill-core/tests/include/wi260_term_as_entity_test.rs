//! WI-260 — `anthill.reflect.term_as_entity(t: Term) -> Option[T = ?E]`.
//! Decodes a `Term::Fn` whose functor is a registered constructor into a
//! typed `Value::Entity`, using `entity_field_types` to recover declared
//! field order.

use anthill_core::eval::Value;
use anthill_core::kb::term::{Literal, Term};
use smallvec::SmallVec;

use crate::common::interp_for;

#[test]
fn term_as_entity_materializes_workitem_into_typed_entity() {
    let src = r#"
namespace test.wi260
  sort Inventory
    entity Item(id: String, name: String, count: Int64)
  end
  operation main() -> Int64 = 0
end
"#;
    let mut interp = interp_for(src);

    let kb = interp.kb_mut();
    let item_sym = kb.try_resolve_symbol("test.wi260.Inventory.Item")
        .expect("Item symbol present");
    let id_sym = kb.intern("id");
    let name_sym = kb.intern("name");
    let count_sym = kb.intern("count");
    let id_term = kb.alloc(Term::Const(Literal::String("X-001".into())));
    let name_term = kb.alloc(Term::Const(Literal::String("widget".into())));
    let count_term = kb.alloc(Term::Const(Literal::Int(42)));
    let mut named: SmallVec<[(_, _); 2]> = SmallVec::new();
    named.push((id_sym, id_term));
    named.push((name_sym, name_term));
    named.push((count_sym, count_term));
    named.sort_by_key(|(s, _)| s.index());
    let item_tid = kb.alloc(Term::Fn {
        functor: item_sym,
        pos_args: SmallVec::new(),
        named_args: named,
    });

    let some_sym = interp.kb().try_resolve_symbol("anthill.prelude.Option.some")
        .expect("Option.some present");

    let result = interp.call(
        "anthill.reflect.term_as_entity",
        &[Value::term(item_tid)],
    ).expect("call term_as_entity");

    let inner = match result {
        Value::Entity { functor, named, .. } => {
            assert_eq!(functor, some_sym,
                "expected some(...), got {}(...)", interp.kb().resolve_sym(functor));
            assert_eq!(named.len(), 1, "some(value: …) has one field");
            named.iter().next().unwrap().1.clone()
        }
        other => panic!("expected some(...) Entity, got {other:?}"),
    };

    // Inner: Item itself, with three declared fields materialized to
    // typed scalars.
    let kb = interp.kb();
    match inner {
        Value::Entity { functor, pos, named, .. } => {
            assert_eq!(kb.resolve_sym(functor), "Item",
                "functor short name should be Item");
            assert!(pos.is_empty(), "Item has no positional args");
            assert_eq!(named.len(), 3, "Item has three fields");

            let find = |key: &str| named.iter()
                .find(|(s, _)| kb.resolve_sym(*s) == key)
                .map(|(_, v)| v.clone())
                .unwrap_or_else(|| panic!("field `{key}` missing"));

            match find("id") {
                Value::Str(s) => assert_eq!(s, "X-001"),
                other => panic!("id should be Value::Str, got {other:?}"),
            }
            match find("name") {
                Value::Str(s) => assert_eq!(s, "widget"),
                other => panic!("name should be Value::Str, got {other:?}"),
            }
            match find("count") {
                Value::Int(n) => assert_eq!(n, 42),
                other => panic!("count should be Value::Int, got {other:?}"),
            }
        }
        other => panic!("expected Value::Entity, got {other:?}"),
    }
}

#[test]
fn term_as_entity_returns_none_for_non_constructor() {
    // String literal isn't a Fn — should return `none()`.
    let src = r#"
namespace test.wi260_none
  operation main() -> Int64 = 0
end
"#;
    let mut interp = interp_for(src);

    let tid = interp.kb_mut()
        .alloc(Term::Const(Literal::String("not-an-entity".into())));
    let none_sym = interp.kb().try_resolve_symbol("anthill.prelude.Option.none")
        .expect("Option.none present");

    let result = interp.call(
        "anthill.reflect.term_as_entity",
        &[Value::term(tid)],
    ).expect("call term_as_entity");

    match result {
        Value::Entity { functor, named, .. } => {
            assert_eq!(functor, none_sym,
                "expected none(), got {}(...)", interp.kb().resolve_sym(functor));
            assert!(named.is_empty(), "none() carries no fields");
        }
        other => panic!("expected none() Entity, got {other:?}"),
    }
}

#[test]
fn term_as_entity_returns_none_for_unregistered_functor() {
    // Fn whose functor is not a registered constructor — should return
    // `none()` because `constructor_parent_sort` reports `None`.
    let src = r#"
namespace test.wi260_unregistered
  operation main() -> Int64 = 0
end
"#;
    let mut interp = interp_for(src);

    let kb = interp.kb_mut();
    let bogus_sym = kb.intern("nope_not_a_ctor_xyz");
    let arg_term = kb.alloc(Term::Const(Literal::Int(1)));
    let tid = kb.alloc(Term::Fn {
        functor: bogus_sym,
        pos_args: SmallVec::from_slice(&[arg_term]),
        named_args: SmallVec::new(),
    });
    let none_sym = interp.kb().try_resolve_symbol("anthill.prelude.Option.none")
        .expect("Option.none present");

    let result = interp.call(
        "anthill.reflect.term_as_entity",
        &[Value::term(tid)],
    ).expect("call term_as_entity");

    match result {
        Value::Entity { functor, .. } => {
            assert_eq!(functor, none_sym,
                "expected none(), got {}(...)", interp.kb().resolve_sym(functor));
        }
        other => panic!("expected none() Entity, got {other:?}"),
    }
}

#[test]
fn term_as_entity_recurses_into_nested_constructor() {
    // Nested entity: an `Outer(inner: Inner(...))` term decodes both
    // levels — verifies that field values which are themselves
    // constructor terms recurse through `materialize_entity`.
    let src = r#"
namespace test.wi260_nested
  sort Tree
    entity Inner(tag: String)
    entity Outer(name: String, child: Inner)
  end
  operation main() -> Int64 = 0
end
"#;
    let mut interp = interp_for(src);

    let kb = interp.kb_mut();
    let inner_sym = kb.try_resolve_symbol("test.wi260_nested.Tree.Inner")
        .expect("Inner present");
    let outer_sym = kb.try_resolve_symbol("test.wi260_nested.Tree.Outer")
        .expect("Outer present");
    let tag_sym = kb.intern("tag");
    let name_sym = kb.intern("name");
    let child_sym = kb.intern("child");

    let tag_term = kb.alloc(Term::Const(Literal::String("leaf".into())));
    let mut inner_named: SmallVec<[(_, _); 2]> = SmallVec::new();
    inner_named.push((tag_sym, tag_term));
    let inner_term = kb.alloc(Term::Fn {
        functor: inner_sym,
        pos_args: SmallVec::new(),
        named_args: inner_named,
    });

    let name_term = kb.alloc(Term::Const(Literal::String("root".into())));
    let mut outer_named: SmallVec<[(_, _); 2]> = SmallVec::new();
    outer_named.push((name_sym, name_term));
    outer_named.push((child_sym, inner_term));
    outer_named.sort_by_key(|(s, _)| s.index());
    let outer_term = kb.alloc(Term::Fn {
        functor: outer_sym,
        pos_args: SmallVec::new(),
        named_args: outer_named,
    });

    let result = interp.call(
        "anthill.reflect.term_as_entity",
        &[Value::term(outer_term)],
    ).expect("call term_as_entity");

    // Unwrap some(value: Outer{name, child: Inner{tag}}).
    let inner_value = match result {
        Value::Entity { named, .. } => {
            let (_, outer_v) = named.into_iter().next()
                .expect("some(value: …) has one field");
            match outer_v {
                Value::Entity { functor, named: outer_named, .. } => {
                    assert_eq!(interp.kb().resolve_sym(*functor), "Outer");
                    let child = outer_named.iter()
                        .find(|(s, _)| interp.kb().resolve_sym(*s) == "child")
                        .map(|(_, v)| v.clone())
                        .expect("child field present");
                    child
                }
                other => panic!("inner some() should hold Outer entity, got {other:?}"),
            }
        }
        other => panic!("expected some(...), got {other:?}"),
    };

    match inner_value {
        Value::Entity { functor, named, .. } => {
            assert_eq!(interp.kb().resolve_sym(functor), "Inner",
                "child must recurse to Inner entity, not stay as Value::Term");
            let tag = named.iter()
                .find(|(s, _)| interp.kb().resolve_sym(*s) == "tag")
                .map(|(_, v)| v.clone())
                .expect("tag field present on Inner");
            match tag {
                Value::Str(s) => assert_eq!(s, "leaf"),
                other => panic!("tag should be Value::Str, got {other:?}"),
            }
        }
        other => panic!("child field must materialize to Value::Entity, got {other:?}"),
    }
}
