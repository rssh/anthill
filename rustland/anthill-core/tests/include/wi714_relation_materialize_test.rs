//! WI-714 (proposal 052) — C1 foundation: runtime materialization of a relation
//! answer stream. A `Relation[T]` consumed as a stream runs the query lazily
//! (026.1 `execute`) and MATERIALIZES each solution's substitution onto the
//! relation's free variables into a named-tuple row — 1-collapsing to the element
//! value for one free var and to `Unit` for zero. These tests drive the
//! `StreamSource::MaterializedResolver` runtime directly over a real KB query
//! (the resolution + typer surface that mints such a stream from a rule name by
//! name is C2/C3; here we validate the runtime it lowers to).

use anthill_core::eval::stream::StreamSource;
use anthill_core::eval::{Interpreter, Value};
use anthill_core::intern::Symbol;
use anthill_core::kb::term::{Term, Var, VarId};

use crate::common::interp_for;

const SRC: &str = r#"
namespace test.wi714_rel
  import anthill.prelude.{String, Int64}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)
end
"#;

/// Execute `query`, wrap the resolver search in a `MaterializedResolver` over
/// `columns`, and drain every materialized row.
fn materialized_rows(
    interp: &mut Interpreter,
    query: Value,
    columns: Vec<(Symbol, VarId)>,
) -> Vec<Value> {
    let search = interp
        .kb_mut()
        .execute_logical_query(&query)
        .expect("execute lowered the query");
    let cols: std::rc::Rc<[(Symbol, VarId)]> = columns.into();
    let mut handle = interp.alloc_stream(StreamSource::MaterializedResolver {
        search: Some(search),
        columns: cols,
    });
    let mut rows = Vec::new();
    while let Some((row, rest)) = interp.stream_split_first(&handle).expect("pump ok") {
        rows.push(row);
        handle = rest;
    }
    rows
}

/// Build `pattern_query(person(<fields...>))`. Each `fields` entry is
/// `(field short-name, bound?)`: `Some(v)` pins the field to a literal, `None`
/// leaves it a fresh FREE variable — a schema column keyed by the field name.
/// Returns the query plus the free-var columns in declaration order.
fn person_query(
    interp: &mut Interpreter,
    fields: &[(&str, Option<Value>)],
) -> (Value, Vec<(Symbol, VarId)>) {
    let kb = interp.kb_mut();
    let person_sym = kb
        .try_resolve_symbol("test.wi714_rel.Person.person")
        .expect("person entity");
    let pattern_query_sym = kb
        .try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query")
        .expect("pattern_query");
    let term_field = kb.intern("term");
    let mut named: Vec<(Symbol, Value)> = Vec::new();
    let mut columns: Vec<(Symbol, VarId)> = Vec::new();
    for (fname, bound) in fields {
        // Short-name intern: fact-head named-arg keys are stored short (load.rs
        // reintern), so the query pattern must key on the same short Symbol.
        let fsym = kb.intern(fname);
        match bound {
            Some(v) => named.push((fsym, v.clone())),
            None => {
                let vid = kb.fresh_var(fsym);
                let vt = kb.alloc(Term::Var(Var::Global(vid)));
                named.push((fsym, Value::term(vt)));
                columns.push((fsym, vid));
            }
        }
    }
    let pattern = Value::Entity {
        functor: person_sym,
        pos: Vec::new().into(),
        named: named.into(),
    };
    let query = Value::Entity {
        functor: pattern_query_sym,
        pos: Vec::new().into(),
        named: vec![(term_field, pattern)].into(),
    };
    (query, columns)
}

/// Multi-column: two free vars → a named tuple `(name, age)` per solution,
/// keyed by column name in declaration order.
#[test]
fn wi714_materializes_multi_column_named_tuple_rows() {
    let mut interp = interp_for(SRC);
    let (query, columns) = person_query(&mut interp, &[("name", None), ("age", None)]);
    assert_eq!(columns.len(), 2, "two free vars");
    let rows = materialized_rows(&mut interp, query, columns);

    let name_sym = interp.kb_mut().intern("name");
    let age_sym = interp.kb_mut().intern("age");
    let mut got: Vec<(String, i64)> = rows
        .iter()
        .map(|r| {
            let named = match r {
                Value::Tuple { named, .. } => named,
                other => panic!("expected a named-tuple row, got {other:?}"),
            };
            let name = named
                .iter()
                .find(|(k, _)| *k == name_sym)
                .map(|(_, v)| match v {
                    Value::Str(s) => s.clone(),
                    o => panic!("name column not a String: {o:?}"),
                })
                .expect("name column present");
            let age = named
                .iter()
                .find(|(k, _)| *k == age_sym)
                .map(|(_, v)| match v {
                    Value::Int(n) => *n,
                    o => panic!("age column not an Int: {o:?}"),
                })
                .expect("age column present");
            (name, age)
        })
        .collect();
    got.sort();
    assert_eq!(
        got,
        vec![("alice".to_string(), 30), ("bob".to_string(), 25)],
        "each solution materializes onto the free vars as a named tuple"
    );
}

/// One free var → the element value itself (1-collapse), NOT a 1-field tuple.
#[test]
fn wi714_single_free_var_collapses_to_element() {
    let mut interp = interp_for(SRC);
    // age pinned to 30 → only alice matches; name is the sole free column.
    let (query, columns) =
        person_query(&mut interp, &[("name", None), ("age", Some(Value::Int(30)))]);
    assert_eq!(columns.len(), 1, "one free var");
    let rows = materialized_rows(&mut interp, query, columns);
    assert_eq!(rows.len(), 1, "only alice is 30");
    match &rows[0] {
        Value::Str(s) => assert_eq!(s, "alice", "1-collapse yields the element, not a tuple"),
        other => panic!("expected a bare String element (1-collapse), got {other:?}"),
    }
}

/// Zero free vars → a membership relation: each proof materializes as `Unit`.
#[test]
fn wi714_zero_free_vars_materialize_as_unit() {
    let mut interp = interp_for(SRC);
    let (query, columns) = person_query(
        &mut interp,
        &[
            ("name", Some(Value::Str("alice".into()))),
            ("age", Some(Value::Int(30))),
        ],
    );
    assert!(columns.is_empty(), "no free vars");
    let rows = materialized_rows(&mut interp, query, columns);
    assert_eq!(rows.len(), 1, "provable exactly once");
    assert!(
        matches!(rows[0], Value::Unit),
        "a 0-free (boolean/membership) relation materializes each proof as Unit, got {:?}",
        rows[0]
    );
}

/// Empty answer set → empty stream (NotFound is not a bespoke arm).
#[test]
fn wi714_no_solution_yields_empty_stream() {
    let mut interp = interp_for(SRC);
    // No person named "nobody".
    let (query, columns) = person_query(
        &mut interp,
        &[("name", Some(Value::Str("nobody".into()))), ("age", None)],
    );
    let rows = materialized_rows(&mut interp, query, columns);
    assert!(rows.is_empty(), "no match → empty materialized stream");
}
