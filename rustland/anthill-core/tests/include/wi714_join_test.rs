//! WI-714 (proposal 052) — `join`: combine two relations by a condition over BOTH
//! rows, with the merged schema `T = Concat[A = r1.T, B = r2.T]`.
//!
//! `join(r1, r2, lambda (c, q) -> eq(c.x, q.y))` compiles the TWO-row lambda — as
//! syntax, never applied — into `guarded(conjunction(r1.query, r2.query), eq(?cx, ?qy))`:
//! the compile-time macro `conjoin_of` (WI-722) reads the lambda + both schemas and
//! splices `join_run(r1, r2, <recipe>)`; the recipe's column holes are filled with the
//! two rows' real column vars at runtime. The result schema is BOTH rows' columns,
//! computed by the typer REDUCING the `Concat[A, B]` type constructor (a merge of two
//! named tuples). First increment: a single atomic predicate over two MULTI-column
//! relations with DISJOINT column names.

use crate::common::{interp_for, try_load_kb_with};
use anthill_core::eval::Value;

const SRC: &str = r#"
namespace test.wi714join
  import anthill.prelude.{String, Int64, Option, List, Pair, Unit, Bool}
  import anthill.prelude.Relation.{join}
  import anthill.prelude.PartialEq.{eq}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)

  sort Membership
    entity member(who: String, dept: String)
  end
  fact member(who: "alice", dept: "eng")
  fact member(who: "carol", dept: "sales")

  -- two 2-column relations with DISJOINT column names.
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)   -- (name, age)
  rule member_row(?who, ?dept) :- member(who: ?who, dept: ?dept)    -- (who, dept)

  -- join on name = who: only "alice" is in BOTH person and member → one joined row.
  operation aliceJoin() -> Bool effects Error =
    let r = person_row.join(member_row, lambda (c, q) -> eq(c.name, q.who))
    r.isEmpty

  -- join on a condition matching nothing (a name never equals a dept here) → empty.
  operation noMatch() -> Bool effects Error =
    let r = person_row.join(member_row, lambda (c, q) -> eq(c.name, q.dept))
    r.isEmpty

  -- drain the joined rows: each is the MERGED 4-field tuple (name, age, who, dept).
  -- The declared element type IS the merged schema — so this annotation type-checking
  -- is itself a test that the typer reduced `Concat[A = r1.T, B = r2.T]` correctly.
  operation joinedRows() -> List[(name: String, age: Int64, who: String, dept: String)] effects Error =
    let r = person_row.join(member_row, lambda (c, q) -> eq(c.name, q.who))
    r.takeN(5)
end
"#;

/// The join keeps the pair (alice-person, alice-member): the filtered relation is
/// NON-empty — proof the two-row lambda compiled to a `guarded(conjunction(...))` the
/// resolver runs, and the column holes `c.name`/`q.who` were filled with the real
/// column vars of each row.
#[test]
fn wi714_join_keeps_matching_rows() {
    let mut interp = interp_for(SRC);
    let r = interp.call("test.wi714join.aliceJoin", &[]).expect("aliceJoin runs the join");
    match r {
        Value::Bool(b) => assert!(!b, "alice is in both rows → non-empty (isEmpty=false)"),
        other => panic!("expected Bool, got {other:?}"),
    }
}

/// The join condition `eq(c.name, q.dept)` matches no pair → the relation is EMPTY
/// (proof the join predicate actually constrains — the conjunction is not a bare,
/// unfiltered cartesian product).
#[test]
fn wi714_join_drops_nonmatching_rows() {
    let mut interp = interp_for(SRC);
    let r = interp.call("test.wi714join.noMatch", &[]).expect("noMatch runs the join");
    match r {
        Value::Bool(b) => assert!(b, "no name equals a dept → empty (isEmpty=true)"),
        other => panic!("expected Bool, got {other:?}"),
    }
}

/// The joined row is the MERGED named tuple `(name, age, who, dept)` — all four columns
/// of both rows, with the real per-row values. The runtime check asserts the merged
/// VALUES (the join found alice-in-eng); the merged field NAMES are asserted by
/// `joinedRows()`'s declared return type `List[(name, age, who, dept)]` type-checking at
/// load — which succeeds only if the typer reduced `Concat[A = r1.T, B = r2.T]` to that
/// exact schema. Together: the runtime column merge (`cols1 ++ cols2'`) AND the typer
/// `Concat` reduction.
#[test]
fn wi714_join_merged_schema_rows() {
    let mut interp = interp_for(SRC);
    let r = interp.call("test.wi714join.joinedRows", &[]).expect("joinedRows drains the join");
    // Walk the cons list; each element is the merged 4-field `Value::Tuple`. There is one
    // joined row (alice); collect its String and Int64 column values by kind — the three
    // `String` columns are name/who/dept, the one `Int64` column is age.
    let mut row_count = 0usize;
    let mut strs: Vec<String> = Vec::new();
    let mut ints: Vec<i64> = Vec::new();
    let mut cur = r;
    while let Value::Entity { named, .. } = &cur {
        if named.is_empty() {
            break;
        }
        let mut head_tuple: Option<Value> = None;
        let mut tail: Option<Value> = None;
        for (_k, v) in named.iter() {
            match v {
                Value::Tuple { .. } => head_tuple = Some(v.clone()),
                Value::Entity { .. } => tail = Some(v.clone()),
                _ => {}
            }
        }
        match (head_tuple, tail) {
            (Some(Value::Tuple { named: fields, .. }), Some(t)) => {
                row_count += 1;
                for (_k, v) in fields.iter() {
                    match v {
                        Value::Str(s) => strs.push(s.clone()),
                        Value::Int(n) => ints.push(*n),
                        other => panic!("unexpected merged-column value {other:?}"),
                    }
                }
                cur = t;
            }
            _ => break,
        }
    }
    strs.sort();
    assert_eq!(row_count, 1, "exactly one joined row (alice is in both)");
    assert_eq!(strs, vec!["alice".to_string(), "alice".to_string(), "eng".to_string()],
        "the merged row's String columns are name=alice, who=alice, dept=eng");
    assert_eq!(ints, vec![30], "the merged row's Int64 column is age=30");
}

/// Two relations that SHARE a column name cannot be merged in this increment: the typer's
/// `Concat[A, B]` reduction requires DISJOINT field names, so a shared name is a loud LOAD
/// error (deferred: qualified-column merge is a follow-up). Both rows here have `name`.
#[test]
fn wi714_join_colliding_column_names_is_load_error() {
    const SRC: &str = r#"
namespace test.wi714joincollide
  import anthill.prelude.{String, Int64, Bool}
  import anthill.prelude.Relation.{join}
  import anthill.prelude.PartialEq.{eq}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "a", age: 1)
  -- both rows expose a `name` column → the merged schema would collide.
  rule left_row(?name, ?age) :- person(name: ?name, age: ?age)
  rule right_row(?name, ?age) :- person(name: ?name, age: ?age)
  operation p() -> Bool effects Error =
    let r = left_row.join(right_row, lambda (c, q) -> eq(c.age, q.age))
    r.isEmpty
end
"#;
    match try_load_kb_with(SRC) {
        Err(errs) => assert!(
            errs.iter().any(|e| e.contains("disjoint") || e.contains("field name")),
            "expected a disjoint-column-name Concat error, got: {errs:?}",
        ),
        Ok(_) => panic!("expected a load error for a join whose merged schema collides on `name`"),
    }
}

/// A 1-collapse (single-column) operand has no named-tuple schema — its column name is
/// dropped from the type — so `Concat` cannot merge it: a loud LOAD error (deferred:
/// single-column joins are a follow-up). `ages` is `Relation[Int64]` (1-collapse).
#[test]
fn wi714_join_one_collapse_operand_is_load_error() {
    const SRC: &str = r#"
namespace test.wi714join1col
  import anthill.prelude.{String, Int64, Bool}
  import anthill.prelude.Relation.{join}
  import anthill.prelude.PartialEq.{eq}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "a", age: 1)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)   -- (name, age)
  rule ages(?age) :- person(age: ?age)                              -- Int64 (1-collapse)
  operation p() -> Bool effects Error =
    let r = person_row.join(ages, lambda (c, q) -> eq(c.age, q))
    r.isEmpty
end
"#;
    match try_load_kb_with(SRC) {
        Err(errs) => assert!(
            errs.iter().any(|e| e.contains("named-tuple") || e.contains("named tuple")),
            "expected a non-named-tuple Concat operand error, got: {errs:?}",
        ),
        Ok(_) => panic!("expected a load error for a join with a 1-collapse (non-named-tuple) operand"),
    }
}
