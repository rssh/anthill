//! WI-714 (proposal 052) — `where`: FILTER a relation by a row condition.
//!
//! `where(r, lambda c -> eq(c.x, v))` compiles the row lambda — as syntax, never
//! applied — into `guarded(r.query, eq(?col_x, v))`: the compile-time macro
//! `guarded_of` (WI-722) reads the lambda + `r`'s schema and splices
//! `where_run(r, <recipe>)`; the recipe's column holes (fresh vars NAMED by the
//! field symbol) are filled with `r`'s real column vars at runtime, by canonical
//! `Symbol` match. Schema is unchanged. Consumed through the inherited Stream API.

use crate::common::interp_for;
use anthill_core::eval::{EvalError, Value};

const SRC: &str = r#"
namespace test.wi714where
  import anthill.prelude.{String, Int64, Option, List, Pair, Unit, Bool}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)

  -- two free head vars → Relation[(name: String, age: Int64)]
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  -- where FILTERS on the `name` column (dot-call resolves the row schema): keep
  -- rows whose name = "alice" → only alice.
  operation hasAlice() -> Bool effects Error =
    let r = person_row.where(lambda c -> eq(c.name, "alice"))
    r.isEmpty

  -- no row named "zed" → the filtered relation is empty.
  operation hasZed() -> Bool effects Error =
    let r = person_row.where(lambda c -> eq(c.name, "zed"))
    r.isEmpty
end
"#;

/// `person_row.where(c -> eq(c.name, "alice"))` filters to alice: the relation is
/// NON-empty (proof the row-lambda compiled to a `guarded` goal the resolver runs,
/// and the column hole `c.name` was filled with the real `name` column var).
#[test]
fn wi714_where_keeps_matching_rows() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi714where.hasAlice", &[])
        .expect("hasAlice runs the where-filtered relation");
    match r {
        Value::Bool(b) => assert!(!b, "name=alice matches → non-empty (isEmpty=false)"),
        other => panic!("expected Bool, got {other:?}"),
    }
}

/// `person_row.where(c -> eq(c.name, "zed"))` filters to nothing: the relation is
/// EMPTY (proof the guard actually constrains — it is not vacuously true).
#[test]
fn wi714_where_drops_nonmatching_rows() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi714where.hasZed", &[])
        .expect("hasZed runs the where-filtered relation");
    match r {
        Value::Bool(b) => assert!(b, "name=zed matches nobody → empty (isEmpty=true)"),
        other => panic!("expected Bool, got {other:?}"),
    }
}

/// Single-column (1-collapse) relation: the row binder `c` IS the sole `Int64`
/// column, so a BARE `eq(c, 30)` (not `c.field`) compiles to a WHOLE-ROW hole that
/// `where_run` maps to the one column. `ages` holds one row of age 30, so `eq(c, 30)`
/// keeps it (non-empty) and `eq(c, 99)` drops it (empty).
const SINGLE_COL_SRC: &str = r#"
namespace test.wi714where1
  import anthill.prelude.{String, Int64, Option, List, Pair, Unit, Bool}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)

  -- ONE free head var → Relation[Int64] (1-collapse); the row IS the age.
  rule ages(?age) :- person(age: ?age)

  operation hasThirty() -> Bool effects Error =
    let r = ages.where(lambda c -> eq(c, 30))
    r.isEmpty

  operation hasNinetyNine() -> Bool effects Error =
    let r = ages.where(lambda c -> eq(c, 99))
    r.isEmpty
end
"#;

/// `eq(c, 30)` on the bare 1-collapse binder keeps the age-30 row → non-empty.
#[test]
fn wi714_where_single_column_whole_row_keeps() {
    let mut interp = interp_for(SINGLE_COL_SRC);
    let r = interp
        .call("test.wi714where1.hasThirty", &[])
        .expect("hasThirty runs the where-filtered single-column relation");
    match r {
        Value::Bool(b) => assert!(!b, "age=30 matches → non-empty (isEmpty=false)"),
        other => panic!("expected Bool, got {other:?}"),
    }
}

/// `eq(c, 99)` on the bare 1-collapse binder matches no row → empty (the whole-row
/// hole actually constrains the sole column, not vacuously true).
#[test]
fn wi714_where_single_column_whole_row_drops() {
    let mut interp = interp_for(SINGLE_COL_SRC);
    let r = interp
        .call("test.wi714where1.hasNinetyNine", &[])
        .expect("hasNinetyNine runs the where-filtered single-column relation");
    match r {
        Value::Bool(b) => assert!(b, "age=99 matches nobody → empty (isEmpty=true)"),
        other => panic!("expected Bool, got {other:?}"),
    }
}

/// A bare whole-row binder `eq(c, c)` over a MULTI-column relation is a whole-row
/// comparison with no single eq column. It is REACHABLE — named-tuple `eq(c, c)`
/// type-checks, so the row lambda compiles and the whole-row hole is minted — so
/// `where_run` must reject it with a clean USER-facing error (not an internal
/// invariant break) naming the multi-column limitation, when the relation is run.
#[test]
fn wi714_where_multicolumn_whole_row_is_a_clean_error() {
    const SRC: &str = r#"
namespace test.wi714where2
  import anthill.prelude.{String, Int64, Option, List, Pair, Unit, Bool}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "a", age: 1)
  rule prow(?name, ?age) :- person(name: ?name, age: ?age)
  operation p() -> Bool effects Error =
    let r = prow.where(lambda c -> eq(c, c))
    r.isEmpty
end
"#;
    let mut interp = interp_for(SRC);
    match interp.call("test.wi714where2.p", &[]) {
        Err(EvalError::TypeMismatch { got, .. }) => assert!(
            got.contains("2-column"),
            "expected a multi-column whole-row diagnostic, got: {got}",
        ),
        other => panic!("expected a clean TypeMismatch for a multi-column whole-row where, got {other:?}"),
    }
}
