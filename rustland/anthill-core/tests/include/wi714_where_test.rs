//! WI-714 (proposal 052) — `where`: FILTER a relation by a row condition.
//!
//! `where(r, lambda c -> eq(c.x, v))` compiles the row lambda — as syntax, never
//! applied — into `guarded(r.query, eq(?col_x, v))`: the compile-time macro
//! `guarded_of` (WI-722) reads the lambda + `r`'s schema and splices
//! `where_run(r, <recipe>)`; the recipe's column holes (fresh vars NAMED by the
//! field symbol) are filled with `r`'s real column vars at runtime, by canonical
//! `Symbol` match. Schema is unchanged. Consumed through the inherited Stream API.

use crate::common::interp_for;
use anthill_core::eval::Value;

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

/// Single-column relation: WI-20260818-YQB1Y (052 OQ5, option A) dropped the schema
/// 1-collapse, so a one-column row is the named tuple `(age: 30)` and the condition names
/// its column exactly as a multi-column one does. `ages` holds one row of age 30, so
/// `eq(c.age, 30)` keeps it (non-empty) and `eq(c.age, 99)` drops it (empty).
///
/// WHAT THIS REPLACES: the bare-binder spelling `eq(c, 30)`, which rode a WHOLE-ROW hole
/// that `where_run` filled with the relation's sole column. That fill was only ever correct
/// BECAUSE the row was the column; with the row a tuple, no column variable carries it, so
/// the sentinel is gone and the bare binder is refused at load (below).
///
/// CONTROL: this pair FAILS on a back-out. On the pre-change tree `ages`'s schema is the
/// bare `Int64`, so `c.age` resolves to no member and the program does not load.
const SINGLE_COL_SRC: &str = r#"
namespace test.wi714where1
  import anthill.prelude.{String, Int64, Option, List, Pair, Unit, Bool}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)

  -- ONE free head var → Relation[(age: Int64)]; the row is `(age: 30)`.
  rule ages(?age) :- person(age: ?age)

  operation hasThirty() -> Bool effects Error =
    let r = ages.where(lambda c -> eq(c.age, 30))
    r.isEmpty

  operation hasNinetyNine() -> Bool effects Error =
    let r = ages.where(lambda c -> eq(c.age, 99))
    r.isEmpty
end
"#;

/// `eq(c.age, 30)` over the one-column relation keeps the age-30 row → non-empty.
#[test]
fn wi714_where_single_column_keeps() {
    let mut interp = interp_for(SINGLE_COL_SRC);
    let r = interp
        .call("test.wi714where1.hasThirty", &[])
        .expect("hasThirty runs the where-filtered single-column relation");
    match r {
        Value::Bool(b) => assert!(!b, "age=30 matches → non-empty (isEmpty=false)"),
        other => panic!("expected Bool, got {other:?}"),
    }
}

/// `eq(c.age, 99)` matches no row → empty. The negative half: the condition really
/// constrains the sole column rather than being vacuously true.
#[test]
fn wi714_where_single_column_drops() {
    let mut interp = interp_for(SINGLE_COL_SRC);
    let r = interp
        .call("test.wi714where1.hasNinetyNine", &[])
        .expect("hasNinetyNine runs the where-filtered single-column relation");
    match r {
        Value::Bool(b) => assert!(b, "age=99 matches nobody → empty (isEmpty=true)"),
        other => panic!("expected Bool, got {other:?}"),
    }
}

/// A BARE row binder is refused at LOAD, at every arity — WI-20260818-YQB1Y.
///
/// The row is a named tuple now, so `c` names no column variable and there is nothing
/// honest to compile it into: `compile_operand` mints no whole-row hole and refuses.
///
/// BOTH ARITIES, because they used to take DIFFERENT paths and neither survives — and
/// they are refused by DIFFERENT gates, which is why each arm asserts its own message:
///  * one column — `eq(c, 30)` used to LOAD AND RUN, filling the whole-row hole with the
///    sole column. The ROW TYPE now refuses it before the macro is reached: `c` is
///    `(age: Int64)` and `30` is `Int64`, so `eq`'s own operand typing rejects the pair,
///    and the message names the row type — better than anything the macro could say.
///  * two columns — `eq(c, c)` used to load and fail at RUNTIME with `where_run`'s
///    "a single-column relation for a whole-row `where` condition". It still type-checks
///    (a named tuple compares with itself), so the MACRO refuses it, at load, naming the
///    remedy `c.age`.
///
/// CONTROL: both arms fail on a back-out — the one-column arm because that program loads
/// and runs clean on the pre-change tree, the two-column arm because its failure is a
/// runtime `EvalError` there rather than a load error.
#[test]
fn wi714_where_a_bare_row_binder_is_refused_at_load() {
    const ONE_COL: &str = r#"
namespace test.wi714whereb1
  import anthill.prelude.{String, Int64, Bool}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule ages(?age) :- person(age: ?age)
  operation p() -> Bool effects Error =
    let r = ages.where(lambda c -> eq(c, 30))
    r.isEmpty
end
"#;
    const TWO_COL: &str = r#"
namespace test.wi714whereb2
  import anthill.prelude.{String, Int64, Bool}
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
    // The one-column arm: `eq`'s operand typing, naming the ROW type the binder now has.
    let errs = crate::common::try_load_kb_with(ONE_COL)
        .err()
        .expect("one-column: a bare row binder must be a LOAD error");
    let joined = errs.join("\n");
    assert!(
        joined.contains("expected (age: Int64), got Int64"),
        "one-column: the refusal must name the ROW type the bare binder has; got: {joined}"
    );

    // The two-column arm: the macro, because `eq(c, c)` type-checks and so reaches it.
    let errs = crate::common::try_load_kb_with(TWO_COL)
        .err()
        .expect("two-column: a bare row binder must be a LOAD error");
    let joined = errs.join("\n");
    assert!(
        joined.contains("bare row binder") && joined.contains("c.age"),
        "two-column: the refusal must say the binder is the WHOLE row and name the remedy; \
         got: {joined}"
    );
}
