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
#[ignore = "WI-714: the TYPER prerequisite (WI-723) is now RESOLVED — the row lambda \
            type-checks with `c : (name, age)` and `c.name : String` (see \
            wi723_row_lambda_binder_test). What remains is WI-714's EVAL mechanism: the \
            `where <=> guarded_of [simp]` rewrite fires during typing but re-typing the \
            `guarded_of(r, cond)` rewrite fails (the quoted lambda passed to the \
            NodeOccurrence-typed macro param gets no schema hint, so `c.name` dot-\
            dispatch fails), so the rewrite is discarded and the bare `where` op reaches \
            eval, where it has no body → `UnknownOperation`. Un-ignore once the \
            where→guarded lowering LOCUS is settled (macro-arg typing vs a Rust typer \
            pass, 052)."]
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
#[ignore = "WI-714: see wi714_where_keeps_matching_rows — the WI-723 typer prereq is \
            resolved; the remaining blocker is WI-714's eval mechanism (macro rewrite \
            discarded, bare `where` reaches eval as UnknownOperation)."]
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
