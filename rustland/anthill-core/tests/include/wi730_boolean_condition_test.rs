//! WI-730 (proposal 052 §"Compiling a row lambda into a query") — BOOLEAN NESTING in
//! a `where` / `join` row-lambda condition.
//!
//! The first `where`/`join` increments compiled a single atomic predicate. 052's
//! tree→query mapping — the LINQ `Expression`→SQL analog — specifies the rest:
//! `and`/`or`/`not` map onto the `conjunction`/`disjunction`/`negation` constructors
//! the `kb/execute.rs` lowerer already wires, composing the same atoms. So the recipe
//! a row lambda compiles to is now a `LogicalQuery` TREE, and nesting is free: the
//! lowerer flattens a conjunction into a goal list and lifts a multi-goal `or`/`not`
//! branch through a synthesized conjunction rule.
//!
//! Every filter is asserted in BOTH directions — a condition that keeps and a
//! condition that drops — so a guard is proven to CONSTRAIN rather than be vacuously
//! true (an unconstraining guard would pass the keep half alone).

use crate::common::{interp_for, try_load_kb_with};
use anthill_core::eval::{EvalError, Interpreter, Value};

const SRC: &str = r#"
namespace test.wi730
  import anthill.prelude.{String, Int64, Option, List, Pair, Unit, Bool}
  import anthill.prelude.Relation.{where, join}
  import anthill.prelude.PartialEq.{eq, neq}
  import anthill.prelude.PartialOrd.{gte}
  import anthill.prelude.Bool.{and, or, not}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)

  sort Membership
    entity member(who: String, dept: String)
  end
  fact member(who: "alice", dept: "eng")
  fact member(who: "bob", dept: "sales")

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  rule member_row(?who, ?dept) :- member(who: ?who, dept: ?dept)

  -- ── and ────────────────────────────────────────────────────
  -- Both atoms hold of alice only.
  operation andKeeps() -> List[(name: String, age: Int64)] effects Error =
    person_row.where(lambda c -> and(eq(c.name, "alice"), eq(c.age, 30))).takeN(5)

  -- Same first atom, second contradicts it: the conjunction must DROP the row the
  -- first atom alone would keep (proof the second goal is really conjoined).
  operation andDrops() -> List[(name: String, age: Int64)] effects Error =
    person_row.where(lambda c -> and(eq(c.name, "alice"), eq(c.age, 99))).takeN(5)

  -- Three atoms — the spine nests, so "multiple predicates" is not capped at two.
  operation andThree() -> List[(name: String, age: Int64)] effects Error =
    person_row
      .where(lambda c -> and(eq(c.name, "alice"), and(gte(c.age, 18), neq(c.age, 25))))
      .takeN(5)

  -- ── or ─────────────────────────────────────────────────────
  -- One row per branch — neither atom alone would keep both.
  operation orKeepsBoth() -> List[(name: String, age: Int64)] effects Error =
    person_row.where(lambda c -> or(eq(c.name, "alice"), eq(c.age, 25))).takeN(5)

  -- Neither branch holds of anything: a disjunction is not vacuously true.
  operation orDropsAll() -> List[(name: String, age: Int64)] effects Error =
    person_row.where(lambda c -> or(eq(c.name, "zed"), eq(c.age, 99))).takeN(5)

  -- ── not ────────────────────────────────────────────────────
  -- Negation-as-failure over a column the relation's own goals already BOUND.
  operation notKeepsOther() -> List[(name: String, age: Int64)] effects Error =
    person_row.where(lambda c -> not(eq(c.name, "alice"))).takeN(5)

  -- Negating a condition nothing satisfies keeps EVERY row (the dual direction:
  -- the negation is not vacuously false either).
  operation notKeepsAll() -> List[(name: String, age: Int64)] effects Error =
    person_row.where(lambda c -> not(eq(c.name, "zed"))).takeN(5)

  -- ── mixed nesting ──────────────────────────────────────────
  -- `(name = alice AND age >= 18) OR NOT(age >= 18)`: alice via the left conjunct,
  -- bob only if the right disjunct's negation fires — it does not (bob is 25), so
  -- this keeps alice ALONE. A disjunction that ignored either operand would keep both.
  operation mixedNesting() -> List[(name: String, age: Int64)] effects Error =
    person_row
      .where(lambda c -> or(and(eq(c.name, "alice"), gte(c.age, 18)), not(gte(c.age, 18))))
      .takeN(5)

  -- ── join ───────────────────────────────────────────────────
  -- The join condition takes the same nesting: match on name = who AND an age bound.
  -- alice (30) and bob (25) both join by name; only alice clears 26.
  operation joinAnd() -> List[(name: String, age: Int64, who: String, dept: String)] effects Error =
    person_row.join(member_row, lambda (c, q) -> and(eq(c.name, q.who), gte(c.age, 26))).takeN(5)

  -- Same shape, second atom unsatisfiable → no joined pair survives.
  operation joinAndDrops() -> List[(name: String, age: Int64, who: String, dept: String)] effects Error =
    person_row.join(member_row, lambda (c, q) -> and(eq(c.name, q.who), gte(c.age, 99))).takeN(5)

  -- ANTI-join: the pairs whose name does NOT match — NAF over both rows' bound
  -- columns. alice/sales and bob/eng survive; the two matching pairs are dropped.
  operation joinNot() -> List[(name: String, age: Int64, who: String, dept: String)] effects Error =
    person_row.join(member_row, lambda (c, q) -> not(eq(c.name, q.who))).takeN(5)
end
"#;

/// The `(name, age)` (or merged) columns of each drained row, as `a/b/…` strings, in
/// drain order. Walks the `List` cons spine; each element is the row's named tuple.
fn rows(v: &Value) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = v.clone();
    while let Value::Entity { named, .. } = &cur {
        if named.is_empty() {
            break; // nil
        }
        let mut head: Option<Value> = None;
        let mut tail: Option<Value> = None;
        for (_k, x) in named.iter() {
            match x {
                Value::Tuple { .. } => head = Some(x.clone()),
                Value::Entity { .. } => tail = Some(x.clone()),
                _ => {}
            }
        }
        match (head, tail) {
            (Some(Value::Tuple { named: fields, .. }), Some(t)) => {
                out.push(
                    fields
                        .iter()
                        .map(|(_, x)| match x {
                            Value::Str(s) => s.clone(),
                            Value::Int(n) => n.to_string(),
                            other => panic!("unexpected column value {other:?}"),
                        })
                        .collect::<Vec<_>>()
                        .join("/"),
                );
                cur = t;
            }
            _ => break,
        }
    }
    out
}

fn drain(interp: &mut Interpreter, op: &str) -> Vec<String> {
    let v = interp
        .call(&format!("test.wi730.{op}"), &[])
        .unwrap_or_else(|e| panic!("{op} runs the filtered relation: {e:?}"));
    let mut r = rows(&v);
    r.sort();
    r
}

/// `and(p, q)` keeps a row only when BOTH atoms hold — and the second atom is really
/// conjoined: flipping it alone empties a filter the first atom would otherwise pass.
#[test]
fn wi730_where_conjunction_keeps_and_drops() {
    let mut interp = interp_for(SRC);
    assert_eq!(drain(&mut interp, "andKeeps"), vec!["alice/30"]);
    assert_eq!(
        drain(&mut interp, "andDrops"),
        Vec::<String>::new(),
        "`age = 99` must drop the row `name = alice` alone would keep"
    );
}

/// The conjunctive spine nests, so a condition can carry more than two atoms —
/// `lower_query` flattens the whole `conjunction` tree into one goal list.
#[test]
fn wi730_where_conjunction_of_three_atoms() {
    let mut interp = interp_for(SRC);
    assert_eq!(drain(&mut interp, "andThree"), vec!["alice/30"]);
}

/// `or(p, q)` keeps the rows either branch admits (neither atom alone keeps both) —
/// and is not vacuously true: a disjunction of two unsatisfiable atoms keeps nothing.
#[test]
fn wi730_where_disjunction_keeps_and_drops() {
    let mut interp = interp_for(SRC);
    assert_eq!(drain(&mut interp, "orKeepsBoth"), vec!["alice/30", "bob/25"]);
    assert_eq!(
        drain(&mut interp, "orDropsAll"),
        Vec::<String>::new(),
        "neither branch holds of any row → the disjunction keeps nothing"
    );
}

/// `not(p)` is negation-as-failure over a column the relation's OWN goals bound —
/// which is why `where_run` conjoins the condition AFTER the relation's query. It
/// both drops (the row `p` admits) and keeps (every row, when `p` admits none).
#[test]
fn wi730_where_negation_keeps_and_drops() {
    let mut interp = interp_for(SRC);
    assert_eq!(
        drain(&mut interp, "notKeepsOther"),
        vec!["bob/25"],
        "`not(name = alice)` drops alice and keeps bob"
    );
    assert_eq!(
        drain(&mut interp, "notKeepsAll"),
        vec!["alice/30", "bob/25"],
        "negating a condition nothing satisfies keeps every row"
    );
}

/// A mixed `or(and(…), not(…))` spine: each operand is compiled by the same
/// recursion, so depth costs nothing. Only the left conjunct fires here — a
/// disjunction that ignored either operand would keep a different row set.
#[test]
fn wi730_where_mixed_nesting() {
    let mut interp = interp_for(SRC);
    assert_eq!(drain(&mut interp, "mixedNesting"), vec!["alice/30"]);
}

/// `join` takes the same nesting through the same compiler: an `and` of the join
/// predicate and a per-row bound, in both directions.
#[test]
fn wi730_join_conjunction_keeps_and_drops() {
    let mut interp = interp_for(SRC);
    assert_eq!(
        drain(&mut interp, "joinAnd"),
        vec!["alice/30/alice/eng"],
        "both rows join by name; only alice clears `age >= 26`"
    );
    assert_eq!(
        drain(&mut interp, "joinAndDrops"),
        Vec::<String>::new(),
        "`age >= 99` must drop the pairs the name match alone would keep"
    );
}

/// `not` in a join condition is an ANTI-join — NAF over columns BOTH rows' queries
/// have bound by the time the condition runs (the condition is conjoined last).
#[test]
fn wi730_join_negation_is_an_antijoin() {
    let mut interp = interp_for(SRC);
    assert_eq!(
        drain(&mut interp, "joinNot"),
        vec!["alice/30/bob/sales", "bob/25/alice/eng"],
        "the anti-join keeps exactly the mismatched pairs"
    );
}

/// A condition outside the goal-expressible `Bool` subset is a LOUD compile error —
/// 052's analog of LINQ's "cannot translate to SQL". `ite` is `Bool`-valued and so
/// type-checks as the lambda's body, but it is not a predicate any rule or builtin
/// can prove: compiled verbatim it would be an atom nothing satisfies, and the
/// filtered relation would come back silently EMPTY. It must fail to LOAD instead.
#[test]
fn wi730_untranslatable_condition_is_a_load_error() {
    const SRC: &str = r#"
namespace test.wi730ite
  import anthill.prelude.{String, Int64, List, Bool}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.Bool.{ite}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  operation p() -> List[(name: String, age: Int64)] effects Error =
    person_row.where(lambda c -> ite(true, true, false)).takeN(5)
end
"#;
    match try_load_kb_with(SRC) {
        Err(errs) => assert!(
            // The macro DECLINES on an untranslatable condition (WI-722: a macro that
            // cannot expand keeps its template), so what surfaces is the kept
            // `guarded_of` template failing to type — loud, and naming the `where`
            // lowering. (Carrying the compiler's own "cannot translate" text out to the
            // user needs a macro DIAGNOSTIC channel, which WI-722 does not have.)
            errs.iter().any(|e| e.contains("guarded_of")),
            "expected the where lowering to fail loudly on an untranslatable condition, got: {errs:?}",
        ),
        Ok(_) => panic!(
            "a `where` whose condition is not goal-expressible must not load — \
             compiled verbatim it silently yields an empty relation"
        ),
    }
}

/// A bare column PROJECTION is not a condition. `where(λ c -> c.ok)` type-checks (the
/// column is `Bool`), and `anthill.reflect.field_access` is itself a registered
/// resolver builtin — so the goal-expressible head check alone would wave it through
/// and compile a projection into GOAL position, where it states nothing. The compiler
/// refuses it: a condition must COMPARE a column (`eq(c.ok, true)`), not name it.
#[test]
fn wi730_bare_column_projection_is_not_a_condition() {
    const SRC: &str = r#"
namespace test.wi730bare
  import anthill.prelude.{String, List, Bool}
  import anthill.prelude.Relation.{where}
  sort Person
    entity person(name: String, ok: Bool)
  end
  fact person(name: "alice", ok: true)
  rule person_row(?name, ?ok) :- person(name: ?name, ok: ?ok)
  operation p() -> List[(name: String, ok: Bool)] effects Error =
    person_row.where(lambda c -> c.ok).takeN(5)
end
"#;
    assert!(
        try_load_kb_with(SRC).is_err(),
        "a bare column projection in condition position must not load — compiled into \
         goal position it is a projection the resolver cannot read as a filter"
    );
}

/// The `!`-over-a-free-column hazard (the WI-728 `negate` dual). `where_run` conjoins
/// the condition AFTER the relation's goals, so every column a relation's own query
/// binds is bound before a negation reads it. A column the query does NOT bind (a free
/// head variable) is the residual case — and it must FLOUNDER LOUDLY, not quietly
/// answer as if the negation had succeeded.
#[test]
fn wi730_negation_over_an_unbound_column_flounders_loudly() {
    const SRC: &str = r#"
namespace test.wi730naf
  import anthill.prelude.{String, Int64, List, Bool}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}
  import anthill.prelude.Bool.{not}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  -- `other` is a free head var no body goal binds: the column stays UNBOUND.
  rule loose_row(?name, ?other) :- person(name: ?name)
  operation p() -> List[(name: String, other: String)] effects Error =
    loose_row.where(lambda c -> not(eq(c.other, "zed"))).takeN(5)
end
"#;
    let mut interp = interp_for(SRC);
    match interp.call("test.wi730naf.p", &[]) {
        Err(EvalError::Raised { payload }) => {
            let functor = match &payload {
                Value::Entity { functor, .. } => *functor,
                other => panic!("expected a floundered-relation entity payload, got {other:?}"),
            };
            assert_eq!(
                functor,
                interp
                    .kb()
                    .try_resolve_symbol("anthill.prelude.RelationFloundered.relation_floundered")
                    .expect("RelationFloundered must be in scope"),
                "a negation over an unbound column raises the flounder witness"
            );
        }
        other => panic!(
            "NAF over a column the relation never binds must RAISE, not answer: got {other:?}"
        ),
    }
}
