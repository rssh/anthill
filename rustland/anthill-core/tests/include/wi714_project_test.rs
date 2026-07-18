//! WI-714 (proposal 052) — `project`: SELECT columns of a relation via the distribute-dot
//! `r.(f1, f2)` (rename `r.(a: f1, b: f2)`; a single member `r.(f)` 1-collapses to `r.f`).
//!
//! Lifted over a relation, the name-keyed row tuple the distribute-dot desugars to (WI-639)
//! IS projection: the typer maps it to a `projected` query and stamps the kept columns'
//! schema. `projected` lowers as a resolver PASS-THROUGH (kb/execute.rs), so the column
//! restriction happens at 052's OWN materialization step — the runtime `project_run`
//! rebuilds the relation's materialized `columns` to the kept/renamed set, leaving the
//! query (and therefore the solutions) unchanged: a dropped column is still SOLVED, so the
//! row multiplicity is the source relation's (bag projection, OQ6). No lambda, so — unlike
//! where/join — NO compile-time macro: the typer synthesizes `project_run` directly.
//!
//! A bare rule-ref receiver's members desugar to `field_access(…, Ident)` and error before
//! the projection is recognized, so — like `where`/`join` (F1) — a bare rule ref is
//! `let`-bound first; a let-bound / computed relation value works directly.

use crate::common::{interp_for, try_load_kb_with};
use anthill_core::eval::Value;

const SRC: &str = r#"
namespace test.wi714project
  import anthill.prelude.{String, Int64, Option, List, Pair, Unit, Bool}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)   -- (name, age)

  -- A NAMED-ARG head: its columns are keyed by the head field key (`name`/`age`), not a
  -- positional var name — exercises that `project_run` matches those columns by the same
  -- canonical interned symbol (not only positional-var-named columns).
  rule person_named(name: ?name, age: ?age) :- person(name: ?name, age: ?age)

  -- SINGLE-column projection: rel.name : Relation[String] (1-collapse).
  operation names() -> List[String] effects Error =
    let rel = person_row
    let col = rel.name
    col.takeN(9)

  -- SINGLE-column via the distribute-dot 1-collapse: rel.(age) : Relation[Int64].
  operation ages() -> List[Int64] effects Error =
    let rel = person_row
    let col = rel.(age)
    col.takeN(9)

  -- MULTI-column projection (identity here): rel.(name, age) : Relation[(name, age)].
  -- The declared return type IS the projected schema — type-checking this annotation
  -- proves the typer stamped `Relation[T = (name: String, age: Int64)]`.
  operation both() -> List[(name: String, age: Int64)] effects Error =
    let rel = person_row
    let cols = rel.(name, age)
    cols.takeN(9)

  -- MULTI-column with RENAME: keep both, renamed (`name`→`person`, `age`→`years`). A
  -- SINGLE renamed member (`rel.(years: age)`) instead 1-collapses and drops the label
  -- (WI-639), so rename only manifests on a ≥2-column projection.
  operation renamed() -> List[(person: String, years: Int64)] effects Error =
    let rel = person_row
    let cols = rel.(person: name, years: age)
    cols.takeN(9)

  -- PROJECTION AFTER WHERE: filter, then project the surviving column.
  operation youngNames() -> List[String] effects Error =
    let rel = person_row
    let filtered = rel.where(lambda c -> eq(c.age, 25))
    let col = filtered.name
    col.takeN(9)

  -- MULTI-column projection over a COMPUTED (let-bound where-result) receiver: proves a
  -- projection composes on any relation VALUE, not only a bare rule reference.
  operation youngRows() -> List[(name: String, age: Int64)] effects Error =
    let filtered = person_row.where(lambda c -> eq(c.age, 25))
    let cols = filtered.(name, age)
    cols.takeN(9)

  -- WI-732: the same projection over an INLINE computed receiver — the `where` result is
  -- projected directly, with no intervening `let`. The declared return type is the projected
  -- schema, so this annotation type-checking is what proves ONE relation restricted to two
  -- columns rather than a tuple of two independent single-column relations.
  operation inlineYoung() -> List[(name: String, age: Int64)] effects Error =
    let cols = person_row.where(lambda c -> eq(c.age, 25)).(name, age)
    cols.takeN(9)

  -- SINGLE-column projection over a NAMED-ARG-head relation.
  operation namedNames() -> List[String] effects Error =
    let rel = person_named
    let col = rel.name
    col.takeN(9)

  -- ================================================================
  -- BAG MULTIPLICITY: projecting a column DROPS the other from the row but STILL SOLVES
  -- it, so a value duplicated across dropped-column values keeps its multiplicity.
  sort Owner
    entity owns(who: String, item: String)
  end
  fact owns(who: "alice", item: "cat")
  fact owns(who: "alice", item: "dog")
  fact owns(who: "bob", item: "fish")

  rule owns_row(?who, ?item) :- owns(who: ?who, item: ?item)   -- (who, item)

  -- project `who`, dropping `item`: alice appears TWICE (cat, dog), bob once.
  operation owners() -> List[String] effects Error =
    let rel = owns_row
    let col = rel.who
    col.takeN(9)
end
"#;

/// Walk a cons list of scalar-collapsed rows, collecting the `String` element of each.
fn drain_strings(v: Value) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = v;
    while let Value::Entity { named, .. } = &cur {
        if named.is_empty() {
            break;
        }
        let (mut head, mut tail) = (None, None);
        for (_k, x) in named.iter() {
            match x {
                Value::Str(s) => head = Some(s.clone()),
                Value::Entity { .. } => tail = Some(x.clone()),
                _ => {}
            }
        }
        match (head, tail) {
            (Some(s), Some(t)) => {
                out.push(s);
                cur = t;
            }
            _ => break,
        }
    }
    out
}

fn drain_ints(v: Value) -> Vec<i64> {
    let mut out = Vec::new();
    let mut cur = v;
    while let Value::Entity { named, .. } = &cur {
        if named.is_empty() {
            break;
        }
        let (mut head, mut tail) = (None, None);
        for (_k, x) in named.iter() {
            match x {
                Value::Int(n) => head = Some(*n),
                Value::Entity { .. } => tail = Some(x.clone()),
                _ => {}
            }
        }
        match (head, tail) {
            (Some(n), Some(t)) => {
                out.push(n);
                cur = t;
            }
            _ => break,
        }
    }
    out
}

/// `rel.name` selects the `name` column, 1-collapsing to `Relation[String]`.
#[test]
fn wi714_project_single_column() {
    let mut interp = interp_for(SRC);
    let r = interp.call("test.wi714project.names", &[]).expect("names runs");
    let mut got = drain_strings(r);
    got.sort();
    assert_eq!(got, vec!["alice".to_string(), "bob".to_string()]);
}

/// `rel.(age)` — a single-member distribute-dot 1-collapses to `rel.age : Relation[Int64]`.
#[test]
fn wi714_project_distribute_dot_1collapse() {
    let mut interp = interp_for(SRC);
    let r = interp.call("test.wi714project.ages", &[]).expect("ages runs");
    let mut got = drain_ints(r);
    got.sort();
    assert_eq!(got, vec![25, 30]);
}

/// `rel.(name, age)` projects BOTH columns; the row is the `(name, age)` tuple. The
/// declared return type `List[(name: String, age: Int64)]` type-checking IS the schema
/// test — it succeeds only if the typer stamped that exact projected schema.
#[test]
fn wi714_project_multi_column() {
    let mut interp = interp_for(SRC);
    let r = interp.call("test.wi714project.both", &[]).expect("both runs");
    let mut rows = 0usize;
    let mut names: Vec<String> = Vec::new();
    let mut ages: Vec<i64> = Vec::new();
    let mut cur = r;
    while let Value::Entity { named, .. } = &cur {
        if named.is_empty() {
            break;
        }
        let (mut tuple, mut tail) = (None, None);
        for (_k, x) in named.iter() {
            match x {
                Value::Tuple { .. } => tuple = Some(x.clone()),
                Value::Entity { .. } => tail = Some(x.clone()),
                _ => {}
            }
        }
        match (tuple, tail) {
            (Some(Value::Tuple { named: fields, .. }), Some(t)) => {
                rows += 1;
                for (_k, v) in fields.iter() {
                    match v {
                        Value::Str(s) => names.push(s.clone()),
                        Value::Int(n) => ages.push(*n),
                        other => panic!("unexpected projected-column value {other:?}"),
                    }
                }
                cur = t;
            }
            _ => break,
        }
    }
    names.sort();
    ages.sort();
    assert_eq!(rows, 2, "both persons projected");
    assert_eq!(names, vec!["alice".to_string(), "bob".to_string()]);
    assert_eq!(ages, vec![25, 30]);
}

/// `rel.(person: name, years: age)` RENAMES both columns. The row is a `(person: String,
/// years: Int64)` tuple — proves each result key differs from its source column, keyed by
/// the RESULT name at both the type (the `List[(person, years)]` annotation) and the value
/// (the materialized tuple's field keys).
#[test]
fn wi714_project_rename() {
    let mut interp = interp_for(SRC);
    let r = interp.call("test.wi714project.renamed", &[]).expect("renamed runs");
    let mut rows = 0usize;
    let mut cur = r;
    while let Value::Entity { named, .. } = &cur {
        if named.is_empty() {
            break;
        }
        let (mut tuple, mut tail) = (None, None);
        for (_k, x) in named.iter() {
            match x {
                Value::Tuple { .. } => tuple = Some(x.clone()),
                Value::Entity { .. } => tail = Some(x.clone()),
                _ => {}
            }
        }
        match (tuple, tail) {
            (Some(Value::Tuple { named: fields, .. }), Some(t)) => {
                rows += 1;
                let keys: Vec<String> =
                    fields.iter().map(|(k, _)| interp.kb().resolve_sym(*k).to_string()).collect();
                assert!(
                    keys.iter().any(|k| k.ends_with("person"))
                        && keys.iter().any(|k| k.ends_with("years")),
                    "renamed keys person/years, got {keys:?}"
                );
                cur = t;
            }
            _ => break,
        }
    }
    assert_eq!(rows, 2, "both rows projected + renamed");
}

/// Projection COMPOSES with `where`: filter to age = 25, then project `name` → ["bob"].
#[test]
fn wi714_project_after_where() {
    let mut interp = interp_for(SRC);
    let r = interp.call("test.wi714project.youngNames", &[]).expect("youngNames runs");
    let got = drain_strings(r);
    assert_eq!(got, vec!["bob".to_string()], "only bob is 25");
}

/// A MULTI-column projection over a COMPUTED, let-bound receiver (`filtered = r.where(..)`)
/// works — projection composes on any relation VALUE. (An INLINE chain
/// `r.where(..).(f1,f2)` instead hits the WI-443 multi-segment dot-chain limitation `where`/
/// `join` share, a LOUD error — see `wi714_project_inline_chain_receiver_errors`.)
#[test]
fn wi714_project_multi_over_computed_receiver() {
    let mut interp = interp_for(SRC);
    let r = interp.call("test.wi714project.youngRows", &[]).expect("youngRows runs");
    let mut rows = 0usize;
    let mut cur = r;
    while let Value::Entity { named, .. } = &cur {
        if named.is_empty() {
            break;
        }
        let (mut tuple, mut tail) = (None, None);
        for (_k, x) in named.iter() {
            match x {
                Value::Tuple { .. } => tuple = Some(()),
                Value::Entity { .. } => tail = Some(x.clone()),
                _ => {}
            }
        }
        match (tuple, tail) {
            (Some(()), Some(t)) => {
                rows += 1;
                cur = t;
            }
            _ => break,
        }
    }
    assert_eq!(rows, 1, "only bob (age 25) survives the filter, then projects to (name, age)");
}

/// Projection over a NAMED-ARG-head relation (`person_named(name: ?, age: ?)`): the columns
/// are keyed by the head field key, and `project_run` matches them by the same canonical
/// interned symbol as a positional-var-named column.
#[test]
fn wi714_project_named_arg_head() {
    let mut interp = interp_for(SRC);
    let r = interp.call("test.wi714project.namedNames", &[]).expect("namedNames runs");
    let mut got = drain_strings(r);
    got.sort();
    assert_eq!(got, vec!["alice".to_string(), "bob".to_string()]);
}

/// BAG MULTIPLICITY: `owns_row.who` projects `who`, dropping `item` — but `item` is still
/// SOLVED, so "alice" (who owns two items) appears TWICE. Proves the drop restricts the
/// materialized columns WITHOUT deduplicating rows (052 OQ6) — the query is unchanged.
#[test]
fn wi714_project_preserves_bag_multiplicity() {
    let mut interp = interp_for(SRC);
    let r = interp.call("test.wi714project.owners", &[]).expect("owners runs");
    let mut got = drain_strings(r);
    got.sort();
    assert_eq!(
        got,
        vec!["alice".to_string(), "alice".to_string(), "bob".to_string()],
        "alice twice (cat, dog) — the dropped `item` column is still solved"
    );
}

/// WI-732 item (1): a MULTI-column projection over an INLINE COMPUTED receiver
/// `r.where(..).(f1, f2)` — no `let` — projects. The declared return type IS the projected
/// schema, so type-checking it proves ONE relation restricted to two columns.
///
/// Before WI-732 this silently typed as a TUPLE OF INDEPENDENT SINGLE-COLUMN RELATIONS
/// (`(name: Relation[String], age: Relation[Int64])`) — see
/// `wi714_project_inline_chain_is_not_a_tuple_of_relations`, which pins that directly. The
/// ticket recorded it as "a LOUD error (the WI-443 chain limit)"; measured, it was neither
/// loud nor a chain-limit error. `convert.rs` distributes ONE receiver over the members as a
/// shared TermId, but that sharing does not survive as a shared `Rc`, so the receiver-identity
/// test (leaf symbol only) failed and each member typed as its own single-column projection.
#[test]
fn wi714_project_inline_chain_computed_receiver() {
    let mut interp = interp_for(SRC);
    let r = interp.call("test.wi714project.inlineYoung", &[]).expect("inlineYoung runs");
    let mut rows = 0usize;
    let mut cur = r;
    while let Value::Entity { named, .. } = &cur {
        if named.is_empty() {
            break;
        }
        let (mut tuple, mut tail) = (None, None);
        for (_k, x) in named.iter() {
            match x {
                Value::Tuple { .. } => tuple = Some(()),
                Value::Entity { .. } => tail = Some(x.clone()),
                _ => {}
            }
        }
        match (tuple, tail) {
            (Some(()), Some(t)) => {
                rows += 1;
                cur = t;
            }
            _ => break,
        }
    }
    assert_eq!(rows, 1, "only bob (age 25) survives the inline filter, then projects to (name, age)");
}

/// WI-732 item (1), the NEGATIVE control that makes the test above non-vacuous: the inline
/// chain must NOT type as a tuple of independent single-column relations. This is the exact
/// shape it silently produced before WI-732 — it loaded CLEAN then — so this annotation
/// failing to type-check is what proves the projection reading won.
#[test]
fn wi714_project_inline_chain_is_not_a_tuple_of_relations() {
    const INLINE: &str = r#"
namespace test.wi714projinline
  import anthill.prelude.{String, Int64, List, Bool, Option, Relation}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  operation inline() -> (name: Relation[T = String], age: Relation[T = Int64]) effects Error =
    person_row.where(lambda c -> eq(c.age, 30)).(name, age)
end
"#;
    let joined = match try_load_kb_with(INLINE) {
        Ok(_) => panic!(
            "the inline chain typed as a TUPLE OF RELATIONS — the pre-WI-732 silent \
             mis-reading, in which each member is its own single-column projection"
        ),
        Err(e) => e.join("\n"),
    };
    assert!(
        joined.contains("T = (name: String, age: Int64)"),
        "expected the mismatch to report the PROJECTED relation as the actual type, got: {joined}"
    );
}

/// A hand-written tuple of column accesses on TWO SEPARATE computed receivers keeps its
/// tuple reading — the receiver-identity test is SOURCE-SPAN based, so it matches only ONE
/// receiver duplicated by the distribute-dot desugaring, never two the user genuinely wrote.
/// Without this distinction the span rung would collapse two independent expressions (and
/// their two evaluations) into one.
#[test]
fn wi714_project_two_written_receivers_stay_a_tuple() {
    const TWO: &str = r#"
namespace test.wi714projtwo
  import anthill.prelude.{String, Int64, List, Bool, Option, Relation}
  import anthill.prelude.Relation.{where}
  import anthill.prelude.PartialEq.{eq}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  operation two() -> List[(name: String, age: Int64)] effects Error =
    let cols = (name: person_row.where(lambda c -> eq(c.age, 30)).name,
                age: person_row.where(lambda c -> eq(c.age, 30)).age)
    cols.takeN(9)
end
"#;
    // Same body shape as `inlineYoung`, which DOES project and therefore DOES answer
    // `takeN` — so the two differ only in whether the receiver was written once or twice.
    let joined = match try_load_kb_with(TWO) {
        Ok(_) => panic!(
            "two separately-written receivers collapsed into ONE projection — the span rung \
             must match only a receiver duplicated by the distribute-dot desugaring"
        ),
        Err(e) => e.join("\n"),
    };
    assert!(
        joined.contains("takeN"),
        "expected the tuple reading to surface as `takeN` having no such member on a tuple, \
         got: {joined}"
    );
}

/// Projecting a column that is NOT in the relation's schema is a loud LOAD error (no such
/// member on the receiver's sort), never a silent empty projection.
#[test]
fn wi714_project_nonexistent_column_errors() {
    const BAD: &str = r#"
namespace test.wi714projbad
  import anthill.prelude.{String, Int64, List, Bool}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  operation bad() -> List[String] effects Error =
    let rel = person_row
    let col = rel.nosuchcolumn
    col.takeN(9)
end
"#;
    let joined = match try_load_kb_with(BAD) {
        Ok(_) => panic!("projecting a nonexistent column must error, but it loaded"),
        Err(e) => e.join("\n"),
    };
    assert!(
        joined.contains("nosuchcolumn") && joined.contains("dot dispatch"),
        "expected a loud no-such-member error naming the column, got: {joined}"
    );
}
