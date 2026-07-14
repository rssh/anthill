//! WI-714 (proposal 052) — C2/C3: a rule cited BY NAME (bare unqualified) resolves
//! to a `Relation[T]` VALUE — C3 typer arm in `check_bare_ref` (schema `T` =
//! named tuple of the free head params, 1-collapsed / `Unit`, `E = {Error}`) + C2
//! eval arm in `reduce_var` (builds the `Value::Relation` carrying
//! `pattern_query(head(?cols))` + columns). Because `Relation provides
//! LogicalStream provides Stream`, the reference consumes through the ordinary
//! Stream API — `splitFirst` (the primitive, `Relation.splitFirst` host builtin →
//! C1 `MaterializedResolver`) and the body-backed combinators built on it
//! (`takeN`, which drains the whole stream). These drive the full surface
//! end-to-end from source.

use anthill_core::eval::Value;

use crate::common::{interp_for, try_load_kb_with};

const SRC: &str = r#"
namespace test.wi714ref
  import anthill.prelude.{String, Int64, Option, List, Pair}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)

  -- one free head variable → Relation[String] (1-collapse)
  rule person_name(?name) :- person(name: ?name, age: ?)

  -- two free head variables → Relation[(name: String, age: Int64)] (named tuple)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  -- zero free head variables → Relation[Unit] (membership; provable ⇔ non-empty)
  rule has_alice() :- person(name: "alice", age: ?)

  -- splitFirst directly: the Relation primitive. Runs the query one step and
  -- materializes (1-collapse) the first row to a `String`.
  operation firstName() -> Option[String] effects Error =
    let r = person_name
    match r.splitFirst
      case some(pair(h, _)) -> some(h)
      case none() -> none()

  -- takeN: an inherited Stream combinator (body-backed, calls splitFirst) — drains
  -- the whole relation as a stream into a `List[String]`.
  operation allNames() -> List[String] effects Error =
    let r = person_name
    r.takeN(5)

  -- multi-column: each row is a named tuple (name, age).
  operation allRows() -> List[(name: String, age: Int64)] effects Error =
    let r = person_row
    r.takeN(5)

  -- 0-column membership relation: is it non-empty? (each proof materializes Unit)
  operation aliceIsEmpty() -> Bool effects Error =
    let r = has_alice
    r.isEmpty
end
"#;

/// `splitFirst` on a bare rule reference: the reference types as `Relation[String]`
/// (C3) and evaluates to a `Value::Relation` (C2); `Relation.splitFirst` runs the
/// query one step, materializing (1-collapse) the first row to a `String`.
#[test]
fn wi714_bare_rule_reference_split_first() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi714ref.firstName", &[])
        .expect("firstName() runs the relation via splitFirst");
    // `some(<name>)` — the payload rides positionally (`some(h)`); unwrap it.
    let inner = match &r {
        Value::Entity { pos, named, .. } if !pos.is_empty() => pos[0].clone(),
        Value::Entity { named, .. } if !named.is_empty() => named[0].1.clone(),
        other => panic!("expected some(name), got {other:?}"),
    };
    match &inner {
        Value::Str(s) => assert!(
            s == "alice" || s == "bob",
            "splitFirst materializes a person name (1-collapse to String), got {s:?}"
        ),
        other => panic!("expected a String element (1-collapse), got {other:?}"),
    }
}

/// The full inherited Stream API: `takeN` (built on `splitFirst`) drains the whole
/// relation as a stream — every solution materialized (1-collapse) into a
/// `List[String]`.
#[test]
fn wi714_bare_rule_reference_drains_via_takeN() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi714ref.allNames", &[])
        .expect("allNames() drains the relation via takeN");
    let mut got = collect_string_list(&r);
    got.sort();
    assert_eq!(
        got,
        vec!["alice".to_string(), "bob".to_string()],
        "takeN drains every solution, each materialized (1-collapse) to its String"
    );
}

/// Multi-column schema: two free head vars → each row is a named tuple
/// `(name, age)`, NOT 1-collapsed. `takeN` drains them into a `List` of tuples.
#[test]
fn wi714_multi_column_rows_are_named_tuples() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi714ref.allRows", &[])
        .expect("allRows() drains the 2-column relation");
    // Walk the cons list; each element is a `Value::Tuple { named: [(name,…),(age,…)] }`.
    let mut rows: Vec<(String, i64)> = Vec::new();
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
                let name = fields.iter().find_map(|(_, v)| match v {
                    Value::Str(s) => Some(s.clone()),
                    _ => None,
                });
                let age = fields.iter().find_map(|(_, v)| match v {
                    Value::Int(n) => Some(*n),
                    _ => None,
                });
                rows.push((name.expect("name col"), age.expect("age col")));
                cur = t;
            }
            _ => break,
        }
    }
    rows.sort();
    assert_eq!(
        rows,
        vec![("alice".to_string(), 30), ("bob".to_string(), 25)],
        "each solution materializes onto the free vars as a (name, age) named tuple"
    );
}

/// Zero free head vars → a membership relation (`Relation[Unit]`): non-empty ⇔
/// provable. `has_alice` is provable, so `isEmpty` is `false`.
#[test]
fn wi714_zero_column_membership_relation() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi714ref.aliceIsEmpty", &[])
        .expect("aliceIsEmpty() runs the 0-column relation");
    assert_eq!(
        r.as_bool(),
        Some(false),
        "a provable membership relation is non-empty"
    );
}

// ── Edge cases surfaced by review: nonlinear / multi-clause / compound heads ──

const SRC2: &str = r#"
namespace test.wi714edge
  import anthill.prelude.{String, Int64, List}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)

  sort Pet
    entity pet(petName: String)
  end
  fact pet(petName: "rex")

  -- nonlinear head var: ?n fills BOTH slots but is ONE column → Relation[String].
  rule twin(?n, ?n) :- person(name: ?n, age: ?)

  -- uniform two-clause relation: both clauses free the same slot (Pos 0), both
  -- String → Relation[String]; the union of solutions (person names + pet names).
  rule any_name(?nm) :- person(name: ?nm, age: ?)
  rule any_name(?nm) :- pet(petName: ?nm)

  operation twins() -> List[String] effects Error =
    let r = twin
    r.takeN(5)

  operation anyNames() -> List[String] effects Error =
    let r = any_name
    r.takeN(5)
end
"#;

/// A nonlinear head variable (`twin(?n, ?n)`) is ONE logical column: the schema
/// collapses to `Relation[String]` (not a duplicate-named 2-tuple), and the rows
/// materialize (1-collapse) to the element.
#[test]
fn wi714_nonlinear_head_var_is_single_column() {
    let mut interp = interp_for(SRC2);
    let r = interp
        .call("test.wi714edge.twins", &[])
        .expect("twins() drains the nonlinear relation");
    let mut got = collect_string_list(&r);
    got.sort();
    assert_eq!(
        got,
        vec!["alice".to_string(), "bob".to_string()],
        "a nonlinear head var is a single String column (dedup), 1-collapsed per row"
    );
}

/// A uniform two-clause relation unions its clauses' solutions, and its column type
/// is the lub across clauses (here both `String`).
#[test]
fn wi714_uniform_multiclause_unions_solutions() {
    let mut interp = interp_for(SRC2);
    let r = interp
        .call("test.wi714edge.anyNames", &[])
        .expect("anyNames() drains the two-clause relation");
    let mut got = collect_string_list(&r);
    got.sort();
    assert_eq!(
        got,
        vec!["alice".to_string(), "bob".to_string(), "rex".to_string()],
        "both clauses contribute solutions (person names ∪ pet names)"
    );
}

/// A COMPOUND head argument (`boxed(some(?x))`) is rejected loudly at LOAD — not
/// silently run as an empty relation (its raw DeBruijn would unify reflexively-only
/// and yield zero solutions). "Loud error over silent skip."
#[test]
fn wi714_compound_head_arg_rejected() {
    let src = r#"
namespace test.wi714compound
  import anthill.prelude.{String, Int64, Option, List}
  import anthill.prelude.Option.{some}

  sort Person
    entity person(name: String, age: Int64)
  end

  rule boxed(some(?name)) :- person(name: ?name, age: ?)

  operation names() -> List[Option[String]] effects Error =
    let r = boxed
    r.takeN(5)
end
"#;
    let errs = try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("compound head argument")),
        "a compound head argument must be a loud load error, got: {errs:?}"
    );
}

/// Heterogeneous multi-clause (one clause pins a slot the other frees) is rejected
/// loudly — silently dropping the pinning clause would under-approximate the schema
/// (unsound: a consumer would see a narrower column type than the relation yields).
#[test]
fn wi714_heterogeneous_clauses_rejected() {
    let src = r#"
namespace test.wi714hetero
  import anthill.prelude.{String, Int64, List}

  sort Person
    entity person(name: String, age: Int64)
  end
  sort Tag
    entity tag(label: String)
  end

  -- clause 1 frees BOTH slots; clause 2 pins slot 0 to a constant (differing
  -- free-slot interface) — not yet supported.
  rule mixed(?a, ?b) :- person(name: ?a, age: ?), tag(label: ?b)
  rule mixed("x", ?b) :- tag(label: ?b)

  operation rows() -> List[(a: String, b: String)] effects Error =
    let r = mixed
    r.takeN(5)
end
"#;
    let errs = try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("differing free-variable slots")),
        "heterogeneous clauses must be a loud load error, got: {errs:?}"
    );
}

/// Decode an anthill `List[String]` value (`cons(head, tail)` chain, `nil` end)
/// into a `Vec<String>`.
fn collect_string_list(v: &Value) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = v.clone();
    loop {
        match cur {
            Value::Entity { functor: _, ref named, .. } if !named.is_empty() => {
                // cons(head: <String>, tail: <List>)
                let mut head: Option<String> = None;
                let mut tail: Option<Value> = None;
                for (_k, val) in named.iter() {
                    match val {
                        Value::Str(s) => head = Some(s.clone()),
                        Value::Entity { .. } => tail = Some(val.clone()),
                        _ => {}
                    }
                }
                match (head, tail) {
                    (Some(h), Some(t)) => {
                        out.push(h);
                        cur = t;
                    }
                    _ => break,
                }
            }
            // nil / empty entity (no fields) ends the list.
            _ => break,
        }
    }
    out
}
