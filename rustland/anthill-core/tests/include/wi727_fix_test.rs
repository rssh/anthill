//! WI-727 (proposal 056) — `fix`: RESTRICT relation columns to constants and DROP them,
//! the driving client of VARIADIC ARGUMENT CAPTURE. `r.fix(x: 1, z: 2)` keeps the solutions
//! whose columns `x`/`z` equal the constants, then removes those columns — `≡ where(eq(x,
//! 1)) + project`.
//!
//! fix is an ORDINARY operation: its dynamic column arguments (`x`/`z` are columns of the
//! receiver, not declared params) are collected by the `...args: R` capture parameter into a
//! named-tuple record, whose type binds `R`; the schema narrows via the `Without[T = p.T,
//! Drop = R]` type constructor (the dual of join's `Concat`). NO compile-time macro, NOTHING
//! keyed on fix's identity in the typer. The declared return types below (`List[(b, c)]`
//! etc.) type-check ONLY if the typer stamped the exact `Without`-reduced schema.
//!
//! Like where/project (F1), a bare rule-ref receiver is `let`-bound first.

use crate::common::{interp_for, try_load_kb_with};
use anthill_core::eval::Value;

const SRC: &str = r#"
namespace test.wi727fix
  import anthill.prelude.{String, Int64, Option, List, Pair, Unit, Bool}
  import anthill.prelude.Relation.{fix}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)
  fact person(name: "carol", age: 30)

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)   -- (name, age)

  -- A NAMED-ARG head: columns keyed by the head field key (`name`/`age`), not a
  -- positional var name — exercises that the captured field symbol (the use-site label)
  -- matches the column by the same canonical interned symbol.
  rule person_named(name: ?name, age: ?age) :- person(name: ?name, age: ?age)

  -- fix over a NAMED-ARG-head relation: `age` (the drop) must match the named-head column.
  operation named_head_at_30() -> List[String] effects Error =
    let rel = person_named
    let f = rel.fix(age: 30)
    f.takeN(9)

  -- MIXED capture: the PREFIX form binds `p` as a NAMED argument matching the declared
  -- parameter, while `age` is a leftover captured into the record — exercises the general
  -- matched-named + captured partition (not just fix's all-leftover dot form).
  operation mixed_prefix_at_30() -> List[String] effects Error =
    let rel = person_row
    let f = fix(p: rel, age: 30)
    f.takeN(9)

  -- fix age = 30, DROP age → Relation[String] (the sole remaining column `name`,
  -- 1-collapsed). Keeps alice & carol (age 30), excludes bob (25).
  operation names_at_30() -> List[String] effects Error =
    let rel = person_row
    let f = rel.fix(age: 30)
    f.takeN(9)

  -- fix name = "alice", DROP name → Relation[Int64] (`age`). Keeps only alice's row.
  operation ages_of_alice() -> List[Int64] effects Error =
    let rel = person_row
    let f = rel.fix(name: "alice")
    f.takeN(9)

  -- EMPTY capture: r.fix() → R = () → Without[T, ()] = T (identity) → Relation[(name, age)].
  operation identity_fix() -> List[(name: String, age: Int64)] effects Error =
    let rel = person_row
    let f = rel.fix()
    f.takeN(9)

  sort Triple
    entity triple(a: Int64, b: Int64, c: Int64)
  end
  fact triple(a: 1, b: 2, c: 3)
  fact triple(a: 1, b: 20, c: 30)
  fact triple(a: 9, b: 2, c: 3)

  rule triple_row(?a, ?b, ?c) :- triple(a: ?a, b: ?b, c: ?c)   -- (a, b, c)

  -- fix a = 1, DROP a → Relation[(b, c)] (TWO remaining columns — a named tuple, not a
  -- 1-collapse). Keeps the two a=1 rows. The declared `List[(b, c)]` return IS the schema
  -- test: it type-checks only if `Without` dropped exactly `a`.
  operation bc_where_a1() -> List[(b: Int64, c: Int64)] effects Error =
    let rel = triple_row
    let f = rel.fix(a: 1)
    f.takeN(9)

  -- fix a = 1 AND c = 3 (TWO captured constants), DROP both → Relation[Int64] (`b`). Keeps
  -- only (a=1, b=2, c=3) → b = 2.
  operation b_where_a1_c3() -> List[Int64] effects Error =
    let rel = triple_row
    let f = rel.fix(a: 1, c: 3)
    f.takeN(9)
end
"#;

/// Walk a cons list of scalar-collapsed `String` rows.
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

/// Walk a cons list of scalar-collapsed `Int64` rows.
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

/// Walk a cons list of `(b, c)` tuple rows, collecting each row's two ints in field order.
fn drain_int_pairs(v: Value) -> Vec<(i64, i64)> {
    let mut out = Vec::new();
    let mut cur = v;
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
                let ints: Vec<i64> = fields
                    .iter()
                    .filter_map(|(_k, v)| match v {
                        Value::Int(n) => Some(*n),
                        _ => None,
                    })
                    .collect();
                assert_eq!(ints.len(), 2, "each row is a (b, c) pair");
                out.push((ints[0], ints[1]));
                cur = t;
            }
            _ => break,
        }
    }
    out
}

/// fix a column to a constant, drop it: the sole remaining column 1-collapses, and only the
/// matching rows survive (alice & carol at age 30).
#[test]
fn wi727_fix_restrict_and_drop_1collapse() {
    let mut interp = interp_for(SRC);
    let r = interp.call("test.wi727fix.names_at_30", &[]).expect("names_at_30 runs");
    let mut got = drain_strings(r);
    got.sort();
    assert_eq!(got, vec!["alice".to_string(), "carol".to_string()]);
}

/// fix the OTHER column (name), leaving age: proves the drop is by name, not position.
#[test]
fn wi727_fix_restrict_other_column() {
    let mut interp = interp_for(SRC);
    let r = interp.call("test.wi727fix.ages_of_alice", &[]).expect("ages_of_alice runs");
    assert_eq!(drain_ints(r), vec![30]);
}

/// fix over a NAMED-ARG-head relation drops the head-keyed column by name.
#[test]
fn wi727_fix_named_arg_head() {
    let mut interp = interp_for(SRC);
    let r = interp.call("test.wi727fix.named_head_at_30", &[]).expect("named_head_at_30 runs");
    let mut got = drain_strings(r);
    got.sort();
    assert_eq!(got, vec!["alice".to_string(), "carol".to_string()]);
}

/// MIXED capture: the prefix `fix(p: rel, age: 30)` binds `p` (a declared parameter) AND
/// captures `age` — proves the mechanism partitions matched-named from captured arguments,
/// not just fix's all-leftover dot form.
#[test]
fn wi727_fix_mixed_prefix() {
    let mut interp = interp_for(SRC);
    let r = interp.call("test.wi727fix.mixed_prefix_at_30", &[]).expect("mixed_prefix_at_30 runs");
    let mut got = drain_strings(r);
    got.sort();
    assert_eq!(got, vec!["alice".to_string(), "carol".to_string()]);
}

/// Empty capture `r.fix()` is the identity — `Without[T, ()] = T` — so all rows survive
/// with the full `(name, age)` schema (the `List[(name, age)]` return type-checks).
#[test]
fn wi727_fix_empty_is_identity() {
    let mut interp = interp_for(SRC);
    let r = interp.call("test.wi727fix.identity_fix", &[]).expect("identity_fix runs");
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
            (Some(_), Some(t)) => {
                rows += 1;
                cur = t;
            }
            _ => break,
        }
    }
    assert_eq!(rows, 3, "identity fix keeps all three persons with full schema");
}

/// Drop ONE of three columns → a TWO-column named-tuple schema (not a 1-collapse). Both
/// a=1 rows survive; the `List[(b, c)]` return type-checking proves the reduced schema.
#[test]
fn wi727_fix_drop_one_of_three() {
    let mut interp = interp_for(SRC);
    let r = interp.call("test.wi727fix.bc_where_a1", &[]).expect("bc_where_a1 runs");
    let mut got = drain_int_pairs(r);
    got.sort();
    assert_eq!(got, vec![(2, 3), (20, 30)]);
}

/// TWO captured constants drop TWO columns → the sole remaining `b` 1-collapses; only the
/// row matching BOTH (a=1, c=3) survives (b = 2).
#[test]
fn wi727_fix_two_constants() {
    let mut interp = interp_for(SRC);
    let r = interp.call("test.wi727fix.b_where_a1_c3", &[]).expect("b_where_a1_c3 runs");
    assert_eq!(drain_ints(r), vec![2]);
}

/// A captured field naming NO column of the receiver schema is a LOAD error — the meaning
/// the otherwise-unconstrained capture is given lives in the `Without` reduction (§2.2).
#[test]
fn wi727_fix_unknown_column_is_load_error() {
    let src = r#"
namespace test.wi727fixbad
  import anthill.prelude.{String, Int64, List}
  import anthill.prelude.Relation.{fix}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  operation bad() -> List[String] effects Error =
    let rel = person_row
    let f = rel.fix(nosuch: 1)
    f.takeN(9)
end
"#;
    let err = match try_load_kb_with(src) {
        Err(e) => e,
        Ok(_) => panic!("fixing a non-column must be a load error"),
    };
    let joined = err.join("\n");
    assert!(
        joined.contains("nosuch") || joined.to_lowercase().contains("without"),
        "error should name the missing column / Without reduction; got: {joined}"
    );
}

/// A captured constant whose type mismatches its column is a LOAD error (the type check
/// that lives in the `Without` reduction — `age` is `Int64`, `"x"` is `String`).
#[test]
fn wi727_fix_type_mismatch_is_load_error() {
    let src = r#"
namespace test.wi727fixty
  import anthill.prelude.{String, Int64, List}
  import anthill.prelude.Relation.{fix}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  operation bad() -> List[String] effects Error =
    let rel = person_row
    let f = rel.fix(age: "notanint")
    f.takeN(9)
end
"#;
    let err = match try_load_kb_with(src) {
        Err(e) => e,
        Ok(_) => panic!("a type-mismatched fix must be a load error"),
    };
    assert!(!err.is_empty(), "expected a loud diagnostic");
}

/// TWO variadic capture parameters is ambiguous — a LOAD error ("at most one, trailing").
#[test]
fn wi727_two_capture_params_is_load_error() {
    let src = r#"
namespace test.wi727twocap
  import anthill.prelude.{Int64}
  operation two_captures[A, B](...x: A, ...y: B) -> Int64 = 0
end
"#;
    let err = match try_load_kb_with(src) {
        Err(e) => e,
        Ok(_) => panic!("two capture parameters must be a load error"),
    };
    let joined = err.join("\n");
    assert!(
        joined.contains("at most one variadic capture"),
        "error should reject the second `...`; got: {joined}"
    );
}

/// A variadic capture parameter that is NOT last leaves the following parameters'
/// matching undefined — a LOAD error ("must be the LAST parameter").
#[test]
fn wi727_non_trailing_capture_is_load_error() {
    let src = r#"
namespace test.wi727nontrail
  import anthill.prelude.{Int64}
  operation nontrailing[A](...x: A, y: Int64) -> Int64 = 0
end
"#;
    let err = match try_load_kb_with(src) {
        Err(e) => e,
        Ok(_) => panic!("a non-trailing capture must be a load error"),
    };
    let joined = err.join("\n");
    assert!(
        joined.contains("must be the LAST parameter"),
        "error should require the capture to be trailing; got: {joined}"
    );
}
