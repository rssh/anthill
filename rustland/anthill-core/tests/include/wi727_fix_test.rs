//! WI-727 (proposal 056) — `fix`: RESTRICT relation columns to given VALUES and DROP them,
//! the driving client of VARIADIC ARGUMENT CAPTURE. `r.fix(x: 1, z: 2)` keeps the solutions
//! whose columns `x`/`z` equal those values, then removes those columns — `≡ where(eq(x,
//! 1)) + project`.
//!
//! The fixed value is an ORDINARY EXPRESSION of the column's type, not a literal and not a
//! compile-time constant: 052's "constant" means ROW-INDEPENDENT (as against `where`'s
//! per-row predicate), which an argument evaluated once at the call is by construction. The
//! `wi727_fix_value_may_be_*` tests drive that; WI-735, which was filed to "relax a literal
//! gate", was rejected because no such gate exists.
//!
//! THE `≡` ONLY BECAME TRUE WITH WI-1127. This header, and the stdlib declaration, always
//! stated it — and while `where`'s OWN operand compiler admitted only a column or a
//! literal it was FALSE for exactly the non-literal `v` that `fix` accepts, because that
//! `where` spelling did not load. WI-1127 lifted the gate (a row-independent operand is
//! captured as a recipe parameter), so the two operand sets now coincide;
//! `wi1127_condition_param_test` drives the `where`/`join` half.
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
  import anthill.prelude.PartialEq.{eq}

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
  operation named_head_at_30() -> List[(name: String)] effects Error =
    let rel = person_named
    let f = rel.fix(age: 30)
    f.takeN(9)

  -- MIXED capture: the PREFIX form binds `p` as a NAMED argument matching the declared
  -- parameter, while `age` is a leftover captured into the record — exercises the general
  -- matched-named + captured partition (not just fix's all-leftover dot form).
  operation mixed_prefix_at_30() -> List[(name: String)] effects Error =
    let rel = person_row
    let f = fix(p: rel, age: 30)
    f.takeN(9)

  -- fix age = 30, DROP age → Relation[(name: String)] — the sole remaining column keeps
  -- its NAME (WI-20260818-YQB1Y). Keeps alice & carol (age 30), excludes bob (25).
  operation names_at_30() -> List[(name: String)] effects Error =
    let rel = person_row
    let f = rel.fix(age: 30)
    f.takeN(9)

  -- fix name = "alice", DROP name → Relation[(age: Int64)]. Keeps only alice's row.
  operation ages_of_alice() -> List[(age: Int64)] effects Error =
    let rel = person_row
    let f = rel.fix(name: "alice")
    f.takeN(9)

  -- EMPTY capture: r.fix() → R = () → Without[T, ()] = T (identity) → Relation[(name, age)].
  operation identity_fix() -> List[(name: String, age: Int64)] effects Error =
    let rel = person_row
    let f = rel.fix()
    f.takeN(9)

  -- A NON-LITERAL fixed value: the result of an operation CALL. Nothing in `fix`
  -- requires a literal or a compile-time constant — the capture is UNCONSTRAINED
  -- (056 §2.2 / OQ #4), the only load checks are the `Without` reduction's
  -- membership + type match, and the runtime guard is a SEMANTIC `eq(?col, v)`
  -- (`PartialEq.eq`, WI-616) over whatever value arrived.
  operation thirty() -> Int64 = 30

  operation names_at_computed() -> List[(name: String)] effects Error =
    let rel = person_row
    let f = rel.fix(age: thirty())
    f.takeN(9)

  -- A `let`-bound value — the third form the doc names, and (until WI-1127) one the
  -- `where` half of the documented equivalence refused.
  operation names_at_letbound() -> List[(name: String)] effects Error =
    let target = 30
    let rel = person_row
    let f = rel.fix(age: target)
    f.takeN(9)

  -- A genuinely RUNTIME fixed value: the enclosing operation's PARAMETER, unknown
  -- until the call. ONE call site, two different restrictions.
  operation names_at(target: Int64) -> List[(name: String)] effects Error =
    let rel = person_row
    let f = rel.fix(age: target)
    f.takeN(9)

  sort Triple
    entity triple(a: Int64, b: Int64, c: Int64)
  end
  fact triple(a: 1, b: 2, c: 3)
  fact triple(a: 1, b: 20, c: 30)
  fact triple(a: 9, b: 2, c: 3)

  rule triple_row(?a, ?b, ?c) :- triple(a: ?a, b: ?b, c: ?c)   -- (a, b, c)

  -- fix a = 1, DROP a → Relation[(b, c)] (TWO remaining columns). Keeps the two a=1 rows.
  -- The declared `List[(b, c)]` return IS the schema test: it type-checks only if
  -- `Without` dropped exactly `a`.
  operation bc_where_a1() -> List[(b: Int64, c: Int64)] effects Error =
    let rel = triple_row
    let f = rel.fix(a: 1)
    f.takeN(9)

  -- fix a = 1 AND c = 3 (TWO captured values), DROP both → Relation[(b: Int64)]. Keeps
  -- only (a=1, b=2, c=3) → b = 2.
  operation b_where_a1_c3() -> List[(b: Int64)] effects Error =
    let rel = triple_row
    let f = rel.fix(a: 1, c: 3)
    f.takeN(9)
end
"#;

/// WI-20260818-YQB1Y — walk a ONE-COLUMN relation drain into its `String` column values.
/// A row is a one-component named tuple now, not a bare scalar, so this goes through the
/// shared strict reader — which panics on any other row shape rather than hunting for the
/// first `Str` among the fields.
fn drain_strings(kb: &anthill_core::kb::KnowledgeBase, v: Value) -> Vec<String> {
    crate::common::list_column_strings(kb, &v)
}

/// The `Int64` twin of [`drain_strings`].
fn drain_ints(kb: &anthill_core::kb::KnowledgeBase, v: Value) -> Vec<i64> {
    crate::common::list_column_ints(kb, &v)
}

/// Walk a cons list of `(b, c)` tuple rows, collecting each row's two ints in field order.
fn drain_int_pairs(kb: &anthill_core::kb::KnowledgeBase, v: Value) -> Vec<(i64, i64)> {
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
                // WI-20260827-3ZNBC — read what each column DENOTES, not the variant.
                let ints: Vec<i64> = fields
                    .iter()
                    .filter_map(|(_k, v)| crate::common::scalar_int(kb, v))
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

/// fix a column to a value, drop it: the sole remaining column KEEPS ITS NAME
/// (`Relation[(name: String)]`, WI-20260818-YQB1Y — it used to 1-collapse to `String`), and
/// only the matching rows survive (alice & carol at age 30).
#[test]
fn wi727_fix_restrict_and_drop_to_one_column() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi727fix.names_at_30", &[])
        .expect("names_at_30 runs");
    let mut got = drain_strings(interp.kb(), r);
    got.sort();
    assert_eq!(got, vec!["alice".to_string(), "carol".to_string()]);
}

/// fix the OTHER column (name), leaving age: proves the drop is by name, not position.
#[test]
fn wi727_fix_restrict_other_column() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi727fix.ages_of_alice", &[])
        .expect("ages_of_alice runs");
    assert_eq!(drain_ints(interp.kb(), r), vec![30]);
}

/// fix over a NAMED-ARG-head relation drops the head-keyed column by name.
#[test]
fn wi727_fix_named_arg_head() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi727fix.named_head_at_30", &[])
        .expect("named_head_at_30 runs");
    let mut got = drain_strings(interp.kb(), r);
    got.sort();
    assert_eq!(got, vec!["alice".to_string(), "carol".to_string()]);
}

/// MIXED capture: the prefix `fix(p: rel, age: 30)` binds `p` (a declared parameter) AND
/// captures `age` — proves the mechanism partitions matched-named from captured arguments,
/// not just fix's all-leftover dot form.
#[test]
fn wi727_fix_mixed_prefix() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi727fix.mixed_prefix_at_30", &[])
        .expect("mixed_prefix_at_30 runs");
    let mut got = drain_strings(interp.kb(), r);
    got.sort();
    assert_eq!(got, vec!["alice".to_string(), "carol".to_string()]);
}

/// Empty capture `r.fix()` is the identity — `Without[T, ()] = T` — so all rows survive
/// with the full `(name, age)` schema (the `List[(name, age)]` return type-checks).
#[test]
fn wi727_fix_empty_is_identity() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi727fix.identity_fix", &[])
        .expect("identity_fix runs");
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
    assert_eq!(
        rows, 3,
        "identity fix keeps all three persons with full schema"
    );
}

/// Drop ONE of three columns → a TWO-column named-tuple schema. Both a=1 rows survive;
/// the `List[(b, c)]` return type-checking proves the reduced schema.
#[test]
fn wi727_fix_drop_one_of_three() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi727fix.bc_where_a1", &[])
        .expect("bc_where_a1 runs");
    let mut got = drain_int_pairs(interp.kb(), r);
    got.sort();
    assert_eq!(got, vec![(2, 3), (20, 30)]);
}

/// TWO captured values drop TWO columns → the sole remaining `b` keeps its name
/// (`Relation[(b: Int64)]`); only the row matching BOTH (a=1, c=3) survives (b = 2).
#[test]
fn wi727_fix_two_constants() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi727fix.b_where_a1_c3", &[])
        .expect("b_where_a1_c3 runs");
    assert_eq!(drain_ints(interp.kb(), r), vec![2]);
}

/// The fixed value need not be a LITERAL: an operation CALL's result restricts the column
/// exactly as `30` does. `fix` has no constant/literal gate anywhere — the capture is
/// unconstrained (056 §2.2), the load checks are membership + type, and the guard is a
/// semantic `eq`.
#[test]
fn wi727_fix_value_may_be_a_computed_expression() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi727fix.names_at_computed", &[])
        .expect("names_at_computed runs");
    let mut got = drain_strings(interp.kb(), r);
    got.sort();
    assert_eq!(got, vec!["alice".to_string(), "carol".to_string()]);
}

/// The fixed value may be a RUNTIME value — here the enclosing operation's parameter. This
/// is the control that a literal-only `fix` could not pass: ONE call site yields two
/// different restrictions, so the value cannot have been read at compile time.
#[test]
fn wi727_fix_value_may_be_a_runtime_parameter() {
    let mut interp = interp_for(SRC);
    let at30 = interp
        .call("test.wi727fix.names_at", &[Value::Int(30)])
        .expect("names_at(30) runs");
    let mut got30 = drain_strings(interp.kb(), at30);
    got30.sort();
    assert_eq!(got30, vec!["alice".to_string(), "carol".to_string()]);

    let mut interp = interp_for(SRC);
    let at25 = interp
        .call("test.wi727fix.names_at", &[Value::Int(25)])
        .expect("names_at(25) runs");
    assert_eq!(drain_strings(interp.kb(), at25), vec!["bob".to_string()]);
}

/// The `let`-bound form — named by the doc alongside the op result and the parameter, so
/// it is driven rather than asserted. This is also the spelling `where` refused until
/// WI-1127, i.e. one of the values for which the documented `fix ≡ where + project`
/// equivalence did not actually hold; `wi1127_where_operand_may_be_a_let_bound_value`
/// is its peer on the other side.
#[test]
fn wi727_fix_value_may_be_a_let_bound_value() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi727fix.names_at_letbound", &[])
        .expect("names_at_letbound runs");
    let mut got = drain_strings(interp.kb(), r);
    got.sort();
    assert_eq!(got, vec!["alice".to_string(), "carol".to_string()]);
}

/// A COMPOUND fixed value — an entity with fields, not a nullary atom — so the guard's
/// `eq` must recurse structurally through the fields, and the value's named args must
/// canonicalize the way the fact's did. The nullary case below compares atoms only, which
/// would not have caught a mismatch here.
#[test]
fn wi727_fix_value_may_be_a_compound_entity() {
    let src = r#"
namespace test.wi727fixpt
  import anthill.prelude.{String, Int64, List}
  import anthill.prelude.Relation.{fix}
  import anthill.prelude.Option.{none}
  sort Point
    entity point(x: Int64, y: Int64)
  end
  sort Marker
    entity marker(name: String, at: Point)
  end
  fact marker(name: "o", at: point(x: 1, y: 2))
  fact marker(name: "p", at: point(x: 3, y: 4))
  fact marker(name: "q", at: point(x: 1, y: 2))
  rule marker_row(?name, ?at) :- marker(name: ?name, at: ?at)
  operation origin() -> Point = point(x: 1, y: 2)
  operation atOrigin() -> List[(name: String)] effects Error =
    let rel = marker_row
    let f = rel.fix(at: origin())
    f.takeN(9)
end
"#;
    let mut interp = interp_for(src);
    let r = interp
        .call("test.wi727fixpt.atOrigin", &[])
        .expect("atOrigin runs");
    let mut got = drain_strings(interp.kb(), r);
    got.sort();
    assert_eq!(
        got,
        vec!["o".to_string(), "q".to_string()],
        "the structural eq must select exactly the two markers at (1, 2) — not none \
         (a failed structural compare) and not all three"
    );
}

/// The fixed value need not be a SCALAR either: a NOMINAL value of a user sort, returned
/// by an operation, restricts the column through the same semantic `eq` guard. Together
/// with the two cases above this pins the whole claim — `fix`'s argument is an ordinary
/// expression of the column's type, with no literal / compile-time-constant gate.
#[test]
fn wi727_fix_value_may_be_a_nominal_entity() {
    let src = r#"
namespace test.wi727fixctor
  import anthill.prelude.{String, Int64, List}
  import anthill.prelude.Relation.{fix}
  sort Color
    entity red
    entity blue
  end
  sort Item
    entity item(name: String, color: Color)
  end
  fact item(name: "a", color: red)
  fact item(name: "b", color: blue)
  fact item(name: "c", color: red)
  rule item_row(?name, ?color) :- item(name: ?name, color: ?color)
  operation redColor() -> Color = red
  operation reds() -> List[(name: String)] effects Error =
    let rel = item_row
    let f = rel.fix(color: redColor())
    f.takeN(9)
end
"#;
    let mut interp = interp_for(src);
    let r = interp.call("test.wi727fixctor.reds", &[]).expect("reds runs");
    let mut got = drain_strings(interp.kb(), r);
    got.sort();
    assert_eq!(got, vec!["a".to_string(), "c".to_string()]);
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

/// A captured value whose type mismatches its column is a LOAD error (the type check that
/// lives in the `Without` reduction — `age` is `Int64`, `"x"` is `String`). The rule is
/// about the value's TYPE, not its constant-ness; `wi727_fix_type_mismatch_computed_is_load_error`
/// drives the same gate through the non-literal channel.
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

/// The type gate through the NON-LITERAL channel. The literal case above proves nothing
/// about it: a literal's type is syntactically evident, while a captured field's type comes
/// from the typed argument result and is checked by `types_compatible`, which UNIFIES — so
/// an argument arriving as an unresolved var would pass VACUOUSLY and yield a silently
/// empty relation instead of a load error. CONTROL: `thirty()` (same shape, right type)
/// loads clean in `names_at_computed`; only the type differs here.
///
/// MEASURED back-out — `if false &&` on the `types_compatible` call in
/// `without_named_tuple_types` (typing.rs): THIS test and
/// `wi727_fix_type_mismatch_is_load_error` fail, the other 15 in this file pass either way
/// by design. So the literal arm is not vacuous after all (it does reach this gate, not a
/// separate literal-typing path), and what this one adds is coverage of the channel where
/// the type is INFERRED rather than syntactically evident.
#[test]
fn wi727_fix_type_mismatch_computed_is_load_error() {
    let src = r#"
namespace test.wi727fixtyc
  import anthill.prelude.{String, Int64, List}
  import anthill.prelude.Relation.{fix}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  operation notanint() -> String = "x"
  operation bad() -> List[String] effects Error =
    let rel = person_row
    let f = rel.fix(age: notanint())
    f.takeN(9)
end
"#;
    let err = match try_load_kb_with(src) {
        Err(e) => e,
        Ok(_) => panic!(
            "a computed argument of the wrong type must be a load error — the `Without` \
             type check must not be vacuous off the non-literal channel"
        ),
    };
    let joined = err.join("\n");
    assert!(
        joined.contains("age"),
        "the diagnostic should name the offending column; got: {joined}"
    );
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
