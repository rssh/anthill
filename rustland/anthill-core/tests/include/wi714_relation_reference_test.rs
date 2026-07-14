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
  import anthill.prelude.{String, Int64, Option, List, Pair, Unit}
  import anthill.prelude.Relation.{negate}

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

  -- WI-714 negate increment: an EMPTY membership relation (no person named "zed"),
  -- the empty counterpart to has_alice, for negation-as-failure.
  rule has_zed() :- person(name: "zed", age: ?)

  -- negate = negation-as-failure as a QUERY combinator (proposal 052 §algebra).
  -- negate(r) : Relation[Unit]; its stream is non-empty (one `unit`) iff r has NO
  -- solution. Provable operand → the negation query fails → empty.
  operation negateProvableIsEmpty() -> Bool effects Error =
    let r = negate(has_alice)
    r.isEmpty

  -- Empty operand → NAF succeeds once with no bindings → non-empty.
  operation negateEmptyIsEmpty() -> Bool effects Error =
    let r = negate(has_zed)
    r.isEmpty

  -- The single solution of negate(empty) materializes as the 0-column Unit row.
  operation negateEmptyHead() -> Option[Unit] effects Error =
    let r = negate(has_zed)
    match r.splitFirst
      case some(pair(h, _)) -> some(h)
      case none() -> none()

  -- negate COMPOSES on itself — only possible because it returns a composable,
  -- query-carrying Relation (combining QUERIES, not streams). not(not(provable))
  -- succeeds, so the double negation is non-empty.
  operation doubleNegateIsEmpty() -> Bool effects Error =
    let r = negate(negate(has_alice))
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

// ── WI-714 relational algebra increment 1: negate → negation (NAF) ──────────
// negate COMBINES QUERIES: it wraps the operand's query in the `negation`
// LogicalQuery constructor (lowered to `not(inner_goals)`), never running the
// operand as a stream. Result is a 0-column `Relation[Unit]` membership relation.

/// `has_alice` is provable, so `negate(has_alice)` is EMPTY: the resolver lowers
/// `negation` to `not(inner)`, which fails when the inner query is provable.
#[test]
fn wi714_negate_of_provable_is_empty() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi714ref.negateProvableIsEmpty", &[])
        .expect("negate(has_alice).isEmpty");
    assert_eq!(
        r.as_bool(),
        Some(true),
        "negate of a provable relation is empty (NAF fails)"
    );
}

/// `has_zed` has no solution, so `negate(has_zed)` is NON-empty — NAF succeeds
/// once with no bindings, materialized as the single Unit row.
#[test]
fn wi714_negate_of_empty_is_nonempty() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi714ref.negateEmptyIsEmpty", &[])
        .expect("negate(has_zed).isEmpty");
    assert_eq!(
        r.as_bool(),
        Some(false),
        "negate of an empty relation is non-empty (NAF succeeds)"
    );
}

/// The single solution of `negate(empty)` materializes as `unit` — the 0-column
/// membership row. `negate(has_zed).headOption == some(unit)`.
#[test]
fn wi714_negate_materializes_unit() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi714ref.negateEmptyHead", &[])
        .expect("negate(has_zed).headOption");
    // some(unit) — payload rides positionally (some) or as the single named field.
    let inner = match &r {
        Value::Entity { pos, .. } if !pos.is_empty() => pos[0].clone(),
        Value::Entity { named, .. } if !named.is_empty() => named[0].1.clone(),
        other => panic!("expected some(unit), got {other:?}"),
    };
    assert!(
        matches!(inner, Value::Unit),
        "negate's row materializes as the 0-column Unit, got {inner:?}"
    );
}

/// negate REQUIRES a membership operand: negating a relation with a FREE column
/// would flounder under NAF (the resolver cannot decide `not p(?x)` with `?x`
/// unbound — resolver changes are out of 052's scope), so it is a LOUD error
/// rather than a silent floundered result. Enforced at runtime (see the stdlib
/// note on why the signature can't carry a `T = Unit`-with-`E`-open constraint).
#[test]
fn wi714_negate_requires_membership_operand() {
    let src = r#"
namespace test.wi714negcol
  import anthill.prelude.{String, Int64, Option, List}
  import anthill.prelude.Relation.{negate}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)

  -- person_name : Relation[String] — a relation WITH a free column
  rule person_name(?name) :- person(name: ?name, age: ?)

  -- negate over a multi-column relation must be rejected (NAF would flounder)
  operation bad() -> Bool effects Error =
    let r = negate(person_name)
    r.isEmpty
end
"#;
    // Loads clean (the guard is at runtime); the call surfaces the loud error.
    let mut interp = interp_for(src);
    let err = interp
        .call("test.wi714negcol.bad", &[])
        .expect_err("negate over a relation with free columns must error, not flounder");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("membership") || msg.contains("free column") || msg.contains("flounder"),
        "negate must loudly reject a non-membership operand, got: {msg}"
    );
}

/// negate COMPOSES on itself — proof it returns a composable, query-carrying
/// `Relation` (combining QUERIES, not streams; a stream-level bool could not be
/// re-negated). `not(not(provable))` succeeds, so the double negation is
/// non-empty.
#[test]
fn wi714_negate_composes_double_negation() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi714ref.doubleNegateIsEmpty", &[])
        .expect("negate(negate(has_alice)).isEmpty");
    assert_eq!(
        r.as_bool(),
        Some(false),
        "double negation of a provable relation is non-empty (composes at the query level)"
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

// ── APPLIED citation position (WI-714): a rule NAME applied to arguments binds columns ──

const SRC3: &str = r#"
namespace test.wi714applied
  import anthill.prelude.{String, Int64, List}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)
  fact person(name: "carol", age: 30)

  rule person_name(?name) :- person(name: ?name, age: ?)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  -- applied, BOTH free vars bound → Relation[Unit] (membership). (alice, 30) is a
  -- fact, so the relation is non-empty.
  operation aliceRowPresent() -> Bool effects Error =
    let r = person_row("alice", 30)
    r.isEmpty

  -- applied, both bound but NO such row → empty membership relation.
  operation ghostRowPresent() -> Bool effects Error =
    let r = person_row("ghost", 99)
    r.isEmpty

  -- applied, bind name POSITIONALLY → the age column narrows T to Relation[Int64]
  -- (1-collapse). alice appears once (age 30).
  operation alicesAges() -> List[Int64] effects Error =
    let r = person_row("alice")
    r.takeN(5)

  -- applied, bind age BY PARAM NAME → the name column narrows T to Relation[String].
  -- both alice and carol are 30.
  operation namesAged30() -> List[String] effects Error =
    let r = person_row(age: 30)
    r.takeN(5)

  -- the bound value is a LOCAL (an operation parameter), not a literal.
  operation agesOf(who: String) -> List[Int64] effects Error =
    let r = person_row(who)
    r.takeN(5)
end
"#;

/// Applied form binding EVERY free variable → a 0-column `Relation[Unit]` membership
/// relation: `person_row("alice", 30)` is provable (a fact), so it is non-empty.
#[test]
fn wi714_applied_full_binding_is_membership() {
    let mut interp = interp_for(SRC3);
    let present = interp
        .call("test.wi714applied.aliceRowPresent", &[])
        .expect("aliceRowPresent runs the fully-bound relation");
    assert_eq!(
        present.as_bool(),
        Some(false),
        "a fully-bound relation matching a fact is a non-empty membership relation"
    );
    let ghost = interp
        .call("test.wi714applied.ghostRowPresent", &[])
        .expect("ghostRowPresent runs the fully-bound relation");
    assert_eq!(
        ghost.as_bool(),
        Some(true),
        "a fully-bound relation matching no fact is empty"
    );
}

/// Applied form binding one free variable POSITIONALLY subtracts that column: the
/// remaining single column narrows `T` (1-collapse), so `person_row("alice")` is a
/// `Relation[Int64]` of alice's ages.
#[test]
fn wi714_applied_positional_binding_narrows_schema() {
    let mut interp = interp_for(SRC3);
    let r = interp
        .call("test.wi714applied.alicesAges", &[])
        .expect("alicesAges drains the partially-bound relation");
    let mut got = collect_int_list(&r);
    got.sort();
    assert_eq!(
        got,
        vec![30],
        "binding name leaves the age column, materialized (1-collapse) to Int64"
    );
}

/// Applied form binding a free variable BY PARAM NAME (`age: 30`) subtracts the age
/// column; the name column narrows `T` to `Relation[String]`. alice and carol are 30.
#[test]
fn wi714_applied_named_binding_narrows_schema() {
    let mut interp = interp_for(SRC3);
    let r = interp
        .call("test.wi714applied.namesAged30", &[])
        .expect("namesAged30 drains the named-bound relation");
    let mut got = collect_string_list(&r);
    got.sort();
    assert_eq!(
        got,
        vec!["alice".to_string(), "carol".to_string()],
        "binding age by param name leaves the name column"
    );
}

/// The bound value can be any expression — here an operation parameter (`who`),
/// evaluated and spliced into the relation's goal atom.
#[test]
fn wi714_applied_binding_from_local() {
    let mut interp = interp_for(SRC3);
    let r = interp
        .call("test.wi714applied.agesOf", &[Value::Str("bob".into())])
        .expect("agesOf drains the relation bound to a local");
    let got = collect_int_list(&r);
    assert_eq!(got, vec![25], "the local's value binds the name column");
}

/// A supplied argument whose type is incompatible with the column it binds is a loud
/// LOAD error (age is `Int64`; binding it to a `String` cannot narrow the schema).
#[test]
fn wi714_applied_type_mismatch_rejected() {
    let src = r#"
namespace test.wi714badtype
  import anthill.prelude.{String, Int64, List}

  sort Person
    entity person(name: String, age: Int64)
  end

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  operation bad() -> List[String] effects Error =
    let r = person_row(age: "notanumber")
    r.takeN(5)
end
"#;
    let errs = try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("incompatible type")),
        "a type-incompatible bound argument must be a loud load error, got: {errs:?}"
    );
}

/// Supplying more positional arguments than the relation has free columns is a loud
/// LOAD error.
#[test]
fn wi714_applied_arity_overflow_rejected() {
    let src = r#"
namespace test.wi714arity
  import anthill.prelude.{String, Int64, List}

  sort Person
    entity person(name: String, age: Int64)
  end

  rule person_name(?name) :- person(name: ?name, age: ?)

  operation bad() -> List[String] effects Error =
    let r = person_name("alice", "extra")
    r.takeN(5)
end
"#;
    let errs = try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("no free column")),
        "a positional-arity overflow must be a loud load error, got: {errs:?}"
    );
}

/// A named argument whose key names no free column is a loud LOAD error.
#[test]
fn wi714_applied_unknown_param_rejected() {
    let src = r#"
namespace test.wi714unknown
  import anthill.prelude.{String, Int64, List}

  sort Person
    entity person(name: String, age: Int64)
  end

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  operation bad() -> List[String] effects Error =
    let r = person_row(nope: 3)
    r.takeN(5)
end
"#;
    let errs = try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("names no free column")),
        "an unknown named param must be a loud load error, got: {errs:?}"
    );
}

/// The applied form works through a QUALIFIED name too — `ns.rule(args)` (the
/// proposal's `Sort.rule(args)`) — because the citation resolves the fn-term name to
/// the rule symbol via existing name resolution, then the same `kind_of(fn_sym)` arm
/// fires. Here the rule lives in one namespace and is applied, qualified, from
/// another.
#[test]
fn wi714_applied_qualified_name() {
    const DATA: &str = r#"
namespace test.wi714q.data
  import anthill.prelude.{String, Int64}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
end
"#;
    const USE: &str = r#"
namespace test.wi714q.use
  import anthill.prelude.{String, Int64, List}

  operation bobsAges() -> List[Int64] effects Error =
    let r = test.wi714q.data.person_row("bob")
    r.takeN(5)
end
"#;
    let kb = crate::common::try_load_kb_with_files(&[DATA, USE])
        .unwrap_or_else(|errs| panic!("qualified applied reference must load; got: {errs:?}"));
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register builtins");
    let r = interp
        .call("test.wi714q.use.bobsAges", &[])
        .expect("bobsAges runs the qualified-applied relation");
    assert_eq!(
        collect_int_list(&r),
        vec![25],
        "a qualified `ns.rule(args)` binds and narrows exactly like the unqualified form"
    );
}

// ── Applied binding operates on COLUMNS, not raw head slots (review edge cases) ──

const SRC4: &str = r#"
namespace test.wi714cols
  import anthill.prelude.{String, Int64, List, Bool}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)

  sort Score
    entity score(rank: Int64, who: String)
  end
  fact score(rank: 1, who: "alice")
  fact score(rank: 1, who: "carol")
  fact score(rank: 2, who: "bob")

  -- NONLINEAR head: ?n fills BOTH slots but is ONE column → bare Relation[String].
  rule twin(?n, ?n) :- person(name: ?n, age: ?)

  -- applied binds the SINGLE column n (all its slots) → Relation[Unit] membership,
  -- NOT a residual echo column. alice is a person, ghost is not.
  operation aliceIsTwin() -> Bool effects Error =
    let r = twin("alice")
    r.isEmpty
  operation ghostIsTwin() -> Bool effects Error =
    let r = twin("ghost")
    r.isEmpty

  -- head with a GROUND slot (rank 1) BEFORE the free var `who` → bare Relation[String]
  -- of rank-1 names. Positional application binds the free COLUMN (who), not the
  -- ground slot — the ground slot must not block left-to-right column binding.
  rule rankOne(1, ?who) :- score(rank: 1, who: ?who)

  operation aliceIsRankOne() -> Bool effects Error =
    let r = rankOne("alice")
    r.isEmpty
  operation bobIsRankOne() -> Bool effects Error =
    let r = rankOne("bob")
    r.isEmpty
end
"#;

/// A NONLINEAR head column bound by the applied form subtracts the WHOLE column (both
/// its slots), yielding a `Relation[Unit]` membership relation — not a residual "echo"
/// column. `twin("alice")` is membership: alice is a person, ghost is not.
#[test]
fn wi714_applied_nonlinear_column_binds_as_one() {
    let mut interp = interp_for(SRC4);
    let alice = interp
        .call("test.wi714cols.aliceIsTwin", &[])
        .expect("aliceIsTwin runs the nonlinear-bound relation");
    assert_eq!(
        alice.as_bool(),
        Some(false),
        "binding the single nonlinear column gives a provable (non-empty) membership relation"
    );
    let ghost = interp
        .call("test.wi714cols.ghostIsTwin", &[])
        .expect("ghostIsTwin runs the nonlinear-bound relation");
    assert_eq!(
        ghost.as_bool(),
        Some(true),
        "a non-person is not a twin — the membership relation is empty"
    );
}

/// Positional application binds the relation's free COLUMNS left to right, so a GROUND
/// head slot before a free var (`rankOne(1, ?who)`) does NOT block positional binding:
/// `rankOne("alice")` binds the sole `who` column (not a load error).
#[test]
fn wi714_applied_positional_skips_ground_slot() {
    let mut interp = interp_for(SRC4);
    let alice = interp
        .call("test.wi714cols.aliceIsRankOne", &[])
        .expect("aliceIsRankOne binds the free column past the ground slot");
    assert_eq!(
        alice.as_bool(),
        Some(false),
        "alice is rank 1 — the positionally-bound membership relation is non-empty"
    );
    let bob = interp
        .call("test.wi714cols.bobIsRankOne", &[])
        .expect("bobIsRankOne runs the relation");
    assert_eq!(
        bob.as_bool(),
        Some(true),
        "bob is rank 2, not rank 1 — the membership relation is empty"
    );
}

/// When two head columns share a type variable (`eq(?x, ?y)` types both at one `T`),
/// the applied type-check threads ONE substitution, so a contradictory pair of bound
/// values (`pair_eq(5, "s")`) is rejected loudly — arg 0 pins `T := Int64`, then `"s"`
/// fails against it (not each arg passing in isolation).
#[test]
fn wi714_applied_correlated_columns_reject_contradiction() {
    let src = r#"
namespace test.wi714corr
  import anthill.prelude.{String, Int64, List, Bool}

  -- ?x and ?y are forced to one type by `eq(?x, ?y)`.
  rule pair_eq(?x, ?y) :- eq(?x, ?y)

  operation bad() -> Bool effects Error =
    let r = pair_eq(5, "s")
    r.isEmpty
end
"#;
    let errs = try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("incompatible type")),
        "contradictory bindings of correlated columns must be a loud load error, got: {errs:?}"
    );
}

/// Binding an UNCONSTRAINED column (a polymorphic head param the body pins to no
/// concrete type) is ACCEPTED, not spuriously rejected — a raw column type var accepts
/// any argument (it is not the reflect `TypeVar` wildcard `types_compatible` alone
/// recognizes). Binding it also NARROWS the shared column: `rel(?x, ?y) :- eq(?x, ?y)`
/// types both columns at one var, so `rel(5)` pins that var to `Int64` — the surviving
/// `y` column is `Int64`, proven by a `List[String]` consumer being rejected while the
/// matching `List[Int64]` one loads.
#[test]
fn wi714_applied_unconstrained_column_accepts_and_narrows() {
    // The matching consumer loads: binding is accepted AND the surviving column is Int64.
    let ok_src = r#"
namespace test.wi714poly
  import anthill.prelude.{String, Int64, List, Bool}

  rule rel(?x, ?y) :- eq(?x, ?y)

  operation relFiveInt() -> List[Int64] effects Error =
    let r = rel(5)
    r.takeN(3)
end
"#;
    try_load_kb_with(ok_src).unwrap_or_else(|errs| {
        panic!("binding an unconstrained column must be accepted and narrow to Int64; got: {errs:?}")
    });

    // The MISmatched consumer is rejected: the surviving column narrowed to Int64, so a
    // `List[String]` result is a type error (were the column left an open var, it would
    // wrongly unify with String and load).
    let bad_src = r#"
namespace test.wi714poly2
  import anthill.prelude.{String, Int64, List, Bool}

  rule rel(?x, ?y) :- eq(?x, ?y)

  operation relFiveStr() -> List[String] effects Error =
    let r = rel(5)
    r.takeN(3)
end
"#;
    let errs = try_load_kb_with(bad_src).err().unwrap_or_default();
    assert!(
        !errs.is_empty(),
        "binding x = 5 narrows the shared column to Int64, so a List[String] result must \
         be rejected — the column did not stay an open var"
    );
}

// ── BARE-QUALIFIED citation position (WI-714): `ns.rule` / `Sort.rule` as a value ──
//
// The third and final citation position (proposal 052 §Naming). A rule cited by a
// dotted name with NO trailing `(…)` parses (§6.7) as a `field_access` chain, not a
// call. When that chain resolves to a rule, the loader collapses it to the SAME
// `var_ref(Ref(rule))` form the bare UNQUALIFIED name takes, so `check_bare_ref` (C3)
// and `reduce_var` (C2) type + run it identically — the reference is a `Relation[T]`
// value consumed through the Stream API.

/// A rule cited by a bare, fully-qualified NAMESPACE name (no application) from
/// another file is a `Relation[T]` value: `test.wi714bq.data.person_row` types as
/// `Relation[(name, age)]` and drains via the inherited `takeN`.
#[test]
fn wi714_bare_qualified_namespace_reference() {
    const DATA: &str = r#"
namespace test.wi714bq.data
  import anthill.prelude.{String, Int64}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
end
"#;
    const USE: &str = r#"
namespace test.wi714bq.use
  import anthill.prelude.{String, Int64, List}

  operation rows() -> List[(name: String, age: Int64)] effects Error =
    let r = test.wi714bq.data.person_row
    r.takeN(5)
end
"#;
    let kb = crate::common::try_load_kb_with_files(&[DATA, USE])
        .unwrap_or_else(|errs| panic!("bare-qualified namespace reference must load; got: {errs:?}"));
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register builtins");
    let r = interp
        .call("test.wi714bq.use.rows", &[])
        .expect("rows() drains the bare-qualified relation");
    let mut rows = collect_named_rows(&r);
    rows.sort();
    assert_eq!(
        rows,
        vec![("alice".to_string(), 30), ("bob".to_string(), 25)],
        "a bare-qualified `ns.rule` value drains exactly like the bare-unqualified form"
    );
}

/// The proposal's canonical `Queen.find` — a rule declared inside a SORT body,
/// cited bare as `Sort.rule` (no application). The receiver `Queen` is a sort symbol
/// (§6.7 mode-2), and `find` names a rule in its scope, so the reference is the
/// `Relation[Int64]` value of solved rows.
#[test]
fn wi714_bare_qualified_sort_scoped_reference() {
    const SRC: &str = r#"
namespace test.wi714bqsort
  import anthill.prelude.{Int64, List}

  sort Queen
    entity queen(row: Int64, col: Int64)
    rule find(?row) :- queen(row: ?row, col: ?)
  end
  fact queen(row: 1, col: 1)
  fact queen(row: 2, col: 3)

  -- bare `Sort.rule` (no parens): the relation value, consumed as a stream.
  operation bareRows() -> List[Int64] effects Error =
    let r = Queen.find
    r.takeN(5)

  -- and the applied form `Sort.rule()` resolves to the same relation.
  operation appliedRows() -> List[Int64] effects Error =
    let r = Queen.find()
    r.takeN(5)
end
"#;
    let mut interp = interp_for(SRC);
    let bare = interp
        .call("test.wi714bqsort.bareRows", &[])
        .expect("bareRows drains the sort-scoped bare relation");
    let mut got = collect_int_list(&bare);
    got.sort();
    assert_eq!(
        got,
        vec![1, 2],
        "a bare `Sort.rule` value (the proposal's `Queen.find`) drains its rows"
    );
    let applied = interp
        .call("test.wi714bqsort.appliedRows", &[])
        .expect("appliedRows drains the sort-scoped applied relation");
    let mut got2 = collect_int_list(&applied);
    got2.sort();
    assert_eq!(got2, vec![1, 2], "the applied `Sort.rule()` resolves to the same relation");
}

/// The proposal's negative invariant (§"`x.name` on a runtime value is not a way to
/// name a relation"): dotting a runtime VALUE with a rule name is operation dispatch,
/// NOT relation naming. A local value `q` bound to a `Queen` has no member `find` (a
/// rule is not a member of a value's sort), so `q.find` is a loud "no such member"
/// error — the bare-qualified collapse fires only for a sort/namespace receiver, and
/// the value-receiver re-route runs first.
#[test]
fn wi714_rule_not_named_off_a_runtime_value() {
    const SRC: &str = r#"
namespace test.wi714bqguard
  import anthill.prelude.{Int64, List}

  sort Queen
    entity queen(row: Int64)
    rule find(?row) :- queen(row: ?row)
  end
  fact queen(row: 1)

  operation bad() -> List[Int64] effects Error =
    let q = queen(row: 1)
    let r = q.find
    r.takeN(5)
end
"#;
    let errs = try_load_kb_with(SRC).err().unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("no such member") || e.contains("dot dispatch")),
        "dotting a runtime value with a rule name must be a loud dispatch error, got: {errs:?}"
    );
}

// ── Labeled rules + multi-clause head-functor uniformity (WI-714) ──

/// A rule cited by its LABEL (`rule adult: head :- …`, `SymbolKind::Rule`) rather than
/// its head functor is a `Relation[T]` value too — the relation machinery is keyed on
/// `RuleId`, fully label-agnostic. Covers the bare-unqualified label and the
/// bare-qualified `ns.label` form (both citation surfaces resolve the label). Every
/// other test uses unlabeled head-functor rules; this closes that coverage gap.
#[test]
fn wi714_labeled_rule_reference() {
    const SRC: &str = r#"
namespace test.wi714label
  import anthill.prelude.{String, Int64, List}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)

  -- a namespace-level LABELED rule: label `adult`, head functor `isAdult`.
  rule adult: isAdult(?name) :- person(name: ?name, age: ?)

  operation viaBareLabel() -> List[String] effects Error =
    let r = adult
    r.takeN(5)

  operation viaQualifiedLabel() -> List[String] effects Error =
    let r = test.wi714label.adult
    r.takeN(5)
end
"#;
    let mut interp = interp_for(SRC);
    for op in ["viaBareLabel", "viaQualifiedLabel"] {
        let r = interp
            .call(&format!("test.wi714label.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op} runs the labeled relation: {e:?}"));
        let mut got = collect_string_list(&r);
        got.sort();
        assert_eq!(
            got,
            vec!["alice".to_string(), "bob".to_string()],
            "{op}: a rule cited by its label is a Relation value keyed on RuleId"
        );
    }
}

/// A legitimate labeled MULTI-CLAUSE relation (all clauses share ONE head functor)
/// unions its clauses' solutions — the ordinary case must keep working after the
/// head-functor-uniformity guard.
#[test]
fn wi714_labeled_multiclause_same_functor_unions() {
    const SRC: &str = r#"
namespace test.wi714lm
  import anthill.prelude.{String, Int64, List}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)

  sort Pet
    entity pet(petName: String)
  end
  fact pet(petName: "rex")

  -- two clauses, same label `grouped` AND same head functor `named` → well-formed.
  rule grouped: named(?n) :- person(name: ?n, age: ?)
  rule grouped: named(?n) :- pet(petName: ?n)

  operation everyName() -> List[String] effects Error =
    let r = grouped
    r.takeN(5)
end
"#;
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi714lm.everyName", &[])
        .expect("everyName drains the labeled same-functor relation");
    let mut got = collect_string_list(&r);
    got.sort();
    assert_eq!(
        got,
        vec!["alice".to_string(), "rex".to_string()],
        "a labeled multi-clause relation sharing one head functor unions its clauses"
    );
}

/// A label grouping clauses with DIFFERING head functors (`rule L: foo(?x) …` /
/// `rule L: bar(?y) …`) is rejected loudly at LOAD. The relation's query is built from
/// ONE head shape (the first clause) and SLD unions clauses through that shared
/// functor, so the schema would union both functors while eval ran only the first —
/// dropping the rest. "Loud error over silent skip."
#[test]
fn wi714_differing_head_functors_rejected() {
    const SRC: &str = r#"
namespace test.wi714dhf
  import anthill.prelude.{String, Int64, List}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)

  sort Pet
    entity pet(petName: String)
  end
  fact pet(petName: "rex")

  rule things: fromPerson(?n) :- person(name: ?n, age: ?)
  rule things: fromPet(?n) :- pet(petName: ?n)

  operation allThings() -> List[String] effects Error =
    let r = things
    r.takeN(5)
end
"#;
    let errs = try_load_kb_with(SRC).err().unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("differing head functors")),
        "a label over multiple head predicates must be a loud load error, got: {errs:?}"
    );
}

// ── Cross-sort, cross-file rule-body call (the SUBGOAL counterpart) ──

/// A rule's BODY may cite another sort's rule by its qualified `Sort.rule` name as a
/// SUBGOAL (a logical atom), across files in the same namespace. This is the ordinary
/// qualified-subgoal path — NOT the WI-714 relation-VALUE collapse (which is
/// expression context only): in a rule body `S.q(?x)` is a subgoal, in an operation
/// body bare `S.q` is the relation value. Here `S2.q2`'s body calls `S.q` (a rule in
/// another sort, another file), and the whole thing is then consumed as a WI-714
/// bare-qualified relation value — exercising both worlds end-to-end.
#[test]
fn wi714_cross_sort_rule_body_subgoal() {
    // file 1: sort S with rule q + facts.
    const F1: &str = r#"
namespace test.wi714xsort
  import anthill.prelude.{Int64}

  sort S
    entity se(v: Int64)
    rule q(?x) :- se(v: ?x)
  end
  fact se(v: 1)
  fact se(v: 2)
  fact se(v: 3)
end
"#;
    // file 2: SAME namespace, sort S2 whose rule body calls the cross-sort `S.q`.
    const F2: &str = r#"
namespace test.wi714xsort
  import anthill.prelude.{Int64, List}

  sort S2
    entity s2e(w: Int64)
    rule other(?x) :- s2e(w: ?x)
    -- `S.q(?x)` is a cross-sort SUBGOAL (S is in file 1); `other(?x)` resolves in
    -- S2's own scope. q2 = S.q ∩ other.
    rule q2(?x) :- S.q(?x), other(?x)
  end
  fact s2e(w: 2)
  fact s2e(w: 3)
  fact s2e(w: 9)

  -- consume the sort-scoped relation as a WI-714 bare-qualified value.
  operation q2Rows() -> List[Int64] effects Error =
    let r = S2.q2
    r.takeN(5)
end
"#;
    let kb = crate::common::try_load_kb_with_files(&[F1, F2])
        .unwrap_or_else(|errs| panic!("cross-sort rule-body call must load; got: {errs:?}"));
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register builtins");
    let r = interp
        .call("test.wi714xsort.q2Rows", &[])
        .expect("q2Rows drains the relation whose clause calls a cross-sort rule");
    let mut got = collect_int_list(&r);
    got.sort();
    assert_eq!(
        got,
        vec![2, 3],
        "q2 = S.q{{1,2,3}} ∩ other{{2,3,9}} — the cross-sort subgoal resolves and runs"
    );
}

/// Decode a `List[(name: String, age: Int64)]` (cons chain of named tuples) into
/// `(String, i64)` pairs — the multi-column-row shape.
fn collect_named_rows(v: &Value) -> Vec<(String, i64)> {
    let mut rows: Vec<(String, i64)> = Vec::new();
    let mut cur = v.clone();
    while let Value::Entity { named, .. } = &cur {
        if named.is_empty() {
            break;
        }
        let mut head_tuple: Option<Value> = None;
        let mut tail: Option<Value> = None;
        for (_k, val) in named.iter() {
            match val {
                Value::Tuple { .. } => head_tuple = Some(val.clone()),
                Value::Entity { .. } => tail = Some(val.clone()),
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
    rows
}

/// Decode an anthill `List[Int64]` value (`cons(head, tail)` chain, `nil` end) into a
/// `Vec<i64>`.
fn collect_int_list(v: &Value) -> Vec<i64> {
    let mut out = Vec::new();
    let mut cur = v.clone();
    loop {
        match cur {
            Value::Entity { ref named, .. } if !named.is_empty() => {
                let mut head: Option<i64> = None;
                let mut tail: Option<Value> = None;
                for (_k, val) in named.iter() {
                    match val {
                        Value::Int(n) => head = Some(*n),
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
            _ => break,
        }
    }
    out
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
