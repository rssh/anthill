//! WI-714 (proposal 052) — schema synthesis over a RECURSIVE relation.
//!
//! Transitive closure (`anc(?c, ?e) :- parent(of: ?c, is: ?e)` /
//! `anc(?c, ?e) :- parent(of: ?c, is: ?m), anc(?m, ?e)`) is THE canonical recursive
//! logic program, and 052's own "associated relations" worked example (`reachable`)
//! has this exact shape. Recursive rules always resolved fine as subgoals; it was
//! only the Relation VALUE face that could not type them.
//!
//! A clause types a head parameter only where a body goal constrains it (an
//! operation parameter / entity field) — a RULE subgoal types nothing. So in the
//! recursive clause the column `e`'s only typing source is the rule's OWN
//! self-reference, leaving it unconstrained: a fresh raw `Var::Global`, which is the
//! ABSENCE of a type. The cross-clause lub treated that absence as a rival type and
//! reported the column disjoint, so the relation failed to LOAD. `join_column_types`
//! makes an unconstrained column contribute nothing, taking the type from the clause
//! that knows — the fixpoint answer, no assume-then-check iteration needed.
//!
//! These tests drive the full surface end-to-end from source (all EVAL), and pin the
//! loud disjoint guard that must SURVIVE the relaxation.

use anthill_core::eval::Value;

use crate::common::{interp_for, try_load_kb_with};

const SRC: &str = r#"
namespace test.wi714rec
  import anthill.prelude.{String, Int64, Option, List, Unit}
  import anthill.prelude.List.{length}

  sort Family
    entity parent(of: String, is: String)
  end
  fact parent(of: "bart", is: "homer")
  fact parent(of: "homer", is: "abe")
  fact parent(of: "lisa", is: "homer")

  -- base clause: `?e` is typed by `parent.is`
  rule anc(?c, ?e) :- parent(of: ?c, is: ?e)
  -- recursive clause: `?e`'s ONLY typing source is the self-reference — it takes
  -- its type from the base clause.
  rule anc(?c, ?e) :- parent(of: ?c, is: ?m), anc(?m, ?e)

  -- the whole transitive closure, drained as a stream
  operation closure() -> List[(c: String, e: String)] effects Error =
    let r = anc
    r.takeN(50)

  -- the recursion-typed column resolves BY NAME in a row lambda, and the guard
  -- really constrains (see the test: 3 of the 5 closure rows survive)
  operation ofAbe() -> List[(c: String, e: String)] effects Error =
    let r = anc
    let f = r.where(lambda x -> eq(x.e, "abe"))
    f.takeN(50)

  -- the GROUND applied citation, which failed identically before the fix
  -- (schema synthesis runs regardless of citation position) → Relation[Unit].
  -- Counted in anthill: a `List[Unit]`'s elements are field-less, so decoding the
  -- cons chain host-side could not tell an element from the `nil` terminator.
  operation bartAncAbe() -> Int64 effects Error =
    let r = anc("bart", "abe")
    length(r.takeN(50))

  -- the same membership query for a pair that is NOT in the closure
  operation abeAncBart() -> Int64 effects Error =
    let r = anc("abe", "bart")
    length(r.takeN(50))

  -- projection onto the recursion-typed column (bag semantics, OQ6)
  operation ancestors() -> List[String] effects Error =
    let r = anc
    let p = r.(e)
    p.takeN(50)
end
"#;

/// Decode `List[(c: String, e: String)]` (a `cons`/`nil` chain of named tuples).
fn collect_pairs(v: &Value) -> Vec<(String, String)> {
    let mut out = Vec::new();
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
                // Columns ride in head-declaration order (c, e).
                let cols: Vec<String> = fields
                    .iter()
                    .filter_map(|(_, v)| match v {
                        Value::Str(s) => Some(s.clone()),
                        _ => None,
                    })
                    .collect();
                assert_eq!(cols.len(), 2, "each row is the 2-column tuple (c, e)");
                out.push((cols[0].clone(), cols[1].clone()));
                cur = t;
            }
            _ => break,
        }
    }
    out
}

/// Decode a `List[String]` (`cons`/`nil` chain).
fn collect_strings(v: &Value) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = v.clone();
    while let Value::Entity { named, .. } = &cur {
        if named.is_empty() {
            break;
        }
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
    out
}

/// A recursive rule cited BY NAME is a `Relation[T]` that LOADS and enumerates the
/// true transitive closure. The exact pairs are asserted, not just the count — a
/// schema that merely loads but drops the recursive clause would still return the
/// 3 base rows.
#[test]
fn wi714_recursive_relation_drains_transitive_closure() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi714rec.closure", &[])
        .expect("a recursive rule cited by name must load and drain");
    let mut got = collect_pairs(&r);
    got.sort();
    let mut want = vec![
        ("bart".to_string(), "homer".to_string()),
        ("homer".to_string(), "abe".to_string()),
        ("lisa".to_string(), "homer".to_string()),
        // the two rows that ONLY the recursive clause derives
        ("bart".to_string(), "abe".to_string()),
        ("lisa".to_string(), "abe".to_string()),
    ];
    want.sort();
    assert_eq!(
        got, want,
        "the relation must enumerate the full transitive closure, including the \
         rows only the recursive clause derives"
    );
}

/// THE SCHEMA ITSELF: the recursion-typed column really is `String`, taken from the
/// base clause — not left as an open type var.
///
/// This is the discriminating test. Merely comparing the column to a string (as
/// `ofAbe` does) would NOT prove it: an unconstrained column is a raw var, and a var
/// unifies with `String` happily. So annotate it at the WRONG type instead — an open
/// var would unify with `Int64` and load clean, while a `String` column must reject.
/// The rejection also prints the synthesized schema, which pins it exactly.
#[test]
fn wi714_recursive_column_schema_is_the_base_clause_type() {
    let bad = SRC.replace(
        "operation closure() -> List[(c: String, e: String)] effects Error =",
        "operation closure() -> List[(c: String, e: Int64)] effects Error =",
    );
    assert_ne!(bad, SRC, "the closure signature must be the one being retyped");
    let errs = try_load_kb_with(&bad).err().unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("e: String")),
        "the recursion-typed column must synthesize as String (from the base clause), \
         so an `Int64` annotation is rejected AND the reported schema names `e: String` \
         — an open var would have unified with Int64 and loaded. Got: {errs:?}"
    );
}

/// The recursion-typed column resolves BY NAME in a row lambda, and the guard really
/// constrains — 3 of the 5 closure rows survive, so it is not vacuously true. (That
/// the column is `String` rather than an open var is pinned by
/// `wi714_recursive_column_schema_is_the_base_clause_type`.)
#[test]
fn wi714_recursive_column_types_from_the_base_clause() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi714rec.ofAbe", &[])
        .expect("where over a recursion-typed column must type and run");
    let mut got = collect_pairs(&r);
    got.sort();
    let mut want = vec![
        ("bart".to_string(), "abe".to_string()),
        ("homer".to_string(), "abe".to_string()),
        ("lisa".to_string(), "abe".to_string()),
    ];
    want.sort();
    assert_eq!(
        got, want,
        "the column must type as String from the base clause AND the guard must \
         really constrain (a vacuous guard would keep all 5 rows)"
    );
}

/// The GROUND applied citation `anc("bart", "abe")` — schema synthesis runs
/// regardless of citation position, so this failed identically before the fix.
/// Both columns bind → `Relation[Unit]` membership: derivable exactly once (via
/// homer), while a non-member pair is empty — so the membership face really
/// decides, rather than being vacuously true.
#[test]
fn wi714_recursive_relation_ground_applied_citation() {
    let mut interp = interp_for(SRC);
    let member = interp
        .call("test.wi714rec.bartAncAbe", &[])
        .expect("a ground applied citation of a recursive rule must load and run");
    assert!(
        matches!(member, Value::Int(1)),
        "`anc(\"bart\", \"abe\")` is derivable exactly once (via homer), got {member:?}"
    );
    let non_member = interp
        .call("test.wi714rec.abeAncBart", &[])
        .expect("the non-member ground citation must run");
    assert!(
        matches!(non_member, Value::Int(0)),
        "`anc(\"abe\", \"bart\")` is not in the closure, got {non_member:?}"
    );
}

/// The algebra still composes over a recursive relation: projecting onto the
/// recursion-typed column keeps bag multiplicity (OQ6) — 5 closure rows → 5 values.
#[test]
fn wi714_recursive_relation_projects() {
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi714rec.ancestors", &[])
        .expect("projection over a recursive relation must run");
    let mut got = collect_strings(&r);
    got.sort();
    assert_eq!(
        got,
        vec!["abe", "abe", "abe", "homer", "homer"],
        "projection is a BAG: every closure row contributes its `e`"
    );
}

/// The fix is NOT self-reference-specific: it keys on a column being unconstrained,
/// so MUTUAL recursion (which a self-reference-specific rule would miss) types the
/// same way. `descA`'s recursive clause types `?e` only through `descB`.
#[test]
fn wi714_mutually_recursive_relation_types() {
    let src = r#"
namespace test.wi714mutual
  import anthill.prelude.{String, Int64, Option, List}

  sort Family
    entity parent(of: String, is: String)
  end
  fact parent(of: "bart", is: "homer")
  fact parent(of: "homer", is: "abe")

  rule descA(?c, ?e) :- parent(of: ?c, is: ?e)
  rule descA(?c, ?e) :- parent(of: ?c, is: ?m), descB(?m, ?e)
  rule descB(?c, ?e) :- descA(?c, ?e)

  operation closure() -> List[(c: String, e: String)] effects Error =
    let r = descA
    r.takeN(50)
end
"#;
    let mut interp = interp_for(src);
    let r = interp
        .call("test.wi714mutual.closure", &[])
        .expect("a mutually recursive rule cited by name must load and drain");
    let mut got = collect_pairs(&r);
    got.sort();
    let mut want = vec![
        ("bart".to_string(), "homer".to_string()),
        ("homer".to_string(), "abe".to_string()),
        ("bart".to_string(), "abe".to_string()),
    ];
    want.sort();
    assert_eq!(got, want, "mutual recursion types via the same unconstrained-column rule");
}

/// THE GUARD THAT MUST SURVIVE: two clauses that BOTH type a column concretely, at
/// genuinely disjoint types (String vs Int64), are still a loud LOAD error. The
/// relaxation applies ONLY where a clause carries no information — it must never
/// silently widen a real conflict (WI-714 CORE piece 3: "a disjoint pair with no lub
/// is a LOAD error, never a silent widen to Term").
#[test]
fn wi714_disjoint_concrete_column_types_still_reject() {
    let src = r#"
namespace test.wi714disjoint
  import anthill.prelude.{String, Int64, Option, List}

  sort Family
    entity parent(of: String, is: String)
    entity num(v: Int64)
  end
  fact parent(of: "bart", is: "homer")
  fact num(v: 7)

  rule mixed(?x) :- parent(of: ?x, is: ?y)
  rule mixed(?x) :- num(v: ?x)

  operation bad() -> List[String] effects Error =
    let r = mixed
    r.takeN(50)
end
"#;
    let errs = try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.iter()
            .any(|e| e.contains("disjoint types for column") || e.contains("common column type")),
        "two clauses typing a column at genuinely disjoint CONCRETE types must stay a \
         loud load error, got: {errs:?}"
    );
}
