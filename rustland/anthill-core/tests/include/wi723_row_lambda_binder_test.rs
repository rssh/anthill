//! WI-723 (proposal 052) — a Relation NAMED-TUPLE schema (`r.T`) resolves as a
//! ROW-LAMBDA BINDER type, so `c.x` (WI-638 named-tuple field access) type-checks.
//!
//! `where(r, cond: (c: r.T) -> Bool)` filters a relation by a row condition whose
//! binder `c` names the row; a column is reached as a TYPED field access `c.x`
//! resolved against `r`'s schema. For that to type-check the binder `c` must be
//! typed at the CONCRETE schema, not the abstract projection `r.T`.
//!
//! Two typer/loader gaps closed here (both diagnosed empirically):
//!   (a) a bare RULE-reference receiver (`person_row.where(λ)`, where `person_row`
//!       is a `Relation[T]` value, WI-714) was flattened to a qualified name
//!       `person_row.where` applied to the lambda — never a dot call — so `where`'s
//!       arrow param could not hint the lambda binder. It now re-routes to a dot
//!       call (`where(person_row, λ)`), like a let-local receiver already did.
//!   (b) that dot-call receiver is a rule reference, not bound in the value env, so
//!       the callback param projection `(c: r.T) -> Bool` could not be eliminated
//!       against it — the receiver's stamped type is now read as a fallback, so
//!       `r.T` grounds to the concrete named tuple and `c` is typed at the schema.
//!
//! This is the TYPER prerequisite of WI-714's `where`; the runtime `where` mechanism
//! (the `guarded_of` macro / `where_run` back-end) is exercised by
//! `wi714_where_test` and is out of scope here (this file asserts type-checking only).

use crate::common::try_load_kb_with;

/// Common domain: a two-column relation `person_row : Relation[(name: String, age:
/// Int64)]`, plus one operation body whose text is the parameter.
fn src(body: &str) -> String {
    format!(
        r#"
namespace test.wi723
  import anthill.prelude.{{String, Int64, Option, List, Pair, Unit, Bool}}
  import anthill.prelude.Relation.{{where}}
  import anthill.prelude.PartialEq.{{eq}}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)

  -- two free head vars → Relation[(name: String, age: Int64)]
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  operation probe() -> Bool effects Error =
    {body}
end
"#
    )
}

/// ACCEPTANCE: a bare rule-reference receiver `person_row.where(λ)` type-checks — the
/// named-tuple schema resolves as the row-lambda binder type, so `c.name` (a String
/// column) is a valid field access compared against a String literal.
#[test]
fn wi723_named_tuple_schema_types_row_lambda_binder() {
    let source = src(
        r#"let r = person_row.where(lambda c -> eq(c.name, "alice"))
    r.isEmpty"#,
    );
    if let Err(errs) = try_load_kb_with(&source) {
        panic!(
            "person_row.where(λ) over a named-tuple relation should type-check \
             (c : (name, age), c.name : String); got {} error(s):\n{}",
            errs.len(),
            errs.join("\n"),
        );
    }
}

/// The binder's column types are CONCRETE, not a demand-absorbing var: `c.name` is
/// `String`, so comparing it to an `Int64` literal is a genuine type mismatch (an
/// unresolved-var binder would instead unify `c.name` to `Int64` and pass).
#[test]
fn wi723_row_lambda_column_type_is_concrete_string() {
    let source = src(
        r#"let r = person_row.where(lambda c -> eq(c.name, 42))
    r.isEmpty"#,
    );
    match try_load_kb_with(&source) {
        Ok(_) => panic!(
            "eq(c.name, 42) must be rejected — c.name is String, not an unresolved var \
             that unifies to Int64"
        ),
        Err(errs) => {
            let joined = errs.join("\n");
            assert!(
                joined.contains("String") && joined.contains("Int64"),
                "expected a String-vs-Int64 mismatch on c.name; got:\n{joined}",
            );
        }
    }
}

/// The OTHER column resolves too: `c.age` is `Int64`, so comparing it to a String
/// literal is the symmetric mismatch — schema resolution is per-column, not just the
/// first field.
#[test]
fn wi723_row_lambda_second_column_type_is_concrete_int() {
    let source = src(
        r#"let r = person_row.where(lambda c -> eq(c.age, "thirty"))
    r.isEmpty"#,
    );
    match try_load_kb_with(&source) {
        Ok(_) => panic!("eq(c.age, \"thirty\") must be rejected — c.age is Int64, not String"),
        Err(errs) => {
            let joined = errs.join("\n");
            assert!(
                joined.contains("String") && joined.contains("Int64"),
                "expected an Int64-vs-String mismatch on c.age; got:\n{joined}",
            );
        }
    }
}

/// A let-LOCAL receiver bound to the rule reference (`let pr = person_row; pr.where(λ)`)
/// resolves the schema through the SAME dot-call path — the two receiver forms agree.
#[test]
fn wi723_local_receiver_resolves_schema_identically() {
    let source = src(
        r#"let pr = person_row
    let r = pr.where(lambda c -> eq(c.name, "alice"))
    r.isEmpty"#,
    );
    if let Err(errs) = try_load_kb_with(&source) {
        panic!(
            "a let-local receiver bound to the rule ref should type-check identically; \
             got {} error(s):\n{}",
            errs.len(),
            errs.join("\n"),
        );
    }
}
