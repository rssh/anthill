//! WI-182 — `anthill.reflect.fresh_var[T](name) -> T`.
//!
//! Closes phase 1 of WI-009: until this builtin existed, anthill code could
//! not construct `Term::Var(Var::Global(_))` values, which `pattern_query`
//! requires for any goal that wants its bindings extracted (the variables
//! are the named holes the resolver fills in). Without it, `cmd_next`
//! couldn't run `pattern_query(claimable(?id, ?desc))` from the bundle.
//!
//! WI-406 retyped `fresh_var` from `-> Term` to `[T] -> T`, so a hole is a
//! `T`-kinded logic var: a `String`-field hole is `fresh_var[String](name)`,
//! and the typed pattern reflects to a `Term` via `as_term` at `pattern_query`.
//!
//! This test exercises the full anthill-side flow:
//!   * call `fresh_var[String]("id")` / `fresh_var[String]("p")` from inside
//!     an operation;
//!   * build a constructor `Item(id: ?id, name: ?p)` whose args are the
//!     returned `T`-kinded logic vars;
//!   * `as_term(goal)` then `pattern_query(...)`, run via `KB.execute(kb(), q)`;
//!   * splitFirst the resulting stream, lookup the bindings by name,
//!     return the bound id string.


use anthill_core::eval::Value;
use crate::common::interp_for;

#[test]
fn fresh_var_builtin_returns_distinct_term_per_call() {
    // Two calls with the same name produce distinct VarIds. The display
    // name is identical (so `lookup` retrieves the latest binding by
    // name), but the underlying `Term::Var(Var::Global(vid))` differs.
    let src = r#"
namespace test.wi182_distinct
  import anthill.reflect.{Term, fresh_var}
  operation main() -> Int64 = 0
end
"#;
    let mut interp = interp_for(src);
    let v1 = interp.call("anthill.reflect.fresh_var", &[Value::Str("x".into())])
        .expect("fresh_var #1");
    let v2 = interp.call("anthill.reflect.fresh_var", &[Value::Str("x".into())])
        .expect("fresh_var #2");
    let t1 = match v1 { Value::Term { id: t, .. } => t, other => panic!("expected Term, got {other:?}") };
    let t2 = match v2 { Value::Term { id: t, .. } => t, other => panic!("expected Term, got {other:?}") };
    assert_ne!(t1, t2, "two fresh_var calls should yield distinct Term ids");
}

#[test]
fn fresh_var_drives_pattern_query_end_to_end() {
    // Acceptance fixture for WI-182. The user-facing surface this enables
    // is exactly the cmd_next port: build pattern_query(claimable(?id, ?d))
    // from anthill code, run it, recover bindings via Substitution.lookup.
    //
    // We use a minimal `kin(parent, child)` relation rather than the
    // full claimable rule so the test is independent of stage0 workflow
    // rules and stays a pure builtin smoke.
    let src = r#"
namespace test.wi182_query
  import anthill.prelude.{LogicalStream, Stream, Option, Pair, String, Error}
  import anthill.prelude.Stream.{splitFirst}
  import anthill.prelude.Pair.{pair}
  import anthill.prelude.Option.{some, none}
  import anthill.reflect.{Term, Substitution, Solution, fresh_var, as_term}
  import anthill.reflect.Solution.{definite, undecided}
  import anthill.reflect.KB.{kb, execute}
  import anthill.reflect.LogicalQuery.{pattern_query}
  import anthill.reflect.Substitution.{lookup}
  import anthill.reflect.{term_as_string}

  -- Mirrors the `WorkItem(id: ?id, ...)` shape that cmd_next will hit
  -- in real use — a fact with String fields rather than Entity refs,
  -- so the Term::Const(String(_)) literal in the fact hash-cons matches
  -- the resolver-side fresh var without an Entity-vs-Ref mismatch.
  sort Inventory
    entity Item(id: String, name: String)
  end
  fact Item(id: "X-001", name: "alice")

  -- Drive the resolver via fresh_var → pattern_query → splitFirst →
  -- lookup. Each branch returns a distinctive String so the outer test
  -- can assert which path was reached.
  operation first_parent_name() -> String effects Error =
    let id_var = fresh_var[String]("id")
    let name_var = fresh_var[String]("p")
    let goal = Item(id: id_var, name: name_var)
    let stream = execute(kb(), pattern_query(term: as_term(goal)))
    -- WI-714: `execute` yields a `Stream[Solution]`; split it via `Stream.splitFirst`
    -- (imported unqualified; LogicalStream.splitFirst's self-receiver no longer
    -- accepts a bare Stream).
    let head = splitFirst(stream)
    match head
      case none() -> "no-solution"
      case some(p) -> after_split(p)

  -- WI-531: the stream element is a `Solution` (definite | undecided); read the
  -- binding off whichever arm (this Item query is definite).
  operation after_split(p: Pair[A = Solution, B = Stream]) -> String =
    match p
      case pair(definite(subst), _)     -> after_lookup(lookup(subst, "p"))
      case pair(undecided(subst, _), _) -> after_lookup(lookup(subst, "p"))

  operation after_lookup(opt: Option[T = Term]) -> String =
    match opt
      case none() -> "no-binding"
      case some(t) -> render_term(t)

  operation render_term(t: Term) -> String =
    match term_as_string(t)
      case none() -> "no-string"
      case some(s) -> s
end
"#;
    let mut interp = interp_for(src);
    // Exactly one solution matches the pattern_query: the user-asserted
    // fact, binding "alice". (WI-515: the loader's synthetic entity
    // declaration used to ride along as a nondeterministically-ordered
    // second match, forcing this test to also accept "no-string".)
    let r = interp.call("test.wi182_query.first_parent_name", &[])
        .expect("call first_parent_name");
    match r {
        Value::Str(s) => assert_eq!(
            s, "alice",
            "the user-fact match must bind the parent name",
        ),
        other => panic!("expected Str, got {other:?}"),
    }
}
