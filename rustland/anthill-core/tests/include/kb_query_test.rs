//! An anthill program that *queries the knowledge base* through reflect.
//!
//! Demonstrates the full query surface from anthill source: obtain the ambient
//! KB with `kb()` (the zero-arg reflect operation — WI-313), build a goal term
//! with a `fresh_var` hole, run it via `KB.execute(kb(), pattern_query(...))`,
//! pull the first solution with `LogicalStream.splitFirst`, and read the bound
//! value with `Substitution.lookup`. The query runs against the interpreter's
//! real `KnowledgeBase` (the `kb()` value is an ignored sentinel).
//!
//! Deterministic by construction: the goal pins `role` to the literal
//! `"admin"`. The loader also asserts a synthetic entity-declaration fact
//! `Person(name: sort_ref(String), role: sort_ref(String))` (type terms in the
//! slots), but a concrete `Const("admin")` does not unify with `sort_ref(String)`,
//! so the declaration — and the `role: "user"` row — are excluded; only the
//! `alice`/`admin` fact matches.

use anthill_core::eval::Value;
use crate::common::interp_for;

#[test]
fn anthill_program_queries_kb_for_matching_fact() {
    let src = r#"
namespace test.kb_query
  import anthill.prelude.{LogicalStream, Option, Pair, String, Error}
  import anthill.prelude.LogicalStream.{splitFirst}
  import anthill.prelude.Pair.{pair}
  import anthill.prelude.Option.{some, none}
  import anthill.reflect.{Term, Substitution, fresh_var, term_as_string}
  import anthill.reflect.KB.{kb, execute}
  import anthill.reflect.LogicalQuery.{pattern_query}
  import anthill.reflect.Substitution.{lookup}

  sort Directory
    entity Person(name: String, role: String)
  end
  fact Person(name: "alice", role: "admin")
  fact Person(name: "bob",   role: "user")

  -- Query the KB for the person whose role is "admin" and return their name.
  -- `role: "admin"` is the concrete discriminator (only the alice fact qualifies);
  -- `name` is the fresh-var hole whose binding we recover.
  operation admin_name() -> String effects Error =
    let goal = Person(name: fresh_var("n"), role: "admin")
    match splitFirst(execute(kb(), pattern_query(term: goal)))
      case none()   -> "no-admin"
      case some(p)  -> name_of(p)

  operation name_of(p: Pair[Substitution, LogicalStream]) -> String =
    match p
      case pair(subst, _) -> string_of(lookup(subst, "n"))

  operation string_of(opt: Option[T = Term]) -> String =
    match opt
      case none()   -> "no-binding"
      case some(t)  -> render(t)

  operation render(t: Term) -> String =
    match term_as_string(t)
      case none()   -> "no-string"
      case some(s)  -> s
end
"#;
    let mut interp = interp_for(src);
    let r = interp
        .call("test.kb_query.admin_name", &[])
        .expect("call admin_name");
    match r {
        Value::Str(s) => assert_eq!(
            s, "alice",
            "querying role=\"admin\" should bind name to \"alice\"; got {s:?}",
        ),
        other => panic!("expected Str(\"alice\"), got {other:?}"),
    }
}
