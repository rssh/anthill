//! An anthill program that *queries the knowledge base* through reflect.
//!
//! Demonstrates the full query surface from anthill source: obtain the ambient
//! KB with `kb()` (the zero-arg reflect operation — WI-313), build a goal term
//! with a `fresh_var` hole, run it via `KB.execute(kb(), pattern_query(...))`,
//! pull the first solution with `Stream.splitFirst`, and read the bound
//! value with `Substitution.lookup`. The query runs against the interpreter's
//! real `KnowledgeBase` (the `kb()` value is an ignored sentinel).
//!
//! Deterministic by construction: the goal pins `role` to the literal
//! `"admin"`, so only the `alice` fact matches (the `role: "user"` row is
//! excluded). WI-515: the loader no longer asserts the synthetic same-functor
//! entity-declaration fact (`Person(name: <String type>, role: <String type>)`)
//! that a var-quantified query used to spuriously match — a concrete
//! discriminator is no longer load-bearing against phantom rows.

use crate::common::interp_for;
use anthill_core::eval::Value;

#[test]
fn anthill_program_queries_kb_for_matching_fact() {
    let src = r#"
namespace test.kb_query
  import anthill.prelude.{Stream, Option, Pair, String, Error}
  -- WI-20260829-1SSXM: `Stream.splitFirst`, not `LogicalStream`'s. `execute` returns a
  -- BARE `Stream[T = Solution, E = Error]`, and provision runs `LogicalStream provides
  -- Stream`, not the reverse — so a `LogicalStream` param cannot accept it. This used to
  -- load because the mismatch sat in a match SCRUTINEE, whose error the typer dropped;
  -- it worked at run time only because eval dispatches on the VALUE (which really is a
  -- LogicalStream). The stdlib says as much on `LogicalStream.splitFirst`: "a value typed
  -- as a bare `Stream` (e.g. `execute`'s `Stream[Solution]`) splits via `Stream.splitFirst`".
  import anthill.prelude.Stream.{splitFirst}
  import anthill.prelude.Pair.{pair}
  import anthill.prelude.Option.{some, none}
  import anthill.reflect.{Term, Substitution, Solution, fresh_var, term_as_string, as_term}
  import anthill.reflect.Solution.{definite, undecided}
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
    let goal = Person(name: fresh_var[String]("n"), role: "admin")
    match splitFirst(execute(kb(), pattern_query(term: as_term(goal))))
      case none()   -> "no-admin"
      case some(p)  -> name_of(p)

  -- WI-531: execute now streams `Solution` (definite | undecided), not bare
  -- Substitution — so the consumer DECIDES. Here we just read the bindings
  -- from either arm (this admin query is definite; the undecided arm exercises
  -- the residual-carrying shape).
  operation name_of(p: Pair[A = Solution, B = Stream[T = Solution, E = Error]]) -> String =
    match p
      case pair(sol, _) -> string_of(lookup(subst_of(sol), "n"))

  operation subst_of(sol: Solution) -> Substitution =
    match sol
      case definite(subst)     -> subst
      case undecided(subst, _) -> subst

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
