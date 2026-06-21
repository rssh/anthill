//! WI-531 — `KB.execute` streams `Solution` (definite | undecided), carrying a
//! floundered branch's residual goals as DATA.
//!
//! WI-519 made the *verdict* honest (a floundered residual is not a definite
//! answer). This WI adds the *data*: the streamed element is now a reflect
//! `Solution`, and the `undecided` arm exposes the undischarged goals so anthill
//! consumers can inspect WHICH goals stayed pending — matching what Rust
//! consumers already see from `SearchStream::split_first`. Undecidedness is a
//! third logical outcome carried in the stream as the `undecided` DATA case,
//! NOT raised on `execute`'s `E = Error` channel.
//!
//! The probe reuses the proven `kb_query` shape (an entity-pattern query via
//! `pattern_query(as_term(...))`), but resolves an entity-headed rule whose body
//! `eq(?a, ?b)` floods (two unbound operands `eq` cannot decide). So `execute`
//! yields exactly one `undecided(subst, residual)` whose `residual` is the
//! pending `eq` goal — observed here from anthill by counting the residual list.

use anthill_core::eval::Value;
use crate::common::interp_for;

#[test]
fn execute_streams_undecided_solution_carrying_residual() {
    let src = r#"
namespace test.wi531_residual
  import anthill.prelude.{LogicalStream, Option, Pair, String, Error, List, Int64}
  import anthill.prelude.LogicalStream.{splitFirst}
  import anthill.prelude.Pair.{pair}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.List.{cons, nil}
  import anthill.reflect.{Term, Substitution, Solution, fresh_var, as_term}
  import anthill.reflect.Solution.{definite, undecided}
  import anthill.reflect.KB.{kb, execute}
  import anthill.reflect.LogicalQuery.{pattern_query}

  sort Directory
    entity Person(name: String, role: String)
  end

  -- An entity-headed rule deriving a "ghost" Person whose body FLOUNDERS:
  -- `eq(?a, ?b)` over two unbound vars is undecidable, so resolving this rule
  -- yields an UNDECIDED solution carrying the residual `eq` goal — not a
  -- definite answer (WI-519), and now with the residual as data (WI-531).
  rule Person(name: ?n, role: "ghost") :- eq(?a, ?b)

  -- Length of the streamed Solution's residual goal list. A value >= 1 proves
  -- `execute` delivered an `undecided` Solution whose pending goals survived as
  -- DATA. Negative sentinels flag the wrong shape (no solution / masqueraded as
  -- definite), so the test distinguishes "residual carried" from every failure.
  operation ghost_residual() -> Int64 effects Error =
    let g = Person(name: fresh_var[String]("n"), role: "ghost")
    match splitFirst(execute(kb(), pattern_query(term: as_term(g))))
      case none()  -> 0 - 1
      case some(p) -> outcome_of(p)

  operation outcome_of(p: Pair[Solution, LogicalStream]) -> Int64 =
    match p
      case pair(definite(_), _)     -> 0 - 2
      case pair(undecided(_, r), _) -> len(r)

  operation len(xs: List[T = Term]) -> Int64 =
    match xs
      case nil()         -> 0
      case cons(_, rest) -> 1 + len(rest)
end
"#;
    let mut interp = interp_for(src);
    let r = interp
        .call("test.wi531_residual.ghost_residual", &[])
        .expect("call ghost_residual");
    match r {
        Value::Int(n) => assert!(
            n >= 1,
            "a floundered query must stream an `undecided` Solution carrying its \
             residual goal(s) as data; got {n} (-1 = no solution, -2 = masqueraded \
             as definite, 0 = undecided but residual dropped)",
        ),
        other => panic!("expected Int residual count, got {other:?}"),
    }
}
