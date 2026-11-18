//! WI-20261113-S4D63 — the SLD bridge is passed the dictionaries of a call the typer reads. A
//! query's goal and an integrity guard's are typed where they are read, as a rule body's goal
//! is (proposal 073 §6.2); a goal that calls an operation taking dictionaries — its own
//! `requires` or its sort's — is typed there too, and its dictionaries are handed to the call,
//! so none is derived from the argument values when it runs (kernel-language §5.2: only a
//! call no typer reads is). Before, only a goal calling a spec operation that owes an instance
//! was typed there: `contains(?ls, "z")` over `List.contains(l, x) requires Eq[T]` reached the
//! bridge with nothing passed, and `Eq[T = String]` was built from the value.
//!
//! The answers are the same either way for these programs; what is asserted is where the
//! dictionary comes from, counted by `bridge_derivations_by_this_thread`.

use anthill_core::kb::resolve::{bridge_derivations_by_this_thread, ResolveConfig};

use crate::common::{load_errors_of, load_kb_with, load_stdlib_kb, query_goals, query_pattern_refusals, run_time_goals};

fn boxes(ns: &str, items: &str, constraint: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{List, String, Bool}}
  import anthill.prelude.List.{{contains}}
  sort Box
    entity Box(items: List[T = String])
  end
{constraint}
  fact Box(items: {items})
end
"#
    )
}

/// A guard's goal is passed its dictionary: `no ?ls: Box(items: ?ls) -: contains(?ls, "z")`
/// is violated over `["z"]` and holds over `["a"]`, and the load derives no dictionary from a
/// value. FAILS, the count, with a goal calling an operation that takes dictionaries left
/// untyped (`typed_spec_op_calls`): 1 derived for each load.
#[test]
fn a_guard_goal_is_passed_its_dictionary() {
    let guard = "  constraint noZ:\n    no ?ls: Box(items: ?ls) -: contains(?ls, \"z\")";
    for (n, (items, violated)) in [(r#"["z"]"#, true), (r#"["a"]"#, false)].into_iter().enumerate() {
        drop(load_stdlib_kb());
        let before = bridge_derivations_by_this_thread();
        let errors = load_errors_of(&boxes(&format!("s4d63.br.g{n}"), items, guard));
        let derived = bridge_derivations_by_this_thread() - before;
        assert_eq!(
            errors.iter().any(|e| e.contains("'noZ' is violated")),
            violated,
            "{items}: {errors:?}"
        );
        assert_eq!(derived, 0, "{items}: a dictionary derived from the values");
    }
}

/// A written query's goal is passed its dictionary too, and answers once; the same goals built
/// at run time and typed by no load are the route that still derives one (§5.2), the control.
/// FAILS, the typed half's count, with the goal left untyped.
#[test]
fn a_query_goal_is_passed_its_dictionary() {
    let mut kb = load_kb_with(&boxes("s4d63.br.q", r#"["z"]"#, ""));
    let patterns = ["s4d63.br.q.Box(items: ?ls)", "anthill.prelude.List.contains(?ls, \"z\")"];
    let typed = query_goals(&mut kb, &patterns);
    let before = bridge_derivations_by_this_thread();
    let sols = kb.resolve(&typed, &ResolveConfig::default());
    assert_eq!(sols.iter().filter(|s| s.is_definite()).count(), 1, "one definite answer");
    assert_eq!(bridge_derivations_by_this_thread() - before, 0, "typed: derived nothing");
    let untyped = run_time_goals(&mut kb, &patterns);
    let before = bridge_derivations_by_this_thread();
    let sols = kb.resolve(&untyped, &ResolveConfig::default());
    assert_eq!(sols.iter().filter(|s| s.is_definite()).count(), 1, "one definite answer");
    assert!(bridge_derivations_by_this_thread() > before, "run-time goals: derived from the value");
}

/// A query has no caller: a goal whose dictionary is at a type the query leaves open is
/// refused where it is read, as a spec operation's is (proposal 073 §6.2). FAILS with the goal
/// left untyped: it converts, and its dictionary is derived when it runs.
#[test]
fn a_query_goal_at_an_open_type_is_refused() {
    let mut kb = load_kb_with(&boxes("s4d63.br.o", r#"["z"]"#, ""));
    let refused = query_pattern_refusals(&mut kb, "anthill.prelude.List.contains(?ls, ?x)");
    assert!(!refused.is_empty(), "refused where it is read");
}

/// A call holding a lambda is typed whole, as the operation-body typer types it, once the clause
/// types what the lambda's body reads: `?r <=> Error.reify(lambda () -> maybe(1))` is a
/// `Result[E = Boom, T = Int64]`, the lambda's row naming the error, so `Result.reflect(?r)`'s
/// `TypeValue[T = Boom]` is built at load and the call answers `3` with nothing derived. FAILS,
/// the count, with the call's result read off `reify`'s signature alone, its error type open: 1
/// derived from the value when `reflect` runs.
#[test]
fn a_call_holding_a_lambda_is_typed_with_it() {
    let mut kb = load_kb_with(
        r#"
namespace s4d63.br.reify
  import anthill.prelude.{Int64, String, Error, Result}
  sort Boom
    entity boom(why: String)
  end
  operation maybe(n: Int64) -> Int64 effects {Error[Boom]} =
    if n > 0 then 3 else Error.raise(boom("none"))
  rule split(?n) :- ?r <=> Error.reify(lambda () -> maybe(1)), ?n <=> Result.reflect(?r)
end
"#,
    );
    let before = bridge_derivations_by_this_thread();
    assert_eq!(crate::common::one_definite_int(&mut kb, "s4d63.br.reify.split"), Some(3));
    assert_eq!(bridge_derivations_by_this_thread() - before, 0, "a dictionary derived from the values");
}
