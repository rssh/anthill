//! `anthill query` renders the resolver's own faults.
//!
//! WHY THIS FILE EXISTS, and it is not a nice-to-have. The resolver used to explain an
//! un-evaluable goal by writing to stderr from `trace_no_order` — the only thing it
//! could do, because `BuiltinResult` had no error channel. Giving it one
//! (`BuiltinResult::Error` → `ResolveStats::errors`) and deleting that `eprintln!`
//! DELETED the diagnostic outright: `KnowledgeBase::resolve` drops stats, and no
//! production site read the new list. Measured — `anthill query` over `gt("a", 1)`
//! explained itself before the change and printed nothing after. A channel with no
//! reader is not a channel.
//!
//! Nothing caught it, and that is the second half of the point: the old diagnostic was
//! an `eprintln!` deduped in a process-wide `thread_local`, which no test could assert
//! on. The behaviour was user-visible and untested for exactly as long as it was
//! unreachable to a test.
//!
//! Since a query is typed where it is read (proposal 073 §6.2), `gt("a", 1)` is refused
//! before it runs, and the fault the channel carries here is one a well-typed query meets
//! when it runs: `1 / 0`.
//!
//! CONTROLS: `a_well_typed_comparison_warns_about_nothing` passes either way by design —
//! it says the channel is not simply always loud. Back out the render loop in
//! `main.rs` and `a_fault_the_search_meets_is_explained` alone fails.

use crate::common::{anthill, fixtures_dir};

fn query(goal: &str) -> crate::common::Output {
    let kb = fixtures_dir("resolve_errors").join("kb.anthill");
    anthill(&["query", "-p", kb.to_str().unwrap(), goal])
}

/// A fault the search meets when a goal runs is explained, before the rows: `?x <=> 1 / 0`
/// raises in `Int64.div`, and the query says the call produced no value and the search is
/// incomplete. An un-evaluable goal does not pass as a refutation (WI-879's property, which the
/// channel had to keep).
#[test]
fn a_fault_the_search_meets_is_explained() {
    let out = query("?x <=> 1 / 0");
    assert!(
        out.has_diagnostic("warning:", "could not be evaluated by the resolver"),
        "the query must explain why the goal produced no value;\nstdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    assert!(
        out.stdout.contains("the search is INCOMPLETE"),
        "an empty answer here is undecided, not refuted;\nstdout:\n{}",
        out.stdout
    );
}

/// The `String`/`Int64` pair asked as a query is refused where the query is read, naming the
/// types, as it is in a clause (below): it reached the resolver, which explained it as a fault
/// and answered a residual.
#[test]
fn an_unorderable_comparison_in_a_query_is_refused_where_it_is_read() {
    let out = query("anthill.kernel.and(cli.mix.tag(?x), anthill.prelude.PartialOrd.gt(?x, 1))");
    assert!(
        out.has_diagnostic("error:", "type mismatch in gt.b (op-arg): expected String, got Int64"),
        "stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    assert!(!out.stdout.contains("residual"), "nothing ran;\nstdout:\n{}", out.stdout);
}

/// The same comparison written in a clause is refused at load, the column `tag` gives `?x`
/// against the `Int64` the comparison's literal asks (068-implementation §6.2, decision 3).
#[test]
fn the_comparison_written_in_a_clause_is_refused_at_load() {
    let kb = fixtures_dir("resolve_errors").join("kb.anthill");
    let written = std::fs::read_to_string(&kb).unwrap().replace(
        "  fact num(7)\n",
        "  rule answer(?r) :- tag(?x), PartialOrd.gt(?x, 1), unify(?r, 5)\n  fact num(7)\n",
    );
    let path = crate::common::write_temp("resolve_errors_written.anthill", &written);
    let out = anthill(&["load", path.to_str().unwrap()]);
    assert!(
        out.has_diagnostic("error:", "type mismatch in tag._1 (rule-column): expected String, got Int64"),
        "stderr:\n{}",
        out.stderr
    );
}

#[test]
fn a_well_typed_comparison_warns_about_nothing() {
    // CONTROL (passes either way by design).
    let out = query("cli.mix.ok(?r)");
    assert!(
        !out.stderr.contains("two DIFFERENT literal sorts"),
        "a healthy comparison must not warn;\nstderr:\n{}",
        out.stderr
    );
    assert!(
        out.stdout.contains("?r = 5"),
        "`gt(7, 1)` holds, so the rule answers;\nstdout:\n{}",
        out.stdout
    );
}
