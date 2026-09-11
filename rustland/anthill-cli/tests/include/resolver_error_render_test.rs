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
//! CONTROLS: `a_well_typed_comparison_warns_about_nothing` passes either way by design —
//! it says the channel is not simply always loud. Back out the render loop in
//! `main.rs` and `an_unorderable_comparison_is_explained` alone fails.

use crate::common::{anthill, fixtures_dir};

fn query(goal: &str) -> crate::common::Output {
    let kb = fixtures_dir("resolve_errors").join("kb.anthill");
    anthill(&["query", "-p", kb.to_str().unwrap(), goal])
}

#[test]
fn an_unorderable_comparison_is_explained() {
    let out = query("cli.mix.answer(?r)");
    assert!(
        out.has_diagnostic("warning:", "two DIFFERENT literal sorts"),
        "the query must explain WHY the goal could not be decided, naming the operand \
         sorts;\nstdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    // The answer itself is unchanged: still a conditional row carrying the residual.
    // This is WI-879's property, which the error channel had to preserve rather than
    // replace — an un-evaluable goal residualizes, it does not vanish and does not fail.
    assert!(
        out.stdout.contains("residual"),
        "the residual answer must still print;\nstdout:\n{}",
        out.stdout
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
