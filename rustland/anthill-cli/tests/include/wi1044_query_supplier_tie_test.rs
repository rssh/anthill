//! WI-1044 — `anthill query` REFUSES a pattern whose spec-op call has two suppliers,
//! and answers the SUPPLIED implementation where it has one.
//!
//! The core-side coverage (the resolver's value-directed classification, the message
//! body, the controls) is `anthill-core`'s `wi1044_query_spec_op_dispatch_test`. What
//! only this binary can show is that the refusal reaches the FRONT DOOR: printed to
//! stderr, exit 1, and with no answer printed beside it.
//!
//! Why the front door is where the tie is caught at all: a top-level query is written
//! in no rule body and no operation body, so no load pass ever sees the call, and the
//! resolver — which does see it — has no diagnostic channel (`BuiltinResult` is
//! Success / Bindings / Delay / Failure; `bridge_op_to_eval` residualizes an
//! `AmbiguousSpecOpDispatch` to `None` by design). MEASURED before this: the program
//! below loads clean and the two-supplier query printed `1 solution` — the spec's
//! DEFAULT — with two rival implementations in the file.
//!
//! The one-supplier arm is here for the same reason the core suite pairs them: a
//! refusal test alone would pass equally if the query path had stopped answering
//! anything at all.

use crate::common::{anthill, write_temp};

/// One spec with a DEFAULT, one carrier, and `extra` supply text appended at namespace
/// level. `Leaf` declares its own `describe`, so `extra` decides whether that member
/// has a rival.
fn program(extra: &str) -> String {
    format!(
        r#"namespace wi1044
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
{extra}end
"#
    )
}

const RIVAL: &str = "\n  operation otherDescribe(x: Leaf) -> Int64 = 9\n\n  \
                     fact Desc[T = Leaf, describe = otherDescribe]\n";

const PATTERN: &str = "wi1044.Desc.describe(wi1044.Leaf.leaf(), ?r)";

fn query(name: &str, src: &str) -> crate::common::Output {
    let path = write_temp(name, src);
    anthill(&["query", "-p", path.to_str().unwrap(), PATTERN])
}

/// The same pattern in `--match` STRUCTURAL BROWSE mode, which evaluates no body.
fn browse(name: &str, src: &str) -> crate::common::Output {
    let path = write_temp(name, src);
    anthill(&["query", "-p", path.to_str().unwrap(), "--match", PATTERN])
}

/// ONE supplier — the carrier's own member. The query must reach `7`, not the spec's
/// default `1`. Both numbers are in the program, so neither can appear by accident.
#[test]
fn a_one_supplier_query_prints_the_supplied_impl() {
    let out = query("wi1044_one.anthill", &program(""));
    assert_eq!(
        out.code, 0,
        "the one-supplier program is legal and must answer; stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr,
    );
    // Whole-line, not a substring: `1 solution(s)` contains both digits, so a
    // substring check could not tell the supplied `7` from the default `1`.
    assert!(
        out.has_stdout_line("?r = 7"),
        "the query must reach the implementation `Leaf` supplies; stdout:\n{}",
        out.stdout,
    );
    assert!(
        !out.has_stdout_line("?r = 1"),
        "…and must not print the spec's DEFAULT, which is what it printed before \
         WI-1044; stdout:\n{}",
        out.stdout,
    );
}

/// TWO suppliers — the carrier's own member beside an instance fact binding a
/// different operation. The PROGRAM is legal (058 §4.9 refuses at the CALL, and no
/// rule or operation in this file makes one), so the query is the call and the query
/// is where it is refused.
#[test]
fn a_two_supplier_query_is_refused_at_the_front_door() {
    let out = query("wi1044_two.anthill", &program(RIVAL));
    assert_eq!(
        out.code, 1,
        "a call with two suppliers must be refused; stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr,
    );
    assert!(
        out.has_diagnostic("error:", "ambiguous dispatch of `wi1044.Desc.describe`"),
        "the refusal must name the spec op; stderr:\n{}",
        out.stderr,
    );
    assert!(
        out.has_diagnostic("error:", "carrier `wi1044.Leaf`"),
        "…and the carrier; stderr:\n{}",
        out.stderr,
    );
    // Each rival by its SUPPLY ROUTE — the three routes are three different syntaxes,
    // and the author has to know which text to delete.
    assert!(
        out.has_diagnostic("error:", "the carrier's own member 'wi1044.Leaf.describe'"),
        "route 1 named by its route; stderr:\n{}",
        out.stderr,
    );
    assert!(
        out.has_diagnostic(
            "error:",
            "an instance fact binding `describe = wi1044.otherDescribe`",
        ),
        "route 2 quoted by the BINDING the author wrote; stderr:\n{}",
        out.stderr,
    );
    // The whole point: a refused query must not ALSO print an answer. Before this it
    // printed one, and it was the spec's default.
    assert!(
        !out.stdout.contains("solution"),
        "a refused query must not also answer; stdout:\n{}",
        out.stdout,
    );
}

/// A `--match` STRUCTURAL BROWSE of the same two-supplier pattern is NOT refused.
///
/// Found by this ticket's own `/code-review`, which is also the reason it is a test
/// and not a comment: the first cut put the check beside `report_contested_query_names`
/// — ahead of the mode split — and so refused a browse too. The two refusals are about
/// different things. A CONTESTED NAME is a pattern the loader could not read, which is
/// a defect of the text wherever it is used. A SUPPLIER TIE is a defect of a DISPATCH,
/// and `--match` performs none: it reports which clause heads unify with the pattern
/// and evaluates no body, so there is no wrong answer for the refusal to prevent and
/// refusing would reject a legal question about a legal program.
///
/// Asserted as "not refused" rather than on a result count: what the browse finds is
/// `query_cmd_test`'s subject, and pinning it here would couple this test to it.
#[test]
fn a_two_supplier_browse_is_not_refused() {
    let out = browse("wi1044_browse.anthill", &program(RIVAL));
    assert_eq!(
        out.code, 0,
        "a structural browse dispatches nothing, so a supplier tie must not refuse it; \
         stdout:\n{}\nstderr:\n{}",
        out.stdout, out.stderr,
    );
    assert!(
        !out.has_diagnostic("error:", "ambiguous dispatch"),
        "…and must not report the dispatch refusal either; stderr:\n{}",
        out.stderr,
    );
}
