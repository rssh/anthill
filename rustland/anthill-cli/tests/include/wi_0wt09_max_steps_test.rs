//! WI-20261115-0WT09 — `anthill query --max-steps`: the search's FUEL, beside `--max-depth`,
//! which now counts NESTING. A search that runs out of fuel stops, and its note names the
//! limit that cut it, so a missing answer reads as UNDECIDED and points at the flag that
//! would let it finish.
//!
//! BACK-OUT, measured 2026-11-16: the note's fuel arm removed — `a_search_out_of_fuel_says_so` prints the depth
//! note for a search no depth limit cut; the flag's refusal removed —
//! `max_steps_under_match_is_refused` loads and answers. `a_search_cut_by_depth_says_so`
//! is the CONTROL, unchanged by both.

use crate::common::{anthill, write_temp};

const SRC: &str = r#"
namespace probe.wi0wt09
  sort N
    entity z
    entity s(p: N)
  end
  fact tree(z)
  rule tree(s(p: ?n)) :- tree(?n), tree(?n)
  rule loopy :- loopy
end
"#;

/// `s(p: s(p: … z))`, `n` deep.
fn nat(n: usize) -> String {
    (0..n).fold("z".to_string(), |inner, _| format!("s(p: {inner})"))
}

/// A doubling search 17 levels deep, far under the default depth, takes some hundred
/// thousand steps: with `--max-steps 5000` it stops, and the note says the fuel cut it. The
/// `-i` brings `z` and `s` into the query's scope: unresolved, they name no clause head, and
/// the search ends complete with no solutions (measured on the first cut of this row).
#[test]
fn a_search_out_of_fuel_says_so() {
    let path = write_temp("wi_0wt09_fuel.anthill", SRC);
    let pattern = format!("tree({})", nat(16));
    let out = anthill(&[
        "query",
        "--max-steps",
        "5000",
        "-i",
        "probe.wi0wt09.*",
        "-p",
        path.to_str().unwrap(),
        &pattern,
    ]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert!(
        out.stdout
            .contains("note: search stopped at --max-steps; a missing answer is UNDECIDED, not refuted"),
        "the note names the fuel; got stdout:\n{}",
        out.stdout
    );
}

/// CONTROL: a left recursion is cut by depth, and the note still names `--max-depth`.
#[test]
fn a_search_cut_by_depth_says_so() {
    let path = write_temp("wi_0wt09_depth.anthill", SRC);
    let out = anthill(&["query", "-p", path.to_str().unwrap(), "probe.wi0wt09.loopy"]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert!(
        out.stdout
            .contains("note: search truncated at --max-depth; a missing answer is UNDECIDED, not refuted"),
        "the note names the depth limit; got stdout:\n{}",
        out.stdout
    );
}

/// `--max-steps` budgets RESOLUTION, as `--max-depth` does: under `--match` it is refused,
/// not silently ignored.
#[test]
fn max_steps_under_match_is_refused() {
    let path = write_temp("wi_0wt09_match.anthill", SRC);
    let out = anthill(&[
        "query",
        "--match",
        "--max-steps",
        "10",
        "-p",
        path.to_str().unwrap(),
        "probe.wi0wt09.loopy",
    ]);
    assert_eq!(out.code, 1, "--max-steps under --match must be refused; stdout:\n{}", out.stdout);
    assert!(
        out.stderr.contains("--max-steps applies only to resolution"),
        "the refusal names the flag; got stderr:\n{}",
        out.stderr
    );
}
