//! WI-20261121-G8E02 — the proof of a goal on the command line is an ordinary query of
//! `anthill.reflect.SLDProof.of` (proposal 075 §4; kernel-language §8.3, "The proof of a goal"):
//! no flag of its own. Before, `good(1)` printed `no solutions` and nothing said why.
//!
//! BACKED OUT with the relation unbound (`SORT_SCOPED_BUILTIN_RELATIONS` emptied): both rows
//! fail — the query has no answer.

use crate::common::{anthill, write_temp};

const SRC: &str = "namespace t\n  import anthill.prelude.{Int64}\n  rule pos(?x) :- ?x > 0\n  \
rule big(?x) :- ?x > 5\n  rule good(?x) :- pos(?x), big(?x)\nend\n";

#[test]
fn a_query_prints_why_a_goal_fails() {
    let path = write_temp("g8e02_refute.anthill", SRC);
    let out = anthill(&[
        "query",
        "--path",
        path.to_str().unwrap(),
        "-i",
        "t.*",
        "-i",
        "anthill.reflect.SLDProof",
        "SLDProof.of(!good(1), ?p)",
    ]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert!(
        out.stdout.contains("?p = refuted(goal: good(1), steps: [Step(clause: some(value: good-")
            && out.stdout.contains("failing: big(1)")
            && out.stdout.contains("builtin_false(goal: quoted(term: gt(1, 5)))"),
        "the proof of !good(1) names big(1) and 1 > 5; stdout:\n{}",
        out.stdout
    );
}

#[test]
fn a_query_prints_how_a_goal_holds() {
    let path = write_temp("g8e02_prove.anthill", SRC);
    let out = anthill(&[
        "query",
        "--path",
        path.to_str().unwrap(),
        "-i",
        "t.*",
        "-i",
        "anthill.reflect.SLDProof",
        "SLDProof.of(good(6), ?p)",
    ]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert!(
        out.stdout.contains("?p = by_clause(goal: good(6), clause: some(value: good-")
            && out.stdout.contains("by_builtin(goal: quoted(term: gt(6, 5)))"),
        "the proof of good(6) runs down to the builtins; stdout:\n{}",
        out.stdout
    );
}
