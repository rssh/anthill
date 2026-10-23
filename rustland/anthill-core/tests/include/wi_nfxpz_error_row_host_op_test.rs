//! WI-20260827-NFXPZ — a host operation whose effect row holds only `Error` runs in a rule
//! body, and its error propagates.
//!
//! A host function is opaque Rust: a state effect it declares it performs, so its row is the
//! only guard, and a rule body may run it only where each member of that row is `Error` —
//! bare, applied, or guarded (`Error[DivisionByZero] :- eq(b, 0)`). The error it RETURNS the
//! eval bridge reports as it reports a raise in a body: the call has no value, the answer
//! set is marked incomplete, and `not(…)` over it is undecided rather than true. The zero
//! divisor of the arithmetic builtins (`div`, `mod`) propagates the same way (user,
//! 2026-10-23), so the operations sharing that guarded row answer alike.
//!
//! Before, the row had to be EMPTY: `Int64.rem(7, 2)` was a conditional residual in a rule
//! body (its goal had no reading, and `Int64.rem(7, 2, ?r)` answered nothing), and
//! `Int64.div(7, 0)` answered a silent `no solutions` that `not(…)` read as a refutation.
//!
//! BACK-OUT, measured with each part switched off alone over the whole `wi_tests` binary:
//!  * the host row read as "empty only" (`host_op_runs_in_rule_body`): `rem_at_a_value_computes`,
//!    `rem_by_zero_propagates_its_error`, `a_raise_from_a_host_function_propagates`,
//!    `the_goal_view_reads_a_host_error_row`, and `wi_vpewk_host_op_operand_test`'s two `Error`
//!    rows fail;
//!  * the goal view alone kept at "empty only" for a host function
//!    (`effect_row_admits_relational_view`): `the_goal_view_reads_a_host_error_row`,
//!    `rem_by_zero_propagates_its_error` (its relation row) and `wi_vpewk`'s arity+1 row fail;
//!  * a guarded member no longer read as `Error` (`effect_member_is_error`): the three
//!    `rem` rows fail;
//!  * the builtin's zero divisor read as a silent `Failure` (the `Int64` slot):
//!    `div_by_zero_propagates_its_error`,
//!    `wi_k4jgc`'s and `wi_cynpe`'s zero-divisor rows, and the three CLI rows (`wi863`, `wi875`)
//!    fail.
//! `a_state_effect_beside_error_still_refuses` and `a_bodied_error_row_is_the_control` pass
//! under each of these by design. The row test on the dictionary-selected member
//! (`reduce_op_value`'s `needs_dict` arm) is driven by no row: a host-mapped member reached
//! through a woven call has no fixture here, and a plain call to a host member of a sort with
//! a `requires` does not take that arm (probed).

use crate::common::{load_kb_with, query_pattern_term};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

const SRC: &str = r#"
namespace nfxpz
  import anthill.prelude.{Int64, String, Clock, BigInt}
  sort Boom
    entity boom(why: String)
  end
  sort MyS
    operation trimClkErr(s: String) -> String
      effects {Clock, Error} @[host_implemented]
  end
  provides MyS language rust
    artifact "scratch"
    carrier { MyS: "String" }
    operation_map {
      trimClkErr: "string_trim"
    }
  end
  operation pick(x: Int64) -> Int64 effects {Error[Boom]} =
    if x > 0 then x else Error.raise(boom(why: "nonpositive"))

  rule rem(?x) :- ?x <=> Int64.rem(7, 2)
  rule remTested(1) :- Int64.rem(7, 2) = 1
  rule remWrong(1) :- Int64.rem(7, 2) = 2
  rule remRelation(?r) :- Int64.rem(7, 2, ?r)
  rule rem0(?x) :- ?x <=> Int64.rem(7, 0)
  rule rem0Relation(?r) :- Int64.rem(7, 0, ?r)
  rule rem0Not(1) :- not(Int64.rem(7, 0) = 3)
  rule div0(?x) :- ?x <=> Int64.div(7, 0)
  rule div0Relation(?r) :- Int64.div(7, 0, ?r)
  rule div0Not(1) :- not(Int64.div(7, 0) = 3)
  rule div0Guarded(?x) :- ?b <=> 0, ?b != 0, ?x <=> Int64.div(7, ?b)
  rule bigDiv(?x) :- ?x <=> BigInt.div(BigInt.to_bigint(7), BigInt.to_bigint(2))
  rule bigDiv0(?x) :- ?x <=> BigInt.div(BigInt.to_bigint(7), BigInt.to_bigint(0))
  rule bigMod0(?x) :- ?x <=> BigInt.mod(BigInt.to_bigint(7), BigInt.to_bigint(0))
  rule raised(?x) :- ?x <=> Error.raise(boom(why: "x"))
  rule clkErr(1) :- MyS.trimClkErr("  a  ") = "a"
  rule bodied(?x) :- ?x <=> pick(5)
  rule bodied0(?x) :- ?x <=> pick(0)
end
"#;

/// `nfxpz.<rel>(?r)`: each answer as (rendered, definite), and whether the answer set was
/// marked incomplete.
fn ask(kb: &mut KnowledgeBase, rel: &str) -> (Vec<(String, bool)>, bool) {
    let goal = query_pattern_term(kb, &format!("nfxpz.{rel}(?r)"));
    let (_, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    (crate::common::shown_rows(kb, &format!("nfxpz.{rel}")), stats.truncated)
}

/// One definite answer, rendered `want`, from a complete search.
fn definite(kb: &mut KnowledgeBase, rel: &str, want: &str) {
    assert_eq!(ask(kb, rel), (vec![(want.to_string(), true)], false), "{rel}");
}

/// The call raised: no definite answer, and the answer set is incomplete.
fn propagated(kb: &mut KnowledgeBase, rel: &str) {
    let (rows, truncated) = ask(kb, rel);
    assert!(rows.iter().all(|(_, d)| !d), "{rel}: no definite answer; got {rows:?}");
    assert!(truncated, "{rel}: the error marks the answer set incomplete; got {rows:?}");
}

/// `Int64.rem` has no builtin; its host function runs behind a GUARDED `Error` row, and
/// computes: at a value, at a comparison in both polarities, and at its result column.
#[test]
fn rem_at_a_value_computes() {
    let mut kb = load_kb_with(SRC);
    definite(&mut kb, "rem", "1");
    definite(&mut kb, "remTested", "1");
    assert_eq!(ask(&mut kb, "remWrong"), (vec![], false), "a wrong answer is decided false");
}

/// The goal view of a host function reads an `Error` row too: `rem(7, 2, ?r)` binds.
#[test]
fn the_goal_view_reads_a_host_error_row() {
    let mut kb = load_kb_with(SRC);
    definite(&mut kb, "remRelation", "1");
}

/// A zero divisor in the host function: the raise propagates at a value, at the goal, and
/// under `not(…)`, which is no refutation.
#[test]
fn rem_by_zero_propagates_its_error() {
    let mut kb = load_kb_with(SRC);
    for rel in ["rem0", "rem0Relation", "rem0Not"] {
        propagated(&mut kb, rel);
    }
}

/// The builtin's zero divisor answers as the host function's does. A rule that tests the
/// divisor first has a decided empty answer and no error.
#[test]
fn div_by_zero_propagates_its_error() {
    let mut kb = load_kb_with(SRC);
    for rel in ["div0", "div0Relation", "div0Not"] {
        propagated(&mut kb, rel);
    }
    assert_eq!(ask(&mut kb, "div0Guarded"), (vec![], false), "a tested divisor is no error");
}

/// The `BigInt` slot of the same builtin: a value, and a zero divisor's raise for `div` and
/// `mod`.
#[test]
fn a_bigint_zero_divisor_propagates_its_error() {
    let mut kb = load_kb_with(SRC);
    definite(&mut kb, "bigDiv", "3");
    for rel in ["bigDiv0", "bigMod0"] {
        propagated(&mut kb, rel);
    }
}

/// `Error.raise` is a host function whose row is `Error[T]`: run, and its raise propagates.
#[test]
fn a_raise_from_a_host_function_propagates() {
    let mut kb = load_kb_with(SRC);
    propagated(&mut kb, "raised");
}

/// CONTROL against this ticket's back-outs: a row with a state effect beside `Error` keeps
/// the host function from running — one conditional answer, the call left unreduced. (It
/// fails with the resolver's body-less arm made to take a host function, the 4DYR6 back-out.)
#[test]
fn a_state_effect_beside_error_still_refuses() {
    let mut kb = load_kb_with(SRC);
    let (rows, _) = ask(&mut kb, "clkErr");
    assert_eq!(rows, vec![("1".to_string(), false)], "clkErr");
}

/// CONTROL against this ticket's back-outs: the bodied twin, which the 2026-10-21 half
/// admitted — its value, and its raise propagating.
#[test]
fn a_bodied_error_row_is_the_control() {
    let mut kb = load_kb_with(SRC);
    definite(&mut kb, "bodied", "5");
    propagated(&mut kb, "bodied0");
}
