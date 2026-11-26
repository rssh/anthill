//! WI-20261126-JR3AD — an override's restated contract clause that holds a VARIABLE matches
//! the spec operation's: the two are compared up to ONE renaming of the operation's clause
//! variables (`kb/typing/contract_renaming.rs`).
//!
//! Before it, the contract legs of the override check compared each clause structurally after
//! aligning the parameters and the `result` binder, and nothing aligned a variable. A written
//! `?k` is one per name per operation and a filler is fresh per pattern, so an override's
//! clause held variables of its own and never matched: a spec operation whose `ensures` (or
//! `requires`) holds a variable had no possible provider (anthill-traces' WI-20261122-4067S:
//! 20 restated clauses refused across nine operations, every one holding a variable).
//!
//! Each row that loads also RUNS: `go()` calls the spec operation, which has no body, so the
//! `7` it answers is the override's — the provider that loaded is the one that answers.
//!
//! BACK-OUT, measured on a binary of this file alone, 21 rows (each change below made by
//! hand, the file run, the change undone):
//!
//!  * The renaming backed out — two variables correspond only when they are one, as
//!    `views_structurally_equal` has it: 14 RED. Every row that loads with a clause variable
//!    (`a_written_variable…`, `a_patterns_fillers…`, `two_clauses_sharing_a_variable_restated_
//!    sharing_one…`, `a_restatement_greedy…`, `a_variable_shared_by_requires_and_ensures_
//!    restated_sharing_one…`, `a_requires_clause_restated…`, `a_dropped_precondition_over_a_
//!    variable_of_its_own…`, `ten_clauses_restated_by_ten…`); the three joint refusals, the
//!    dropped-precondition refusal and the budget row, each refused as a weakened
//!    postcondition instead; and `a_result_type_mismatch…`, where no clause is discharged and
//!    nothing names the types. GREEN either way, BY DESIGN, the seven that pin what the
//!    renaming must not admit or never touches: `a_variable_restated_as_a_constant…`,
//!    `a_constant_restated_as_a_variable…`, `one_variable_restating_two_in_a_clause…`,
//!    `a_variable_the_signature_binds…`, `a_requires_variable_restated_as_a_constant…`,
//!    `ground_clauses_still_load`, and `an_ensures_over_a_parameter_types_variable…` (its
//!    variable is the signature's, compared by identity once aligned).
//!  * The signature's variables renamed too (`ClauseVariables` empty): RED is
//!    `a_variable_the_signature_binds_is_not_renamed` alone (it loads).
//!  * One-to-one backed out (an override variable may restate two of the spec operation's):
//!    RED are `one_variable_restating_two_in_a_clause…`, `…_across_clauses…` and the budget row
//!    (ten restated by nine then fits).
//!  * Each clause on a renaming of its own (the joint search answering `Found`): RED are the
//!    three joint refusals — `two_clauses_sharing_a_variable_restated_with_two…`,
//!    `a_variable_shared_by_requires_and_ensures_restated_with_two…`,
//!    `one_variable_restating_two_across_clauses…` — the dropped-precondition refusal and the
//!    budget row.
//!  * The search made greedy (each clause's first fitting counterpart kept, never revisited):
//!    RED are `a_restatement_greedy_matching_misses_loads` and the budget row (greedy fails
//!    the pigeonhole at once, within the bound).
//!  * `result_binder_discharges` comparing by identity again: RED is
//!    `a_result_type_mismatch_behind_a_variable_clause_is_named` alone.
//!  * A precondition's variable not held bound (`keeps_preconditions_variables` answering
//!    `true`): RED is `a_dropped_precondition_does_not_unbind_the_postconditions_variable`
//!    alone (it loads).
//!  * The `ensures` leg's type-parameter variables left unaligned, as before the review: RED is
//!    `an_ensures_over_a_parameter_types_variable_restated_loads` alone.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

const WEAKENED: &str = "it weakens the postcondition";
const STRENGTHENED: &str = "it strengthens the precondition";
const NO_ONE_RENAMING: &str = "only under different renamings of their variables";
const ABANDONED: &str = "was given up after 100000 attempts";
const UNBOUND: &str = "restates a variable the spec operation's `requires` binds";

/// The fixture: a spec `Spec` whose operation `f` carries `spec_clauses`, a provider `Impl`
/// whose own `f` carries `impl_clauses` and answers `7`, and `go()`, which calls `Spec.f`.
fn program(ns: &str, spec_clauses: &str, impl_clauses: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  entity Pt(x: Int64, y: Int64)
  rule holds(?a, ?b) :- true
  rule p(?a) :- true
  rule q(?a) :- true
  sort Spec
    sort T = ?
    operation f(s: T, n: Int64) -> Int64
{spec_clauses}
  end
  sort Impl
    entity mk
    provides Spec[T = Impl]
    operation f(s: Impl, n: Int64) -> Int64
{impl_clauses}
      = 7
  end
  operation go() -> Int64 = Spec.f(Impl.mk, 1)
end
"#
    )
}

/// The row loads, and `go()` runs the override.
fn loads_and_runs(ns: &str, spec_clauses: &str, impl_clauses: &str) {
    let src = program(ns, spec_clauses, impl_clauses);
    assert_eq!(
        run_int64(&src, &format!("{ns}.go")),
        Ok(7),
        "{ns}: the override restates the spec operation's contract, so it loads and answers"
    );
}

/// The row is refused, every refusal for `reason`, and as many as `count`.
fn refused_for(ns: &str, spec_clauses: &str, impl_clauses: &str, reason: &str, count: usize) {
    let errs = load_errors_of(&program(ns, spec_clauses, impl_clauses));
    assert_refused_naming(&errs, &["'jr3ad.", "overrides", reason], ns);
    assert_eq!(
        errs.iter().filter(|e| e.contains(reason)).count(),
        count,
        "{ns}: {count} refusal(s) for `{reason}`, got: {errs:?}"
    );
    assert_eq!(errs.len(), count, "{ns}: no other refusal, got: {errs:?}");
}

// ── (1) restatements that hold variables load ───────────────────────────

#[test]
fn a_written_variable_restated_loads() {
    // THE TICKET'S `named`: the override's `?k` is a variable of its own.
    loads_and_runs(
        "jr3ad.named",
        "      ensures holds(result, ?k)",
        "      ensures holds(result, ?k)",
    );
    // A different name for it is the same restatement.
    loads_and_runs(
        "jr3ad.named_other",
        "      ensures holds(result, ?k)",
        "      ensures holds(result, ?j)",
    );
}

#[test]
fn a_patterns_fillers_restated_load() {
    // THE TICKET'S `filled`: `Pt(x: n)` leaves `y` out, and the loader fills it with a
    // variable fresh per pattern — one on each side.
    loads_and_runs(
        "jr3ad.filled",
        "      ensures holds(n, Pt(x: n))",
        "      ensures holds(n, Pt(x: n))",
    );
}

#[test]
fn two_clauses_sharing_a_variable_restated_sharing_one_load() {
    // One clause of two goals, and two clauses — and restated in the other order.
    loads_and_runs(
        "jr3ad.shared_goals",
        "      ensures holds(result, ?k), holds(n, ?k)",
        "      ensures holds(result, ?j), holds(n, ?j)",
    );
    loads_and_runs(
        "jr3ad.shared_clauses",
        "      ensures holds(result, ?k)\n      ensures holds(n, ?k)",
        "      ensures holds(n, ?j)\n      ensures holds(result, ?j)",
    );
}

#[test]
fn a_restatement_greedy_matching_misses_loads() {
    // WHY THE SEARCH BACKTRACKS. Each spec clause fits two of the override's on its own, so
    // taking the clause with the fewest counterparts first decides nothing and they are
    // tried in order. `holds(n, ?a)` takes `a ↦ x`, `holds(n, ?b)` is left `b ↦ y`, and
    // `holds(?b, result)` then fits neither `holds(?x, result)` nor `holds(?z, result)`. The
    // restatement is `a ↦ y, b ↦ x` — the override promises `holds(?z, result)` besides,
    // which is no weakening.
    loads_and_runs(
        "jr3ad.greedy_miss",
        "      ensures holds(n, ?a)\n      ensures holds(n, ?b)\n      ensures holds(?b, result)",
        "      ensures holds(n, ?x)\n      ensures holds(n, ?y)\n      ensures holds(?x, result)\n      \
         ensures holds(?z, result)",
    );
}

#[test]
fn a_variable_shared_by_requires_and_ensures_restated_sharing_one_loads() {
    // A written `?k` is the operation's, so the renaming is ONE across both legs.
    loads_and_runs(
        "jr3ad.across_legs",
        "      requires holds(n, ?k)\n      ensures holds(result, ?k)",
        "      requires holds(n, ?j)\n      ensures holds(result, ?j)",
    );
}

#[test]
fn ground_clauses_still_load() {
    // The ticket's `ground`, which loaded before: a clause with no variable is settled
    // without the search.
    loads_and_runs(
        "jr3ad.ground",
        "      requires holds(n, 1)\n      ensures holds(result, n)",
        "      requires holds(n, 1)\n      ensures holds(result, n)",
    );
}

// ── (2) controls: what is not a restatement is still refused ────────────

#[test]
fn two_clauses_sharing_a_variable_restated_with_two_is_refused() {
    // `∃k. P(k) ∧ Q(k)` restated as `∃j. P(j) ∧ ∃i. Q(i)` says less. Each clause has its
    // counterpart on its own, so it is the joint refusal, once.
    refused_for(
        "jr3ad.split",
        "      ensures holds(result, ?k)\n      ensures holds(n, ?k)",
        "      ensures holds(result, ?j)\n      ensures holds(n, ?i)",
        NO_ONE_RENAMING,
        1,
    );
}

#[test]
fn a_variable_shared_by_requires_and_ensures_restated_with_two_is_refused() {
    refused_for(
        "jr3ad.across_legs_split",
        "      requires holds(n, ?k)\n      ensures holds(result, ?k)",
        "      requires holds(n, ?j)\n      ensures holds(result, ?i)",
        NO_ONE_RENAMING,
        1,
    );
}

#[test]
fn a_variable_restated_as_a_constant_is_refused() {
    refused_for(
        "jr3ad.var_as_const",
        "      ensures holds(result, ?k)",
        "      ensures holds(result, 3)",
        WEAKENED,
        1,
    );
}

#[test]
fn a_constant_restated_as_a_variable_is_refused() {
    refused_for(
        "jr3ad.const_as_var",
        "      ensures holds(result, 3)",
        "      ensures holds(result, ?k)",
        WEAKENED,
        1,
    );
}

#[test]
fn one_variable_restating_two_in_a_clause_is_refused() {
    // NOT ONE-TO-ONE, within one clause: `holds(?x, ?x)` would need `a ↦ x` and `b ↦ x`.
    // Logically stronger, and refused: the check is syntactic.
    refused_for(
        "jr3ad.collapse",
        "      ensures holds(?a, ?b)",
        "      ensures holds(?x, ?x)",
        WEAKENED,
        1,
    );
}

#[test]
fn one_variable_restating_two_across_clauses_is_refused() {
    // NOT ONE-TO-ONE, across two clauses that each fit on their own: the joint refusal.
    refused_for(
        "jr3ad.merge",
        "      ensures p(?a)\n      ensures q(?b)",
        "      ensures p(?x)\n      ensures q(?x)",
        NO_ONE_RENAMING,
        1,
    );
}

#[test]
fn a_variable_the_signature_binds_is_not_renamed() {
    // `?t` is the spec operation's type variable (written in `y`'s type), aligned with the
    // override's `?u`. The override's clause holds a variable `?w` the signature does not
    // bind: renaming it to `?t` would read a requirement over another type as the spec's.
    let errs = load_errors_of(
        r#"
namespace jr3ad.bound
  import anthill.prelude.{Int64}
  rule holds(?a, ?b) :- true
  sort Spec
    operation d(x: Int64, y: ?t) -> Int64
      requires holds(y, ?t)
  end
  sort Impl
    entity mk
    operation d(x: Int64, y: ?u) -> Int64
      requires holds(y, ?w)
      = x
    provides Spec
  end
end
"#,
    );
    assert_refused_naming(&errs, &["'jr3ad.bound.Impl' overrides", STRENGTHENED], "jr3ad.bound");
    assert_eq!(errs.len(), 1, "one refusal, got: {errs:?}");
}

#[test]
fn a_dropped_precondition_does_not_unbind_the_postconditions_variable() {
    // The spec operation promises `holds(result, k)` of the `k` its precondition names. The
    // override drops the precondition — a weaker one, which is allowed — and restates the
    // promise over a `?j` nothing binds: it promises `holds(result, j)` of SOME `j`. Every
    // clause reads as restated; the renaming `k ↦ j` is what is turned down.
    refused_for(
        "jr3ad.dropped_pre",
        "      requires holds(n, ?k)\n      ensures holds(result, ?k)",
        "      ensures holds(result, ?j)",
        UNBOUND,
        1,
    );
}

#[test]
fn a_dropped_precondition_over_a_variable_of_its_own_loads() {
    // CONTROLS for the row above. A precondition whose variable no `ensures` shares may be
    // dropped; so may one of two that bind the shared variable, while the other still does.
    loads_and_runs(
        "jr3ad.dropped_pre_unshared",
        "      requires holds(n, ?k)\n      ensures holds(result, ?m)",
        "      ensures holds(result, ?j)",
    );
    loads_and_runs(
        "jr3ad.dropped_one_of_two",
        "      requires holds(n, ?k)\n      requires holds(?k, n)\n      ensures holds(result, ?k)",
        "      requires holds(n, ?j)\n      ensures holds(result, ?j)",
    );
}

#[test]
fn an_ensures_over_a_parameter_types_variable_restated_loads() {
    // `?m` is the variable `b`'s type writes, paired with the override's `?q`: the `requires`
    // leg aligned it before this ticket and the `ensures` leg did not, so the same clause
    // loaded as a precondition and was refused as a postcondition (found by review).
    let ns = "jr3ad.tyvar";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  rule holds(?a, ?b) :- true
  sort Box
    sort T = ?
    entity box(v: T)
  end
  sort Spec
    sort T = ?
    operation f(s: T, b: Box[T = ?m]) -> Int64
      requires holds(s, ?m)
      ensures holds(result, ?m)
  end
  sort Impl
    entity mk
    provides Spec[T = Impl]
    operation f(s: Impl, b: Box[T = ?q]) -> Int64
      requires holds(s, ?q)
      ensures holds(result, ?q)
      = 7
  end
  operation go() -> Int64 = Spec.f(Impl.mk, Box.box(v: 1))
end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(7), "{ns}");
}

// ── (3) the `requires` leg reads the same way ───────────────────────────

#[test]
fn a_requires_clause_restated_with_a_variable_loads() {
    loads_and_runs(
        "jr3ad.requires",
        "      requires holds(n, ?k)",
        "      requires holds(n, ?j)",
    );
}

#[test]
fn a_requires_variable_restated_as_a_constant_is_refused() {
    refused_for(
        "jr3ad.requires_const",
        "      requires holds(n, ?k)",
        "      requires holds(n, 3)",
        STRENGTHENED,
        1,
    );
}

// ── the return-type question reads the renaming too ─────────────────────

#[test]
fn a_result_type_mismatch_behind_a_variable_clause_is_named() {
    // WI-20260822-59CDQ: aligning the `result` binders is a claim that the two return types
    // agree, refused naming both where the alignment is what discharges a clause. Here the
    // clause holds a variable; compared by identity, it matched under neither alignment and
    // nothing named the types.
    let errs = load_errors_of(
        r#"
namespace jr3ad.ret
  import anthill.prelude.{Int64, String}
  rule holds(?a, ?b) :- true
  sort Spec
    operation f(n: Int64) -> Int64
      ensures holds(result, ?k)
  end
  sort Impl
    entity mk
    operation f(n: Int64) -> String
      ensures holds(result, ?j)
      = "s"
    provides Spec
  end
end
"#,
    );
    assert_refused_naming(
        &errs,
        &["the contract clause it restates from the spec", "it returns `String`", "returns `Int64`"],
        "jr3ad.ret",
    );
}

// ── the search's bound ─────────────────────────────────────────────────

/// One side's `count` clauses `ensures holds(n, ?{prefix}i)`, each over a variable of its own.
fn same_shape_clauses(prefix: &str, count: usize) -> String {
    (1..=count)
        .map(|i| format!("      ensures holds(n, ?{prefix}{i})"))
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn ten_clauses_restated_by_ten_load() {
    // Every spec clause fits every override clause on its own; the search finds the
    // correspondence without branching back.
    loads_and_runs(
        "jr3ad.ten",
        &same_shape_clauses("a", 10),
        &same_shape_clauses("x", 10),
    );
}

#[test]
fn ten_clauses_restated_by_nine_run_out_of_the_budget() {
    // A pigeonhole: each of ten spec clauses fits each of nine override clauses on its own,
    // and no one-to-one renaming exists. The search tries every partial correspondence, well
    // past the bound, and the override is refused for running out — not passed. (Four
    // restated by three is ruled out within it: the joint refusal.)
    refused_for(
        "jr3ad.pigeonhole",
        &same_shape_clauses("a", 10),
        &same_shape_clauses("x", 9),
        ABANDONED,
        1,
    );
    refused_for(
        "jr3ad.pigeonhole_small",
        &same_shape_clauses("a", 4),
        &same_shape_clauses("x", 3),
        NO_ONE_RENAMING,
        1,
    );
}
