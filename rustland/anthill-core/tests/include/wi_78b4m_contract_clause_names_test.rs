//! WI-20261126-78B4M — a name in a contract clause denotes what it names in the operation's
//! scope, in both spellings:
//!
//!  * a QUALIFIED name of a const, an entity constructor or a sort in a clause's data slot is
//!    the term its one-segment spelling is (`Loader::contract_clause_qualified_reference`):
//!    `Spec.lim` written in a provider's `requires` is the reference the spec's own
//!    `requires n < lim` holds. It stayed the converter's `field_access(Spec, lim)` chain, and
//!    override refinement, comparing clauses structurally, matched it with no clause holding
//!    the reference — so a provider restating a spec's clause that names the spec's const was
//!    refused as strengthening the precondition (MEASURED, the ticket's probe through
//!    anthill-traces' binary, and again here);
//!  * a BARE name in a clause's data slot that resolves to nothing is refused
//!    (`LoadError::UnresolvedContractName`). It was kept as a symbolic constant, so the
//!    provider's bare `lim` — which reaches no const there, nothing declares it in the
//!    provider — loaded as another thing, and so did `requires n < nosuch` on any operation.
//!    The user's decision (2026-11-26): refused at load, as the operation's body refuses it.
//!
//! Each row that loads also RUNS: `go()` calls the spec operation, which has no body, so the
//! `7` it answers is the override's.
//!
//! BACK-OUT, measured on a binary of this file alone, 14 rows (each change made by hand, the
//! file run, the change undone):
//!
//!  * The qualified rung backed out (`contract_clause_qualified_reference` answering `None`):
//!    6 RED — `a_const_restated_qualified_loads`, `the_tickets_probe_loads_and_runs`,
//!    `an_ensures_naming_a_const_restated_qualified_loads`,
//!    `a_constructor_restated_qualified_loads`, `a_sort_restated_qualified_loads`, each
//!    refused as a strengthened precondition or a weakened postcondition, and
//!    `a_precondition_naming_a_const_is_discharged_across_spellings`, refused at the call,
//!    the caller's `m < lim` not discharging `n < A.lim`. GREEN either way, BY DESIGN, the
//!    controls the rung must not admit — `another_const_does_not_restate_the_const`,
//!    `a_literal_does_not_restate_the_const` — and the rows of the other half.
//!  * The refusal backed out (`refuse_unresolved_contract_name` reporting nothing): RED are
//!    `the_bare_name_in_the_provider_is_refused` and `a_bare_name_naming_nothing_is_refused_
//!    on_any_operation` (it loads). GREEN either way, BY DESIGN, the rows pinning what it
//!    must not judge: `a_goal_naming_nothing_is_refused_once`, `a_name_its_resolution_
//!    refuses_is_refused_once`, `a_lambdas_binder_is_not_refused` and
//!    `a_name_in_a_quoted_field_is_not_refused`.
//!  * The refusal made whatever resolving the name reported: RED is `a_name_its_resolution_
//!    refuses_is_refused_once` alone — `Self` is reported twice (found by `/code-review`).
//!  * Every slot of a clause read as data (`contract_slot` left `Data` for the goal): RED is
//!    `a_goal_naming_nothing_is_refused_once` alone — the goal is reported twice, by the goal
//!    check and by this one.
//!  * A binder's name not exempt: RED is `a_lambdas_binder_is_not_refused` alone.
//!  * A quoted field's name not exempt: RED is `a_name_in_a_quoted_field_is_not_refused` alone.

use anthill_core::eval::{HostValue, Value};

use crate::common::{assert_refused_naming, interp_for, load_errors_of, run_int64};

const STRENGTHENED: &str = "it strengthens the precondition";
const WEAKENED: &str = "it weakens the postcondition";
const NAMES_NOTHING: &str = "which resolves to nothing in the operation's scope";

/// The fixture: a spec `Spec` holding the consts `lim` and `other`, whose operation `f`
/// carries `spec_clauses`; a provider `Impl` whose own `f` carries `impl_clauses` and answers
/// `7`; and `go()`, which calls `Spec.f`. `below` and `kind` hold of anything, so a call's
/// precondition over them is proved whatever the const is.
fn program(ns: &str, spec_clauses: &str, impl_clauses: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  rule below(?a, ?b) :- true
  rule kind(?a, ?b) :- true
  sort Colour
    entity red
    entity blue
  end
  sort Spec
    import {ns}.Colour.{{red}}
    sort T = ?
    const lim: Int64 = 5
    const other: Int64 = 5
    operation f(s: T, n: Int64) -> Colour
{spec_clauses}
  end
  sort Impl
    entity mk
    provides Spec[T = Impl]
    operation f(s: Impl, n: Int64) -> Colour
{impl_clauses}
      = Colour.red
  end
  operation go() -> Int64 = if Spec.f(Impl.mk, 1) === Colour.red then 7 else 0
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

/// The row is refused, every refusal naming `tokens`, `count` in all.
fn refused_for(ns: &str, spec_clauses: &str, impl_clauses: &str, tokens: &[&str], count: usize) {
    let errs = load_errors_of(&program(ns, spec_clauses, impl_clauses));
    assert_refused_naming(&errs, tokens, ns);
    assert_eq!(errs.len(), count, "{ns}: {count} refusal(s), got: {errs:?}");
}

// ── (1) a qualified name is the reference its one-segment spelling is ───────

#[test]
fn a_const_restated_qualified_loads() {
    // THE TICKET'S `qualified`, over a predicate a call proves whatever the const is.
    loads_and_runs(
        "b4m.qconst",
        "      requires below(n, lim)",
        "      requires below(n, Spec.lim)",
    );
}

#[test]
fn the_tickets_probe_loads_and_runs() {
    // THE TICKET'S PROBE, `<` and all. No call proves `1 < lim` (a precondition over a const
    // is not evaluated), so the host vouches for `go`'s, which is written over `Spec.lim` —
    // and `go`'s own clause, the spec's and the provider's are one term, so `go` discharges
    // the call it makes.
    let src = r#"
namespace b4m.probe
  import anthill.prelude.{Int64}
  sort Spec
    sort T = ?
    const lim: Int64 = 5
    operation qualified(s: T, n: Int64) -> Int64
      requires n < lim
  end
  sort Impl
    entity mk
    provides Spec[T = Impl]
    operation qualified(s: Impl, n: Int64) -> Int64
      requires n < Spec.lim
      = n + 6
  end
  operation go(m: Int64) -> Int64
    requires m < Spec.lim
    = Spec.qualified(Impl.mk, m)
end
"#;
    let mut interp = interp_for(src);
    let answer = interp
        .call_assuming_requires("b4m.probe.go", &[HostValue::from(Value::Int(1))])
        .map(|h| h.value)
        .unwrap_or_else(|e| panic!("`go(1)` must run the override; got {e:?}"));
    assert!(matches!(answer, Value::Int(7)), "`go(1)` answers the override's `n + 6`, got {answer:?}");
}

#[test]
fn an_ensures_naming_a_const_restated_qualified_loads() {
    // THE `ensures` LEG: the same reading.
    loads_and_runs(
        "b4m.qpost",
        "      ensures below(n, lim)",
        "      ensures below(n, Spec.lim)",
    );
}

#[test]
fn a_constructor_restated_qualified_loads() {
    // `red` is imported into `Spec`; the provider names it `Colour.red`.
    loads_and_runs(
        "b4m.qctor",
        "      ensures kind(result, red)",
        "      ensures kind(result, Colour.red)",
    );
}

#[test]
fn a_sort_restated_qualified_loads() {
    loads_and_runs(
        "b4m.qsort",
        "      ensures kind(result, Colour)",
        "      ensures kind(result, b4m.qsort.Colour)",
    );
}

// ── (2) controls: what the reading must not admit ─────────────────────────

#[test]
fn another_const_does_not_restate_the_const() {
    // `other` holds the same value, and is another name: the clauses differ.
    refused_for(
        "b4m.other",
        "      requires below(n, lim)",
        "      requires below(n, Spec.other)",
        &["'b4m.other.Impl' overrides", STRENGTHENED],
        1,
    );
    refused_for(
        "b4m.other_post",
        "      ensures below(n, lim)",
        "      ensures below(n, Spec.other)",
        &["'b4m.other_post.Impl' overrides", WEAKENED],
        1,
    );
}

#[test]
fn a_literal_does_not_restate_the_const() {
    // The const's value written in its place is not the const: a contract clause keeps
    // every const the symbol it is.
    refused_for(
        "b4m.literal",
        "      requires below(n, lim)",
        "      requires below(n, 5)",
        &["'b4m.literal.Impl' overrides", STRENGTHENED],
        1,
    );
}

// ── (3) a bare name that resolves to nothing is refused ───────────────────

#[test]
fn the_bare_name_in_the_provider_is_refused() {
    // THE TICKET'S `unqualified`. `lim` is `Spec`'s, and the provider's scope does not reach
    // it — its body refuses it too. Refused where it is written, and the override, whose
    // clause then restates nothing of the spec's, is refused as well.
    let errs = load_errors_of(&program(
        "b4m.bare",
        "      requires below(n, lim)",
        "      requires below(n, lim)",
    ));
    assert_refused_naming(
        &errs,
        &[
            "the `requires` clause of operation `b4m.bare.Impl.f` names `lim`",
            NAMES_NOTHING,
            "`Sort.lim`",
        ],
        "b4m.bare",
    );
    let at_name = errs
        .iter()
        .find(|e| e.contains(NAMES_NOTHING))
        .expect("the refusal of the name");
    // Line 22 of the fixture (its first line is empty), the name at column 25: where it is
    // written, not the operation's declaration.
    assert!(at_name.starts_with("22:25:"), "located at the name, got: {at_name}");
    assert_eq!(errs.len(), 2, "the name, and the override it leaves unrefined: {errs:?}");
    assert!(errs.iter().any(|e| e.contains(STRENGTHENED)), "{errs:?}");
}

#[test]
fn a_bare_name_naming_nothing_is_refused_on_any_operation() {
    // No spec stands over `h`: the name was a symbolic constant, and the clause a condition
    // no value meets. Both clause lists.
    let errs = load_errors_of(
        r#"
namespace b4m.any
  import anthill.prelude.{Int64}
  rule below(?a, ?b) :- true
  sort A
    entity mk
    operation h(n: Int64) -> Int64
      requires below(n, nosuch)
      ensures below(result, nosuch_either)
      = n
  end
end
"#,
    );
    assert_refused_naming(
        &errs,
        &[
            "the `requires` clause of operation `b4m.any.A.h` names `nosuch`",
            "the `ensures` clause of operation `b4m.any.A.h` names `nosuch_either`",
        ],
        "b4m.any",
    );
    assert_eq!(errs.len(), 2, "one per name: {errs:?}");
}

// ── (4) what the refusal does not judge ───────────────────────────────────

#[test]
fn a_goal_naming_nothing_is_refused_once() {
    // A goal is a proposition, and the goal check refuses one that names nothing — at the
    // clause itself and inside a `not`. Not reported a second time as a name.
    for (ns, clause) in [("b4m.goal", "nosuch_goal"), ("b4m.goal_not", "!nosuch_goal")] {
        let errs = load_errors_of(&format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort A
    entity mk
    operation h(n: Int64) -> Int64
      requires {clause}
      = n
  end
end
"#
        ));
        assert_refused_naming(&errs, &["names `nosuch_goal`", "declared nowhere"], ns);
        assert_eq!(errs.len(), 1, "{ns}: refused once, by the goal check: {errs:?}");
    }
}

#[test]
fn a_name_its_resolution_refuses_is_refused_once() {
    // `Self` written as a value: resolving it already says why it means nothing there.
    let errs = load_errors_of(
        r#"
namespace b4m.self_once
  import anthill.prelude.{Int64}
  rule kind(?a, ?b) :- true
  sort Spec
    operation f(x: Self) -> Int64
      requires kind(x, Self)
  end
end
"#,
    );
    assert_refused_naming(&errs, &["`Self` is a type"], "b4m.self_once");
    assert_eq!(errs.len(), 1, "refused once, by the `Self` reading: {errs:?}");
}

#[test]
fn a_lambdas_binder_is_not_refused() {
    // `y` is the lambda's, at the binder and at the use: a binding, not a name that resolves
    // to nothing.
    let src = r#"
namespace b4m.lam
  import anthill.prelude.{Int64}
  rule known(?x, ?f) :- true
  sort A
    entity mk
    operation h(x: Int64) -> Int64
      requires known(x, lambda (y: Int64) -> y + x)
      ensures known(result, lambda (z: Int64) -> z)
      = x + 6
  end
  operation go() -> Int64 = A.h(1)
end
"#;
    assert_eq!(run_int64(src, "b4m.lam.go"), Ok(7));
}

#[test]
fn a_name_in_a_quoted_field_is_not_refused() {
    // A field declared `Term` holds a quoted term, whose names denote nothing by design.
    let src = r#"
namespace b4m.quoted
  import anthill.prelude.{Int64}
  import anthill.reflect.{Term}
  entity Pattern(t: Term)
  rule holds(?x, ?p) :- true
  sort A
    entity mk
    operation h(x: Int64) -> Int64
      requires holds(x, Pattern(t: some_symbol))
      = x + 6
  end
  operation go() -> Int64 = A.h(1)
end
"#;
    assert_eq!(run_int64(src, "b4m.quoted.go"), Ok(7));
}

#[test]
fn a_precondition_naming_a_const_is_discharged_across_spellings() {
    // `g` names the const qualified, its caller bare in the const's own sort: one term, so
    // the caller's precondition discharges the call's.
    let src = r#"
namespace b4m.discharge
  import anthill.prelude.{Int64}
  sort A
    const lim: Int64 = 5
    operation callg(m: Int64) -> Int64
      requires m < lim
      = B.g(m)
  end
  sort B
    entity mk
    operation g(n: Int64) -> Int64
      requires n < A.lim
      = n + 6
  end
end
"#;
    let mut interp = interp_for(src);
    let answer = interp
        .call_assuming_requires("b4m.discharge.A.callg", &[HostValue::from(Value::Int(1))])
        .map(|h| h.value)
        .unwrap_or_else(|e| panic!("`callg(1)` must run; got {e:?}"));
    assert!(matches!(answer, Value::Int(7)), "`callg(1)` answers `g`'s `n + 6`, got {answer:?}");
}
