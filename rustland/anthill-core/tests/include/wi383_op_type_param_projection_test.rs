//! WI-383: sort-carried projection `T.V` off an OPERATION type-parameter.
//!
//! The type-receiver projection machinery (`RigidTypeProjection`, WI-428) licensed a
//! projection `P.Key` off a SORT type-param via the sort's `requires` chain
//! (`SortRequiresInfo`). An OPERATION type-param (`getV[T](target: T) -> T.V`) is lent
//! its members by the operation's OWN `requires Spec[C = T]` clause, stored on
//! `OperationInfo.requires` — a different store. WI-383 (fill mechanism, piece 2) makes
//! the formation consult that:
//!
//!   - the classifier accepts an OPERATION parent for a type-param head (`getV.T`), so
//!     `decl_sort` is the operation;
//!   - `resolve_rigid_projection` reads `OperationInfo.requires` (`op_requires_entries`)
//!     for an operation `decl_sort`, instead of the (empty) sort-level chain.
//!
//! This file's passing test pins FORMATION (the projection forms as a rigid neutral and
//! the operation loads clean). The `#[ignore]`'d anchor pins the next increment:
//! CALL-TIME concrete-fill grounding (`getV(c) : Int64` when `c`'s sort provides the
//! spec with `V = Int64`).

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn load_errors(extras: &[&str]) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    for ex in extras {
        parsed.push(parse::parse(ex).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// The shared spec + carrier: `Resource` declares a carrier `C` plus a value member `V`;
/// `CounterState` provides it with `V = Int64`.
const RESOURCE: &str = r#"
  sort Resource
    sort C = ?
    sort V = ?
    operation peek(c: C) -> C
  end

  sort CounterState
    provides Resource[C = CounterState, V = Int64]
    entity Counter(n: Int64)
    operation peek(c: CounterState) -> CounterState = c
  end
"#;

fn with_resource(ns: &str, rest: &str) -> String {
    format!(
        "namespace test.wi383.{ns}\n  import anthill.prelude.{{String, Int64}}\n{RESOURCE}\n{rest}\nend\n"
    )
}

/// FORMATION: `getV[T](target: T) -> T.V requires Resource[C = T]` loads clean — the
/// op-type-param projection `T.V` is licensed by the operation's own `requires` clause
/// (`Resource` declares `V`, and the bound mentions `T`), so it forms as a rigid neutral
/// rather than the pre-WI-383 "no requires bound on getV.T mentioning T declares V".
#[test]
fn op_type_param_projection_forms_via_op_requires() {
    let errs = load_errors(&[&with_resource(
        "forms",
        "  operation getV[T](target: T) -> T.V requires Resource[C = T]",
    )]);
    assert!(
        errs.is_empty(),
        "op-type-param projection should form via the op's requires; got: {errs:?}"
    );
}

/// FORMATION still LOUD when no bound declares the member: `T.W` (Resource has no `W`)
/// must remain a hard error — the op-requires path widens WHICH bounds are consulted,
/// never WHICH members are licensed.
#[test]
fn op_type_param_projection_undeclared_member_is_loud() {
    let errs = load_errors(&[&with_resource(
        "undeclared",
        "  operation getW[T](target: T) -> T.W requires Resource[C = T]",
    )]);
    assert!(
        errs.iter().any(|e| e.contains("W")),
        "projecting an undeclared member must stay loud; got: {errs:?}"
    );
}

/// A MULTI-GOAL requires clause (`requires Resource[C = T], Other[C = T]`) lowers to a
/// `conjunction(...)` term; the formation must FLATTEN it so each spec-shaped conjunct
/// still lends its members. Regression guard for the silent-drop the conjunction functor
/// would otherwise cause (loud-error-over-silent-skip).
#[test]
fn op_type_param_projection_via_multi_goal_requires() {
    let errs = load_errors(&[&with_resource(
        "multigoal",
        "  sort Other\n    sort C = ?\n    operation ping(c: C) -> C\n  end\n\
         \x20 operation getV[T](target: T) -> T.V requires Resource[C = T], Other[C = T]",
    )]);
    assert!(
        errs.is_empty(),
        "a multi-goal requires clause should still license T.V via the Resource conjunct; got: {errs:?}"
    );
}

/// CALL-TIME GROUNDING (concrete fill ⟹ CHECK against `provides`): `getV(c)` with
/// `c : CounterState` grounds `T.V` to `Int64` (CounterState `provides Resource[C =
/// CounterState, V = Int64]`), so a `-> Int64` body conforms.
#[test]
fn op_type_param_projection_grounds_at_concrete_call() {
    let errs = load_errors(&[&with_resource(
        "grounds",
        "  operation getV[T](target: T) -> T.V requires Resource[C = T]\n\
         \x20 operation useGood(c: CounterState) -> Int64 = getV(c)",
    )]);
    assert!(
        errs.is_empty(),
        "getV(c) should ground T.V to Int64 via CounterState's provides; got: {errs:?}"
    );
}

/// SOUNDNESS (review Q2 — licensing-spec-precise, NOT `provides`-order-dependent): a
/// carrier provides BOTH the licensing `Resource[V = Int64]` AND an unrelated
/// `Other[V = String]`, with `Other` declared FIRST. `getV` is licensed by
/// `requires Resource`, so `T.V` must ground to `Int64` (Resource's V) regardless of
/// provides order — never `String` off the first-matching `Other`.
#[test]
fn op_type_param_projection_grounds_via_licensing_spec_not_provides_order() {
    let snippet = r#"namespace test.wi383.q2
  import anthill.prelude.{String, Int64}
  sort Resource
    sort C = ?
    sort V = ?
    operation peek(c: C) -> C
  end
  sort Other
    sort C = ?
    sort V = ?
    operation ping(c: C) -> C
  end
  sort Dual
    provides Other[C = Dual, V = String]
    provides Resource[C = Dual, V = Int64]
    entity Mk(n: Int64)
    operation peek(c: Dual) -> Dual = c
    operation ping(c: Dual) -> Dual = c
  end
  operation getV[T](target: T) -> T.V requires Resource[C = T]
  operation useDual(c: Dual) -> Int64 = getV(c)
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        errs.is_empty(),
        "T.V must ground to the LICENSING Resource's V (Int64), not the first-declared Other's V; got: {errs:?}"
    );
}

/// SOUNDNESS (review Q3 — the carrier must actually PROVIDE the licensing spec): a carrier
/// provides only an unrelated `Foo[V = String]`, NOT the licensing `Resource`. `getV(c)`
/// must NOT ground `T.V` off `Foo` — the projection stays the opaque neutral (the unmet
/// `requires Resource` is not silently satisfied), so a `-> String` body is REJECTED.
#[test]
fn op_type_param_projection_unlicensed_carrier_does_not_ground() {
    let snippet = r#"namespace test.wi383.q3
  import anthill.prelude.{String, Int64}
  sort Resource
    sort C = ?
    sort V = ?
    operation peek(c: C) -> C
  end
  sort Foo
    sort C = ?
    sort V = ?
    operation ping(c: C) -> C
  end
  sort OnlyFoo
    provides Foo[C = OnlyFoo, V = String]
    entity Mk(n: Int64)
    operation ping(c: OnlyFoo) -> OnlyFoo = c
  end
  operation getV[T](target: T) -> T.V requires Resource[C = T]
  operation useStr(c: OnlyFoo) -> String = getV(c)
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        !errs.is_empty(),
        "T.V must NOT ground off the unlicensed Foo spec; useStr should be rejected, but loaded clean"
    );
}

/// SOUNDNESS of grounding: the wrong member type is REJECTED — `getV(c) : Int64`, so a
/// declared `-> String` body must fail (grounding is real, not a permissive wildcard).
#[test]
fn op_type_param_projection_grounding_rejects_wrong_type() {
    let errs = load_errors(&[&with_resource(
        "grounds_bad",
        "  operation getV[T](target: T) -> T.V requires Resource[C = T]\n\
         \x20 operation useBad(c: CounterState) -> String = getV(c)",
    )]);
    assert!(
        errs.iter().any(|e| e.contains("String") || e.contains("Int64")),
        "a String return must be rejected (T.V grounds to Int64); got: {errs:?}"
    );
}
