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

/// SELF-CARRIER implicit licensing: `getV[T](target: T) -> T.V` with NO `requires` —
/// self-licensed, the obligation forwarded. At a concrete call `getV(c)` it grounds `T.V`
/// to the carrier's OWN declared `sort V = Int64` (the resource-declares-its-value-type
/// tie), so a `-> Int64` body conforms.
#[test]
fn self_carrier_grounds_via_declared_member() {
    let snippet = r#"namespace test.wi383.sc
  import anthill.prelude.{Int64, String}
  sort CounterState
    sort V = Int64
    entity Counter(n: Int64)
  end
  operation getV[T](target: T) -> T.V
  operation useGood(c: CounterState) -> Int64 = getV(c)
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        errs.is_empty(),
        "self-carrier T.V should ground to the carrier's declared V (Int64); got: {errs:?}"
    );
}

/// SELF-CARRIER soundness: the declared-member grounding is real — `getV(c) : Int64`, so a
/// `-> String` body is REJECTED.
#[test]
fn self_carrier_rejects_wrong_type() {
    let snippet = r#"namespace test.wi383.scbad
  import anthill.prelude.{Int64, String}
  sort CounterState
    sort V = Int64
    entity Counter(n: Int64)
  end
  operation getV[T](target: T) -> T.V
  operation useBad(c: CounterState) -> String = getV(c)
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        errs.iter().any(|e| e.contains("String") || e.contains("Int64")),
        "self-carrier T.V grounds to Int64; a String body must be rejected; got: {errs:?}"
    );
}

/// SELF-CARRIER abstract member stays NEUTRAL (no spurious grounding): a carrier whose
/// `sort V = ?` is abstract leaves `T.V` un-ground, so forcing it to a concrete `-> Int64`
/// is REJECTED — the element type is genuinely unknown for that carrier.
#[test]
fn self_carrier_abstract_member_does_not_ground() {
    let snippet = r#"namespace test.wi383.scabs
  import anthill.prelude.Int64
  sort Opaque
    sort V = ?
    entity Mk(n: Int64)
  end
  operation getV[T](target: T) -> T.V
  operation useInt(c: Opaque) -> Int64 = getV(c)
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        !errs.is_empty(),
        "an abstract `sort V = ?` must NOT spuriously ground T.V to Int64; useInt should be rejected"
    );
}

/// SELF-CARRIER soundness (review): a carrier whose child sharing the member NAME is NOT
/// a declared `sort` member (here an ENTITY `Velem`) must NOT ground off an UNRELATED
/// sort's same-named member (`Other`'s `sort Velem = String`). The exact-alias lookup
/// reads only the carrier's own declared member, so `Carrier` (no `sort Velem`) leaves
/// `T.Velem` neutral and the `-> String` body is REJECTED.
#[test]
fn self_carrier_name_collision_does_not_ground() {
    let snippet = r#"namespace test.wi383.collide
  import anthill.prelude.{Int64, String}
  sort Other
    sort Velem = String
    entity Mk(n: Int64)
  end
  sort Carrier
    entity Velem(n: Int64)
  end
  operation getV[T](target: T) -> T.Velem
  operation useStr(c: Carrier) -> String = getV(c)
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        !errs.is_empty(),
        "T.Velem must not ground off Other's same-named member; Carrier has no `sort Velem`, so useStr should be rejected"
    );
}

/// PROVIDER-FACT BIND (WI-383 scope 3, the Modify driver): a spec op whose receiver is
/// typed by the spec's CARRIER type-param (`rd(target: T)`, like `ModifyRuntime.get`)
/// ties its independent value param `V` to the carrier's GROUND provider-fact binding
/// (`fact Box[T = IntCell, V = Int64]`). So `Box.rd(c)` on an `IntCell` is `Int64`, and a
/// `-> Int64` read conforms. (The REF shape `fact Box[T=Cell, V=V]` already worked via
/// WI-424; this closes the GROUND-valued case for entity resources.)
#[test]
#[ignore = "WI-383 B (provider-fact ground bind): needs a LATE pass (bind still-free ground value-params after per-call threading) — an early bind disrupts WI-424/441 Iterable threading (EffP). Root cause + fix direction in WI-383 feedback."]
fn provider_fact_ground_value_ties_spec_op() {
    let snippet = r#"namespace test.wi383.pf
  import anthill.prelude.{Int64, String}
  sort Box
    sort T = ?
    sort V = ?
    operation rd(target: T) -> V
  end
  sort IntCell
    operation rd(target: IntCell) -> Int64
    fact Box[T = IntCell, V = Int64]
  end
  operation readInt(c: IntCell) -> Int64 = Box.rd(c)
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        errs.is_empty(),
        "Box.rd(c) should tie V to the carrier's ground provider-fact V (Int64); got: {errs:?}"
    );
}

/// PROVIDER-FACT BIND soundness: the tie is real — `Box.rd(c) : Int64`, so a `-> String`
/// read is REJECTED (this is the exact value-untied soundness hole the Modify model named).
#[test]
#[ignore = "WI-383 B (provider-fact ground bind): the value-untied soundness hole — `Box.rd(c) : V` floats free, so a String read is wrongly accepted until the LATE-pass ground bind lands. Anchor."]
fn provider_fact_ground_value_rejects_wrong_type() {
    let snippet = r#"namespace test.wi383.pfbad
  import anthill.prelude.{Int64, String}
  sort Box
    sort T = ?
    sort V = ?
    operation rd(target: T) -> V
  end
  sort IntCell
    operation rd(target: IntCell) -> Int64
    fact Box[T = IntCell, V = Int64]
  end
  operation readStr(c: IntCell) -> String = Box.rd(c)
end
"#;
    let errs = load_errors(&[snippet]);
    assert!(
        errs.iter().any(|e| e.contains("String") || e.contains("Int64")),
        "Box.rd(c) ties V to Int64; a String read must be rejected; got: {errs:?}"
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
