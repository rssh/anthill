//! WI-20261015-ZPETZ — a host call (`Interpreter::call`, `call_with_requirements`, and the
//! resolver's bridge, which a rule body's call reaches the evaluator through) is dispatched
//! by the dispatch an operation body's call takes, so the two cannot answer differently.
//!
//! Before, the host entry (`invoke_op_with_requirements`) kept a list of routes of its own —
//! a body, a supplier found from the value (WI-1057's copy), `PartialEq.eq` by the values, the
//! `Error.reify` boundary (`invoke_reify_boundary`) — and missed the rest. Measured on
//! 15e39605 over the programs below, a host call and the same call in an operation body:
//!
//! - `Desc.describe(leaf())`, `describe` written in `Desc` as `= 5` and `Leaf` writing its own
//!   `= 1`: 5 from the host, the spec's body run for a carrier with its own member; 1 in a body;
//! - `Desc.describe(wrap(leaf()))` there: 5 from the host, 12 in a body;
//! - `Own.eq(ow(v: 1), ow(v: 1))`, `Own` providing `Eq` with `eq = false`: `false` from the
//!   host, entered on identical operands; `true` in a body, by `Eq`'s law (kernel-language §8.3).
//!
//! Now (1) the host entry pushes one frame for the call and hands it to
//! `dispatch_resolved_operation`, whose answer is the run's first step (`run_from`), and its
//! copies are gone. (2) A redirected member's frame is built from the values where the
//! channel the call brought is headed by a stand-in for the spec's own frame rather than an
//! instance (`requirements_for_value_directed_impl`): the host entry seeds one
//! (`seed_entry_requirements`), and passed on, a conditional member read none of its own —
//! `Desc.describe(wrap(leaf()))` over a body-less `describe` died `__req_desc not bound` in
//! `WrapDesc.describe`, where HEAD's WI-1057 copy, discarding the channel, answered 12.
//!
//! ## Back-out
//!
//! - (1), the tree before (15e39605, the same programs):
//!   `a_host_call_of_a_spec_body_reaches_the_carriers_own_member` answers 5 and 5, and
//!   `a_host_call_of_a_lawful_eq_is_equal_by_the_law` `false`;
//!   `a_host_call_of_a_body_less_spec_operation_reaches_a_conditional_member` passes there, by
//!   the WI-1057 copy (1) deletes;
//! - (2) alone (the stand-in read as a caller's channel): the body-less row dies
//!   `__req_desc not bound` at `wrap(leaf())`, and the spec-body row at its `Wrap`; the law row
//!   passes. No other row of `wi_tests` fails (9,220 passed, 0 failed).
//!
//! Measured 2026-11-12, (1) on the tree before and (2) by a temporary switch.
//!
//! Both `Desc` rows ask `Interpreter::call` and `call_with_requirements` (with the empty chain
//! `Desc` has): each seeds the stand-in (2) reads.
//!
//! The `Error.reify` route a rule body's call reaches through the bridge is
//! `wi_9wvt7_reify_rule_body_test`'s, now through the dispatch's own boundary step.
//!
//! PASS EITHER WAY, BY DESIGN: each row's operation-body twin, the answer the host call is held
//! to; and the member called straight from the host with no dictionary, refused on both trees.

use anthill_core::eval::value::Value;

/// `common::DESC_INSTANCES` (a body-less `Desc.describe`, `Leaf` answering 1, `WrapDesc`
/// conditioned on its element's `Desc` answering `10 * inner + 2`), and makers for the values.
fn desc_program(ns: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.{{Int64}}
{}
  operation viaBody(x: Wrap[A = Leaf]) -> Int64 = Desc.describe(x)
  operation viaBody2(x: Wrap[A = Wrap[A = Leaf]]) -> Int64 = Desc.describe(x)
  operation mk() -> Wrap[A = Leaf] = wrap(inner: leaf())
  operation mk2() -> Wrap[A = Wrap[A = Leaf]] = wrap(inner: wrap(inner: leaf()))
end
"#,
        crate::common::DESC_INSTANCES
    )
}

/// A host call of the body-less `Desc.describe` on a `Wrap` reaches `WrapDesc.describe`, whose
/// frame holds the element's `Desc` built from the value: 12 and 122, what the call in an
/// operation body answers. Fails with (2) backed out: `__req_desc not bound`.
#[test]
fn a_host_call_of_a_body_less_spec_operation_reaches_a_conditional_member() {
    let ns = "zpetz.bodyless";
    let mut interp = crate::common::interp_for(&desc_program(ns));
    for (mk, body, want) in [("mk", "viaBody", 12), ("mk2", "viaBody2", 122)] {
        let w = interp.call(&format!("{ns}.{mk}"), &[]).expect("the value is made");
        let host = interp.call(&format!("{ns}.Desc.describe"), &[w.clone()]);
        let passed = interp.call_with_requirements(&format!("{ns}.Desc.describe"), &[w.clone()], Default::default());
        let in_body = interp.call(&format!("{ns}.{body}"), &[w]);
        assert!(matches!(host, Ok(Value::Int(n)) if n == want), "host call at `{mk}`: {host:?}");
        assert!(matches!(passed, Ok(Value::Int(n)) if n == want), "`call_with_requirements` at `{mk}`: {passed:?}");
        assert!(matches!(in_body, Ok(Value::Int(n)) if n == want), "body at `{mk}`: {in_body:?}");
    }
    // The member called straight from the host: the host has no spelling for the element's
    // instance, and the entry builds its own `requires` at the argument's value, as the
    // resolver's bridge builds a rule's call's — the host's value step, until a host call
    // passes what its callee reads or is refused (proposal 073 §6.1, WI-20261105-CBRD2). It
    // was handed nothing and raised `UnpinnedRequirement` while a call in a body still chose
    // from values.
    let w = interp.call(&format!("{ns}.mk"), &[]).expect("the value is made");
    let member = interp.call(&format!("{ns}.WrapDesc.describe"), &[w]);
    assert!(matches!(member, Ok(Value::Int(12))), "the member at the value: {member:?}");
}

/// `Desc.describe` with a body in `Desc` (`= 5`): a host call reaches the member the carrier
/// writes — `Leaf`'s 1, `WrapDesc`'s 12 over its element's — as the call in an operation body
/// does. Fails on the tree before (1): 5 and 5, the spec's body run for both; and with (2)
/// backed out: `__req_desc not bound` at the `Wrap`.
#[test]
fn a_host_call_of_a_spec_body_reaches_the_carriers_own_member() {
    let src = r#"namespace zpetz.body
  import anthill.prelude.{Int64}
  import anthill.prelude.Additive.{add}
  import anthill.prelude.Multiplicative.{mul}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 5
  end
  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 1
  end
  sort Wrap
    sort A = ?
    entity wrap(inner: A)
  end
  sort WrapDesc
    sort E = ?
    requires Desc[T = E]
    provides Desc[T = Wrap[A = E]]
    operation describe(w: Wrap[A = E]) -> Int64 =
      add(mul(10, Desc.describe(w.inner)), 2)
  end
  operation mkLeaf() -> Leaf = leaf()
  operation mkWrap() -> Wrap[A = Leaf] = wrap(inner: leaf())
  operation leafBody(x: Leaf) -> Int64 = Desc.describe(x)
  operation wrapBody(x: Wrap[A = Leaf]) -> Int64 = Desc.describe(x)
end
"#;
    let mut interp = crate::common::interp_for(src);
    for (mk, body, want) in [("mkLeaf", "leafBody", 1), ("mkWrap", "wrapBody", 12)] {
        let v = interp.call(&format!("zpetz.body.{mk}"), &[]).expect("the value is made");
        let host = interp.call("zpetz.body.Desc.describe", &[v.clone()]);
        let passed = interp.call_with_requirements("zpetz.body.Desc.describe", &[v.clone()], Default::default());
        let in_body = interp.call(&format!("zpetz.body.{body}"), &[v]);
        assert!(matches!(host, Ok(Value::Int(n)) if n == want), "host call at `{mk}`: {host:?}");
        assert!(matches!(passed, Ok(Value::Int(n)) if n == want), "`call_with_requirements` at `{mk}`: {passed:?}");
        assert!(matches!(in_body, Ok(Value::Int(n)) if n == want), "body at `{mk}`: {in_body:?}");
    }
}

/// `Own` provides `Eq` and writes `eq = false`: on identical operands its `eq` is not entered,
/// `Eq`'s law answers `true` (kernel-language §8.3), from the host as in an operation body. A
/// pair apart still asks the member. Fails on the tree before (1): the host call entered the
/// member and answered `false`.
#[test]
fn a_host_call_of_a_lawful_eq_is_equal_by_the_law() {
    let src = r#"namespace zpetz.refl
  import anthill.prelude.{Int64, Bool, PartialEq, Eq}
  sort Own
    import anthill.prelude.{Int64, Bool, PartialEq, Eq}
    entity ow(v: Int64)
    provides PartialEq[Own]
    provides Eq[Own]
    operation eq(x: Own, y: Own) -> Bool = false
  end
  operation one() -> Own = ow(v: 1)
  operation two() -> Own = ow(v: 2)
  operation viaBody(a: Own, b: Own) -> Bool = PartialEq.eq(a, b)
end
"#;
    let mut interp = crate::common::interp_for(src);
    let one = interp.call("zpetz.refl.one", &[]).expect("one");
    let two = interp.call("zpetz.refl.two", &[]).expect("two");
    for (a, b, want) in [(&one, &one, true), (&one, &two, false)] {
        let host = interp.call("zpetz.refl.Own.eq", &[a.clone(), b.clone()]);
        let in_body = interp.call("zpetz.refl.viaBody", &[a.clone(), b.clone()]);
        assert!(matches!(host, Ok(Value::Bool(x)) if x == want), "host call: {host:?}");
        assert!(matches!(in_body, Ok(Value::Bool(x)) if x == want), "body: {in_body:?}");
    }
}
