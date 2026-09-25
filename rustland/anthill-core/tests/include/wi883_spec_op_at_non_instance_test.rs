//! WI-883 (058 §3.9) — a call to a spec's OPERATION at a carrier that is not an INSTANCE of
//! that spec is refused at LOAD, naming the carrier and the spec.
//!
//! WI-1102 discharges a callee's DECLARED `requires` — the spec's own chain and the
//! operation's own clauses. Calling `Spec.op(x)` at `C` also asserts `Spec[T = C]` itself,
//! and nothing declares that, so no chain carried it. Before this ticket a carrier that
//! provided everything the spec REQUIRES but not the spec loaded clean and died at eval:
//!
//!   * a body-less op — `Desc.describe(pebble(…))`, `Pebble` providing no `Desc` —
//!     "operation has no body: Desc.describe";
//!   * a defaulted op — `max(p, q)` on a `P` providing `Eq` and `PartialOrd` but not
//!     `WeakOrd` — entered the default body and died the same way on `WeakOrd.compare`.
//!
//! `max(1.5, 2.75)` WAS refused, but only by accident: `WeakOrd` also `requires Eq[T]`,
//! which `Float` cannot meet, so the message named `Eq`. `eval_test::
//! m3_float_comparison_and_max` now pins the sentence naming `WeakOrd`.
//!
//! ── THE VERDICT: "NOT AN INSTANCE BY ANY ROUTE" ─────────────────────────────────
//!
//! A carrier is refused only when it has NO provision of the spec at all — own, witness,
//! derived, or transitive (`carrier_is_an_instance`). A failed resolution at the call's
//! bindings is NOT the verdict: measured, it also fires where the carrier IS an instance and
//! the call leaves something open (`isEmpty(nil)`, `wi818`), and every one of those loads
//! and answers. And only a spec with an ABSTRACT member owes an instance: a sort whose every
//! operation has a body is a parameterized module (`vec3`'s `SortHolder`, `wi1037`'s
//! defaulted `Desc`), and what its calls owe is its DECLARED `requires`, which WI-1102 checks.
//!
//! ── WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT ──────────────────────────────
//!
//! Backing out the BODY-LESS arm (the `NoCandidates` refusal in `check_apply_iter`) fails
//! `a_body_less_spec_op_at_a_carrier_that_provides_nothing_is_refused`, and outside this
//! file `wi1111…::the_direct_call_mask_is_not_this_tickets` and `wi1043`'s operation-body
//! twin, both of which pinned the old eval-time trap so this change would land on them.
//!
//! Backing out the DEFAULTED arm (`defaulted_call_at_non_instance`, both sites) fails
//! `a_defaulted_spec_op_at_a_carrier_meeting_every_requirement_is_refused` and
//! `eval_test::m3_float_comparison_and_max` (back to the `Eq` sentence).
//!
//! Backing out the RULE-BODY widening (`check_occ_spec_op_requirements` taking a defaulted
//! member of a spec with an abstract one) fails `a_defaulted_spec_op_in_a_rule_body_is_refused_too`;
//! backing out its carrier-naming sentence fails that row and
//! `a_body_less_spec_op_in_a_rule_body_is_diagnosed_once` (back to "abstract type parameter").
//!
//! Backing out the RESOLUTION half of the defaulted verdict (keeping only the
//! binding-blind instance test) fails `a_generic_witness_is_an_instance_at_every_carrier`;
//! backing out the rule-body pass's REFLEXIVE exemption fails
//! `a_sorts_own_member_on_its_own_value_is_not_asked_for_an_instance`. Both measured.
//!
//! Each EXEMPTION, backed out, fails its own row here: the SELF-REPRESENTING gate
//! (`a_self_representing_sorts_parameter_is_its_element_not_its_carrier`, and ~20 programs
//! over `List`'s own members in the first full run), the HOST exemption
//! (`a_host_implemented_callees_parameter_is_a_payload`, every `wi_9wvt7` row that raises,
//! the stdlib's own `raise(EmptyStream…)`), the ABSTRACT-MEMBER gate
//! (`a_parameterized_module_owes_no_instance`, `vec3`, `wi1037`), and the TRANSITIVE leg of
//! the instance test (the stdlib's `Iterable.find` at `List` — every fixture).
//!
//! PASS EITHER WAY BY DESIGN — the controls the refusal must not reach: the carrier's own
//! provision, a witness provision, an instance running the default body, a conditional
//! instance, and an abstract carrier forwarded through the caller's `requires`.

use anthill_core::eval::Value;

// ── helpers ─────────────────────────────────────────────────────────────────

fn refusal(src: &str, what: &str) -> String {
    match crate::common::try_load_kb_with(src) {
        Err(errs) => errs.join("\n"),
        Ok(_) => panic!("{what}: expected a LOAD refusal, but the program loaded clean"),
    }
}

/// The refusal names the CALL, the CARRIER, the SPEC it is not an instance of, and the
/// line that repairs it.
fn assert_names_carrier_and_spec(text: &str, callee: &str, carrier: &str, spec: &str) {
    assert!(
        text.contains(&format!("call to `{callee}`")),
        "the refusal must name the call (`{callee}`); got:\n{text}"
    );
    assert!(
        text.contains(&format!("`{carrier}` provides no `{spec}`")),
        "the refusal must name the carrier and the SPEC it is not an instance of \
         (`{carrier}` / `{spec}`); got:\n{text}"
    );
    assert!(
        text.contains(&format!("provides {spec}[T = {carrier}]")),
        "…and spell the repair as a line the author can paste; got:\n{text}"
    );
}

fn eval_int(src: &str, op: &str) -> i64 {
    let mut interp = crate::common::interp_for(src);
    match interp.call(op, &[Value::Int(0)]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{op}: expected an Int, got {other:?}"),
    }
}

/// A typeclass whose parameter IS its carrier — no operation receives `Desc` itself.
const DESC: &str = r#"
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Pebble
    entity pebble(n: Int64)
  end
"#;

/// `P` meets every requirement `WeakOrd` declares (`Eq`, `PartialOrd`) and is not one.
const P_NOT_WEAKORD: &str = r#"
  sort P
    entity p(n: Int64)
    provides Eq[T = P]
    provides PartialOrd[T = P]
  end
"#;

// ── the refusal ─────────────────────────────────────────────────────────────

#[test]
fn a_body_less_spec_op_at_a_carrier_that_provides_nothing_is_refused() {
    let src = format!(
        r#"
namespace test.wi883.bodyless
  import anthill.prelude.{{Int64}}
{DESC}
  operation g(u: Int64) -> Int64 = Desc.describe(pebble(n: 1))
end
"#
    );
    let text = refusal(&src, "`Desc.describe` at a `Pebble` that provides no `Desc`");
    assert_names_carrier_and_spec(
        &text,
        "test.wi883.bodyless.Desc.describe",
        "test.wi883.bodyless.Pebble",
        "test.wi883.bodyless.Desc",
    );
}

#[test]
fn a_defaulted_spec_op_at_a_carrier_meeting_every_requirement_is_refused() {
    let src = format!(
        r#"
namespace test.wi883.defaulted
  import anthill.prelude.{{Int64, Eq, PartialOrd}}
  import anthill.prelude.Ord.{{max}}
{P_NOT_WEAKORD}
  operation g(u: Int64) -> Int64 = max(p(n: 3), p(n: 5)).n
end
"#
    );
    let text = refusal(&src, "`max` at a `P` that is not a `WeakOrd`");
    assert_names_carrier_and_spec(
        &text,
        "anthill.prelude.WeakOrd.max",
        "test.wi883.defaulted.P",
        "anthill.prelude.WeakOrd",
    );
}

/// A RULE body's spec-op calls are `check_rule_body_requirements`' — the pass that holds
/// the clause's declared `requires(…)` — so the sentence is its own, naming the carrier
/// and offering the clause-level repair beside the provision.
fn assert_rule_body_refusal(text: &str, callee: &str, carrier: &str, spec: &str) {
    assert!(text.contains(callee), "the refusal must name `{callee}`; got:\n{text}");
    assert!(
        text.contains(&format!("`{carrier}` provides no `{spec}`")),
        "the refusal must name the carrier and the spec; got:\n{text}"
    );
    let short = spec.rsplit('.').next().unwrap();
    assert!(
        text.contains(&format!("requires({short}[…])")),
        "…and the clause's own repair; got:\n{text}"
    );
}

/// The same call from a RULE body. It reaches eval through the SLD bridge, which gave it
/// no way out either: `WeakOrd.compare` has nothing to run at `P`. Before WI-883 the
/// rule-body pass took body-less members only, so this loaded clean.
#[test]
fn a_defaulted_spec_op_in_a_rule_body_is_refused_too() {
    let src = format!(
        r#"
namespace test.wi883.rule
  import anthill.prelude.{{Int64, Eq, PartialOrd}}
  import anthill.prelude.Ord.{{max}}
{P_NOT_WEAKORD}
  rule biggest(?m) :- ?m = max(p(n: 1), p(n: 2))
end
"#
    );
    let text = refusal(&src, "a rule-body `max` at a `P` that is not a `WeakOrd`");
    assert_rule_body_refusal(
        &text,
        "anthill.prelude.WeakOrd.max",
        "test.wi883.rule.P",
        "anthill.prelude.WeakOrd",
    );
}

/// ONE diagnosis, not two: the typer's operation-body refusal stays out of a rule body,
/// whose pass already reports the call. And the sentence names the GROUND carrier — the
/// pass used to say "covering abstract type parameter … on enclosing sort".
#[test]
fn a_body_less_spec_op_in_a_rule_body_is_diagnosed_once() {
    let src = format!(
        r#"
namespace test.wi883.ruleonce
  import anthill.prelude.{{Int64}}
{DESC}
  rule described(?d) :- ?d = Desc.describe(pebble(n: 1))
end
"#
    );
    let errs = crate::common::try_load_kb_with(&src)
        .err()
        .expect("a rule-body `Desc.describe` at a `Pebble` that provides no `Desc`");
    assert_eq!(errs.len(), 1, "one call, one diagnosis; got:\n{}", errs.join("\n"));
    assert_rule_body_refusal(
        &errs[0],
        "test.wi883.ruleonce.Desc.describe",
        "test.wi883.ruleonce.Pebble",
        "test.wi883.ruleonce.Desc",
    );
}

// ── what the refusal must not reach ─────────────────────────────────────────

/// `Bag`'s operations receive a `Bag`, so its `T` is the ELEMENT: `Bag.make(6)` says
/// nothing about whether `Int64` is a `Bag`. Reading the goal `Bag[T = Int64]` as a
/// carrier is WI-1076's defect, one site over.
#[test]
fn a_self_representing_sorts_parameter_is_its_element_not_its_carrier() {
    let src = r#"
namespace test.wi883.bag
  import anthill.prelude.{Int64}
  sort Bag
    sort T = ?
    entity bag(x: T)
    operation first(b: Bag) -> T = match b case bag(x) -> x
    operation make(x: T) -> Bag = bag(x: x)
  end
  operation g(u: Int64) -> Int64 = Bag.first(Bag.make(6))
end
"#;
    assert_eq!(eval_int(src, "test.wi883.bag.g"), 6);
}

/// `Error.raise` has an `operation_map` entry of its own, so the host runs it at every
/// payload — `Boom` is what is raised, not a carrier that must be an `Error`.
#[test]
fn a_host_implemented_callees_parameter_is_a_payload() {
    let src = r#"
namespace test.wi883.raise
  import anthill.prelude.{Int64, String, Error}
  import anthill.prelude.Result.{ok, err}
  sort Boom
    entity boom(why: String)
  end
  operation mayFail(n: Int64) -> Int64 effects {Error[Boom]} =
    if n < 0 then Error.raise(boom(why: "negative")) else n + 1
  operation g(u: Int64) -> Int64 =
    match Error.reify(lambda () -> mayFail(0 - 1))
      case ok(v)  -> v
      case err(_) -> 7
end
"#;
    assert_eq!(eval_int(src, "test.wi883.raise.g"), 7);
}

/// A GENERIC witness — `AnyMon` provides `Mon[T = E]` for every `E` — is an instance at
/// `Int64` though no row names `Int64`. The binding-blind half of the verdict cannot see
/// it; the call's own resolution does, which is why the defaulted arm needs both halves
/// (found by /code-review). Backing the resolution half out refuses this program.
#[test]
fn a_generic_witness_is_an_instance_at_every_carrier() {
    let src = r#"
namespace test.wi883.anymon
  import anthill.prelude.{Int64}
  sort Mon
    sort T = ?
    operation unit(x: T) -> Int64
    operation twice(x: T) -> Int64 = unit(x) + unit(x)
  end
  sort AnyMon
    sort E = ?
    provides Mon[T = E]
    operation unit(x: E) -> Int64 = 21
  end
  operation g(u: Int64) -> Int64 = Mon.twice(5)
end
"#;
    assert_eq!(eval_int(src, "test.wi883.anymon.g"), 42);
}

/// A sort's OWN member called on its own value is not an instance question: a `Box` is a
/// `Box`. The rule-body pass reads the self-receiver as the carrier, and `sort_provides(Box,
/// Box)` is false, so without its reflexive exemption this RULE is refused "`Box` provides
/// no `Box` — … `provides Box[T = Box]`", a repair that is not one (measured). The program
/// is broken for a different reason — `get` has no implementation — which is not this
/// check's to report. The operation-body spelling never reaches the question.
#[test]
fn a_sorts_own_member_on_its_own_value_is_not_asked_for_an_instance() {
    let src = r#"
namespace test.wi883.refl
  import anthill.prelude.{Int64}
  sort Box
    sort T = ?
    entity box(v: T)
    operation get(b: Box) -> Int64
    operation twice(b: Box) -> Int64 = get(b) + get(b)
  end
  rule twiced(?x) :- ?x = Box.twice(Box.box(1))
end
"#;
    crate::common::load_kb_with(src);
}

/// `SortHolder`'s shape (`vec3_ops_test`): every member has a body, so the sort is a
/// PARAMETERIZED MODULE. `Holder.cmp(7, 3)` owes `Ord[Int64]` — its declared `requires`,
/// which WI-1102 discharges — and nothing asks whether `Int64` is a `Holder`.
#[test]
fn a_parameterized_module_owes_no_instance() {
    let src = r#"
namespace test.wi883.module
  import anthill.prelude.{Int64, Ord, WeakOrd}
  sort Holder
    sort T = ?
    requires Ord[T]
    operation cmp(a: T, b: T) -> Int64 = WeakOrd.compare(a, b)
  end
  operation g(u: Int64) -> Int64 = Holder.cmp(7, 3)
end
"#;
    assert_eq!(eval_int(src, "test.wi883.module.g"), 1);
}

/// `Sq` is a `Shape` only where its element is a `Tag`, and the caller REQUIRES that. `Sq`
/// HAS a `Shape` row, so it is an instance to this check whatever the condition does; the
/// row pins that a conditional instance reached through the caller's `requires` still runs.
#[test]
fn a_conditional_instance_whose_condition_the_caller_requires_is_an_instance() {
    let src = r#"
namespace test.wi883.cond
  import anthill.prelude.{Int64}
  sort Tag
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort Shape
    sort T = ?
    operation area(s: Shape) -> Int64
    operation twice(s: Shape) -> Int64 = area(s) + area(s)
  end
  sort Sq
    sort E = ?
    entity sq(v: E)
    provides Shape[T = E] :- Tag[T = E]
    operation area(s: Sq) -> Int64 = 4
  end
  sort Pebble
    entity pebble(n: Int64)
    provides Tag[T = Pebble]
    operation tag(x: Pebble) -> Int64 = 1
  end
  operation f[X](s: Sq[E = X]) -> Int64 requires Tag[T = X] = Shape.twice(s)
  operation g(u: Int64) -> Int64 = f(sq(v: pebble(n: 1)))
end
"#;
    assert_eq!(eval_int(src, "test.wi883.cond.g"), 8);
}

#[test]
fn control_the_carriers_own_provision_loads_and_answers() {
    let src = r#"
namespace test.wi883.own
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Pebble
    entity pebble(n: Int64)
    provides Desc[T = Pebble]
    operation describe(x: Pebble) -> Int64 = 7
  end
  operation g(u: Int64) -> Int64 = Desc.describe(pebble(n: 1))
end
"#;
    assert_eq!(eval_int(src, "test.wi883.own.g"), 7);
}

#[test]
fn control_a_witness_provision_loads_and_answers() {
    let src = format!(
        r#"
namespace test.wi883.witness
  import anthill.prelude.{{Int64}}
{DESC}
  sort PebbleDesc
    provides Desc[T = Pebble]
    operation describe(x: Pebble) -> Int64 = 9
  end
  operation g(u: Int64) -> Int64 = Desc.describe(pebble(n: 1))
end
"#
    );
    assert_eq!(eval_int(&src, "test.wi883.witness.g"), 9);
}

#[test]
fn control_an_instance_runs_the_default_body() {
    let src = r#"
namespace test.wi883.inst
  import anthill.prelude.{Int64, Eq, PartialOrd, WeakOrd}
  import anthill.prelude.Ord.{max}
  import anthill.prelude.Numeric.{sub}
  sort P
    entity p(n: Int64)
    provides Eq[T = P]
    provides PartialOrd[T = P]
    provides WeakOrd[T = P]
    operation compare(a: P, b: P) -> Int64 = sub(a.n, b.n)
  end
  operation g(u: Int64) -> Int64 = max(p(n: 3), p(n: 5)).n
end
"#;
    assert_eq!(eval_int(src, "test.wi883.inst.g"), 5);
}

/// An abstract carrier names nothing — the caller's `requires` is what the call forwards.
#[test]
fn control_an_abstract_carrier_is_left_to_the_callers_requires() {
    let src = r#"
namespace test.wi883.generic
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Pebble
    entity pebble(n: Int64)
    provides Desc[T = Pebble]
    operation describe(x: Pebble) -> Int64 = 7
  end
  operation render[X](x: X) -> Int64 requires Desc[T = X] = Desc.describe(x)
  operation g(u: Int64) -> Int64 = render(pebble(n: 1))
end
"#;
    assert_eq!(eval_int(src, "test.wi883.generic.g"), 7);
}
