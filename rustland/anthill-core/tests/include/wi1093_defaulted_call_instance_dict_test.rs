//! WI-1093 — A DEFAULTED SPEC-OP CALL DOES NOT THREAD THE INSTANCE DICTIONARY, so THE
//! ELEMENTS' DICTIONARIES ARE MISSING from the frame the implementation runs in.
//!
//! WHAT A PARENT BUNDLE CARRIES AND WHAT IT DOES NOT. `Ord.max` is a DEFAULTED spec op
//! and `Pair` declares no `max`, so the typer falls through the WI-1012 supplier arm and
//! classifies a Direct call, building the WI-415 parent bundle: `Dictionary(impl: Ord,
//! subs: [Eq[Pair], PartialOrd[Pair]])` — the SPEC's own `requires` chain resolved at the
//! carrier. What `Pair.compare` actually reads when it compares `al` against `bl` is
//! `Ord[A]` and `Ord[B]`, the conditions of `provides Ord[Pair] :- Ord[A], Ord[B]`. Those
//! live in the `Ord[Pair]` INSTANCE dictionary and in no parent bundle.
//!
//! TWO ARMS, ONE ROOT. A defaulted spec-op call with a statically pinned carrier has two
//! exits and NEITHER built the instance:
//!
//!   * **SUPPLIER PINNED** — `carrier_override_suppliers` answers one, and the arm called
//!     `classify_pin_or_apply_within(.., resolved_tree: None, ..)`. No tree, so no
//!     dispatch dict AT ALL: the implementation is entered with an EMPTY channel and its
//!     first condition-slot read dies `not bound`. **This ticket fixes that arm**;
//!     [`the_pinned_override_reads_its_provision_condition`] is its driver.
//!   * **NO SUPPLIER** — the default body runs and the Direct arm builds the WI-415
//!     parent bundle: right for the default body's OWN reads (`Sp requires Base[T]` at
//!     `T = Wrap` genuinely IS `Base[Wrap]`), wrong for the carrier's provision
//!     CONDITIONS, which the bundle does not carry at all. **NOT fixed here** — pinned as
//!     a failing expectation by
//!     [`pins_the_defaulted_fall_through_losing_the_elements_dictionary`], whose doc
//!     carries the two causes and the measurement showing a typer-only fix moves nothing.
//!
//! **THE MEASUREMENT THAT DECIDES WHETHER A NUMBER IS EVIDENCE.** An op WITH a receiver is
//! repaired by value-direction at every call: `spec_call_runtime_carrier` classifies the
//! carrier from the argument and `resolve_bridge_requirements` rebuilds the chain from the
//! runtime values, so the answer is right whatever the frame holds. A test that reads one
//! therefore measures the repair, not the dictionary — and an earlier draft of this file
//! did exactly that, went green on the fall-through arm, and recorded the false conclusion
//! "the eta hypothesis does not drive it". A RECEIVER-LESS spec op (`Sp.mark()`) has no
//! such route: with no argument to classify, value-direction answers `NoSupplier` and the
//! requirement dictionary is the only way to an answer. Every assertion below reads
//! through one, which is what makes 10-vs-20 name WHICH dictionary was threaded rather
//! than merely reporting that the program ran.
//!
//! WHY A LOCAL TOWER AND NOT `Ord`/`Pair`. No stdlib carrier with CONDITIONED provisions
//! overrides a DEFAULTED spec op, so the pinned arm has no library face: `Pair` overrides
//! only `compare` and `eq`, both body-LESS, which take the `lookup_spec_op_dispatch` route
//! that already resolves a tree. (And an eta cannot be written inside `Ord.max`, which is
//! what the second arm would need.) The tower below is the same shape with three sorts: a
//! spec that `requires` a sibling, a CONDITIONED carrier whose member reads its own
//! provision's condition slot through a receiver-less op, and a LEAF carrier that reads
//! nothing — the leaf being the control that shows what the accident was hiding.
//!
//! Reference: 058 §3.8 (per-provision conditions) and WI-869 (the slots one introduces);
//! WI-1012 (the supplier arm this fixes); WI-829 (`emit_tree_as_projection`, the tree the
//! body-less route already emits); WI-420 (`attach_eta_dispatch_dict`'s same-sort arm);
//! WI-822 LEG 2 (`requirements_for_value_directed_impl`'s non-empty short-circuit).

use anthill_core::eval::Value;

/// The tower. `Base` is a plain spec; `Sp` `requires Base[T]` — so its parent bundle is
/// non-empty and its slot name is `__req_base`.
///
/// `Wrap` is the CONDITIONED carrier. Its `rank` reads the condition of `provides
/// Sp[Wrap] :- Sp[E]` — the ELEMENT's dictionary, the local twin of `Pair.compare`'s
/// `Ord.compare(al, bl)`. It reads its OWN provision's condition and not a sibling's,
/// which matters: 058 §3.8 leaves a sibling provision's slot present-but-unfilled at a
/// dispatch that did not earn it, so a `Base.base(i)` here would refuse LEGITIMATELY and
/// the fixture would be measuring that rule instead of this defect. (Measured while
/// writing this file: with `rank` reading `Base[E]`, the fixed build answers
/// `UnpinnedRequirement` off a `__req_base` slot the `Sp[Wrap]` tree correctly left as
/// `NoProvider`.)
///
/// `Leaf` is the control carrier — its `rank` reads nothing, so an empty channel serves
/// it and it stays green on every route. Its `mark()` answers 10 against `Wrap`'s 20, and
/// that pair is the whole instrument: the number says which dictionary was read.
const TOWER: &str = r#"
namespace wi1093.tower
  import anthill.prelude.{Int64, Function}

  sort Base
    sort T = ?
    operation base(x: T) -> Int64
  end

  sort Sp
    sort T = ?
    requires Base[T]

    -- DEFAULTED rather than body-less, and that is forced, not a preference:
    -- `reduce_var` mints a `Value::OpRef` only for an op that HAS a body, so a bare
    -- reference to a body-less op in a function-typed slot becomes a zero-arg CALL and
    -- dies `OperationBodyMissing` before any dictionary is read. The default of `-1` is
    -- never an answer below — both carriers override it — so a `-1` would say the
    -- override was lost, which is a different defect and must stay distinguishable.
    operation rank(x: T) -> Int64 = -1

    -- RECEIVER-LESS, and it lives on `Sp` because it must: a carrier dispatched through
    -- the `Sp[Wrap]` provision may read THAT provision's condition and no sibling's
    -- (058 §3.8 leaves a sibling's slot present-but-unfilled, and reading one is a
    -- legitimate refusal — measured here as `UnpinnedRequirement` when this op briefly
    -- lived on its own spec). No parameter mentions T, so NO runtime value can direct
    -- the call: `spec_call_runtime_carrier` has no receiver argument to classify,
    -- value-direction answers `NoSupplier`, and the ONLY route to an answer is the
    -- requirement dictionary. That is what makes the number evidence ABOUT the
    -- dictionary instead of evidence that some route answered.
    operation mark() -> Int64

    -- The higher-order hop the eta'd `OpRef` escapes through.
    operation via(f: Function[A = T, B = Int64], x: T) -> Int64 = f(x)

    -- The DEFAULTED op with NO supplier at either carrier, so its own body runs. It
    -- eta-lifts the same-sort `rank`, and that eta is what carries this frame's
    -- `__req_self` out to a foreign apply frame.
    operation ranked(x: T) -> Int64 = via(rank, x)
  end

  enum Leaf
    entity leaf(n: Int64)
    provides Base[T = Leaf]
    provides Sp[T = Leaf]
    operation base(x: Leaf) -> Int64 = match x case leaf(n) -> n
    operation rank(x: Leaf) -> Int64 = match x case leaf(n) -> n
    -- THE ELEMENT'S ANSWER.
    operation mark() -> Int64 = 10
  end

  enum Wrap
    sort E = ?
    entity wrap(inner: E)
    provides Base[T = Wrap] :- Base[T = E]
    provides Sp[T = Wrap]   :- Sp[T = E]
    operation base(x: Wrap) -> Int64 = match x case wrap(i) -> Base.base(i)
    -- Reads the `Sp[Wrap]` provision's OWN CONDITION slot — the ELEMENT's dictionary.
    -- Its own provision's, not a sibling's: 058 §3.8 makes a slot belonging to a
    -- SIBLING provision present-but-unfilled at a dispatch that did not earn it, so
    -- `Base.base(i)` here would be a legitimate refusal and not this ticket's defect.
    -- This is exactly `Pair.compare`'s `Ord.compare(al, bl)`.
    --
    -- THE CARRIER'S RIVAL ANSWER, so 10-vs-20 names which dictionary was read.
    operation mark() -> Int64 = 20
    -- THE MEASUREMENT. `Sp.mark()` takes NO receiver, so no value can direct it and the
    -- answer can only come from the `Sp[E]` condition slot of this carrier's OWN
    -- provision — the ELEMENT's dictionary. 10 = the element's, 20 = this carrier's own
    -- (the wrong one), a raise = none at all.
    operation rank(x: Wrap) -> Int64 = Sp.mark()
  end

  sort Driver
    -- ARM 1: the defaulted `rank`, PINNED to `Wrap.rank` by the supplier arm.
    operation pinned_at_wrap(n: Int64) -> Int64 = Sp.rank(wrap(inner: leaf(7)))
    -- …and nested, so the condition slot has to be right at TWO levels.
    operation pinned_at_wrap2(n: Int64) -> Int64 =
      Sp.rank(wrap(inner: wrap(inner: leaf(7))))
    -- ARM 2: the defaulted `ranked`, no supplier, default body runs and etas `rank`.
    operation defaulted_at_wrap(n: Int64) -> Int64 = Sp.ranked(wrap(inner: leaf(7)))
    -- CONTROLS.
    operation pinned_at_leaf(n: Int64) -> Int64 = Sp.rank(leaf(7))
    operation defaulted_at_leaf(n: Int64) -> Int64 = Sp.ranked(leaf(7))
  end
end
"#;

fn eval_int(entry: &str, why: &str) -> i64 {
    let mut interp = crate::common::interp_for(TOWER);
    match interp.call(entry, &[Value::Int(0)]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{why}; got {other:?}"),
    }
}

/// **THE DRIVER — the one test in this file that fails when the fix is backed out.**
///
/// `Sp.rank` is defaulted and `Wrap` declares its own, so the WI-1012 supplier arm pins
/// `Wrap.rank` — and passed `resolved_tree: None`. No tree, no dispatch dict, EMPTY
/// channel, and `Wrap.rank`'s `Sp.mark()` has no `Sp[E]` to read.
///
/// **WHY THE NUMBER IS EVIDENCE, which an earlier draft of this file got wrong.** It read
/// `Sp.rank(i)` on the wrapped element — an op WITH a receiver, which value-direction can
/// resolve from the runtime value alone. Its answer therefore said only "some route
/// answered", never "the dictionary answered", and the discrimination came entirely from
/// the error on the back-out. `Sp.mark()` takes NO receiver: `spec_call_runtime_carrier`
/// has no argument to classify, so value-direction returns `NoSupplier` and the ONLY route
/// to an answer is the requirement dictionary. Both carriers implement it and they answer
/// DIFFERENTLY, so the number names which dictionary was threaded:
///
/// | answer | what it says |
/// |---|---|
/// | 10 | the ELEMENT's dictionary (`Sp[Leaf]`) — correct for one wrap |
/// | 20 | the CARRIER's own (`Sp[Wrap]`) — the wrong one for one wrap, right for two |
/// | -1 | the override was lost and `Sp`'s default body ran |
/// | raise | no dictionary at all — the pre-fix behaviour |
///
/// BACKED OUT (`resolved_tree` → `None` at the pin, nothing else): `Internal("var_ref(
/// __req_base) unbound in requirement position (running `wi1093.tower.Wrap.rank`; frame
/// binds [])")`.
#[test]
fn the_pinned_override_reads_its_provision_condition() {
    assert_eq!(
        eval_int(
            "wi1093.tower.Driver.pinned_at_wrap",
            "the pinned `Wrap.rank` must be entered with the `Sp[Wrap]` INSTANCE, so its \
             receiver-less `Sp.mark()` reads the ELEMENT's `Sp[Leaf]` and answers 10 \
             — a 20 is `Sp[Wrap]`, the carrier's own dictionary read in its place"
        ),
        10,
    );
    // NESTED, and it discriminates in the OTHER direction: here the element IS a `Wrap`,
    // so the same slot must answer 20. A fix that stubbed every condition slot with the
    // carrier's own dictionary would pass the row above and fail this one; one that
    // always reached the innermost leaf would pass this row's opposite and fail it here.
    assert_eq!(
        eval_int(
            "wi1093.tower.Driver.pinned_at_wrap2",
            "with a `Wrap` as the element, the element's dictionary is `Sp[Wrap]` = 20"
        ),
        20,
    );
}

/// CONTROL, GREEN EITHER WAY BY DESIGN — the LEAF carrier, whose `rank` reads no
/// dictionary at all. This is the shape whose accidental correctness hid the defect (a
/// leaf impl is self-contained, so an empty channel serves it), and keeping it green is
/// what says the fix did not start refusing defaulted calls wholesale.
#[test]
fn control_a_leaf_carrier_reads_nothing_and_is_unaffected() {
    assert_eq!(
        eval_int(
            "wi1093.tower.Driver.pinned_at_leaf",
            "pinned at a leaf carrier"
        ),
        7,
    );
    assert_eq!(
        eval_int(
            "wi1093.tower.Driver.defaulted_at_leaf",
            "defaulted at a leaf carrier"
        ),
        7,
    );
}

/// **PINS THE SECOND ARM'S DEFECT — this row asserts a FAILURE, on purpose.**
///
/// The FALL-THROUGH arm: no supplier, so `Sp`'s own default body runs and the Direct arm
/// builds the WI-415 PARENT BUNDLE. `Sp.ranked` eta-lifts its sibling `rank`, so
/// `attach_eta_dispatch_dict` captures `var_ref(__req_self)` and the `OpRef` carries that
/// bundle to a foreign apply frame, where the caller cannot re-resolve.
///
/// **WHY IT IS VISIBLE AT ALL, and why an earlier draft of this file wrongly concluded it
/// was not.** That draft had `Wrap.rank` read `Sp.rank(i)` — an op WITH a receiver — and
/// the row went GREEN, so it recorded "the eta hypothesis does not drive it". FALSE, and
/// the greenness was the repair, not the absence of a defect: value-direction re-resolves
/// a receiver-carrying call from the argument value and hands back the right answer no
/// matter what the frame holds. With the receiver-LESS `Sp.mark()` there is no such route
/// and the wrong frame is exactly what one sees.
///
/// TWO CAUSES, and NEITHER is fixed here — which is why this asserts the error:
///   1. the typer threads the parent bundle instead of the instance (this ticket's arm 2);
///   2. eval's value-directed redirect to `Wrap.rank` keeps the SPEC's half of the
///      channel, and `requirements_for_value_directed_impl` will not rebuild it because
///      `incoming` is non-empty (WI-822 LEG 2's deliberate short-circuit).
/// FIXING ONLY (1) CHANGES NOTHING HERE — measured: implemented, it fired on this fixture
/// AND on stdlib `Iterable.find`, and this row's message did not move. So arm 2 has no
/// driver of its own and both causes belong to WI-1091, whose increment (a) is the first
/// forward of `__req_self` and whose increment (b) is the eta's missing op half.
///
/// WHEN WI-1091 LANDS THIS ROW MUST FAIL, and its replacement is `10` — the element's
/// dictionary, exactly as [`the_pinned_override_reads_its_provision_condition`] asserts on
/// the arm that IS fixed. A pinned defect that silently starts passing is the failure mode
/// this shape exists to prevent.
#[test]
fn pins_the_defaulted_fall_through_losing_the_elements_dictionary() {
    let mut interp = crate::common::interp_for(TOWER);
    let err = interp
        .call("wi1093.tower.Driver.defaulted_at_wrap", &[Value::Int(0)])
        .expect_err(
            "WI-1091 not landed: the eta must still carry the PARENT BUNDLE out of the \
             default body, so `Wrap.rank` cannot find its `Sp[E]` condition slot",
        );
    let msg = err.to_string();
    assert!(
        msg.contains("__req_sp") && msg.contains("not bound"),
        "expected the unbound provision-condition slot; got: {msg}"
    );
    assert!(
        msg.contains("__req_self") && msg.contains("__req_base"),
        "…and the frame it DOES bind is the SPEC's half — the parent bundle, naming \
         `Sp`'s own `requires` chain and none of `Wrap`'s provision conditions. got: {msg}"
    );
}
