## Attributes

- id: WI-20260923-WN9P8-forward-soundness-of-a
- created: 2026-09-23T08:45:54Z

- status: Open
- status_agent: user
- status_at: 2026-09-23T08:45:54Z

- acceptance: cargo-test

## Description

FORWARD SOUNDNESS OF A QUANTIFIED SLOT BINDER: a named slot bound to a parameter the
signature DECLARED is forwarded, and the forward is answered by the slot's spec-keyed GOAL,
so ANY same-spec entry of the frame answers it, including one unrelated to the binder. The
binder does not appear in the goal at all. Silent wrong answer on the type channel,
measured; the written channels avoid it only with a gate that also refuses a correct shape.

FOUND by WI-20260911-TX0G6 (its delivery note, finding 2). An inline fix was attempted
there and reverted; see WHY NOT BELOW.

TWO SHAPES MUST BE TOLD APART, both measured at the TX0G6 delivery commit:
  * TIED (sound). The frame entry that answers is tied to the binder. Either it is a named
    slot whose binder it is, `sort R { requires OE: WeakOrd[E] }` with
    `s: SortedSet[T = E, O = OE]`. Or it is a requirement whose bindings mention it:
    `sort PolyD { sort OE = ?; requires PersistentCollection[C = SortedSet[T = E, O = OE],
    Element = E] }`, answered by Strategy 2b's provider-half projection. That one runs at
    both orderings (`wi456_no_scope_route_test::a_parent_instance_requirement_projects_
    the_comparator`).
  * UNTIED (wrong answer). `sort R3 { sort E = ?; sort P = ?; requires OE: WeakOrd[E];
    operation add(s: SortedSet[T = E, O = P], x: E) -> SortedSet[T = E, O = P] =
    SortedSet.insert(s, x) }`. At `R3.add[E = String, P = ByLength, OE = RevLen]`, a set
    typed `O = ByLength` is inserted into in RevLen's order (`bbb,cc,a,` where ByLength
    says `a,cc,bbb,`). It loads clean. The same happens through
    `PersistentCollection.insert(s, x)` (the `carried_slot` route). The frame's `OE` slot
    answers a goal that `P` was supposed to decide.

WHERE: `infer_named_slot_bindings`' `Quantified` arm (`param_rigids` membership = "declared
here") and `carried_slot`'s twin of it. The goal is then resolved `FromScope` by spec.

WHY NOT "IS THE BINDER A SLOT" — built inline at TX0G6 as a rigid-provenance set read by
both arms. It closes UNTIED and breaks TIED's 2b shape: 4 rows of
`wi456_no_scope_route_test` fail, `a_parent_instance_requirement_projects_the_comparator`
and three rows about refusal wording. Reverted. The question has to be asked where the goal
is ANSWERED: the entry resolving a quantified slot's goal must be tied to the binder (its
slot, or a requirement mentioning it), not merely cover the spec.

THE WRITTEN CHANNELS use exactly that rejected slot test today (TX0G6's
`names_a_declared_slot`, in `validate_written_selection`). It is conservative, never a wrong
answer: UNTIED is refused in both brackets. But TIED-2b written as a bracket
(`SortedSet[T = E, O = OE].insert(s, x)` inside `PolyD`) is refused too. That program RAN
before TX0G6 through the receiver spelling (the callee spelling always refused it); the bare
spelling still runs. There are zero such brackets in the suite or the three corpora. The
criterion this ticket settles should replace that gate as well, so that brackets accept TIED
and refuse UNTIED as the type channel will.

ACCEPTANCE.
  * UNTIED is refused (or answers correctly) on all four channels — callee bracket,
    receiver bracket, the direct type route, the spec (`carried_slot`) route — each driven.
  * TIED runs on all four, driven to values at TWO orderings (one answer could be a search
    that happened to agree).
  * The TX0G6 pinned row for 2b-through-a-bracket flips, and is updated with the decision.
  * A census over the three corpora and the full suite of what changes verdict, reported
    separately for the two shapes.
  * cargo-test green via rustland/scripts/test.sh.

REFERENCE: `infer_named_slot_bindings`, `carried_slot`, `slot_binder_state`,
`validate_written_selection` / `names_a_declared_slot`, `provider_half_projection` (Strategy
2b), `resolve_inner`'s `FromScope` step (typing.rs); WI-1094 (the forward rule), WI-456 (the
carrier route and Strategy 2b), WI-20260921-EE0EP (the parameter channel),
WI-20260911-TX0G6.

