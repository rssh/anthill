## Attributes

- id: WI-20260923-WN9P8-forward-soundness-of-a
- created: 2026-09-23T08:45:54Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-23T11:30:00Z

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

## Changes

### 2026-09-23T11:29:54Z — feedback — claude

DELIVERED. A forward is answered by the frame's dictionary FOR its parameter, on every channel it reaches, or refused. Nothing that merely covers the slot's goal by spec answers it any more.

MEASURED FIRST (parent e8f6f9a3), scratch probe (deleted). A set typed O = ByLength driven against a frame whose other ordering is RevLen, and the mirror image. Columns: direct, spec (PersistentCollection.insert), callee bracket, receiver bracket.
  UNTIED, the ticket's R3 (named OE beside plain P): WRONG / WRONG / refused (check 1) / refused (check 1).
  Four more UNTIED variants, WRONG on the type channels: an anonymous requires WeakOrd[E]; an op-level P beside an op slot; a requirement binding OE while the set is typed P (2b answered P with OE's comparator); a callee's OWN op-scoped slot (RC2.add[E, OE] requires OE: ...) reached with P. And an eta'd insert at O = P: WRONG.
  P over String with no requirement at all: loaded clean, died at eval (Internal DeferToRequirement __req_weakord not bound).
  TIED: a named slot ran on all four channels, plus eta and a callee's op slot. X: Ord[E] answering WeakOrd ran on all four. 2b via FiniteCollection[C = SortedSet[T = El, O = OE]]: direct ran; spec REFUSED ("unresolved: WeakOrd[T = ?]": the scope searched the sub-goal by spec, and the provider half is no scope entry); both brackets refused (TX0G6's conservative gate).

THE CRITERION, one owner (typing.rs, binder_frame_slots): the frame slots that hold the parameter X's dictionary.
  * X's OWN named slot, found by X's DECLARATION, not by searching the frame. The path is rigid -> canonical var (param_rigids) -> parameter -> declaring sort or op -> slot -> frame position, verified against the entry's spec. New: KnowledgeBase::type_param_of_canonical_var, the reverse of the canonical-var map, with the same one writer. An op's position skips value preconditions (op_named_slot_chain_index).
  * a CARRIER's named slot that a frame requirement binds to X: the 2b shape, under 2b's own gates (provider_half_carrier, now shared with provider_half_projection).
  Own slot first; the first one that answers the demand is used. One level into X's own slot is allowed (Strategy 2's composition), so X: Ord[E] answers WeakOrd.

WHERE IT IS ASKED: at the answer sites, as the ticket said it must be.
  * The dictionary build, project_forwarded_slot, for a callee's sort-level slot (build_dispatching_dict_from_chain: direct, eta, rule body) and its op-scoped slot (build_op_scoped_dicts). A forward never reaches Strategies 1-3.
  * The spec route: carried_slot -> Forwarded(slots) / Untied, and resolve_inner answers the sub-goal FromScope at that slot (the provider-half offset for a carrier's slot).
  * The brackets: validate_written_selection forwards any value naming a parameter, and the answer site decides. names_a_declared_slot is deleted.
  * Both same-sort inherits (the direct call, and the eta's __req_self capture) are taken only where every named slot forwards ITSELF (inherit_answers_every_forward). Otherwise a dictionary is built, and the rule above answers or refuses.
  An untied forward is refused with one sentence on every channel: RequirementRefusal::untied, and the spec route's NoMatch hint. It names the slot and the parameter, and says whether the frame holds nothing for it, holds a slot that does not answer, or holds the operation's own slot on a route that reads only the sort half (eta).

NOW (wi_wn9p8_forward_soundness_test, 12 rows):
  UNTIED is refused on direct, spec, both brackets, eta, a callee's op slot and a same-sort sibling. Direct and both brackets refuse with byte-identical messages. All five UNTIED variants are refused (R10's eval death is now a load refusal).
  TIED runs at two orderings: named slot, 2b via FiniteCollection and the Ord slot on all four channels; an operation's own slot (after a value precondition) on direct and spec; a callee's op slot and eta.
  TX0G6 rows: a_plain_parameter_tied_to_a_requirement_is_refused_in_brackets_too FLIPPED to ..._forwards_in_brackets_too (bare, callee, receiver at two orderings). a_plain_parameter_is_refused_in_both_spellings keeps its verdict, with the forward's message.

CENSUS (counters at the direct, spec and bracket sites plus the no-route park, removed).
  CORPORA: anthill load of stdlib (--no-stdlib), examples/github-todo, rustland/anthill-todo/anthill, rustland/anthill-stl/anthill. 0 hits at every site; no corpus verdict changes.
  SUITE, whole workspace (37 binaries), pre-existing tests only:
    TIED: 35 forwards in 7 files (wi1094 4, wi456_no_scope_route 7, wi456_sorted_set_collection 4 via spec, wi844 2, wi_159s9 4, wi_ee0ep 4, wi_tx0g6 10). EVERY one answered with the same dictionary the spec-keyed search picked. 0 verdict changes.
    UNTIED: 4. wi456 an_undeclared_ordering_is_refused_at_load, the_refusal_names_the_repair_and_not_a_witness_choice, a_callee_that_never_reads_the_slot_...; wi_3g1yt a_carriers_own_requires_is_not_held_by_a_value_of_it. All were refused before by the parked no-route refusal and are refused now by the forward's. Verdicts and assertions unchanged.
    Newly forwarded bracket values: only TX0G6's two rows above.
    The no-route park is still reached by 7 non-forward deps (wi1000, wi1110, wi456 strategy_2b..., wi822, wi_1z3e7, wi_n31xx, wi_rs2g4), so it stays.

BACK-OUT, measured one mechanism at a time (the test file's header has the full table):
  (D) dictionary-build forward -> 4 WN9P8 rows + wi_tx0g6 plain-parameter row
  (S) spec-route forward -> 2
  (B) bracket gate back to "is a named slot" -> 2 WN9P8 + 2 TX0G6
  (P) projection into the own slot -> 1
  (Q) value-precondition skip -> 1
  (I) inherit check -> 1
  The no-route park alone -> wi456 strategy_2b_declines_a_witness_provider only; route 4's obtainability gate alone -> nothing. wi456's three no-route rows and wi_3g1yt's row are refused by (D) first, and redden only with (D) plus the park, or (D) plus the gate (measured; the wi456 and wi_3g1yt comments are updated to say so).

REVIEW. /code-review (high), 7 findings, 6 fixed:
  (1) CONFIRMED REGRESSION of the widened bracket gate. A same-sort sibling ins[OE = P](s, x) inherits the frame, so no answer site asked, and all three spellings ran in OE's order. Fixed by inherit_answers_every_forward and pinned by a_same_sort_sibling_refuses_an_untied_forward.
  (2) The eta refusal of an operation's own slot claimed nothing held its dictionary; it now names the route's reach.
  (3) A slot binder with no canonical variable now panics as a loader invariant instead of silently skipping the forward.
  (4) All tied slots are tried, not only the own slot.
  (5) One owner for rigid -> parameter (param_of_rigid).
  (7) A comment at the spec route's early continue.
  Skipped (6): op-slot index recomputation, reached only by operations that declare named slots (6 forwards in the whole suite).

BOUNDARIES, recorded and not closed:
  * An operation's own type parameter written as a bracket VALUE (SortedSet.insert[T = E, O = OE] inside add[E, OE]) reaches the σ-read producer with no witness reading and is refused ("must name a WITNESS SORT") before any forward is asked. Pre-existing and loud; recorded at an_operations_own_slot_forwards.
  * The eta route builds from the sort half only, so a forward of the enclosing operation's own slot is refused there (it was refused before too), now with that reason.
  * Two same-spec named slots cannot be driven at two orderings: the caller refuses two witnesses for one spec.
  * PolyD's spelling through the spec, with PersistentCollection itself required, fails on an unrelated effect row (undeclared effect ?_). That is why the 2b spec row requires FiniteCollection instead.

DOCS: kernel-language §5.4 (the forward rule); proposal 058 §3.4 (forwarding needs the frame's dictionary FOR the parameter); 058-implementation §2.
RUST-ONLY: scaland loads no operations and has no dictionary build.
cargo-test: full workspace green via rustland/scripts/test.sh (36 binaries, 7366 passed, 0 failed).

