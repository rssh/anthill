## Attributes

- id: WI-20260923-DK0QJ-a-named-slot-reached-with
- created: 2026-09-23T18:41:30Z

- status: Open
- status_agent: user
- status_at: 2026-09-23T18:41:30Z

- acceptance: cargo-test

- tags: typing

## Description

A NAMED SLOT REACHED WITH VALUES ONLY IS STILL RANKED BY SPECIFICITY — ONE LEVEL DOWN AND ONE HALF OVER FROM WI-20260922-ATFGH — SO A VALUE BUILT WITH A GENERIC WITNESS CAN BE ANSWERED FROM A MORE SPECIFIC RIVAL, IN SILENCE. Found by /code-review (round 3) on ATFGH.

WHAT ATFGH CLOSED. An EE0EP type-carried slot (`has(s: MySet[T = String], x)` → `s.O`) reached with argument VALUES only — host entry, SLD bridge, value-directed dispatch, the eval gate — now resolves under `DefaultRung::Unranked`: neither 058 §3.2's default NOR specificity may choose, because the value chose a provider and does not carry it (058 §4.7). One provider is exact; a tie is the `ParamSlotNotCarried` marker. MEASURED by `wi_ee0ep_param_dictionary_test::specificity_does_not_choose_a_type_carried_slot`: under `Withhold`, `pick_most_specific` handed a set built at the generic witness `Flat` the more specific `PairNe`'s dictionary and answered `Ok(false)`.

WHAT IT DID NOT, and it is the same class. Two sibling slots still take `DefaultRung::Withhold`, which withholds only the default and lets a strictly-more-specific candidate win silently:
 (a) NESTED — the chosen witness's OWN named slots (`ByInner requires OI: WeakOrd[…]`), whose rung `resolve_inner` re-derives per sub-goal through `rung_for_dep` (Withhold). Reached by plain `interp.call` when the top witness is unique, and by `call_with_witnesses`, whose selection carries `slots: Vec::new()` (a bare witness name cannot spell `O = ByInner[OI = Flat]`; the typed route reads it through `witness_value_slot_selections`). Shape: a set built at `O = ByInner[OI = Flat]` beside a more specific `PairNe` → `OI` answered by `PairNe`.
 (b) SORT HALF — a carrier's own named slot reached by value (value-directed dispatch to `MySet.contains`, the SLD bridge): `resolve_bridge_requirements`' sort half asks `rung_for_dep(parent, …)` → Withhold. Ties already record absent there (WI-456); a strictly-more-specific rival takes the same `pick_most_specific` path. NOT MEASURED — it is the code path, and the first job is to drive it.

DO NOT CONFLATE with R10KC's pinned host row (`wi_r10kc_spec_default_body_dictionary_test::the_host_entry_route_answers_by_value_direction`): that one is WI-868's STAND-IN falling to value-direction on `interp.call`, a different mechanism with its own decision (ATFGH point (d)).

DECIDE AT PICKUP.
 (1) WHERE the value-only fact reaches `resolve_inner`. `rung_for_dep` is also the typer's COMPILE-TIME path, where `Withhold` + specificity is 058's rule for a slot nobody chose — so `Unranked` cannot simply replace `Withhold` for every named slot; the route has to be threaded down (the sub-goal recursion derives its own rung).
 (2) The host spelling of a nested witness, if (a) is to be answerable from the host rather than only refused.

FIXTURE LANDMINE, measured on ATFGH: a witness generic over an ABSTRACT element (`sort Flat sort E = ? provides WeakOrd[T = E]`) does not load — the provider check wants `Eq`/`PartialOrd` provided by the witness itself at an abstract `T`, and a `:-` condition does not satisfy it. Make it generic over a CONTAINER that provides them (`provides WeakOrd[T = Pair[A = A, B = B]]`), as `specificity_does_not_choose_a_type_carried_slot` does. And a carrier's own concrete provider cannot be written as a witness (`O = Pair` is refused: "an explicit `[WeakOrd = Pair]` cannot change it").

ACCEPTANCE: a fixture per half — (a) nested, (b) sort half — with a generic witness beside a more specific rival: the value-only route refuses naming the slot or agrees with the typed route, never the rival's answer; each row's `Withhold` back-out measured to fail; ATFGH's rows still green; full workspace green via rustland/scripts/test.sh.

REFERENCE: `DefaultRung::Unranked` and `resolve_inner`'s choice (kb/typing/synth.rs), `sole_provider` / `pick_most_specific` (kb/typing/candidates.rs), `rung_for_dep`, `resolve_bridge_requirements`, `resolve_param_witnesses` (kb/typing/bridge.rs), `param_slot_witness` / `witness_value_slot_selections` (the typed route), WI-456, WI-861.

