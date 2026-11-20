## Attributes

- id: WI-20260923-DK0QJ-a-named-slot-reached-with
- created: 2026-09-23T18:41:30Z

- status: Claimed
- status_agent: claude
- status_at: 2026-11-20T19:14:30Z

- acceptance: cargo-test

- depends_on: WI-20261105-P0QGF-proposal-073-stage-3-a-value, WI-20261105-CBRD2-proposal-073-stage-4-no-typed, WI-20261113-S4D63-proposal-074-stage-10-the-host

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

## Changes

### 2026-11-05T19:50:00Z — feedback — claude

Decided with the user 2026-11-05: not fixed by ranking. Proposal 073 (docs/proposals/073-abstract-values-are-instances.md) removes both routes this ticket ranks on: no dictionary is built from argument values at run time (073 §4), so (b), the sort half through resolve_bridge_requirements, goes with that stage, and (a), the nested slot reached by interp.call, goes with it and with the host-entry question (073 §6.1). This ticket stays open and depends on the 073 tickets that remove them. Its acceptance becomes theirs: a set built at the generic witness beside a more specific rival answers what the typed route answers, or is refused at load, never with the rival's dictionary.

### 2026-11-13T23:42:26Z — feedback — claude

Half (a) — the nested slot reached on the host route — moved with 073 §6.1 to 074's stage 10 (WI-20261113-S4D63), decided with the user 2026-11-13; this ticket now depends on it as well. Half (b) through the SLD bridge stays with WI-20261105-CBRD2.

### 2026-11-20T19:45:58Z — feedback — user

Picked up 2026-11-20 (the user: 'Yes', fix both routes). MEASURED first on main with a probe over ATFGH's fixture (a set {pair("a", "z")} built at the generic Flat beside the more specific PairNe and the stdlib Pair; asked for its own element, only PairNe says false): the typed host call and a rule body answered true on both shapes (direct O = Flat, nested O = ByInner[OI = Flat]); a WRITTEN QUERY Driver.flat(0, ?s), MySet.contains(?s, x, ?r) answered false definite with nothing derived; a goal built at run time and typed by no load answered false definite, one dictionary derived from the value. Three changes. (1) A query's late positions are settled as a clause's: query_goal_var_types collected its goals' constraints and never read flat's result column (a LatePosition::ResultColumn), so ?s was at MySet[T = ..., O = ?] and contains' O was inferred by the ladder. settle_late_positions takes a ClauseSite (a stored rule, or a query: no head, no bound, the global scope); a query skips RuleGoal positions, read by its own stamped_column_type (settling them too refused two wi_cbrd2_typed_query_variable rows, held's column read as Option[T = Int64] where the stamp leaves T open). (2) Half (b): the bridge's derivation (kernel-language 5.2, a call no typer reads) answers a named slot of either owner Unranked, not only a type-carried one: MySet's own O went to PairNe at Withhold. (3) Half (a), the nested slot: below an Unranked goal a chosen provider's named slot is Unranked too (resolve_inner's sub_rung); an anonymous one keeps its rung, its provider being no choice of the value's. Rows: wi_dk0qj_generic_witness_rival_test (5): the written query true on both shapes and on the <=> spelling, 0 derived; the run-time goal undecided on both shapes (one delayed answer per literal, neither definite); controls: a sole provider (Int64, and ByInner over Boxed[E = Int64]) answers the run-time goal definitely, and the host call and both rule spellings answer true. Back-outs measured with temporary switches, each alone: query settling off fails the query row (false definite; the <=> spelling alone answers nothing at true); the bridge at Withhold fails both run-time rows; the sub-slot at its own rung fails the nested row only; the controls pass under all three. Pinned to one load by name (PairNe provides the stdlib's WeakOrd at the stdlib's Pair), in wi_rah0z's PINNED. /code-review high: 8 findings, 2 fixed (the query's dropped disagreements comment overclaimed a refusal; the <=> query form undriven), 2 no change (an anonymous intermediate's provider is not the value's choice; the DeBruijn unreachable in a query site, loud by design, no gate row reaches it), 4 skipped (a dot in a query settles at no variable types, as before nothing settled it; the query's domain is the global scope, as every caller reads one; the supplied-dictionary check's resolution under a sticky Unranked, which can only keep the supplied dictionary; two overlapping rung conditions). Gate 12405 / 0 / 17; families green on both carriers, no verdict moved; scaland not run (no Scala change).

