## Attributes

- id: WI-20260925-P5G39-provision-checks-resolve-under
- created: 2026-09-25T04:49:45Z

- status: Open
- status_agent: user
- status_at: 2026-09-25T04:49:45Z

- acceptance: cargo-test

- tags: typing

## Description

PROVISION CHECKS RESOLVE UNDER THE PROVISION'S OWN CONDITIONS. `coherence::check_provider_requires` checks `provides Spec[C] :- G…` against Spec's own contract by resolving each required goal with NO CONTEXT: `C`'s type parameters open and none of `G…` in scope. For a conditional provision that question is false by construction ('is every Pair an Eq?') and can only be answered by the second, hand-rolled route (`self_provides_required` + `conditions_entail`), which is what actually passes Pair today. The right question is 058 §3.9's: does the required goal hold with `C`'s parameters RIGID and `G…` in scope as ASSUMPTIONS (Candidate::Assumption).

MEASURED 2026-09-25 (probe on the Unavailable producer, then reverted), a bare stdlib load leaves 10 spec-half slots unresolved, all from this check via `spec_resolves_at_bindings` → `resolve` with an empty scope:
 (1) PAIR: `Eq[T = Pair]` / `PartialOrd[T = Pair]` / `WeakOrd[T = Pair]` resolve to Pair's own rows, whose conditions `PartialEq[Pair.A]` etc. are over Pair's OPEN parameters: forwarded NoMatch, a silent Unavailable in the spec half, and the result is discarded when the second route passes. Nothing is missing in pair.anthill.
 (2) THE SAME INNER GOAL, searched: `Eq[T = Pair.A]` unifies the open `A` with SortedSet's head `provides Eq[SortedSet[T, O]] :- Eq[T]`, so SortedSet is 'chosen' and its spec half fails. Its NoMatch hint talks about SortedSet's named slot `O`, which is noise from searching a goal nothing has pinned.
Contributing: `type_value_is_ground` answers true for a bare parametric sort (`Pair`), so the check takes its 'concrete' branch.

ACCEPTANCE: the check resolves required goals with the provision's parameters rigid and its conditions as assumptions; a bare stdlib load creates ZERO load-time `Unavailable` slots (re-run the probe: an eprintln at the synth.rs spec-half `Unavailable` push); `self_provides_required`/`conditions_entail` are removed or reduced to the resolver, and `ProvisionConditionsTooWeak` / `UnsatisfiedProviderRequires` keep their tests (wi1033/wi1110 rows); full workspace green via rustland/scripts/test.sh. CONTROL: a provision whose conditions really are too weak (`provides Ord[C] :- PartialOrd[E]` beside `provides Eq[C] :- Eq[E]`) is still refused. SOURCE: the WI-883 follow-up discussion (option 3).

## Changes

### 2026-09-25T04:55:06Z — feedback — user

CODE MAP AND PLAN (2026-09-25, prepared for the next session; read before designing). THE SITE: coherence.rs:227 check_provider_requires. For each provision row p (one row = one clause), for each goal in provision.rs:1149 provider_requires_subgoals(kb, p.spec, &p.sigma), it decides 'satisfied' by: (i) if every binding is type_value_is_ground (TRUE for a bare parametric sort, e.g. `Pair`): sorts.rs:1254 spec_resolves_at_bindings (an EMPTY ResolutionScope, sigma None, i.e. no assumptions and head-only candidate matching), OR the hand-rolled self_provides_required (a self-provision at the carrier AND coherence.rs:98 conditions_entail); (ii) otherwise a base-level sort_provides fallback. THE ASSUMPTION SET ALREADY EXISTS BY HAND: conditions_entail builds 'available = direct_requires_chain(carrier) + this clause's conditions as RequiresEntry{supply: Required}' from requires.rs:608 provision_conditions(kb, carrier). That is the scope P5G39 wants resolve to use. THE TWO HALVES OF THE FIX: (1) ASSUMPTIONS: resolve the required goal with ResolutionScope{available_requires: sort-level chain + p's own clause conditions, sub_goal_requires: the same (CKD4J's channel for sub-goals)}, per clause (for EVERY clause of the provision the goal must resolve; the quantifiers are in conditions_entail's doc). (2) RIGID PARAMETERS: pass sigma with the provision's own parameters as rigids. candidates.rs:178 collect_provides_candidates classifies a goal element by its sigma role (WI-827) and, with sigma None, falls back to a head-only match, which is exactly how the open `Pair.A` unified with SortedSet's head `Eq[SortedSet[T, O]]`. A rigid element should match only a variable head (a generic witness `provides Mon[T = E]`) or an assumption (FromScope). OPEN QUESTIONS to settle first: does requires_entry_covers_goal match the condition's `A` against the goal's `Pair.A` (same symbol, since conditions are written in Pair's scope; verify); does FromScope reach SUB-goals through available_requires or only sub_goal_requires (ResolutionScope doc, synth.rs:139); how a conversion (`Eq provides PartialEq[T = T]`, WI-1110) discharges `PartialEq[A]` from an assumed `Eq[A]` (it should: the FromScope projection path `[k]`, CKD4J). MEASURE-FIRST RECIPE: eprintln at synth.rs, the spec-half arm pushing ResolvedRequiresNode::Unavailable (the `i < provider_half_start` branch, ~line 1056), printing format_goal(goal), format_goal(sg), and the NoMatch goal_text/forwarded; build anthill-cli; `target/debug/anthill load <empty namespace file>`. Baseline 10 lines (7 distinct), all via check_provider_requires. Target 0. PINNING TESTS to read before changing the checker: wi869_per_provision_conditions_test, wi343_provider_requires_test, wi590_witness_param_carrier_test, wi1111_provision_chain_search_test, wi1098_derive_eq_total_test, wi_kxnex_provision_names_carrier_test, wi865/wi868 (absence). NOTE: on the main dev machine the full suite takes ~10 min; on the laptop it took ~80 min (target/ 83 GB, disk 94% full).

