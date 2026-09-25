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

