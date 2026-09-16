## Attributes

- id: WI-20260916-8WRJC-default-rung-2a-is-declined
- created: 2026-09-16T18:08:41Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-16T18:44:58Z

- acceptance: cargo-test, scaland-sbt-test

- tags: vvm1r

## Description

DEFAULT RUNG 2a IS DECLINED FOR A SPEC WHOSE OPERATIONS ARE ALL NULLARY, so a provision tie that HAS a default is reported as one nobody can settle. `goal_carrier_key` (typing.rs:33974) reads `spec_carrier_param` — rung 1 only, "the param some declared OPERATION receives on" — where WI-1102's `spec_carrier_param_or_sole` (typing.rs:36504) is the ONE owner of the same question and answers it op-independently. A spec declaring `sort T = ?` whose ops are all nullary has a carrier PARAMETER and no op mentioning it, so rung 1 answers None, `goal_carrier_key` declines the rung outright, and `default_among_candidates` (typing.rs:33937) never asks the defaults substrate at all.

MEASURED 2026-09-16, two providers of one instance — `Red provides Desc[T = Red]` (tag 7, so the INFERRED `default_provider` row of 058 sec 3.6 names it) beside `Rival provides Desc[T = Red]` (tag 11). Spec ops all nullary: the goal TIES and `find_dictionary` reports 'two providers answer Desc[T = Red] at run time: Red, Rival'. THE SAME PROGRAM with one DEFAULTED carrier-bearing op added to the spec (`operation touch(x: T) -> Int64 = 0`, which no provider implements and nothing calls) answers 7 — the self-providing carrier's default — with no tie at all. One op declaration, present or absent, decides whether a default is consulted; nothing about the providers or the goal changes.

THE FIX IS TO ASK THE OWNER, not to widen rung 1: `goal_carrier_key` calls `spec_carrier_param_or_sole`. Its rung 2 (a SOLE type parameter) is already gated on `spec_is_self_representing` for exactly the hazard that would otherwise bite here — WI-1076's measured defect, seven stdlib provisions filed at the type VARIABLE T when a spec's sole parameter is the ELEMENT and not the carrier. Both of rung 1's `None`s reach `goal_carrier_key` today and only one of them licenses rung 2; that distinction is the whole of WI-1102 and this site does not make it.

BLAST RADIUS TO CENSUS BEFORE BUILDING, and it is the reason this is a ticket rather than a one-line edit. Fourteen stdlib sorts reach rung 2 per WI-1102's own measurement (Eq, NonEq, Monad, DelayMonad, BoundedLattice, Modify, Effect, EffectsRuntime, Modifiable, Option, StoredRef, Monad.M, the two realization.runtime dictionaries). Every one of them becomes default-consultable AT THE DICTIONARY FETCH, where it was not before, and the change is in the ANSWERING direction: a goal that residualized now answers. Count which of them actually have two candidates at a fetch — a rung that can be consulted and never fires changes nothing — and say so at the site.

ACCEPTANCE. The two-provider nullary-spec program above answers 7 by default and records NO tie. That is a row this repo already ships and it FLIPS: `wi_x9pb4_require_dictionary_element_test::a_tie_the_default_rung_never_saw_is_an_error_not_an_abort` must be re-aimed, and its sibling `the_same_tie_takes_its_default_when_the_spec_has_a_carrier_bearing_op` — whose whole content is that the added op is what decides — becomes the CONTROL that measures nothing and should be folded into it. The file header paragraph that cross-references them says which row reaches which arm and must be corrected with them.

AND THE Error ARM MUST STAY DRIVEN. A tie with NO default — two rival providers where neither is the carrier itself, so no inferred row names one — is the population that still reaches `FindDictFetch::Defect`, and since 2026-09-16 that arm returns `BuiltinResult::Error` (resolve.rs:8284) rather than aborting. Replace the flipped row with that shape, asserted on the message in `ResolveStats::errors`, or this fix silently retires the only test that reaches the arm.

CONTROLS, each stated at its site: a SELF-REPRESENTING spec must still decline rung 2 (WI-1076's seven provisions — back out the gate and they move); a spec with a carrier-bearing op answers exactly as today (passes either way by design); and a MULTI-parameter spec with no receiving operation stays None, which `spec_carrier_param_or_sole`'s own doc calls out as deliberately not refused. Say which rows fail when the change is backed out and run each back-out with a patch that ASSERTS it applied. cargo-test green via scripts/test.sh.

