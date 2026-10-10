## Attributes

- id: WI-20261010-9BKZ4-a-later-load-types-every
- created: 2026-10-10T06:11:50Z

- status: Open
- status_agent: user
- status_at: 2026-10-10T06:11:50Z

- acceptance: cargo-test, scaland-sbt-test

- tags: test-infra

## Description

A LATER LOAD TYPES EVERY LIBRARY OPERATION BODY AGAIN — make the typer's free-operation sweep and its rule-body sweep work over what the load added. The first pass of lever A3 in docs/design/test-infrastructure.md §4 (frontier-driven passes), which goes one ticket a pass, filed one at a time (user, 2026-10-06); this pass is first because it measures largest.

MEASURED 2026-10-10 on f68982b5, the gate's build (anthill-core at opt-level 2): a copy of the loaded stdlib (87 files), then one 4-line user file loaded into it, 15 runs, medians, `ANTHILL_LOAD_TIMING=1` plus temporary marks inside `type_check_sorts_collect` (not kept). A java process held 30-40 % of a core throughout and the machine ran about 1.4x slower than on 2026-10-09 (parse 108 ms against 77 ms), so read the shares before the milliseconds.

  the second call, 267 ms                                          ms    share
  type_check_sorts                                                119     45 %
      the free-operation sweep (`check_operation_bodies`)          99     37 %   it is 16 ms in the stdlib's own load
      `type_rule_bodies`                                           11      4 %
      its fourteen other steps, none over 1.5 ms                    9      3 %
  eq_derive::classify + derive_total_eq + derive_conditional_eq    69     26 %   and 44 ms in the stdlib's own load
  check_provider_requires                                          33     12 %
  register_specialization_witnesses                                14      5 %
  check_override_refinement                                         6      2 %
  eq_derive::run                                                    4      2 %
  everything else, about forty phases                              22      8 %   loading the file itself is 1.6 ms

WHY THE SWEEP IS THE WHOLE KB. `free_ops` (kb/typing/sorts.rs) is every body in `op_bodies` that no sort in THIS LOAD's list owns. In the stdlib's own load that is the namespace-level operations, 16 ms. In a later load the list holds the later load's sorts only, so every library operation, sort-owned or not, counts as free and is typed again: 99 ms for a 4-line file.

WHAT TO BUILD. The sweep is handed the operation bodies this load added, as the sort loop is already handed `typing::Loaded` (the sorts it defined and the range of rule slots it filled, WI-20261006-SZKV7's fix): one more member of `Loaded`, filled by the loader from what the load declared, not found by subtracting from the KB. `type_rule_bodies` reads `Loaded::rules` the same way. In one call the frontier is everything, so a one-call load is unchanged.

WHAT A LATER LOAD MAY DO TO A LIBRARY BODY — DECIDED 2026-10-10 (user). Once library bodies are not typed again, a later load that would change how one is read has to be either followed (that body typed again) or refused. Three ways were named, none probed yet:

  the later load adds                                                        in one call                                          decided
  (a) a `@[simp]` rule whose head is a library operation                     it rewrites every library body calling that head    REFUSED, a load error
  (b) an operation inside a library scope                                    a library body's bare name may resolve to it        REFUSED, a load error
  (c) a more specific provider, or an override                               a library call site may select it                   MUST WORK as it does in one call

(a) and (b) extend the seal (WI-20261009-4ZRTG) and go into kernel-language.md §8.3 beside it, with this change. (c) needs NO library body typed again in the ordinary case (user, same day): a provision or an override for the PROGRAM's own type cannot be what a library call site selected, the library having no call at a type it cannot name — a generic library body reaches it through the dictionary its caller passes, and the caller is typed in the later load; an override is reached by the value's carrier. What is left is one corner, argued from §5.4's "a strictly more specific head wins outright" and NOT YET REPRODUCED: a later load's provision of a library spec at a carrier built from LIBRARY types only (`Show[T = List[T = Int64]]` beside the library's `Show[T = List[T = A]]`), which in one call a library body's concrete call at that type would select. It is the shape `EqualityOfEarlierSort` already refuses for equality. DECIDED (user, same day): REFUSED, a load error, for every spec — when ALL ITS ELEMENTS ARE SITUATED IN ONE SEALED LAYER (the library, in our case): the spec, every type of the carrier, and the provision it overlaps. A provision with any element of the program's own is not this shape and loads. So no library body is ever typed again, and the frontier is exactly what the load added. Note for the build: the seal (`SealedDeclarations`, WI-20261009-4ZRTG) is one set with no layer identity; with one sealed layer the two coincide, and "one layer" has to be recorded before there is a second. First step of the work: probe the three under one call and two and bring the table, with (i) for (c), the corner above, reproduced or shown impossible; (ii) for (a) and (b), how wide the refusal is — every `@[simp]` rule over a sealed operation and every operation declared into a sealed scope (cheap, and what the user's words say), or only those a library body could reach — and how many fixtures of the suite do either today.

THE CONTROL. The trap is a body skipped that should have been typed: it fails in silence and the suite stays green. (1) An oracle switch for tests: with it set the typer computes the frontier, then runs the whole sweep as today, and fails loudly if a body OUTSIDE the frontier produced a diagnostic or came out different (its body tree after the simp write-back, its call classifications, its dispatch rewrites). The anthill-core suite is run under the oracle in the shared-base recipe and in two-step; every hit is a missing edge or a case for §8.3. (2) For (c), a test whose fixture is a later load adding a provider for its own type, and one adding an override, each asserting the VALUE a generic library body then computes through it, the same under one call and two. They pass with the sweep as it is today too, by design: they are what the narrowed sweep must not break, and the oracle is what catches a body it skipped. For (a), (b) and (c)'s corner, a row each: refused as a later load, with the library's site named; back the refusal out and the row fails. (3) The gate green under all three recipes.

EXPECTED. The second call 267 ms to about 160 ms on the machine as measured; a test under the shared base (`clone+incr`) 288 ms to about 180 ms. This is not the whole of A3: with equality derivation and `check_provider_requires` done too the call is still about 55 ms, a fifth of today's and not the 0.01 s the design doc's §9 row 4 expected, the rest being the tail in the table.

NEXT, not this ticket, each filed after the one before it lands: equality derivation (69 ms, and why it costs more in a later load than in the stdlib's own); `check_provider_requires` (33 ms); then the tail (`register_specialization_witnesses`, `check_override_refinement`, the forty small phases).

DONE WHEN: a later load types the bodies it added and no others; (a), (b) and (c)'s corner are load errors behind the seal and §8.3 says so; the oracle run is clean under shared-base and two-step; (c) has its value-asserting tests; the bench's `incr` and `clone+incr` are re-taken on a quiet machine and written into docs/measurements/test-infrastructure/ and the design doc's §9 row 4; the gate is green under all three recipes.

