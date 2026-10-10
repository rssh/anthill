## Attributes

- id: WI-20261010-9BKZ4-a-later-load-types-every
- created: 2026-10-10T06:11:50Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-10T12:42:42Z

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

## Changes

### 2026-10-10T12:42:40Z — feedback — user

DELIVERED 2026-10-10 — a sealed load's bodies are typed once, and what a later load could have changed in them is refused.

WHAT WAS BUILT IS NOT A FRONTIER. The description asked for "the operation bodies this load added". Built instead: the typer's two sweeps skip what a SEAL holds (WI-20261009-4ZRTG's seal, extended) — the sealed operations and the sealed sources whose load ran its typer. Everything not sealed is typed as before, so there is no ledger of what a load added, nothing to get wrong when an unsealed load replaces a body, and a plain sequence of loads (and `KB.loaded` over one) is unchanged. The refusals and the skip rest on the same seal.

THE PROBE, a library file sealed with the stdlib and then a program, against one call over both: (a) a `@[simp]` rule over a library operation rewrote the library bodies calling it in BOTH — in the later load because the sweep typed them again; (b) an operation added to a library scope under a name a library body reads was refused in both already, by proposal 059 R4's capture rule — nothing to add; (c) a provision of a library spec at library types, more specific than the library's, answered every call in one load and in two answered NEITHER the library's call nor the program's own, only a call through a generic body; a provider, an override and a more specific provision at a type of the program's OWN reached a generic library body the same way in both.

THE REFUSALS (`kb/typing/sealed.rs`, `LoadError::ChangesSealedCode`; kernel-language.md §8.3). Raised by the typer, inside its run, and read off the KB — every clause asserted since the seal was taken — so a run made by hand raises them and a load made after a refused one is refused again. (1) A `@[simp]` rule that reaches a sealed body: each sealed body that calls or constructs the rule's head is typed once more, and one that comes back rewritten or no longer types is the finding. EXACT, not "its head is a sealed operation" (user's words allowed the wider rule): the library itself documents `rule fact_monotonicity(Mine) <=> …` for a program's own sort, and a rule over a library operation for an argument only the program can write matches no library call. A dot rule cannot be asked that way and is refused when written for a sealed sort. (2) A provision that changes who answers a sealed dispatch: judged when all its elements are a sealed load's (user: "all elements should be situated in one sealed layer") — the spec, every type in its head, and its carrier where that is the provider — and refused when it is written into a sealed sort beside a provision that sort already makes there, when at its own head the unselected answer changes (strictly more specific, or a tie no default arbitrates), or when it overlaps a sealed provision with neither the more specific. NARROWER THAN "OVERLAPS", which is what was agreed in the discussion: a second provider that leaves the unselected answer where it was is the language's named-instance feature (`ByLength provides Ord[T = String]`) and loads; so does a program's spec that converts to a sealed one.

FOUND AND FIXED ON THE WAY. The typer's dispatch memo (`resolve_cache`) was never dropped between loads, though its own comment says a producer of provisions owes the call: an UNSEALED base and then a more specific provision answered the later file's own call with the base's choice (12 where one load answers 2), and a copy of the base, whose memos start empty, answered 2 — the two test recipes disagreed. A typer run now starts from no memoized dispatch.

THE CONTROL. `ANTHILL_TYPER_ORACLE=1` types the sealed bodies as well and fails a run that changes one (a call's classification compared without the terms a run mints; the dictionary slots as they are). The whole anthill-core suite under it on the shared base: no finding but the shapes refused. It cannot see a dot rule (said at the switch). `typing::bodies_typed_by_this_thread` counts what a run typed. `wi_9bkz4_sealed_bodies_test`: 25 rows, 22 measured back-outs in its header, each failing the rows it should.

/CODE-REVIEW of the first cut found fifteen things, fixed here and each with a row: the checks were the pipeline's (a typer run by hand skipped sealed bodies and refused nothing) and read one load's range (the load after a refused one loaded clean) — they are the typer's and read the KB; a load sealed without having run its typer had bodies no run would type — the seal keeps which were typed; a receiver-dispatched spec's carrier is its provider, so a second implementation of `Stream`-like specs was refused; a rule that leaves a sealed body ill-typed, a dot rule, and a second provision put into a sealed sort were not seen. An alias in a head needs nothing: the loader stores the head at what it stands for (a row holds that).

ONE EXISTING TEST PINNED to one load by name: `wi_ee0ep_param_dictionary_test::specificity_does_not_choose_a_type_carried_slot`, whose fixture provides the stdlib's `WeakOrd` at the stdlib's `Pair[String, String]` more specifically than the stdlib does — the refused shape, and the fixture's point.

MEASURED (docs/measurements/test-infrastructure/sealed-bodies-2026-10-10.txt): a later load after a sealed stdlib 159 ms -> 96 ms (the description expected 267 -> about 160 on that morning's slower machine, the same 40 %); a test's load on the shared base 179 ms -> 107 ms; `full / (clone + incr)` 1.5 -> 2.5; `wi_tests` 248 s in the gate, 412-491 s on the shared base the day before.

GATE, the change as landed: everything on the shared base 8 982 passed / 0 failed / 14 ignored; anthill-core under FRESH_LOAD, TWO_STEP_LOAD and TYPER_ORACLE each 8 099 / 0 / 6.

NOT COVERED, and said in the spec: a sealed load's own guarded `@[simp]` equation whose guard a later load's facts make provable; a type no source declares is in no seal. A sealed load's DERIVED rules (132 of the stdlib's 254 with a body) have no source to be known by and are still typed at every load.

NEXT, not filed: equality derivation (26 % of a later load before this change), `check_provider_requires` (12 %), then the tail.

