## Attributes

- id: WI-20261011-A3NND-check-provider-requires-checks
- created: 2026-10-11T05:08:35Z

- status: Open
- status_agent: user
- status_at: 2026-10-11T05:08:35Z

- acceptance: cargo-test

- tags: test-infra

## Description

`check_provider_requires` CHECKS EVERY PROVISION OF THE KB AGAIN AT EVERY LOAD — measure where its time goes on a later load, then decide with the user what a later load owes it. The third pass of lever A3 in docs/design/test-infrastructure.md §4 (one ticket a pass, filed one at a time: user, 2026-10-06; this one asked for 2026-10-11, after WI-20261010-ANK4X).

MEASURED 2026-10-11 on the tree of WI-20261010-ANK4X as delivered (docs/measurements/test-infrastructure/provider-index-2026-10-10.txt §2 and §8). One thread, the gate's build (anthill-core at opt-level 2), medians of 15, the bench's loads: on a LATER load — one small user file that writes no provision, into a copy of the sealed stdlib — the pass is 26.0 ms of 62.2 ms, 42 %. On a full load it is 21.8 ms of 254.6 ms, 8.6 %. So it costs more on the load that adds nothing than on the one that loads the library. Over one traced run of anthill-core (12 threads, a machine at two thirds of its speed): 63.5 ms of the 149.4 ms a test's load on the shared base costs, 42.5 %; those loads are 77 % of `wi_tests`' thread-time, and loading is 90.7 % of it.

WHAT IS KNOWN OF WHY. The pass (`typing::check_provider_requires`, kb/typing/coherence.rs) takes no list of what the load added: it decodes every `SortProvidesInfo` row of the KB (`provides_rows`; 413 after the stdlib's own load) and resolves, for each, the `requires` goals of the provided spec through the resolver (`provider_requires_subgoals`, `resolve_within_provider`), under what the carrier's own provision may assume (`CarrierAtOwnParams`). The provider index STANDS when it runs, and stood before ANK4X too — the pass was 23.5–24.9 ms on a later load before that change and is 24.2–26.0 ms after — so its cost is not the scans that ticket removed.

WHAT IS NOT KNOWN, and is to be measured before anything is designed: how the 26 ms divides between decoding the rows, building the requires chains (load.rs says the pass builds the chain for every provider), and the resolutions; why the later load is the dearer of the two; and how many of the 413 verdicts a later load CAN change. ONE LEAD, read off the code and not measured: the chains and dictionaries the pass walks are memoized (`requires_chain_cache` and its siblings, `resolve_cache`), `load_phase_inner` clears the chain memos unconditionally at two points of every load (`invalidate_requires_chain_cache`, around `derive_forwarded_provisions`), and `KnowledgeBase::deep_clone` starts all ten of them EMPTY in a copy — so a later load may be rebuilding for every provision of the stdlib what the stdlib's own load had already built. If that is where the time is, the lever is in when those memos are cleared and whether a copy carries them, which is WI-20261011-W3VWC's subject (filed the same day); measure before leaning on it.

FIRST, MEASURE, as ANK4X was: temporary marks inside the pass (not kept), each with the count of what the step visited; the bench at ITERS=15, the BEFORE and AFTER binaries run side by side so that a row is of one machine state; the raw file into docs/measurements/test-infrastructure/.

THEN DECIDE, with the user, which this is — not decided here. Either the pass's reads want a memo or an index, as equality derivation's turned out to (no rule about loads needed); or the pass is a frontier's: a provision is checked by the load that asserted it, and a later load checks its own rows plus whatever it could have changed the verdict of — the shape WI-20261010-9BKZ4 gave the typer's sweeps behind a seal (`typing/sealed.rs`). For the second, the question that has to be answered first is which earlier verdicts a later load can change: the provider relation only grows, so a requirement that RESOLVED keeps a provider but can gain a second one (a tie where there was one answer), and a later load can add a condition or a `requires`. Each such way is either re-checked or refused, and said so at its site.

THE CONTROL. The trap is A3's: a row skipped that should have been checked fails in silence — a provision whose requirement nothing supplies loads clean and dies at eval on an unbound dictionary slot. So whatever is built carries an ORACLE switch for tests, as `ANTHILL_TYPER_ORACLE` is for the typer's sweeps: with it set the pass checks every row as it does today, and a load whose errors differ from the narrowed pass's fails loudly. anthill-core's suite under it on the shared base and under `ANTHILL_TEST_TWO_STEP_LOAD=1`. A fixture for each way a later load can change an earlier provision's verdict, asserting the refusal or the re-check, with its back-out measured and written at its site. The switch has a control of its own that says in the run's log whether it took (the pattern of `wi_ank4x_provider_index_takes_rows_test::the_agreement_control_runs_when_it_is_asked_for`). The gate green under all three recipes.

EXPECTED, by arithmetic, to be replaced by the measurement: a later load 62 ms -> about 36 ms if the pass costs nothing where nothing was added; `wi_tests` 158–165 s -> about 118 s by the design doc's §2.4 arithmetic. Twelve-thread wall times are of a machine that throttles (§5.1, §10: read `pmset -g therm` around a run); the one-thread bench is the measurement.

NEXT, not this ticket, filed after this lands: `register_specialization_witnesses` (17 % of a later load today), the typer's remainder (11 %), `check_override_refinement` (6 %).

DONE WHEN: the pass's time on a later load is accounted for step by step in a raw file; the shape is decided and recorded here; the oracle run is clean on the shared base and under two steps, and its own control is in; each fixture's back-out is measured; the bench's rows and one traced run are re-taken into docs/measurements/test-infrastructure/ and the design doc's §2.4 and §9 row 4; the gate is green under all three recipes.

