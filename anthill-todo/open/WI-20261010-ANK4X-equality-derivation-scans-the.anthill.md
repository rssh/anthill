## Attributes

- id: WI-20261010-ANK4X-equality-derivation-scans-the
- created: 2026-10-10T19:53:16Z

- status: Open
- status_agent: user
- status_at: 2026-10-10T19:53:16Z

- acceptance: cargo-test

- tags: test-infra

## Description

EQUALITY DERIVATION SCANS THE PROVIDER RELATION AT EVERY READ — give the pre-typer half of `eq_derive` (`classify`, `derive_total_eq`, `derive_conditional_eq`) indexed reads, by making the provider index take a row where one is asserted. The second pass of lever A3 in docs/design/test-infrastructure.md §4 (one ticket a pass, filed one at a time: user, 2026-10-06), and NOT a frontier: the pass stays a pass over every composite, and no rule about what a later load may do is needed for it. With it, in the tests' support: a pool of bases in place of the one.

MEASURED 2026-10-10 on 5273d5a2, the gate's build (anthill-core at opt-level 2), one thread, medians of 15, temporary marks inside the three functions (not kept); a bloop JVM held half of one core throughout. Raw: docs/measurements/test-infrastructure/eq-derive-later-load-2026-10-10.txt. The later load is a copy of the sealed base and then one small user file that defines no composite — what a test on the shared base pays.

  the pass as it is                                     full load, one call    later load, on a sealed copy
  the whole load                                        283.0 ms               110.0 ms
  classify + derive_total_eq + derive_conditional_eq     25.5 ms    9 %         43.0 ms   39 %
      classify, all 127 composites                        0.6                    1.0
      total_composites                                    1.8  (41 total)        6.4  (0 total)
      the candidates filter of the conditional half       3.7  (77 candidates)  12.8  (60 candidates)
      its two fixpoints, PartialEq and Eq                17.8  (17 derivable)   20.9  (0 derivable)

Over a whole gate (docs/measurements/test-infrastructure/load-count-2026-10-10.txt, 12 threads): the pass is 36 % of a test's load on the shared base, those loads are 82 % of `wi_tests`' thread-time, and loading is 94 % of it.

WHY. The three functions run with `kb.provides_index` at `None`, by design: they assert provision rows, and the index is built once per state and takes no row (the drop at `load.rs` before `derive_forwarded_provisions` says so: "its reads must hit the live scan"). So `sort_provides` and the conditions lookup each fall back to a scan of the whole relation — once per composite in `total_composites`' seed, twice per composite in the candidates filter, and per field per round in the conditional fixpoint (`field_conditions`). Classifying every composite is 1 ms; the scans are the rest. The LATER load is the dearer of the two while deriving nothing: the relation it scans holds the rows the stdlib's load derived, and its 60 candidates are the stdlib composites that load found underivable (77 candidates less the 17 derived), asked again field by field at every load and found underivable again.

THE PROBE. `build_provides_index` at the top of `classify`, on the later load only — valid there because that load asserts nothing in the pass:

  the later load                                         as it is     index built first
  the whole load                                         110.0 ms      62.9 ms
  the three functions                                     43.0 ms       2.1 ms   (0.27 ms of it the build)
  the bench's `sealed clone+incr`, a test's load          116.9 ms      70.1 ms

Every count is the same in both columns: 127 composites, 3 boundaries, 6 partial, 76 carriers spoken for, 60 candidates, 0 derived.

WHAT TO BUILD — DECIDED 2026-10-10 (user): THE PROVIDER INDEX TAKES A ROW WHERE ONE IS ASSERTED. The index is updated where a `SortProvidesInfo` or a `ProvidesConditionInfo` fact enters the KB — the assert path, not each producer — so it is true at every read and no producer can leave it stale: the state "an index behind a producer that forgot to rebuild", the class WI-954 names for the requires-chain cache, stops being representable. The three functions then read through it in a full load as in a later one, and the drop-and-rebuild around this pass, `derive_forwarded_provisions` and `eq_derive::run` goes, with `later_equality_refusals`' build-for-one-read. The other way was weighed and not taken: rebuild the index after each batch of rows the pass asserts (0.27 ms a build, about four batches) — small, and it keeps the stale state possible. Things the build has to settle, each to be said at its site: what the index does at the points that drop it today for a reason other than staleness, if any is one; what a layer's discard does to it (`kb/layer.rs`); that `deep_clone` copies it or starts it empty and rebuilt, by the copier's own rules; and whether anything else keyed like it (`conditions_by_carrier`, the spec-base direction) has a producer outside that one place. No language rule changes: kernel-language.md is not touched.

THE CONTROL. The trap is a stale or wrong index: a read that misses a row asserted earlier in the same pass, and a composite silently not derived for, or derived twice — the suite can stay green through either. (1) An AGREEMENT switch for tests: with it set, every read of the provider relation is made both ways, through the index and by scan, and a difference fails the load loudly, naming the carrier and the spec. anthill-core's suite under it on the shared base AND under `ANTHILL_TEST_FRESH_LOAD=1` — one call over the stdlib is where the pass asserts between its reads. (2) A row that NEEDS a row asserted earlier in the same pass: a composite whose field is a parametric sort at a composite derived total in the same load (`holder(o: Option[T = Colour])`), asserting the VALUE of a call that requires `Eq[Holder]`, in one call and as a later load. Back the update out — the index left as it stood before `derive_total_eq`'s rows — and say at the site which rows fail and which pass either way by design. (3) The derived provisions of the stdlib's own load, listed before the change and after: the same rows, the same conditions. (4) The gate green under all three recipes.

WITH IT, in `anthill-core/tests/common/mod.rs` — A POOL OF BASES (user, 2026-10-10). `shared_base_instance` copies the binary's one loaded stdlib under ONE lock. Measured over a gate with a temporary timer: `wi_tests` takes 9 553 copies, 40-42 a second asked; a copy made beside eleven other threads takes 12.2-12.5 ms (6.8 ms alone), so one lock gives 80-82 a second and is half busy; a copy waits 6-7 ms for it on average, 2 % of the binary's thread-time. 9 553 copies one at a time are 116-119 s, so with one base `wi_tests` cannot run in less whatever a load costs; this ticket's change takes the asking rate to about 56 a second and the next pass to the floor (design doc §5.1). Build: N bases, each its own lock, each a deep copy of the first — the stdlib is still LOADED once per binary — a test taking a free one; N sized from the measurement, not guessed. KEEP the trace line that measured it, under `ANTHILL_LOAD_TIMING=1`: `[load_timing] base_copy wait=<duration> copy=<duration>` (docs/measurements/test-infrastructure/load_trace_report.py reads it and says so in its header). Its controls: `wi_szkv7_two_step_load_test` still OBSERVES the shared base, and the stdlib is still loaded once per binary (`SHARED_BASE_BUILDS`) — a pool that loaded N times would pass every test and give the gain back; the `wait` column before and after is the measurement.

EXPECTED. A later load on a sealed copy 110 ms -> about 63 ms; a test's load on the shared base 117 ms -> about 70 ms; `wi_tests` 240 s -> about 170 s, by the arithmetic of the design doc's §2.4 (the pass's share taken out of every later load, the rest as measured). A full load 283 ms -> about 260 ms, ESTIMATED from the marks (the pass 25 ms -> about 3 ms) and not probed, the probe being invalid where the pass asserts; that is the CLI's start and every spawn of `cmd_tests` too.

NEXT, not this ticket, filed after this lands: `check_provider_requires` — 38 % of what the probe leaves of a later load (23.8 of 62.9 ms), and the index STANDS when it runs, so its cause is another one, to be measured the same way before anything is designed; then `register_specialization_witnesses` (16 %), the typer's remainder (11 %), `check_override_refinement` (6 %).

DONE WHEN: the three functions make no scan of the provider relation in any load, and nothing drops the index to make a read true; the agreement run is clean on the shared base and under the fresh recipe; the back-out of control (2) is measured and written at its site; the pool is in, the stdlib loaded once per binary, and the `wait` column re-taken; the bench's rows and one traced gate are re-taken into docs/measurements/test-infrastructure/ and into the design doc's §2.4, §5.1 and §9 row 4; the gate is green under all three recipes.

