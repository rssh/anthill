## Attributes

- id: WI-20260920-E3DC5-provision-relation-readers
- created: 2026-09-20T09:35:32Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-20T13:56:29Z

- acceptance: cargo-test, scaland-sbt-test

- tags: perf

## Description

PROVISION-RELATION READERS SCALE BADLY — `derive_forwarded_provisions` is QUADRATIC in the provision count, and several load passes read the relation before `provides_index` exists. Pre-existing; MEASURED by WI-20260919-HXGXF, which exposed it rather than caused it.

THE MEASUREMENT (ANTHILL_LOAD_TIMING=1, 3-run averages — a single run carries ~35ms of noise, a third of the effect, so single-run attribution is not trustworthy here). Adding 168 derived provisions to the stdlib grew the relation 219 -> 387 (+77%) and cost +113ms on a ~940ms load. Only ~5ms of that was the pass doing the deriving. The rest, per phase:
  type_check_sorts                288 -> 341ms   +52.5   (46%)
  check_provider_requires         102 -> 126ms   +24.2   (21%)
  derive_forwarded_provisions     5.6 -> 19.6ms  +14.1   (12%)
  eq_derive (classify+total+cond)  85 -> 91ms     +6.3    (6%)
  eq_derive::run                  5.4 -> 9.3ms    +3.9    (3%)

(1) `derive_forwarded_provisions` IS QUADRATIC. 5.6 -> 19.6ms for a 1.77x input: linear predicts 9.9ms, quadratic predicts 17.5ms. Whoever adds provisions pays it, and it compounds as the stdlib grows.

(2) PASSES SCAN THE RELATION BEFORE `provides_index` IS BUILT. The index is not built until the typer starts, so every pass above it does a live scan per query. `eq_derive::total_composites` already memoizes locally to dodge this and says so at its site; HXGXF's own `type_value_derive` hit the same thing (a `sort_provides` per sort, fixed inline by reading the carrier set once). Two local workarounds for one general problem is the signal. Ask whether the index can be built earlier, or whether these readers can share one.

WHY IT MATTERS NOW: HXGXF ships DEMAND-GATED, deriving nothing because nothing requires `TypeValue` yet — so the cost currently reads ZERO and the regression is invisible. Proposal 065 step 3 (WI-20260919-N31XX) makes a `requires TypeValue` appear at every rigid value read, at which point all 168 rows are derived and the full +113ms returns, worsened by (1). The gate DEFERS the cost; it does not remove it. Landing this before step 3 is what keeps that cost from ever shipping.

NOT IN SCOPE: making `type_value_derive` derive fewer rows. That was considered and rejected — the demand cannot be narrowed before the typer (the typer resolves `requires` against the relation, so the pass must precede it), and step 3 widens the demand to most sorts anyway. The lever is cost-per-row, not row count.

ACCEPTANCE: the quadratic shape of `derive_forwarded_provisions` demonstrated and then shown linear, by measurement at two relation sizes rather than by inspection; a load-timing comparison showing the HXGXF delta materially reduced when its gate is forced open (flip `any_requirement_names_spec` to `true` to get the 387-provision world without step 3); full workspace green via rustland/scripts/test.sh.

REF: rustland/anthill-core/src/kb/typing.rs (`derive_forwarded_provisions`, `build_provides_index`, `total_composites`' memo comment); rustland/anthill-core/src/kb/type_value_derive.rs (the gate and its measurement); commit 6f7487ae.

## Changes

### 2026-09-20T13:57:04Z — feedback — user

DELIVERED. Three readers fixed; all measured, both arms interleaved, medians reported.

(1) THE QUADRATIC, FOUND AND REMOVED. It was NOT the pending-dedup scan (that short-circuits on carrier+target before comparing bindings). It was `conditioned_provision_pairs`, whose doc already claimed 'ONE sweep of the condition facts' and in fact called `provision_conditions` once PER CARRIER, each call walking the whole ProvidesConditionInfo relation: carriers x conditions, and HXGXF grows BOTH (it asserts a condition row per parametric sort as well as a provision row per sort). Rewritten as one real sweep.

SHAPE DEMONSTRATED AT FOUR SIZES, not two, with a generated fixture whose carriers and conditions grow together; two release binaries (parent commit vs this one) run interleaved, medians of 5, timed at the derive_forwarded_provisions mark:
  n        50     100     200     400     x8 input   last doubling   exponent
  before  3.26    7.83   23.96   82.06ms    x25.2        x3.43         1.78
  after   0.59    0.80    1.42    2.77ms     x4.7        x1.95         0.96
Before climbs toward the x4 of a quadratic as the base cost washes out; after climbs toward x2. 30x faster at n=400.

(2) THE 'READERS SCAN THE RELATION' HALF, two more instances of the same class:
  * `provision_conditions` had no bucket at all — ~877 calls per stdlib load, each a full relation walk. Given one: `ProvidesIndex::conditions_by_carrier`. It lives INSIDE ProvidesIndex deliberately, because its validity window is provides_index's EXACTLY — every ProvidesConditionInfo fact is written beside the SortProvidesInfo fact it conditions, by the loader or by eq_derive — so every existing drop site drops it and there is no fourth set of producers to audit (cf. WI-1112).
  * `region_sorts` sat inside `check_operation_bodies`, which runs once per SORT, under a comment saying it was computed once per typing pass. 204 full provision walks per load. Hoisted to the caller; a debug_assert recomputes and compares at every call site, so the loop-invariance the hoist rests on is checked by every debug test run rather than asserted in prose.

HXGXF DELTA (gate forced open, stdlib + empty namespace, medians of 15 interleaved, one binary with both arms behind a switch):
  TOTAL                    +9.88 -> +3.91 ms   (60% of the regression gone)
  type_check_sorts         +3.37 -> +1.70
  check_provider_requires  +1.91 -> +0.65
  derive_forwarded_provs   +1.53 -> +0.11      (93%)
The residue is real per-row work: the deriving pass itself (+0.62) and eq_derive::run (+0.52).

TODAY'S LOADS GET FASTER TOO, not just the future one: gate CLOSED, HEAD vs this commit, two binaries interleaved, type_check_sorts 18.75 -> 16.38 ms, check_provider_requires 6.18 -> 5.73, derive_forwarded 0.48 -> 0.25.

TESTS — four, in typing/tests.rs, each with its control VERIFIED by mutation rather than asserted:
  * the_condition_bucket_answers_exactly_what_the_scan_answers (whole-KB equivalence)
  * the_condition_sweep_finds_every_conditioned_pair_and_only_those (positive + negative; fails if the sweep keeps one pair per carrier)
  * a_denoted_condition_fact_is_bucketed_not_dropped (fails iff the builder reads the head term-only)
  * the_unconditional_carrier_gains_its_derived_lower_floor (says the deriver still derives, so the negatives mean something)

TWO CLAIMS I WROTE AND THEN MEASURED FALSE, corrected in the comments so nobody re-derives them: (a) that eq_derive's derived condition rows are value-facts needing a carrier-agnostic read — they are term-carried, and a term-only builder passes the whole suite; the real distinguishing shape is a denoted-bearing condition, which is why that test builds one by hand. (b) that canonical keying / sort_ref_functor are distinguished by the corpus — neither mutation fails any test; they are faithfulness-to-the-consumer choices and are now labelled as such.

/code-review raised the triplicated condition-row decode (builder + sweep + predicate). Fixed inline, not deferred: one `decoded_condition_row` now serves all three, so a bucket cannot file facts under a key its reader never looks up.

ACCEPTANCE: rustland/scripts/test.sh 7211 passed / 0 failed (run twice — before and after the review fix). scaland `sbt testFull` 613 passed / 0 failed; the first scaland run exited 0 having run NOTHING (stale-server disconnect, the trap CLAUDE.md documents) and was re-run after a clean shutdown.

