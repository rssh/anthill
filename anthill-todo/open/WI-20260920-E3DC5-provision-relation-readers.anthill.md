## Attributes

- id: WI-20260920-E3DC5-provision-relation-readers
- created: 2026-09-20T09:35:32Z

- status: Open
- status_agent: claude
- status_at: 2026-09-20T09:35:32Z

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

