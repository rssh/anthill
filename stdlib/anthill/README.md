# Anthill standard library

`.anthill` sources for the standard library: `prelude/` (primitives,
collections, algebra, effects), `geometry.anthill`, `reflect/`,
`realization/`, `persistence/`. They are loaded by every `anthill` invocation
(embedded via `anthill::stdlib`).

This README documents one cross-cutting feature that the stdlib and example
specs rely on but that has no `.anthill` source of its own: the **proof-tactic
catalog** used inside `proof <rule> by z3(...)` blocks. The canonical design
reference is [`docs/proposals/025.1-z3-tactic-dsl.md`](../../docs/proposals/025.1-z3-tactic-dsl.md);
this is the user-facing summary with worked examples that actually discharge in
the tree.

## Proof tactic catalog

A `proof` block discharges a rule (its body read as a proof obligation) through
Z3. The strategy is written as a `tactic:` value inside `by z3(...)`. Tactics
are a **closed catalog** (an unknown tactic name is a load error, not a silent
no-op). All tactics are **sound**: success means `proved`, never bug-finder
"no counterexample found yet".

```
by z3( [tactic: <tactic>,] [logic: "<LOGIC>",] [timeout: <ms>,]
       [model: true,] [cores: true] )
```

`logic` / `timeout` / `model` / `cores` are the outcome/solver knobs (passed
through to Z3). When `tactic:` is omitted it defaults to `smt`.

### `smt` — single satisfiability check (default)

```anthill
-- explicit
proof lower_violation by z3(tactic: smt(logic: "LRA")) end
-- shorthand: tactic defaults to smt
proof lower_violation by z3(logic: "LRA") end
```

Worked example: `examples/webots-modelling/lf1/safety_gps.anthill` —
`lower_violation`, `upper_violation` (`by z3(logic: "LRA")`),
`safety_min_distance` / `safety_max_distance` (`by z3(logic: "QF_NRA")`).

### `ranking` — bounded excursion via a well-founded measure

Discharges a *bounded-excursion* obligation by combining two sub-queries you
supply as violation rules: **boundedness** (no reachable state drives the
measure below 0) and **decrease** (every "bad step" strictly decreases it).
Both `unsat` ⇒ proved; either `sat` ⇒ disproved; either `unknown` ⇒ unknown.

```anthill
-- the two obligations, written as ordinary rules:
rule bound_violation_transponder(?w)
  :- gte(?upc, -6), lte(?upc, 0), gt(?upc, 0), ?w = ?upc
rule decrease_violation_transponder(?w)
  :- gte(?upc, -6), lt(?upc, 0), ?upc_next = ?upc + 1, lte(?upc_next, ?upc), ?w = ?upc

proof post_armed_excursion_bound
  by z3(tactic: ranking(boundedness: bound_violation_transponder,
                        decrease:     decrease_violation_transponder),
        logic: "LIA")
end
```

Worked example: `examples/webots-modelling/lf1/safety_transponder.anthill`
(`post_armed_excursion_bound`, measure R = −upc over the post-armed regime
upc ∈ [−6, 0]). This replaced a hand-written smt-gen worked example that
previously lived in `anthill-smt-gen/tests/lf1_real_spec_test.rs`.

> Each sub-query goes through the standard SMT path independently, so the proof
> cache and outcome flags compose with no special-casing. The minimum-viable
> form takes two pre-written violation rules; deriving the queries from a bare
> `measure:` function and emitting a `RankingProof` witness fact (with a
> `pessimistic_bound: N` argument) is a later increment — see the proposal.

### `induction` — case-split into per-case sub-queries

Emits one SMT sub-query per case and combines verdicts (all cases proved ⇒
proved). Cases are given either as named `base:` / `step:` (binary induction
over `Int64`/`Bool`/single-recursive enums) or as a positional list of case
rules; `over:` optionally names the sort being inducted over.

```anthill
proof reachability_band
  by z3(tactic: induction(base_lower_violation,
                          base_upper_violation,
                          lower_violation,
                          upper_violation),
        logic: "LRA")
end
```

Worked example: `examples/webots-modelling/lf1/safety_gps.anthill`
(`reachability_band` — the ∀k band invariant via four case rules).

### Combinators — `then`, `or_else`, `repeat`, `par`

Pass-through to Z3's own tactic combinators, surfaced verbatim:

```anthill
proof step_distance_bound
  by z3(tactic: or_else(smt(logic: "LRA"),    -- try cheap LRA first
                        smt(logic: "NRA")))   -- fall back to nonlinear
end
```

### `raw(...)` — escape hatch

`raw("...")` splices a Z3 tactic expression verbatim into `(check-sat-using ...)`
for incantations the catalog does not cover:

```anthill
proof some_obligation
  by z3(tactic: raw("(then simplify (using-params smt :random_seed 42))"))
end
```

## Running proofs + the cache

`examples/webots-modelling/lf1/discharge.sh` runs every `proof … by z3` block in
that directory through `anthill prove`; see its header for the cache flags
(`--show-cache`, `--stats`, the warm-cache CI pattern, etc.). The same flags
work on any `anthill prove <dir>` invocation. Z3 must be on `$PATH`; without it,
obligations report `skipped` rather than `failed`.
