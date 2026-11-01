## Attributes

- id: WI-20261020-G37HS-the-typer-s-refinement-through
- created: 2026-10-20T07:56:48Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-01T00:42:44Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

THE TYPER'S REFINEMENT THROUGH `requires` IGNORES THE CLAUSE'S ARGUMENTS. MEASURED on 663ac457, the same on 098ce8a9: `sort Wide { sort W = ? }`, `sort Narrow { requires Wide[W = Int64]  entity narrow }`, `sort WP { provides Wide[W = Int64] }`, `operation takeInt(x: Wide[W = Int64]) -> Int64 = 1`, `operation takeStr(x: Wide[W = String]) -> Int64 = 2`: `takeInt(narrow()) + 10 * takeStr(narrow())` loads and answers 21 — a `narrow()` accepted where a `Wide[W = String]` is expected. `sort_sym_compatible` → `sort_refines` → `transitive_required_sorts` compares heads only. Since SQZPQ the run-time test reads the clause — `type_admits(Wide[W = String], Narrow)` answers no, each instance the clauses give the refining sort (`instances_through_requires`, kb/typing/type_pattern.rs; user, 2026-10-20) — so the typer and the run time disagree, and stage (e) (WI-20261016-BDVYW) makes the typer's discharge of an `Error` label read that test. FIX DIRECTION: the typer's subsumption of a refining sort under an applied type reads the instances its `requires` clauses give it, its own arguments put for the parameters a clause names, as `type_admits` does — one reader for both where it can be shared. ACCEPTANCE: `takeStr(narrow())` refused at load; `takeInt(narrow())` and every refinement whose target writes no argument unchanged; a parametric clause (`sort Narrow2 { sort Q = ?  requires Wide[W = Q] }`) accepts `Narrow2[Q = String]` at `Wide[W = String]` and refuses it at `Wide[W = Int64]`; families green; full gate green.

## Changes

### 2026-11-01T00:42:36Z — feedback — claude

DELIVERED (a5720275). Run on the tree first (2026-11-01): the ticket's program loaded and answered 21; Narrow2[Q = String] at Wide[W = String] was REFUSED (the applied arm's binding loop reads only the actual's own arguments or a provision's), so the parametric acceptance was a defect of its own, not only the bare arm's accept. Fix: the typer's subtype relation reads a refinement through instances_through_requires, the reader type_admits uses — the bare arm (bare_nominal_admits_applied, where sort_sym_compatible admitted by name) and the applied arm (parameterized_compatible_view); sort_sym_compatible now says which leg answered (nominal_leg). /code-review found the shared reader had no cycle guard: A requires B, B requires A + Wide[W = Int64] hit the 512 cap, so the typer refused A at Wide[W = Int64] (HEAD admitted it) and type_admits erred — instances_below now enters no sort a path has passed through, as build_requires_tree does not. Rows: rustland/anthill-core/tests/include/wi_g37hs_refinement_reads_clause_test.rs (6; each arm and the path guard backed out alone, per-row table in its header; eight positions — argument, return, let, field, list element, const, rule body, callback parameter, inside an argument — two clauses down, a contravariant parameter, a cycle, and the typer beside type_admits pair by pair). Probed besides: alias-written requires, a Self binding (now admitted, HEAD refused), a variant-typed actual, the node carrier — all as type_admits answers. Traced over the full gate: 76 refinement reads, each one instance, none empty or erring; outside the new rows only dyr6refines and wi461 reach it, the stdlib never. Family g-compatibility: the two G37HS exceptions taken off, six verdicts UNSOUND runs 1 -> not admitted. Full workspace 11,325 passed (node carrier too), families green, scaland 792. Left: inference does not climb a requires clause — takeAt(n) over n: Narrow2[Q = X] is refused 'expected a type for Y, got unconstrained' before and after, while takeAt[X](n) now loads; /code-review (xhigh): 11 findings, 3 fixed, 4 no change (probed), 4 skipped (spec sentence for the user; the inference gap above; a bool relation carrying an unjudged reason; a repeated chain walk, gate time unchanged).

