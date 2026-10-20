## Attributes

- id: WI-20261020-G37HS-the-typer-s-refinement-through
- created: 2026-10-20T07:56:48Z

- status: Open
- status_agent: user
- status_at: 2026-10-20T07:56:48Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

THE TYPER'S REFINEMENT THROUGH `requires` IGNORES THE CLAUSE'S ARGUMENTS. MEASURED on 663ac457, the same on 098ce8a9: `sort Wide { sort W = ? }`, `sort Narrow { requires Wide[W = Int64]  entity narrow }`, `sort WP { provides Wide[W = Int64] }`, `operation takeInt(x: Wide[W = Int64]) -> Int64 = 1`, `operation takeStr(x: Wide[W = String]) -> Int64 = 2`: `takeInt(narrow()) + 10 * takeStr(narrow())` loads and answers 21 — a `narrow()` accepted where a `Wide[W = String]` is expected. `sort_sym_compatible` → `sort_refines` → `transitive_required_sorts` compares heads only. Since SQZPQ the run-time test reads the clause — `type_admits(Wide[W = String], Narrow)` answers no, each instance the clauses give the refining sort (`instances_through_requires`, kb/typing/type_pattern.rs; user, 2026-10-20) — so the typer and the run time disagree, and stage (e) (WI-20261016-BDVYW) makes the typer's discharge of an `Error` label read that test. FIX DIRECTION: the typer's subsumption of a refining sort under an applied type reads the instances its `requires` clauses give it, its own arguments put for the parameters a clause names, as `type_admits` does — one reader for both where it can be shared. ACCEPTANCE: `takeStr(narrow())` refused at load; `takeInt(narrow())` and every refinement whose target writes no argument unchanged; a parametric clause (`sort Narrow2 { sort Q = ?  requires Wide[W = Q] }`) accepts `Narrow2[Q = String]` at `Wide[W = String]` and refuses it at `Wide[W = Int64]`; families green; full gate green.

