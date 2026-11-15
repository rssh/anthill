## Attributes

- id: WI-20261115-GSA4F-the-sld-eval-bridge-builds-a
- created: 2026-11-15T20:14:43Z

- status: Open
- status_agent: claude
- status_at: 2026-11-15T20:14:43Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE SLD→EVAL BRIDGE BUILDS A NEW INTERPRETER FOR EVERY OPERATION CALL A RULE BODY MAKES, so a call from a rule costs an interpreter's construction where a goal costs one step. Decided with the user (2026-11-15, on WI-20261115-YR3N7): "spawning new interpreter on each operation is a design flaw"; "The fill call should have the same cost as goal (not only fill - operation flow)". Re-engineer it.

WHERE. `KnowledgeBase::run_in_bridge_interp` (`kb/resolve.rs`, the "shared core of the SLD→eval bridge (WI-625)") does, for EVERY bridged evaluation:
  1 `std::mem::take` of the whole KB, lent to the new interpreter and handed back after (`into_kb`);
  2 `Interpreter::with_config` (`eval/mod.rs`): `ReflectSymbols`, `ErrorLayer` and `FieldSymbols` resolved again; six arenas made fresh (closures, streams, substitutions, maps, layers, cells); an empty effect registry; and EMPTY `op_body_cache` and `const_cache`, so every call lowers its operation bodies and forces its consts again;
  3 `register_standard_builtins`: every host operation and const mapping registered into the fresh interpreter's map — the operation list memoized on the KB since WI-880, the registration not; the const list rebuilt each time (`register_const_mappings`);
  4 the call, then `release_layers_for_handback`, then the KB handed back.
Its callers: a rule-body operation call (`bridge_op_to_eval`); an expression form in a rule body (`bridge_form_to_eval`); the bodied `eq` of a semantic compare; an operation unfolding's dictionary frame (`fill_sort_half` — operation unfolding, unrelated to `Fillable`); a const forced from resolution (`kb/const_value.rs`); the `@[simp]` macro hook (`kb/simp_rewrite.rs`). YR3N7's example pays it once per query (`?s <=> st()`); a rule that calls an operation for each element of a list pays it per element.

WHY IT IS SO (the site's own comments): the interpreter OWNS its KB, so the KB is lent by `mem::take`; the builtins are re-registered because they cannot persist across calls ("the simple-correct choice"); the fresh effect registry and arenas ISOLATE a bridged run from what the resolver sees, so re-running it on a backtrack is idempotent; `BRIDGE_REENTRY_CAP` (8) bounds eval↔SLD re-entry on the native stack, a budget the optimized and unoptimized builds differ in.

NOT THE FILL PATH (read 2026-11-15): `apply_domain` is lowered in `step_init`, and its dictionary reads (`domain_evidence`, `domain_sub_evidence`, `normalize_domain_sub`) evaluate nothing, so a derived fill reaches no bridge. A fill pays the spawn only where its clauses call an operation — a written provision's, or proposal 067 §4's collection builder through `fromList`.

PRINCIPLE (user): a call made from a rule body costs what a goal costs; no interpreter is built for it.

DESIGN FIRST, with the user, then build. What the design owes:
  - who owns the KB: one interpreter per resolution (or per thread) that the resolver re-enters, the KB shared rather than moved;
  - builtins and host mappings registered once (per KB, or per interpreter that lives as long as it), and the op-body and const caches kept across calls;
  - isolation without a fresh interpreter: a per-call scope (arena marks, an effect-registry frame) that a backtrack discards, so a bridged run still cannot change what the resolver sees;
  - the re-entry cap and the native-stack budget it guards (`BRIDGE_REENTRY_CAP`'s measurement, both builds);
  - which callers need an evaluation at all (an unfolding frame, a const force).

ACCEPTANCE (every row driven, measured before and after):
  1 A rule that calls an operation once per element of a list: the cost per call (resolution steps, and wall time on a quiet machine) is a goal's, not an interpreter's construction.
  2 No interpreter is constructed per call — a counter, read by the test.
  3 Isolation holds: a bridged run's effects and arena values are invisible to the resolver after a backtrack, and re-running it gives the same answer.
  4 The re-entry cap's rows hold on both builds; no native stack overflow.
  5 The full workspace green on both builds.
Back-out: the per-call interpreter restored reddens rows 1 and 2.

