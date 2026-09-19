## Attributes

- id: WI-20260919-N31XX-proposal-065-step-3-the-load
- created: 2026-09-19T15:19:37Z

- status: Open
- status_agent: user
- status_at: 2026-09-19T15:19:37Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260919-BQHGD-proposal-065-step-1-census-of, WI-20260919-HXGXF-proposal-065-step-2-derive

- tags: typing

## Description

PROPOSAL 065 STEP 3 — THE LOAD RULE AND THE LOWERING: a rigid type read as a value is well-formed only under `requires TypeValue[T = B]`, and it lowers to that slot's `type_value()`. The existing reads are migrated IN THE SAME CHANGE.

THE RULE (065, "The rule"; amends 055 §2's type-parameter bullet). A rigid read in value position with no `requires TypeValue[T = B]` among the requirements in scope is a LOAD error naming the parameter, the read's line and column, and the clause to add. Such a read is a bare `B`, a `B` inside a type expression (`Cell[V = B]`), or a `Type`-slot argument. EXPLICIT, not inferred (user decision, 2026-09-19). Untouched: type positions, concrete sorts, and rule bodies.

THE LOWERING (065 §1). The read becomes `TypeValue[T = B].type_value()` dispatched through the slot, using the ordinary `DeferToRequirement` route. The argument pump already builds `Cell[V = <computed>]`; only the leaf changes. After this, value reads no longer consult the frame type-argument channel. `Error.reify`'s `T1` still does (065 open question 2; 3MV2C decides), so the channel stays and this ticket says at its site why.

THE OVERRIDE SUBSET (065 §3). An implementation's OPERATION-level requires must be a subset of its spec operation's, and a direct call to the member does not relax it. Clauses over the provider's own sort parameters ride on the instance and are allowed. If step 1's probe found this already refused, record which leg enforces it and add a `TypeValue` row. If it loaded, add the leg to `check_override_refinement`.

MIGRATION: every site in step 1's census, in this change, so the suite never passes through a state where the rule is on and a read is unmigrated. That includes the WI-708 rows, the RS2G4 rows (a SORT parameter, so the sort gains `requires TypeValue[T = T]`) and R541X's file. R541X's (D) run-time fault stays as a backstop; say at its site that it is now unreachable from checked source.

ACCEPTANCE:
 - the load refusal DRIVEN with its message;
 - its control: the same program with the clause loads AND answers the ground type through one and two generic levels;
 - the override-subset refusal, and the instance-context control that loads;
 - every migrated row still answering what it answered before.
Each row names the back-out that turns it red. `docs/kernel-language.md`: the R541X paragraph is rewritten to the rule, and 055/065's statuses are updated. Full workspace green via rustland/scripts/test.sh.

