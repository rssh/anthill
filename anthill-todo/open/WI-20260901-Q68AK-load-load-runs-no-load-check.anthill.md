## Attributes

- id: WI-20260901-Q68AK-load-load-runs-no-load-check
- created: 2026-09-01T08:05:19Z

- status: Open
- status_agent: user
- status_at: 2026-09-01T08:05:19Z

- acceptance: cargo-test, scaland-sbt-test

## Description

`load::load` RUNS NO LOAD CHECK, AND NOW SILENTLY DISCARDS THE ONE PIECE OF CHECK WORK IT USED TO LEAVE BEHIND. Decide whether that entry point should judge its own file or stop existing.

Found by /code-review while reviewing WI-20260901-EA6KS, whose repair is what forced the choice. `pub fn load` (rustland/anthill-core/src/kb/load.rs:11573) is the single-file entry point: it registers the prelude, scans definitions, walks items, runs `resolve_instantiations`, and RETURNS. It never reaches `load_phase_inner`, so none of that function's ~20 load checks run over what it loaded.

WHAT EA6KS CHANGED, and why it is not the whole answer. The item walk writes two registries that ONLY a check reads, and leaving either changed hands the NEXT batch work it did not do:

  * `judged_row_binding_clauses` — EA6KS made the walk DROP claims (`note_metadata_fact_presented`) and only the check re-adds them, so a `load` of an offending file left every clause un-claimed. MEASURED: `load_all(stdlib+spec+bad)` reports 2 row-label refusals, `load(bad)` reports 0, and a following `load_incremental(one unrelated clean sort)` then reports 2 refusals naming a file it was never given. That was EA6KS's OWN regression (backing the drop out takes the last number to 0) and is fixed there.
  * `parameterized_type_sites` — push-only within a load, drained ONCE by `load_phase_inner`, so a `load`'s sites simply waited for the next batch to drain them. MEASURED identically with the drop backed out, so PRE-EXISTING. Fixed beside the other in EA6KS because the alternative was source 1 and source 2 of ONE check answering "what does `load` mean" two different ways.

Both are now rolled back by `KnowledgeBase::restore_load_check_marks` (kb/mod.rs), pinned by `wi_v25n3_written_row_label_test::a_check_less_load_entry_point_records_no_load_check_work`, which asserts both halves with a back-out apiece (clause half 2, site half 1).

THE COST THAT IS NOT PAID, and this ticket owns it. The site rollback DROPS TWO REFUSALS for a file loaded through this entry point — WI-644's use-site `requires Eq` and WI-20260831-V25N3's source-1 written-row-label one. They are not relocated; nothing judges them. That is a silent skip, which this repo's principles disfavour; it was taken because the alternative is that a `load_incremental` of a CLEAN UNRELATED FILE FAILS, which is the outcome V25N3 was filed for and which makes this entry point unusable in exactly the incremental workflow it exists to serve.

THE THIRD OPTION IS THE RIGHT ONE. `load` should run those two checks over its OWN drained sites. It cannot today: `check_use_site_requires_eq` reads `eq_derive`'s derived `NonEq` rows, and this entry point never runs `eq_derive`, so on a Float composite it would answer WRONGLY rather than not at all — a false refusal is worse than a missing one. So the decision is between:

  (a) give `load` the minimum pipeline those two checks need (at least `eq_derive::run` and whatever ordering its own doc requires) and run them;
  (b) declare the entry point check-free BY CONTRACT, say so on `pub fn load`'s doc, and keep the rollback;
  (c) delete it. REACHABILITY SAYS THIS IS CHEAP TO CONSIDER: /code-review found the only non-test reference is `anthill-stl/src/reflect/bridge.rs:1145`, and that one is inside `#[cfg(test)]` — so today this is a test-only API with a `pub` signature. VERIFY THAT BEFORE ACTING; a `pub fn` in a library crate has readers this repo cannot see.

WHICHEVER IS CHOSEN, the doc block on `LoadCheckMarks` (kb/mod.rs) records the current trade in full and cites this ticket as the owner; it must be updated or deleted with the decision, not left pointing at an answered question.

ACCEPTANCE: `pub fn load`'s own doc states what it checks and what it does not, in those words. If (a): a file loaded through `load` that writes `Map[K = Float]` or a bad row label in a signature is REFUSED by `load` itself, with a fixture driving each, and the Float-composite case is asserted to answer the same way it does under `load_all` (the wrong-answer trap above is the thing to pin). If (b) or (c): the two dropped refusals are named on the entry point as a known, contracted gap, and `a_check_less_load_entry_point_records_no_load_check_work` cites the contract rather than just the behaviour. Regression: nothing in the workspace suite changes verdict.

