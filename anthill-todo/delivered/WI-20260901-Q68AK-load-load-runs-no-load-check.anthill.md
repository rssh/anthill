## Attributes

- id: WI-20260901-Q68AK-load-load-runs-no-load-check
- created: 2026-09-01T08:05:19Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-01T11:48:28Z

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

## Changes

### 2026-09-01T08:24:53Z — feedback — user

REACHABILITY VERIFIED, and it is STRONGER than the ticket says: there are ZERO production callers of `load::load` in the workspace, not one. Every call site is a test.

  rustland/anthill-core   89 (tests/include/*, tests/common/mod.rs, src/kb/typing/tests.rs)
  rustland/anthill-stl     1 (reflect/bridge.rs:1145 — inside `#[cfg(test)] mod tests`,
                             opened at bridge.rs:1134, so it is a test despite living
                             under src/)

Nothing in `anthill-cli`, `anthill-todo`, `anthill-stl`'s runtime, or `anthill-core`'s own
non-test code calls it. Checked by grepping `load::load(` across `rustland/` and reading
the enclosing item for the one `src/` hit.

WHAT THAT DOES AND DOES NOT SETTLE. It removes the "a live embedder depends on the current
behaviour" objection to (a) and (c), which is the objection that would have made this
expensive. It does NOT make (c) a rename: the function is `pub` in a library crate, so
demoting it to `pub(crate)` is a breaking API change AND is blocked in-tree by the
`anthill-stl` test, which is in a different crate and so needs the `pub`. Converting that
one caller to `load_all` is not mechanical either — several of the 89 use this entry point
PRECISELY because it runs no checks (`wi966_loader_verdict_test` is about the loader's
verdict), so a blanket swap would change what those tests measure.

So the practical shape is: (b) is nearly done already — the rollback and the full trade are
in `LoadCheckMarks`, and what remains is one honest sentence on `pub fn load`'s own doc.
(a) and (c) are both now affordable, and the 89 callers are the real cost centre for
either, not the API surface.

### 2026-09-01T08:55:54Z — feedback — user

DECIDED BY THE USER (2026-09-01): REMOVE `load`. Not rename, not contract — the API should not carry two single-file loaders, and "make it right" means one loading pipeline.

BLOCKED ON WI-20260901-7ZZ1Z. Removing `load` today would delete the sole detector of a live bug: `typing_test::conditional_spec_field_rejects_eq_list_of_non_eq_elements` catches a WI-274 violation ONLY because it loads through the partial loader and drives `type_check_sorts` by hand. Through `load_all` the same program loads clean. Settle that verdict first.

THE REMOVAL COST, MEASURED. All ~90 `load::load(kb, parsed, r)` call sites were mechanically rewritten to `load_all(kb, &[parsed], r)`. It COMPILES CLEAN. The suite goes 6251/0 -> 6200 passed / 51 failed. Classified by panic reason, all 51:

    48   `load_all` REPORTED an error `load` did not — it is STRICTER. These tests
         load a deliberately ill-typed source, expect the load to SUCCEED, then call
         `type_check_sorts` themselves and assert the diagnostic. Migration is
         mechanical: assert the load `Err` instead. 34 are in `typing_test`, 6 in
         `wi946_belongs_to_readers_test` (via `common::load_stdlib_kb_with_source`),
         4 in `parse_test` (of 64 — the other 60 pass unchanged).
     1   `kb::typing::tests::wi1112_requires_index_tests::a_single_file_load_does_not_read_a_stale_index`
         — its SUBJECT is `load`'s own path (WI-1112 fixed a stale-index bug there).
         It retires with the function; nothing to migrate.
     1   `wi_v25n3_written_row_label_test::a_check_less_load_entry_point_records_no_load_check_work`
         — EA6KS's own fixture, asserting `load` reports nothing. Retires too, and
         `LoadCheckMarks` + `restore_load_check_marks` go with it: they exist ONLY to
         roll back what this entry point leaves behind.
     1   `typing_test::conditional_spec_field_rejects_eq_list_of_non_eq_elements`
         — the REVERSE direction, and the blocker above.

WHAT ELSE THE REMOVAL SHOULD TAKE WITH IT. `load` is a hand-maintained COPY of `load_phase_inner`'s prologue, not a delegation — it re-spells register_sources / scan_definitions_with_sources / resolve_builtins / declare_file_field_types / load_with_visited / resolve_instantiations for one file. Every invariant the real pipeline maintains has had to be re-established in the copy by hand, each discovered by a bug: WI-967 (bootstrap panic), WI-1112 (stale requires index), and EA6KS's two registries. Deleting the copy is the point of the exercise; deleting only the `pub` name would leave it.

SEPARATE, AND ALSO THE USER'S CALL (2026-09-01): the API carries THREE PUBLIC NAMES FOR ONE FUNCTION. `load_stdlib` (51 call sites) and `load_incremental` (19) have identical signatures to `load_all` (228) and bodies that are a single delegating call to it — WI-967 removed the last behavioural difference and left the names. Collapsing them into `load_all` is 70 mechanical renames with zero behaviour change. `load_all_per_file` (3 sites) stays: its return type is genuinely different. End state: ONE checked loader, its per-file variant, and nothing else.

### 2026-09-01T10:00:40Z — feedback — user

UNBLOCKED (2026-09-01). WI-20260901-7ZZ1Z is delivered, and its answer removes the block entirely: there was no live bug for `load::load` to be the sole detector of. That test was detecting its OWN fixture — its "non-equatable" element sort was an entity with one `Int64` field, which `eq_derive::derive_total_eq` correctly derives `Eq` for, and it read as non-equatable only because `load` skips the derivation. Both halves of the pair now run through `load_all` and the element is made non-equatable by a `Float` field instead of by its name.

SO THE MIGRATION SHRINKS. Of the 51 failures measured for the swap, the single REVERSE-direction one is gone: that was `conditional_spec_field_rejects_eq_list_of_non_eq_elements`, and it now passes through `load_all` on its own. What remains is 48 mechanical migrations (tests that load a deliberately ill-typed source, expect the load to SUCCEED, then drive `type_check_sorts` themselves — rewrite each to assert the load `Err`) plus two tests whose subject IS `load` and which retire with it (`wi1112…a_single_file_load_does_not_read_a_stale_index` and EA6KS's `a_check_less_load_entry_point_records_no_load_check_work`, taking `LoadCheckMarks` and `restore_load_check_marks` with them).

RE-MEASURE THE 51 BEFORE STARTING: that count was taken before the WI-274 repair landed, so the mechanical rewrite of `load::load(kb, p, r)` to `load_all(kb, &[p], r)` should be re-run and re-classified rather than trusted from here.

### 2026-09-01T11:48:04Z — feedback — user

DELIVERED as `LoadOptions`, not as a plain deletion — the USER's design (2026-09-01), and it is better than removal alone.

WHAT SHIPPED. `pub fn load` is gone, and with it `load_stdlib` and `load_incremental` (one-line delegations to `load_all` since WI-967). The partial shape it provided is now `load_all_with(kb, files, resolver, LoadOptions { run_typer: false })` on the ONE pipeline. Public loading API: `load_all` (defaults), `load_all_with` (explicit options), `load_all_per_file` (same pipeline, per-file results) — five names for three behaviours became three functions for three behaviours, and 20 call sites now SAY at the point of use that they take the partial path, where `load`'s partialness was visible nowhere.

THE OPTION IS STRICTLY BETTER THAN THE FUNCTION IT REPLACED, and this is the part worth keeping. `run_typer: false` stops immediately BEFORE `type_check_sorts`, so everything the typer reads is already built — the sort-ops table, the provider/requires indexes, `derive_forwarded_provisions`, `eq_derive::derive_total_eq`. A hand-driven `type_check_sorts` therefore sees exactly the KB the pipeline's own call would. `load` stopped far earlier (right after `resolve_instantiations`), and that gap is precisely what let WI-20260901-7ZZ1Z ship: a test asserting a refusal that held only because the equality derivation had not run. The new stop point cannot produce that class of disagreement.

MIGRATION, re-measured after 7ZZ1Z landed rather than trusted from the earlier count: 50 failures, not 51. 27 were the exact `load_with_result` + hand-driven `type_check_sorts` pair and moved mechanically to reading the load's verdict. 4 drive the typer themselves because their subject is the TYPED `TypeError` (entity/field SYMBOLS, a resolvable span) which the load boundary flattens to strings — those take `run_typer: false`. 9 more load fixtures that are incomplete for the passes above the loader, same option, applied ONE TEST AT A TIME. The two tests whose subject WAS `load` did not retire: `wi1112_requires_index_tests` and EA6KS's `a_check_less_load_entry_point_records_no_load_check_work` both repoint to the partial option, which is the shape they were always about. `LoadCheckMarks` survives for the same reason — the partial path still writes two registries only a check reads.

/code-review FOUND SEVEN, ALL REAL, ALL FIXED:
  1. `load_all_with(` does NOT contain `load_all(`, so WI-966's discard recogniser could not see the new entry point — the guard covered LESS than before. Literal added, plus a corpus row.
  2. The `*_untyped` helpers returned `LoadResult::default()` on error, so `defined_sorts` was `[]`, the caller's `type_check_sorts` checked NOTHING, and every downstream `is_empty()` assertion passed VACUOUSLY over a KB that never loaded — WI-966's own class wearing a returned-verdict disguise. Both helpers now `expect` the partial load; the suite passing is what says those fixtures really do load clean up to the typer.
  3. `restore_load_check_marks`'s doc claimed the registry cannot shrink because `load_phase_inner` "does NOT capture these marks" — true when the capturer was `load`, FALSE once `load_phase_inner` became the capturer. Rewritten to state the real guarantee (the partial return sits ABOVE the drain) and what breaks if a drain is hoisted.
  4. Eight doc sites still named the removed functions, three as broken intra-doc links and two as load-bearing arguments citing a sibling that no longer exists. Fixed; 57 prose mentions of `load_incremental` renamed.
  5. `load_with_result` now types inside the load, so two tests' "first pass" comments described a pass that no longer happens there. Corrected rather than left to mislead.
  6. My blanket rename had renamed three LOCAL `fn load_stdlib()` test helpers to `load_all()`. Restored.
  7. Formatting from my own scripted edits. Fixed — and note `rustfmt` on the 38 touched files inflated the diff by ~480 lines of UNRELATED reformatting (the tree is not rustfmt-clean), so two files were reverted and hand-edited instead.

RESULT: rustland 6251 passed / 0 failed, count unchanged; scaland 524 / 0.

