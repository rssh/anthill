## Attributes

- id: WI-20260901-EA6KS-loader-judged-row-binding
- created: 2026-09-01T05:38:34Z

- status: Open
- status_agent: user
- status_at: 2026-09-01T05:38:34Z

- acceptance: cargo-test, scaland-sbt-test

## Description

LOADER: `judged_row_binding_clauses` DROPS A LOAD-BLOCKING REFUSAL FOR A RE-PRESENTED FILE, AND IS PLACED IN THE LAYERING TABLE AS IF SCOPED WHILE CLASSIFIED MONOTONE.

Found by /code-review while reviewing WI-20260830-JM7A8; the field is WI-20260831-V25N3's (`rustland/anthill-core/src/kb/mod.rs:1420`, claimed at `typing.rs`'s `check_written_row_bindings` sources 2 and 3). Two coupled halves, one field.

HALF 1 — THE REFUSAL IS LOST. RE-MEASURED INDEPENDENTLY, with its control.

The field's own doc asserts "A RE-PRESENTED FILE IS STILL JUDGED, and must be: `load_incremental` re-scans files already in the KB and banks a SECOND fact for each (WI-1049), with a NEW RuleId". That is FALSE for the two fact sources this claim-set gates. `assert_fact` / `assert_fact_value` return the EXISTING `RuleId` for a structurally identical live fact (`live_dedup_hit`, `mod.rs:464`), and WI-1049's "second fact" observation (`op_info.rs:242`) is scoped to TYPE-PARAMETER-BEARING operations, where `load_operation` mints a `fresh_var` per declared parameter and that is what defeats hash-consing. `SortProvidesInfo` / `SortRequiresInfo` / `ProvidesConditionInfo` heads carry no such fresh var; neither does an `OperationInfo` head for an op declaring no bracket parameters.

MEASURED (throwaway probe, since removed): stdlib + a sort carrying `requires Spec[E = {BeepI}]` (an unregistered kind) through `load_all` reports 1 refusal. Then `load_incremental(&mut kb, [the SAME unchanged file])` returns **Ok, zero errors**.

    first judged=1  second judged=0   second errs: []

CONTROL: with `claim_row_binding_clause` patched to always return `true`, the same probe gives `first judged=1 second judged=1` and the second load carries the full "is not a REGISTERED effect kind" diagnostic. So the claim-set is what suppresses it, not some neighbouring gate.

This is a REGRESSION and it is the "loads clean while breaking a load-blocking rule" class: before V25N3 (`check_provision_row_bindings`, no claim set) the second load reported it.

WHY THE OBVIOUS FIXES ARE NOT ONE-LINERS, and why this is a ticket rather than an inline repair:

  * The question the claim-set WANTS is "did THIS BATCH present this clause", not "has this KB ever judged this RuleId".
  * Gating on the clause's owning FILE is closed off today: V25N3's own note records that these are loader-emitted metadata facts, so `rule_head_span` is empty and `functor_span` keys off an APPLIED name — a fact-sourced refusal carries no span at all. Provenance would have to be ADDED.
  * Un-claiming at `assert_fact`'s dedup-hit path (the two sites at `mod.rs:3599` / `3637`) does express "this batch re-presented this fact", but it needs a census of who ELSE re-asserts these three clause facts every load — `eq_derive::run` asserts `SortProvidesInfo` rows on every load, and un-claiming those would re-report a row in a batch that never presented it, i.e. reintroduce the bug V25N3's claim-set was added to fix.

THE EXISTING TEST ONLY PINS THE OTHER DIRECTION. `a_later_load_does_not_re_report_an_earlier_batchs_clause` presents an UNRELATED file in the second batch and asserts 0. The re-presented direction the doc asserts has no fixture, which is why the false claim shipped. Whatever key this lands on needs BOTH directions asserted in one test.

HALF 2 — THE LAYERING CLASSIFICATION CONTRADICTS ITS OWN SECTION AND ITS CITED PRECEDENT.

`classify_every_field_for_layering` (`kb/layer.rs`) is the structural guard WI-SPGBP built against silent mis-classification. Its SCOPED section header (`layer.rs:301`) reads "every field to the NEXT HEADER is in `kb_scoped_fields!`". `judged_row_binding_clauses` sits INSIDE that block — between `resolved_requires_facts` and `unbacked_derived_provisions`, both of which ARE in `kb_scoped_fields!` — but is bound under a MONOTONE comment and is absent from the macro list. So the section header is now false. The comment further claims it is monotone "for `resolved_requires_facts`' reason", and `resolved_requires_facts` is SCOPED — the precedent says the opposite of what is cited.

The monotone CHOICE looks behaviourally safe today (`tombstone_layer_rules` never reissues a discarded layer's `RuleId`, and `fact_dedup` is rolled back, so a re-checked candidate mints fresh ids). The defect is the PLACEMENT and the wrong precedent: the compile-time check only forces a field to be MENTIONED, never correctly CLASSIFIED, so the next author adding a field after this one reads the header, assumes SCOPED, and omits it from the macro list — exactly the failure that function exists to prevent.

COUPLED ON PURPOSE: half 1's repair may change which classification is correct, so the placement should be settled with it rather than churned twice.

ACCEPTANCE: a file re-presented to `load_incremental` is refused again with the same diagnostic, AND a batch that does not present it still reports nothing — both directions in one test, each named as the other's control. The layering entry sits under a header whose invariant it satisfies, with a reason that does not cite a scoped field as precedent for being monotone. Regression: nothing in the workspace suite changes verdict.

