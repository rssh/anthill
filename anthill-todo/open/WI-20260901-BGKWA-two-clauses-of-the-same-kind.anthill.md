## Attributes

- id: WI-20260901-BGKWA-two-clauses-of-the-same-kind
- created: 2026-09-01T08:06:11Z

- status: Open
- status_agent: user
- status_at: 2026-09-01T08:06:11Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TWO CLAUSES OF THE SAME KIND ON ONE OWNER COLLAPSE TO ONE ROW-LABEL REFUSAL, so an author fixes one, reloads, and meets the other — WI-20260831-V25N3's own dedup defect, recurring one level down.

Found by /code-review while reviewing WI-20260901-EA6KS. `typing::check_written_row_bindings` (rustland/anthill-core/src/kb/typing.rs) dedups its refusals on `(origin, span, spec, param, label)`, and V25N3's doc says that key is "exactly as fine as the message". It is — and that is the problem: for two clauses of the SAME kind on one owner the message itself does not distinguish them, so the key cannot either.

MEASURED, both halves, throwaway probes since removed:

  * TWO PROVISION CONDITIONS. `sort CD` with `provides SA[C = String] :- Spec[E = {BeepD}]` beside `provides SB[C = String] :- Spec[E = {BeepD}]` reports ONE refusal. Both `ProvidesConditionInfo` facts render origin "`CD <keyword> Spec`" — the CONDITION's spec, never the provision it conditions — so the two are indistinguishable. Note this is exactly what `ProvidesConditionInfo.clause` (the per-clause index, WI-1033) exists to separate, and the origin ignores it.
  * TWO ITEMS OF ONE OPERATION'S CLAUSE LIST. `operation askD(p: String) -> Out requires Spec[E = {BeepE}], b: Spec[E = {BeepE}]` reports ONE. Origin is "`askD`'s `requires` clause" for both.

THE OBVIOUS REPAIR IS WRONG, AND THAT IS WORTH THE TICKET. /code-review proposed adding the `SpecClauseView.rid` / `OperationInfo` rid to the key, noting it is "already in hand and would cost nothing". MEASURED against the two cases above, it fixes NEITHER properly:

  * The op-clause-list case has ONE `OperationInfo` fact carrying BOTH items (the claim is per-FACT, deliberately — see the source-3 loop's own comment), so the rid is IDENTICAL for the two items and the key does not move at all.
  * The two-conditions case does have two rids, so it would report twice — but the two messages are BYTE-IDENTICAL, since neither names its provision. The author would see the same paragraph twice with no way to tell which clause each is about. That is duplication, not a diagnosis.

SO THE FIX IS IN THE ORIGIN, NOT THE KEY. The key is downstream of the message and cannot be finer than it. What each half needs:

  * A condition should name the provision it conditions — the `provided` field is on the very fact `all_spec_clause_views` already reads, and the `clause` index beside it. `all_spec_clause_views` currently reads only `sort_ref` plus the kind's one spec field, so it would grow a per-kind extra.
  * An op clause item should name WHICH item — its binder when it has one (`b:`), else its position in the list. `all_operation_contract_clauses` already yields the items in order.

DECIDE THE PROSE, because that is the real work: "`CD provides SA` condition `Spec`" versus something that reads. Whatever is chosen, both spellings appear in a user-facing load error and should read the way the SITE-sourced refusals beside them do.

THE FIXTURE THAT ALREADY EXISTS is `two_clause_kinds_on_one_owner_are_each_reported` (wi_v25n3_written_row_label_test.rs), which pins the axis one level up — a `provides` beside a `requires`, and an op's `requires` beside its `ensures`. This ticket is the SAME axis within one kind, and its fixture belongs beside that one so the two read as a pair.

ACCEPTANCE: each of the two measured shapes reports TWICE, with the two messages differing in the text that says which clause is meant — not merely repeated. The existing `two_clause_kinds_…` test and RSRP5's `each_bad_row_parameter_is_reported_against_its_own_slot` (the third axis, two SLOTS of one clause) both stay green, and the new fixture states which of the three axes it is. Regression: nothing in the workspace suite changes verdict.

