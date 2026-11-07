## Attributes

- id: WI-20260901-BGKWA-two-clauses-of-the-same-kind
- created: 2026-09-01T08:06:11Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-07T05:16:13Z

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

## Changes

### 2026-11-07T05:16:11Z — feedback — claude

DELIVERED. Measured on 0d0dacde first: both shapes still reported once, and so did seven more of the same axis — two provisions of one spec at two bindings, two requirements likewise, `requires A: Spec[…]` beside `requires B: Spec[…]` (one fact, two requirements), two conditions of one provision, one condition under two provisions of one spec, two `requires` lines of an operation, two goals of one `ensures` list: the origin named a clause by owner, keyword and the spec's base. The origin now writes the clause: the spec at its bindings (`spec_display_text`, the display twin of `qualified_spec_text`, operation bindings left out), a condition with the provision it conditions (`CD provides SA[C = String] :- Spec[E = {BeepD}]`), each goal of an operation's list on its own with its binder (`askD`'s `requires b: Spec[E = {BeepE}]`, read through `op_requires_entries_of`), and a sort requirement once per name its lines gave it (`collect_sort_requires`). Two clauses that still read the same each say which in parentheses: a goal by its place (goal 2 of the list), a condition by its provision's `clause` index, a provision or requirement by its qualified text (`Spec[C = a.P]` beside `Spec[C = b.P]`). The text is rendered only for a refused binding: judged first, named after. From /code-review (xhigh, 9 findings, 8 fixed): a positionally written row in an operation's contract (`requires Spec[Int64, {BeepE}]`) was never judged — it loaded clean where its named twin is refused; it is paired with the declared parameters by the typer's `op_requires_application_bindings` and written as written. Not changed, by the language: a binding written through an alias beside its written-out twin (`C = I64` beside `C = Int64`) states one provision and is refused once; writing the alias by name made the count follow the carrier (2 on the plain, which holds two facts, 1 on the node). Fixture `two_clauses_of_one_kind_on_one_owner_are_each_reported` (14 rows, the third axis, beside `two_clause_kinds_…`); each of eight parts backed out alone fails its rows, all together all 14; RSRP5's slot test passes under each; the three tests that asserted the old wording updated. Full workspace 11,751 passed, 0 failed; families green; the fixture and every probe identical under the node carrier; no Scala file changed (scaland has no typer).

