## Attributes

- id: WI-20261020-NNQ1S-a-carrier-s-own-operation
- created: 2026-10-20T07:56:46Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-21T10:32:07Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A CARRIER'S OWN OPERATION NAMED LIKE A SPEC MEMBER IS DISPATCHED TO, WHETHER OR NOT IT SUPPLIES THE MEMBER. MEASURED on 663ac457, the same on 098ce8a9. `sort P { entity p(x: Int64)  operation neq(a: Int64, b: Int64) -> Bool = true }`, no provision written, `import anthill.prelude.PartialEq.{eq, neq}`: `eq(p(x: 1), p(x: 1))` answers yes and `neq(p(x: 1), p(x: 1))` answers yes — `P.neq`, an operation over two `Int64`s, answered the `neq` of two `P`s, a silent wrong answer. With `operation neq(n: Int64) -> Bool` the call dies at run time, "operation call: expected 1 args, got 2". Writing `provides anthill.prelude.PartialEq[T = P]` changes nothing. THE RULE: `neq` is derived, `rule neq(?a, ?b) <=> not(eq(?a, ?b))` (eq.anthill); "an own `neq` member is never consulted" (kernel-language.md §8.7), and "a member merely named `neq` that does not compare the carrier's own values … supplies nothing and is untouched" — the load check classifies `P.neq(a: Int64, b: Int64)` so, and refuses `neq(a: P, b: P)` (`CarrierSuppliesNeq`), while dispatch takes it. THE ROUTE: a carrier's member is found by short name in the sort-operations table (`sort_ops_lookup(carrier, short)`), read by `carrier_own_op` (call_class.rs, route 1 of `spec_op_suppliers_for_carrier`), by `resolve_op_target` (call_class.rs) and by the typer's `resolve_at_goal` (carrier.rs). SQZPQ special-cased one builtin there (`answered_by_its_dictionary`, for `TypeValue.type_value`). FIX DIRECTION: take a carrier's member only where it is a member of the spec at that carrier — the criterion the loader applies (`member_operands_are_the_carrier`, load.rs) — at every reader, retiring the special case where it is covered. ACCEPTANCE: with the own `neq` present, written provision or not, `neq(p(x: 1), p(x: 1))` answers no (the derived `neq`) and the one-argument variant runs; `P.neq(3, 3)` still calls the own operation; a row per reader, back-outs measured; full gate green.

## Changes

### 2026-10-26T07:09:30Z — feedback — claude

Measured with WI-20261025-TSYS6 (user, 2026-10-25: the type's own `eq` decides `=`, identical operands included, unless the type provides `Eq`): a type with its own `eq` and NO provision — this ticket's shape — is keyed in the equality index and provides no `Eq`, so its `eq` now decides identical operands too: `sort Pq { entity pq(v: Int64)  operation eq(x: Pq, y: Pq) -> Bool = false }`, `PartialEq.eq(pq(v: 1), pq(v: 1))` 1 -> 0. Whether such an undeclared `eq` is dispatched to at all is still this ticket's question; the answer it gets when it is dispatched is TSYS6's.

### 2026-11-21T06:15:03Z — feedback — user

DECIDED WITH THE USER (2026-11-21): reading (A) of WI-20260930-FB53M, done here together with it. A carrier's member of a spec operation's short name supplies that operation only where it fits the spec operation at that carrier; one owner decides it and every dispatch reader reads it, and a member that does not fit is a distinct operation, so the default (or the derived neq) runs. To be recorded in kernel-language.md, for the user's approval.

### 2026-11-21T10:27:54Z — feedback — user

IMPLEMENTED (with WI-20260930-FB53M, decision (A), 2026-11-21; not committed yet). MEASURED FIRST on 7d609b66: neq(p(x: 1), p(x: 1)) over P.neq(a: Int64, b: Int64) answered true; one-parameter Q.neq died 'expected 1 args, got 2'; FB53M's Car.peek(s: Car) died the same way, Car2 (returns String) died adding, Car3 (k: String) answered 9. FIX: typing::record_members_that_supply_nothing (run after each build_sort_ops_table) decides, for every carrier member whose short name a spec operation with an implementation of its own (a body, a builtin) shares, whether it fits — compare_member_signature (check_member_signature split at its gate), at each provision dispatching to the carrier (its own, a witness's that names it), or at the carrier itself where none does (equality is asked of any type: read as 'supplies nothing' there, six rows fail); filed on SortOpsTable.supplies_nothing; carrier_own_op, which every reader goes through, and resolve_op_target_at's inherited row pass a member that does not fit. A pair a seal holds keeps its verdict (17 ms of each later load otherwise, release build). An eq that does not fit PartialEq.eq beside a provision is refused (check_override_refinement): it holds the derived eq's name, and the provision had no member (EqualityWithNoMember at run time). THE GAP (user: fix it too): a spec call typed by the spec's own signature read a provision's effect row resting on the caller's rigid row parameter as nothing ('type Car has no member E', on main too); Discharge.rows: RowReading::RigidsFixed retries the return/effects elimination where no override threads, and the call's parameter types (found by /code-review). Two defects found by the fresh-load recipe and fixed: the pass looked the short name up with lookup_symbol (the table interns it) and enumerated op_records (incomplete in a single load) — now the OperationInfo facts. ROWS: wi_nnq1s_member_supplies_only_where_it_fits_test (7); 14 rows of wi_0rp29 and wi_jpsdh rewritten to (A): the spec spelling of a call over a member that does not fit runs the default or is refused by the spec's own signature, the carrier spelling keeps its verdict. BACK-OUTS over the whole anthill-core (11364), switches: control 0; filter 14; witness rows 1 (wi_y6zcd); rigid reading 15; eq refusal 1; parameter site 1 (selected). Gate 12443 / 0 / 17; anthill-core two-step and node-carrier green; fresh-load green but wi_rah0z::the_outcome_entries_follow_the_switch, which fails on main under that recipe too; families green on both carriers; scaland testFull 811 + 51 (2 skipped) + 1. Spec text (kernel-language.md *A member that does not fit is no supplier*, the effect-row reading in 8.7, *Operation override*) awaiting the user's approval. /code-review high: 5 findings, 2 fixed, 2 no change, 1 skipped (a member fitting one provision supplies at all; Y6ZCD's per-application filter decides that).

### 2026-11-21T10:32:05Z — feedback — user

The kernel-language.md text (A member that does not fit is no supplier; the effect-row reading in 8.7; Operation override) approved by the user 2026-11-21. Committed as 08eefd36.

