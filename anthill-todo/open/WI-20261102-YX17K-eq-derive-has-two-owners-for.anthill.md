## Attributes

- id: WI-20261102-YX17K-eq-derive-has-two-owners-for
- created: 2026-11-02T17:48:33Z

- status: Open
- status_agent: user
- status_at: 2026-11-02T17:48:33Z

- acceptance: cargo-test, scaland-sbt-test

## Description

EQ_DERIVE HAS TWO OWNERS FOR ONE ROW: the TOTAL pass and the CONDITIONAL pass both derive the unconditional `Eq`+`PartialEq` of a non-parametric total composite, so a back-out of either measures nothing and a fix to one pass's exclusions that the other does not mirror is masked. Found by /code-review of WI-20260831-QF5JT (user, 2026-11-02: file it).

THE OVERLAP, MEASURED (QF5JT, 2026-11-02). `eq_derive::derive_total_eq` asserts the pair for each sort `total_composites` returns. `derive_conditional_eq`, called right after it (`kb/load.rs`, the `eq_derive::classify` block of `load_phase_inner`), takes as candidates every composite that is not a boundary, not partial, not spoken for and not already providing, so a non-parametric one the total pass skipped is derived again, with an EMPTY condition list. Measured three ways:
  * skip a fixture sort in the total loop alone: it still provides both specs, and the guard row passes;
  * skip it in BOTH passes: it provides nothing (`wi300_rule_body_requires_test::a_carrier_whose_fields_provide_eq_derives_it_and_passes_the_guard` fails);
  * back out the `derive_total_eq` CALL: `wi1098_derive_eq_total_test` fails ONE row (`a_parametric_sort_derives_a_conditional_row`, `Duration`'s clause count 0 -> 1) where its header recorded FIVE before WI-20260918-CKD4J added the conditional pass. That header now says so.
The two exclusion lists are written twice (`total_composites`' seed, `derive_conditional_eq`'s `candidates`), and the field rule twice (`total_composites`' fixpoint over head sorts, `field_conditions` over field types).

THE ONE OBSERVABLE DIFFERENCE, which is the decision this ticket owes. The conditional pass files a provision-clause record (`record_derived_conditions` -> `record_provides_clause`) and the total pass does not. `a_parametric_sort_derives_a_conditional_row` pins `Duration` at 0 ("outside the clause record"). The record is read by `provides_clause_count` (`typing/candidates.rs` `alternative_condition_goals`, `typing/requires.rs` provision layout key, `eq_derive.rs` ~717) and by `KnowledgeBase::provides_unconditioned_clause`. Folding the total loop into the conditional pass would make `provides_unconditioned_clause` true for every derived total composite, where it is false today. Not measured what that changes.

DIRECTION, not decided: make the two domains DISJOINT by construction. Restrict `derive_conditional_eq`'s candidates to what the total pass cannot derive (a parametric sort, a composite with a parametric field), so each derived row has one owner and no clause record changes. The other way is to fold, with the record question answered first. Either way the Partial `PartialEq` half stays in `derive_total_eq`; it is not duplicated.

ACCEPTANCE: each derived row has one owner; backing out either pass fails rows of its own (the `derive_total_eq` call back-out fails wi1098's five rows again, or the header says by measurement why not); the QF5JT row's both-passes note restated if it changes; full workspace green via rustland/scripts/test.sh, families green.

REFERENCE: kb/eq_derive.rs `derive_total_eq`, `total_composites`, `derive_conditional_eq`, `record_derived_conditions`; WI-1098, WI-20260918-CKD4J, WI-20260831-QF5JT.

