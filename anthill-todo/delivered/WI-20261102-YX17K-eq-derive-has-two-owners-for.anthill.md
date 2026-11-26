## Attributes

- id: WI-20261102-YX17K-eq-derive-has-two-owners-for
- created: 2026-11-02T17:48:33Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-26T15:38:02Z

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

## Changes

### 2026-11-26T15:37:47Z — feedback — user

Delivered in 2518e895a and 62806cafa. ONE OWNER: derive_total_eq, total_composites and every_field_names_a_sort are deleted; derive_conditional_eq derives every Eq+PartialEq row, a non-parametric composite's unconditional row (Colour, Duration) recorded as one clause with no conditions, as a written provides Eq[T = Colour] is — the record question the ticket owed, answered by the fold. Its readers answer one unconditioned clause as they answered none (alternative_condition_goals, provision_layout_key, coherence's ProvisionScope, check_member_blocks_have_one_clause), measured: an optimized anthill-core run over the fold moved 3 rows, all clause-count pins. BACK-OUTS, MEASURED 2026-11-26: skipping wi1098's non-Partial sorts in the one pass fails its five rows again (now as load refusals, "no impl provides Eq") and two more (a_direct_eq_call…, declaring_neq…); wi300's total row alone (every test.wi300 sort: its Partial row beside it). The candidate guards each fail a row of their own — boundary (declaring_neq…'s capeq), witness (a_carrier_a_witness…), Partial for Eq (new a_partial_holder_of_a_written_eq_is_not_refused_for_it: a holder of a sort writing Eq over a Float was refused a second time for nothing it wrote); the field-type translation fails 18 of 24. Restated pins (wi1098 Duration, wi_ank4x Colour: 0 -> 1) fail on the two-pass tree. Headers restated (wi1098, wi300's QF5JT row, wi_ank4x's index back-outs re-measured on the fold). Load time unchanged (~48 ms for the derivation step, both trees). The ANTHILL_LOAD_TIMING mark for the derivation stands after it now (it measured ~10 us). KERNEL-LANGUAGE §8.3, decided with the user: a later load may not CHANGE an earlier composite's equality; a provision the sort already has (same spec, instantiation, conditions, the same eq if it binds one), written again, is no change — derived or written by the earlier load. The fold made a restatement of a DERIVED provision load where the two-pass tree refused it (its derived row had no clause); 2518e895a refused it by a written mark, 62806cafa takes the mark back for the rule as decided. Rows: a_later_restatement_of_a_derived_provision_is_accepted and its written twin, an_earlier_sort_witnessing_a_later_ones_equality_is_accepted, a_later_provision_binding_an_eq_is_refused (binding provision new, derived one unchanged); on the two-pass tree three fail and the written twin passes; with the record's merge backed out all four fail (and HWD8A's SHED7 layout). Gate 12870 / 0; families green; scaland testFull 811+51+1 / 0; anthill-core under ANTHILL_TEST_TWO_STEP_LOAD=1 green. Pre-existing under ANTHILL_TEST_FRESH_LOAD=1, same on HEAD, not ticketed: 6 (wi_2ksaa, wi_5cz9f, wi_64272). Found and filed: WI-20261126-Q1WE9 (a derived eq member of a witness sort counted as a supplier of the sort it witnesses). Left, not ticketed: a holder whose field's sort provides Eq only conditionally (two clauses, or a condition over none of its parameters) no longer derives Eq, where the total pass claimed it outright; no row pins it.

