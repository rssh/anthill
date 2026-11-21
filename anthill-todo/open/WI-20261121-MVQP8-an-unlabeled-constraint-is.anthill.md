## Attributes

- id: WI-20261121-MVQP8-an-unlabeled-constraint-is
- created: 2026-11-21T13:07:02Z

- status: Open
- status_agent: user
- status_at: 2026-11-21T13:07:02Z

- acceptance: cargo-test, scaland-sbt-test

## Description

AN UNLABELED CONSTRAINT IS REPORTED WITHOUT A NAME OR A LOCATION: two violated unlabeled constraints print two identical lines, `integrity constraint is violated by the loaded facts`, and nothing tells them apart.

FOUND while choosing how a test harness reports which invariant a state breaks (WI-20261121-G8E02, explaining a failed goal). `anthill check` names a violated constraint only by a label written in the source. A label is also the only thing a description can attach to, so an unlabeled constraint cannot carry the prose a specification writes about it (WI-20261115-S6CWK row 3).

MEASURED on a4fb58dc9 (debug CLI of 2026-11-21), with `fact p(1)`, `fact q(1)`, `big(?x) :- ?x > 5`, `small(?x) :- ?x < 0`:
  1 `constraint forall ?x: p(?x) -: big(?x)` beside `constraint forall ?x: q(?x) -: small(?x)`: both violated, reported as two identical lines `error: integrity constraint is violated by the loaded facts`.
  2 `constraint labeled_one: forall ?x: p(?x) -: small(?x)`: `integrity constraint 'labeled_one' is violated by the loaded facts`. No location either.
  3 `{< every p is big >}` before an unlabeled constraint: refused, "description block on unlabeled constraint has no stable target" (S6CWK row 3, unchanged since 53a0d453b).

THE CAUSE. `LoadError::ConstraintViolated { label: Option<String> }` (kb/load.rs:2820) carries the written label and nothing else: no span, no head. Its neighbour `AggregationConstraintUnsupported` carries a span, so the loader has it at hand.

PROPOSED: the loader gives every unlabeled constraint a label generated from its head, and every violation report carries the constraint's location.
- The head is what §6.2 calls it: "The invariant (head) states what must be true". For `forall ?x: A -: C` it is the innermost consequent `C`; for `Inv :- Guard`, `Inv`; for an aggregation, the comparison. Row 1's labels are `big(?x)` and `small(?x)`.
- When two unlabeled constraints in one scope share a head, each label adds its guard: the guard as printed when it is short (a limit to decide; about 40 characters), otherwise a short hash of the guard's stored form, so that renaming a variable or reformatting does not change the label. Two identical constraints are refused at load as duplicates. Two different guards whose short hashes clash are refused.
- A label is never positional (`#1`, `#2`): reordering two declarations must not move a label from one constraint to the other.
- The generated label is the constraint's symbol in its scope, as a written one is, so it is the target of a description: row 3 loads. The rest of S6CWK (clauses, facts, goals in a body) stays there.
- The report reads `integrity constraint big(?x) is violated by the loaded facts (file:line)`, and adds the description when the constraint has one. A written label is reported as today, with the location added.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven):
- row 1 reports two lines that differ, `big(?x)` and `small(?x)`, each with its location;
- row 2 is reported with its location;
- row 3 loads, stores a DescriptionInfo naming the generated label, and its violation report shows the description;
- two unlabeled constraints with one head: with a short guard, each label shows its guard; with a long guard, each shows a hash, and renaming a variable in the guard leaves the hash unchanged;
- two identical unlabeled constraints are refused at load;
- written labels are unchanged apart from the location;
- back-out: without the generated label, row 1 prints two identical lines and row 3 is refused again.

## Changes

### 2026-11-21T13:22:44Z — feedback — claude

EXTENDED with the user 2026-11-21: EVERY UNLABELED CLAUSE GETS A GENERATED LABEL, not only a constraint. A rule's clause and a fact get one by the same rule as a constraint. A description before any of them then has a target. This closes WI-20261115-S6CWK rows 1-3 (a rule, a fact, a constraint) and answers its open design question: the target is the generated label, not the stored clause or its source occurrence.

- A rule's or a fact's label is its head as written: `product_has_positive_price(ShopState(products: ?ps))`.
- Where two clauses in one scope have the same head, the label adds the body. The three `can_add_to_cart(?s, ?customerId, ?productId, ?delta)` scenarios are such clauses. The body is printed when short, and otherwise replaced by a short hash of its stored form, as for a constraint's guard. Two identical clauses are one clause, as the store holds them, and share their descriptions.
- A written label is unchanged.
- The predicate-level case in S6CWK's feedback of 2026-11-21 reads as option (a) there: a predicate's description is its clauses' descriptions together.

ACCEPTANCE, added:
- S6CWK rows 1-3 load, and each stores a DescriptionInfo naming the generated label;
- the three `can_add_to_cart` clauses get three different labels, each with its own description;
- renaming a variable in a body leaves its hash unchanged;
- back-out: without the generated label, those rows are refused again.

