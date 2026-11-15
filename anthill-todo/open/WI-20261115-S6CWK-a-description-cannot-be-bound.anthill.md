## Attributes

- id: WI-20261115-S6CWK-a-description-cannot-be-bound
- created: 2026-11-15T15:22:50Z

- status: Open
- status_agent: user
- status_at: 2026-11-15T15:22:50Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A DESCRIPTION CANNOT BE BOUND TO AN UNLABELED CLAUSE, A FACT, AN UNLABELED CONSTRAINT OR A GOAL IN A BODY, so the prose a specification writes about each clause can only be a discarded `--` comment, or a label the clause does not otherwise need (user, 2026-11-15: "This is problem in anthill").

FOUND writing the invariants of a shop's state (modelled as a value) in place: each invariant is one clause of `violation(?s, name)`, or one conjunct of a single `valid_state` rule, and each carries a sentence from the original specification ("Product: price is greater than zero"). Today that sentence can only be a `--` comment, which the parser discards. So nothing that reads the KB has it: a generated document, a report of which invariant a state breaks, or a model repairing the spec.

MEASURED on 53a0d453b (anthill CLI of 2026-11-13):
  1 `{< … >}` before an unlabeled bodied rule is refused: "description block on unlabeled rule has no stable target: descriptions name a declaration symbol or citation handle. Add a label where this construct permits one, …"
  2 before a `fact`: refused with the same message ("on fact")
  3 before an unlabeled `constraint`: refused with the same message
  4 before a goal in a rule body (`rule r(S(products: ?ps)) :- {< … >} (forall ?p in ?ps: ?p.price > 0)`): syntax error
  5 after a bounded quantifier's binder (`(forall ?p {< … >} ? in ?ps: …)`): syntax error. §4.1 admits a description "after a variable" in any term position, and a binder is one.
  6 Controls: a labeled rule takes one. `{< Product: price is greater than zero >} rule product_has_positive_price: positive_prices(S(products: ?ps)) :- …` stores `DescriptionInfo(target: product_has_positive_price, content: "Product: price is greater than zero", index: 0)`. So does an ordinary variable (`rule valid_c(?s {< the state under check >} ?) :- …`).

THE CAUSE is the target, not the grammar (apart from rows 4 and 5). `DescriptionInfo(target, content, index)` names a symbol, and an unlabeled clause has none. §4.1 states this, and the refusal is deliberate: a block is refused, never silently dropped. The repair the message advises, a label, gives the clause a citation handle it does not otherwise need: one more name to keep unique in its scope. In the in-place pattern, the label also repeats the name the clause already carries (`violation(…, "product_has_positive_price")`).

PROPOSED (the target design to decide first):
- An unlabeled clause is a description target: the clause itself. Candidates for the target term are the stored clause (hash-consed, so two identical clauses are one clause and share their descriptions) or its source occurrence. The same goes for a `fact` and an unlabeled `constraint`.
- A goal in a rule body may carry a description, targeting that goal's occurrence in its clause. This gives conjunct-level documentation for the one-rule spelling.
- A quantifier binder takes a variable description, as any variable does (row 5).
- `DescriptionInfo` and `KB.descriptions` answer for these targets.

ACCEPTANCE: rows 1-5 load, and each stores a DescriptionInfo that names the clause (or goal, or binder) it is written on. A query for that clause's descriptions answers the text. Row 6 is unchanged. Back-out: rows 1-5 are refused again.

