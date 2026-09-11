## Attributes

- id: WI-20260911-09E6M-domain-fair-enumeration-for-a
- created: 2026-09-11T10:03:00Z

- status: Open
- status_agent: user
- status_at: 2026-09-11T10:03:00Z

- acceptance: cargo-test, scaland-sbt-test

## Description

DOMAIN: fair enumeration for a constructor with TWO OR MORE recursive positions.

WI-743 derives a sort's domain as a disjunction over its constructors, and buys fairness
with two ordering rules stated at the derivation: base constructors before recursive
ones, and inside a branch the recursive field positions before the others. Those make a
CHAIN come out by length — `List[T = Letter]` enumerates `nil, [a], [b], [c], [a, a], …`,
fair and infinite, and `examples/classic-mini/alphabet-words` rests on it.

THEY DO NOT MAKE TWO RECURSIVE POSITIONS FAIR, and the gap is INCOMPLETENESS, not just an
odd order. `entity node(l: Tree, r: Tree)` descends depth-first in the later position, so
`l` stays at the base constructor for ever and `node(node(leaf, leaf), leaf)` is NEVER
REACHED — no cap, no depth limit, simply not in the stream. MEASURED and pinned by
`wi743_finite_domain_test::two_recursive_positions_in_one_constructor_are_not_fair`, which
asserts only what IS true (the stream is infinite and every row definite) precisely
because the shape of the incompleteness is the finding.

WHAT IT NEEDS is interleaving — an iterative deepening over term SIZE, so the k-th round
yields every inhabitant of size k — and no part of this resolver does that today. SLD with
`push_choice` is depth-first by construction, so this is a resolver capability and not a
tweak to the derivation's clause order: reordering branches cannot make a product of two
infinite streams fair.

RELATED, and worth deciding together: the same machinery is what a bounded `forall_in`
over a derived domain would want (WI-743's note that the future link is `forall_in`, not
`forall_impl` — the latter SKOLEMISES its binder and a skolem matches no domain row).

ACCEPTANCE: a `Tree` domain with nothing bound yields, within the first N rows, at least
one inhabitant whose LEFT position is not the base constructor; the `List` order stays
exactly `nil, [a], [b], [c], [a, a], …` (pinned by `an_infinite_domain_is_fair`, whose
first four LENGTHS are asserted); `alphabet-words` still prints 27 / 12 and `tiny-sat` 2.
State at the site what the ordering rules mean once interleaving exists — they may become
redundant, and if so the two rows that measure them today say which.

