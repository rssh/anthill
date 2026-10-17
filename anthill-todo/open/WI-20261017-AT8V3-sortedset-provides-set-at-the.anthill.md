## Attributes

- id: WI-20261017-AT8V3-sortedset-provides-set-at-the
- created: 2026-10-17T09:37:58Z

- status: Open
- status_agent: user
- status_at: 2026-10-17T09:37:58Z

- acceptance: cargo-test, scaland-sbt-test

## Description

SORTEDSET PROVIDES SET AT THE FACTOR DOMAIN OF ITS ORDERING -- a coarse ordering O over X is an equivalence (a ~ b iff O.compare(a, b) = 0), and SortedSet keeps one representative per class, so it is a lawful Set not of X but of the factor domain X/O: `SortedSet[T = X, O = Ord] provides Set[T = Factor[X, Ord]]` (user, 2026-10-17).

WHY. Set has no implementation at all: its operations are body-less, there is no host mapping, and nothing provides it, so every Set call in an operation body dies at eval (MEASURED 2026-10-17: `Set.insert(Set.empty(), 1)` -> 'operation has no body: anthill.prelude.Set.empty'). SortedSet is the library's one persistent set, and it deliberately does NOT provide Set (sortedset.anthill, 'AND NO provides Set EITHER'): it lacks contains / subset / intersection / difference, and under a coarse comparator `union` keeps the left operand's representative, so it is not a Set of X. Read as a Set of the factor domain, both objections go: membership and equality are by class, and `union` is commutative on classes.

WHAT IT NEEDS, to be designed rather than assumed:
 1. The factor domain as a type: `Factor[X, Ord]`, whose equality is the ordering's equivalence. Set requires Eq[T], so Eq[Factor[X, O]] has to be provided from O's WeakOrd.
 2. SortedSet's missing operations: contains, subset, intersection, difference (insert / union / empty / eq exist).
 3. The provision itself, and how a value of X stands as an element of Factor[X, O] at a call (the class of its representative).
 4. Where O agrees with Eq on X (a total order consistent with equality), Factor[X, O] is X: say whether the provision is then also Set[T = X], or whether that is left to a separate implementation.

RELATION: this is route (a) of WI-20260926-QCJ0B (Set's operations have no implementation). WI-20260909-M8QWJ's load-time dictionary check is what would refuse a Set call while no provider exists. Cross-references, not dependencies.

