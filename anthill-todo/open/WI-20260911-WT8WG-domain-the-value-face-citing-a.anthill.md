## Attributes

- id: WI-20260911-WT8WG-domain-the-value-face-citing-a
- created: 2026-09-11T10:03:05Z

- status: Open
- status_agent: user
- status_at: 2026-09-11T10:03:05Z

- acceptance: cargo-test, scaland-sbt-test

## Description

DOMAIN: the VALUE face — citing a sort's domain as a relation value.

WI-743 delivers §2.2's GOAL face only: a typed relational head reads the derived
`anthill.kernel.domain_member` relation as an appended body goal, and an explicitly built
goal answers the same rows (pinned by
`wi743_finite_domain_test::an_explicit_member_goal_answers_what_the_typed_head_does`).
What it does NOT deliver is the VALUE face — `Colour.domain` cited BY NAME as a
`Relation[…]`, the way WI-714 lets a rule be cited and `takeN`/`where`-d.

THE BOUNDARY WAS STATED DELIBERATELY, not skipped: the 2026-09-11 implementation review
records that `Colour.domain` over ground facts would type as `Relation[Unit]`, not
`Relation[Colour]`, and warned against delivering the value face BY ACCIDENT through a
rule-shaped derivation, which reopens the typed-column and self-call questions. WI-743
derives CLAUSES under ONE kernel functor rather than per-sort `<Sort>.domain` relations,
so there is no `Colour.domain` name to cite at all today — the citation has to be
designed, not merely enabled.

THREE QUESTIONS TO SETTLE FIRST, none of which WI-743 answers:
  1. WHAT IS CITED. A per-sort name (`Colour.domain`) is what §2.2's prose suggests and
     what WI-714's dotted machinery already resolves, but the derivation is deliberately
     ONE clause set on one functor — that is what lets `domain_member(?h, ?T)` inside the
     `List` clause dispatch on whatever `?T` binds to. A per-sort face would be a
     projection of it, not a second definition.
  2. WHAT IT TYPES AS. `Relation[(x: Colour)]`, presumably — and for a PARAMETERISED sort
     the citation has to carry the type argument (`List[T = Letter].domain`?), which is a
     surface question 052 has not been asked.
  3. WHAT IT DOES WHEN THE DOMAIN IS INFINITE. `takeN` is fine; draining raises. That is
     WI-737's existing route and needs driving, not building.

ACCEPTANCE: `let c = Colour.domain` (or whatever (1) settles) types as a Relation over
Colour and `c.takeN(5)` answers 3 rows; the same citation over `List[T = Letter]` answers
its cap and does not hang; a full drain of an infinite domain raises
`Error[RelationFloundered]` rather than materializing a row. The GOAL face is unchanged —
`wi743_finite_domain_test` keeps its counts.

