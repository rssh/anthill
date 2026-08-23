## Attributes

- id: WI-20260823-53W12-proposal-055-umbrella-b
- created: 2026-08-23T09:40:05Z

- status: Open
- status_agent: user
- status_at: 2026-08-23T09:40:05Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260823-ZF3AK-proposal-055-umbrella-a

- tags: proposal-055

## Description

Proposal 055 umbrella B — PRESERVE TYPE-VALUE DENOTATION THROUGH FACTS, RULES, AND PROPOSAL-062 GUARDS. Implement docs/design/055-implementation.md §§6–10 for convert_term and build_body_atom_occurrence using umbrella A's resolved TypeValue rather than independently reclassifying syntax. Separate denotation from validation: declared Type columns accept; declared Term columns accept the structural raw-term carrier; every other declared sort is a loud mismatch; undeclared relational columns preserve the type term and participate in relation-column inference. Keep logical variables in type applications, the top-level instance-claim depth gate, and the [] type/instance versus () construction surface gate. DRIVE proposal compatibility: requires Ord[X] remains a requirement edge; require[Ord[X]] remains proposal-060 dictionary acquisition; proposal-062 requires is_entity_of(Trust, TrustLevel) resolves as an ordinary two-argument goal whose arguments are the enclosing type parameter and sort type terms, substitutes, and actually resolves; is_entity_of[Trust, TrustLevel] is refused because the untyped rule declares no type parameters. ACCEPTANCE: Type- and String-declared fact-field controls, variable-bearing rule type term, instance-claim control, and the 060/062 forms above; tests state which fail on back-out; full Rust workspace via rustland/scripts/test.sh. This is an umbrella and may be split, but the existing proposal-062 implementation must remain blocked until this complete logical-carrier boundary is delivered.
