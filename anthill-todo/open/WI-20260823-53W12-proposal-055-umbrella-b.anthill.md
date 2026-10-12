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
## Changes

### 2026-10-12T11:17:56Z — feedback — claude

ROWS FOUND WITH WI-20261012-RXT6S (2026-10-12, measured on 4f282c2a; the same on 65b1e7b4, the tree before it) — A SORT NAMED BY A DOTTED PATH IN A RULE BODY'S OWN TERM IS THE CHAIN, NOT THE TYPE ITS BARE NAME IS. Since RXT6S an operation body, and the receiver of a dot in a rule body, read `Outer.Inner` as the sort's type value; every other slot of a clause's term keeps the `field_access` chain (kernel-language §6.7). Over `sort Outer { sort Inner { operation deep() -> Int64 = 21 } }`, `import ….Outer.Inner` and `operation which(t: Type) -> Int64 = if t = Inner then 21 else 0`: WRONG ANSWER — `?x <=> which(Outer.Inner)` binds 0 where `?x <=> which(Inner)` binds 21; so do the written call `H.keep(Outer.Inner)` and the dot `(H).keep(Outer.Inner)` over `operation keep(t: Type) -> Int64 = which(t)`. NO MATCH — `fact holds(Outer.Inner)` is not answered by the goal `holds(Inner)`, nor `fact holds(Inner)` by `holds(Outer.Inner)`; the same spelling on both sides answers. AGREES ALREADY — `?x <=> Outer.Inner` binds `Inner` as `?x <=> Inner` does, and `Outer.Inner <=> Inner` holds: a `<=>` operand reduces the chain (§6.7's sort component access), an argument of an evaluated call is not reduced so — the walker's side of it is proposal 068's (WI-20260926-DSEXA). REFUSED FOR THE BARE NAME TOO — `Outer.Inner = Inner`, `not(Outer.Inner = Inner)` and `Outer.Inner = 7` draw the per-segment unresolved-name refusal, and so do `Inner = Inner` and `Inner = 7`, where an operation body says `eq.b: expected Type, got Int64`. UNDER A COMPOUND EXPRESSION the path is the type value now, as the bare name is (`?x <=> (if true then which(Outer.Inner) else 2)` is the residual `if true then which(Inner) else 2`), so one rule body holds the path both ways until this lands. PINNED by `wi_rxt6s_dotted_sort_type_value_test::a_rule_bodys_argument_is_still_the_term_it_was` and the two unmatched rows of `a_data_slot_still_stores_the_chain`; they turn here. Whether the stored term folds to the sort's reference, as a chain that names a const folds to its value, or is reduced where it is an operand, as a nullary operation's is, is this ticket's to say — §6.7 states both precedents.

