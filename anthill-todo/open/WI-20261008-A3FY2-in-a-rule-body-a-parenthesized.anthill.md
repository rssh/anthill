## Attributes

- id: WI-20261008-A3FY2-in-a-rule-body-a-parenthesized
- created: 2026-10-08T09:06:20Z

- status: Open
- status_agent: claude
- status_at: 2026-10-08T09:06:20Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-055

## Description

IN A RULE BODY A PARENTHESIZED TYPE RECEIVER IS REFUSED WITH AN UNRESOLVED-NAME MESSAGE — `rule r(?x) :- ?x <=> (Box).tag()` fails with "type mismatch in Box.name: expected resolved name, got unresolved", and `(Box[V = Int64]).tag()` with the same about `Int64`, while `?x <=> Box.tag()` and `?x <=> Box[V = Int64].tag()` bind 7. In an operation body all four answer 7. Measured 2026-10-08 on fd1cf282.

WHY. Since WI-20260824-PAPX0 a parenthesized receiver is a value receiver (`is_value_receiver`, parse/convert.rs), so the rule-body lowering gets a `dot_apply` whose receiver is a sort name. An operation body classifies that name as a type value and the typer's `denoted_sort_dot` answers; the rule-body walk does neither. Before PAPX0 the receiver was dropped and the program was refused as well, so the verdict did not change. The message is not about what is wrong.

WHAT. Give the rule body the operation body's reading — the dot is the written companion call — or refuse in a sentence that names the parenthesized type receiver and the spelling that works. Umbrella A (WI-20260823-ZF3AK) carries the type-value classification through operation expressions; check whether a rule-body classification is already planned before building one here.

CONTROL. `(Box).tag()` and `(Box[V = Int64]).tag()` in a rule body beside their unparenthesized spellings, resolved and the binding asserted (or the refusal's distinguishing words). Say which rows fail with the change backed out.

DONE WHEN: a rule body answers the parenthesized spelling as it answers the written one, or refuses it in words about the receiver; the gate is green.

