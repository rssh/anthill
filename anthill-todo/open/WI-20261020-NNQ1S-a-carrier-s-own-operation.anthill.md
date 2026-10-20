## Attributes

- id: WI-20261020-NNQ1S-a-carrier-s-own-operation
- created: 2026-10-20T07:56:46Z

- status: Open
- status_agent: user
- status_at: 2026-10-20T07:56:46Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A CARRIER'S OWN OPERATION NAMED LIKE A SPEC MEMBER IS DISPATCHED TO, WHETHER OR NOT IT SUPPLIES THE MEMBER. MEASURED on 663ac457, the same on 098ce8a9. `sort P { entity p(x: Int64)  operation neq(a: Int64, b: Int64) -> Bool = true }`, no provision written, `import anthill.prelude.PartialEq.{eq, neq}`: `eq(p(x: 1), p(x: 1))` answers yes and `neq(p(x: 1), p(x: 1))` answers yes — `P.neq`, an operation over two `Int64`s, answered the `neq` of two `P`s, a silent wrong answer. With `operation neq(n: Int64) -> Bool` the call dies at run time, "operation call: expected 1 args, got 2". Writing `provides anthill.prelude.PartialEq[T = P]` changes nothing. THE RULE: `neq` is derived, `rule neq(?a, ?b) <=> not(eq(?a, ?b))` (eq.anthill); "an own `neq` member is never consulted" (kernel-language.md §8.7), and "a member merely named `neq` that does not compare the carrier's own values … supplies nothing and is untouched" — the load check classifies `P.neq(a: Int64, b: Int64)` so, and refuses `neq(a: P, b: P)` (`CarrierSuppliesNeq`), while dispatch takes it. THE ROUTE: a carrier's member is found by short name in the sort-operations table (`sort_ops_lookup(carrier, short)`), read by `carrier_own_op` (call_class.rs, route 1 of `spec_op_suppliers_for_carrier`), by `resolve_op_target` (call_class.rs) and by the typer's `resolve_at_goal` (carrier.rs). SQZPQ special-cased one builtin there (`answered_by_its_dictionary`, for `TypeValue.type_value`). FIX DIRECTION: take a carrier's member only where it is a member of the spec at that carrier — the criterion the loader applies (`member_operands_are_the_carrier`, load.rs) — at every reader, retiring the special case where it is covered. ACCEPTANCE: with the own `neq` present, written provision or not, `neq(p(x: 1), p(x: 1))` answers no (the derived `neq`) and the one-argument variant runs; `P.neq(3, 3)` still calls the own operation; a row per reader, back-outs measured; full gate green.

